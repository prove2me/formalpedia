-- Prove2me | solution 1 for GraphonMF.DenseRate.eq_6_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:59:19.192602+00:00
-- url     : https://prove2.me/submissions/03e70c21-81bf-4e33-9693-18413f54eeeb

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace P2MGmf3a

/-- Pointwise real estimate behind (6.17). -/
theorem real_bound {d n : ℕ} (hn : 0 < n) (K : ℝ) (hK : 0 ≤ K) (ξ : Fin n → ℝ)
    (hξ : ∀ j, |ξ j| ≤ 1) (Δ : Fin n → (Fin d → ℝ)) (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (i : Fin n) (hΔ : ∀ j, ‖Δ j‖ ≤ K * (a i + a j)) :
    ‖(1 / (n : ℝ)) • ∑ j, ξ j • Δ j‖ ^ 2 ≤
      ∑ j, (2 * K ^ 2 / n) * (a i ^ 2 + a j ^ 2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ‖(1 / (n : ℝ)) • ∑ j, ξ j • Δ j‖ ≤ (1 / (n : ℝ)) * ∑ j, K * (a i + a j) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    calc |ξ j| * ‖Δ j‖ ≤ 1 * ‖Δ j‖ := mul_le_mul_of_nonneg_right (hξ j) (norm_nonneg _)
      _ ≤ K * (a i + a j) := by rw [one_mul]; exact hΔ j
  have hc : 0 ≤ (1 / (n : ℝ)) * ∑ j, K * (a i + a j) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => mul_nonneg hK (add_nonneg (ha i) (ha j)))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans ?_
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => K * (a i + a j))
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have h3 : ((1 / (n : ℝ)) * ∑ j, K * (a i + a j)) ^ 2 ≤
      (1 / (n : ℝ)) * ∑ j, (K * (a i + a j)) ^ 2 := by
    rw [mul_pow]
    have : (1 / (n : ℝ)) ^ 2 * (∑ j, K * (a i + a j)) ^ 2 ≤
        (1 / (n : ℝ)) ^ 2 * ((n : ℝ) * ∑ j, (K * (a i + a j)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  refine h3.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hnr.le
  nlinarith [sq_nonneg (a i - a j), sq_nonneg K]

end P2MGmf3a

open GraphonMF.DenseRate in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    (h32 : Cond32 P X0 B ξ G)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → (Fin d → ℝ)),
      IsParticleSolution T P X0 B ξ b sigma n Xn → ∀ (i : Fin n) (s : ℝ≥0), s ≤ T →
      Tt1 P ξ b X n Xn i s ≤
        ENNReal.ofReal (2 * κ) * ⨆ i' : Fin n, ∫⁻ ω, ‖Xn i' s ω - X (lab n i') s ω‖ₑ ^ 2 ∂P := by
  obtain ⟨-, -, -, K, hK0, hK⟩ := h21
  have hξ : ∀ n ω (i j : Fin n), |ξ n ω i j| ≤ 1 := by
    intro n ω i j
    rcases h32 with h | h
    · rw [h]
      have := hG.2.2 (lab n i) (lab n j)
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rcases (h n).1.2.2.1 ω i j with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
  refine ⟨2 * K ^ 2 + 1, by positivity, ?_⟩
  intro n Xn hXn i s hs
  have hn : 0 < n := Fin.pos i
  -- measurability of the time-`s` marginals
  have evalAE : ∀ (Y : ℝ≥0 → Ω → (Fin d → ℝ)),
      (∀ ω, Continuous (fun r : Set.Icc (0 : ℝ≥0) T => Y r ω)) →
      AEMeasurable (pathOf T Y) P → AEMeasurable (Y s) P := by
    intro Y hc hm
    have heq : Y s = (fun x : GraphonMF.Stability.Cd T d => x ⟨s, ⟨bot_le, hs⟩⟩) ∘ pathOf T Y := by
      funext ω
      simp [pathOf, dif_pos (hc ω)]
    rw [heq]
    exact (continuous_eval_const _).measurable.comp_aemeasurable hm
  have hD : ∀ k : Fin n, AEMeasurable (fun ω => ‖Xn k s ω - X (lab n k) s ω‖ₑ ^ 2) P := by
    intro k
    exact (((evalAE _ (hXn.cont k) (hXn.meas_path k)).sub
      (evalAE _ (hX.cont (lab n k)) (hX.meas_path (lab n k)))).enorm).pow_const 2
  set D : Fin n → Ω → ℝ≥0∞ := fun k ω => ‖Xn k s ω - X (lab n k) s ω‖ₑ ^ 2 with hDdef
  set M := ⨆ i' : Fin n, ∫⁻ ω, D i' ω ∂P with hM
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * K ^ 2 / n) with hc
  have hpt : ∀ ω, ‖(1 / (n : ℝ)) • ∑ j, ξ n ω i j •
      (b (Xn i s ω) (Xn j s ω) - b (X (lab n i) s ω) (X (lab n j) s ω))‖ₑ ^ 2 ≤
      ∑ j, c * (D i ω + D j ω) := by
    intro ω
    have hr := P2MGmf3a.real_bound hn K hK0 (fun j => ξ n ω i j) (fun j => hξ n ω i j)
      (fun j => b (Xn i s ω) (Xn j s ω) - b (X (lab n i) s ω) (X (lab n j) s ω))
      (fun k => ‖Xn k s ω - X (lab n k) s ω‖) (fun k => norm_nonneg _) i (fun j => by
        have := hK (Xn i s ω) (X (lab n i) s ω) (Xn j s ω) (X (lab n j) s ω)
        have h0 := norm_nonneg (Peng1990.SMP.matEntries
          (sigma (Xn i s ω) (Xn j s ω) - sigma (X (lab n i) s ω) (X (lab n j) s ω)))
        linarith)
    have hrhs : ∑ j, c * (D i ω + D j ω) = ENNReal.ofReal
        (∑ j, (2 * K ^ 2 / n) * (‖Xn i s ω - X (lab n i) s ω‖ ^ 2 +
          ‖Xn j s ω - X (lab n j) s ω‖ ^ 2)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [hc, hDdef, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    rw [hrhs, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hr
  unfold Tt1
  calc _ ≤ ∫⁻ ω, ∑ j, c * (D i ω + D j ω) ∂P := lintegral_mono hpt
    _ = ∑ j, c * (∫⁻ ω, D i ω ∂P + ∫⁻ ω, D j ω ∂P) := by
        have hsum := lintegral_finsetSum' (μ := P) Finset.univ (f := fun j ω => c * (D i ω + D j ω))
          (fun j _ => ((hD i).add (hD j)).const_mul c)
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' (hD i)]
    _ ≤ ∑ _j : Fin n, c * (M + M) := by
        refine Finset.sum_le_sum fun j _ => ?_
        gcongr
        · exact le_iSup (fun i' : Fin n => ∫⁻ ω, D i' ω ∂P) i
        · exact le_iSup (fun i' : Fin n => ∫⁻ ω, D i' ω ∂P) j
    _ = ENNReal.ofReal (4 * K ^ 2) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ← two_mul, mul_comm (2 : ℝ≥0∞) M, ← mul_assoc]
        rw [mul_assoc, mul_comm M 2, ← mul_assoc]
        congr 1
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn
        rw [hc, show ((n : ℝ≥0∞)) = ENNReal.ofReal n by simp,
          ← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by nlinarith)) bot_le
