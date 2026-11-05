-- Prove2me | solution 1 for GraphonMF.SparseRate.eq_7_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:25:18.064383+00:00
-- url     : https://prove2.me/submissions/6b610d6e-5390-42db-a721-4fe4b7147f82

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace P2MGmf5b

theorem sq4 {E : Type*} [SeminormedAddCommGroup E] (x1 x2 x3 x4 : E) :
    ‖x1 + x2 + x3 + x4‖ₑ ^ 2 ≤ 4 * (‖x1‖ₑ ^ 2 + ‖x2‖ₑ ^ 2 + ‖x3‖ₑ ^ 2 + ‖x4‖ₑ ^ 2) := by
  simp only [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h : ‖x1 + x2 + x3 + x4‖ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ := norm_add₄_le
  have h0 := norm_nonneg (x1 + x2 + x3 + x4)
  have := norm_nonneg x1; have := norm_nonneg x2; have := norm_nonneg x3; have := norm_nonneg x4
  nlinarith [sq_nonneg (‖x1‖ - ‖x2‖), sq_nonneg (‖x1‖ - ‖x3‖), sq_nonneg (‖x1‖ - ‖x4‖),
    sq_nonneg (‖x2‖ - ‖x3‖), sq_nonneg (‖x2‖ - ‖x4‖), sq_nonneg (‖x3‖ - ‖x4‖),
    mul_le_mul h h h0 (by positivity)]

theorem lint4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f1 f2 f3 f4 : Ω → ℝ≥0∞)
    (h1 : AEMeasurable f1 P) (h2 : AEMeasurable f2 P) (h3 : AEMeasurable f3 P) :
    ∫⁻ ω, 4 * (f1 ω + f2 ω + f3 ω + f4 ω) ∂P =
      4 * (∫⁻ ω, f1 ω ∂P + ∫⁻ ω, f2 ω ∂P + ∫⁻ ω, f3 ω ∂P + ∫⁻ ω, f4 ω ∂P) := by
  rw [lintegral_const_mul' _ _ (by norm_num),
    lintegral_add_left' (f := fun ω => f1 ω + f2 ω + f3 ω) ((h1.add h2).add h3),
    lintegral_add_left' (f := fun ω => f1 ω + f2 ω) (h1.add h2), lintegral_add_left' h1]

end P2MGmf5b

open GraphonMF.SparseRate in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) :
    ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ s : ℝ≥0, s ≤ T →
        (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s ω) (Xn j s ω) -
              driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P ≤
          4 * (((1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (Xn i s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω))‖ₑ ^ 2 ∂P) + Rn2 P b β ξ X n Xn s + ((1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / (n : ℝ)) • ∑ j : Fin n, ((ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
              G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))‖ₑ ^ 2 ∂P) + Rn4 P b G X n s) := by
  intro n Xn hXn s hs
  haveI : IsProbabilityMeasure P := hN.prob
  obtain ⟨⟨Cb, hCb⟩, Kb, hKb⟩ := h41.2.1
  have hbL : LipschitzWith (Real.toNNReal (2 * max Kb 0))
      (fun p : (Fin d → ℝ) × (Fin d → ℝ) => b p.1 p.2) := by
    refine LipschitzWith.of_dist_le_mul fun p p' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    calc ‖b p.1 p.2 - b p'.1 p'.2‖ ≤ Kb * (‖p.1 - p'.1‖ + ‖p.2 - p'.2‖) := hKb _ _ _ _
      _ ≤ max Kb 0 * (‖p.1 - p'.1‖ + ‖p.2 - p'.2‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Kb 0 * (‖p - p'‖ + ‖p - p'‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (norm_fst_le (p - p')) (norm_snd_le (p - p')))
            (le_max_right _ _)
      _ = 2 * max Kb 0 * ‖p - p'‖ := by ring
  have hbm : ∀ f g : Ω → Fin d → ℝ, Measurable f → Measurable g →
      Measurable (fun ω => b (f ω) (g ω)) := fun f g hf hg =>
    hbL.continuous.measurable.comp (hf.prodMk hg)
  have hXnm : ∀ j, Measurable (Xn j s) := fun j => by
    have h1 := (((hXn.2.2.2 j).1.stronglyAdapted s).mono ((filtN hN h43.meas n).le s)).measurable
    have h2 : Measurable (fun ω => (Xn j s ω - X0 (GraphonMF.DenseRate.lab n j) ω) +
        X0 (GraphonMF.DenseRate.lab n j) ω) := h1.add (hN.meas0 (GraphonMF.DenseRate.lab n j))
    simpa only [sub_add_cancel] using h2
  have hXm : ∀ u, Measurable (X u s) := fun u => by
    have h1 := (((hX.2.2.2.2 u).1.stronglyAdapted s).mono ((filtU hN u).le s)).measurable
    have h2 : Measurable (fun ω => (X u s ω - X0 u ω) + X0 u ω) := h1.add (hN.meas0 u)
    simpa only [sub_add_cancel] using h2
  have hξm : ∀ i j, Measurable (fun ω => ξ n ω i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (h43.meas n))
  have hIm : ∀ j, Measurable (fun y => ∫ x, b y x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s))) := by
    intro j
    refine (LipschitzWith.continuous (K := Real.toNNReal (max Kb 0 * (P.map (X (GraphonMF.DenseRate.lab n j) s)).real Set.univ))
      (LipschitzWith.of_dist_le_mul fun y y' => ?_)).measurable
    have hint : ∀ z, Integrable (fun x => b z x) (P.map (X (GraphonMF.DenseRate.lab n j) s)) := fun z =>
      Integrable.of_bound ((hbL.continuous.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable) Cb
        (Filter.Eventually.of_forall fun x => hCb z x)
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity), ← integral_sub (hint y) (hint y')]
    calc ‖∫ x, (b y x - b y' x) ∂(P.map (X (GraphonMF.DenseRate.lab n j) s))‖
        ≤ (max Kb 0 * ‖y - y'‖) * (P.map (X (GraphonMF.DenseRate.lab n j) s)).real Set.univ := by
          refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
          calc ‖b y x - b y' x‖ ≤ Kb * (‖y - y'‖ + ‖x - x‖) := hKb _ _ _ _
            _ = Kb * ‖y - y'‖ := by simp
            _ ≤ max Kb 0 * ‖y - y'‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ = _ := by ring
  have hkey : ∀ (i : Fin n) (ω : Ω),
      (1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s ω) (Xn j s ω) -
          driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω) =
        (1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (Xn i s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω)) +
        (1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω)) +
        (1 / (n : ℝ)) • ∑ j : Fin n, ((ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
              G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s))) +
        (((1 / (n : ℝ)) • ∑ j : Fin n,
            G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))
          - driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)) := by
    intro i ω
    have e : (1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s ω) (Xn j s ω) =
        (1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) • b (Xn i s ω) (Xn j s ω) := by
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  have hpt : ∀ i : Fin n, ∫⁻ ω,
      ‖(1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s ω) (Xn j s ω) -
          driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P ≤
      4 * ((∫⁻ ω, ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (Xn i s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω))‖ₑ ^ 2 ∂P) +
        (∫⁻ ω, ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω))‖ₑ ^ 2 ∂P) +
        (∫⁻ ω, ‖(1 / (n : ℝ)) • ∑ j : Fin n, ((ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
              G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))‖ₑ ^ 2 ∂P) +
        (∫⁻ ω, ‖((1 / (n : ℝ)) • ∑ j : Fin n,
            G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))
          - driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P)) := by
    intro i
    rw [← P2MGmf5b.lint4]
    · refine lintegral_mono fun ω => ?_
      rw [hkey i ω]
      exact P2MGmf5b.sq4 _ _ _ _
    · have hin : ∀ j, Measurable (fun ω => (ξ n ω i j / β n) •
          (b (Xn i s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω))) := fun j =>
        ((hξm i j).div_const _).smul ((hbm _ _ (hXnm i) (hXnm j)).sub (hbm _ _ (hXm _) (hXnm j)))
      exact (Measurable.pow_const (Measurable.enorm
        ((Finset.measurable_sum Finset.univ fun j _ => hin j).const_smul (1 / (n : ℝ)))) 2).aemeasurable
    · have hin : ∀ j, Measurable (fun ω => (ξ n ω i j / β n) •
          (b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω))) := fun j =>
        ((hξm i j).div_const _).smul ((hbm _ _ (hXm _) (hXnm j)).sub (hbm _ _ (hXm _) (hXm _)))
      exact (Measurable.pow_const (Measurable.enorm
        ((Finset.measurable_sum Finset.univ fun j _ => hin j).const_smul (1 / (n : ℝ)))) 2).aemeasurable
    · have hin : ∀ j, Measurable (fun ω => (ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
          G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s))) := fun j =>
        (((hξm i j).div_const _).smul (hbm _ _ (hXm _) (hXm _))).sub
          (((hIm j).comp (hXm (GraphonMF.DenseRate.lab n i))).const_smul (G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j)) :
            Measurable (fun ω => G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) •
              ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s))))
      exact (Measurable.pow_const (Measurable.enorm
        ((Finset.measurable_sum Finset.univ fun j _ => hin j).const_smul (1 / (n : ℝ)))) 2).aemeasurable
  calc _ ≤ (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, 4 * ((∫⁻ ω, ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (Xn i s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω))‖ₑ ^ 2 ∂P) +
        (∫⁻ ω, ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω))‖ₑ ^ 2 ∂P) +
        (∫⁻ ω, ‖(1 / (n : ℝ)) • ∑ j : Fin n, ((ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
              G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))‖ₑ ^ 2 ∂P) +
        (∫⁻ ω, ‖((1 / (n : ℝ)) • ∑ j : Fin n,
            G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))
          - driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P)) :=
        mul_le_mul_right (Finset.sum_le_sum fun i _ => hpt i) _
    _ = _ := by
      simp only [Rn2, Rn4]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
      ring
