-- Prove2me | solution 1 for LeiBR.Sync.prop_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:48:00.385324+00:00
-- url     : https://prove2.me/submissions/c5f1c8f7-3e2e-40f8-b0e3-230593530ab3

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1
import Theorems.Thm_LeiBR_Sync_eq_20
import Theorems.Thm_LeiBR_Sync_lemma_2

open MeasureTheory

open LeiBR.Sync in
theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs)
    (F : Filtration ℕ mΩ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (x0 : Profile n) (x : ℕ → Ω → Profile n)
    (hx : IsAlg1 P F X xhat (fun _ k => η ^ (k + 1)) x0 x)
    (C : ℝ) (hC : ∀ i : Fin N, ‖x0 i - xs i‖ ≤ C)
    (q : ℝ) (hcq : max (specNorm (Gamma X (payoff P ξ ψ) μ)) η < q) (hq1 : q < 1)
    (D : ℝ) (hD : D = 1 / (Real.exp 1 *
      Real.log (q / max (specNorm (Gamma X (payoff P ξ ψ) μ)) η))) :
    ∀ k : ℕ, ∫ ω, blockDist (x k ω) xs ∂P ≤ Real.sqrt N * (C + D) * q ^ k := by
  set a := specNorm (Gamma X (payoff P ξ ψ) μ) with ha
  set c := max a η with hc
  have ha0 : 0 ≤ a := norm_nonneg _
  have hc0 : 0 < c := lt_of_lt_of_le hη0 (le_max_right _ _)
  have hac : a ≤ c := le_max_left _ _
  have hηc : η ≤ c := le_max_right _ _
  have hc1 : c < 1 := lt_trans hcq hq1
  set u : ℕ → ℝ := fun k => ∫ ω, blockDist (x k ω) xs ∂P with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k =>
    integral_nonneg fun ω => Real.sqrt_nonneg _
  -- recursion (20)
  have h20 := eq_20 P ξ X ψ gψ M hA1 μ hμ hA2 xhat hxhat xs hxs F (fun _ k => η ^ (k + 1))
    (fun _ k => (pow_pos hη0 _).le) x0 x hx
  have hsup : ∀ k, Real.sqrt N * (⨆ _i : Fin N, η ^ (k + 1)) ≤ Real.sqrt N * η ^ (k + 1) := by
    intro k
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      rw [ciSup_const]
  have hrec : ∀ k, u (k + 1) ≤ a * u k + Real.sqrt N * η ^ (k + 1) := fun k =>
    (h20 k).trans (add_le_add le_rfl (hsup k))
  -- unrolled bound
  have hunroll : ∀ k : ℕ, u k ≤ c ^ k * u 0 + Real.sqrt N * (k * c ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hB : 0 ≤ c ^ k * u 0 + Real.sqrt N * (k * c ^ k) := by
        have := hu0 0; positivity
      have hηk : η ^ (k + 1) ≤ c ^ (k + 1) := pow_le_pow_left₀ hη0.le hηc _
      calc u (k + 1) ≤ a * u k + Real.sqrt N * η ^ (k + 1) := hrec k
        _ ≤ c * (c ^ k * u 0 + Real.sqrt N * (k * c ^ k)) + Real.sqrt N * c ^ (k + 1) := by
            exact add_le_add ((mul_le_mul_of_nonneg_left ih ha0).trans
              (mul_le_mul_of_nonneg_right hac hB))
              (mul_le_mul_of_nonneg_left hηk (Real.sqrt_nonneg _))
        _ = c ^ (k + 1) * u 0 + Real.sqrt N * (((k + 1 : ℕ) : ℝ) * c ^ (k + 1)) := by
            push_cast; ring
  -- initial point
  have hinit : u 0 ≤ Real.sqrt N * C := by
    have e : u 0 = blockDist x0 xs := by
      simp only [hu]
      rw [show (fun ω => blockDist (x 0 ω) xs) = fun _ => blockDist x0 xs from
        funext fun ω => by rw [hx.2.1 ω]]
      simp
    rw [e]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [blockDist]
    · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC ⟨0, hN⟩)
      unfold blockDist
      calc Real.sqrt (∑ i : Fin N, ‖x0 i - xs i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin N, C ^ 2) :=
            Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hC i) 2)
        _ = Real.sqrt N * C := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hC0]
  -- Lemma 2
  have hL2 := lemma_2 c q D hc0 hc1 hcq hq1 (le_of_eq hD.symm)
  intro k
  have hkc : (k : ℝ) * c ^ k ≤ D * q ^ k := by
    have := hL2 k (Nat.cast_nonneg k)
    simpa [Real.rpow_natCast] using this
  have hcqk : c ^ k ≤ q ^ k := pow_le_pow_left₀ hc0.le hcq.le _
  have hsN : 0 ≤ Real.sqrt N * C := (hu0 0).trans hinit
  calc u k ≤ c ^ k * u 0 + Real.sqrt N * (k * c ^ k) := hunroll k
    _ ≤ q ^ k * (Real.sqrt N * C) + Real.sqrt N * (D * q ^ k) := by
        exact add_le_add ((mul_le_mul_of_nonneg_right hcqk (hu0 0)).trans
            (mul_le_mul_of_nonneg_left hinit (pow_nonneg (lt_trans hc0 hcq).le _)))
          (mul_le_mul_of_nonneg_left hkc (Real.sqrt_nonneg _))
    _ = Real.sqrt N * (C + D) * q ^ k := by ring
