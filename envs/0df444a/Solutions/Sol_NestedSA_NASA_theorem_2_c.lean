-- Prove2me | solution 1 for NestedSA.NASA.theorem_2_c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:54:09.064256+00:00
-- url     : https://prove2.me/submissions/7af25a85-2e85-4af9-bb76-d8328ca47a94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model
import Theorems.Thm_NestedSA_NASA_theorem_2_b

open MeasureTheory ProbabilityTheory
open NestedSA.NASA
open scoped RealInnerProductSpace

/-- The scalar comparison behind (3.37): with `s = √N > 1`, `Σ_{k=1}^{N-1} τ_k = (s²-1)/s` and
`Σ_{k=0}^{N-1} τ_k² = 1 + (s²-1)/s²`. -/
private lemma nasa2c_key (s A E W σh σJ σs : ℝ) (hs : 1 < s) (hA : 0 < A) (hE : 0 ≤ E)
    (hW : 0 ≤ W) (hσh : 0 ≤ σh) :
    1 / ((s ^ 2 - 1) * (1 / s)) *
        ((1 / (A / 4) * E * σh + 2 * σJ ^ 2 * σs ^ 2) * (1 + (s ^ 2 - 1) * (1 / s) ^ 2)
          + 1 / (A / 4) * E * W) ≤
      4 / (s - 1) * (2 / A * E * (W + σh) + σJ ^ 2 * σs ^ 2) := by
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  set Q := E / A with hQ
  have hQ0 : 0 ≤ Q := div_nonneg hE hA.le
  set σ2 := σJ ^ 2 * σs ^ 2 with hσ2
  have hσ20 : 0 ≤ σ2 := by positivity
  have e1 : 1 / (A / 4) * E = 4 * Q := by rw [hQ]; field_simp
  have e2 : 2 / A * E = 2 * Q := by rw [hQ]; field_simp
  have e3 : 2 * σJ ^ 2 * σs ^ 2 = 2 * σ2 := by rw [hσ2]; ring
  rw [e1, e2, e3, show s ^ 2 - 1 = (s - 1) * (s + 1) by ring]
  have hs1' : s - 1 ≠ 0 := hs1.ne'
  have hL : 1 / (((s - 1) * (s + 1)) * (1 / s)) *
        ((4 * Q * σh + 2 * σ2) * (1 + ((s - 1) * (s + 1)) * (1 / s) ^ 2) + 4 * Q * W)
      = ((4 * Q * σh + 2 * σ2) * (2 * s ^ 2 - 1) + 4 * Q * W * s ^ 2) /
          (s * ((s - 1) * (s + 1))) := by
    field_simp
    ring
  have hR : 4 / (s - 1) * (2 * Q * (W + σh) + σ2) =
      (4 * (2 * Q * (W + σh) + σ2) * (s * (s + 1))) / (s * ((s - 1) * (s + 1))) := by
    field_simp
  rw [hL, hR]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg hQ0 hσh, mul_nonneg hQ0 hW, mul_nonneg (mul_nonneg hQ0 hW) hs0.le,
    mul_nonneg (mul_nonneg hQ0 hσh) hs0.le, mul_nonneg hσ20 hs0.le,
    mul_nonneg (mul_nonneg hQ0 hW) (sq_nonneg s)]

theorem solution {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (hF_bdd : BddBelow ((fun x => f (g x)) '' X))
    (hLdf : 0 < Ldf) (α : ℝ) (hα : 0 < α) (N : ℕ) (hN : 2 ≤ N)
    (β : ℝ) (hβ : β = ((1 + α) ^ 2 / α * Lg ^ 2 + α / 4) * Ldf)
    (τ : ℕ → ℝ) (hτ0 : τ 0 = 1) (hτ : ∀ k, 1 ≤ k → τ k = 1 / Real.sqrt N)
    (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P 1 1 β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs) :
    (∀ k, Integrable (fun ω => V P f g (x k ω) (z k ω)) μ) ∧
    (∑ k ∈ Finset.Icc 1 (N - 1), τ k * ∫ ω, V P f g (x k ω) (z k ω) ∂μ) /
        (∑ k ∈ Finset.Icc 1 (N - 1), τ k) ≤
      4 / (Real.sqrt N - 1) *
        (2 / (α * Ldf) * (max (L1 1 Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2)) *
            (W P f g X 1 (α * Ldf) β x0 z0 u0 +
              sigmaHatSq 1 1 (α * Ldf) β Lf Lg Ldf Ldg σG σJ σs z0)
          + σJ ^ 2 * σs ^ 2) := by
  -- basic facts about `t = 1/√N`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / Real.sqrt N := ⟨_, rfl⟩
  simp only [← ht] at hτ
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqN : Real.sqrt 2 ≤ Real.sqrt N := Real.sqrt_le_sqrt hN2
  have hsq2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs1 : 1 < Real.sqrt N := lt_of_lt_of_le hsq2 hsqN
  have hs0 : 0 < Real.sqrt N := by linarith
  have hsN : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hs0]; linarith
  have hτle1 : ∀ k, τ k ≤ 1 := by
    intro k
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [hτ0]
    · rw [hτ k h]; exact ht1
  -- a sample point and the facts about the run
  have hΩ : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨ω0⟩ := hΩ
  have hR := hrun ω0
  have hx0 : x0 ∈ X := hR.x0_mem
  have hβpos : 0 < β := hR.β_pos
  -- the Γ's for `a = 1`
  set q : ℝ := 1 - t with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hGam : ∀ i, 1 ≤ i → Gamma 1 τ i = q ^ (i - 1) := by
    intro i hi
    unfold Gamma Gamma1
    rw [if_pos (by rw [hτ0]; norm_num), one_mul]
    rw [Finset.prod_congr rfl (g := fun _ => q)]
    · rw [Finset.prod_const, Nat.card_Ico]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hτ j hj.1, one_mul]
  have hsumM : ∀ k M : ℕ,
      ∑ i ∈ Finset.Icc (k + 1) (k + M), τ i * Gamma 1 τ i = q ^ k - q ^ (k + M) := by
    intro k M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), ih,
        hτ (k + M + 1) (by omega), hGam (k + M + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      have : t = 1 - q := by rw [hq]; ring
      rw [this]
      ring
  have h330 : ∀ k N' : ℕ, 1 ≤ N' →
      ∑ i ∈ Finset.Icc (k + 1) N', τ i * Gamma 1 τ i ≤ 1 * Gamma 1 τ (k + 1) := by
    intro k N' _
    rw [hGam (k + 1) (by omega), Nat.add_sub_cancel, one_mul]
    rcases le_or_gt N' k with h | h
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      exact pow_nonneg hq0 k
    · obtain ⟨M, rfl⟩ : ∃ M, N' = k + M := ⟨N' - k, by omega⟩
      rw [hsumM k M]
      have := pow_nonneg hq0 (k + M)
      linarith
  have haτ : ∀ k, 1 ≤ k → 1 * τ k ≤ 1 / Real.sqrt 2 := by
    intro k hk
    rw [one_mul, hτ k hk, ht]
    exact one_div_le_one_div_of_le (by positivity) hsqN
  -- the parameter condition (3.16) for `c = αL_∇f/4`, `γ = αL_∇f`
  have h316 : Lg ^ 2 * (1 * Ldf + α * Ldf) ^ 2 ≤
      2 * (1 * β - α * Ldf / 4) * (α * Ldf * 1 - 2 * (α * Ldf / 4)) := by
    apply le_of_eq
    rw [hβ]
    field_simp
    ring
  have hcβ : α * Ldf / 4 ≤ 1 * β := by
    rw [hβ, one_mul]
    have : 0 ≤ (1 + α) ^ 2 / α * Lg ^ 2 * Ldf := by positivity
    nlinarith
  have hcγ : 2 * (α * Ldf / 4) ≤ α * Ldf * 1 := by nlinarith [mul_pos hα hLdf]
  obtain ⟨hint, hbound⟩ := theorem_2_b μ ℱ X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 hF_bdd
    1 1 β τ x0 z0 u0 x z u G s J hrun σG σJ σs hA1 (α * Ldf / 4) (α * Ldf)
    (by positivity) (by positivity) hcβ hcγ h316 hτle1 (fun k => by rw [one_mul]; exact hτle1 k)
    (by rw [hτ0]; norm_num) 1 one_pos h330 haτ N hN
  refine ⟨hint, le_trans hbound ?_⟩
  -- evaluate the stepsize sums
  have hNc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hS : ∑ k ∈ Finset.Icc 1 (N - 1), τ k = (Real.sqrt N ^ 2 - 1) * t := by
    rw [Finset.sum_congr rfl (g := fun _ => t)]
    · rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, hNc, hsN]
    · intro k hk
      rw [Finset.mem_Icc] at hk
      exact hτ k hk.1
  have hT : ∑ k ∈ Finset.range N, τ k ^ 2 =
      1 + (Real.sqrt N ^ 2 - 1) * t ^ 2 := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [show Finset.range N = Finset.range (M + 1) by rw [hM], Finset.sum_range_succ', hτ0]
    rw [Finset.sum_congr rfl (g := fun _ => t ^ 2)]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsN, hM]
      push_cast
      ring
    · intro k _
      rw [hτ (k + 1) (by omega)]
  rw [hS, hT, ht]
  -- nonnegativity of `W(x⁰, z⁰, u⁰)` and of `σ̂²`
  have hW : 0 ≤ W P f g X 1 (α * Ldf) β x0 z0 u0 := by
    unfold W
    have hF : Fstar f g X ≤ f (g x0) := csInf_le hF_bdd ⟨x0, hx0, rfl⟩
    have heta : eta P β x0 z0 ≤ 0 := by
      unfold eta ybar
      set w := x0 - β⁻¹ • z0 with hw
      have hmin := (hP w).2 x0 hx0
      set y := P w
      have hsq : ‖w - y‖ ^ 2 ≤ ‖w - x0‖ ^ 2 := by
        gcongr
      have e1 : w - y = -(β⁻¹ • z0) - (y - x0) := by rw [hw]; abel
      have e2 : w - x0 = -(β⁻¹ • z0) := by rw [hw]; abel
      rw [e1, e2, norm_sub_sq_real, norm_neg, inner_neg_left, inner_smul_left] at hsq
      simp only [RCLike.conj_to_real] at hsq
      have hβi : 0 < β⁻¹ := inv_pos.mpr hβpos
      have h1 : 2 * (β⁻¹ * ⟪z0, y - x0⟫) + ‖y - x0‖ ^ 2 ≤ 0 := by linarith
      have h2 : β / 2 * (2 * (β⁻¹ * ⟪z0, y - x0⟫) + ‖y - x0‖ ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
      have h3 : β / 2 * (2 * (β⁻¹ * ⟪z0, y - x0⟫) + ‖y - x0‖ ^ 2) =
          ⟪z0, y - x0⟫ + β / 2 * ‖y - x0‖ ^ 2 := by
        field_simp
      linarith
    have : 0 ≤ α * Ldf / 2 * ‖g x0 - u0‖ ^ 2 := by positivity
    nlinarith
  have hσh : 0 ≤ sigmaHatSq 1 1 (α * Ldf) β Lf Lg Ldf Ldg σG σJ σs z0 := by
    unfold sigmaHatSq LgradF Leta
    have := hA2.Lf_nonneg
    have := hA2.Lg_nonneg
    have := hA2.Ldg_nonneg
    positivity
  have hE : 0 ≤ max (L1 1 Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2) := by
    have : 0 ≤ L2 Lg Ldf := by unfold L2; positivity
    have h1 := le_max_right (L1 1 Lf Lg Ldf Ldg) (L2 Lg Ldf)
    have h2 := le_max_left (1 : ℝ) (β ^ 2)
    linarith
  have key := nasa2c_key (Real.sqrt N) (α * Ldf)
    (max (L1 1 Lf Lg Ldf Ldg) (L2 Lg Ldf) + max 1 (β ^ 2))
    (W P f g X 1 (α * Ldf) β x0 z0 u0) (sigmaHatSq 1 1 (α * Ldf) β Lf Lg Ldf Ldg σG σJ σs z0)
    σJ σs hs1 (mul_pos hα hLdf) hE hW hσh
  refine le_trans (le_of_eq ?_) key
  ring
