-- Prove2me | solution 1 for GhadimiLan.RSG.theorem_2_1_a
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T22:53:19.823092+00:00
-- url     : https://prove2.me/submissions/248a274a-2934-4e0e-865e-bde470874908

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Theorems.Thm_GhadimiLan_RSG_eq_2_11
import Theorems.Thm_GhadimiLan_RSG_weighting_identity
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Theorem 2.1 a), Eq. (2.4) (Ghadimi & Lan, arXiv:1309.5549v1, p. 6), as a reduction to
Eq. (2.11) and the weighting identity. From (2.11), each `‖∇f(x_k)‖²` is integrable and
`Σ_k (γ_k − (L/2)γ_k²) E‖∇f(x_k)‖² ≤ f(x_1) − f* + (Lσ²/2) Σ_k γ_k²`. The weighting identity
(applied to the noise sequence modified at the unused index `0` so that every `ξ' k` is
measurable; the run and the independence hypothesis transfer because only `k ≥ 1` is used)
gives integrability of `‖∇f(x_R)‖²` and
`E‖∇f(x_R)‖² = Σ_k (2γ_k − Lγ_k²) E‖∇f(x_k)‖² / Σ_k (2γ_k − Lγ_k²)`. Since
`2γ_k − Lγ_k² = 2(γ_k − (L/2)γ_k²)`, `D_f² = 2(f(x_1) − f*)/L` and the denominator is
positive, the bound (2.4) follows by real arithmetic. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ)
    (R : Ω → ℕ) (hR : IsRandomOutputIndex μ R L γ N)
    (hRind : IndepFun R (fun ω k => ξ k ω) μ) :
    Integrable (fun ω => ‖g (x (R ω) ω)‖ ^ 2) μ ∧
    1 / L * ∫ ω, ‖g (x (R ω) ω)‖ ^ 2 ∂μ ≤
      (Df f x1 fstar L ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) /
        ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by
  -- Step 1: Eq. (2.11)
  obtain ⟨hint, h211⟩ :=
    eq_2_11 f g L hf hL fstar hfstar G hG μ ℱ ξ σ N hN γ hγ x1 x hx hA1
  -- Step 2: a globally measurable modification of the noise (ξ 0 is unused)
  have hmeas : ∀ j, 1 ≤ j → Measurable (ξ j) := fun j hj =>
    (hA1.adapted j hj).mono (ℱ.le j) le_rfl
  set ξ' : ℕ → Ω → Ξ := fun k ω => if k = 0 then ξ 1 ω else ξ k ω with hξ'
  have hξ'meas : ∀ k, Measurable (ξ' k) := by
    intro k
    by_cases hk : k = 0
    · simp only [hξ', hk, if_true]
      exact hmeas 1 le_rfl
    · simp only [hξ', hk, if_false]
      exact hmeas k (Nat.one_le_iff_ne_zero.mpr hk)
  have hx' : IsRSGRun G γ x1 ξ' x := by
    refine ⟨hx.1, fun k hk ω => ?_⟩
    have hk0 : k ≠ 0 := by omega
    simp only [hξ', hk0, if_false]
    exact hx.2 k hk ω
  have hRind' : IndepFun R (fun ω k => ξ' k ω) μ := by
    let Φ : (ℕ → Ξ) → (ℕ → Ξ) := fun s k => if k = 0 then s 1 else s k
    have hΦ : Measurable Φ := by
      refine measurable_pi_lambda _ (fun k => ?_)
      by_cases hk : k = 0
      · simp only [Φ, hk, if_true]
        exact measurable_pi_apply 1
      · simp only [Φ, hk, if_false]
        exact measurable_pi_apply k
    exact hRind.comp measurable_id hΦ
  -- Step 3: the weighting identity
  obtain ⟨hintR, hid⟩ :=
    weighting_identity f g L hf hL G hG μ ξ' hξ'meas N hN γ hγ x1 x hx' R hR hRind' hint
  refine ⟨hintR, ?_⟩
  rw [hid]
  -- Step 4: real arithmetic
  have hS : 0 < ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by
    apply Finset.sum_pos
    · intro k hk
      obtain ⟨h0, h2⟩ := hγ k hk
      have : L * γ k < 2 := by
        have := (lt_div_iff₀ hL).mp h2
        linarith
      nlinarith
    · exact Finset.nonempty_Icc.mpr hN
  have hA : ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ
      = 2 * ∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hDf : Df f x1 fstar L ^ 2 = 2 * (f x1 - fstar) / L := by
    unfold Df
    apply Real.sq_sqrt
    apply div_nonneg _ hL.le
    have := hfstar.1 ⟨x1, rfl⟩
    linarith
  rw [hA, hDf]
  calc 1 / L * (2 * (∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ)
        / ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2))
      = (2 * (∑ k ∈ Finset.Icc 1 N, (γ k - L / 2 * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) / L)
        / ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by ring
    _ ≤ (2 * (f x1 - fstar + L * σ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) / L)
        / ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by
        apply div_le_div_of_nonneg_right _ hS.le
        apply div_le_div_of_nonneg_right _ hL.le
        linarith
    _ = (2 * (f x1 - fstar) / L + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2)
        / ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by
        congr 1
        field_simp
