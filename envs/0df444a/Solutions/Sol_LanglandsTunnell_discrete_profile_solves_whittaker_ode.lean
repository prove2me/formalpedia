-- Prove2me | solution 1 for LanglandsTunnell.discrete_profile_solves_whittaker_ode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ae2201ff-465d-53d2-bbc5-184fbcf0dedd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_discrete_profile_solves_whittaker_ode

set_option autoImplicit false

open scoped Real
open Filter Topology

private noncomputable def wProf (a : ℝ) (y : ℝ) : ℝ := 2 * y ^ a * Real.exp (-(2 * π * y))

private noncomputable def wProf₁ (a : ℝ) (y : ℝ) : ℝ :=
  2 * (a * y ^ (a - 1)) * Real.exp (-(2 * π * y)) + 2 * y ^ a * (Real.exp (-(2 * π * y)) * (-(2 * π)))

private noncomputable def wProf₂ (a : ℝ) (y : ℝ) : ℝ :=
  (2 * (a * ((a - 1) * y ^ (a - 1 - 1))) * Real.exp (-(2 * π * y))
      + 2 * (a * y ^ (a - 1)) * (Real.exp (-(2 * π * y)) * (-(2 * π))))
    + (2 * (a * y ^ (a - 1)) * (Real.exp (-(2 * π * y)) * (-(2 * π)))
      + 2 * y ^ a * ((Real.exp (-(2 * π * y)) * (-(2 * π))) * (-(2 * π))))

private lemma hasDerivAt_expNeg (y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(2 * π * y))) (Real.exp (-(2 * π * y)) * (-(2 * π))) y := by
  have h : HasDerivAt (fun y : ℝ => -(2 * π * y)) (-(2 * π)) y := by
    have h__af := ((hasDerivAt_id y).const_mul (2 * π)).neg
    simp at h__af
    exact h__af
  exact h.exp

private lemma hasDerivAt_wProf (a : ℝ) {y : ℝ} (hy : 0 < y) : HasDerivAt (wProf a) (wProf₁ a y) y := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y ^ a) (2 * (a * y ^ (a - 1))) y :=
    (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul 2
  exact h1.mul (hasDerivAt_expNeg y)

private lemma hasDerivAt_wProf₁ (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (wProf₁ a) (wProf₂ a y) y := by
  have hA : HasDerivAt (fun y : ℝ => 2 * (a * y ^ (a - 1))) (2 * (a * ((a - 1) * y ^ (a - 1 - 1)))) y :=
    ((Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul a).const_mul 2
  have hB : HasDerivAt (fun y : ℝ => 2 * y ^ a) (2 * (a * y ^ (a - 1))) y :=
    (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul 2
  have hE := hasDerivAt_expNeg y
  have hE' : HasDerivAt (fun y : ℝ => Real.exp (-(2 * π * y)) * (-(2 * π)))
      (Real.exp (-(2 * π * y)) * (-(2 * π)) * (-(2 * π))) y := hE.mul_const _
  exact (hA.mul hE).add (hB.mul hE')

private lemma wProf_ode (n : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ 2 * wProf₂ (((n : ℝ) + 1) / 2) y
      + (1 / 4 - ((n : ℝ) / 2) ^ 2 + 2 * π * ((n : ℝ) + 1) * y - 4 * π ^ 2 * y ^ 2)
          * wProf (((n : ℝ) + 1) / 2) y = 0 := by
  have hy0 : y ≠ 0 := hy.ne'
  simp only [wProf, wProf₂]
  rw [Real.rpow_sub_one hy0, Real.rpow_sub_one hy0]
  field_simp [hy0]
  ring

private lemma profile_eq (n : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ (1 / 2 : ℝ) * (2 * y ^ ((n : ℝ) / 2) * Real.exp (-(2 * π * y))) = wProf (((n : ℝ) + 1) / 2) y := by
  simp only [wProf]
  have : ((n : ℝ) + 1) / 2 = 1 / 2 + (n : ℝ) / 2 := by ring
  rw [this, Real.rpow_add hy]
  ring

theorem solution (n : ℕ) (k : ℝ) (ν : ℂ) (hk : k = n + 1)
    (hν : ν = (n : ℂ) / 2) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = ((y ^ (1 / 2 : ℝ) * (2 * y ^ ((n : ℝ) / 2) * Real.exp (-(2 * π * y))) : ℝ) : ℂ)) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by

  have hfe : ∀ {y : ℝ}, 0 < y → f =ᶠ[𝓝 y] fun z : ℝ => ((wProf (((n : ℝ) + 1) / 2) z : ℝ) : ℂ) := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with z hz
    rw [hf z, profile_eq n hz]

  have hD1 : ∀ {y : ℝ}, 0 < y → HasDerivAt f ((wProf₁ (((n : ℝ) + 1) / 2) y : ℝ) : ℂ) y := fun hy =>
    ((hasDerivAt_wProf _ hy).ofReal_comp).congr_of_eventuallyEq (hfe hy)

  have hde : ∀ {y : ℝ}, 0 < y → deriv f =ᶠ[𝓝 y] fun z : ℝ => ((wProf₁ (((n : ℝ) + 1) / 2) z : ℝ) : ℂ) := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact (hD1 hz).deriv
  have hD2 : ∀ {y : ℝ}, 0 < y → HasDerivAt (deriv f) ((wProf₂ (((n : ℝ) + 1) / 2) y : ℝ) : ℂ) y := fun hy =>
    ((hasDerivAt_wProf₁ _ hy).ofReal_comp).congr_of_eventuallyEq (hde hy)
  refine ⟨fun y hy => (hD1 hy).differentiableAt.differentiableWithinAt,
    fun y hy => (hD2 hy).differentiableAt.differentiableWithinAt, fun y hy => ?_⟩
  rw [(hD2 hy).deriv, hf y, profile_eq n hy, hk, hν]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (wProf_ode n hy)
  push_cast at h ⊢
  linear_combination h

end S_LanglandsTunnell_discrete_profile_solves_whittaker_ode
end P2MW
export P2MW.S_LanglandsTunnell_discrete_profile_solves_whittaker_ode (solution)
