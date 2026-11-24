-- Prove2me | solution 1 for GlobalTheory.ThetaPositivity.exists_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:05.295214+00:00
-- url     : https://prove2.me/submissions/0e077344-5f0e-499b-a15a-668c737fb1bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero
import Theorems.Thm_GlobalTheory_ThetaPositivity_form_add_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma continuous_re_dotProduct_mulVec_star (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous (fun z : Fin g → ℂ => (z ⬝ᵥ Hm.mulVec (star z)).re) :=
  Complex.continuous_re.comp (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))
end GlobalTheory.ThetaPositivity
end

set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.ThetaPositivity
namespace _root_.GlobalTheory.ThetaPositivity
theorem _root_.solution (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Continuous θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) :
    ∃ C : ℝ, ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
  classical
  set F : (Fin g → ℂ) → ℝ := fun z =>
    ‖θ z‖ * Real.exp (-(Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)) with hFdef
  have hF : Continuous F :=
    hθ.norm.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_re_dotProduct_mulVec_star Hm)).neg))
  have hper : ∀ (l : Λ) z, F (z + l) = F z := by
    intro l z
    have hre : ∀ a b : ℂ, ((Real.pi : ℂ) * a + Real.pi / 2 * b).re
        = Real.pi * a.re + Real.pi / 2 * b.re := fun a b => by
      simp [Complex.add_re, Complex.re_ofReal_mul]
    simp only [hFdef, htr, norm_mul, hχ, one_mul, Complex.norm_exp, hre,
      _root_.GlobalTheory.ThetaPositivity.form_add_self hH]
    rw [mul_comm (Real.exp _) ‖θ z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  have hK : IsCompact (closure (ZSpan.fundamentalDomain bR)) :=
    (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun z => ?_⟩
  have hmem : ((ZSpan.floor bR z : Submodule.span ℤ (Set.range bR)) : Fin g → ℂ) ∈ Λ := by
    exact (Module.Basis.ofZLatticeBasis_span ℝ Λ b).le (ZSpan.floor bR z).2
  have hz : F z = F (ZSpan.fract bR z) := by
    have := hper ⟨_, hmem⟩ (ZSpan.fract bR z)
    rw [← this, ZSpan.fract_apply]
    simp
  have hbd : F z ≤ C := by
    rw [hz]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain bR z)))
  have hexp := Real.exp_pos (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)
  calc ‖θ z‖ = F z * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
        rw [hFdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) :=
        mul_le_mul_of_nonneg_right hbd hexp.le
end _root_.GlobalTheory.ThetaPositivity
end GlobalTheory.ThetaPositivity
