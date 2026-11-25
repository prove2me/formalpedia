-- Prove2me | solution 1 for GlobalTheory.OfPeriod.exists_imPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:21.323801+00:00
-- url     : https://prove2.me/submissions/4aa68aa6-7e76-44f5-954a-2e0fb3aa62e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


attribute [local simp] GlobalTheory.OfPeriod.reForm_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
namespace GlobalTheory.OfPeriod
theorem _root_.solution [FiniteDimensional ℝ W] (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) :
    ∃ b : W →ₗ[ℝ] W, (∀ w, b w ∈ R) ∧ ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im := by
  have hnd : ((reForm S).restrict R).Nondegenerate := by
    constructor
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
  refine ⟨R.subtype ∘ₗ (LinearMap.BilinForm.toDual _ hnd).symm.toLinearMap ∘ₗ (imForm S).domRestrict₂ R,
    fun w => Subtype.property _, fun w r hr => Complex.ext ?_ ?_⟩
  · exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) ((imForm S).domRestrict₂ R w) ⟨r, hr⟩
  · exact hR _ (Subtype.property _) r hr
end GlobalTheory.OfPeriod
