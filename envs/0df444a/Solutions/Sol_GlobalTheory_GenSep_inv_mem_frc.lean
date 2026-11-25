-- Prove2me | solution 1 for GlobalTheory.GenSep.inv_mem_frc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:28:28.425481+00:00
-- url     : https://prove2.me/submissions/50c5bdea-4de3-4cf5-b9f7-3da2aed0be6f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')
namespace GlobalTheory.GenSep
theorem _root_.solution (A : Subring (F × F')) {y : F} {y' : F'} (h : (y, y') ∈ frc A) (hy : y ≠ 0) (hy' : y' ≠ 0) :
    (y⁻¹, y'⁻¹) ∈ frc A := by
  obtain ⟨d, hd, d1, d2, hz⟩ := h
  refine ⟨d * (y, y'), hz, mul_ne_zero d1 hy, mul_ne_zero d2 hy', ?_⟩
  have : d * (y, y') * (y⁻¹, y'⁻¹) = d := by
    ext <;> simp [hy, hy']
  rwa [this]
end GlobalTheory.GenSep
