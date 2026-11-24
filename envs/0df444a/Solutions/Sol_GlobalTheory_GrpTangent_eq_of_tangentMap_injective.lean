-- Prove2me | solution 1 for GlobalTheory.GrpTangent.eq_of_tangentMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:14.020932+00:00
-- url     : https://prove2.me/submissions/807e6105-f592-434b-86a6-edaa95c16d40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_toFibre_injective
import Theorems.Thm_GlobalTheory_GrpTangent_toFibre_comp
import Theorems.Thm_GlobalTheory_GrpTangent_epsZeroAt_epsBaseAt
import Theorems.Thm_GlobalTheory_GrpTangent_isTangent_toFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.GrpTangent.epsZeroAt_epsBaseAt

set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
variable {k : Type} [CommRing k] (p : Sp k ⟶ S)
variable (f : G ⟶ H) [IsMonHom f]
namespace GlobalTheory.GrpTangent
theorem _root_.solution
    (h : Function.Injective (tangentMap ((Over.pullback p).map f)))
    (w w' : Over.mk (dualBase k ≫ p) ⟶ G) (h₀ : epsZeroAt p ≫ w = epsZeroAt p ≫ w')
    (hf : w ≫ f = w' ≫ f) : w = w' := by
  have := @h ⟨toFibre p (w * w'⁻¹), (isTangent_toFibre p _).mpr (by
      rw [comp_mul, GrpObj.comp_inv, h₀, mul_inv_cancel])⟩
    ⟨toFibre p 1, (isTangent_toFibre p _).mpr (comp_one _)⟩ (Subtype.ext (by
      simp only [tangentMap_coe, ← toFibre_comp]
      rw [mul_comp, GrpObj.inv_comp, hf, mul_inv_cancel, one_comp]))
  exact mul_inv_eq_one.mp (toFibre_injective p (congrArg Subtype.val this))
end GlobalTheory.GrpTangent
