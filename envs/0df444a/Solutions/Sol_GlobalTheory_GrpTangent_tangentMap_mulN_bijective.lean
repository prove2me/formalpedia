-- Prove2me | solution 1 for GlobalTheory.GrpTangent.tangentMap_mulN_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:02.605909+00:00
-- url     : https://prove2.me/submissions/807017aa-8ed3-43ab-8bed-2ee3598a9e1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_epsScale_one
import Theorems.Thm_GlobalTheory_GrpTangent_isTangent_epsScale
import Theorems.Thm_GlobalTheory_GrpTangent_pow_eq_epsScale_comp
import Theorems.Thm_GlobalTheory_GrpTangent_epsZeroAt_epsBaseAt
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
namespace GlobalTheory.GrpTangent
theorem _root_.solution {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] {n : ℕ} (hn : IsUnit (n : R)) : Function.Bijective (tangentMap (mulN G n)) := by
  obtain ⟨u, hu⟩ := hn
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun w => ⟨epsScale (↑u⁻¹ : R) ≫ w.1, isTangent_epsScale _ w.2⟩, fun w => Subtype.ext ?_,
      fun w => Subtype.ext ?_⟩
  · simp only [tangentMap_coe]
    rw [comp_mulN, pow_eq_epsScale_comp w.2, epsScale_mul_assoc, ← hu, Units.inv_mul, epsScale_one,
      Category.id_comp]
  · simp only [tangentMap_coe]
    rw [comp_mulN, pow_eq_epsScale_comp (isTangent_epsScale _ w.2), epsScale_mul_assoc, ← hu,
      Units.mul_inv, epsScale_one, Category.id_comp]
end GlobalTheory.GrpTangent
