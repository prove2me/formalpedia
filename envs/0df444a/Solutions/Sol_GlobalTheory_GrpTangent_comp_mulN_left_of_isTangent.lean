-- Prove2me | solution 1 for GlobalTheory.GrpTangent.comp_mulN_left_of_isTangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:01.858527+00:00
-- url     : https://prove2.me/submissions/615fd125-6627-48ba-8340-c697620e026e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_pow_eq_epsScale_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
    {w : epsR R ⟶ G} (hw : IsTangent w) (n : ℕ) :
    (w ≫ mulN G n).left = spMap (epsScaleR (n : R)) ≫ w.left := by
  rw [comp_mulN, pow_eq_epsScale_comp hw]; rfl
end GlobalTheory.GrpTangent
