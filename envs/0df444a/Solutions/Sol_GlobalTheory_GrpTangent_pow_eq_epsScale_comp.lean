-- Prove2me | solution 1 for GlobalTheory.GrpTangent.pow_eq_epsScale_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:51:57.120548+00:00
-- url     : https://prove2.me/submissions/3c51073d-161d-443b-a95a-ff14ca9e059d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_GrpTangent_epsScale_one
import Theorems.Thm_GlobalTheory_GrpTangent_epsScale_zero_comp
import Theorems.Thm_GlobalTheory_GrpTangent_epsScale_add_comp

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
variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]
namespace GlobalTheory.GrpTangent
theorem _root_.solution {w : epsR R ⟶ G} (hw : IsTangent w) (n : ℕ) :
    w ^ n = epsScale (n : R) ≫ w := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, epsScale_zero_comp hw]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, epsScale_add_comp _ _ hw, ih, epsScale_one, Category.id_comp]
end GlobalTheory.GrpTangent
