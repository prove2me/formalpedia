-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.loc_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:17.562903+00:00
-- url     : https://prove2.me/submissions/e09c97cb-99aa-49dc-8f2d-7814d830e2c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')) (c : R') (v : Fin P.a → R') (i : P.I) :
    loc P π f' (c • v) i = cst f' _ c * loc P π f' v i := by
  simp only [loc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]
end GlobalTheory.AbLaw.Seesaw
