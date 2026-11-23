-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.mem_basicOpen_cst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:13.639435+00:00
-- url     : https://prove2.me/submissions/a973b03d-a444-4ebc-bfd9-aadcd0aeecb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_mem_basicOpen_rs

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
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) {x : X} (hx : x ∈ W) :
    x ∈ X.basicOpen (cst f W r) ↔ r ∉ (f x).asIdeal := by
  refine (mem_basicOpen_rs le_top _ hx).trans ?_
  have e₁ := f.preimage_basicOpen_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₂ := basicOpen_eq_of_affine (R := CommRingCat.of R) r
  refine (congrArg (x ∈ ·) e₁).to_iff.symm.trans ?_
  exact (congrArg (f x ∈ ·) e₂).to_iff
end GlobalTheory.AbLaw.Seesaw
