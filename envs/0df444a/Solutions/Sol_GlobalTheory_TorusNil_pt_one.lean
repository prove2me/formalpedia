-- Prove2me | solution 1 for GlobalTheory.TorusNil.pt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:55.443807+00:00
-- url     : https://prove2.me/submissions/81b3ee01-1e24-44b5-9763-01e63d7b8c34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)
omit [IsOpenImmersion j.left]
include hε
namespace GlobalTheory.TorusNil
theorem _root_.solution (C : Type) [CommRing C] [Algebra A C] :
    spm ((Algebra.ofId A C).comp ε) ≫ j = 1 := by
  rw [spm_comp, Category.assoc, hε, MonObj.comp_one]
end GlobalTheory.TorusNil
