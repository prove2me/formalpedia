-- Prove2me | solution 1 for GlobalTheory.TorusNil.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:11.5918+00:00
-- url     : https://prove2.me/submissions/6019d05d-3c2c-4a84-b442-3bbf2824d870

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_injective

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
omit [GrpObj B]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C : Type} [CommRing C] [Algebra A C] {φ ψ : R →ₐ[A] C}
    (h : spm φ ≫ j = spm ψ ≫ j) : φ = ψ := by
  apply spm_injective
  apply Over.OverMorphism.ext
  rw [← cancel_mono j.left, ← Over.comp_left, h, Over.comp_left]
end GlobalTheory.TorusNil
