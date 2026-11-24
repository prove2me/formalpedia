-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension.sum_ulift_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:39:59.050791+00:00
-- url     : https://prove2.me/submissions/36fa2259-e1c7-4fa9-a707-b424e58275db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
theorem _root_.solution (f : ULift.{u} (Fin 3) → ℤ) : ∑ k, f k = f ⟨0⟩ + f ⟨1⟩ + f ⟨2⟩ := by
  rw [← Equiv.ulift.symm.sum_comp, Fin.sum_univ_three]; rfl
end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
