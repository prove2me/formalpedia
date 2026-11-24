-- Prove2me | solution 1 for GlobalTheory.QuotientDescent.up_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:30.893677+00:00
-- url     : https://prove2.me/submissions/891a1ae8-4c16-4fd7-aa0f-7e8503567879

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientDescendGrpObj
import Theorems.Thm_GlobalTheory_QuotientDescent_up_left
import Theorems.Thm_GlobalTheory_QuotientDescent_hom_ext
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_isPullback
import Theorems.Thm_GlobalTheory_exists_action_of_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientDescent
variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}
variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}
namespace GlobalTheory.QuotientDescent
theorem _root_.solution (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over X'}
    (hT : Flat T.hom) : Function.Injective (up H : (T ⟶ G') → _) := fun x y e ↦ by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  refine Over.OverMorphism.ext (hq'.hom_ext ?_)
  rw [← up_left H, ← up_left H, e]
end GlobalTheory.QuotientDescent
