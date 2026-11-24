-- Prove2me | solution 1 for GlobalTheory.QuotientDescent.Equivariant.exists_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:29.949127+00:00
-- url     : https://prove2.me/submissions/49a73f97-5247-46b6-a281-8a982c067481

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
namespace Equivariant
theorem _root_.solution (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hτ : ∀ g, (τ g).hom ≫ φ = φ) {T : Over X'} (hT : Flat T.hom)
    {w : (Over.pullback π).obj T ⟶ G} (hw : Equivariant ρ τ w) : ∃ z : T ⟶ G', up H z = w := by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  obtain ⟨z, hz⟩ := hq'.exists_comp_eq (w.left ≫ φ) fun g ↦ by
    rw [← Category.assoc, hw g _ (hσ g).1 (hσ g).2, Category.assoc, hτ]
  refine ⟨Over.homMk z (hq'.hom_ext ?_), hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))
end Equivariant
end GlobalTheory.QuotientDescent
