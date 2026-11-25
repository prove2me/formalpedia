-- Prove2me | solution 1 for GlobalTheory.SecPow.exists_finite_affine_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:48:08.139531+00:00
-- url     : https://prove2.me/submissions/e8599700-2c52-4358-b2f6-a9eb35be9ed9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.SecPow
variable {X X' : Scheme.{0}}
namespace GlobalTheory.SecPow
theorem _root_.solution [CompactSpace X] {H : LB X} (hH : H.IsLB) :
    ∃ (I : Type) (_ : Finite I) (V : I → X.Opens) (c : I → H.ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ H.U (c a)) ∧ ⊤ ≤ ⨆ a, V a := by
  have h : ∀ x : X, ∃ (V : X.Opens) (i : H.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ H.U i := fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (H.U i).isOpen
    exact ⟨V, i, hV, hx, hle⟩
  choose V c hV hx hle using h
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨S, inferInstance, fun a => V a, fun a => c a, fun a => hV a, fun a => hle a, fun x _ => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
end GlobalTheory.SecPow
