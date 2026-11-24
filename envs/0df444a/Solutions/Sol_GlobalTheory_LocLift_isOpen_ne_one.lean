-- Prove2me | solution 1 for GlobalTheory.LocLift.isOpen_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:14.99858+00:00
-- url     : https://prove2.me/submissions/d1023c9b-5481-4ddf-b346-22c95a92af96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Theorems.Thm_GlobalTheory_LocLift_one_left
import Theorems.Thm_GlobalTheory_LocLift_eq_one_of_mem_range
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem


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
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution [IsSeparated G.hom] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} {x : ∀ b, Over.mk (y b) ⟶ G} (hx : IsHolTo B (fun b => (x b).left)) :
    IsOpen {b ∈ B | x b ≠ 1} := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  let U : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  convert (hx U 0).1 using 3 with b
  refine and_congr_right fun _ => ?_
  rw [top_le_preimage_iff_mem]
  refine not_congr ⟨fun h => ?_, eq_one_of_mem_range _⟩
  beta_reduce
  rw [h, one_left]
  exact ⟨y b (default : PrimeSpectrum ℂ), rfl⟩
end GlobalTheory.LocLift
