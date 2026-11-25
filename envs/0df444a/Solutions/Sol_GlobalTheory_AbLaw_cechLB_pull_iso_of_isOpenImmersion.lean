-- Prove2me | solution 1 for GlobalTheory.AbLaw.cechLB_pull_iso_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:10.205004+00:00
-- url     : https://prove2.me/submissions/77b62bf7-146b-4005-af6b-388466f6aeaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBPullIsoOfIsOpenImmersion
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_pullLE_bijective_of_le_opensRange
import Theorems.Thm_GlobalTheory_AbLaw_secCubePull_res
import Theorems.Thm_GlobalTheory_IsGradedMap_id
import Theorems.Thm_GlobalTheory_isIso_cechComplexMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (Y' : Scheme.{0}) (e : Y' ⟶ Y) [IsOpenImmersion e] (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → (∀ i, D i ≤ e.opensRange) → Nonempty (cechLB (e ≫ f) (M.pull e) (fun i => e ⁻¹ᵁ D i) ≅ cechLB f M D) := by
  intro R _ Y f M Y' e _ κ _ _ D _ hD
  have w : e ≫ f = (e ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  let φ : secCube f M D ⟶ secCube (e ≫ f) (M.pull e) fun i => e ⁻¹ᵁ D i :=
    GlobalTheory.Cube.homMk (fun s => secCubePull M D w s) fun h x => secCubePull_res D w h x
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ fun s ⟨i, hi⟩ =>
    SecOn.pullLE_bijective_of_le_opensRange M e ((biInf_le D hi).trans (hD i))
      (preimage_biInf D e s).ge (preimage_biInf D e s).le
  exact ⟨(asIso (cechComplexMap φ)).symm⟩
end GlobalTheory.AbLaw
