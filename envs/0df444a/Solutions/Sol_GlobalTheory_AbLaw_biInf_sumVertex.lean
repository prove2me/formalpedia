-- Prove2me | solution 1 for GlobalTheory.AbLaw.biInf_sumVertex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:11:04.830221+00:00
-- url     : https://prove2.me/submissions/662768e2-dc3f-421c-8f1c-815acf4c0413

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe

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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}
namespace GlobalTheory.AbLaw
theorem _root_.solution [LinearOrder ν] [LinearOrder κ] (E : ν ⊕ₗ κ → Y.Opens) (s : Finset ν)
    (t : Finset κ) : ⨅ i ∈ Cube.sumVertex s t, E i =
      (⨅ i ∈ s, E (toLex (Sum.inl i))) ⊓ ⨅ k ∈ t, E (toLex (Sum.inr k)) := by
  apply le_antisymm
  · exact le_inf (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inl_mem_sumVertex.2 hi))
      (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inr_mem_sumVertex.2 hi))
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨i | i, rfl⟩ := toLex.surjective i
    · exact inf_le_left.trans (iInf₂_le _ (Cube.inl_mem_sumVertex.1 hi))
    · exact inf_le_right.trans (iInf₂_le _ (Cube.inr_mem_sumVertex.1 hi))
end GlobalTheory.AbLaw
