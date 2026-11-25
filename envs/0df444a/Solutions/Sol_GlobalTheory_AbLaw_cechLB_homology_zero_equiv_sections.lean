-- Prove2me | solution 1 for GlobalTheory.AbLaw.cechLB_homology_zero_equiv_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:26:32.916008+00:00
-- url     : https://prove2.me/submissions/53e918a6-ed01-4945-b4c0-82a3677f837d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBHomologyZeroEquivSections

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
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
      (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), ⨆ i, D i = ⊤ →
      Nonempty ((cechLB f M D).homology 0 ≃ₗ[R] SecOnR f M ⊤) := by
  intro R _ Y f M κ _ _ D hc
  exact ⟨((CochainComplex.isoHomologyπ₀ _).symm ≪≫
      cochainCyclesIsoKer (cechLB f M D) 0 ((cechLB f M D).d 0 1).hom rfl).toLinearEquiv ≪≫ₗ
    (CechOne.kerEquiv M f (fun _ => le_top) hc.ge).symm⟩
end GlobalTheory.AbLaw
