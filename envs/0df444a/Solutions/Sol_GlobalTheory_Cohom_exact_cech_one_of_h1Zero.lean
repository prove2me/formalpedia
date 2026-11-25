-- Prove2me | solution 1 for GlobalTheory.Cohom.exact_cech_one_of_h1Zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:32.541042+00:00
-- url     : https://prove2.me/submissions/26ade4f7-ef97-4348-a3ef-9af2a3b0043e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactCechOneOfH1Zero
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_exactAt_one_of_h1Zero
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.Cohom
namespace GlobalTheory.Cohom
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → ⨆ i, D i = ⊤ → FirstCohomologyVanishes M → Function.Exact (Cube.d (secCube f M D) 1) (Cube.d (secCube f M D) 2) :=
  fun _ _ _ f M _ _ _ D hM hc h =>
    (cechComplex_exactAt_succ_iff (secCube f M D) 0).1 (CechOne.exactAt_one_of_h1Zero f hM hc h)
end GlobalTheory.Cohom
