-- Prove2me | solution 1 for GlobalTheory.AbLaw.firstCohomologyVanishes_of_exact_secCube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:40.96146+00:00
-- url     : https://prove2.me/submissions/3b01125f-7eb7-4010-b880-2293a02c2249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FirstCohomologyVanishesOfExactSecCube
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_h1Zero_of_exactAt_one
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
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hM : M.IsLB) (hc : ⨆ i, D i = ⊤) (hA : ∀ i, IsAffineOpen (D i))
    (h : Function.Exact (Cube.d (secCube f M D) 1) (Cube.d (secCube f M D) 2)) : FirstCohomologyVanishes M :=
  CechOne.h1Zero_of_exactAt_one f hM hc hA
    ((cechComplex_exactAt_succ_iff (secCube f M D) 0).2 h)
end GlobalTheory.AbLaw
