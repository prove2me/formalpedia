-- Prove2me | solution 1 for GlobalTheory.xProd_smul_bijective_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:53:16.49515+00:00
-- url     : https://prove2.me/submissions/fd95f3af-239f-406e-bfdf-b0a3670b4f41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R) N]
    (s : Finset ι) (h : ∀ i ∈ s, Function.Bijective fun m : N => (X i : MvPolynomial ι R) • m) :
    Function.Bijective fun m : N => xProd R s • m := by
  refine Finset.prod_induction _ (fun p : MvPolynomial ι R => Function.Bijective fun m : N => p • m)
    (fun p q hp hq => ?_) ?_ h
  · simp only [mul_smul]
    exact hp.comp hq
  · simp only [one_smul]
    exact Function.bijective_id
end GlobalTheory
