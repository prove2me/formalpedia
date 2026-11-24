-- Prove2me | solution 1 for GlobalTheory.X_smul_mem_gr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:34.384264+00:00
-- url     : https://prove2.me/submissions/d3893c25-68d8-41db-bf85-3afc370b7b66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_X_mem_polyGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
namespace GlobalTheory
theorem _root_.solution (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (i : ι) (n : ℤ) (m : M)
    (hm : m ∈ ℳ n) : (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1) :=
  grSMul_mem ℳ (X_mem_polyGrading i) hm
end GlobalTheory
