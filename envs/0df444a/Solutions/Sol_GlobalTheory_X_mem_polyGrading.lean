-- Prove2me | solution 1 for GlobalTheory.X_mem_polyGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:01.3378+00:00
-- url     : https://prove2.me/submissions/7297a24a-bd93-4a32-b878-d1bd06304513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination

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
variable (ι : Type*) (R : Type*) [CommRing R]
variable {ι R}
namespace GlobalTheory
theorem _root_.solution (i : ι) : (X i : MvPolynomial ι R) ∈ polyGrading ι R 1 :=
  mem_polyGrading_natCast (d := 1).2 (isHomogeneous_X R i)
end GlobalTheory
