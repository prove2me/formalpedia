-- Prove2me | solution 1 for GlobalTheory.OrbCpt.hm_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:42.853917+00:00
-- url     : https://prove2.me/submissions/23ae4259-62c5-44ba-af7a-fd76d69da4e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_gsum_inter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
namespace GlobalTheory.OrbCpt
theorem _root_.solution (p : k[X]) (X Y : Matrix (Fin r) (Fin r) k) :
    X * hm p X Y - hm p X Y * Y = aeval X p - aeval Y p := by
  have h1 : p.natDegree < p.natDegree + 2 := by omega
  rw [aeval_eq_sum_range' h1, aeval_eq_sum_range' h1, hm, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, gsum_inter, smul_sub]
end GlobalTheory.OrbCpt
