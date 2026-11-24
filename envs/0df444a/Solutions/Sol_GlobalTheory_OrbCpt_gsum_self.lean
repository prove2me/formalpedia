-- Prove2me | solution 1 for GlobalTheory.OrbCpt.gsum_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:26.389877+00:00
-- url     : https://prove2.me/submissions/2f5a9283-3415-4763-9f77-864af27e225b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer

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
theorem _root_.solution (X : Matrix (Fin r) (Fin r) k) (m : ℕ) :
    gsum X X (m + 1) = ((m + 1 : ℕ) : k) • X ^ m := by
  induction m with
  | zero => simp [gsum]
  | succ m ih =>
    rw [gsum, ih, smul_mul_assoc, ← pow_succ, Nat.cast_succ (m + 1), add_smul, one_smul, add_comm]
end GlobalTheory.OrbCpt
