-- Prove2me | solution 1 for GlobalTheory.OrbCpt.gsum_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:25.193194+00:00
-- url     : https://prove2.me/submissions/cc3e8351-7d54-4074-87cb-1bb961ff6a96

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
theorem _root_.solution (X Y : Matrix (Fin r) (Fin r) k) (m : ℕ) :
    X * gsum X Y m - gsum X Y m * Y = X ^ m - Y ^ m := by
  induction m with
  | zero => simp [gsum]
  | succ m ih =>
    have h : X * gsum X Y m = gsum X Y m * Y + (X ^ m - Y ^ m) := by rw [← ih]; abel
    simp only [gsum, mul_add, add_mul, ← mul_assoc, h]
    rw [pow_succ' X m, pow_succ Y m]
    noncomm_ring
end GlobalTheory.OrbCpt
