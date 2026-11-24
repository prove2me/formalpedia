-- Prove2me | solution 1 for GlobalTheory.OrbCpt.det_hm_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:29.804623+00:00
-- url     : https://prove2.me/submissions/9acd533e-6184-4105-9987-f998509666de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_hm_self

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
theorem _root_.solution {p : k[X]} (hp : p.Separable) {X : Matrix (Fin r) (Fin r) k}
    (hX : aeval X p = 0) : (hm p X X).det ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hp
  have h := congrArg (aeval X) huv
  rw [map_add, map_mul, map_mul, hX, mul_zero, zero_add, map_one] at h
  rw [hm_self]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero
end GlobalTheory.OrbCpt
