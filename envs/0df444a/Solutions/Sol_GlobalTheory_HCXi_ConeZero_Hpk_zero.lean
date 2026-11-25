-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.Hpk_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:07:44.402627+00:00
-- url     : https://prove2.me/submissions/beec1c59-a3d0-4050-b157-e7da67df61b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero
namespace GlobalTheory.HCXi.ConeZero
theorem _root_.solution (k : ℕ) : Hpk k 0 = Matrix.diagonal
    (fun i : Fin (2 * 0 + k + 1) => if i = Fin.last (2 * 0 + k) then (-1 : ℂ) else 1) := by
  ext i j
  have hi := i.isLt
  by_cases h : i = j
  · subst h
    simp only [Hpk, diagonal_apply_eq, Fin.ext_iff, Fin.val_last]
    have : i.val ≤ 0 + k := by omega
    simp [show i.val ≤ k by omega]
  · simp [Hpk, h]
end GlobalTheory.HCXi.ConeZero
