-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.gram_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:24:57.190014+00:00
-- url     : https://prove2.me/submissions/d66e902c-c76b-4753-a6a7-789c6c153935

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_mulVec_inj

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.GramPos
namespace GlobalTheory.HCXi.GramPos
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) (a : Fin (r + 1)) :
    0 < gram k r g a := by
  have hP : ((g * frame k r)ᴴ * (g * frame k r)).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ (mulVec_inj k r hk g hg)
  have hS := hP.submatrix (Fin.castLE_injective (Nat.succ_le_of_lt a.isLt))
  have hd := hS.det_pos
  exact (Complex.pos_iff.mp hd).1
end GlobalTheory.HCXi.GramPos
