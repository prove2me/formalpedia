-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.mulVec_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:05.67198+00:00
-- url     : https://prove2.me/submissions/f2c7579d-0c3d-4cc7-808f-63dcb50fdef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_frame_orthonormal
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold


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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) :
    Function.Injective (g * frame k r).mulVec := by
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have hF : (frame k r)ᴴ * frame k r = 1 := frame_orthonormal k r hk
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) * (g * frame k r) = 1 := by
    calc ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) * (g * frame k r)
        = (frame k r)ᴴ * ((Hpk k r * (gᴴ * Hpk k r * g)) * frame k r) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hH, Matrix.one_mul, hF]
  intro x y hxy
  have := congrArg (fun v => ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
end GlobalTheory.HCXi.GramPos
