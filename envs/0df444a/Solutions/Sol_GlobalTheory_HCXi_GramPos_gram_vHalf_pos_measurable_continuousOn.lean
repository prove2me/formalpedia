-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:31:47.408327+00:00
-- url     : https://prove2.me/submissions/58c186fd-0cd4-4d44-888f-820356cf526c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_gram_pos
import Theorems.Thm_GlobalTheory_HCXi_GramPos_gram_continuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_gram_measurable

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
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  intro k r hk
  refine ⟨gram_pos k r hk, fun g hg => ?_, ?_, ?_⟩
  · unfold vHalf
    exact mul_pos (Finset.prod_pos fun a _ => inv_pos.mpr (gram_pos k r hk g hg _))
      (Real.rpow_pos_of_pos (gram_pos k r hk g hg _) _)
  · unfold vHalf
    exact (Finset.measurable_prod _ fun a _ => (gram_measurable k r _).inv).mul
      ((gram_measurable k r _).pow_const _)
  · unfold vHalf
    refine ContinuousOn.mul (continuousOn_finsetProd _ fun a _ => ?_) ?_
    · exact (gram_continuous k r _).continuousOn.inv₀ fun g hg => (gram_pos k r hk g hg _).ne'
    · exact (gram_continuous k r _).continuousOn.rpow_const
        fun g hg => Or.inl (gram_pos k r hk g hg _).ne'
end GlobalTheory.HCXi.GramPos
