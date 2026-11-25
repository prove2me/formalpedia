-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.ae_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:57.821959+00:00
-- url     : https://prove2.me/submissions/b65a8223-ab24-49a5-9de5-5a7712bcd1ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_continuous_param
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_herm_param

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
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ v ∂coneMeasure n, v ≠ 0 ∧
      herm (Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (-1 : ℂ) else 1)) v v = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [coneMeasure, ae_map_iff (continuous_param n).measurable.aemeasurable]
  · refine ae_restrict_of_ae ?_
    have h0 : ∀ᵐ p : (Fin n → ℂ) × ℝ, p.1 ≠ 0 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : Fin n → ℂ))
    filter_upwards [h0] with p hp
    refine ⟨fun h => hp ?_, herm_param n p⟩
    funext j
    have := congrFun h j.castSucc
    simpa [param] using this
  · refine MeasurableSet.inter (measurableSet_singleton (0 : Fin (n + 1) → ℂ)).compl ?_
    refine (isClosed_eq ?_ continuous_const).measurableSet
    unfold herm
    fun_prop
end GlobalTheory.HCXi.ConeZero
