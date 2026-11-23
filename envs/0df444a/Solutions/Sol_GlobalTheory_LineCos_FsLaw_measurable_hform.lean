-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.measurable_hform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:28.886079+00:00
-- url     : https://prove2.me/submissions/86afcdb4-8c49-41e2-8416-57c4e95d272c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos
namespace GlobalTheory.LineCos.FsLaw
theorem _root_.solution (G : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℂ → Fin 2 → ℂ} (ha : ∀ i, Measurable fun x => a x i)
    (hb : ∀ i, Measurable fun x => b x i) : Measurable fun x => hform G (a x) (b x) := by
  unfold hform
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((ha i).mul (Complex.continuous_conj.measurable.comp (hb j))).mul_const _
end GlobalTheory.LineCos.FsLaw
