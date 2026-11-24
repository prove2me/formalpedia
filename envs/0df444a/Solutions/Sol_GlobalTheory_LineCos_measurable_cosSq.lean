-- Prove2me | solution 1 for GlobalTheory.LineCos.measurable_cosSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:09.414603+00:00
-- url     : https://prove2.me/submissions/d7f7f2e2-be42-42f3-b4d9-dc771ac49110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have hw : ∀ i, Continuous (fun x : ℂ => lineVec s x i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact continuous_id
    · fin_cases i
      · exact continuous_id
      · exact continuous_const
  have hh : ∀ (b : ℂ → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      Continuous (fun z => hform G (lineVec s z) (b z)) := fun b hb => by
    unfold hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hw i).mul ((Complex.continuous_conj).comp (hb j))).mul continuous_const
  exact ((hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2).measurable.div
    ((Complex.continuous_re.comp (hh _ hw)).mul continuous_const).measurable
end GlobalTheory.LineCos
