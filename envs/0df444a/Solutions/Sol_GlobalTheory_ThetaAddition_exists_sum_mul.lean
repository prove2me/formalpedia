-- Prove2me | solution 1 for GlobalTheory.ThetaAddition.exists_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:40.938655+00:00
-- url     : https://prove2.me/submissions/9a186e35-5ca3-4af8-9a62-ce20ba22881c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AdditionLevelTwoMul
import Theorems.Thm_GlobalTheory_EvaluationSpanTopToricGeometry_exists_sum_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAddition
namespace GlobalTheory.ThetaAddition
theorem _root_.solution {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (h1 : ∀ y, (fun x => F x y) ∈ V)
    (h2 : ∀ x, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ), (∀ i, h i ∈ V ∧ k i ∈ L) ∧
      ∀ x y, F x y = ∑ i, h i x * k i y := by
  first
  | exact @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | (apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul ..)
end GlobalTheory.ThetaAddition
