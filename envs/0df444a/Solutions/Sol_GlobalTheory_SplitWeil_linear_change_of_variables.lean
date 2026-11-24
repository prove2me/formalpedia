-- Prove2me | solution 1 for GlobalTheory.SplitWeil.linear_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:17.407798+00:00
-- url     : https://prove2.me/submissions/ea863c69-09ec-4b3f-9d03-bcd154803406

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mulVec_eq_smul
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mul_mul_volM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩
end GlobalTheory.SplitWeil
