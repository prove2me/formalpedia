-- Prove2me | solution 1 for GlobalTheory.HermLocal.Model.exists_cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:52.856848+00:00
-- url     : https://prove2.me/submissions/623a8b7a-ae9d-4a04-87a4-d51cc8c1383a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal
open GlobalTheory GlobalTheory.HermLocal GlobalTheory.HermLocal.Model
namespace GlobalTheory.HermLocal.Model
theorem _root_.solution : ∃ _ : IsCMField (CyclotomicField 4 ℚ),
    Nonempty (HeightOneSpectrum (𝓞 (maximalRealSubfield (CyclotomicField 4 ℚ)))) := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) := by
    have h : @IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) _ _ (CyclotomicField.algebra 4 ℚ) :=
      inferInstance
    convert h
    exact Subsingleton.elim _ _
  refine ⟨IsCyclotomicExtension.Rat.isCMField _ (S := {4}) ⟨4, rfl, by norm_num⟩, ?_⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 (maximalRealSubfield (CyclotomicField 4 ℚ)))
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField _)⟩⟩
end GlobalTheory.HermLocal.Model
