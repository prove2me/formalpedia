-- Prove2me | solution 1 for GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:12.604074+00:00
-- url     : https://prove2.me/submissions/0d363a8f-288e-4735-b8b5-d3777ba26841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasisStatement
import Theorems.Thm_GlobalTheory_integral_of_sq_sub_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] {ι : Type} [Fintype ι] (b : Module.Basis ι E E'), (∀ i, IsIntegral ℤ (b i)) → ∀ (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E')), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal → ∀ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) → w''.valuation E' ε ≤ 1 := by
  first | exact @GlobalTheory.integral_of_sq_sub_integral | exact GlobalTheory.integral_of_sq_sub_integral | (intros; apply GlobalTheory.integral_of_sq_sub_integral <;> assumption)
end _root_.GlobalTheory.T
