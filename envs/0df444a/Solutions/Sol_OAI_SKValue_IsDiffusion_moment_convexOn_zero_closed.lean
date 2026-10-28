-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.moment_convexOn_zero_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:55:32.455982+00:00
-- url     : https://prove2.me/submissions/24c6972b-aff5-4603-92d1-02acafad43a4

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_curvatureExpr_hasDerivAt
import Theorems.Thm_OAI_SKValue_IsDiffusion_gradientMoment_continuous
import Theorems.Thm_OAI_SKValue_IsDiffusion_momentExpr_hasDerivAt

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_PolynomialMoment
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
namespace JetExpr
lemma momentExpr_eval (R:ℕ → ℝ):eval R momentExpr=(R 0)^2 := by simp only [momentExpr,square,eval,pow_two]
lemma curvatureSlope_eval (R:ℕ → ℝ) (c:ℝ):eval R (curvatureSlope c)=(R 2)^2-2*c*(R 1)^3 := by
  simp only [curvatureSlope,square,cube,eval];ring
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_CurvatureMoment
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma continuousAt_of_constant_interval {f:ℝ → ℝ} {a b c t:ℝ}
    (ht:t∈Ioo a b) (he:∀s∈Ioo a b,f s=c):ContinuousAt f t := by
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact he s hs
lemma momentExpr_eq_gradientMoment (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ):
    jetMoment W γ X JetExpr.momentExpr=gradientMoment W γ X := by
  funext t
  simp only [jetMoment,polyJet,JetExpr.momentExpr_eval,iteratedDeriv_zero,gradientMoment,gradient]
lemma IsDiffusion.moment_convexOn_zero_closed_oai {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {a b:ℝ} (ha:0≤a) (hb:b<1)
    (he:∀t∈Ioo a b,γ.coeff t=0):ConvexOn ℝ (Icc a b) (gradientMoment W γ X) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (f':=jetMoment W γ X JetExpr.curvatureExpr) (f'':=jetMoment W γ X (JetExpr.curvatureSlope 0))
  · exact hX.gradientMoment_continuous.mono (fun t ht ↦ ⟨ha.trans ht.1,ht.2.trans_lt hb⟩)
  · intro t ht
    rw [interior_Icc] at ht
    simpa only [momentExpr_eq_gradientMoment] using
      (hX.momentExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans hb⟩
        (continuousAt_of_constant_interval ht he)).hasDerivWithinAt (s:=interior (Icc a b))
  · intro t ht
    rw [interior_Icc] at ht
    exact (hX.curvatureExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    simp only [jetMoment,polyJet,JetExpr.curvatureSlope_eval,mul_zero,zero_mul,sub_zero]
    exact integral_nonneg (fun z ↦ sq_nonneg _)
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.moment_convexOn_zero_closed_oai := @OAI.SKValue.IsDiffusion.moment_convexOn_zero_closed_oai
