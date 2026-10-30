-- Prove2me | solution 1 for OAI.MetricKMedian.GeneratorAverage.expanded_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:52:15.496929+00:00
-- url     : https://prove2.me/submissions/c5276668-4395-419f-b2db-24d7b82e4497

import Mathlib
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_expanded_bound_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem _root_.solution (μ : FiniteLaw Ω) {g x y pHat b : ℝ}
    (d N s : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i, 0 ≤ d i) (hysum : ∑ _i : I, g=y)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hincoming : ∀ i, ∑ h, g*qE h i ≤ 1)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t)
    (hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
      (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i)
        (GraphMoments.kernel g qE) x y pHat+Analytic.B x*g*V := by
  first
  | exact _root_.OAI.MetricKMedian.GeneratorAverage.expanded_bound_s35
  | (apply _root_.OAI.MetricKMedian.GeneratorAverage.expanded_bound_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.GeneratorAverage.expanded_bound_s35 <;> assumption)

end MetricKMedian.GeneratorAverage
end
end

end OAI
end

