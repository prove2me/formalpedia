-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:36:51.707231+00:00
-- url     : https://prove2.me/submissions/17103bc5-675a-4caf-827c-cd1ff106072b

import Mathlib
import Definitions.Def_OAIQ035K062
import Theorems.Thm_OAI_MetricKMedian_Preparation_FractionalRefinement_scan_spec_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation.FractionalRefinement
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c b, dist (client c) (i b)=(dc c b:ℝ))
    (hcc : ∀ c c', dist (client c) (client c')=(dd c c':ℝ))
    {η τ : ℝ} (p : RationalAllParameters η τ)

theorem _root_.solution (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin f), scan a k ha hj dc dd df hdc hdd hds i client hdf hc hcc p (k+C)=some O ∧
      O.Nonempty ∧ O.card≤k+C ∧ (Completion.Rational.score dc O:ℝ) ≤
        ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value dc:ℝ) := by
  first
  | exact _root_.OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35
  | (apply _root_.OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35 <;> assumption)

end MetricKMedian.Preparation.FractionalRefinement
end

end OAI
end

