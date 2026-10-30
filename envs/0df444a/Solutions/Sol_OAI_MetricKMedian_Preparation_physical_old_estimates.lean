-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.physical_old_estimates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:48:03.482997+00:00
-- url     : https://prove2.me/submissions/2155a87a-56b1-4392-9357-4bf2645d21aa

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_physical_old_estimates_s35

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem _root_.solution {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ}
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (L.ν.joint L.κ).expect (fun z => max (1-∑ a, oldAssignment L F z a) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    (L.ν.joint L.κ).expect (fun z => ∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ F, y i*d i)/p₀ := by
  first
  | exact _root_.OAI.MetricKMedian.Preparation.physical_old_estimates_s35
  | (apply _root_.OAI.MetricKMedian.Preparation.physical_old_estimates_s35 <;> assumption)
  | (intros; apply _root_.OAI.MetricKMedian.Preparation.physical_old_estimates_s35 <;> assumption)

end MetricKMedian.Preparation
end
end

end OAI
end

