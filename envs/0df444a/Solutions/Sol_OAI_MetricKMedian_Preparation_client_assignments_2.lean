-- Prove2me | solution 2 for OAI.MetricKMedian.Preparation.client_assignments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:52:05.608608+00:00
-- url     : https://prove2.me/submissions/0d3e2ac8-1b5b-4a94-a676-d5b66701837a

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_client_assignments_s35

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
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem _root_.solution (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ T₁ g γ B v : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4)
    (hT : 0 < T₁) (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hnearest : ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
    (hV : V t ≤ v) (hD : dist j (s t) ≤ M*v) :
    let p₀ := 1-1/(M*δ)
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        max (farFactor δ p₀ (M/(δ*T₁)) (M/T₁) γ)
          (nearFactor p₀ (M+(1+δ)*T₁) γ g)*v := by
  exact _root_.OAI.MetricKMedian.Preparation.client_assignments_s35 F y s i V G L hy hM hδ hδ1 hT hθ hα hg hγ hunit j t Fj hmj hms hvj hnearest hV hD

end MetricKMedian.Preparation
end
end

end OAI
end

