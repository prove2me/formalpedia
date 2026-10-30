-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.distant_assignments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:51:06.938407+00:00
-- url     : https://prove2.me/submissions/bf984250-c0d4-4586-bdfd-a842b595f655

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Preparation_distant_assignments_s35

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
    (V : T → ℝ) {M δ g γ B v p₀ α β : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 < δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp : ∀ t, p₀ ≤ G.p t) (hα : 0 ≤ α) (hα1 : α < 1)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hV : V t ≤ v) (R : ℝ) (hDα : dist j (s t) ≤ α*R)
    (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R)
    (hmin : ∀ a ∉ F t, R ≤ dist (s t) (i a))
    (hDβ : 0 < G.c t → dist j (s t) ≤ β*G.L t) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        farFactor δ p₀ α β γ*v := by
  exact _root_.OAI.MetricKMedian.Preparation.distant_assignments_s35 F y s i V G L hy hδ hβ hsep hg hγ hunit hp₀ hp hα hα1 j t Fj hmj hms hvj hV R hDα hmax hmin hDβ

end MetricKMedian.Preparation
end
end

end OAI
end

