-- Prove2me | solution 2 for OAI.Problem356.ae_branchCoupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:01:59.506718+00:00
-- url     : https://prove2.me/submissions/932ae9b8-a8e2-4d93-b590-19c4d38255a8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchCoupling.lean:L155-L181
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.ae_branchCoupling. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

-- ---- from OAI.Analysis.CoulombTransport.BranchCoupling ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_branchGraph {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (branchGraph f g h) := hf.prodMk (hg.prodMk hh)

/-- Any measurable cyclically invariant property holding on the two branches
also holds almost everywhere for their explicit coupling. -/
theorem ae_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by
  have h12r : ∀ᵐ x ∂nu, P (branchGraph H1 H2 id x) :=
    h12.mono fun x hx => hcycle _ _ _ hx
  have h12rr : ∀ᵐ x ∂nu, P (branchGraph H2 id H1 x) :=
    h12r.mono fun x hx => hcycle _ _ _ hx
  have h34r : ∀ᵐ x ∂nu, P (branchGraph H3 H4 id x) :=
    h34.mono fun x hx => hcycle _ _ _ hx
  have h34rr : ∀ᵐ x ∂nu, P (branchGraph H4 id H3 x) :=
    h34r.mono fun x hx => hcycle _ _ _ hx
  unfold branchCoupling
  apply Measure.ae_smul_measure
  simp only [ae_add_measure_iff,
    ae_map_iff (measurable_branchGraph measurable_id h1 h2).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h1 h2 measurable_id).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h2 measurable_id h1).aemeasurable hP,
    ae_map_iff (measurable_branchGraph measurable_id h3 h4).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h3 h4 measurable_id).aemeasurable hP,
    ae_map_iff (measurable_branchGraph h4 measurable_id h3).aemeasurable hP]
  exact ⟨⟨⟨⟨⟨h12, h12r⟩, h12rr⟩, h34⟩, h34r⟩, h34rr⟩

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.ae_branchCoupling := @_root_.OAI.Problem356.ae_branchCoupling
