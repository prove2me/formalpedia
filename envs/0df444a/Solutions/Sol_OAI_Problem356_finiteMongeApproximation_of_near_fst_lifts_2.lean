-- Prove2me | solution 2 for OAI.Problem356.finiteMongeApproximation_of_near_fst_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:49:06.633412+00:00
-- url     : https://prove2.me/submissions/b6d839a6-96c1-4be0-b62b-9730500dba09

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SeparatedLiftApproximation.lean:L12-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.finiteMongeApproximation_of_near_fst_lifts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Theorems.Thm_OAI_Problem356_FirstCoordinateLift_graph_cost_of_lift

-- ---- from OAI.Analysis.CoulombTransport.SeparatedLiftApproximation ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Arbitrarily small first-coordinate lifts of a uniformly separated optimal
coupling give finite Monge approximation. Only the first coordinate is adjusted
to obtain a graph, and uniform separation controls the cost of that adjustment. -/
theorem finiteMongeApproximation_of_near_fst_lifts
    {mu : Measure E3} [IsProbabilityMeasure mu] {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t)
    (hlifts : ∀ delta : ℝ, 0 < delta →
      ∃ Q : E3 → Triple, Measurable Q ∧ Measure.map Q mu = pi ∧
        ∀ᵐ x ∂mu, dist x (Q x).1 ≤ delta) :
    FiniteMongeApproximation mu := by
  intro epsilon hepsilon
  let delta : ℝ := min (eta / 2) (epsilon * eta ^ 2 / 24)
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min
    · positivity
    · positivity
  obtain ⟨Q, hQ, hmap, hclose⟩ := hlifts delta hdelta
  have hdelta_eta : delta ≤ eta / 2 := min_le_left _ _
  obtain ⟨h2, h3, hfinite, hcost⟩ :=
    FirstCoordinateLift.graph_cost_of_lift hpi hQ hmap heta hdelta_eta hseparated hclose
  refine ⟨tripleSnd ∘ Q, tripleThd ∘ Q, h2, h3, hfinite, ?_⟩
  have herror : 24 * delta / eta ^ 2 ≤ epsilon := by
    apply (div_le_iff₀ (sq_pos_of_pos heta)).2
    have hdelta_eps : delta ≤ epsilon * eta ^ 2 / 24 := min_le_right _ _
    linarith
  calc
    graphCost mu (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂pi) + ENNReal.ofReal (24 * delta / eta ^ 2) := hcost
    _ ≤ kantorovichValue mu + ENNReal.ofReal epsilon := by
      rw [hoptimal]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal herror)

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.finiteMongeApproximation_of_near_fst_lifts := @_root_.OAI.Problem356.finiteMongeApproximation_of_near_fst_lifts
