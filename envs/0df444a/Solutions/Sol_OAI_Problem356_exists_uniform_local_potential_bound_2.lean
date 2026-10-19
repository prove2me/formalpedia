-- Prove2me | solution 2 for OAI.Problem356.exists_uniform_local_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:32:40.319566+00:00
-- url     : https://prove2.me/submissions/b752d1e8-f1b9-4dd4-96b1-c7d84b2cdf15

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalPotentialBounds.lean:L12-L34
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_uniform_local_potential_bound. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Theorems.Thm_OAI_Problem356_finite_eventual_neighborhoods

-- ---- from OAI.Analysis.CoulombTransport.CertificateNeighborhoods ----
namespace OAI

universe uIndex uX uY

noncomputable section

open Set Filter Metric
open scoped ENNReal

namespace Problem356

/-- Finitely many strict inequalities at their respective centers persist on
one common positive-radius neighborhood. This is the finite shrinking step
for the bad, distinct-center component types in the certificate. -/
theorem finite_strict_neighborhoods {ι : Type uIndex} {X : Type uX} {Y : Type uY} [PseudoMetricSpace X]
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y]
    (s : Finset ι) (p : ι → X) (f g : ι → X → Y)
    (hf : ∀ i ∈ s, ContinuousAt (f i) (p i))
    (hg : ∀ i ∈ s, ContinuousAt (g i) (p i))
    (hgap : ∀ i ∈ s, f i (p i) < g i (p i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → f i x < g i x := by
  exact finite_eventual_neighborhoods s p (fun i x => f i x < g i x)
    (fun i hi => (hf i hi).eventually_lt (hg i hi) (hgap i hi))

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.LocalPotentialBounds ----
namespace OAI

universe uIndex uX

noncomputable section
open Set Filter Metric
open scoped BigOperators
namespace Problem356

/-- Continuity of finitely many potentials at their centers gives one
positive radius and one positive absolute bound on every component ball. -/
theorem exists_uniform_local_potential_bound {ι : Type uIndex} {X : Type uX} [Fintype ι]
    [PseudoMetricSpace X] (p : ι → X) (v : ι → X → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) :
    ∃ M : ℝ, 0 < M ∧ ∃ r : ℝ, 0 < r ∧
      ∀ i x, x ∈ ball (p i) r → |v i x| ≤ M := by
  classical
  let M : ℝ := (∑ i, |v i (p i)|) + 1
  have hsum : 0 ≤ ∑ i, |v i (p i)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hM : 0 < M := by dsimp [M]; linarith
  have hgap : ∀ i ∈ (Finset.univ : Finset ι), |v i (p i)| < M := by
    intro i _
    have hi : |v i (p i)| ≤ ∑ j, |v j (p j)| :=
      Finset.single_le_sum (f := fun j => |v j (p j)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [M]
    linarith
  obtain ⟨r, hr, h⟩ := finite_strict_neighborhoods Finset.univ p
    (fun i x => |v i x|) (fun _ _ => M)
    (fun i _ => (hv i).abs) (fun _ _ => continuousAt_const) hgap
  refine ⟨M, hM, r, hr, ?_⟩
  intro i x hx
  exact (h i (Finset.mem_univ i) x hx).le

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter Metric
open scoped BigOperators


theorem solution.{uIndex,uX} : type_of% @_root_.OAI.Problem356.exists_uniform_local_potential_bound.{uIndex,uX} := @_root_.OAI.Problem356.exists_uniform_local_potential_bound.{uIndex,uX}
