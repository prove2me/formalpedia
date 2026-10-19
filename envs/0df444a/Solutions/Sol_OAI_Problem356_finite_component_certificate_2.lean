-- Prove2me | solution 2 for OAI.Problem356.finite_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:52:06.366723+00:00
-- url     : https://prove2.me/submissions/004f4c77-d1d3-4f32-a4df-590e767d390d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ComponentCertificate.lean:L68-L105
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.finite_component_certificate. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_continuousAt_component_sum
import Theorems.Thm_OAI_Problem356_finite_eventual_neighborhoods

-- ---- from OAI.Analysis.CoulombTransport.CertificateNeighborhoods ----
namespace OAI

universe uIndex uX uY

noncomputable section

open Set Filter Metric
open scoped ENNReal

namespace Problem356

/-- Triple-coordinate ball version of finite eventual shrinking. -/
theorem finite_eventual_triple_neighborhoods {ι : Type uIndex}
    (s : Finset ι) (p : ι → Triple) (P : ι → Triple → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ t in nhds (p i), P i t) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x y z : E3,
      x ∈ ball (p i).1 r → y ∈ ball (p i).2.1 r →
      z ∈ ball (p i).2.2 r → P i (x, (y, z)) := by
  obtain ⟨r, hr, h⟩ := finite_eventual_neighborhoods s p P hP
  refine ⟨r, hr, ?_⟩
  intro i hi x y z hx hy hz
  apply h i hi (x, (y, z))
  simpa only [Prod.dist_eq, max_lt_iff, Metric.mem_ball] using And.intro hx (And.intro hy hz)

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CostTopology ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma continuous_invDistance : Continuous (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact (ENNReal.continuous_ofReal.comp (continuous_fst.sub continuous_snd).norm).inv

lemma continuous_coulombCost : Continuous coulombCost := by
  unfold coulombCost
  have h1 : Continuous tripleFst := continuous_fst
  have h2 : Continuous tripleSnd := continuous_fst.comp continuous_snd
  have h3 : Continuous tripleThd := continuous_snd.comp continuous_snd
  exact ((continuous_invDistance.comp (h1.prodMk h2)).add
    (continuous_invDistance.comp (h1.prodMk h3))).add
    (continuous_invDistance.comp (h2.prodMk h3))

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ComponentCertificate ----
namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- The local-to-global finite-type certificate step. Local supporting
inequalities and exact contact sets are needed only at the good types;
strict gaps at every other center type are enough for all remaining types.
A single radius works for the inequalities and exact equality characterization. -/
theorem finite_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (v : ι → E3 → ℝ)
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hv : ∀ i, ContinuousAt (v i) (p i))
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ a, ∀ x y z : E3,
      x ∈ ball (p a.1) r → y ∈ ball (p a.2.1) r → z ∈ ball (p a.2.2) r →
      ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) ≤ coulombCost (x, (y, z)) ∧
      (ENNReal.ofReal (v a.1 x + v a.2.1 y + v a.2.2 z) = coulombCost (x, (y, z)) ↔
        Good a ∧ Contact a (x, (y, z))) := by
  classical
  have hevent : ∀ a ∈ (Finset.univ : Finset (ι × (ι × ι))),
      ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Good a ∧ Contact a t) := by
    intro a _
    by_cases ha : Good a
    · filter_upwards [hgood a ha] with t ht
      exact ⟨ht.1, by simpa [ha] using ht.2⟩
    · have he := (continuousAt_component_sum p v hv a).eventually_lt
        continuous_coulombCost.continuousAt (hbad a ha)
      filter_upwards [he] with t ht
      exact ⟨ht.le, by simp [ha, ht.ne]⟩
  obtain ⟨r, hr, h⟩ := finite_eventual_triple_neighborhoods Finset.univ
    (fun a : ι × (ι × ι) => (p a.1, (p a.2.1, p a.2.2))) _ hevent
  exact ⟨r, hr, fun a => h a (Finset.mem_univ a)⟩

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter Metric
open scoped ENNReal BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.finite_component_certificate.{uIndex} := @_root_.OAI.Problem356.finite_component_certificate.{uIndex}
