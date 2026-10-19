-- Prove2me | solution 2 for OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:47:25.775657+00:00
-- url     : https://prove2.me/submissions/c5bc8cdd-d64c-49cb-b937-da66a3906c5b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/FirstCoordinateLift.lean:L47-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_CoulombEstimates_coulombCost_le_add_of_separated

-- ---- from OAI.Analysis.CoulombTransport.CoulombEstimates ----
namespace OAI

universe uE uA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- Uniform boundedness of the Coulomb cost on a separated triple. -/
theorem realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z : E} {eta : ℝ} (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    realCost x y z ≤ 3 / eta := by
  have h1 := one_div_le_one_div_of_le heta hxy
  have h2 := one_div_le_one_div_of_le heta hxz
  have h3 := one_div_le_one_div_of_le heta hyz
  simp only [one_div] at h1 h2 h3
  unfold realCost
  rw [div_eq_mul_inv]
  linarith

/-- The real formula agrees with the extended-valued cost away from collisions. -/
theorem coulombCost_eq_ofReal_realCost {x y z : E3}
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold realCost
  rw [ENNReal.ofReal_add (add_nonneg (inv_nonneg.mpr dist_nonneg)
        (inv_nonneg.mpr dist_nonneg)) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_add (inv_nonneg.mpr dist_nonneg) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz,
    ENNReal.ofReal_inv_of_pos hyz]
  rfl

/-- The exact extended-valued Coulomb cost is uniformly bounded on separated triples. -/
theorem coulombCost_le_of_separated {x y z : E3} {eta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z) :
    coulombCost (x, (y, z)) ≤ ENNReal.ofReal (3 / eta) := by
  rw [coulombCost_eq_ofReal_realCost (heta.trans_le hxy)
    (heta.trans_le hxz) (heta.trans_le hyz)]
  exact ENNReal.ofReal_le_ofReal (realCost_le heta hxy hxz hyz)

/-- A uniform graph-cost bound; no regularity of the maps is needed for this bound. -/
theorem graphCost_le_of_ae_separated (mu : Measure E3) {T2 T3 : E3 → E3} {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ x ∂mu, Separated eta (x, (T2 x, T3 x))) :
    graphCost mu T2 T3 ≤ ENNReal.ofReal (3 / eta) * mu Set.univ := by
  unfold graphCost
  calc
    _ ≤ ∫⁻ _x : E3, ENNReal.ofReal (3 / eta) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with x hx
      exact coulombCost_le_of_separated heta hx.1 hx.2.1 hx.2.2
    _ = _ := lintegral_const _

/-- The finite-cost condition in finite Monge approximation follows from separation. -/
theorem graphCost_lt_top_of_ae_separated (mu : Measure E3) [IsFiniteMeasure mu]
    {T2 T3 : E3 → E3} {eta : ℝ}
    (heta : 0 < eta) (hsep : ∀ᵐ x ∂mu, Separated eta (x, (T2 x, T3 x))) :
    graphCost mu T2 T3 < ⊤ :=
  (graphCost_le_of_ae_separated mu heta hsep).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top mu Set.univ))

/-- Integrating the pointwise oscillation bound under a common parametrization. -/
theorem lintegral_coulombCost_le_add_of_ae_close
    {A : Type uA} [MeasurableSpace A] (mu : Measure A) {P Q : A → Triple} {eta delta : ℝ}
    (heta : 0 < eta)
    (hsepP : ∀ᵐ a ∂mu, Separated eta (P a))
    (hsepQ : ∀ᵐ a ∂mu, Separated eta (Q a))
    (hclose : ∀ᵐ a ∂mu, dist (P a).1 (Q a).1 ≤ delta ∧
      dist (P a).2.1 (Q a).2.1 ≤ delta ∧ dist (P a).2.2 (Q a).2.2 ≤ delta) :
    (∫⁻ a, coulombCost (P a) ∂mu) ≤ (∫⁻ a, coulombCost (Q a) ∂mu) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) * mu Set.univ := by
  calc
    _ ≤ ∫⁻ a, coulombCost (Q a) + ENNReal.ofReal ((6 * delta) / eta ^ 2) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hsepP, hsepQ, hclose] with a hP hQ hc
      exact coulombCost_le_add_of_separated heta hP.1 hP.2.1 hP.2.2
        hQ.1 hQ.2.1 hQ.2.2 hc.1 hc.2.1 hc.2.2
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const]

end Problem356.CoulombEstimates

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GraphBridge ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_tripleFst : Measurable tripleFst := measurable_fst
lemma measurable_tripleSnd : Measurable tripleSnd := measurable_fst.comp measurable_snd
lemma measurable_tripleThd : Measurable tripleThd := measurable_snd.comp measurable_snd

lemma measurable_invDistance : Measurable (fun p : E3 × E3 => invDistance p.1 p.2) := by
  unfold invDistance
  exact ((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).inv

lemma measurable_coulombCost : Measurable coulombCost := by
  unfold coulombCost
  exact ((measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleSnd)).add
    (measurable_invDistance.comp (measurable_tripleFst.prodMk measurable_tripleThd))).add
    (measurable_invDistance.comp (measurable_tripleSnd.prodMk measurable_tripleThd))

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FirstCoordinateLift ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.FirstCoordinateLift

open CoulombEstimates

/-- Replacing only the first coordinate by a nearby point preserves half the
separation, without any component-label hypothesis. -/
lemma separated_replace_first {η δ : ℝ} {t : Triple} {x : E3}
    (hη : 0 < η) (ht : Separated η t)
    (hclose : dist x t.1 ≤ δ) (hδ : δ ≤ η / 2) :
    Separated (η / 2) (x, t.2) := by
  rcases t with ⟨a, b, c⟩
  rcases ht with ⟨hab, hac, hbc⟩
  have hx : dist a x ≤ δ := by simpa only [dist_comm] using hclose
  have hab' := dist_triangle a x b
  have hac' := dist_triangle a x c
  refine ⟨?_, ?_, ?_⟩ <;> dsimp at * <;> linarith

/-- Weakening separation to half its value. -/
lemma separated_half {η : ℝ} {t : Triple} (hη : 0 < η)
    (ht : Separated η t) : Separated (η / 2) t := by
  rcases ht with ⟨h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The two noncentral coordinates of a measure-valued lift preserve the marginal. -/
lemma preserves_coordinates {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {Q : E3 → Triple}
    (hQ : Measurable Q) (hmap : Measure.map Q μ = π) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) := by
  constructor
  · refine ⟨measurable_tripleSnd.comp hQ, ?_⟩
    rw [← Measure.map_map measurable_tripleSnd hQ, hmap]
    exact hπ.2.2.1
  · refine ⟨measurable_tripleThd.comp hQ, ?_⟩
    rw [← Measure.map_map measurable_tripleThd hQ, hmap]
    exact hπ.2.2.2

/-- A lift of a separated coupling, whose first coordinate remains nearby,
gives a finite-cost preserving pair and the quantitative Coulomb estimate. -/
theorem graph_cost_of_lift {μ : Measure E3} [IsProbabilityMeasure μ]
    {π : Measure Triple} (hπ : IsThreeCoupling μ π)
    {Q : E3 → Triple} (hQ : Measurable Q) (hmap : Measure.map Q μ = π)
    {η δ : ℝ} (hη : 0 < η) (hδ : δ ≤ η / 2)
    (hsep : ∀ᵐ t ∂π, Separated η t)
    (hclose : ∀ᵐ x ∂μ, dist x (Q x).1 ≤ δ) :
    Preserves μ (tripleSnd ∘ Q) ∧ Preserves μ (tripleThd ∘ Q) ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) < ⊤ ∧
      graphCost μ (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂π) + ENNReal.ofReal (24 * δ / η ^ 2) := by
  have hsepQ : ∀ᵐ x ∂μ, Separated η (Q x) :=
    ae_of_ae_map hQ.aemeasurable (by rwa [hmap])
  have hsepP : ∀ᵐ x ∂μ, Separated (η / 2) (x, (Q x).2) := by
    filter_upwards [hsepQ, hclose] with x hx hc
    exact separated_replace_first hη hx hc hδ
  have hsepQ' : ∀ᵐ x ∂μ, Separated (η / 2) (Q x) :=
    hsepQ.mono fun _ hx => separated_half hη hx
  have hc : ∀ᵐ x ∂μ, dist (x, (Q x).2).1 (Q x).1 ≤ δ ∧
      dist (x, (Q x).2).2.1 (Q x).2.1 ≤ δ ∧
      dist (x, (Q x).2).2.2 (Q x).2.2 ≤ δ := by
    filter_upwards [hclose] with x hx
    have hδ0 : 0 ≤ δ := dist_nonneg.trans hx
    exact ⟨hx, by simpa using hδ0, by simpa using hδ0⟩
  have hbound := lintegral_coulombCost_le_add_of_ae_close μ (half_pos hη)
    hsepP hsepQ' hc
  have herr : (6 * δ) / (η / 2) ^ 2 = 24 * δ / η ^ 2 := by
    field_simp
    ring
  rw [measure_univ, mul_one, herr] at hbound
  have hint : (∫⁻ x, coulombCost (Q x) ∂μ) = ∫⁻ t, coulombCost t ∂π := by
    rw [← lintegral_map measurable_coulombCost hQ, hmap]
  rw [hint] at hbound
  exact ⟨(preserves_coordinates hπ hQ hmap).1,
    (preserves_coordinates hπ hQ hmap).2,
    graphCost_lt_top_of_ae_separated μ (half_pos hη) hsepP, hbound⟩

end Problem356.FirstCoordinateLift

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FirstCoordinateLift
open MeasureTheory
open scoped ENNReal
open CoulombEstimates


theorem solution : type_of% @_root_.OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift := @_root_.OAI.Problem356.FirstCoordinateLift.graph_cost_of_lift
