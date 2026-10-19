-- Prove2me | solution 2 for OAI.Problem356.hasCoulombCounterexample_of_branches
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:26:13.389309+00:00
-- url     : https://prove2.me/submissions/22acc23f-3d3a-46bf-b0b5-a02d58179363

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CounterexampleAssembly.lean:L53-L130
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.hasCoulombCounterexample_of_branches. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_Splitting_no_preserving_branch_selection
import Theorems.Thm_OAI_Problem356_Splitting_splitMeasure_apply_image
import Theorems.Thm_OAI_Problem356_ae_branchCoupling
import Theorems.Thm_OAI_Problem356_ae_branchMarginal_mem
import Theorems.Thm_OAI_Problem356_isProbabilityMeasure_branchCoupling

-- ---- from OAI.Analysis.CoulombTransport.BranchCoupling ----
namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_branchGraph {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (branchGraph f g h) := hf.prodMk (hg.prodMk hh)

lemma map_tripleFst_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleFst (Measure.map (branchGraph f g h) nu) = Measure.map f nu := by
  rw [Measure.map_map (show Measurable tripleFst from measurable_fst) (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleSnd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleSnd (Measure.map (branchGraph f g h) nu) = Measure.map g nu := by
  rw [Measure.map_map (show Measurable tripleSnd from measurable_fst.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma map_tripleThd_branchGraph (nu : Measure E3) {f g h : E3 → E3}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measure.map tripleThd (Measure.map (branchGraph f g h) nu) = Measure.map h nu := by
  rw [Measure.map_map (show Measurable tripleThd from measurable_snd.comp measurable_snd)
    (measurable_branchGraph hf hg hh)]
  rfl

lemma six_smul_group (a b c d e : Measure E3) :
    (1 / 6 : ℝ≥0∞) • (a + b + c + a + d + e) =
      (1 / 3 : ℝ≥0∞) • a + (1 / 6 : ℝ≥0∞) • (b + c + d + e) := by
  have h : (1 / 3 : ℝ≥0∞) = 1 / 6 + 1 / 6 := by
    simp only [one_div]
    change ((3 : NNReal) : ℝ≥0∞)⁻¹ = ((6 : NNReal) : ℝ≥0∞)⁻¹ +
      ((6 : NNReal) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0), ← ENNReal.coe_add]
    norm_num
  rw [h, add_smul]
  simp only [smul_add]
  ac_rfl

lemma map_tripleFst_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleFst (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleFst := measurable_fst
  simp only [branchCoupling, Measure.map_smul _ _ tripleFst, Measure.map_add _ _ hp,
    map_tripleFst_branchGraph nu measurable_id h1 h2,
    map_tripleFst_branchGraph nu h1 h2 measurable_id,
    map_tripleFst_branchGraph nu h2 measurable_id h1,
    map_tripleFst_branchGraph nu measurable_id h3 h4,
    map_tripleFst_branchGraph nu h3 h4 measurable_id,
    map_tripleFst_branchGraph nu h4 measurable_id h3, Measure.map_id]
  exact six_smul_group _ _ _ _ _

lemma map_tripleSnd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleSnd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleSnd := measurable_fst.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul _ _ tripleSnd, Measure.map_add _ _ hp,
    map_tripleSnd_branchGraph nu measurable_id h1 h2,
    map_tripleSnd_branchGraph nu h1 h2 measurable_id,
    map_tripleSnd_branchGraph nu h2 measurable_id h1,
    map_tripleSnd_branchGraph nu measurable_id h3 h4,
    map_tripleSnd_branchGraph nu h3 h4 measurable_id,
    map_tripleSnd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

lemma map_tripleThd_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    Measure.map tripleThd (branchCoupling nu H1 H2 H3 H4) =
      branchMarginal nu H1 H2 H3 H4 := by
  have hp : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [branchCoupling, Measure.map_smul _ _ tripleThd, Measure.map_add _ _ hp,
    map_tripleThd_branchGraph nu measurable_id h1 h2,
    map_tripleThd_branchGraph nu h1 h2 measurable_id,
    map_tripleThd_branchGraph nu h2 measurable_id h1,
    map_tripleThd_branchGraph nu measurable_id h3 h4,
    map_tripleThd_branchGraph nu h3 h4 measurable_id,
    map_tripleThd_branchGraph nu h4 measurable_id h3, Measure.map_id]
  unfold branchMarginal
  rw [← six_smul_group]
  congr 1
  ac_rfl

/-- The explicit two-branch mixture is an admissible coupling of its five-component marginal. -/
theorem isThreeCoupling_branchCoupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    IsThreeCoupling (branchMarginal nu H1 H2 H3 H4) (branchCoupling nu H1 H2 H3 H4) :=
  ⟨isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4,
    map_tripleFst_branchCoupling nu h1 h2 h3 h4,
    map_tripleSnd_branchCoupling nu h1 h2 h3 h4,
    map_tripleThd_branchCoupling nu h1 h2 h3 h4⟩

lemma isProbabilityMeasure_branchMarginal (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchMarginal nu H1 H2 H3 H4) := by
  have := isProbabilityMeasure_branchCoupling nu h1 h2 h3 h4
  rw [← map_tripleFst_branchCoupling nu h1 h2 h3 h4]
  exact Measure.isProbabilityMeasure_map
    (show Measurable tripleFst from measurable_fst).aemeasurable

end Problem356

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

lemma measurable_graphMap {T2 T3 : E3 → E3} (h2 : Measurable T2) (h3 : Measurable T3) :
    Measurable (graphMap T2 T3) := measurable_id.prodMk (h2.prodMk h3)

lemma graphMeasure_isThreeCoupling (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    IsThreeCoupling mu (graphMeasure mu T2 T3) := by
  have hm := measurable_graphMap h2.1 h3.1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance,
    ?_, ?_, ?_⟩
  · rw [graphMeasure, Measure.map_map measurable_tripleFst hm]
    change Measure.map id mu = mu
    exact Measure.map_id
  · rw [graphMeasure, Measure.map_map measurable_tripleSnd hm]
    exact h2.2
  · rw [graphMeasure, Measure.map_map measurable_tripleThd hm]
    exact h3.2

lemma lintegral_graphMeasure (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Measurable T2) (h3 : Measurable T3) :
    (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) = graphCost mu T2 T3 := by
  exact lintegral_map measurable_coulombCost (measurable_graphMap h2 h3)

lemma kantorovichValue_le_graphCost (mu : Measure E3) [IsProbabilityMeasure mu]
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    kantorovichValue mu ≤ graphCost mu T2 T3 := by
  rw [← lintegral_graphMeasure mu h2.1 h3.1]
  exact iInf₂_le (graphMeasure mu T2 T3) (graphMeasure_isThreeCoupling mu h2 h3)

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CouplingSupport ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A property holding almost everywhere for the common marginal holds in all
three coordinates of every feasible coupling. No measurability of the property
is needed for this direction of transport. -/
lemma IsThreeCoupling.ae_coordinates {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {p : E3 → Prop} (hp : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ t ∂pi, p (tripleFst t) ∧ p (tripleSnd t) ∧ p (tripleThd t) := by
  have h1 : ∀ᵐ t ∂pi, p (tripleFst t) := by
    apply ae_of_ae_map measurable_tripleFst.aemeasurable
    simpa only [hpi.2.1] using hp
  have h2 : ∀ᵐ t ∂pi, p (tripleSnd t) := by
    apply ae_of_ae_map measurable_tripleSnd.aemeasurable
    simpa only [hpi.2.2.1] using hp
  have h3 : ∀ᵐ t ∂pi, p (tripleThd t) := by
    apply ae_of_ae_map measurable_tripleThd.aemeasurable
    simpa only [hpi.2.2.2] using hp
  exact h1.and (h2.and h3)

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.ContactObstruction ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A contact condition for optimal couplings also holds along any optimal
admissible graph. This needs no measurable-set hypothesis on `Contact`. -/
lemma ae_contact_of_graphCost_eq {mu : Measure E3} [IsProbabilityMeasure mu]
    {Contact : Triple → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    {T2 T3 : E3 → E3} (h2 : Preserves mu T2) (h3 : Preserves mu T3)
    (hopt : graphCost mu T2 T3 = kantorovichValue mu) :
    ∀ᵐ x ∂mu, Contact (graphMap T2 T3 x) := by
  have hpi := graphMeasure_isThreeCoupling mu h2 h3
  have hcost : (∫⁻ t, coulombCost t ∂graphMeasure mu T2 T3) =
      kantorovichValue mu := (lintegral_graphMeasure mu h2.1 h3.1).trans hopt
  exact ae_of_ae_map (measurable_graphMap h2.1 h3.1).aemeasurable
    (hcontact (graphMeasure mu T2 T3) hpi hcost)

lemma noMongeOptimizer_of_contact_obstruction (mu : Measure E3) [IsProbabilityMeasure mu]
    {Contact : Triple → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    (hobstruction : ∀ T2 T3 : E3 → E3, Preserves mu T2 → Preserves mu T3 →
      ¬ (∀ᵐ x ∂mu, Contact (graphMap T2 T3 x))) :
    NoMongeOptimizer mu := by
  intro T2 T3 h2 h3
  refine lt_of_le_of_ne (kantorovichValue_le_graphCost mu h2 h3) ?_
  intro heq
  exact hobstruction T2 T3 h2 h3 (ae_contact_of_graphCost_eq hcontact h2 h3 heq.symm)

/-- Abstract branch-selection endgame. A contact triple whose first coordinate
lies in `B` forces its second coordinate to satisfy `Select`. If no preserving
map can satisfy that selection almost everywhere for an absolutely continuous
submeasure, no admissible graph is optimal. -/
lemma noMongeOptimizer_of_selection_obstruction
    (mu nu : Measure E3) [IsProbabilityMeasure mu]
    (hnu : nu ≪ mu) {B : Set E3} (hB : ∀ᵐ x ∂nu, x ∈ B)
    {Contact : Triple → Prop} {Select : E3 → E3 → Prop}
    (hcontact : ∀ pi : Measure Triple, IsThreeCoupling mu pi →
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu → ∀ᵐ t ∂pi, Contact t)
    (hselect : ∀ x y z : E3, x ∈ B → Contact (x, (y, z)) → Select x y)
    (hobstruction : ∀ T : E3 → E3, Preserves mu T →
      ¬ (∀ᵐ x ∂nu, Select x (T x))) :
    NoMongeOptimizer mu := by
  apply noMongeOptimizer_of_contact_obstruction mu hcontact
  intro T2 T3 h2 h3 hgraph
  apply hobstruction T2 h2
  have hgraph' : ∀ᵐ x ∂nu, Contact (graphMap T2 T3 x) := hnu.ae_le hgraph
  filter_upwards [hB, hgraph'] with x hx hcx
  exact hselect x (T2 x) (T3 x) hx hcx

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.DualCertificate ----
namespace OAI

universe uAlpha

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356
namespace DualCertificate

lemma measurable_potentialSum {v : E3 → ℝ≥0∞} (hv : Measurable v) :
    Measurable (potentialSum v) := by
  exact ((hv.comp measurable_fst).add
    (hv.comp (measurable_fst.comp measurable_snd))).add
    (hv.comp (measurable_snd.comp measurable_snd))

/-- Complementary slackness for a shifted nonnegative certificate. -/
lemma ae_contact_of_equal_integrals {α : Type uAlpha} [MeasurableSpace α]
    {pi : Measure α} [IsProbabilityMeasure pi] {p c : α → ℝ≥0∞}
    {offset : ℝ≥0∞} (hc : AEMeasurable c pi)
    (hbound : p ≤ᵐ[pi] fun t => c t + offset)
    (hfinite : (∫⁻ t, p t ∂pi) ≠ ⊤)
    (heq : (∫⁻ t, p t ∂pi) = (∫⁻ t, c t ∂pi) + offset) :
    p =ᵐ[pi] fun t => c t + offset := by
  apply ae_eq_of_ae_le_of_lintegral_le hbound hfinite (hc.add aemeasurable_const)
  rw [lintegral_add_offset, heq]

/-- A finite shifted dual value forces every optimal coupling onto the
contact set.  The value identity is the sole input needed from dual optimality. -/
lemma ae_contact_of_optimal_coupling {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hfinite : kantorovichValue mu ≠ ⊤)
    (hcost : AEMeasurable coulombCost pi)
    (hbound : potentialSum v ≤ᵐ[pi] fun t => coulombCost t + offset)
    (hvalue : (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
      kantorovichValue mu + offset)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu) :
    potentialSum v =ᵐ[pi] fun t => coulombCost t + offset := by
  have : IsProbabilityMeasure pi := hpi.1
  have hid := lintegral_potentialSum hpi hv
  rw [hvalue] at hid
  exact ae_contact_of_equal_integrals hcost hbound
    (hid ▸ ENNReal.add_ne_top.mpr ⟨hfinite, hoffset⟩)
    (by rw [hoptimal]; exact hid)

end DualCertificate
end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.OptimalLocalization ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

namespace ShiftedCoulombCertificate

variable {mu : Measure E3} {value : ℝ≥0∞}

/-- A constant shift integrates to itself under any feasible coupling. -/
theorem lintegral_cost_add (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi) :
    (∫⁻ t, coulombCost t + cert.shift ∂pi) =
      (∫⁻ t, coulombCost t ∂pi) + cert.shift := by
  have : IsProbabilityMeasure pi := hpi.1
  rw [lintegral_add_right _ measurable_const]
  simp

/-- Every coupling has cost at least the certified value. -/
theorem le_cost (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi) :
    value ≤ ∫⁻ t, coulombCost t ∂pi := by
  apply (ENNReal.add_le_add_iff_right cert.shift_ne_top).mp
  rw [← cert.integral_eq pi hpi, ← cert.lintegral_cost_add hpi]
  exact lintegral_mono_ae (cert.lower_bound pi hpi)

/-- A feasible candidate matching a certificate realizes the exact infimum. -/
theorem value_eq (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    kantorovichValue mu = value := by
  apply le_antisymm
  · exact iInf_le_of_le pi (iInf_le_of_le hpi hcost.le)
  · exact le_iInf fun q => le_iInf fun hq => cert.le_cost hq

/-- A matching candidate supplies the attainment assertion. -/
theorem attained (cert : ShiftedCoulombCertificate mu value)
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hcost : (∫⁻ t, coulombCost t ∂pi) = value) :
    KantorovichAttained mu := by
  exact ⟨pi, hpi, hcost.trans (cert.value_eq hpi hcost).symm⟩

end ShiftedCoulombCertificate

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CertificateAttainment ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

open DualCertificate

namespace ShiftedCoulombCertificate

end ShiftedCoulombCertificate

/-- Finite marginal potential integral makes every contact candidate finite. -/
theorem candidateCost_lt_top_of_contact {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    (hvfinite : (∫⁻ x, v x ∂mu) ≠ ⊤) {offset : ℝ≥0∞}
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    (∫⁻ t, coulombCost t ∂pi0) < ⊤ := by
  have : IsProbabilityMeasure pi0 := hpi0.1
  have hsum : (∫⁻ t, coulombCost t ∂pi0) + offset ≠ ⊤ := by
    rw [← lintegral_add_offset pi0 coulombCost offset,
      ← lintegral_congr_ae hcontact, lintegral_potentialSum hpi0 hv]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hvfinite, hvfinite⟩, hvfinite⟩
  exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mp hsum).1

theorem attained_finite_of_contact_candidate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    (hvfinite : (∫⁻ x, v x ∂mu) ≠ ⊤) {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, potentialSum v t ≤ coulombCost t + offset)
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    KantorovichAttained mu ∧ kantorovichValue mu < ⊤ ∧
      kantorovichValue mu = (∫⁻ t, coulombCost t ∂pi0) ∧
      (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) =
        kantorovichValue mu + offset := by
  let cert := ShiftedCoulombCertificate.ofContactCandidate hpi0 hv hoffset hbound hcontact
  have hvalue := cert.value_eq hpi0 rfl
  refine ⟨cert.attained hpi0 rfl, ?_, hvalue, ?_⟩
  · rw [hvalue]
    exact candidateCost_lt_top_of_contact hpi0 hv hvfinite hcontact
  · rw [hvalue, ← lintegral_potentialSum hpi0 hv]
    exact cert.integral_eq pi0 hpi0

theorem measurable_triplePotential {p : E3 → ℝ≥0∞} (hp : Measurable p) :
    Measurable (triplePotential p) := DualCertificate.measurable_potentialSum hp

theorem IsThreeCoupling.ae_of_support_certificate {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {U : Set E3} (hU : MeasurableSet U)
    (hmu : ∀ᵐ x ∂mu, x ∈ U) {P : Triple → Prop}
    (hP : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U → P t) :
    ∀ᵐ t ∂pi, P t := by
  have hf : Measurable tripleFst := measurable_fst
  have hs : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have ht : Measurable tripleThd := measurable_snd.comp measurable_snd
  have h1 : ∀ᵐ t ∂pi, tripleFst t ∈ U :=
    (ae_map_iff hf.aemeasurable hU).mp (by rwa [hpi.2.1])
  have h2 : ∀ᵐ t ∂pi, tripleSnd t ∈ U :=
    (ae_map_iff hs.aemeasurable hU).mp (by rwa [hpi.2.2.1])
  have h3 : ∀ᵐ t ∂pi, tripleThd t ∈ U :=
    (ae_map_iff ht.aemeasurable hU).mp (by rwa [hpi.2.2.2])
  exact (h1.and (h2.and h3)).mono fun t h => hP t h.1 h.2.1 h.2.2

theorem kantorovichAttained_of_certificate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C) :
    KantorovichAttained mu ∧ kantorovichValue mu < ⊤ := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact ⟨h.1, h.2.1⟩

theorem certificate_contact_of_optimal {mu : Measure E3} {pi0 pi : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) (hpi : IsThreeCoupling mu pi)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hcost : Measurable coulombCost)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu) :
    ∀ᵐ t ∂pi, triplePotential p t = coulombCost t + C := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact DualCertificate.ae_contact_of_optimal_coupling hpi hp hC h.2.1.ne
    hcost.aemeasurable (hbound pi hpi) h.2.2.2 hoptimal

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.SplitMeasure ----
namespace OAI

universe uAlpha uIndex

/-! Measure identities for the five-component splitting construction. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356
namespace Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- A measure supported almost everywhere on `B` vanishes on any set disjoint from `B`. -/
theorem measure_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hBS : Disjoint B S) : ν S = 0 := by
  apply measure_mono_null (t := Bᶜ)
  · intro x hx
    exact fun hxB => Set.disjoint_left.mp hBS hxB hx
  · exact ae_iff.mp hν

/-- A branch pushforward vanishes away from the image of the central component. -/
theorem map_eq_zero_of_disjoint
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hS : MeasurableSet S) (hBS : Disjoint (H '' B) S) :
    (Measure.map H ν) S = 0 := by
  rw [Measure.map_apply hH hS]
  apply measure_eq_zero_of_disjoint ν hν
  exact Set.disjoint_left.mpr fun x hxB hxS =>
    Set.disjoint_left.mp hBS ⟨x, hxB, rfl⟩ hxS

variable [Fintype ι]

/-- A nonzero central coefficient transfers all almost-everywhere properties
of the mixture to its central reference measure. -/
theorem absolutelyContinuous_splitMeasure
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    (ha : a ≠ 0) : ν ≪ splitMeasure ν a b H := by
  exact (Measure.absolutelyContinuous_smul ha).add_right _

/-- On the central component, only the central summand contributes. -/
theorem splitMeasure_apply_central
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hSB : S ⊆ B) (hS : MeasurableSet S)
    (hDisj : ∀ i, Disjoint B (H i '' B)) :
    splitMeasure ν a b H S = a * ν S := by
  have hz : ∀ i, (Measure.map (H i) ν) S = 0 := by
    intro i
    apply map_eq_zero_of_disjoint ν hν (hH i) hS
    exact (hDisj i).symm.mono_right hSB
  simp [splitMeasure, Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, hz]

end Splitting
end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.SplittingConstruction ----
namespace OAI

universe uAlpha uIndex

/-!
# The disjoint-component selection obstruction

This combines the abstract mass argument with the exact mass identities for
a finite mixture of a central measure and its injective branch pushforwards.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356.Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α] [Fintype ι]

/-- A finite family of disjoint injective branches with strictly smaller
outer coefficients cannot support any preserving deterministic selector. -/
theorem no_preserving_splitMeasure_selection [MeasurableEq α]
    {ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν c (fun _ => d) H) =
        splitMeasure ν c (fun _ => d) H ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  apply no_preserving_branch_selection hν hB hfull hH himage
  · intro S hS hSB
    exact splitMeasure_apply_central ν c (fun _ => d) H
      hfull hH hSB hS hCentral
  · intro i S hS hSB
    exact splitMeasure_apply_image ν c (fun _ => d) H
      hfull hH hInj hSB (fun j => himage j S hS hSB) hCentral hPair i
  · exact hdc

end Problem356.Splitting

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CounterexampleAssembly ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The four-map marginal is the generic finite split measure, with central
weight `1/3` and four equal outer weights `1/6`. -/
lemma branchMarginal_eq_splitMeasure (nu : Measure E3) (H : Fin 4 → E3 → E3) :
    branchMarginal nu (H 0) (H 1) (H 2) (H 3) =
      Splitting.splitMeasure nu (1 / 3) (fun _ : Fin 4 => 1 / 6) H := by
  simp [branchMarginal, Splitting.splitMeasure, Fin.sum_univ_succ, smul_add, add_assoc]

private lemma coulombCost_cycle_assembly (x y z : E3) :
    coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev y x, norm_sub_rev z x]
  ac_rfl

private lemma triplePotential_cycle_assembly (p : E3 → ℝ≥0∞) (x y z : E3) :
    triplePotential p (y, (z, x)) = triplePotential p (x, (y, z)) := by
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd]
  ac_rfl

theorem hasCoulombCounterexample_of_branches
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C)
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      triplePotential p (x, (y, z)) = coulombCost (x, (y, z)) + C →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  let mu := branchMarginal nu (H 0) (H 1) (H 2) (H 3)
  let pi0 := branchCoupling nu (H 0) (H 1) (H 2) (H 3)
  have : IsProbabilityMeasure mu :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hpi0 : IsThreeCoupling mu pi0 :=
    isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU : ∀ᵐ x ∂mu, x ∈ U := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hboundall : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C := by
    intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  have hcontact0 : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C := by
    apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [triplePotential_cycle_assembly, coulombCost_cycle_assembly]
      exact hxyz
    · exact hcontact01
    · exact hcontact23
  obtain ⟨hattained, hfinite⟩ :=
    kantorovichAttained_of_certificate hpi0 hp hpfinite hC hboundall hcontact0
  have hnu : nu ≪ mu := by
    change nu ≪ branchMarginal nu (H 0) (H 1) (H 2) (H 3)
    rw [branchMarginal_eq_splitMeasure]
    exact Splitting.absolutelyContinuous_splitMeasure nu (1 / 3) (fun _ : Fin 4 => 1 / 6) H
      (by norm_num)
  have hno : NoMongeOptimizer mu := by
    apply noMongeOptimizer_of_selection_obstruction mu nu hnu hfull
      (Contact := fun t => tripleSnd t ∈ U ∧ tripleThd t ∈ U ∧
        triplePotential p t = coulombCost t + C)
      (Select := fun x y => ∃ i, y = H i x)
    · intro pi hpi hopt
      have heq := certificate_contact_of_optimal hpi0 hpi hp hpfinite hC
        measurable_coulombCost hboundall hcontact0 hopt
      filter_upwards [hpi.ae_coordinates hmuU, heq] with t ht heq
      exact ⟨ht.2.1, ht.2.2, heq⟩
    · intro x y z hx ht
      exact hselect x y z hx ht.1 ht.2.1 ht.2.2
    · intro T hT hselection
      have hbad := Splitting.no_preserving_splitMeasure_selection
        (H := H) (c := (1 / 3 : ℝ≥0∞)) (d := (1 / 6 : ℝ≥0∞))
        (by simp : nu Set.univ ≠ 0) hB hfull hH hInj himage hCentral hPair
        (by norm_num)
      apply hbad
      refine ⟨T, hT.1, ?_, hselection⟩
      simpa only [← branchMarginal_eq_splitMeasure] using hT.2
  change IsSmoothCompactProbabilityDensity rho ∧
    IsProbabilityMeasure (densityMeasure rho) ∧ kantorovichValue (densityMeasure rho) < ⊤ ∧
    KantorovichAttained (densityMeasure rho) ∧ NoMongeOptimizer (densityMeasure rho)
  rw [hdensity]
  exact ⟨hrho, inferInstanceAs (IsProbabilityMeasure mu), hfinite, hattained, hno⟩

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.hasCoulombCounterexample_of_branches := @_root_.OAI.Problem356.hasCoulombCounterexample_of_branches
