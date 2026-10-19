-- Prove2me | solution 2 for OAI.Problem356.branchCoupling_optimality_of_shifted_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:29:30.058603+00:00
-- url     : https://prove2.me/submissions/b5ce2372-e96c-467e-b3b8-0512da420ea5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchOptimizer.lean:L23-L55
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.branchCoupling_optimality_of_shifted_certificate. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_ae_branchCoupling
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

theorem certificate_optimality {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂mu) ≠ ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C) :
    (∫⁻ t, coulombCost t ∂pi0) = kantorovichValue mu ∧
      (∫⁻ t, coulombCost t ∂pi0) < ⊤ := by
  have h := attained_finite_of_contact_candidate hpi0 hp hpfinite hC hbound hcontact
  exact ⟨h.2.2.1.symm, candidateCost_lt_top_of_contact hpi0 hp hpfinite hcontact⟩

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.BranchOptimizer ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

private lemma branchOptimizer_cost_cycle (x y z : E3) :
    coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev y x, norm_sub_rev z x]
  ac_rfl

private lemma branchOptimizer_potential_cycle (p : E3 → ℝ≥0∞) (x y z : E3) :
    triplePotential p (y, (z, x)) = triplePotential p (x, (y, z)) := by
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd]
  ac_rfl

/-- The explicit six-graph branch coupling is itself a finite optimizer.
This preserves the identity of the optimizer, unlike an existential attainment
statement, so its geometric separation can be used in Monge approximation. -/
theorem branchCoupling_optimality_of_shifted_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {U : Set E3} (hU : MeasurableSet U)
    (hmuU : ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  apply certificate_optimality
    (isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)) hp hpfinite hC
  · intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  · apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [branchOptimizer_potential_cycle, branchOptimizer_cost_cycle]
      exact hxyz
    · exact hcontact01
    · exact hcontact23

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.branchCoupling_optimality_of_shifted_certificate := @_root_.OAI.Problem356.branchCoupling_optimality_of_shifted_certificate
