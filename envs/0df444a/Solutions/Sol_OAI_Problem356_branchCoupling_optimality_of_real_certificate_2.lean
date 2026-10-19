-- Prove2me | solution 2 for OAI.Problem356.branchCoupling_optimality_of_real_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:31:15.510953+00:00
-- url     : https://prove2.me/submissions/87443d8d-9e7f-4c60-87b0-cb02a8fe8ff6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchOptimizer.lean:L57-L101
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.branchCoupling_optimality_of_real_certificate. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_ae_branchMarginal_mem
import Theorems.Thm_OAI_Problem356_branchCoupling_optimality_of_shifted_certificate
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

-- ---- from OAI.Analysis.CoulombTransport.Calibration ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

lemma measurable_shiftedPotential {u : E3 → ℝ} (hu : Measurable u) (M : ℝ) :
    Measurable (shiftedPotential u M) :=
  (hu.add_const M).ennreal_ofReal

lemma shifted_three_sum {a b c M : ℝ}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      ENNReal.ofReal (a + b + c + 3 * M) := by
  have ha' : 0 ≤ a + M := by linarith
  have hb' : 0 ≤ b + M := by linarith
  have hc' : 0 ≤ c + M := by linarith
  rw [← ENNReal.ofReal_add ha' hb', ← ENNReal.ofReal_add (add_nonneg ha' hb') hc']
  congr 1
  ring

lemma shifted_three_le {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c)
    (h : ENNReal.ofReal (a + b + c) ≤ z) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) ≤
      z + ENNReal.ofReal (3 * M) := by
  rw [shifted_three_sum ha hb hc]
  exact ENNReal.ofReal_add_le.trans (add_le_add h le_rfl)

lemma shifted_three_eq_of_contact {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (hs : 0 ≤ a + b + c) (hz : ENNReal.ofReal (a + b + c) = z) :
    ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M) := by
  rw [shifted_three_sum ha hb hc, ENNReal.ofReal_add hs (by positivity), hz]

lemma contact_of_shifted_three_eq {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (h : ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) +
      ENNReal.ofReal (c + M) = z + ENNReal.ofReal (3 * M)) :
    0 ≤ a + b + c ∧ ENNReal.ofReal (a + b + c) = z := by
  rw [shifted_three_sum ha hb hc] at h
  have hz : z ≠ ⊤ := by
    intro hz
    simp only [hz, top_add] at h
    exact ENNReal.ofReal_ne_top h
  have hs : 0 ≤ a + b + c + 3 * M := by linarith
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal hs, ENNReal.toReal_add hz ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * M)] at ht
  have heq : a + b + c = z.toReal := by linarith
  constructor
  · rw [heq]
    exact ENNReal.toReal_nonneg
  · rw [heq, ENNReal.ofReal_toReal hz]

lemma shifted_three_eq_iff {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M)) ↔
      0 ≤ a + b + c ∧ ENNReal.ofReal (a + b + c) = z := by
  exact ⟨contact_of_shifted_three_eq ha hb hc hM,
    fun h => shifted_three_eq_of_contact ha hb hc hM h.1 h.2⟩

/-- For a positive cost, equality already forces nonnegativity of the signed sum. -/
lemma shifted_three_eq_iff_of_pos {a b c M : ℝ} {z : ℝ≥0∞}
    (ha : -M ≤ a) (hb : -M ≤ b) (hc : -M ≤ c) (hM : 0 ≤ M)
    (hz : 0 < z) :
    (ENNReal.ofReal (a + M) + ENNReal.ofReal (b + M) + ENNReal.ofReal (c + M) =
      z + ENNReal.ofReal (3 * M)) ↔ ENNReal.ofReal (a + b + c) = z := by
  rw [shifted_three_eq_iff ha hb hc hM]
  constructor
  · exact And.right
  · intro h
    refine ⟨le_of_lt (ENNReal.ofReal_pos.mp ?_), h⟩
    rw [h]
    exact hz

lemma shiftedPotential_certificate {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t))
    (h : ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
      coulombCost t) :
    shiftedPotential u M (tripleFst t) + shiftedPotential u M (tripleSnd t) +
      shiftedPotential u M (tripleThd t) ≤ coulombCost t + ENNReal.ofReal (3 * M) :=
  shifted_three_le h1 h2 h3 h

/-- An almost-everywhere upper bound suffices for finiteness of the shifted
potential; no signed-integrability conversion is needed. -/
lemma lintegral_shiftedPotential_le_of_ae_le {mu : Measure E3} [IsProbabilityMeasure mu]
    {u : E3 → ℝ} {M A : ℝ} (hbound : ∀ᵐ x ∂mu, u x ≤ A) :
    (∫⁻ x, shiftedPotential u M x ∂mu) ≤ ENNReal.ofReal (A + M) := by
  calc
    (∫⁻ x, shiftedPotential u M x ∂mu) ≤ (∫⁻ _x, ENNReal.ofReal (A + M) ∂mu) := by
      apply lintegral_mono_ae
      exact hbound.mono fun x hx => ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (A + M) := by simp

lemma lintegral_shiftedPotential_lt_top_of_ae_le {mu : Measure E3}
    [IsProbabilityMeasure mu] {u : E3 → ℝ} {M A : ℝ}
    (hbound : ∀ᵐ x ∂mu, u x ≤ A) :
    (∫⁻ x, shiftedPotential u M x ∂mu) < ⊤ :=
  (lintegral_shiftedPotential_le_of_ae_le hbound).trans_lt ENNReal.ofReal_lt_top

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.RealCounterexampleAssembly ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

private lemma coulombCost_pos_realAssembly (t : Triple) : 0 < coulombCost t := by
  have hpos : 0 < invDistance (tripleFst t) (tripleSnd t) :=
    ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  unfold coulombCost
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hpos zero_le) zero_le

/-- For the strictly positive Coulomb cost, the shifted and signed contact
conditions are equivalent; no nonnegativity assumption on the signed sum is
needed. -/
lemma triplePotential_shifted_contact_iff {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (hM : 0 ≤ M)
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t)) :
    (triplePotential (shiftedPotential u M) t =
      coulombCost t + ENNReal.ofReal (3 * M)) ↔
    ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) =
      coulombCost t :=
  shifted_three_eq_iff_of_pos h1 h2 h3 hM (coulombCost_pos_realAssembly t)

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.BranchOptimizer ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Signed-potential version of explicit branch optimizer certification.
The assumptions are a subset of the real counterexample assembly assumptions;
no density, injectivity, or nonattainment hypothesis is required. -/
theorem branchCoupling_optimality_of_real_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {B U : Set E3} (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 0 x) + u (H 1 x)) = coulombCost (x, (H 0 x, H 1 x)))
    (hcontact23 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 2 x) + u (H 3 x)) = coulombCost (x, (H 2 x, H 3 x))) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  have : IsProbabilityMeasure (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hfinite : (∫⁻ x, shiftedPotential u M x
      ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤ :=
    (lintegral_shiftedPotential_lt_top_of_ae_le
      (M := M) (hmuU.mono fun x hx => (hubound x hx).2)).ne
  apply branchCoupling_optimality_of_shifted_certificate nu H hH hU hmuU
    (measurable_shiftedPotential hu M) hfinite ENNReal.ofReal_ne_top
  · intro t h1 h2 h3
    exact shiftedPotential_certificate (hubound _ h1).1 (hubound _ h2).1
      (hubound _ h3).1 (hbound t h1 h2 h3)
  · filter_upwards [hfull, hcontact01] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 0 x) (hHU 0 ⟨x, hx, rfl⟩)).1
      (hubound (H 1 x) (hHU 1 ⟨x, hx, rfl⟩)).1).mpr
    exact heq
  · filter_upwards [hfull, hcontact23] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 2 x) (hHU 2 ⟨x, hx, rfl⟩)).1
      (hubound (H 3 x) (hHU 3 ⟨x, hx, rfl⟩)).1).mpr
    exact heq

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.branchCoupling_optimality_of_real_certificate := @_root_.OAI.Problem356.branchCoupling_optimality_of_real_certificate
