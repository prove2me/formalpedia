-- Prove2me | solution 1 for OAI.Problem356.branchCoupling_optimality_of_shifted_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:28:31.221985+00:00
-- url     : https://prove2.me/submissions/7487e47b-3310-49a3-aecc-5694550f8b80

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal
theorem pb_map_zero {nu : Measure E3} {g : E3 → Triple} (hg : Measurable g)
    {P : Triple → Prop} (hP : MeasurableSet {t | P t}) (h : ∀ᵐ x ∂nu, P (g x)) :
    Measure.map g nu {t | ¬ P t} = 0 := by
  rw [show {t | ¬ P t} = {t | P t}ᶜ from rfl, Measure.map_apply hg hP.compl]
  exact ae_iff.mp h

theorem pb_ae_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  rw [ae_iff]
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [pb_map_zero (hg _ _ _ measurable_id h1 h2) hP h12,
    pb_map_zero (hg _ _ _ h1 h2 measurable_id) hP (h12.mono fun x hx => hcycle _ _ _ hx),
    pb_map_zero (hg _ _ _ h2 measurable_id h1) hP
      (h12.mono fun x hx => hcycle _ _ _ (hcycle _ _ _ hx)),
    pb_map_zero (hg _ _ _ measurable_id h3 h4) hP h34,
    pb_map_zero (hg _ _ _ h3 h4 measurable_id) hP (h34.mono fun x hx => hcycle _ _ _ hx),
    pb_map_zero (hg _ _ _ h4 measurable_id h3) hP
      (h34.mono fun x hx => hcycle _ _ _ (hcycle _ _ _ hx))]
  simp

theorem pb_isProb (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  constructor
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [Measure.map_apply (hg _ _ _ measurable_id h1 h2) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h1 h2 measurable_id) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h2 measurable_id h1) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ measurable_id h3 h4) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h3 h4 measurable_id) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h4 measurable_id h3) MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ]
  have : (1 : ℝ≥0∞) + 1 + 1 + 1 + 1 + 1 = 6 := by norm_num
  rw [this]
  exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)

theorem pb_third : (1 / 3 : ℝ≥0∞) = 1 / 6 + 1 / 6 := by
  rw [ENNReal.div_add_div_same]
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem pb_map_graph (nu : Measure E3) {f g h : E3 → E3} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (π : Triple → E3) (hπ : Measurable π) (k : E3 → E3)
    (hk : π ∘ branchGraph f g h = k) :
    Measure.map π (Measure.map (branchGraph f g h) nu) = Measure.map k nu := by
  rw [Measure.map_map hπ (show Measurable (branchGraph f g h) from hf.prodMk (hg.prodMk hh)), hk]

theorem pb_coupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    IsThreeCoupling (branchMarginal nu H1 H2 H3 H4) (branchCoupling nu H1 H2 H3 H4) := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  have hm1 : Measurable tripleFst := measurable_fst
  have hm2 : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have hm3 : Measurable tripleThd := measurable_snd.comp measurable_snd
  have hid := (measurable_id : Measurable (id : E3 → E3))
  refine ⟨pb_isProb nu h1 h2 h3 h4, ?_, ?_, ?_⟩ <;>
  · ext s hs
    simp only [branchCoupling, branchMarginal, Measure.map_smul, Measure.map_add _ _ hm1,
      Measure.map_add _ _ hm2, Measure.map_add _ _ hm3,
      pb_map_graph nu hid h1 h2 _ hm1 id rfl, pb_map_graph nu h1 h2 hid _ hm1 H1 rfl,
      pb_map_graph nu h2 hid h1 _ hm1 H2 rfl, pb_map_graph nu hid h3 h4 _ hm1 id rfl,
      pb_map_graph nu h3 h4 hid _ hm1 H3 rfl, pb_map_graph nu h4 hid h3 _ hm1 H4 rfl,
      pb_map_graph nu hid h1 h2 _ hm2 H1 rfl, pb_map_graph nu h1 h2 hid _ hm2 H2 rfl,
      pb_map_graph nu h2 hid h1 _ hm2 id rfl, pb_map_graph nu hid h3 h4 _ hm2 H3 rfl,
      pb_map_graph nu h3 h4 hid _ hm2 H4 rfl, pb_map_graph nu h4 hid h3 _ hm2 id rfl,
      pb_map_graph nu hid h1 h2 _ hm3 H2 rfl, pb_map_graph nu h1 h2 hid _ hm3 id rfl,
      pb_map_graph nu h2 hid h1 _ hm3 H1 rfl, pb_map_graph nu hid h3 h4 _ hm3 H4 rfl,
      pb_map_graph nu h3 h4 hid _ hm3 id rfl, pb_map_graph nu h4 hid h3 _ hm3 H3 rfl,
      Measure.map_id, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    rw [pb_third]
    ring

theorem pb_cost_cycle (x y z : E3) : coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev z x, norm_sub_rev y x]
  ring

theorem pb_cost_meas : Measurable coulombCost := by
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  fun_prop

theorem pb_opt {μ : Measure E3} {π0 : Measure Triple} (h0 : IsThreeCoupling μ π0)
    {U : Set E3} (hU : MeasurableSet U) (hmuU : ∀ᵐ x ∂μ, x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂μ) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂π0, triplePotential p t = coulombCost t + C) :
    (∫⁻ t, coulombCost t ∂π0) = kantorovichValue μ ∧ (∫⁻ t, coulombCost t ∂π0) < ⊤ := by
  have hm1 : Measurable tripleFst := measurable_fst
  have hm2 : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have hm3 : Measurable tripleThd := measurable_snd.comp measurable_snd
  have hval : (∫⁻ t, coulombCost t ∂π0) + C = (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) := by
    have := h0.1
    rw [← DualCertificate.lintegral_add_offset, ← DualCertificate.lintegral_potentialSum h0 hp]
    exact (lintegral_congr_ae hcontact).symm
  have hlow : ∀ pi, IsThreeCoupling μ pi → (∫⁻ t, coulombCost t ∂π0) ≤ ∫⁻ t, coulombCost t ∂pi := by
    intro pi hpi
    have := hpi.1
    have a1 : ∀ᵐ t ∂pi, tripleFst t ∈ U := by
      exact (ae_map_iff hm1.aemeasurable hU).mp (by rw [hpi.2.1]; exact hmuU)
    have a2 : ∀ᵐ t ∂pi, tripleSnd t ∈ U := by
      exact (ae_map_iff hm2.aemeasurable hU).mp (by rw [hpi.2.2.1]; exact hmuU)
    have a3 : ∀ᵐ t ∂pi, tripleThd t ∈ U := by
      exact (ae_map_iff hm3.aemeasurable hU).mp (by rw [hpi.2.2.2]; exact hmuU)
    have hle : (∫⁻ t, coulombCost t ∂π0) + C ≤ (∫⁻ t, coulombCost t ∂pi) + C := by
      rw [hval, ← DualCertificate.lintegral_potentialSum hpi hp,
        ← DualCertificate.lintegral_add_offset]
      apply lintegral_mono_ae
      filter_upwards [a1, a2, a3] with t t1 t2 t3
      exact hbound t t1 t2 t3
    exact (ENNReal.add_le_add_iff_right hC).mp hle
  refine ⟨le_antisymm (le_iInf fun pi => le_iInf fun hpi => hlow pi hpi)
    (iInf_le_of_le π0 (iInf_le_of_le h0 le_rfl)), ?_⟩
  have : (∫⁻ t, coulombCost t ∂π0) + C < ⊤ := by
    rw [hval]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hpfinite.lt_top, hpfinite.lt_top⟩, hpfinite.lt_top⟩
  exact lt_of_le_of_lt le_self_add this

theorem solution
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
  have h0 := pb_coupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  refine pb_opt h0 hU hmuU hp hpfinite hC hbound ?_
  have hPm : MeasurableSet {t : Triple | triplePotential p t = coulombCost t + C} := by
    apply measurableSet_eq_fun
    · unfold triplePotential tripleFst tripleSnd tripleThd; fun_prop
    · exact pb_cost_meas.add measurable_const
  refine pb_ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3) hPm ?_ hcontact01 hcontact23
  intro x y z h
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd] at h ⊢
  rw [pb_cost_cycle, ← h]
  ring

