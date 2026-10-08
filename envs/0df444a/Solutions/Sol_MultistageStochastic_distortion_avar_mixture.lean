-- Prove2me | solution 1 for MultistageStochastic.distortion_avar_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:46:05.335447+00:00
-- url     : https://prove2.me/submissions/c29e1460-62e7-47d3-a150-a5f203759d56

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace DAM033
open MultistageStochastic

/-- super-level sets of `σ` inside `(0,1)` -/
def S (σ : ℝ → ℝ) (t : ℝ) : Set ℝ := {p | t < σ p} ∩ Ioo 0 1

noncomputable def m (σ : ℝ → ℝ) (t : ℝ) : ℝ := (volume (S σ t)).toReal

noncomputable def a (σ : ℝ → ℝ) (t : ℝ) : ℝ := 1 - m σ t

lemma S_sub (σ : ℝ → ℝ) (t : ℝ) : S σ t ⊆ Ioo 0 1 := inter_subset_right

lemma S_anti (σ : ℝ → ℝ) {t t' : ℝ} (h : t ≤ t') : S σ t' ⊆ S σ t :=
  fun _ hp => ⟨lt_of_le_of_lt h hp.1, hp.2⟩

lemma vol_S_le (σ : ℝ → ℝ) (t : ℝ) : volume (S σ t) ≤ 1 := by
  calc volume (S σ t) ≤ volume (Ioo (0:ℝ) 1) := measure_mono (S_sub σ t)
    _ = 1 := by simp [Real.volume_Ioo]

lemma vol_S_ne_top (σ : ℝ → ℝ) (t : ℝ) : volume (S σ t) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (vol_S_le σ t)

lemma m_nonneg (σ : ℝ → ℝ) (t : ℝ) : 0 ≤ m σ t := ENNReal.toReal_nonneg

lemma m_le_one (σ : ℝ → ℝ) (t : ℝ) : m σ t ≤ 1 := by
  unfold m
  have := ENNReal.toReal_mono ENNReal.one_ne_top (vol_S_le σ t)
  simpa using this

lemma m_anti (σ : ℝ → ℝ) : Antitone (m σ) := fun _ _ h =>
  ENNReal.toReal_mono (vol_S_ne_top σ _) (measure_mono (S_anti σ h))

lemma m_meas (σ : ℝ → ℝ) : Measurable (m σ) := (m_anti σ).measurable

lemma a_meas (σ : ℝ → ℝ) : Measurable (a σ) := measurable_const.sub (m_meas σ)

lemma S_struct {σ : ℝ → ℝ} (hmono : MonotoneOn σ (Ico 0 1)) (t : ℝ)
    (hne : (S σ t).Nonempty) :
    ∃ b, 0 ≤ b ∧ b < 1 ∧ Ioo b 1 ⊆ S σ t ∧ S σ t ⊆ Icc b 1 := by
  have hbdd : BddBelow (S σ t) := ⟨0, fun p hp => hp.2.1.le⟩
  refine ⟨sInf (S σ t), le_csInf hne (fun p hp => hp.2.1.le), ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hne
    exact lt_of_le_of_lt (csInf_le hbdd hp) hp.2.2
  · intro p hp
    obtain ⟨q, hqS, hqp⟩ := exists_lt_of_csInf_lt hne hp.1
    have hq0 : 0 < q := hqS.2.1
    refine ⟨?_, hq0.trans hqp, hp.2⟩
    have : σ q ≤ σ p := hmono ⟨hq0.le, hqS.2.2⟩ ⟨(hq0.trans hqp).le, hp.2⟩ hqp.le
    exact lt_of_lt_of_le hqS.1 this
  · intro p hp
    exact ⟨csInf_le hbdd hp, hp.2.2.le⟩

lemma S_eq {σ : ℝ → ℝ} (hmono : MonotoneOn σ (Ico 0 1)) (t : ℝ) :
    (S σ t) =ᵐ[volume] Ioo (a σ t) 1 := by
  rcases (S σ t).eq_empty_or_nonempty with h | h
  · have : a σ t = 1 := by simp [a, m, h]
    rw [h, this, Ioo_self]
    exact EventuallyEq.rfl
  · obtain ⟨b, hb0, hb1, h1, h2⟩ := S_struct hmono t h
    have hvol : volume (S σ t) = ENNReal.ofReal (1 - b) := by
      apply le_antisymm
      · calc volume (S σ t) ≤ volume (Icc b 1) := measure_mono h2
          _ = _ := Real.volume_Icc
      · calc ENNReal.ofReal (1 - b) = volume (Ioo b 1) := Real.volume_Ioo.symm
          _ ≤ _ := measure_mono h1
    have ha : a σ t = b := by
      simp only [a, m, hvol]; rw [ENNReal.toReal_ofReal (by linarith)]; ring
    rw [ha]
    exact (ae_eq_of_subset_of_measure_ge h1 (by rw [hvol, Real.volume_Ioo])
      measurableSet_Ioo.nullMeasurableSet (vol_S_ne_top σ t)).symm

lemma key_t {σ : ℝ → ℝ} (hmono : MonotoneOn σ (Ico 0 1)) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (t : ℝ) :
    m σ t * averageValueAtRisk P Y (a σ t) = ∫ p in S σ t, valueAtRisk P Y p := by
  rw [setIntegral_congr_set (S_eq hmono t)]
  have hm : m σ t = 1 - a σ t := by unfold a; ring
  unfold averageValueAtRisk
  split_ifs with h
  · rw [hm, h, Ioo_self, Measure.restrict_empty, integral_zero_measure]; ring
  · rw [hm, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm h)), one_mul]

lemma intOn_bdd {s : Set ℝ} (hs : volume s ≠ ∞) {f : ℝ → ℝ} (hf : Measurable f) (K : ℝ)
    (hK : ∀ p, |f p| ≤ K) : IntegrableOn f s :=
  Measure.integrableOn_of_bounded (M := K) hs hf.aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hK p)

lemma LC {σ : ℝ → ℝ} (hσ : IsDistortionFunction σ) (W : ℝ → ℝ) (hWm : Measurable W)
    (hW0 : ∀ p, 0 ≤ W p) (K : ℝ) (hWK : ∀ p, W p ≤ K) :
    IntegrableOn (fun t => ∫ p in S σ t, W p) (Ioi 0) ∧
    ∫ t in Ioi 0, (∫ p in S σ t, W p) = ∫ p in Ioo 0 1, σ p * W p := by
  obtain ⟨hnn, _, hint, _⟩ := hσ
  have hWabs : ∀ p, |W p| ≤ K := fun p => by rw [abs_of_nonneg (hW0 p)]; exact hWK p
  have hWi : ∀ t, IntegrableOn W (S σ t) := fun t => intOn_bdd (vol_S_ne_top σ t) hWm K hWabs
  have hσae : AEMeasurable σ (volume.restrict (Ioo (0:ℝ) 1)) :=
    hint.aestronglyMeasurable.aemeasurable
  have hσW : IntegrableOn (fun p => σ p * W p) (Ioo 0 1) :=
    hint.mul_bdd (c := K) hWm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hWabs p)
  have hnnI : ∀ p ∈ Ioo (0:ℝ) 1, 0 ≤ σ p := fun p hp => hnn p ⟨hp.1.le, hp.2⟩
  have hL : ∫⁻ t in Ioi 0, ∫⁻ p in S σ t, ENNReal.ofReal (W p) =
      ∫⁻ p in Ioo 0 1, ENNReal.ofReal (σ p * W p) := by
    have hac := withDensity_absolutelyContinuous (volume.restrict (Ioo (0:ℝ) 1))
      (fun p => ENNReal.ofReal (W p))
    have h1 := lintegral_eq_lintegral_meas_lt
      ((volume.restrict (Ioo (0:ℝ) 1)).withDensity (fun p => ENNReal.ofReal (W p))) (f := σ)
      (hac.ae_le (ae_restrict_of_forall_mem measurableSet_Ioo hnnI)) (hσae.mono_ac hac)
    have h2 : ∀ t, ((volume.restrict (Ioo (0:ℝ) 1)).withDensity (fun p => ENNReal.ofReal (W p)))
        {p | t < σ p} = ∫⁻ p in S σ t, ENNReal.ofReal (W p) := by
      intro t
      rw [withDensity_apply' _ _, Measure.restrict_restrict' measurableSet_Ioo]
      rfl
    simp_rw [h2] at h1
    rw [← h1, lintegral_withDensity_eq_lintegral_mul₀ hWm.ennreal_ofReal.aemeasurable
      hσae.ennreal_ofReal]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro p hp
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hnnI p hp), mul_comm]
  have hg0 : ∀ t, 0 ≤ ∫ p in S σ t, W p := fun t => integral_nonneg (fun p => hW0 p)
  have hgofReal : ∀ t, ENNReal.ofReal (∫ p in S σ t, W p) = ∫⁻ p in S σ t, ENNReal.ofReal (W p) :=
    fun t => ofReal_integral_eq_lintegral_ofReal (hWi t) (Eventually.of_forall (fun p => hW0 p))
  have hgmeas : Measurable (fun t => ∫ p in S σ t, W p) := by
    apply Antitone.measurable
    intro t t' h
    exact setIntegral_mono_set (hWi t) (Eventually.of_forall (fun p => hW0 p))
      (S_anti σ h).eventuallyLE
  have hσW0 : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun p => σ p * W p) :=
    ae_restrict_of_forall_mem measurableSet_Ioo (fun p hp => mul_nonneg (hnnI p hp) (hW0 p))
  have hfin : ∫⁻ p in Ioo 0 1, ENNReal.ofReal (σ p * W p) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hσW hσW0]; exact ENNReal.ofReal_lt_top
  have hint_g : IntegrableOn (fun t => ∫ p in S σ t, W p) (Ioi 0) := by
    refine ⟨hgmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)]
    simp_rw [hgofReal]; rw [hL]; exact hfin
  refine ⟨hint_g, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgmeas.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hσW0 hσW.aestronglyMeasurable]
  simp_rw [hgofReal]; rw [hL]

noncomputable def nu (σ : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun t => ((Real.toNNReal (m σ t) : NNReal) : ℝ≥0∞))

noncomputable def mu (σ : ℝ → ℝ) : Measure ℝ := (nu σ).map (a σ)

lemma integral_mu (σ : ℝ → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ α, f α ∂(mu σ) = ∫ t in Ioi 0, m σ t * f (a σ t) := by
  unfold mu nu
  rw [integral_map (a_meas σ).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul ((m_meas σ).real_toNNReal)]
  congr 1; funext t
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (m_nonneg σ t)]

lemma mu_univ {σ : ℝ → ℝ} (hσ : IsDistortionFunction σ) : mu σ univ = 1 := by
  unfold mu nu
  rw [Measure.map_apply (a_meas σ) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  obtain ⟨hi, he⟩ := LC hσ (fun _ => 1) measurable_const (fun _ => zero_le_one) 1 (fun _ => le_rfl)
  have hS1 : ∀ t, ∫ p in S σ t, (fun _ => (1:ℝ)) p = m σ t := by
    intro t; simp [m, measureReal_def]
  simp_rw [hS1] at hi he
  have h1 : ∫ p in Ioo (0:ℝ) 1, σ p * 1 = 1 := by simpa using hσ.2.2.2
  rw [h1] at he
  have := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun t => m_nonneg σ t))
  rw [he, ENNReal.ofReal_one] at this
  rw [this]
  rfl

lemma mu_supp (σ : ℝ → ℝ) : mu σ (Icc 0 1)ᶜ = 0 := by
  unfold mu
  rw [Measure.map_apply (a_meas σ) measurableSet_Icc.compl]
  have : a σ ⁻¹' (Icc 0 1)ᶜ = ∅ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_empty_iff_false, iff_false, not_not]
    exact ⟨by unfold a; linarith [m_le_one σ t], by unfold a; linarith [m_nonneg σ t]⟩
  rw [this, measure_empty]

lemma var_facts {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLinfty P Y) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ p, |valueAtRisk P Y p| ≤ C) ∧ Measurable (valueAtRisk P Y) := by
  obtain ⟨hYm, C0, hC0⟩ := hY
  obtain ⟨C, hCnn, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P, |Y ω| ≤ C :=
    ⟨max C0 0, le_max_right _ _, hC0.mono fun ω h => h.trans (le_max_left _ _)⟩
  have hup : P {ω | Y ω ≤ C} = 1 := by
    have h1 : ∀ᵐ ω ∂P, Y ω ≤ C := hC.mono fun ω h => (le_abs_self _).trans h
    rw [← measure_univ (μ := P)]
    exact (ae_iff_measure_eq (measurableSet_le hYm measurable_const).nullMeasurableSet).mp h1
  have hlow : ∀ y < -C, P {ω | Y ω ≤ y} = 0 := by
    intro y hy
    apply measure_mono_null _ (ae_iff.mp hC)
    intro ω hω
    simp only [mem_ofPred_eq, not_le] at hω ⊢
    have := neg_abs_le (Y ω)
    linarith
  have hV : ∀ p, valueAtRisk P Y p = sInf {y | ENNReal.ofReal p ≤ P {ω | Y ω ≤ y}} :=
    fun p => rfl
  have hmemC : ∀ p : ℝ, p ≤ 1 → C ∈ {y | ENNReal.ofReal p ≤ P {ω | Y ω ≤ y}} := fun p hp => by
    show ENNReal.ofReal p ≤ P {ω | Y ω ≤ C}
    rw [hup]; exact ENNReal.ofReal_le_one.mpr hp
  have hlowA : ∀ p : ℝ, 0 < p → ∀ y ∈ {y | ENNReal.ofReal p ≤ P {ω | Y ω ≤ y}}, -C ≤ y := by
    intro p hp y hy
    by_contra hlt'
    have hlt : y < -C := not_le.mp hlt'
    have : ENNReal.ofReal p ≤ 0 := by rw [← hlow y hlt]; exact hy
    exact absurd (ENNReal.ofReal_pos.mpr hp) (not_lt.mpr this)
  have hbdd : ∀ p : ℝ, 0 < p → BddBelow {y | ENNReal.ofReal p ≤ P {ω | Y ω ≤ y}} :=
    fun p hp => ⟨-C, hlowA p hp⟩
  have hin : ∀ p ∈ Ioc (0:ℝ) 1, -C ≤ valueAtRisk P Y p ∧ valueAtRisk P Y p ≤ C := by
    intro p hp
    rw [hV]
    exact ⟨le_csInf ⟨C, hmemC p hp.2⟩ (hlowA p hp.1), csInf_le (hbdd p hp.1) (hmemC p hp.2)⟩
  have hle0 : ∀ p : ℝ, p ≤ 0 → valueAtRisk P Y p = 0 := by
    intro p hp
    have : {y | ENNReal.ofReal p ≤ P {ω | Y ω ≤ y}} = univ := by
      ext y; simp only [mem_ofPred_eq, mem_univ, iff_true]
      rw [ENNReal.ofReal_of_nonpos hp]; exact bot_le
    rw [hV, this]; exact Real.sInf_of_not_bddBelow not_bddBelow_univ
  have hgt1 : ∀ p : ℝ, 1 < p → valueAtRisk P Y p = 0 := by
    intro p hp
    have : {y | ENNReal.ofReal p ≤ P {ω | Y ω ≤ y}} = ∅ := by
      ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      calc P {ω | Y ω ≤ y} ≤ 1 := prob_le_one
        _ < ENNReal.ofReal p := by
          rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hp
    rw [hV, this, Real.sInf_empty]
  have hmono : MonotoneOn (valueAtRisk P Y) (Ioc 0 1) := by
    intro p hp q hq hpq
    rw [hV, hV]
    apply csInf_le_csInf (hbdd p hp.1) ⟨C, hmemC q hq.2⟩
    intro y hy
    exact le_trans (ENNReal.ofReal_le_ofReal hpq) hy
  refine ⟨C, hCnn, ?_, ?_⟩
  · intro p
    rcases le_or_gt p 0 with h | h
    · rw [hle0 p h, abs_zero]; exact hCnn
    rcases le_or_gt p 1 with h' | h'
    · exact abs_le.mpr (hin p ⟨h, h'⟩)
    · rw [hgt1 p h', abs_zero]; exact hCnn
  · let Vh : ℝ → ℝ := fun p => if p ≤ 0 then -C else if p ≤ 1 then valueAtRisk P Y p else C
    have hVh : Monotone Vh := by
      intro x y hxy
      simp only [Vh]
      split_ifs <;> (try linarith) <;>
        first
        | exact (hin _ ⟨by linarith, by linarith⟩).1
        | exact (hin _ ⟨by linarith, by linarith⟩).2
        | exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hxy
    have heq : valueAtRisk P Y = (Ioc (0:ℝ) 1).indicator Vh := by
      funext p
      by_cases hp : p ∈ Ioc (0:ℝ) 1
      · rw [indicator_of_mem hp]; simp only [Vh, if_neg (not_le.mpr hp.1), if_pos hp.2]
      · rw [indicator_of_notMem hp]
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hp
        rcases hp with h | h
        · exact hle0 p h
        · exact hgt1 p h
    rw [heq]; exact hVh.measurable.indicator measurableSet_Ioc

lemma avar_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (hV : Measurable (valueAtRisk P Y)) : Measurable (averageValueAtRisk P Y) := by
  have hG : Measurable (fun α : ℝ => ∫ p in Ioo α 1, valueAtRisk P Y p) := by
    have hset : MeasurableSet {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < 1} :=
      (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)
    have hF : Measurable ({q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < 1}.indicator
        (fun q => valueAtRisk P Y q.2)) := (hV.comp measurable_snd).indicator hset
    have := (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    convert this using 1
    funext α
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    refine Eventually.of_forall fun p => ?_
    beta_reduce
    by_cases h : α < p ∧ p < 1
    · rw [indicator_of_mem (show p ∈ Ioo α 1 from h),
        indicator_of_mem (show (α, p) ∈ {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < 1} from h)]
    · rw [indicator_of_notMem (show p ∉ Ioo α 1 from h),
        indicator_of_notMem (show (α, p) ∉ {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < 1} from h)]
  show Measurable (fun α => if α = 1 then essSupBook P Y
    else (1 - α)⁻¹ * ∫ p in Ioo α 1, valueAtRisk P Y p)
  exact Measurable.ite (measurableSet_singleton (1:ℝ)) measurable_const
    ((measurable_const.sub measurable_id).inv.mul hG)

end DAM033

open MeasureTheory MultistageStochastic in
theorem solution (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ) :
    ∃ μ : Measure ℝ, IsKusuokaMeasure μ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ Y, MemLinfty P Y →
          distortionFunctional P σ Y = ∫ α, averageValueAtRisk P Y α ∂μ := by
  refine ⟨DAM033.mu σ, ⟨⟨DAM033.mu_univ hσ⟩, DAM033.mu_supp σ⟩, ?_⟩
  intro Ω _ P hP Y hY
  obtain ⟨C, hC0, hCb, hVm⟩ := DAM033.var_facts P Y hY
  rw [DAM033.integral_mu σ (DAM033.avar_meas P Y hVm)]
  simp_rw [DAM033.key_t hσ.2.1 P Y]
  obtain ⟨hi1, he1⟩ := DAM033.LC hσ (fun p => valueAtRisk P Y p + C)
    (hVm.add measurable_const) (fun p => by linarith [(abs_le.mp (hCb p)).1]) (2 * C)
    (fun p => by linarith [(abs_le.mp (hCb p)).2])
  obtain ⟨hi2, he2⟩ := DAM033.LC hσ (fun _ => C) measurable_const (fun _ => hC0) C
    (fun _ => le_rfl)
  have hsplit : ∀ t, ∫ p in DAM033.S σ t, valueAtRisk P Y p =
      (∫ p in DAM033.S σ t, (valueAtRisk P Y p + C)) - ∫ p in DAM033.S σ t, C := by
    intro t
    rw [integral_add (DAM033.intOn_bdd (DAM033.vol_S_ne_top σ t) hVm C hCb)
      (DAM033.intOn_bdd (DAM033.vol_S_ne_top σ t) measurable_const C
        (fun _ => by rw [abs_of_nonneg hC0]))]
    ring
  simp_rw [hsplit]
  rw [integral_sub hi1 hi2, he1, he2]
  have hint := hσ.2.2.1
  have hσV : IntegrableOn (fun p => σ p * valueAtRisk P Y p) (Ioo 0 1) :=
    hint.mul_bdd (c := C) hVm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hCb p)
  have hσC : IntegrableOn (fun p => σ p * C) (Ioo 0 1) := hint.mul_const C
  simp_rw [mul_add]
  rw [integral_add hσV hσC]
  unfold distortionFunctional
  ring
