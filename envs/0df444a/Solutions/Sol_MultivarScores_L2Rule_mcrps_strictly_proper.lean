-- Prove2me | solution 1 for MultivarScores.L2Rule.mcrps_strictly_proper
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:02:11.124993+00:00
-- url     : https://prove2.me/submissions/e6b1e2cd-d4c7-4df4-9c7f-f0bf047b0a74

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting
import Theorems.Thm_MultivarScores_L2Rule_theorem_1

open MeasureTheory MultivarScores.L2Rule Set Filter Topology

lemma mvs_hv_eq {d : ℕ} : (heaviside : E d → ℝ) = (Set.Ici (0 : E d)).indicator 1 := rfl

lemma mvs_hv_shift {d : ℕ} (y z : E d) : heaviside (z - y) = (Set.Ici y).indicator 1 z := by
  rw [mvs_hv_eq]
  by_cases hz : y ≤ z
  · have : (0 : E d) ≤ z - y := sub_nonneg.mpr hz
    simp [Set.indicator_of_mem, this, hz]
  · have : ¬ (0 : E d) ≤ z - y := fun h => hz (sub_nonneg.mp h)
    simp [this, hz]

lemma mvs_hv_shift' {d : ℕ} (z s : E d) : heaviside (z - s) = (Set.Iic z).indicator 1 s := by
  rw [mvs_hv_eq]
  by_cases hz : s ≤ z
  · have : (0 : E d) ≤ z - s := sub_nonneg.mpr hz
    simp [Set.indicator_of_mem, this, hz]
  · have : ¬ (0 : E d) ≤ z - s := fun h => hz (sub_nonneg.mp h)
    simp [this, hz]

lemma mvs_hv_meas {d : ℕ} : Measurable (heaviside : E d → ℝ) := by
  rw [mvs_hv_eq]; exact measurable_one.indicator measurableSet_Ici

lemma mvs_hv_bound {d : ℕ} (x : E d) : ‖heaviside x‖ ≤ 1 := by
  rw [mvs_hv_eq]
  by_cases hx : x ∈ Set.Ici (0 : E d) <;> simp [hx]

lemma mvs_smooth_eq_cdf {d : ℕ} (P : Measure (E d)) (z : E d) :
    smooth P heaviside z = cdf P z := by
  unfold smooth cdf
  simp_rw [mvs_hv_shift']
  rw [integral_indicator_one measurableSet_Iic, measureReal_def]

lemma mvs_cdf_bound {d : ℕ} (P : Measure (E d)) [IsProbabilityMeasure P] (z : E d) :
    ‖cdf P z‖ ≤ 1 := by
  unfold cdf
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma mvs_smooth_meas {d : ℕ} (P : Measure (E d)) [IsProbabilityMeasure P] :
    Measurable (smooth P heaviside) := by
  have : Measurable (fun p : E d × E d => heaviside (p.1 - p.2)) :=
    mvs_hv_meas.comp (measurable_fst.sub measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right').measurable

lemma mvs_smooth_bound {d : ℕ} (P : Measure (E d)) [IsProbabilityMeasure P] (z : E d) :
    ‖smooth P heaviside z‖ ≤ 1 := by
  rw [mvs_smooth_eq_cdf]; exact mvs_cdf_bound P z

lemma mvs_isCountablySpanning_Iic : IsCountablySpanning (range (Iic : ℝ → Set ℝ)) := by
  refine ⟨fun n : ℕ => Iic (n : ℝ), fun n => ⟨n, rfl⟩, ?_⟩
  ext x
  simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
  exact ⟨⌈x⌉₊, Nat.le_ceil x⟩

lemma mvs_ext_of_Iic {d : ℕ} (P Q : Measure (E d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (h : ∀ z, P (Iic z) = Q (Iic z)) : P = Q := by
  let C : Set (Set (E d)) := pi univ '' pi univ (fun _ : Fin d => range (Iic : ℝ → Set ℝ))
  have hgen : (inferInstance : MeasurableSpace (E d)) = MeasurableSpace.generateFrom C := by
    refine (generateFrom_eq_pi (fun _ => ?_) (fun _ => mvs_isCountablySpanning_Iic)).symm
    rw [← borel_eq_generateFrom_Iic]; exact BorelSpace.measurable_eq.symm
  refine ext_of_generate_finite C hgen (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ (by simp)
  rintro s ⟨t, ht, rfl⟩
  have : ∀ i, ∃ a, t i = Iic a := fun i => by
    obtain ⟨a, ha⟩ := ht i (mem_univ i); exact ⟨a, ha.symm⟩
  choose a ha using this
  have : (pi univ t) = Iic a := by
    rw [← pi_univ_Iic]; congr 1; funext i; exact ha i
  rw [this]; exact h a

lemma mvs_cdf_ext {d : ℕ} (P Q : Measure (E d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hae : cdf P =ᵐ[volume] cdf Q) : P = Q := by
  -- points of agreement close to and above `z`
  have hpts : ∀ z : E d, ∀ n : ℕ, ∃ x : E d, z ≤ x ∧ x ≤ (fun j => z j + 1 / ((n : ℝ) + 1)) ∧
      cdf P x = cdf Q x := by
    intro z n
    by_contra hcon
    push Not at hcon
    have hsub : (pi univ fun j => Ioo (z j) (z j + 1 / ((n : ℝ) + 1))) ⊆
        {x | ¬ (cdf P x = cdf Q x)} := by
      intro x hx
      simp only [Set.mem_pi, mem_univ, mem_Ioo, true_implies] at hx
      exact hcon x (fun j => (hx j).1.le) (fun j => (hx j).2.le)
    have hnull : volume {x : E d | ¬ (cdf P x = cdf Q x)} = 0 := ae_iff.1 hae
    have h0 := measure_mono_null hsub hnull
    rw [Real.volume_pi_Ioo] at h0
    rw [Finset.prod_eq_zero_iff] at h0
    obtain ⟨j, -, hj⟩ := h0
    rw [ENNReal.ofReal_eq_zero] at hj
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hle : ∀ (P Q : Measure (E d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
      (∀ z : E d, ∀ n : ℕ, ∃ x : E d, z ≤ x ∧ x ≤ (fun j => z j + 1 / ((n : ℝ) + 1)) ∧
        cdf P x = cdf Q x) → ∀ z, P (Iic z) ≤ Q (Iic z) := by
    intro P Q _ _ hp z
    let u : ℕ → E d := fun n j => z j + 1 / ((n : ℝ) + 1)
    have hanti : Antitone fun n => Iic (u n) := by
      intro m n hmn x hx j
      have := hx j
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      simp only [u] at this ⊢; linarith
    have hinter : (⋂ n, Iic (u n)) = Iic z := by
      ext x
      simp only [mem_iInter, mem_Iic]
      constructor
      · intro hx j
        have ht : Tendsto (fun n : ℕ => z j + 1 / ((n : ℝ) + 1)) atTop (𝓝 (z j + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at ht
        exact ge_of_tendsto' ht fun n => hx n j
      · intro hx n j
        have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
        simp only [u]; linarith [hx j]
    have hlim : Tendsto (fun n => Q (Iic (u n))) atTop (𝓝 (Q (Iic z))) := by
      rw [← hinter]
      exact tendsto_measure_iInter_atTop (fun n => measurableSet_Iic.nullMeasurableSet) hanti
        ⟨0, measure_ne_top _ _⟩
    refine ge_of_tendsto' hlim fun n => ?_
    obtain ⟨x, hzx, hxu, hcdf⟩ := hp z n
    have hPQ : P (Iic x) = Q (Iic x) := by
      unfold cdf at hcdf
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hcdf
    calc P (Iic z) ≤ P (Iic x) := measure_mono (Iic_subset_Iic.2 hzx)
      _ = Q (Iic x) := hPQ
      _ ≤ Q (Iic (u n)) := measure_mono (Iic_subset_Iic.2 hxu)
  have hpts' : ∀ z : E d, ∀ n : ℕ, ∃ x : E d, z ≤ x ∧ x ≤ (fun j => z j + 1 / ((n : ℝ) + 1)) ∧
      cdf Q x = cdf P x := by
    intro z n
    obtain ⟨x, h1, h2, h3⟩ := hpts z n
    exact ⟨x, h1, h2, h3.symm⟩
  exact mvs_ext_of_Iic P Q fun z => le_antisymm (hle P Q hpts z) (hle Q P hpts' z)

theorem solution {d : ℕ} (h : E d → ℝ) (hh : Measurable h)
    (h_nonneg : ∀ z, 0 ≤ h z) (h_int : Integrable h) (h_ne : ∀ᵐ z, h z ≠ 0)
    (PX PY : Measure (E d)) [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (hne : PX ≠ PY) :
    (∫ y, MCRPS PY h y ∂PY) < (∫ y, MCRPS PX h y ∂PY) ∧
      (∫ y, MCRPS' PY h y ∂PY) < (∫ y, MCRPS' PX h y ∂PY) := by
  set 𝒱 : Set (Measure (E d)) := {PX, PY} with h𝒱
  have hprob : ∀ P ∈ 𝒱, IsProbabilityMeasure P := by
    intro P hP
    rcases hP with rfl | hP
    · infer_instance
    · rw [mem_singleton_iff] at hP; subst hP; infer_instance
  have hw_meas : Measurable (fun p : E d × E d => heaviside (p.2 - p.1)) :=
    mvs_hv_meas.comp (measurable_snd.sub measurable_fst)
  have hA : Assumption1 heaviside h 𝒱 := by
    refine
      { measurable_w := mvs_hv_meas
        measurable_h := hh
        h_nonneg := h_nonneg
        integrable_h := h_int
        isProb := hprob
        smooth_wd := ?_
        sq_smooth := ?_
        sq_w := ?_
        sq_w_prod := ?_
        cross := ?_
        cross_prod := ?_ }
    · intro P hP z
      haveI := hprob P hP
      exact Integrable.of_bound
        ((mvs_hv_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) 1
        (Eventually.of_forall fun s => mvs_hv_bound _)
    · intro P hP
      haveI := hprob P hP
      refine h_int.bdd_mul (c := 1) ((mvs_smooth_meas P).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (mvs_smooth_bound P z)
    · intro y
      refine h_int.bdd_mul (c := 1)
        ((mvs_hv_meas.comp (measurable_id.sub measurable_const)).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (mvs_hv_bound _)
    · intro P hP
      haveI := hprob P hP
      refine (h_int.comp_snd P).bdd_mul (c := 1) (hw_meas.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (mvs_hv_bound _)
    · intro P hP y
      haveI := hprob P hP
      refine h_int.bdd_mul (c := 1)
        ((mvs_smooth_meas P).mul
          (mvs_hv_meas.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (mvs_smooth_bound P z) (norm_nonneg _) (mvs_hv_bound _)
    · intro P hP Q hQ
      haveI := hprob P hP
      haveI := hprob Q hQ
      refine (h_int.comp_snd Q).bdd_mul (c := 1)
        (((mvs_smooth_meas P).comp measurable_snd).mul hw_meas).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      rw [norm_mul]
      exact mul_le_one₀ (mvs_smooth_bound P _) (norm_nonneg _) (mvs_hv_bound _)
  have hchar : Characterizes heaviside 𝒱 := by
    intro P hP Q hQ hPQ
    haveI := hprob P hP
    haveI := hprob Q hQ
    apply mvs_cdf_ext P Q
    have e1 : smooth P heaviside = cdf P := funext (mvs_smooth_eq_cdf P)
    have e2 : smooth Q heaviside = cdf Q := funext (mvs_smooth_eq_cdf Q)
    rw [← e1, ← e2]; exact hPQ
  have hS : ∀ P : Measure (E d), ∀ y, MCRPS P h y = S P heaviside h y := by
    intro P y
    unfold MCRPS S
    simp_rw [mvs_smooth_eq_cdf, mvs_hv_shift]
  have hS' : ∀ P : Measure (E d), ∀ y, MCRPS' P h y = S' P heaviside h y := by
    intro P y
    unfold MCRPS' S'
    simp_rw [mvs_smooth_eq_cdf, mvs_hv_shift]
  obtain ⟨-, -, h3⟩ := theorem_1 heaviside h 𝒱 hA
  have key := h3 h_ne hchar PX (by simp [h𝒱]) PY (by simp [h𝒱]) hne
  simp_rw [hS, hS']
  exact key
