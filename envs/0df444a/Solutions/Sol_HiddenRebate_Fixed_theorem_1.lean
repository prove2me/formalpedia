-- Prove2me | solution 1 for HiddenRebate.Fixed.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:05:35.049331+00:00
-- url     : https://prove2.me/submissions/4dd6dcef-286b-4687-bdd5-f4881f72ebb7

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model
import Theorems.Thm_HiddenRebate_Fixed_contract_star_ic
import Theorems.Thm_HiddenRebate_Fixed_cost_star_eq


open HiddenRebate.Fixed MeasureTheory Set

namespace HRAux

/-- positive part -/
noncomputable def pp (y : ℝ) : ℝ := max y 0

lemma pp_nonneg (y : ℝ) : 0 ≤ pp y := le_max_right _ _

lemma pp_le_abs (y : ℝ) : pp y ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)

lemma measurable_pp : Measurable pp := measurable_id.max measurable_const

/-- the deviation functional -/
noncomputable def phi (r : ℝ) (σ d : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  d x.2 * pp (x.1 - x.2) + σ x.1 * (1 - d x.2) * pp (x.2 - x.1) - r * σ x.1 * d x.2

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integ_bound (hint : Integrable id μ) (g : ℝ × ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hb : ∀ x, |g x| ≤ C + 2 * (|x.1| + |x.2|)) : Integrable g (μ.prod μ) := by
  have h1 : Integrable (fun x : ℝ × ℝ => x.1) (μ.prod μ) := hint.comp_fst μ
  have h2 : Integrable (fun x : ℝ × ℝ => x.2) (μ.prod μ) := hint.comp_snd μ
  refine Integrable.mono' ((integrable_const C).add ((h1.abs.add h2.abs).const_mul 2))
    hg.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  simpa [Real.norm_eq_abs] using hb x

lemma integ_bound1 (hint : Integrable id μ) (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hb : ∀ x, |g x| ≤ C + |x|) : Integrable g μ := by
  refine Integrable.mono' ((integrable_const C).add hint.abs)
    hg.aestronglyMeasurable (ae_of_all _ (fun x => ?_))
  simpa [Real.norm_eq_abs] using hb x

lemma abs_bound01 {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : |a| ≤ 1 := by
  rw [abs_of_nonneg h0]; exact h1

lemma phi_bound (r : ℝ) (hr : 0 ≤ r) (σ d : ℝ → ℝ) (hσ : ∀ s, 0 ≤ σ s ∧ σ s ≤ 1)
    (hd : ∀ s, 0 ≤ d s ∧ d s ≤ 1) (x : ℝ × ℝ) :
    |phi r σ d x| ≤ r + 2 * (|x.1| + |x.2|) := by
  unfold phi
  obtain ⟨a0, a1⟩ := hσ x.1
  obtain ⟨b0, b1⟩ := hd x.2
  have p1 := pp_le_abs (x.1 - x.2)
  have p2 := pp_le_abs (x.2 - x.1)
  have q1 := pp_nonneg (x.1 - x.2)
  have q2 := pp_nonneg (x.2 - x.1)
  have e1 : |x.1 - x.2| ≤ |x.1| + |x.2| := abs_sub _ _
  have e2 : |x.2 - x.1| ≤ |x.1| + |x.2| := by rw [abs_sub_comm]; exact e1
  have t1 : d x.2 * pp (x.1 - x.2) ≤ |x.1| + |x.2| := by nlinarith
  have t1' : 0 ≤ d x.2 * pp (x.1 - x.2) := mul_nonneg b0 q1
  have t2 : σ x.1 * (1 - d x.2) * pp (x.2 - x.1) ≤ |x.1| + |x.2| := by
    have : σ x.1 * (1 - d x.2) ≤ 1 := by nlinarith
    have h0 : 0 ≤ σ x.1 * (1 - d x.2) := mul_nonneg a0 (by linarith)
    nlinarith
  have t2' : 0 ≤ σ x.1 * (1 - d x.2) * pp (x.2 - x.1) :=
    mul_nonneg (mul_nonneg a0 (by linarith)) q2
  have t3 : 0 ≤ r * σ x.1 * d x.2 := mul_nonneg (mul_nonneg hr a0) b0
  have t3' : r * σ x.1 * d x.2 ≤ r := by
    have : σ x.1 * d x.2 ≤ 1 := by nlinarith
    nlinarith
  rw [abs_le]; constructor <;> nlinarith [abs_nonneg x.1, abs_nonneg x.2]

lemma measurable_phi (r : ℝ) (σ d : ℝ → ℝ) (hσ : Measurable σ) (hd : Measurable d) :
    Measurable (phi r σ d) := by
  unfold phi
  have a : Measurable fun x : ℝ × ℝ => σ x.1 := hσ.comp measurable_fst
  have b : Measurable fun x : ℝ × ℝ => d x.2 := hd.comp measurable_snd
  have c : Measurable fun x : ℝ × ℝ => pp (x.1 - x.2) :=
    measurable_pp.comp (measurable_fst.sub measurable_snd)
  have e : Measurable fun x : ℝ × ℝ => pp (x.2 - x.1) :=
    measurable_pp.comp (measurable_snd.sub measurable_fst)
  exact ((b.mul c).add ((a.mul (measurable_const.sub b)).mul e)).sub
    ((measurable_const.mul a).mul b)

lemma integrable_phi (hint : Integrable id μ) (r : ℝ) (hr : 0 ≤ r) (σ d : ℝ → ℝ)
    (hσm : Measurable σ) (hdm : Measurable d) (hσ : ∀ s, 0 ≤ σ s ∧ σ s ≤ 1)
    (hd : ∀ s, 0 ≤ d s ∧ d s ≤ 1) : Integrable (phi r σ d) (μ.prod μ) := by
  exact integ_bound μ hint _ (measurable_phi r σ d hσm hdm) r (phi_bound r hr σ d hσ hd)

lemma ind01 (U : Set ℝ) (s : ℝ) : 0 ≤ U.indicator (fun _ => (1:ℝ)) s ∧
    U.indicator (fun _ => (1:ℝ)) s ≤ 1 := by
  by_cases h : s ∈ U
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- Step 1 of the bathtub argument: optimise σ for fixed d. -/
lemma step_sigma (hint : Integrable id μ) (r : ℝ) (hr : 0 ≤ r) (σ d : ℝ → ℝ)
    (hσm : Measurable σ) (hdm : Measurable d) (hσ : ∀ s, 0 ≤ σ s ∧ σ s ≤ 1)
    (hd : ∀ s, 0 ≤ d s ∧ d s ≤ 1) :
    ∃ U : Set ℝ, MeasurableSet U ∧ (∀ s s', s ∈ U → s ≤ s' → s' ∈ U) ∧
      ∫ x, phi r (U.indicator (fun _ => 1)) d x ∂(μ.prod μ) ≤ ∫ x, phi r σ d x ∂(μ.prod μ) := by
  set g : ℝ × ℝ → ℝ := fun x => (1 - d x.2) * pp (x.2 - x.1) - r * d x.2 with hg
  set k : ℝ → ℝ := fun s => ∫ t, g (s, t) ∂μ with hk
  have gint : ∀ s, Integrable (fun t => g (s, t)) μ := by
    intro s
    refine integ_bound1 μ hint _ ?_ (r + |s|) (fun t => ?_)
    · exact ((measurable_const.sub hdm).mul (measurable_pp.comp (measurable_id.sub
        measurable_const))).sub (measurable_const.mul hdm)
    · obtain ⟨b0, b1⟩ := hd t
      have p2 := pp_le_abs (t - s)
      have q2 := pp_nonneg (t - s)
      have e : |t - s| ≤ |t| + |s| := abs_sub _ _
      simp only [hg]
      rw [abs_le]; constructor <;> nlinarith [abs_nonneg t, abs_nonneg s]
  have kanti : Antitone k := by
    intro s s' hss
    simp only [hk]
    refine integral_mono (gint s') (gint s) (fun t => ?_)
    simp only [hg]
    obtain ⟨b0, b1⟩ := hd t
    have : pp (t - s') ≤ pp (t - s) := max_le_max (by linarith) le_rfl
    nlinarith
  refine ⟨{s | k s < 0}, measurableSet_lt kanti.measurable measurable_const, ?_, ?_⟩
  · intro s s' hs hss
    exact lt_of_le_of_lt (kanti hss) hs
  set u := ({s | k s < 0} : Set ℝ).indicator (fun _ => (1:ℝ))
  have um : Measurable u := measurable_const.indicator
    (measurableSet_lt kanti.measurable measurable_const)
  have hdiff : ∀ x, phi r σ d x - phi r u d x = (σ x.1 - u x.1) * g x := by
    intro x; simp only [phi, hg]; ring
  rw [← sub_nonneg, ← integral_sub (integrable_phi μ hint r hr σ d hσm hdm hσ hd)
    (integrable_phi μ hint r hr u d um hdm (ind01 _) hd)]
  simp_rw [hdiff]
  have hint2 : Integrable (fun x : ℝ × ℝ => (σ x.1 - u x.1) * g x) (μ.prod μ) := by
    have := (integrable_phi μ hint r hr σ d hσm hdm hσ hd).sub
      (integrable_phi μ hint r hr u d um hdm (ind01 _) hd)
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only [Pi.sub_apply]; exact hdiff x
  rw [integral_prod _ hint2]
  refine integral_nonneg (fun s => ?_)
  simp only
  rw [integral_const_mul]
  show 0 ≤ (σ s - u s) * k s
  obtain ⟨a0, a1⟩ := hσ s
  by_cases hs : k s < 0
  · have : u s = 1 := by simp [u, Set.indicator_of_mem (show s ∈ {s | k s < 0} from hs)]
    rw [this]; nlinarith
  · have : u s = 0 := by simp [u, Set.indicator_of_notMem (show s ∉ {s | k s < 0} from hs)]
    rw [this]; push Not at hs; nlinarith

/-- Step 2: optimise d for fixed σ = 1_U. -/
lemma step_d (hint : Integrable id μ) (r : ℝ) (hr : 0 ≤ r) (σ d : ℝ → ℝ)
    (hσm : Measurable σ) (hdm : Measurable d) (hσ : ∀ s, 0 ≤ σ s ∧ σ s ≤ 1)
    (hd : ∀ s, 0 ≤ d s ∧ d s ≤ 1) :
    ∃ V : Set ℝ, MeasurableSet V ∧ (∀ s s', s ∈ V → s ≤ s' → s' ∈ V) ∧
      ∫ x, phi r σ (V.indicator (fun _ => 1)) x ∂(μ.prod μ) ≤ ∫ x, phi r σ d x ∂(μ.prod μ) := by
  set g : ℝ × ℝ → ℝ := fun x => pp (x.1 - x.2) - σ x.1 * pp (x.2 - x.1) - r * σ x.1 with hg
  set k : ℝ → ℝ := fun t => ∫ s, g (s, t) ∂μ with hk
  have gint : ∀ t, Integrable (fun s => g (s, t)) μ := by
    intro t
    refine integ_bound1 μ hint _ ?_ (r + 2 * |t|) (fun s => ?_)
    · exact ((measurable_pp.comp (measurable_id.sub measurable_const)).sub
        (hσm.mul (measurable_pp.comp (measurable_const.sub measurable_id)))).sub
        (measurable_const.mul hσm)
    · obtain ⟨b0, b1⟩ := hσ s
      have p1 := pp_le_abs (s - t)
      have p2 := pp_le_abs (t - s)
      have q1 := pp_nonneg (s - t)
      have q2 := pp_nonneg (t - s)
      have e : |t - s| ≤ |t| + |s| := abs_sub _ _
      have e' : |s - t| ≤ |s| + |t| := abs_sub _ _
      have hmax : pp (s - t) = 0 ∨ pp (t - s) = 0 := by
        unfold pp
        rcases le_total s t with h | h
        · left; exact max_eq_right (by linarith)
        · right; exact max_eq_right (by linarith)
      simp only [hg]
      rw [abs_le]
      rcases hmax with h | h <;> rw [h] <;> constructor <;>
        nlinarith [abs_nonneg t, abs_nonneg s]
  have kanti : Antitone k := by
    intro t t' htt
    simp only [hk]
    refine integral_mono (gint t') (gint t) (fun s => ?_)
    simp only [hg]
    obtain ⟨b0, b1⟩ := hσ s
    have h1 : pp (s - t') ≤ pp (s - t) := max_le_max (by linarith) le_rfl
    have h2 : pp (t - s) ≤ pp (t' - s) := max_le_max (by linarith) le_rfl
    nlinarith
  refine ⟨{s | k s < 0}, measurableSet_lt kanti.measurable measurable_const, ?_, ?_⟩
  · intro s s' hs hss
    exact lt_of_le_of_lt (kanti hss) hs
  set u := ({s | k s < 0} : Set ℝ).indicator (fun _ => (1:ℝ))
  have um : Measurable u := measurable_const.indicator
    (measurableSet_lt kanti.measurable measurable_const)
  have hdiff : ∀ x, phi r σ d x - phi r σ u x = (d x.2 - u x.2) * g x := by
    intro x; simp only [phi, hg]; ring
  rw [← sub_nonneg, ← integral_sub (integrable_phi μ hint r hr σ d hσm hdm hσ hd)
    (integrable_phi μ hint r hr σ u hσm um hσ (ind01 _))]
  simp_rw [hdiff]
  have hint2 : Integrable (fun x : ℝ × ℝ => (d x.2 - u x.2) * g x) (μ.prod μ) := by
    have := (integrable_phi μ hint r hr σ d hσm hdm hσ hd).sub
      (integrable_phi μ hint r hr σ u hσm um hσ (ind01 _))
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only [Pi.sub_apply]; exact hdiff x
  rw [integral_prod_symm _ hint2]
  refine integral_nonneg (fun t => ?_)
  simp only
  rw [integral_const_mul]
  show 0 ≤ (d t - u t) * k t
  obtain ⟨a0, a1⟩ := hd t
  by_cases hs : k t < 0
  · have : u t = 1 := by simp [u, Set.indicator_of_mem (show t ∈ {s | k s < 0} from hs)]
    rw [this]; nlinarith
  · have : u t = 0 := by simp [u, Set.indicator_of_notMem (show t ∉ {s | k s < 0} from hs)]
    rw [this]; push Not at hs; nlinarith

end

end HRAux

open HiddenRebate.Fixed MeasureTheory Set

namespace HRAux

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma Gbar_eq (t : ℝ) : Gbar μ t = μ.real (Ioi t) := by
  simp [Gbar, measureReal_def]

lemma Gbar_nonneg (t : ℝ) : 0 ≤ Gbar μ t := by rw [Gbar_eq]; exact measureReal_nonneg

lemma Gbar_le_one (t : ℝ) : Gbar μ t ≤ 1 := by
  rw [Gbar_eq]; exact measureReal_le_one

lemma Gbar_anti {a b : ℝ} (h : a ≤ b) : Gbar μ b ≤ Gbar μ a := by
  rw [Gbar_eq, Gbar_eq]; exact measureReal_mono (Ioi_subset_Ioi h)

lemma Iic_zero_null (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0) : μ (Iic 0) = 0 := by
  rw [← Iio_union_right]; exact measure_union_null hneg (hatom 0)

lemma real_Ioi_zero (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0) :
    μ.real (Ioi 0) = 1 := by
  have h := prob_compl_eq_one_sub (μ := μ) (measurableSet_Iic (a := (0:ℝ)))
  rw [compl_Iic, Iic_zero_null μ hneg hatom, tsub_zero] at h
  simp [measureReal_def, h]

lemma ae_pos (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0) :
    ∀ᵐ x ∂(μ.prod μ), 0 < x.1 ∧ 0 < x.2 := by
  rw [ae_iff]
  refine measure_mono_null (t := (Iic 0 ×ˢ univ) ∪ (univ ×ˢ Iic 0)) ?_ ?_
  · intro x hx
    simp only [mem_setOf_eq, not_and_or, not_lt] at hx
    rcases hx with h | h
    · left; exact ⟨h, mem_univ _⟩
    · right; exact ⟨mem_univ _, h⟩
  · refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, Iic_zero_null μ hneg hatom, zero_mul]
    · rw [Measure.prod_prod, Iic_zero_null μ hneg hatom, mul_zero]

/-- upper sets have a threshold -/
lemma upper_thresh (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0) (U : Set ℝ)
    (hU : ∀ s s', s ∈ U → s ≤ s' → s' ∈ U) (hne : U.Nonempty) :
    ∃ a, 0 ≤ a ∧ Ioi a ⊆ U ∧ (∀ s, 0 ≤ s → s < a → s ∉ U) ∧ μ.real U ≤ μ.real (Ioi a) := by
  by_cases hb : BddBelow U
  · set a0 := sInf U
    by_cases ha0 : a0 ≤ 0
    · refine ⟨0, le_rfl, ?_, fun s hs hs' => absurd hs' (not_lt.2 hs), ?_⟩
      · intro s hs
        obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt ha0 hs)
        exact hU u s hu hus.le
      · rw [real_Ioi_zero μ hneg hatom]; exact measureReal_le_one
    · push Not at ha0
      refine ⟨a0, ha0.le, ?_, ?_, ?_⟩
      · intro s hs
        obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt hne hs
        exact hU u s hu hus.le
      · intro s _ hs hsU
        exact absurd (csInf_le hb hsU) (not_le.2 hs)
      · have hsub : U ⊆ Ici a0 := fun s hs => csInf_le hb hs
        calc μ.real U ≤ μ.real (Ici a0) := measureReal_mono hsub
          _ = μ.real (Ioi a0) := by
            simp only [measureReal_def]
            rw [measure_congr (Ioi_ae_eq_Ici' (hatom a0))]
  · refine ⟨0, le_rfl, ?_, fun s hs hs' => absurd hs' (not_lt.2 hs), ?_⟩
    · intro s _
      have : ¬ ∀ u ∈ U, s ≤ u := fun h => hb ⟨s, h⟩
      push Not at this
      obtain ⟨u, hu, hus⟩ := this
      exact hU u s hu hus.le
    · rw [real_Ioi_zero μ hneg hatom]; exact measureReal_le_one

/-- the threshold integrand -/
noncomputable def psi (a T : ℝ) (x : ℝ × ℝ) : ℝ :=
  (if T < x.2 then pp (x.1 - x.2) else 0) +
  (if a < x.1 ∧ 0 ≤ x.2 ∧ x.2 < T then pp (x.2 - x.1) else 0)

lemma psi_nonneg (a T : ℝ) (x : ℝ × ℝ) : 0 ≤ psi a T x := by
  unfold psi
  have := pp_nonneg (x.1 - x.2); have := pp_nonneg (x.2 - x.1)
  split_ifs <;> linarith

lemma psi1_meas (T : ℝ) : Measurable fun x : ℝ × ℝ => if T < x.2 then pp (x.1 - x.2) else 0 :=
  Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (measurable_pp.comp (measurable_fst.sub measurable_snd)) measurable_const

lemma psi2_meas (a T : ℝ) : Measurable fun x : ℝ × ℝ =>
    if a < x.1 ∧ 0 ≤ x.2 ∧ x.2 < T then pp (x.2 - x.1) else 0 :=
  Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)))
    (measurable_pp.comp (measurable_snd.sub measurable_fst)) measurable_const

lemma pp_abs_bound (y z : ℝ) : |pp (y - z)| ≤ 0 + 2 * (|y| + |z|) := by
  rw [abs_of_nonneg (pp_nonneg _)]
  have := pp_le_abs (y - z); have := abs_sub y z
  linarith [abs_nonneg y, abs_nonneg z]

lemma psi1_int (hint : Integrable id μ) (T : ℝ) :
    Integrable (fun x : ℝ × ℝ => if T < x.2 then pp (x.1 - x.2) else 0) (μ.prod μ) := by
  refine integ_bound μ hint _ (psi1_meas T) 0 (fun x => ?_)
  split_ifs
  · exact pp_abs_bound _ _
  · simp; positivity

lemma psi2_int (hint : Integrable id μ) (a T : ℝ) :
    Integrable (fun x : ℝ × ℝ => if a < x.1 ∧ 0 ≤ x.2 ∧ x.2 < T then pp (x.2 - x.1) else 0)
      (μ.prod μ) := by
  refine integ_bound μ hint _ (psi2_meas a T) 0 (fun x => ?_)
  split_ifs
  · have := pp_abs_bound x.2 x.1; linarith
  · simp; positivity

lemma psi_int (hint : Integrable id μ) (a T : ℝ) : Integrable (psi a T) (μ.prod μ) :=
  (psi1_int μ hint T).add (psi2_int μ hint a T)

lemma integral_psi (hint : Integrable id μ) (a T : ℝ) :
    ∫ x, psi a T x ∂(μ.prod μ) =
      (∫ x, (if T < x.2 then pp (x.1 - x.2) else 0) ∂(μ.prod μ)) +
      ∫ x, (if a < x.1 ∧ 0 ≤ x.2 ∧ x.2 < T then pp (x.2 - x.1) else 0) ∂(μ.prod μ) :=
  integral_add (psi1_int μ hint T) (psi2_int μ hint a T)

/-- Num₁ is dominated by ∫ψ. -/
lemma num_le_psi (hint : Integrable id μ) (a T b : ℝ) (hb : 0 < b) (hab : a ≤ b ∨ T ≤ b) :
    rbarNum₁ μ b T ≤ ∫ x, psi a T x ∂(μ.prod μ) := by
  rw [integral_psi μ hint, rbarNum₁]
  refine add_le_add ?_ ?_
  · refine integral_mono_of_nonneg (ae_of_all _ (fun x => ?_)) (psi1_int μ hint T)
      (ae_of_all _ (fun x => ?_))
    · beta_reduce
      split_ifs with h
      · simp only [Pi.zero_apply]; linarith [h.1]
      · exact le_rfl
    · beta_reduce
      have := pp_nonneg (x.1 - x.2)
      split_ifs with h1 h2
      · exact le_max_left _ _
      · exact absurd h1.2 h2
      · exact this
      · exact le_rfl
  · refine integral_mono_of_nonneg (ae_of_all _ (fun x => ?_)) (psi2_int μ hint a T)
      (ae_of_all _ (fun x => ?_))
    · beta_reduce
      split_ifs with h
      · simp only [Pi.zero_apply]; linarith [h.2.1]
      · exact le_rfl
    · beta_reduce
      have := pp_nonneg (x.2 - x.1)
      split_ifs with h1 h2
      · exact le_max_left _ _
      · exfalso; apply h2
        obtain ⟨e1, e2, e3⟩ := h1
        rcases hab with hab | hab
        · exact ⟨by linarith, by linarith, by linarith⟩
        · linarith
      · exact this
      · exact le_rfl

/-- The second term of footnote 15 is dominated by ∫ψ(0,T). -/
lemma term2_le_psi (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0)
    (hint : Integrable id μ) (T : ℝ) (hT : 0 ≤ T) :
    rbarTerm₂ μ T ≤ ∫ x, psi 0 T x ∂(μ.prod μ) := by
  have h1 : Integrable (fun x : ℝ × ℝ => x.1) (μ.prod μ) := hint.comp_fst μ
  have h2 : Integrable (fun x : ℝ × ℝ => x.2) (μ.prod μ) := hint.comp_snd μ
  have eA : (∫ y, (if y < T then y else 0) ∂μ) =
      ∫ x, (if x.2 < T then x.2 else 0) ∂(μ.prod μ) := by
    rw [integral_fun_snd (f := fun y => if y < T then y else 0)]; simp
  have eB : (∫ y, y ∂μ) * Gbar μ T =
      ∫ x, x.1 * (Ioi T).indicator 1 x.2 ∂(μ.prod μ) := by
    rw [integral_prod_mul (f := fun y => y) (g := (Ioi T).indicator 1),
      integral_indicator_one measurableSet_Ioi, Gbar_eq]
  have iA : Integrable (fun x : ℝ × ℝ => if x.2 < T then x.2 else 0) (μ.prod μ) := by
    refine integ_bound μ hint _ (Measurable.ite (measurableSet_lt measurable_snd
      measurable_const) measurable_snd measurable_const) 0 (fun x => ?_)
    split_ifs <;> simp <;> linarith [abs_nonneg x.1, abs_nonneg x.2]
  have iB : Integrable (fun x : ℝ × ℝ => x.1 * (Ioi T).indicator 1 x.2) (μ.prod μ) := by
    refine integ_bound μ hint _ (measurable_fst.mul ((measurable_const.indicator
      measurableSet_Ioi).comp measurable_snd)) 0 (fun x => ?_)
    by_cases h : x.2 ∈ Ioi T
    · simp [Set.indicator_of_mem h]; linarith [abs_nonneg x.1, abs_nonneg x.2]
    · simp [Set.indicator_of_notMem h]; positivity
  have iC : Integrable (fun x : ℝ × ℝ => min x.1 x.2) (μ.prod μ) := h1.inf h2
  have eR : ∫ x, ((if x.2 < T then x.2 else 0) + x.1 * (Ioi T).indicator 1 x.2 - min x.1 x.2)
      ∂(μ.prod μ) = (∫ x, (if x.2 < T then x.2 else 0) ∂(μ.prod μ)) +
        (∫ x, x.1 * (Ioi T).indicator 1 x.2 ∂(μ.prod μ)) - ∫ x, min x.1 x.2 ∂(μ.prod μ) := by
    have e1 := integral_sub (iA.add iB) iC
    have e2 := integral_add iA iB
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
  rw [rbarTerm₂, eA, eB, ← eR]
  refine integral_mono_ae ((iA.add iB).sub iC) (psi_int μ hint 0 T) ?_
  filter_upwards [ae_pos μ hneg hatom] with x hx
  obtain ⟨hs, ht⟩ := hx
  simp only [Pi.add_apply, Pi.sub_apply, psi, pp]
  rcases lt_trichotomy x.2 T with h | h | h
  · have : x.2 ∉ Ioi T := fun h' => absurd (mem_Ioi.1 h') (not_lt.2 h.le)
    simp only [h, if_true, Set.indicator_of_notMem this, not_lt.2 h.le, if_false,
      hs, ht.le, and_self, mul_zero, add_zero, zero_add]
    rcases le_total x.1 x.2 with h' | h'
    · rw [min_eq_left h', max_eq_left (by linarith)]
    · rw [min_eq_right h', max_eq_right (by linarith)]; linarith
  · subst h
    have : x.2 ∉ Ioi x.2 := fun h => lt_irrefl x.2 (mem_Ioi.1 h)
    simp only [lt_irrefl, if_false, Set.indicator_of_notMem this, mul_zero, add_zero,
      and_false]
    have := le_min hs.le ht.le
    linarith
  · have : x.2 ∈ Ioi T := h
    simp only [h, if_true, Set.indicator_of_mem this, Pi.one_apply, mul_one,
      not_lt.2 h.le, if_false, and_false, add_zero, zero_add]
    rcases le_total x.1 x.2 with h' | h'
    · rw [min_eq_left h', max_eq_right (by linarith)]; linarith
    · rw [min_eq_right h', max_eq_left (by linarith)]

end

end HRAux

open HiddenRebate.Fixed MeasureTheory Set

namespace HRAux

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma psi_T0 (a : ℝ) : psi a 0 = psi 0 0 := by
  funext x
  unfold psi
  have e1 : ¬ (a < x.1 ∧ 0 ≤ x.2 ∧ x.2 < 0) := fun h => absurd h.2.1 (not_le.2 h.2.2)
  have e2 : ¬ ((0:ℝ) < x.1 ∧ 0 ≤ x.2 ∧ x.2 < 0) := fun h => absurd h.2.1 (not_le.2 h.2.2)
  rw [if_neg e1, if_neg e2]

lemma thresh_eval (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0)
    (hint : Integrable id μ) (r : ℝ) (hr : 0 ≤ r)
    (h1 : ∀ a T : ℝ, 0 < a → a ≤ T → 0 < Gbar μ T * Gbar μ a →
      r * (Gbar μ T * Gbar μ a) < rbarNum₁ μ a T)
    (h2 : ∀ T : ℝ, 0 ≤ T → r < rbarTerm₂ μ T)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    r * (Gbar μ a * Gbar μ T) ≤ ∫ x, psi a T x ∂(μ.prod μ) := by
  have ga0 := Gbar_nonneg μ a; have ga1 := Gbar_le_one μ a
  have gT0 := Gbar_nonneg μ T; have gT1 := Gbar_le_one μ T
  have hprod1 : Gbar μ a * Gbar μ T ≤ 1 := by nlinarith
  have hprod0 : 0 ≤ Gbar μ a * Gbar μ T := mul_nonneg ga0 gT0
  have hrle : r * (Gbar μ a * Gbar μ T) ≤ r := by nlinarith
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    have := h2 T hT
    have := term2_le_psi μ hneg hatom hint T hT
    linarith
  rcases eq_or_lt_of_le hT with hT0 | hT0
  · subst hT0
    rw [psi_T0]
    have := h2 0 le_rfl
    have := term2_le_psi μ hneg hatom hint 0 le_rfl
    linarith
  rcases eq_or_lt_of_le hprod0 with hp | hp
  · rw [← hp, mul_zero]; exact integral_nonneg (psi_nonneg a T)
  rcases le_total a T with haT | haT
  · have := h1 a T ha0 haT (by rw [mul_comm]; exact hp)
    have := num_le_psi μ hint a T a ha0 (Or.inl le_rfl)
    rw [mul_comm (Gbar μ a)]; linarith
  · have gle : Gbar μ a ≤ Gbar μ T := Gbar_anti μ haT
    have gTpos : 0 < Gbar μ T := by
      rcases eq_or_lt_of_le gT0 with h | h
      · rw [← h, mul_zero] at hp; exact absurd hp (lt_irrefl _)
      · exact h
    have := h1 T T hT0 le_rfl (mul_pos gTpos gTpos)
    have := num_le_psi μ hint a T T hT0 (Or.inr le_rfl)
    have : r * (Gbar μ a * Gbar μ T) ≤ r * (Gbar μ T * Gbar μ T) := by
      apply mul_le_mul_of_nonneg_left _ hr; nlinarith
    linarith

lemma delta_nonneg (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0)
    (hint : Integrable id μ) (r : ℝ) (hr : 0 ≤ r)
    (h1 : ∀ a T : ℝ, 0 < a → a ≤ T → 0 < Gbar μ T * Gbar μ a →
      r * (Gbar μ T * Gbar μ a) < rbarNum₁ μ a T)
    (h2 : ∀ T : ℝ, 0 ≤ T → r < rbarTerm₂ μ T)
    (σ d : ℝ → ℝ) (hσm : Measurable σ) (hdm : Measurable d) (hσ : ∀ s, 0 ≤ σ s ∧ σ s ≤ 1)
    (hd : ∀ s, 0 ≤ d s ∧ d s ≤ 1) :
    0 ≤ ∫ x, phi r σ d x ∂(μ.prod μ) := by
  obtain ⟨U, hUm, hU, hstep1⟩ := step_sigma μ hint r hr σ d hσm hdm hσ hd
  set u := U.indicator (fun _ => (1:ℝ)) with hu
  have um : Measurable u := measurable_const.indicator hUm
  obtain ⟨V, hVm, hV, hstep2⟩ := step_d μ hint r hr u d um hdm (ind01 U) hd
  set v := V.indicator (fun _ => (1:ℝ)) with hv
  have vm : Measurable v := measurable_const.indicator hVm
  refine le_trans ?_ (le_trans hstep2 hstep1)
  -- now evaluate at indicator functions of upper sets
  by_cases hUe : U = ∅
  · refine integral_nonneg (fun x => ?_)
    have : u x.1 = 0 := by simp [hu, hUe]
    simp only [phi, this, zero_mul, mul_zero, add_zero, sub_zero]
    exact mul_nonneg (ind01 V x.2).1 (pp_nonneg _)
  by_cases hVe : V = ∅
  · refine integral_nonneg (fun x => ?_)
    have : v x.2 = 0 := by simp [hv, hVe]
    simp only [phi, this, zero_mul, mul_zero, sub_zero, zero_add, sub_zero, mul_one]
    exact mul_nonneg (ind01 U x.1).1 (pp_nonneg _)
  obtain ⟨a, ha, haU, -, hμU⟩ :=
    upper_thresh μ hneg hatom U hU (Set.nonempty_iff_ne_empty.2 hUe)
  obtain ⟨T, hT, hTV, hTV', hμV⟩ :=
    upper_thresh μ hneg hatom V hV (Set.nonempty_iff_ne_empty.2 hVe)
  set P : ℝ × ℝ → ℝ := fun x => v x.2 * pp (x.1 - x.2) + u x.1 * (1 - v x.2) * pp (x.2 - x.1)
    with hP
  have hPint : Integrable P (μ.prod μ) := by
    refine integ_bound μ hint _ ?_ 0 (fun x => ?_)
    · exact ((vm.comp measurable_snd).mul (measurable_pp.comp (measurable_fst.sub
        measurable_snd))).add (((um.comp measurable_fst).mul (measurable_const.sub
        (vm.comp measurable_snd))).mul (measurable_pp.comp (measurable_snd.sub measurable_fst)))
    · have := phi_bound 0 le_rfl u v (ind01 U) (ind01 V) x
      simp only [phi, zero_mul, sub_zero] at this
      exact this
  have hQint : Integrable (fun x : ℝ × ℝ => u x.1 * v x.2) (μ.prod μ) := by
    refine integ_bound μ hint _ ((um.comp measurable_fst).mul (vm.comp measurable_snd)) 1
      (fun x => ?_)
    obtain ⟨a0, a1⟩ := ind01 U x.1; obtain ⟨b0, b1⟩ := ind01 V x.2
    rw [abs_of_nonneg (mul_nonneg a0 b0)]
    nlinarith [abs_nonneg x.1, abs_nonneg x.2]
  have hsplit : ∫ x, phi r u v x ∂(μ.prod μ) =
      (∫ x, P x ∂(μ.prod μ)) - r * ∫ x, u x.1 * v x.2 ∂(μ.prod μ) := by
    rw [← integral_const_mul, ← integral_sub hPint (hQint.const_mul r)]
    congr 1; funext x; simp only [phi, hP]; ring
  have hQ : ∫ x, u x.1 * v x.2 ∂(μ.prod μ) = μ.real U * μ.real V := by
    rw [integral_prod_mul (f := u) (g := v), hu, hv]
    rw [show (fun _ : ℝ => (1:ℝ)) = 1 from rfl, integral_indicator_one hUm,
      integral_indicator_one hVm]
  have hPpsi : ∫ x, psi a T x ∂(μ.prod μ) ≤ ∫ x, P x ∂(μ.prod μ) := by
    refine integral_mono (psi_int μ hint a T) hPint (fun x => ?_)
    simp only [psi, hP]
    have q1 := pp_nonneg (x.1 - x.2); have q2 := pp_nonneg (x.2 - x.1)
    obtain ⟨a0, a1⟩ := ind01 U x.1; obtain ⟨b0, b1⟩ := ind01 V x.2
    have t1 : (if T < x.2 then pp (x.1 - x.2) else 0) ≤ v x.2 * pp (x.1 - x.2) := by
      split_ifs with h
      · have : v x.2 = 1 := by simp [hv, Set.indicator_of_mem (hTV h)]
        rw [this, one_mul]
      · exact mul_nonneg b0 q1
    have t2 : (if a < x.1 ∧ 0 ≤ x.2 ∧ x.2 < T then pp (x.2 - x.1) else 0) ≤
        u x.1 * (1 - v x.2) * pp (x.2 - x.1) := by
      split_ifs with h
      · have e1 : u x.1 = 1 := by simp [hu, Set.indicator_of_mem (haU h.1)]
        have e2 : v x.2 = 0 := by
          simp [hv, Set.indicator_of_notMem (hTV' x.2 h.2.1 h.2.2)]
        rw [e1, e2]; ring_nf; exact le_rfl
      · exact mul_nonneg (mul_nonneg a0 (by linarith)) q2
    linarith
  have hev := thresh_eval μ hneg hatom hint r hr h1 h2 a T ha hT
  have hmU : μ.real U * μ.real V ≤ Gbar μ a * Gbar μ T := by
    rw [Gbar_eq, Gbar_eq]
    exact mul_le_mul hμU hμV measureReal_nonneg measureReal_nonneg
  rw [hsplit, hQ]
  have : r * (μ.real U * μ.real V) ≤ r * (Gbar μ a * Gbar μ T) :=
    mul_le_mul_of_nonneg_left hmU hr
  linarith

end

end HRAux

open HiddenRebate.Fixed MeasureTheory Set

namespace HRAux

lemma payoff_truth (r : ℝ) (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) (q : ℝ × ℝ) :
    payoff r A F q q = (if A q = .W then r else 0) + F q := by
  simp [payoff]

lemma supplier_cases (a : Supplier) : a = .S ∨ a = .W := by cases a <;> simp

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma lower_bound (hneg : μ (Iio 0) = 0) (hatom : ∀ a : ℝ, μ {a} = 0)
    (hint : Integrable id μ) (r : ℝ) (hr : 0 ≤ r)
    (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) (hF : Feasible A F) (hIC : IsIC r A F)
    (hc : Integrable (costIntegrand r A F) (μ.prod μ)) :
    ∃ σ d : ℝ → ℝ, Measurable σ ∧ Measurable d ∧ (∀ s, 0 ≤ σ s ∧ σ s ≤ 1) ∧
      (∀ s, 0 ≤ d s ∧ d s ≤ 1) ∧
      (∫ x, (min x.1 x.2 + r) ∂(μ.prod μ)) + ∫ x, phi r σ d x ∂(μ.prod μ) ≤ cost μ r A F := by
  obtain ⟨hF0, hSW, hFm⟩ := hF
  have hWS : MeasurableSet {z : ℝ × ℝ | A z = .W} := by
    have : {z : ℝ × ℝ | A z = .W} = {z | A z = .S}ᶜ := by
      ext z; simp only [mem_setOf_eq, mem_compl_iff]
      rcases supplier_cases (A z) with h | h <;> simp [h]
    rw [this]; exact hSW.compl
  have hf : Measurable fun x : ℝ × ℝ => quote r x :=
    measurable_fst.prodMk (measurable_snd.add_const r)
  set EW : Set (ℝ × ℝ) := (fun x => quote r x) ⁻¹' {z | A z = .W} with hEW
  set ES : Set (ℝ × ℝ) := (fun x => quote r x) ⁻¹' {z | A z = .S} with hES
  have mEW : MeasurableSet EW := hf hWS
  have mES : MeasurableSet ES := hf hSW
  set D : Set ℝ := {t | μ ((fun s => (s, t)) ⁻¹' EW) = 0} with hD
  have mD : MeasurableSet D :=
    (measurable_measure_prodMk_right mEW) (measurableSet_singleton 0)
  set E2 : Set (ℝ × ℝ) := (Prod.snd ⁻¹' Dᶜ) ∩ ES with hE2
  have mE2 : MeasurableSet E2 := (measurable_snd mD.compl).inter mES
  set Sg : Set ℝ := {s | μ (Prod.mk s ⁻¹' E2) = 0} with hSg
  have mSg : MeasurableSet Sg :=
    (measurable_measure_prodMk_left mE2) (measurableSet_singleton 0)
  set σ := Sg.indicator (fun _ => (1:ℝ)) with hσ
  set d := D.indicator (fun _ => (1:ℝ)) with hd
  have σm : Measurable σ := measurable_const.indicator mSg
  have dm : Measurable d := measurable_const.indicator mD
  refine ⟨σ, d, σm, dm, ind01 Sg, ind01 D, ?_⟩
  -- (c): rows outside D give the intermediary at least r
  have keyc : ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → x.2 ∉ D →
      r ≤ payoff r A F (quote r x) (quote r x) := by
    intro x h1 h2 hxD
    have hne : ((fun s => (s, x.2)) ⁻¹' EW).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact hxD (by simp only [hD, mem_setOf_eq, h, measure_empty])
    obtain ⟨s0, hs0⟩ := hne
    have hA : A (s0, x.2 + r) = .W := hs0
    have := hIC x h1 h2 (s0, x.2 + r)
    have e : payoff r A F (s0, x.2 + r) (quote r x) = r + F (s0, x.2 + r) := by
      simp [payoff, hA, sel, quote]
    rw [e] at this
    linarith [hF0 (s0, x.2 + r)]
  -- (d): columns outside Sg pay at least r on S-points
  have keyd : ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → x.1 ∉ Sg → A (quote r x) = .S →
      r ≤ F (quote r x) := by
    intro x h1 h2 hxS hAS
    have hne : ∃ t, 0 ≤ t ∧ (x.1, t) ∈ E2 := by
      by_contra h
      push Not at h
      apply hxS
      show μ (Prod.mk x.1 ⁻¹' E2) = 0
      refine measure_mono_null (fun t ht => ?_) hneg
      by_contra ht'
      exact h t (not_lt.1 ht') ht
    obtain ⟨t, ht0, htD, htS⟩ := hne
    have hA' : A (quote r (x.1, t)) = .S := htS
    have c' := keyc (x.1, t) h1 ht0 htD
    rw [payoff_truth, hA'] at c'
    simp only [reduceCtorEq, if_false, zero_add] at c'
    have := hIC x h1 h2 (quote r (x.1, t))
    rw [payoff_truth, hAS] at this
    simp only [payoff, hA', reduceCtorEq, if_false, zero_add, sel, quote] at this
    have hA'' : A (x.1, t + r) = .S := hA'
    simp only [hA'', reduceCtorEq, if_false, zero_add, if_true, mul_one] at this
    simp only [quote] at c' ⊢
    linarith
  -- null sets
  have hN1 : (μ.prod μ) {x | x.2 ∈ D ∧ x ∈ EW} = 0 := by
    have m : MeasurableSet {x : ℝ × ℝ | x.2 ∈ D ∧ x ∈ EW} := (measurable_snd mD).inter mEW
    rw [Measure.prod_apply_symm m]
    refine (lintegral_congr (fun t => ?_)).trans (lintegral_zero)
    by_cases ht : t ∈ D
    · refine measure_mono_null (fun s hs => hs.2) ht
    · have : (fun s => (s, t)) ⁻¹' {x : ℝ × ℝ | x.2 ∈ D ∧ x ∈ EW} = ∅ := by
        ext s; simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => ht h.1
      rw [this, measure_empty]
  have hN2 : (μ.prod μ) {x | x.1 ∈ Sg ∧ x ∈ E2} = 0 := by
    have m : MeasurableSet {x : ℝ × ℝ | x.1 ∈ Sg ∧ x ∈ E2} := (measurable_fst mSg).inter mE2
    rw [Measure.prod_apply m]
    refine (lintegral_congr (fun s => ?_)).trans (lintegral_zero)
    by_cases hs : s ∈ Sg
    · exact measure_mono_null (fun t ht => ht.2) hs
    · have : Prod.mk s ⁻¹' {x : ℝ × ℝ | x.1 ∈ Sg ∧ x ∈ E2} = ∅ := by
        ext t; simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => hs h.1
      rw [this, measure_empty]
  have ae1 : ∀ᵐ x ∂(μ.prod μ), ¬ (x.2 ∈ D ∧ x ∈ EW) := by
    rw [ae_iff]; simpa using hN1
  have ae2 : ∀ᵐ x ∂(μ.prod μ), ¬ (x.1 ∈ Sg ∧ x ∈ E2) := by
    rw [ae_iff]; simpa using hN2
  have h1 : Integrable (fun x : ℝ × ℝ => x.1) (μ.prod μ) := hint.comp_fst μ
  have h2 : Integrable (fun x : ℝ × ℝ => x.2) (μ.prod μ) := hint.comp_snd μ
  have iM : Integrable (fun x : ℝ × ℝ => min x.1 x.2 + r) (μ.prod μ) :=
    (h1.inf h2).add (integrable_const r)
  have iP := integrable_phi μ hint r hr σ d σm dm (ind01 Sg) (ind01 D)
  rw [← integral_add iM iP, cost]
  refine integral_mono_ae (iM.add iP) hc ?_
  filter_upwards [ae_pos μ hneg hatom, ae1, ae2] with x hx hx1 hx2
  obtain ⟨hs, ht⟩ := hx
  simp only [Pi.add_apply, phi, costIntegrand]
  have hmin1 : min x.1 x.2 + pp (x.1 - x.2) = x.1 := by
    unfold pp; rcases le_total x.1 x.2 with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hmin2 : min x.1 x.2 + pp (x.2 - x.1) = x.2 := by
    unfold pp; rcases le_total x.1 x.2 with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  have q1 := pp_nonneg (x.1 - x.2); have q2 := pp_nonneg (x.2 - x.1)
  have hF0q := hF0 (quote r x)
  obtain ⟨σ0, σ1⟩ := ind01 Sg x.1
  rcases supplier_cases (A (quote r x)) with hA | hA
  · -- S selected
    have hsel : sel (A (quote r x)) (quote r x) = x.1 := by rw [hA]; rfl
    rw [hsel]
    by_cases htD : x.2 ∈ D
    · have dv : d x.2 = 1 := by simp [hd, Set.indicator_of_mem htD]
      rw [dv]
      by_cases hsS : x.1 ∈ Sg
      · have sv : σ x.1 = 1 := by simp [hσ, Set.indicator_of_mem hsS]
        rw [sv]; linarith
      · have sv : σ x.1 = 0 := by simp [hσ, Set.indicator_of_notMem hsS]
        rw [sv]
        have := keyd x hs.le ht.le hsS hA
        linarith
    · have dv : d x.2 = 0 := by simp [hd, Set.indicator_of_notMem htD]
      rw [dv]
      have hsS : x.1 ∉ Sg := fun h => hx2 ⟨h, htD, hA⟩
      have sv : σ x.1 = 0 := by simp [hσ, Set.indicator_of_notMem hsS]
      rw [sv]
      have := keyc x hs.le ht.le htD
      rw [payoff_truth, hA] at this
      simp only [reduceCtorEq, if_false, zero_add] at this
      have : min x.1 x.2 ≤ x.1 := min_le_left _ _
      linarith
  · -- W selected
    have hsel : sel (A (quote r x)) (quote r x) = x.2 + r := by rw [hA]; rfl
    rw [hsel]
    have htD : x.2 ∉ D := fun h => hx1 ⟨h, hA⟩
    have dv : d x.2 = 0 := by simp [hd, Set.indicator_of_notMem htD]
    rw [dv]
    have : σ x.1 * pp (x.2 - x.1) ≤ pp (x.2 - x.1) := by nlinarith
    linarith

end

end HRAux

open HiddenRebate.Fixed MeasureTheory Set

namespace HRAux

lemma lt_of_lt_sInf' {S : Set ℝ} {r : ℝ} (hr0 : 0 ≤ r) (h : r < sInf S) {ρ : ℝ}
    (hρ : ρ ∈ S) : r < ρ := by
  by_cases hb : BddBelow S
  · exact lt_of_lt_of_le h (csInf_le hb hρ)
  · rw [Real.sInf_of_not_bddBelow hb] at h; linarith

end HRAux

theorem solution (μ : Measure ℝ) (r : ℝ) (hμ : Standing μ r) (hr : r < rbar μ) :
    Feasible (contractStar r).1 (contractStar r).2 ∧
    IsIC r (contractStar r).1 (contractStar r).2 ∧
    Integrable (costIntegrand r (contractStar r).1 (contractStar r).2) (μ.prod μ) ∧
    ∀ (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ), Feasible A F → IsIC r A F →
      Integrable (costIntegrand r A F) (μ.prod μ) →
      cost μ r (contractStar r).1 (contractStar r).2 ≤ cost μ r A F := by
  have hμ' := hμ
  obtain ⟨hprob, hneg, hac, hint, hr0⟩ := hμ'
  have hatom : ∀ a : ℝ, μ {a} = 0 := fun a => hac (Real.volume_singleton)
  obtain ⟨hfeas, hic, -⟩ := contract_star_ic r hr0
  obtain ⟨hcint, hceq⟩ := cost_star_eq μ r hμ
  refine ⟨hfeas, hic, hcint, ?_⟩
  intro A F hF hIC hc
  have hr1 : r < sInf {ρ | ∃ a T : ℝ, 0 < a ∧ a ≤ T ∧ 0 < Gbar μ T * Gbar μ a ∧
      ρ = rbarNum₁ μ a T / (Gbar μ T * Gbar μ a)} := lt_of_lt_of_le hr (min_le_left _ _)
  have hr2 : r < sInf {ρ | ∃ T : ℝ, 0 ≤ T ∧ ρ = rbarTerm₂ μ T} :=
    lt_of_lt_of_le hr (min_le_right _ _)
  have h1 : ∀ a T : ℝ, 0 < a → a ≤ T → 0 < Gbar μ T * Gbar μ a →
      r * (Gbar μ T * Gbar μ a) < rbarNum₁ μ a T := by
    intro a T ha haT hp
    have := HRAux.lt_of_lt_sInf' hr0 hr1 ⟨a, T, ha, haT, hp, rfl⟩
    rwa [lt_div_iff₀ hp] at this
  have h2 : ∀ T : ℝ, 0 ≤ T → r < rbarTerm₂ μ T := fun T hT =>
    HRAux.lt_of_lt_sInf' hr0 hr2 ⟨T, hT, rfl⟩
  obtain ⟨σ, d, σm, dm, hσ, hd, hlb⟩ :=
    HRAux.lower_bound μ hneg hatom hint r hr0 A F hF hIC hc
  have hδ := HRAux.delta_nonneg μ hneg hatom hint r hr0 h1 h2 σ d σm dm hσ hd
  rw [hceq]
  linarith

