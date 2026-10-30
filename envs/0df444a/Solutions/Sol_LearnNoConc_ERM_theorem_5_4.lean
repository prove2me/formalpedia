-- Prove2me | solution 1 for LearnNoConc.ERM.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T12:29:52.910442+00:00
-- url     : https://prove2.me/submissions/7f9d38a5-6ebf-4de1-8a85-8be1a4d2cbaf

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting
open MeasureTheory
namespace Queelius.SmallBallCutoff
noncomputable def cutoff (τ t : ℝ) : ℝ := min 1 (max 0 (|t|/τ-1))
lemma bounds (τ t : ℝ) : 0 ≤ cutoff τ t ∧ cutoff τ t ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
lemma measurable_cutoff (τ : ℝ) : Measurable (cutoff τ) := by unfold cutoff;fun_prop
lemma sandwich (τ t : ℝ) (hτ : 0 < τ) :
    (if 2*τ ≤ |t| then (1:ℝ) else 0) ≤ cutoff τ t ∧
      cutoff τ t ≤ (if τ ≤ |t| then (1:ℝ) else 0) := by
  constructor
  · by_cases ht : 2*τ ≤ |t|
    · have hd : 1 ≤ |t|/τ-1 := by have hh := (le_div_iff₀ hτ).mpr ht;linarith
      simp only [if_pos ht,cutoff,min_eq_left (le_max_of_le_right hd)]
      exact le_rfl
    · simpa only [if_neg ht] using (bounds τ t).1
  · by_cases ht : τ ≤ |t|
    · simpa only [if_pos ht] using (bounds τ t).2
    · have hd : |t|/τ-1 ≤ 0 := by have hh := (div_lt_one hτ).mpr (lt_of_not_ge ht);linarith
      simp [ht,cutoff,max_eq_left hd]
lemma lipschitz (τ : ℝ) (hτ : 0 < τ) (x y : ℝ) :
    |cutoff τ x-cutoff τ y| ≤ |x-y|/τ := by
  have hmin := abs_min_sub_min_le_max (1:ℝ) (max 0 (|x|/τ-1)) 1 (max 0 (|y|/τ-1))
  have hmax := abs_max_sub_max_le_max (0:ℝ) (|x|/τ-1) 0 (|y|/τ-1)
  have h1 : |cutoff τ x-cutoff τ y| ≤ |max 0 (|x|/τ-1)-max 0 (|y|/τ-1)| := by
    simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg (max 0 (|x|/τ-1)-max 0 (|y|/τ-1))),cutoff] using hmin
  have h2 : |max 0 (|x|/τ-1)-max 0 (|y|/τ-1)| ≤ |(|x|/τ-1)-(|y|/τ-1)| := by
    simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg ((|x|/τ-1)-(|y|/τ-1)))] using hmax
  have he : |x|/τ-1-(|y|/τ-1)=(|x|-|y|)/τ := by ring
  have h3 : |(|x|/τ-1)-(|y|/τ-1)| ≤ |x-y|/τ := by
    rw [he,abs_div,abs_of_pos hτ]
    exact div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) hτ.le
  exact (h1.trans h2).trans h3
lemma cutoff_zero (τ : ℝ) : cutoff τ 0=0 := by simp [cutoff]
lemma boundary_control : cutoff 1 1=0 ∧ cutoff 1 2=1 ∧
    (if (1:ℝ) ≤ |(1:ℝ)| then (1:ℝ) else 0)=1 := by norm_num [cutoff]
lemma empirical_upper {N : ℕ} (τ : ℝ) (hτ : 0 < τ) (v : Fin N → ℝ) :
    (∑ i,cutoff τ (v i)) ≤ ((Finset.univ.filter fun i => τ ≤ |v i|).card : ℝ) := by
  classical
  calc
    _ ≤ ∑ i : Fin N,if τ ≤ |v i| then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun i _ => (sandwich τ (v i) hτ).2)
    _ = _ := by rw [Finset.sum_ite];simp
lemma population_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → ℝ) (hm : Measurable h) (τ : ℝ) (hτ : 0 < τ) :
    μ.real {x | 2*τ ≤ |h x|} ≤ ∫ x,cutoff τ (h x) ∂μ := by
  have he : MeasurableSet {x | 2*τ ≤ |h x|} := measurableSet_le measurable_const hm.abs
  have hi : Integrable (fun x => cutoff τ (h x)) μ :=
    Integrable.of_mem_Icc 0 1 ((measurable_cutoff τ).comp hm).aemeasurable (ae_of_all _ (fun x => bounds τ (h x)))
  have hib : Integrable (Set.indicator {x | 2*τ ≤ |h x|} (fun _ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator he
  calc
    _ = ∫ x,Set.indicator {x | 2*τ ≤ |h x|} (fun _ => (1:ℝ)) x ∂μ := by
      rw [integral_indicator he]
      simp
    _ ≤ _ := integral_mono hib hi (fun x => by
      simpa only [Set.indicator_apply,Set.mem_setOf_eq] using (sandwich τ (h x) hτ).1)
lemma empirical_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → ℝ) (hm : Measurable h) (τ : ℝ) (hτ : 0 < τ)
    (N : ℕ) (hN : 0 < N) (x : Fin N → Ω) :
    μ.real {z | 2*τ ≤ |h z|}-
      |(∑ i,cutoff τ (h (x i)))/(N:ℝ)-(∫ z,cutoff τ (h z) ∂μ)| ≤
      ((Finset.univ.filter fun i => τ ≤ |h (x i)|).card : ℝ)/N := by
  have hp := population_lower μ h hm τ hτ
  have he := div_le_div_of_nonneg_right (empirical_upper τ hτ (fun i => h (x i))) (Nat.cast_nonneg N)
  have ha := neg_abs_le ((∑ i,cutoff τ (h (x i)))/(N:ℝ)-(∫ z,cutoff τ (h z) ∂μ))
  linarith
lemma bounded_average_difference {N : ℕ} (hN : 0 < N) (a b : Fin N → ℝ)
    (ha : ∀ i,0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i,0 ≤ b i ∧ b i ≤ 1)
    (k : Fin N) (heq : ∀ i,i ≠ k → a i=b i) :
    |(∑ i,a i)/(N:ℝ)-(∑ i,b i)/(N:ℝ)| ≤ 1/(N:ℝ) := by
  have hs : (∑ i,a i)-(∑ i,b i)=a k-b k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single k
    · intro i _ hik;rw [heq i hik,sub_self]
    · intro hk;exact False.elim (hk (Finset.mem_univ k))
  rw [← sub_div,hs,abs_div,abs_of_pos (Nat.cast_pos.mpr hN : (0:ℝ) < N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply abs_le.mpr
  constructor <;> linarith [(ha k).1,(ha k).2,(hb k).1,(hb k).2]
lemma cutoff_average_difference {Ω : Type*} (h : Ω → ℝ) (τ : ℝ)
    (N : ℕ) (hN : 0 < N) (x y : Fin N → Ω) (k : Fin N)
    (heq : ∀ i,i ≠ k → x i=y i) :
    |(∑ i,cutoff τ (h (x i)))/(N:ℝ)-(∑ i,cutoff τ (h (y i)))/(N:ℝ)| ≤ 1/(N:ℝ) := by
  apply bounded_average_difference hN _ _ (fun i => bounds τ (h (x i)))
    (fun i => bounds τ (h (y i))) k
  intro i hik
  rw [heq i hik]
end Queelius.SmallBallCutoff
namespace Queelius.SmallBallCutoff
open Filter Topology LearnNoConc.ERM
open scoped ENNReal
lemma continuous_cutoff (τ : ℝ) : Continuous (cutoff τ) := by unfold cutoff;fun_prop
noncomputable def centered {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℝ)
    (N : ℕ) (h : Ω → ℝ) (x : Fin N → Ω) : ℝ :=
  (∑ i,cutoff τ (h (x i)))/(N:ℝ)-(∫ z,cutoff τ (h z) ∂μ)
noncomputable def deviation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℝ)
    (N : ℕ) (h : Ω → ℝ) (x : Fin N → Ω) : ℝ≥0∞ := ENNReal.ofReal |centered μ τ N h x|
noncomputable def process {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℝ)
    (N : ℕ) (H : Set (Ω → ℝ)) (x : Fin N → Ω) : ℝ≥0∞ := ⨆ h ∈ H,deviation μ τ N h x
lemma deviation_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℝ)
    (N : ℕ) (h : Ω → ℝ) (hm : Measurable h) : Measurable (deviation μ τ N h) := by
  have hi (i : Fin N) : Measurable (fun x : Fin N → Ω => cutoff τ (h (x i))) :=
    ((measurable_cutoff τ).comp hm).comp (measurable_pi_apply i)
  unfold deviation centered
  fun_prop
lemma mean_converges {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (u : ℕ → Ω → ℝ) (h : Ω → ℝ) (hm : ∀ n,Measurable (u n))
    (hl : ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x))) :
    Tendsto (fun n => ∫ z,cutoff τ (u n z) ∂μ) atTop (𝓝 (∫ z,cutoff τ (h z) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
  · intro n;exact ((measurable_cutoff τ).comp (hm n)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (bounds τ (u n x)).1];exact (bounds τ (u n x)).2)
  · exact ae_of_all _ (fun x => (continuous_cutoff τ).continuousAt.tendsto.comp (hl x))
lemma deviation_converges {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (u : ℕ → Ω → ℝ) (h : Ω → ℝ) (hm : ∀ n,Measurable (u n))
    (hl : ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x))) (x : Fin N → Ω) :
    Tendsto (fun n => deviation μ τ N (u n) x) atTop (𝓝 (deviation μ τ N h x)) := by
  have hs : Tendsto (fun n => ∑ i : Fin N,cutoff τ (u n (x i))) atTop
      (𝓝 (∑ i : Fin N,cutoff τ (h (x i)))) := by
    apply tendsto_finset_sum
    intro i _
    exact (continuous_cutoff τ).continuousAt.tendsto.comp (hl (x i))
  have hc := (hs.div_const (N:ℝ)).sub (mean_converges μ τ u h hm hl)
  have he : Continuous (fun t : ℝ => ENNReal.ofReal |t|) := ENNReal.continuous_ofReal.comp continuous_abs
  exact he.continuousAt.tendsto.comp hc
lemma countable_process {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (H G : Set (Ω → ℝ)) (hGH : G ⊆ H) (hm : ∀ h ∈ H,Measurable h)
    (hd : ∀ h ∈ H,∃ u : ℕ → Ω → ℝ,(∀ n,u n ∈ G) ∧
      ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x))) : process μ τ N H=process μ τ N G := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro h
    apply iSup_le
    intro hh
    obtain ⟨u,hu,hl⟩ := hd h hh
    apply le_of_tendsto (deviation_converges μ τ N u h (fun n => hm _ (hGH (hu n))) hl x)
    exact Filter.Eventually.of_forall (fun n => le_iSup_of_le (u n) (le_iSup_of_le (hu n) le_rfl))
  · apply iSup_le
    intro h
    apply iSup_le
    intro hh
    exact le_iSup_of_le h (le_iSup_of_le (hGH hh) le_rfl)
lemma process_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) : Measurable (process μ τ N H) := by
  obtain ⟨G,hGH,hG,hd⟩ := hsep
  have ha : ∀ h ∈ H,∃ u : ℕ → Ω → ℝ,(∀ n,u n ∈ G) ∧
      ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x)) := by
    intro h hh
    obtain ⟨u,hu,hl,_⟩ := hd h hh
    exact ⟨u,hu,hl⟩
  rw [countable_process μ τ N H G hGH hm ha]
  exact Measurable.biSup G hG (fun h hh => deviation_measurable μ τ N h (hm h (hGH hh)))

lemma centered_abs_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (h : Ω → ℝ) (hm : Measurable h) (x : Fin N → Ω) :
    |centered μ τ N h x| ≤ 1 := by
  have hi : Integrable (fun z => cutoff τ (h z)) μ :=
    Integrable.of_mem_Icc 0 1 ((measurable_cutoff τ).comp hm).aemeasurable
      (ae_of_all _ (fun z => bounds τ (h z)))
  have hI0 : 0 ≤ ∫ z,cutoff τ (h z) ∂μ := integral_nonneg (fun z => (bounds τ (h z)).1)
  have hI1 : (∫ z,cutoff τ (h z) ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫ z,(1:ℝ) ∂μ := integral_mono hi (integrable_const 1) (fun z => (bounds τ (h z)).2)
      _ = 1 := by simp
  have hs0 : 0 ≤ ∑ i : Fin N,cutoff τ (h (x i)) := Finset.sum_nonneg (fun i _ => (bounds τ (h (x i))).1)
  have hs1 : (∑ i : Fin N,cutoff τ (h (x i))) ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ i : Fin N,(1:ℝ) := Finset.sum_le_sum (fun i _ => (bounds τ (h (x i))).2)
      _ = _ := by simp
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hm0 := div_nonneg hs0 hn.le
  have hm1 := (div_le_one hn).mpr hs1
  unfold centered
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma process_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (x : Fin N → Ω) : process μ τ N H x ≤ 1 := by
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  exact (ENNReal.ofReal_le_one).mpr (centered_abs_le_one μ τ N hN h (hm h hh) x)
lemma deviation_change {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℝ)
    (N : ℕ) (hN : 0 < N) (h : Ω → ℝ) (x y : Fin N → Ω) (k : Fin N)
    (heq : ∀ i,i ≠ k → x i=y i) :
    deviation μ τ N h x ≤ deviation μ τ N h y+ENNReal.ofReal (1/(N:ℝ)) := by
  have hb := cutoff_average_difference h τ N hN x y k heq
  have hc : |centered μ τ N h x-centered μ τ N h y| ≤ 1/(N:ℝ) := by
    simpa only [centered,sub_sub_sub_cancel_right] using hb
  have ha := abs_sub_abs_le_abs_sub (centered μ τ N h x) (centered μ τ N h y)
  unfold deviation
  rw [← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith
lemma process_change {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℝ)
    (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (x y : Fin N → Ω) (k : Fin N)
    (heq : ∀ i,i ≠ k → x i=y i) :
    process μ τ N H x ≤ process μ τ N H y+ENNReal.ofReal (1/(N:ℝ)) := by
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  have hp : deviation μ τ N h y ≤ process μ τ N H y :=
    le_iSup_of_le h (le_iSup_of_le hh le_rfl)
  exact (deviation_change μ τ N hN h x y k heq).trans (add_le_add hp le_rfl)
lemma real_process_change {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (x y : Fin N → Ω) (k : Fin N) (heq : ∀ i,i ≠ k → x i=y i) :
    |(process μ τ N H x).toReal-(process μ τ N H y).toReal| ≤ 1/(N:ℝ) := by
  have finite (z : Fin N → Ω) : process μ τ N H z ≠ ⊤ :=
    ne_of_lt ((process_le_one μ τ N hN H hm z).trans_lt (by simp))
  have oneSide (v z : Fin N → Ω) (hz : ∀ i,i ≠ k → v i=z i) :
      (process μ τ N H v).toReal ≤ (process μ τ N H z).toReal+1/(N:ℝ) := by
    have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finite z,ENNReal.ofReal_ne_top⟩)
      (process_change μ τ N hN H v z k hz)
    rw [ENNReal.toReal_add (finite z) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at he
    exact he
  have h1 := oneSide x y heq
  have h2 := oneSide y x (fun i hi => (heq i hi).symm)
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma real_process_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    Integrable (fun x => (process μ τ N H x).toReal) (Measure.pi fun _ : Fin N => μ) := by
  apply Integrable.of_mem_Icc 0 1
    (ENNReal.measurable_toReal.comp (process_measurable μ τ N H hm hsep)).aemeasurable
  exact ae_of_all _ (fun x => ⟨ENNReal.toReal_nonneg,by
    have h := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ⊤) (process_le_one μ τ N hN H hm x)
    simpa using h⟩)

lemma process_ready {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    Measurable (process μ τ N H) ∧
    Integrable (fun x => (process μ τ N H x).toReal) (Measure.pi fun _ : Fin N => μ) ∧
    (∀ x : Fin N → Ω,process μ τ N H x ≤ 1) ∧
    ∀ (x y : Fin N → Ω) (k : Fin N),(∀ i,i ≠ k → x i=y i) →
      |(process μ τ N H x).toReal-(process μ τ N H y).toReal| ≤ 1/(N:ℝ) := by
  exact ⟨process_measurable μ τ N H hm hsep,real_process_integrable μ τ N hN H hm hsep,
    process_le_one μ τ N hN H hm,fun x y k heq => real_process_change μ τ N hN H hm x y k heq⟩
end Queelius.SmallBallCutoff
open MeasureTheory LearnNoConc.ERM in
 theorem _root_.prior_process {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    Measurable (Queelius.SmallBallCutoff.process μ τ N H) ∧
    Integrable (fun x => (Queelius.SmallBallCutoff.process μ τ N H x).toReal)
      (Measure.pi fun _ : Fin N => μ) ∧
    (∀ x : Fin N → Ω,Queelius.SmallBallCutoff.process μ τ N H x ≤ 1) ∧
    ∀ (x y : Fin N → Ω) (k : Fin N),(∀ i,i ≠ k → x i=y i) →
      |(Queelius.SmallBallCutoff.process μ τ N H x).toReal-
        (Queelius.SmallBallCutoff.process μ τ N H y).toReal| ≤ 1/(N:ℝ) := by
  exact Queelius.SmallBallCutoff.process_ready μ τ N hN H hm hsep

namespace Queelius.ProductConcentration
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
lemma section_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (F : α × β → ℝ) (hF : Measurable F)
    (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1) (a : α) : Integrable (fun b => F (a,b)) ν := by
  exact Integrable.of_mem_Icc 0 1 (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
    (ae_of_all _ (fun b => hb (a,b)))
lemma section_mean {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (F : α × β → ℝ) (hF : Measurable F)
    (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1) :
    Measurable (fun a => ∫ b,F (a,b) ∂ν) ∧ ∀ a,0 ≤ (∫ b,F (a,b) ∂ν) ∧ (∫ b,F (a,b) ∂ν) ≤ 1 := by
  refine ⟨hF.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  intro a
  refine ⟨integral_nonneg (fun b => (hb (a,b)).1),?_⟩
  calc
    _ ≤ ∫ b,(1:ℝ) ∂ν := integral_mono (section_integrable ν F hF hb a) (integrable_const 1)
      (fun b => (hb (a,b)).2)
    _ = 1 := by simp
lemma section_oscillation {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (F : α × β → ℝ) (hF : Measurable F)
    (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1) (a a' : α) (c : ℝ)
    (hc : ∀ b,|F (a,b)-F (a',b)| ≤ c) :
    |(∫ b,F (a,b) ∂ν)-(∫ b,F (a',b) ∂ν)| ≤ c := by
  rw [← integral_sub (section_integrable ν F hF hb a) (section_integrable ν F hF hb a')]
  have he := norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun b => F (a,b)-F (a',b)) (C:=c) (ae_of_all _ (fun b => by simpa only [Real.norm_eq_abs] using hc b))
  simpa [Real.norm_eq_abs] using he
lemma centered_product_subgaussian {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (hF : Measurable F) (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1)
    (c₁ c₂ : ℝ≥0)
    (hsections : ∀ a,HasSubgaussianMGF (fun b => F (a,b)-(∫ v,F (a,v) ∂ν)) c₂ ν)
    (hmean : HasSubgaussianMGF (fun a => (∫ b,F (a,b) ∂ν)-(∫ u,∫ b,F (u,b) ∂ν ∂μ)) c₁ μ) :
    HasSubgaussianMGF (fun z => F z-(∫ v,F v ∂μ.prod ν)) (c₁+c₂) (μ.prod ν) := by
  let G := fun a => ∫ b,F (a,b) ∂ν
  let m := ∫ a,G a ∂μ
  have hFI : Integrable F (μ.prod ν) := Integrable.of_mem_Icc 0 1 hF.aemeasurable (ae_of_all _ hb)
  have hEF : (∫ z,F z ∂μ.prod ν)=m := integral_prod F hFI
  have hEXP (t : ℝ) : Integrable (fun z => exp (t*(F z-m))) (μ.prod ν) := by
    apply integrable_exp_mul_of_mem_Icc (a:=-m) (b:=1-m) (hF.aemeasurable.sub_const m)
    exact ae_of_all _ (fun z => ⟨by linarith [(hb z).1],by linarith [(hb z).2]⟩)
  constructor
  · intro t
    simpa only [hEF] using hEXP t
  · intro t
    change (∫ z,exp (t*(F z-(∫ v,F v ∂μ.prod ν))) ∂μ.prod ν) ≤ _
    rw [hEF,integral_prod _ (hEXP t)]
    have he (a : α) : (∫ b,exp (t*(F (a,b)-m)) ∂ν)=
        exp (t*(G a-m))*mgf (fun b => F (a,b)-G a) ν t := by
      unfold mgf
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun b => by
        change exp (t*(F (a,b)-m))=exp (t*(G a-m))*exp (t*(F (a,b)-G a))
        rw [← exp_add];congr 1;ring)
    have hi : Integrable (fun a => exp (t*(G a-m))*exp ((c₂:ℝ)*t^2/2)) μ :=
      (hmean.integrable_exp_mul t).mul_const _
    calc
      _ ≤ ∫ a,exp (t*(G a-m))*exp ((c₂:ℝ)*t^2/2) ∂μ := by
        apply integral_mono (hEXP t).integral_prod_left hi
        intro a
        change (∫ b,exp (t*(F (a,b)-m)) ∂ν) ≤ exp (t*(G a-m))*exp ((c₂:ℝ)*t^2/2)
        rw [he a]
        exact mul_le_mul_of_nonneg_left ((hsections a).mgf_le t) (exp_nonneg _)
      _ = mgf (fun a => G a-m) μ t*exp ((c₂:ℝ)*t^2/2) := by rw [integral_mul_const];rfl
      _ ≤ exp ((c₁:ℝ)*t^2/2)*exp ((c₂:ℝ)*t^2/2) :=
        mul_le_mul_of_nonneg_right (hmean.mgf_le t) (exp_nonneg _)
      _ = exp (((c₁+c₂:ℝ≥0):ℝ)*t^2/2) := by rw [← exp_add];congr 1;push_cast;ring
end Queelius.ProductConcentration
open scoped NNReal ENNReal
namespace Queelius.ProductConcentration
open MeasureTheory ProbabilityTheory Real
lemma diameter_subgaussian {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hm : Measurable X) (hb : ∀ a,0 ≤ X a ∧ X a ≤ 1)
    (c : ℝ) (hc : ∀ a a',|X a-X a'| ≤ c) :
    HasSubgaussianMGF (fun a => X a-(∫ u,X u ∂μ)) ((‖c‖₊/2)^2) μ := by
  classical
  have hne : (Set.range X).Nonempty :=
    ⟨_,Set.mem_range_self (Classical.choice (nonempty_of_isProbabilityMeasure μ))⟩
  have hbd : BddBelow (Set.range X) := by
    refine ⟨0,?_⟩
    rintro _ ⟨a,rfl⟩
    exact (hb a).1
  let L := sInf (Set.range X)
  have hL (a : α) : X a ∈ Set.Icc L (L+c) := by
    refine ⟨csInf_le hbd (Set.mem_range_self a),?_⟩
    have hh : X a-c ≤ L := by
      apply le_csInf hne
      rintro _ ⟨a',rfl⟩
      have h := (abs_le.mp (hc a a')).2
      linarith
    linarith
  have h := hasSubgaussianMGF_of_mem_Icc (μ:=μ) hm.aemeasurable (ae_of_all _ hL)
  simpa only [add_sub_cancel_left] using h
lemma product_of_sections {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (hF : Measurable F) (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1)
    (c : ℝ) (c₂ : ℝ≥0) (hc : ∀ a a' b,|F (a,b)-F (a',b)| ≤ c)
    (hsections : ∀ a,HasSubgaussianMGF (fun b => F (a,b)-(∫ v,F (a,v) ∂ν)) c₂ ν) :
    HasSubgaussianMGF (fun z => F z-(∫ v,F v ∂μ.prod ν)) (((‖c‖₊/2)^2)+c₂) (μ.prod ν) := by
  have hm := section_mean ν F hF hb
  apply centered_product_subgaussian μ ν F hF hb ((‖c‖₊/2)^2) c₂ hsections
  exact diameter_subgaussian μ _ hm.1 hm.2 c (fun a a' => section_oscillation ν F hF hb a a' c (hc a a'))
lemma product_tail {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (hF : Measurable F) (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1)
    (c : ℝ) (c₂ : ℝ≥0) (hc : ∀ a a' b,|F (a,b)-F (a',b)| ≤ c)
    (hsections : ∀ a,HasSubgaussianMGF (fun b => F (a,b)-(∫ v,F (a,v) ∂ν)) c₂ ν)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ.prod ν).real {z | t ≤ F z-(∫ v,F v ∂μ.prod ν)} ≤
      exp (-t^2/(2*((((‖c‖₊/2)^2)+c₂:ℝ≥0):ℝ))) := by
  exact (product_of_sections μ ν F hF hb c c₂ hc hsections).measure_ge_le ht
end Queelius.ProductConcentration
open MeasureTheory ProbabilityTheory in
 theorem _root_.product_solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (hF : Measurable F) (hb : ∀ z,0 ≤ F z ∧ F z ≤ 1)
    (c : ℝ) (c₂ : ℝ≥0) (hc : ∀ a a' b,|F (a,b)-F (a',b)| ≤ c)
    (hsections : ∀ a,HasSubgaussianMGF (fun b => F (a,b)-(∫ v,F (a,v) ∂ν)) c₂ ν) :
    HasSubgaussianMGF (fun z => F z-(∫ v,F v ∂μ.prod ν)) (((‖c‖₊/2)^2)+c₂) (μ.prod ν) := by
  exact Queelius.ProductConcentration.product_of_sections μ ν F hF hb c c₂ hc hsections

namespace Queelius.ProductConcentration
open MeasureTheory ProbabilityTheory Real
lemma pi_subgaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (F : (Fin N → Ω) → ℝ) (hF : Measurable F) (hb : ∀ x,0 ≤ F x ∧ F x ≤ 1)
    (c : Fin N → ℝ)
    (hc : ∀ (i : Fin N) (x y : Fin N → Ω),(∀ j,j ≠ i → x j=y j) → |F x-F y| ≤ c i) :
    HasSubgaussianMGF (fun x => F x-(∫ y,F y ∂Measure.pi fun _ : Fin N => μ))
      (∑ i,(‖c i‖₊/2)^2) (Measure.pi fun _ : Fin N => μ) := by
  classical
  induction N with
  | zero =>
    have hz (x : Fin 0 → Ω) : F x-(∫ y,F y ∂Measure.pi fun _ : Fin 0 => μ)=0 := by
      have he : F=(fun _ => F x) := funext (fun y => congrArg F (Subsingleton.elim y x))
      rw [he]
      simp
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
    exact HasSubgaussianMGF.fun_zero.congr (ae_of_all _ (fun x => (hz x).symm))
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) 0
    let Fp := fun z : Ω × (Fin n → Ω) => F (e.symm z)
    have hFp : Measurable Fp := hF.comp e.symm.measurable
    have hbp : ∀ z,0 ≤ Fp z ∧ Fp z ≤ 1 := fun z => hb (e.symm z)
    have hcons (a : Ω) (b : Fin n → Ω) : Fp (a,b)=F (Fin.cons a b) := by
      simp [Fp,e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero]
    have hs (a : Ω) : HasSubgaussianMGF
        (fun b => Fp (a,b)-(∫ v,Fp (a,v) ∂Measure.pi fun _ : Fin n => μ))
        (∑ i : Fin n,(‖c i.succ‖₊/2)^2) (Measure.pi fun _ : Fin n => μ) := by
      apply ih (fun b => Fp (a,b)) (hFp.comp (measurable_const.prodMk measurable_id))
        (fun b => hbp (a,b)) (fun i => c i.succ)
      intro i x y heq
      rw [hcons,hcons]
      apply hc i.succ
      intro j
      refine Fin.cases ?_ (fun k hk => ?_) j
      · intro _;simp
      · simp only [Fin.cons_succ]
        exact heq k (by intro he;subst k;exact hk rfl)
    have hfirst (a a' : Ω) (b : Fin n → Ω) : |Fp (a,b)-Fp (a',b)| ≤ c 0 := by
      rw [hcons,hcons]
      apply hc 0
      intro j
      refine Fin.cases ?_ (fun k _ => ?_) j
      · intro h;exact False.elim (h rfl)
      · simp
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    have hmean : (∫ z,Fp z ∂μ.prod (Measure.pi fun _ : Fin n => μ))=
        ∫ x,F x ∂Measure.pi fun _ : Fin (n+1) => μ := by
      have h := hp.integral_comp' Fp
      simpa only [Fp,e,MeasurableEquiv.symm_apply_apply] using h.symm
    have hprod := product_of_sections μ (Measure.pi fun _ : Fin n => μ) Fp hFp hbp
      (c 0) (∑ i : Fin n,(‖c i.succ‖₊/2)^2) hfirst hs
    rw [Fin.sum_univ_succ]
    have hmap : HasSubgaussianMGF
        (fun z => Fp z-(∫ v,Fp v ∂μ.prod (Measure.pi fun _ : Fin n => μ)))
        ((‖c 0‖₊/2)^2+∑ i : Fin n,(‖c i.succ‖₊/2)^2)
        ((Measure.pi fun _ : Fin (n+1) => μ).map e) := by
      rw [hp.map_eq]
      exact hprod
    have h := HasSubgaussianMGF.of_map hp.measurable.aemeasurable hmap
    simpa only [Function.comp_def,Fp,e,MeasurableEquiv.symm_apply_apply,hmean] using h
end Queelius.ProductConcentration

namespace Queelius.ProductConcentration
open MeasureTheory ProbabilityTheory Real Queelius.SmallBallCutoff LearnNoConc.ERM
lemma uniform_process_subgaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    HasSubgaussianMGF
      (fun x => (process μ τ N H x).toReal-(∫ y,(process μ τ N H y).toReal ∂Measure.pi fun _ : Fin N => μ))
      (1/(4*(N:ℝ≥0))) (Measure.pi fun _ : Fin N => μ) := by
  have hz : Measurable (fun x => (process μ τ N H x).toReal) :=
    ENNReal.measurable_toReal.comp (process_measurable μ τ N H hm hsep)
  have hb (x : Fin N → Ω) : 0 ≤ (process μ τ N H x).toReal ∧ (process μ τ N H x).toReal ≤ 1 := by
    refine ⟨ENNReal.toReal_nonneg,?_⟩
    have h := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ⊤) (process_le_one μ τ N hN H hm x)
    simpa using h
  have hs := pi_subgaussian μ N _ hz hb (fun _ => 1/(N:ℝ))
    (fun i x y heq => real_process_change μ τ N hN H hm x y i heq)
  have hv : (∑ i : Fin N,(‖(1:ℝ)/(N:ℝ)‖₊/2)^2)=(1/(4*(N:ℝ≥0))) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat,coe_nnnorm',Real.norm_eq_abs]
    change (∑ i : Fin N,(|(1:ℝ)/(N:ℝ)|/2)^2)=1/(4*(N:ℝ))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [abs_of_nonneg (by positivity)]
    have hn : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    field_simp
    <;> norm_num
  rw [hv] at hs
  exact hs
lemma uniform_process_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin N => μ).real
      {x | t ≤ (process μ τ N H x).toReal-
        (∫ y,(process μ τ N H y).toReal ∂Measure.pi fun _ : Fin N => μ)} ≤ exp (-2*N*t^2) := by
  have hs := (uniform_process_subgaussian μ τ N hN H hm hsep).measure_ge_le ht
  convert hs using 1
  congr 1
  change -2*(N:ℝ)*t^2 = -t^2/(2*(1/(4*(N:ℝ))))
  have hn : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp
  <;> ring
end Queelius.ProductConcentration
open MeasureTheory ProbabilityTheory LearnNoConc.ERM Queelius.SmallBallCutoff in
 theorem _root_.prior_concentration {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    HasSubgaussianMGF
      (fun x => (process μ τ N H x).toReal-(∫ y,(process μ τ N H y).toReal ∂Measure.pi fun _ : Fin N => μ))
      (1/(4*(N:ℝ≥0))) (Measure.pi fun _ : Fin N => μ) := by
  exact Queelius.ProductConcentration.uniform_process_subgaussian μ τ N hN H hm hsep

namespace Queelius.SmallBallSymmetrization
open MeasureTheory Filter Topology LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
noncomputable def empirical {Ω : Type*} (τ : ℝ) (N : ℕ) (h : Ω → ℝ) (x : Fin N → Ω) : ℝ :=
  (∑ i,cutoff τ (h (x i)))/(N:ℝ)
noncomputable def ghost {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (z : (Fin N → Ω) × (Fin N → Ω)) : ℝ≥0∞ :=
  ⨆ h ∈ H,ENNReal.ofReal |empirical τ N h z.1-empirical τ N h z.2|
lemma empirical_measurable {Ω : Type*} [MeasurableSpace Ω] (τ : ℝ) (N : ℕ)
    (h : Ω → ℝ) (hm : Measurable h) : Measurable (empirical τ N h) := by
  have hi (i : Fin N) : Measurable (fun x : Fin N → Ω => cutoff τ (h (x i))) :=
    ((measurable_cutoff τ).comp hm).comp (measurable_pi_apply i)
  unfold empirical;fun_prop
lemma empirical_bounds {Ω : Type*} (τ : ℝ) (N : ℕ) (hN : 0 < N) (h : Ω → ℝ)
    (x : Fin N → Ω) : 0 ≤ empirical τ N h x ∧ empirical τ N h x ≤ 1 := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (bounds τ (h (x i))).1)) (Nat.cast_nonneg N)
  · change (∑ i,cutoff τ (h (x i)))/(N:ℝ) ≤ 1
    apply (div_le_one hn).mpr
    calc (∑ i,cutoff τ (h (x i))) ≤ ∑ i : Fin N,(1:ℝ) :=
      Finset.sum_le_sum (fun i _ => (bounds τ (h (x i))).2)
    _ = (N:ℝ) := by simp
lemma empirical_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (h : Ω → ℝ) (hm : Measurable h) :
    Integrable (empirical τ N h) (Measure.pi fun _ : Fin N => μ) := by
  apply Integrable.of_mem_Icc 0 1 (empirical_measurable τ N h hm).aemeasurable
  exact ae_of_all _ (empirical_bounds τ N hN h)
lemma empirical_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (h : Ω → ℝ) (hm : Measurable h) :
    (∫ x,empirical τ N h x ∂Measure.pi fun _ : Fin N => μ)=∫ z,cutoff τ (h z) ∂μ := by
  have hi : Integrable (fun z => cutoff τ (h z)) μ :=
    Integrable.of_mem_Icc 0 1 ((measurable_cutoff τ).comp hm).aemeasurable
      (ae_of_all _ (fun z => bounds τ (h z)))
  unfold empirical
  rw [integral_div,integral_finset_sum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin N => μ) hi.aestronglyMeasurable]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (Nat.cast_pos.mpr hN).ne'
  · intro i _;exact integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hi
lemma ghost_le_one {Ω : Type*} (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ))
    (z : (Fin N → Ω) × (Fin N → Ω)) : ghost τ N H z ≤ 1 := by
  apply iSup_le;intro h;apply iSup_le;intro hh
  apply ENNReal.ofReal_le_one.mpr
  have hx := empirical_bounds τ N hN h z.1
  have hy := empirical_bounds τ N hN h z.2
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma process_le_ghost_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (x : Fin N → Ω) :
    process μ τ N H x ≤ ∫⁻ y,ghost τ N H (x,y) ∂Measure.pi fun _ : Fin N => μ := by
  apply iSup_le;intro h;apply iSup_le;intro hh
  have he : centered μ τ N h x=
      ∫ y,empirical τ N h x-empirical τ N h y ∂Measure.pi fun _ : Fin N => μ := by
    rw [integral_sub (integrable_const _) (empirical_integrable μ τ N hN h (hm h hh)),
      integral_const,empirical_mean μ τ N hN h (hm h hh)]
    simp [centered,empirical]
  unfold deviation
  rw [he]
  calc ENNReal.ofReal |∫ y,empirical τ N h x-empirical τ N h y ∂Measure.pi fun _ : Fin N => μ|
      = ‖∫ y,empirical τ N h x-empirical τ N h y ∂Measure.pi fun _ : Fin N => μ‖ₑ := by
        simp only [Real.enorm_eq_ofReal_abs]
    _ ≤ ∫⁻ y,‖empirical τ N h x-empirical τ N h y‖ₑ ∂Measure.pi fun _ : Fin N => μ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ _ := lintegral_mono (fun y => by
      rw [Real.enorm_eq_ofReal_abs]
      unfold ghost
      exact le_iSup_of_le h (le_iSup_of_le hh le_rfl))
lemma expected_process_le_iterated_ghost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : ℝ) (N : ℕ) (hN : 0 < N)
    (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h) :
    (∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ) ≤
      ∫⁻ x,∫⁻ y,ghost τ N H (x,y) ∂Measure.pi fun _ : Fin N => μ
        ∂Measure.pi fun _ : Fin N => μ := by
  exact lintegral_mono (process_le_ghost_mean μ τ N hN H hm)
end Queelius.SmallBallSymmetrization

namespace Queelius.SmallBallSymmetrization
open MeasureTheory Filter Topology LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
lemma empirical_converges {Ω : Type*} (τ : ℝ) (N : ℕ) (u : ℕ → Ω → ℝ) (h : Ω → ℝ)
    (hl : ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x))) (x : Fin N → Ω) :
    Tendsto (fun n => empirical τ N (u n) x) atTop (𝓝 (empirical τ N h x)) := by
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro i _
  exact (continuous_cutoff τ).continuousAt.tendsto.comp (hl (x i))
lemma ghost_countable {Ω : Type*} (τ : ℝ) (N : ℕ) (H G : Set (Ω → ℝ)) (hGH : G ⊆ H)
    (hd : ∀ h ∈ H,∃ u : ℕ → Ω → ℝ,(∀ n,u n ∈ G) ∧
      ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x))) : ghost τ N H=ghost τ N G := by
  funext z
  apply le_antisymm
  · apply iSup_le;intro h;apply iSup_le;intro hh
    obtain ⟨u,hu,hl⟩ := hd h hh
    have he : Continuous (fun t : ℝ => ENNReal.ofReal |t|) :=
      ENNReal.continuous_ofReal.comp continuous_abs
    have ht := he.continuousAt.tendsto.comp
      ((empirical_converges τ N u h hl z.1).sub (empirical_converges τ N u h hl z.2))
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall (fun n => le_iSup_of_le (u n) (le_iSup_of_le (hu n) le_rfl))
  · apply iSup_le;intro h;apply iSup_le;intro hh
    exact le_iSup_of_le h (le_iSup_of_le (hGH hh) le_rfl)
lemma ghost_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) : Measurable (ghost τ N H) := by
  obtain ⟨G,hGH,hG,hd⟩ := hsep
  have ha : ∀ h ∈ H,∃ u : ℕ → Ω → ℝ,(∀ n,u n ∈ G) ∧
      ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x)) := by
    intro h hh
    obtain ⟨u,hu,hl,_⟩ := hd h hh
    exact ⟨u,hu,hl⟩
  rw [ghost_countable τ N H G hGH ha]
  apply Measurable.biSup G hG
  intro h hh
  have he := empirical_measurable τ N h (hm h (hGH hh))
  exact ENNReal.measurable_ofReal.comp ((he.comp measurable_fst).sub (he.comp measurable_snd)).abs
lemma ghost_real_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    Integrable (fun z => (ghost τ N H z).toReal)
      ((Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N => μ)) := by
  apply Integrable.of_mem_Icc 0 1
    (ENNReal.measurable_toReal.comp (ghost_measurable μ τ N H hm hsep)).aemeasurable
  exact ae_of_all _ (fun z => ⟨ENNReal.toReal_nonneg,by
    have h := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ⊤) (ghost_le_one τ N hN H z)
    simpa using h⟩)
lemma expected_process_le_joint_ghost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : ℝ) (N : ℕ) (hN : 0 < N)
    (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h) (hsep : PointwiseSeparable μ H) :
    (∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ) ≤
      ∫⁻ z,ghost τ N H z
        ∂(Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N => μ) := by
  rw [lintegral_prod _ (ghost_measurable μ τ N H hm hsep).aemeasurable]
  exact expected_process_le_iterated_ghost μ τ N hN H hm
end Queelius.SmallBallSymmetrization

namespace Queelius.SmallBallSymmetrization
open MeasureTheory Filter Topology LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
noncomputable def pairGhost {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (z : Fin N → Ω × Ω) : ℝ≥0∞ := ghost τ N H (fun i => (z i).1,fun i => (z i).2)
noncomputable def signedPairGhost {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (σ : Fin N → Bool) (z : Fin N → Ω × Ω) : ℝ≥0∞ :=
  ⨆ h ∈ H,ENNReal.ofReal |(∑ i,sgn σ i*(cutoff τ (h (z i).1)-cutoff τ (h (z i).2)))/(N:ℝ)|
def swapSigns {Ω : Type*} (N : ℕ) (σ : Fin N → Bool) (z : Fin N → Ω × Ω) : Fin N → Ω × Ω :=
  fun i => if σ i then z i else ((z i).2,(z i).1)
lemma swapSigns_preserving {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (σ : Fin N → Bool) :
    MeasurePreserving (swapSigns N σ) (Measure.pi fun _ : Fin N => μ.prod μ)
      (Measure.pi fun _ : Fin N => μ.prod μ) := by
  unfold swapSigns
  apply measurePreserving_pi (fun _ : Fin N => μ.prod μ) (fun _ : Fin N => μ.prod μ)
    (f := fun i (z : Ω × Ω) => if σ i then z else (z.2,z.1))
  intro i
  cases h : σ i
  · convert! (Measure.measurePreserving_swap :
      MeasurePreserving (Prod.swap : Ω × Ω → Ω × Ω) (μ.prod μ) (μ.prod μ)) using 1 <;>
      (ext z <;> simp [h,Prod.swap])
  · convert! (MeasurePreserving.id (μ.prod μ)) using 1 <;> (ext z <;> simp [h,id])
lemma pairGhost_swapSigns {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (σ : Fin N → Bool) (z : Fin N → Ω × Ω) :
    pairGhost τ N H (swapSigns N σ z)=signedPairGhost τ N H σ z := by
  unfold pairGhost ghost signedPairGhost
  congr 1;funext h
  congr 1;funext hh
  congr 2
  unfold empirical
  rw [← sub_div,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hi : σ i <;> simp [swapSigns,sgn,hi] <;> ring
lemma pairGhost_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) : Measurable (pairGhost τ N H) := by
  exact (ghost_measurable μ τ N H hm hsep).comp (by fun_prop)
lemma pairGhost_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    (∫⁻ z,pairGhost τ N H z ∂Measure.pi fun _ : Fin N => μ.prod μ)=
      ∫⁻ z,ghost τ N H z
        ∂(Measure.pi fun _ : Fin N => μ).prod (Measure.pi fun _ : Fin N => μ) := by
  exact (measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin N)
    (fun _ => μ) (fun _ => μ)).lintegral_comp (ghost_measurable μ τ N H hm hsep)
lemma signs_invariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) (σ : Fin N → Bool) :
    (∫⁻ z,signedPairGhost τ N H σ z ∂Measure.pi fun _ : Fin N => μ.prod μ)=
      ∫⁻ z,pairGhost τ N H z ∂Measure.pi fun _ : Fin N => μ.prod μ := by
  have hi := (swapSigns_preserving μ N σ).lintegral_comp (pairGhost_measurable μ τ N H hm hsep)
  simpa only [pairGhost_swapSigns] using hi
end Queelius.SmallBallSymmetrization

namespace Queelius.SmallBallSymmetrization
open MeasureTheory Filter Topology LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
noncomputable def single {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (σ : Fin N → Bool) (x : Fin N → Ω) : ℝ≥0∞ :=
  ⨆ h ∈ H,ENNReal.ofReal |(∑ i,sgn σ i*cutoff τ (h (x i)))/(N:ℝ)|
lemma single_countable {Ω : Type*} (τ : ℝ) (N : ℕ) (H G : Set (Ω → ℝ)) (hGH : G ⊆ H)
    (hd : ∀ h ∈ H,∃ u : ℕ → Ω → ℝ,(∀ n,u n ∈ G) ∧
      ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x))) (σ : Fin N → Bool) :
    single τ N H σ=single τ N G σ := by
  funext x
  apply le_antisymm
  · apply iSup_le;intro h;apply iSup_le;intro hh
    obtain ⟨u,hu,hl⟩ := hd h hh
    have ht : Tendsto (fun n => ∑ i : Fin N,sgn σ i*cutoff τ (u n (x i))) atTop
        (𝓝 (∑ i : Fin N,sgn σ i*cutoff τ (h (x i)))) := by
      apply tendsto_finset_sum
      intro i _
      exact tendsto_const_nhds.mul ((continuous_cutoff τ).continuousAt.tendsto.comp (hl (x i)))
    have he : Continuous (fun t : ℝ => ENNReal.ofReal |t|) :=
      ENNReal.continuous_ofReal.comp continuous_abs
    apply le_of_tendsto (he.continuousAt.tendsto.comp (ht.div_const (N:ℝ)))
    exact Filter.Eventually.of_forall (fun n => le_iSup_of_le (u n) (le_iSup_of_le (hu n) le_rfl))
  · apply iSup_le;intro h;apply iSup_le;intro hh
    exact le_iSup_of_le h (le_iSup_of_le (hGH hh) le_rfl)
lemma single_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) (σ : Fin N → Bool) : Measurable (single τ N H σ) := by
  obtain ⟨G,hGH,hG,hd⟩ := hsep
  have ha : ∀ h ∈ H,∃ u : ℕ → Ω → ℝ,(∀ n,u n ∈ G) ∧
      ∀ x,Tendsto (fun n => u n x) atTop (𝓝 (h x)) := by
    intro h hh
    obtain ⟨u,hu,hl,_⟩ := hd h hh
    exact ⟨u,hu,hl⟩
  rw [single_countable τ N H G hGH ha σ]
  apply Measurable.biSup G hG
  intro h hh
  have he (i : Fin N) : Measurable (fun x : Fin N → Ω => cutoff τ (h (x i))) :=
    ((measurable_cutoff τ).comp (hm h (hGH hh))).comp (measurable_pi_apply i)
  fun_prop
lemma signedPair_triangle {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (σ : Fin N → Bool) (z : Fin N → Ω × Ω) :
    signedPairGhost τ N H σ z ≤ single τ N H σ (fun i => (z i).1)+
      single τ N H σ (fun i => (z i).2) := by
  apply iSup_le;intro h;apply iSup_le;intro hh
  have he : (∑ i,sgn σ i*(cutoff τ (h (z i).1)-cutoff τ (h (z i).2)))/(N:ℝ)=
      (∑ i,sgn σ i*cutoff τ (h (z i).1))/(N:ℝ)-
        (∑ i,sgn σ i*cutoff τ (h (z i).2))/(N:ℝ) := by
    simp only [mul_sub,Finset.sum_sub_distrib,sub_div]
  rw [he]
  apply (ENNReal.ofReal_le_ofReal (abs_sub _ _)).trans
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply add_le_add <;> exact le_iSup_of_le h (le_iSup_of_le hh le_rfl)
lemma pairGhost_le_two_single {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) (σ : Fin N → Bool) :
    (∫⁻ z,pairGhost τ N H z ∂Measure.pi fun _ : Fin N => μ.prod μ) ≤
      2*(∫⁻ x,single τ N H σ x ∂Measure.pi fun _ : Fin N => μ) := by
  have hfst := measurePreserving_pi (fun _ : Fin N => μ.prod μ) (fun _ : Fin N => μ)
    (fun _ => (measurePreserving_fst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ))
  have hsnd := measurePreserving_pi (fun _ : Fin N => μ.prod μ) (fun _ : Fin N => μ)
    (fun _ => (measurePreserving_snd : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ))
  have hm1 := single_measurable μ τ N H hm hsep σ
  rw [← signs_invariance μ τ N H hm hsep σ]
  calc (∫⁻ z,signedPairGhost τ N H σ z ∂Measure.pi fun _ : Fin N => μ.prod μ)
      ≤ ∫⁻ z,single τ N H σ (fun i => (z i).1)+single τ N H σ (fun i => (z i).2)
          ∂Measure.pi fun _ : Fin N => μ.prod μ := lintegral_mono (signedPair_triangle τ N H σ)
    _ = (∫⁻ z,single τ N H σ (fun i => (z i).1) ∂Measure.pi fun _ : Fin N => μ.prod μ)+
        ∫⁻ z,single τ N H σ (fun i => (z i).2) ∂Measure.pi fun _ : Fin N => μ.prod μ :=
      lintegral_add_aux (hm1.comp hfst.measurable) (hm1.comp hsnd.measurable)
    _ = _ := by rw [hfst.lintegral_comp hm1,hsnd.lintegral_comp hm1,two_mul]
lemma expected_process_symmetrization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : ℝ) (N : ℕ) (hN : 0 < N)
    (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h) (hsep : PointwiseSeparable μ H) :
    (∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ) ≤
      2*((2^N:ℝ≥0∞)⁻¹*∑ σ : Fin N → Bool,
        ∫⁻ x,single τ N H σ x ∂Measure.pi fun _ : Fin N => μ) := by
  classical
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (σ : Fin N → Bool) _ => pairGhost_le_two_single μ τ N H hm hsep σ)
  have hh := mul_le_mul' (le_refl ((2^N:ℝ≥0∞)⁻¹)) hs
  have hc : (Fintype.card (Fin N → Bool):ℝ≥0∞)=(2^N:ℝ≥0∞) := by simp
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc] at hh
  have h0 : (2^N:ℝ≥0∞) ≠ 0 := by positivity
  have hf : (2^N:ℝ≥0∞) ≠ ⊤ := by finiteness
  rw [← mul_assoc,ENNReal.inv_mul_cancel h0 hf,one_mul] at hh
  have he := (expected_process_le_joint_ghost μ τ N hN H hm hsep).trans_eq
    (pairGhost_expectation μ τ N H hm hsep).symm
  apply he.trans
  convert hh using 1
  rw [← Finset.mul_sum]
  ring
end Queelius.SmallBallSymmetrization

namespace Queelius.SmallBallSymmetrization
open MeasureTheory Filter Topology LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
def cutoffClass {Ω : Type*} (τ : ℝ) (H : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  {g | ∃ h ∈ H,g=fun x => cutoff τ (h x)}
lemma single_cutoff_class {Ω : Type*} (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ))
    (σ : Fin N → Bool) (x : Fin N → Ω) :
    (⨆ g ∈ cutoffClass τ H,‖(N:ℝ)⁻¹*∑ i,sgn σ i*g (x i)‖ₑ)=single τ N H σ x := by
  have he (h : Ω → ℝ) : ‖(N:ℝ)⁻¹*∑ i,sgn σ i*cutoff τ (h (x i))‖ₑ=
      ENNReal.ofReal |(∑ i,sgn σ i*cutoff τ (h (x i)))/(N:ℝ)| := by
    rw [Real.enorm_eq_ofReal_abs,div_eq_inv_mul]
  apply le_antisymm
  · apply iSup_le;intro g;apply iSup_le;intro hg
    obtain ⟨h,hh,rfl⟩ := hg
    rw [he]
    exact le_iSup_of_le h (le_iSup_of_le hh le_rfl)
  · apply iSup_le;intro h;apply iSup_le;intro hh
    rw [← he]
    exact le_iSup_of_le (fun x => cutoff τ (h x)) (le_iSup_of_le ⟨h,hh,rfl⟩ le_rfl)
lemma cutoff_radSup {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : ℝ) (N : ℕ) (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h)
    (hsep : PointwiseSeparable μ H) :
    radSup μ (cutoffClass τ H) N=(2^N:ℝ≥0∞)⁻¹*∑ σ : Fin N → Bool,
      ∫⁻ x,single τ N H σ x ∂Measure.pi fun _ : Fin N => μ := by
  unfold radSup
  simp_rw [single_cutoff_class]
  rw [lintegral_const_mul]
  · rw [lintegral_finsetSum]
    intro σ _;exact single_measurable μ τ N H hm hsep σ
  · exact Finset.measurable_sum _ (fun σ _ => single_measurable μ τ N H hm hsep σ)
lemma expected_process_le_radSup_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : ℝ) (N : ℕ) (hN : 0 < N)
    (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h) (hsep : PointwiseSeparable μ H) :
    (∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ) ≤
      2*radSup μ (cutoffClass τ H) N := by
  rw [cutoff_radSup μ τ N H hm hsep]
  exact expected_process_symmetrization μ τ N hN H hm hsep
end Queelius.SmallBallSymmetrization

open MeasureTheory LearnNoConc.ERM Queelius.SmallBallCutoff Queelius.SmallBallSymmetrization in
theorem _root_.prior_symmetrization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : ℝ) (N : ℕ) (hN : 0 < N)
    (H : Set (Ω → ℝ)) (hm : ∀ h ∈ H,Measurable h) (hsep : PointwiseSeparable μ H) :
    (∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ) ≤
      2*radSup μ (cutoffClass τ H) N := by
  exact expected_process_le_radSup_cutoff μ τ N hN H hm hsep

namespace Queelius.RademacherContraction
open LearnNoConc.ERM
noncomputable def finMax {J : Type*} [Fintype J] [Nonempty J] (a : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty a
lemma le_finMax {J : Type*} [Fintype J] [Nonempty J] (a : J → ℝ) (j : J) : a j ≤ finMax a :=
  Finset.le_sup' a (Finset.mem_univ j)
lemma finMax_witness {J : Type*} [Fintype J] [Nonempty J] (a : J → ℝ) :
    ∃ j,finMax a=a j := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  exact ⟨j,he⟩
lemma pair_contraction {J : Type*} [Fintype J] [Nonempty J] (a x y : J → ℝ)
    (hxy : ∀ j k,|y j-y k| ≤ |x j-x k|) :
    finMax (fun j => a j+y j)+finMax (fun j => a j-y j) ≤
      finMax (fun j => a j+x j)+finMax (fun j => a j-x j) := by
  obtain ⟨j,hj⟩ := finMax_witness (fun j => a j+y j)
  obtain ⟨k,hk⟩ := finMax_witness (fun j => a j-y j)
  rw [hj,hk]
  have h1 := le_finMax (fun j => a j+x j) j
  have h2 := le_finMax (fun j => a j-x j) k
  have h3 := le_finMax (fun j => a j+x j) k
  have h4 := le_finMax (fun j => a j-x j) j
  have hh := (le_abs_self (y j-y k)).trans (hxy j k)
  rcases le_total (x k) (x j) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hh
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hh
    linarith
lemma sum_signs_succ (n : ℕ) (F : (Fin (n+1) → Bool) → ℝ) :
    (∑ σ : Fin (n+1) → Bool,F σ)=
      ∑ σ : Fin n → Bool,(F (Fin.cons true σ)+F (Fin.cons false σ)) := by
  classical
  have he := (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp F
  rw [← he]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Fin.consEquiv_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rfl
lemma finite_signed_contraction {J : Type*} [Fintype J] [Nonempty J]
    (n : ℕ) (a : J → ℝ) (x y : J → Fin n → ℝ)
    (hxy : ∀ i j k,|y j i-y k i| ≤ |x j i-x k i|) :
    (∑ σ : Fin n → Bool,finMax (fun j => a j+∑ i,sgn σ i*y j i)) ≤
      ∑ σ : Fin n → Bool,finMax (fun j => a j+∑ i,sgn σ i*x j i) := by
  classical
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have split_sum (z : J → Fin (n+1) → ℝ) :
        (∑ σ : Fin (n+1) → Bool,finMax (fun j => a j+∑ i,sgn σ i*z j i))=
          ∑ σ : Fin n → Bool,
            (finMax (fun j => (a j+z j 0)+∑ i,sgn σ i*z j i.succ)+
              finMax (fun j => (a j-z j 0)+∑ i,sgn σ i*z j i.succ)) := by
      rw [sum_signs_succ]
      apply Finset.sum_congr rfl
      intro σ _
      congr 1 <;> congr 1 <;> funext j
      <;> simp [Fin.sum_univ_succ,sgn]
      <;> ring
    rw [split_sum y,split_sum x]
    calc
      _ ≤ ∑ σ : Fin n → Bool,
          (finMax (fun j => (a j+x j 0)+∑ i,sgn σ i*y j i.succ)+
            finMax (fun j => (a j-x j 0)+∑ i,sgn σ i*y j i.succ)) := by
        apply Finset.sum_le_sum
        intro σ _
        have hc := pair_contraction (fun j => a j+∑ i : Fin n,sgn σ i*y j i.succ)
          (fun j => x j 0) (fun j => y j 0) (hxy 0)
        simpa only [sub_eq_add_neg,add_assoc,add_left_comm,add_comm] using hc
      _ ≤ _ := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
        exact add_le_add
          (ih (fun j => a j+x j 0) (fun j i => x j i.succ) (fun j i => y j i.succ)
            (fun i => hxy i.succ))
          (ih (fun j => a j-x j 0) (fun j i => x j i.succ) (fun j i => y j i.succ)
            (fun i => hxy i.succ))
end Queelius.RademacherContraction

namespace Queelius.RademacherContraction
open LearnNoConc.ERM
noncomputable def augment {J : Type*} {n : ℕ} (x : J → Fin n → ℝ) : Option J → Fin n → ℝ :=
  fun j => match j with | none => fun _ => 0 | some j => x j
def flipSigns (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ i := !(σ i)
  invFun σ i := !(σ i)
  left_inv σ := by funext i;exact Bool.not_not (σ i)
  right_inv σ := by funext i;exact Bool.not_not (σ i)
lemma sign_flip (n : ℕ) (σ : Fin n → Bool) (i : Fin n) :
    sgn (flipSigns n σ) i = -sgn σ i := by cases h : σ i <;> simp [sgn,flipSigns,h]
lemma sum_negative_max {J : Type*} [Fintype J] [Nonempty J]
    (n : ℕ) (x : J → Fin n → ℝ) :
    (∑ σ : Fin n → Bool,finMax (fun j => -(∑ i,sgn σ i*x j i)))=
      ∑ σ : Fin n → Bool,finMax (fun j => ∑ i,sgn σ i*x j i) := by
  have he := (flipSigns n).sum_comp (fun σ => finMax (fun j => ∑ i,sgn σ i*x j i))
  simp_rw [sign_flip,neg_mul,Finset.sum_neg_distrib] at he
  exact he
lemma absolute_pair_bound {J : Type*} [Fintype J] [Nonempty J] (n : ℕ)
    (x : J → Fin n → ℝ) (σ : Fin n → Bool) :
    finMax (fun j => |∑ i,sgn σ i*x j i|) ≤
      finMax (fun j : Option J => ∑ i,sgn σ i*augment x j i)+
        finMax (fun j : Option J => -(∑ i,sgn σ i*augment x j i)) := by
  have h0 : 0 ≤ finMax (fun j : Option J => ∑ i,sgn σ i*augment x j i) := by
    convert! le_finMax (fun j : Option J => ∑ i,sgn σ i*augment x j i) none using 1 <;> simp [augment]
  have h0' : 0 ≤ finMax (fun j : Option J => -(∑ i,sgn σ i*augment x j i)) := by
    convert! le_finMax (fun j : Option J => -(∑ i,sgn σ i*augment x j i)) none using 1 <;> simp [augment]
  change Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ i,sgn σ i*x j i|) ≤ _
  apply (Finset.sup'_le_iff _ _).mpr
  intro j _
  have h1 := le_finMax (fun j : Option J => ∑ i,sgn σ i*augment x j i) (some j)
  have h2 := le_finMax (fun j : Option J => -(∑ i,sgn σ i*augment x j i)) (some j)
  change (∑ i,sgn σ i*x j i) ≤ _ at h1
  change -(∑ i,sgn σ i*x j i) ≤ _ at h2
  rcases le_total 0 (∑ i,sgn σ i*x j i) with h | h
  · rw [abs_of_nonneg h];linarith
  · rw [abs_of_nonpos h];linarith
lemma augment_max_le_abs {J : Type*} [Fintype J] [Nonempty J] (n : ℕ)
    (x : J → Fin n → ℝ) (σ : Fin n → Bool) :
    finMax (fun j : Option J => ∑ i,sgn σ i*augment x j i) ≤
      finMax (fun j => |∑ i,sgn σ i*x j i|) := by
  change Finset.univ.sup' Finset.univ_nonempty (fun j : Option J => ∑ i,sgn σ i*augment x j i) ≤ _
  apply (Finset.sup'_le_iff _ _).mpr
  intro j _
  cases j with
  | none =>
    simp only [augment,mul_zero,Finset.sum_const_zero]
    exact (abs_nonneg _).trans (le_finMax (fun j => |∑ i,sgn σ i*x j i|) (Classical.choice (inferInstance : Nonempty J)))
  | some j =>
    change (∑ i,sgn σ i*x j i) ≤ _
    exact (le_abs_self _).trans (le_finMax (fun j => |∑ i,sgn σ i*x j i|) j)
lemma finite_absolute_contraction {J : Type*} [Fintype J] [Nonempty J]
    (n : ℕ) (x y : J → Fin n → ℝ)
    (hxy : ∀ i j k,|y j i-y k i| ≤ |x j i-x k i|)
    (h0 : ∀ i j,|y j i| ≤ |x j i|) :
    (∑ σ : Fin n → Bool,finMax (fun j => |∑ i,sgn σ i*y j i|)) ≤
      2*∑ σ : Fin n → Bool,finMax (fun j => |∑ i,sgn σ i*x j i|) := by
  have hc : ∀ i (j k : Option J),|augment y j i-augment y k i| ≤
      |augment x j i-augment x k i| := by
    intro i j k
    cases j <;> cases k <;> simp only [augment,sub_zero,zero_sub,abs_neg,sub_self,abs_zero]
    · exact le_rfl
    · exact h0 _ _
    · exact h0 _ _
    · exact hxy _ _ _
  have hi := finite_signed_contraction n (fun _ : Option J => (0:ℝ)) (augment x) (augment y) hc
  simp only [zero_add] at hi
  calc
    _ ≤ ∑ σ : Fin n → Bool,
        (finMax (fun j : Option J => ∑ i,sgn σ i*augment y j i)+
          finMax (fun j : Option J => -(∑ i,sgn σ i*augment y j i))) :=
      Finset.sum_le_sum (fun σ _ => absolute_pair_bound n y σ)
    _ = 2*∑ σ : Fin n → Bool,finMax (fun j : Option J => ∑ i,sgn σ i*augment y j i) := by
      rw [Finset.sum_add_distrib,sum_negative_max,two_mul]
    _ ≤ 2*∑ σ : Fin n → Bool,finMax (fun j : Option J => ∑ i,sgn σ i*augment x j i) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => augment_max_le_abs n x σ)) (by norm_num)
end Queelius.RademacherContraction

namespace Queelius.RademacherContraction
open LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
lemma finMax_mul {J : Type*} [Fintype J] [Nonempty J] (a : J → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    finMax (fun j => c*a j)=c*finMax a := by
  obtain ⟨j,hj⟩ := finMax_witness (fun j => c*a j)
  obtain ⟨k,hk⟩ := finMax_witness a
  apply le_antisymm
  · rw [hj];exact mul_le_mul_of_nonneg_left (le_finMax a j) hc
  · rw [hk];exact le_finMax (fun j => c*a j) k
lemma finMax_abs_div {J : Type*} [Fintype J] [Nonempty J] (a : J → ℝ) (c : ℝ) (hc : 0 < c) :
    finMax (fun j => |a j/c|)=(1/c)*finMax (fun j => |a j|) := by
  simp_rw [abs_div,abs_of_pos hc,div_eq_inv_mul]
  simpa only [one_div,mul_one] using finMax_mul (fun j => |a j|) c⁻¹ (inv_nonneg.mpr hc.le)
lemma finite_cutoff_real {J : Type*} [Fintype J] [Nonempty J]
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (u : J → Fin N → ℝ) :
    (∑ σ : Fin N → Bool,finMax (fun j => |(∑ i,sgn σ i*cutoff τ (u j i))/(N:ℝ)|)) ≤
      (2/τ)*∑ σ : Fin N → Bool,finMax (fun j => |(∑ i,sgn σ i*u j i)/(N:ℝ)|) := by
  have hc := finite_absolute_contraction N (fun j i => u j i/τ) (fun j i => cutoff τ (u j i))
    (fun i j k => by
      rw [← sub_div,abs_div,abs_of_pos hτ]
      exact lipschitz τ hτ (u j i) (u k i))
    (fun i j => by
      rw [abs_div,abs_of_pos hτ]
      simpa only [cutoff_zero,sub_zero] using lipschitz τ hτ (u j i) 0)
  have hs (σ : Fin N → Bool) :
      finMax (fun j => |∑ i,sgn σ i*(u j i/τ)|)=(1/τ)*finMax (fun j => |∑ i,sgn σ i*u j i|) := by
    simp_rw [← mul_div_assoc,← Finset.sum_div]
    exact finMax_abs_div _ τ hτ
  simp_rw [hs] at hc
  rw [← Finset.mul_sum] at hc
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  simp_rw [finMax_abs_div _ (N:ℝ) hn]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hc (one_div_nonneg.mpr hn.le)
  convert! hh using 1 <;> ring
lemma ofReal_finMax {J : Type*} [Fintype J] [Nonempty J] (a : J → ℝ) :
    ENNReal.ofReal (finMax a)=⨆ j,ENNReal.ofReal (a j) := by
  apply le_antisymm
  · obtain ⟨j,hj⟩ := finMax_witness a
    rw [hj];exact le_iSup (fun j => ENNReal.ofReal (a j)) j
  · apply iSup_le;intro j
    exact ENNReal.ofReal_le_ofReal (le_finMax a j)
lemma finite_cutoff_ennreal {J : Type*} [Fintype J] [Nonempty J]
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (u : J → Fin N → ℝ) :
    (∑ σ : Fin N → Bool,⨆ j,ENNReal.ofReal |(∑ i,sgn σ i*cutoff τ (u j i))/(N:ℝ)|) ≤
      ENNReal.ofReal (2/τ)*(∑ σ : Fin N → Bool,⨆ j,ENNReal.ofReal |(∑ i,sgn σ i*u j i)/(N:ℝ)|) := by
  have hn (a : J → ℝ) : 0 ≤ finMax (fun j => |a j|) :=
    (abs_nonneg _).trans (le_finMax (fun j => |a j|) (Classical.choice (inferInstance : Nonempty J)))
  simp_rw [← ofReal_finMax]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => hn _),
    ← ENNReal.ofReal_sum_of_nonneg (fun σ _ => hn _),← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (finite_cutoff_real τ hτ N hN u)
end Queelius.RademacherContraction

open LearnNoConc.ERM Queelius.SmallBallCutoff Queelius.RademacherContraction in
theorem _root_.prior_finite_contraction {J : Type*} [Fintype J] [Nonempty J]
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (u : J → Fin N → ℝ) :
    (∑ σ : Fin N → Bool,⨆ j,ENNReal.ofReal |(∑ i,sgn σ i*cutoff τ (u j i))/(N:ℝ)|) ≤
      ENNReal.ofReal (2/τ)*(∑ σ : Fin N → Bool,⨆ j,ENNReal.ofReal |(∑ i,sgn σ i*u j i)/(N:ℝ)|) := by
  exact finite_cutoff_ennreal τ hτ N hN u

namespace Queelius.RademacherContraction
open LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
lemma iSup_finsets {J : Type*} (a : J → ℝ≥0∞) :
    (⨆ F : Finset J,⨆ j : F,a j)=⨆ j,a j := by
  classical
  apply le_antisymm
  · apply iSup_le;intro F;apply iSup_le;intro j;exact le_iSup a j
  · apply iSup_le;intro j
    exact le_iSup_of_le {j} (le_iSup_of_le (⟨j,Finset.mem_singleton_self j⟩ : ({j} : Finset J)) le_rfl)
lemma arbitrary_cutoff_ennreal {J : Type*}
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (u : J → Fin N → ℝ) :
    (∑ σ : Fin N → Bool,⨆ j,ENNReal.ofReal |(∑ i,sgn σ i*cutoff τ (u j i))/(N:ℝ)|) ≤
      ENNReal.ofReal (2/τ)*(∑ σ : Fin N → Bool,⨆ j,ENNReal.ofReal |(∑ i,sgn σ i*u j i)/(N:ℝ)|) := by
  classical
  let a := fun (σ : Fin N → Bool) (j : J) => ENNReal.ofReal |(∑ i,sgn σ i*cutoff τ (u j i))/(N:ℝ)|
  let b := fun (σ : Fin N → Bool) (j : J) => ENNReal.ofReal |(∑ i,sgn σ i*u j i)/(N:ℝ)|
  change (∑ σ,⨆ j,a σ j) ≤ ENNReal.ofReal (2/τ)*(∑ σ,⨆ j,b σ j)
  simp_rw [← iSup_finsets (a _)]
  rw [ENNReal.finsetSum_iSup_of_monotone (fun σ F K hFK => ?_)]
  · apply iSup_le
    intro F
    by_cases hF : F.Nonempty
    · letI : Nonempty F := ⟨⟨hF.choose,hF.choose_spec⟩⟩
      have hc := finite_cutoff_ennreal τ hτ N hN (fun j : F => u j)
      apply hc.trans
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro σ _
      apply iSup_le;intro j;exact le_iSup (b σ) j
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      simp only [iSup_of_empty,bot_eq_zero,Finset.sum_const_zero]
      exact bot_le
  · apply iSup_le;intro j
    exact le_iSup_of_le (⟨j,hFK j.property⟩ : K) le_rfl
end Queelius.RademacherContraction

namespace Queelius.RademacherContraction
open MeasureTheory LearnNoConc.ERM Queelius.SmallBallCutoff Queelius.SmallBallSymmetrization
open scoped ENNReal
lemma cutoff_rad_contraction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ)) :
    radSup μ (cutoffClass τ H) N ≤ ENNReal.ofReal (2/τ)*radSup μ H N := by
  have hp (x : Fin N → Ω) :
      (∑ σ : Fin N → Bool,⨆ g ∈ cutoffClass τ H,‖(N:ℝ)⁻¹*∑ i,sgn σ i*g (x i)‖ₑ) ≤
        ENNReal.ofReal (2/τ)*(∑ σ : Fin N → Bool,⨆ h ∈ H,‖(N:ℝ)⁻¹*∑ i,sgn σ i*h (x i)‖ₑ) := by
    simp_rw [single_cutoff_class,single,Real.enorm_eq_ofReal_abs,← iSup_subtype'']
    simpa only [div_eq_inv_mul] using arbitrary_cutoff_ennreal τ hτ N hN (fun h : H => fun i => h.val (x i))
  unfold radSup
  calc
    _ ≤ ∫⁻ x,(2^N:ℝ≥0∞)⁻¹*(ENNReal.ofReal (2/τ)*
        (∑ σ : Fin N → Bool,⨆ h ∈ H,‖(N:ℝ)⁻¹*∑ i,sgn σ i*h (x i)‖ₑ))
          ∂Measure.pi fun _ : Fin N => μ := lintegral_mono (fun x => mul_le_mul' le_rfl (hp x))
    _ = ∫⁻ x,ENNReal.ofReal (2/τ)*((2^N:ℝ≥0∞)⁻¹*
        (∑ σ : Fin N → Bool,⨆ h ∈ H,‖(N:ℝ)⁻¹*∑ i,sgn σ i*h (x i)‖ₑ))
          ∂Measure.pi fun _ : Fin N => μ := by congr 1;funext x;ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
lemma expected_process_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ))
    (hm : ∀ h ∈ H,Measurable h) (hsep : PointwiseSeparable μ H) :
    (∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (4/τ)*radSup μ H N := by
  have hs := (expected_process_le_radSup_cutoff μ τ N hN H hm hsep).trans
    (mul_le_mul' le_rfl (cutoff_rad_contraction μ τ hτ N hN H))
  have he : (2:ℝ≥0∞)*ENNReal.ofReal (2/τ)=ENNReal.ofReal (4/τ) := by
    rw [show (2:ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,← ENNReal.ofReal_mul (by norm_num)]
    congr 1;ring
  simpa only [← mul_assoc,he] using hs
end Queelius.RademacherContraction

namespace Queelius.RademacherContraction
open MeasureTheory LearnNoConc.ERM Queelius.SmallBallCutoff
open scoped ENNReal
lemma real_process_mean_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) (N : ℕ) (hN : 0 < N) (H : Set (Ω → ℝ))
    (hm : ∀ h ∈ H,Measurable h) (hsep : PointwiseSeparable μ H) (q : ℝ) (hq : 0 ≤ q)
    (hE : radSup μ H N ≤ ENNReal.ofReal (τ*q/16)) :
    (∫ x,(process μ τ N H x).toReal ∂Measure.pi fun _ : Fin N => μ) ≤ q/4 := by
  have hi := real_process_integrable μ τ N hN H hm hsep
  have hm0 : 0 ≤ (∫ x,(process μ τ N H x).toReal ∂Measure.pi fun _ : Fin N => μ) :=
    integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have he : ENNReal.ofReal (∫ x,(process μ τ N H x).toReal ∂Measure.pi fun _ : Fin N => μ)=
      ∫⁻ x,process μ τ N H x ∂Measure.pi fun _ : Fin N => μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))]
    apply lintegral_congr
    intro x
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (process_le_one μ τ N hN H hm x))
  have hb := (expected_process_bound μ τ hτ N hN H hm hsep).trans (mul_le_mul' le_rfl hE)
  have hc : ENNReal.ofReal (4/τ)*ENNReal.ofReal (τ*q/16)=ENNReal.ofReal (q/4) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    <;> ring
  rw [← he,hc] at hb
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal hm0,ENNReal.toReal_ofReal (by positivity : 0 ≤ q/4)] using ht
end Queelius.RademacherContraction
namespace LearnNoConc.ERM
open MeasureTheory Queelius.SmallBallCutoff Queelius.RademacherContraction
open scoped ENNReal
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Set (Ω → ℝ)) (hHm : ∀ h ∈ H, Measurable h) (hH2 : ∀ h ∈ H, MemLp h 2 μ)
    (hS : ∀ h ∈ H, eLpNorm h 2 μ = 1) (hHsep : PointwiseSeparable μ H)
    (N : ℕ) (hN : 0 < N) (τ : ℝ) (hτ : 0 < τ) (hQ : 0 < Q μ H (2 * τ))
    (hE : radSup μ H N ≤ ENNReal.ofReal (τ * Q μ H (2 * τ) / 16)) :
    (Measure.pi fun _ : Fin N => μ)
      {x | ∃ h ∈ H, ((Finset.univ.filter fun i => τ ≤ |h (x i)|).card : ℝ)
          < N * Q μ H (2 * τ) / 4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(N * Q μ H (2 * τ) ^ 2 / 2))) := by
  classical
  let q := Q μ H (2*τ)
  let m := ∫ y,(process μ τ N H y).toReal ∂Measure.pi fun _ : Fin N => μ
  have hm : m ≤ q/4 := real_process_mean_bound μ τ hτ N hN H hHm hHsep q hQ.le hE
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hsub : {x | ∃ h ∈ H, ((Finset.univ.filter fun i => τ ≤ |h (x i)|).card : ℝ)<N*q/4} ⊆
      {x | q/2 ≤ (process μ τ N H x).toReal-m} := by
    rintro x ⟨h,hh,hbad⟩
    have hB : BddBelow (Set.range (fun h : H => μ.real {z | (2*τ)*(eLpNorm h.val 2 μ).toReal ≤ |h.val z|})) := by
      refine ⟨0,?_⟩
      rintro _ ⟨g,rfl⟩;positivity
    have hlow := ciInf_le hB (⟨h,hh⟩ : H)
    change q ≤ μ.real {z | (2*τ)*(eLpNorm h 2 μ).toReal ≤ |h z|} at hlow
    rw [hS h hh,ENNReal.toReal_one,mul_one] at hlow
    have he := empirical_lower μ h (hHm h hh) τ hτ N hN x
    have hd : deviation μ τ N h x ≤ process μ τ N H x :=
      le_iSup_of_le h (le_iSup_of_le hh le_rfl)
    have hf : process μ τ N H x ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (process_le_one μ τ N hN H hHm x)
    have ha := ENNReal.toReal_mono hf hd
    simp only [deviation,ENNReal.toReal_ofReal (abs_nonneg _),centered] at ha
    have hcard : ((Finset.univ.filter fun i => τ ≤ |h (x i)|).card : ℝ)/(N:ℝ)<q/4 :=
      (div_lt_iff₀ hn).mpr (by nlinarith)
    change q/2 ≤ (process μ τ N H x).toReal-m
    linarith
  have ht := Queelius.ProductConcentration.uniform_process_tail μ τ N hN H hHm hHsep (q/2) (by linarith [hQ])
  have hmono := measure_mono (μ := Measure.pi fun _ : Fin N => μ) hsub
  apply hmono.trans
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply (ENNReal.ofReal_le_ofReal ht).trans
  apply ENNReal.ofReal_le_ofReal
  have hex : -2*(N:ℝ)*(q/2)^2= -((N:ℝ)*q^2/2) := by ring
  rw [hex]
  change Real.exp (-((N:ℝ)*q^2/2)) ≤ 2*Real.exp (-((N:ℝ)*q^2/2))
  linarith [Real.exp_pos (-((N:ℝ)*q^2/2))]
end LearnNoConc.ERM
