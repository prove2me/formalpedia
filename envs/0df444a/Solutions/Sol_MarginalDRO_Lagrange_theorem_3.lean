-- Prove2me | solution 1 for MarginalDRO.Lagrange.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:24:03.207778+00:00
-- url     : https://prove2.me/submissions/ef8be162-fe68-4b50-8e44-3c70c84bde64

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model
import Theorems.Thm_MarginalDRO_Lagrange_sec_3_1_measurable_selection

open MeasureTheory ProbabilityTheory Set Filter Topology
open MarginalDRO.Lagrange

namespace MDROq

variable (m : Measure ℝ) [IsProbabilityMeasure m]

lemma S_nonempty {t : ℝ} (ht : t < 1) : {x | t < cdf m x}.Nonempty :=
  ((tendsto_cdf_atTop m).eventually (lt_mem_nhds ht)).exists

lemma S_bdd {t : ℝ} (ht : 0 < t) : BddBelow {x | t < cdf m x} := by
  obtain ⟨x0, hx0⟩ := ((tendsto_cdf_atBot m).eventually (gt_mem_nhds ht)).exists
  refine ⟨x0, fun y hy => ?_⟩
  by_contra h
  have := (cdf m).mono (not_le.mp h).le
  simp only [mem_ofPred_eq] at hy
  linarith

lemma quantile_le_of_lt {t x : ℝ} (h0 : 0 < t) (h : t < cdf m x) : quantile m t ≤ x :=
  csInf_le (S_bdd m h0) h

lemma le_cdf_of_quantile_le {t x : ℝ} (h1 : t < 1) (h : quantile m t ≤ x) : t ≤ cdf m x := by
  by_contra hlt
  have hlt : cdf m x < t := not_le.mp hlt
  have hc : ContinuousWithinAt (cdf m) (Ici x) x := (cdf m).right_continuous x
  have h2 : ∀ᶠ y in 𝓝[>] x, cdf m y < t :=
    (hc.mono Ioi_subset_Ici_self) (Iio_mem_nhds hlt)
  obtain ⟨y, hy, hyx⟩ := (h2.and self_mem_nhdsWithin).exists
  have : y ≤ quantile m t := le_csInf (S_nonempty m h1) fun z hz => by
    by_contra hzy
    have := (cdf m).mono (not_le.mp hzy).le
    simp only [mem_ofPred_eq] at hz
    linarith
  have : x < y := hyx
  linarith

lemma cdf_le_of_lt_quantile {t s : ℝ} (h0 : 0 < t) (h : s < quantile m t) : cdf m s ≤ t := by
  by_contra hlt
  exact absurd (quantile_le_of_lt m h0 (not_le.mp hlt)) (not_le.mpr h)

lemma quantile_monotoneOn : MonotoneOn (quantile m) (Ioo 0 1) := by
  intro t ht t' ht' htt'
  refine csInf_le_csInf (S_bdd m ht.1) (S_nonempty m ht'.2) fun x hx => ?_
  simp only [mem_ofPred_eq] at hx ⊢
  linarith

lemma quantile_aemeasurable : AEMeasurable (quantile m) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monotoneOn m)

instance isProb_Ioo : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) where
  measure_univ := by simp

theorem map_quantile : (volume.restrict (Ioo (0 : ℝ) 1)).map (quantile m) = m := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply_of_aemeasurable (quantile_aemeasurable m) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf]
  apply le_antisymm
  · calc volume (quantile m ⁻¹' Iic x ∩ Ioo 0 1) ≤ volume (Ioc 0 (cdf m x)) :=
          measure_mono fun t ht => ⟨ht.2.1, le_cdf_of_quantile_le m ht.2.2 ht.1⟩
      _ = ENNReal.ofReal (cdf m x) := by simp [Real.volume_Ioc]
  · calc ENNReal.ofReal (cdf m x) = volume (Ioo 0 (cdf m x)) := by simp [Real.volume_Ioo]
      _ ≤ volume (quantile m ⁻¹' Iic x ∩ Ioo 0 1) := measure_mono fun t ht =>
          (⟨quantile_le_of_lt m ht.1 ht.2, ht.1, lt_of_lt_of_le ht.2 (cdf_le_one m x)⟩ :
            t ∈ quantile m ⁻¹' Iic x ∩ Ioo 0 1)


/-- `max_{b ∈ A} (c b - ψ b)`. -/
noncomputable def conjA (A : Finset ℝ) (hA : A.Nonempty) (ψ : ℝ → ℝ) (c : ℝ) : ℝ :=
  A.sup' hA (fun b => c * b - ψ b)

/-- the quantile coupling -/
noncomputable def γQ (μ π : Measure ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map (fun t => (quantile μ t, quantile π t))

/-- a measurable version of `ψ` agreeing with it on `A` -/
noncomputable def psiHat (A : Finset ℝ) (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ b ∈ A, ψ b * ({b} : Set ℝ).indicator 1 y

lemma psiHat_eq (A : Finset ℝ) (ψ : ℝ → ℝ) {y : ℝ} (hy : y ∈ A) : psiHat A ψ y = ψ y := by
  classical
  unfold psiHat
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb; simp [Set.indicator_apply, Ne.symm hb]
  · intro h; exact absurd hy h

lemma psiHat_measurable (A : Finset ℝ) (ψ : ℝ → ℝ) : Measurable (psiHat A ψ) := by
  unfold psiHat
  exact Finset.measurable_sum _ fun b _ =>
    (measurable_one.indicator (measurableSet_singleton b)).const_mul _

lemma psiHat_abs_le (A : Finset ℝ) (ψ : ℝ → ℝ) (y : ℝ) : |psiHat A ψ y| ≤ ∑ b ∈ A, |ψ b| := by
  unfold psiHat
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul]
  have : |({b} : Set ℝ).indicator (1 : ℝ → ℝ) y| ≤ 1 := by
    by_cases h : y ∈ ({b} : Set ℝ) <;> simp [Set.indicator_apply, h]
  nlinarith [abs_nonneg (ψ b)]

lemma integral_psiHat (A : Finset ℝ) (ψ : ℝ → ℝ) (π : Measure ℝ) [IsFiniteMeasure π] :
    ∫ y, psiHat A ψ y ∂π = ∑ b ∈ A, π.real {b} * ψ b := by
  unfold psiHat
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_indicator_one (measurableSet_singleton b), mul_comm]
  · intro b _
    exact ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton b)).const_mul _

lemma conjA_measurable (A : Finset ℝ) (hA : A.Nonempty) (ψ : ℝ → ℝ) :
    Measurable (conjA A hA ψ) := by
  have : conjA A hA ψ = A.sup' hA (fun b (c : ℝ) => c * b - ψ b) := by
    funext c; rw [Finset.sup'_apply]; rfl
  rw [this]
  exact Finset.measurable_sup' _ fun b _ => by fun_prop

lemma conjA_abs_le (A : Finset ℝ) (hA : A.Nonempty) (ψ : ℝ → ℝ) (c : ℝ) :
    |conjA A hA ψ c| ≤ |c| * (∑ b ∈ A, |b|) + ∑ b ∈ A, |ψ b| := by
  obtain ⟨a, ha, hca⟩ := Finset.exists_mem_eq_sup' hA (fun b => c * b - ψ b)
  rw [conjA, hca]
  have h1 : |a| ≤ ∑ b ∈ A, |b| :=
    Finset.single_le_sum (f := fun b : ℝ => |b|) (fun _ _ => abs_nonneg _) ha
  have h2 : |ψ a| ≤ ∑ b ∈ A, |ψ b| :=
    Finset.single_le_sum (f := fun b : ℝ => |ψ b|) (fun _ _ => abs_nonneg _) ha
  calc |c * a - ψ a| ≤ |c * a| + |ψ a| := abs_sub _ _
    _ = |c| * |a| + |ψ a| := by rw [abs_mul]
    _ ≤ _ := by gcongr

lemma conjA_integrable (A : Finset ℝ) (hA : A.Nonempty) (ψ : ℝ → ℝ)
    (m : Measure ℝ) [IsFiniteMeasure m] (hm : Integrable id m) :
    Integrable (conjA A hA ψ) m := by
  refine Integrable.mono' (g := fun c => |c| * (∑ b ∈ A, |b|) + ∑ b ∈ A, |ψ b|)
    ((hm.abs.mul_const _).add (integrable_const _))
    (conjA_measurable A hA ψ).aestronglyMeasurable (Filter.Eventually.of_forall fun c => ?_)
  rw [Real.norm_eq_abs]; exact conjA_abs_le A hA ψ c

lemma ae_snd_mem (π : Measure ℝ) (A : Finset ℝ) (hπA : π (↑A)ᶜ = 0) (γ : Measure (ℝ × ℝ))
    (hγ : γ.map Prod.snd = π) : ∀ᵐ p ∂γ, p.2 ∈ A := by
  have : ∀ᵐ y ∂(γ.map Prod.snd), y ∈ A := by
    rw [hγ, ae_iff]; exact hπA
  exact ae_of_ae_map measurable_snd.aemeasurable this

lemma integrable_mul_coupling (μ π : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (A : Finset ℝ) (hπA : π (↑A)ᶜ = 0) (γ : Measure (ℝ × ℝ))
    (hγ : γ ∈ couplings μ π) : Integrable (fun p : ℝ × ℝ => p.1 * p.2) γ := by
  have h1 : Integrable (fun p : ℝ × ℝ => p.1) γ := by
    have := hμ
    rw [← hγ.2.1] at this
    exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).mp this
  refine h1.mul_bdd (c := ∑ b ∈ A, |b|) measurable_snd.aestronglyMeasurable ?_
  filter_upwards [ae_snd_mem π A hπA γ hγ.2.2] with p hp
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun b : ℝ => |b|) (fun _ _ => abs_nonneg _) hp

/-- weak duality -/
lemma weak_duality (μ π : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : Integrable id μ) (A : Finset ℝ) (hA : A.Nonempty) (hπA : π (↑A)ᶜ = 0)
    (γ : Measure (ℝ × ℝ)) (hγ : γ ∈ couplings μ π) (ψ : ℝ → ℝ) :
    ∫ p, p.1 * p.2 ∂γ ≤ ∑ b ∈ A, π.real {b} * ψ b + ∫ c, conjA A hA ψ c ∂μ := by
  have hγP : IsProbabilityMeasure γ := hγ.1
  have hI1 := integrable_mul_coupling μ π hμ A hπA γ hγ
  have hI2 : Integrable (fun p : ℝ × ℝ => psiHat A ψ p.2) γ :=
    Integrable.of_bound ((psiHat_measurable A ψ).comp measurable_snd).aestronglyMeasurable
      (∑ b ∈ A, |ψ b|) (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact psiHat_abs_le A ψ p.2)
  have hI3 : Integrable (fun p : ℝ × ℝ => conjA A hA ψ p.1) γ := by
    have := conjA_integrable A hA ψ μ hμ
    rw [← hγ.2.1] at this
    exact (integrable_map_measure (conjA_measurable A hA ψ).aestronglyMeasurable
      measurable_fst.aemeasurable).mp this
  have h1 : ∫ p, p.1 * p.2 ∂γ ≤ ∫ p, (psiHat A ψ p.2 + conjA A hA ψ p.1) ∂γ := by
    refine integral_mono_ae hI1 (hI2.add hI3) ?_
    filter_upwards [ae_snd_mem π A hπA γ hγ.2.2] with p hp
    rw [psiHat_eq A ψ hp]
    have : p.1 * p.2 - ψ p.2 ≤ conjA A hA ψ p.1 :=
      Finset.le_sup' (fun b => p.1 * b - ψ b) hp
    show p.1 * p.2 ≤ ψ p.2 + conjA A hA ψ p.1
    linarith
  rw [integral_add hI2 hI3] at h1
  have e2 : ∫ p, psiHat A ψ p.2 ∂γ = ∑ b ∈ A, π.real {b} * ψ b := by
    rw [← integral_psiHat A ψ π, ← hγ.2.2, integral_map measurable_snd.aemeasurable
      (psiHat_measurable A ψ).aestronglyMeasurable]
  have e3 : ∫ p, conjA A hA ψ p.1 ∂γ = ∫ c, conjA A hA ψ c ∂μ := by
    rw [← hγ.2.1, integral_map measurable_fst.aemeasurable
      (conjA_measurable A hA ψ).aestronglyMeasurable]
  linarith

lemma γQ_mem (μ π : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure π] :
    γQ μ π ∈ couplings μ π := by
  have hm : AEMeasurable (fun t => (quantile μ t, quantile π t)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (quantile_aemeasurable μ).prodMk (quantile_aemeasurable π)
  refine ⟨Measure.isProbabilityMeasure_map hm, ?_, ?_⟩
  · rw [γQ, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hm]
    exact map_quantile μ
  · rw [γQ, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hm]
    exact map_quantile π


lemma dual_approx (μ π : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : Integrable id μ) (A : Finset ℝ) (hA : A.Nonempty) (hπA : π (↑A)ᶜ = 0) :
    ∀ ε > 0, ∃ ψ : ℝ → ℝ, ∑ b ∈ A, π.real {b} * ψ b + ∫ c, conjA A hA ψ c ∂μ ≤
      ∫ p, p.1 * p.2 ∂(γQ μ π) + ε := by
  classical
  intro ε hε
  set S := A.filter (fun b => π {b} ≠ 0) with hSdef
  have hSA : ∀ b ∈ S, b ∈ A := fun b hb => (Finset.mem_filter.mp hb).1
  have hS0 : ∀ b ∈ A, b ∉ S → π {b} = 0 := fun b hb hbS => by
    by_contra h; exact hbS (Finset.mem_filter.mpr ⟨hb, h⟩)
  have hπS : π (↑S)ᶜ = 0 := by
    have hsub : (↑S : Set ℝ)ᶜ ⊆ (↑A)ᶜ ∪ ↑(A.filter (fun b => b ∉ S)) := by
      intro y hy
      by_cases hyA : y ∈ A
      · right; simp only [Finset.coe_filter, mem_setOf_eq]
        exact ⟨hyA, hy⟩
      · left; exact hyA
    refine measure_mono_null hsub (measure_union_null hπA ?_)
    rw [← sum_measure_singleton]
    exact Finset.sum_eq_zero fun b hb => by
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb; exact hS0 b hb1 hb2
  have hS : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 : π univ = 0 := by
      rw [← compl_empty, ← Finset.coe_empty, ← hne]; exact hπS
    simp at h1
  set amin := S.min' hS
  set amax := S.max' hS
  have hamin : amin ∈ S := S.min'_mem hS
  have hamax : amax ∈ S := S.max'_mem hS
  have hpos : ∀ b ∈ S, 0 < π.real {b} := fun b hb => by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Finset.mem_filter.mp hb).2 (measure_ne_top _ _)
  set δ := min (π.real {amin}) (π.real {amax}) with hδdef
  have hδ : 0 < δ := lt_min (hpos _ hamin) (hpos _ hamax)
  have hFlo : ∀ s, amin ≤ s → δ ≤ cdf π s := fun s hs => by
    rw [cdf_eq_real]
    exact (min_le_left _ _).trans (measureReal_mono (by
      intro y hy; simp only [mem_singleton_iff] at hy; subst hy; exact hs))
  have hFhi : ∀ s, s < amax → cdf π s ≤ 1 - δ := fun s hs => by
    rw [cdf_eq_real]
    have hd : Disjoint (Iic s) {amax} := by
      rw [Set.disjoint_singleton_right]; simp only [mem_Iic, not_le]; exact hs
    have := measureReal_union (μ := π) hd (measurableSet_singleton amax)
    have h1 : π.real (Iic s ∪ {amax}) ≤ 1 := measureReal_le_one
    have h2 : δ ≤ π.real {amax} := min_le_right _ _
    linarith
  set clamp : ℝ → ℝ := fun u => max δ (min u (1 - δ)) with hclampdef
  set h : ℝ → ℝ := fun s => quantile μ (clamp (cdf π s)) with hhdef
  have hmono : Monotone h := by
    intro s s' hss'
    by_cases hδ' : δ ≤ 1 - δ
    · have hc : ∀ u, clamp u ∈ Ioo (0 : ℝ) 1 := fun u => by
        refine ⟨lt_of_lt_of_le hδ (le_max_left _ _), ?_⟩
        refine lt_of_le_of_lt (max_le hδ' (min_le_right _ _)) (by linarith)
      refine quantile_monotoneOn μ (hc _) (hc _) ?_
      exact max_le_max le_rfl (min_le_min ((cdf π).mono hss') le_rfl)
    · have hc : ∀ u, clamp u = δ := fun u =>
        max_eq_left ((min_le_right _ _).trans (le_of_lt (not_le.mp hδ')))
      simp only [h, hc, le_refl]
  have hII : ∀ a b, IntervalIntegrable h volume a b := fun a b => hmono.intervalIntegrable
  set ψ : ℝ → ℝ := fun b => ∫ s in amin..b, h s with hψdef
  have hψsub : ∀ a b, ψ b - ψ a = ∫ s in a..b, h s := fun a b =>
    intervalIntegral.integral_interval_sub_left (hII _ _) (hII _ _)
  have hclamp : ∀ s, amin ≤ s → s < amax → clamp (cdf π s) = cdf π s := fun s h1 h2 => by
    simp only [clamp]
    rw [min_eq_left (hFhi s h2), max_eq_right (hFlo s h1)]
  have hFIoo : ∀ s, amin ≤ s → s < amax → cdf π s ∈ Ioo (0 : ℝ) 1 := fun s h1 h2 =>
    ⟨lt_of_lt_of_le hδ (hFlo s h1), lt_of_le_of_lt (hFhi s h2) (by linarith)⟩
  have key : ∀ t ∈ Ioo (0 : ℝ) 1, quantile π t ∈ S → ∀ b, amin ≤ b → b ≤ amax →
      quantile μ t * b - ψ b ≤ quantile μ t * quantile π t - ψ (quantile π t) := by
    intro t ht haS b hb1 hb2
    set a := quantile π t
    set c := quantile μ t
    have ha1 : amin ≤ a := S.min'_le a haS
    have ha2 : a ≤ amax := S.le_max' a haS
    rcases le_total a b with hab | hab
    · have h1 : ∫ s in a..b, c ≤ ∫ s in a..b, h s :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab intervalIntegrable_const (hII _ _)
          fun s hs => by
            have hs1 : amin ≤ s := ha1.trans hs.1.le
            have hs2 : s < amax := lt_of_lt_of_le hs.2 hb2
            simp only [h]
            rw [hclamp s hs1 hs2]
            refine quantile_monotoneOn μ ht (hFIoo s hs1 hs2) ?_
            exact (le_cdf_of_quantile_le π ht.2 le_rfl).trans ((cdf π).mono hs.1.le)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have := hψsub a b
      nlinarith
    · have h1 : ∫ s in b..a, h s ≤ ∫ s in b..a, c :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab (hII _ _) intervalIntegrable_const
          fun s hs => by
            have hs1 : amin ≤ s := hb1.trans hs.1.le
            have hs2 : s < amax := lt_of_lt_of_le hs.2 ha2
            simp only [h]
            rw [hclamp s hs1 hs2]
            exact quantile_monotoneOn μ (hFIoo s hs1 hs2) ht
              (cdf_le_of_lt_quantile π ht.1 hs.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have := hψsub b a
      nlinarith
  -- a.e. facts on (0,1)
  set vol' := volume.restrict (Ioo (0 : ℝ) 1) with hvol'
  have aeS : ∀ᵐ t ∂vol', quantile π t ∈ S := by
    refine ae_of_ae_map (quantile_aemeasurable π) ?_
    rw [map_quantile, ae_iff]; exact hπS
  have aeIoo : ∀ᵐ t ∂vol', t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  -- the restricted conjugate
  set I := A.filter (fun b => amin ≤ b ∧ b ≤ amax) with hIdef
  have hI : I.Nonempty := ⟨amin, Finset.mem_filter.mpr ⟨hSA _ hamin, le_rfl, S.min'_le _ hamax⟩⟩
  have hconjIn : ∀ t ∈ Ioo (0 : ℝ) 1, quantile π t ∈ S →
      conjA I hI ψ (quantile μ t) = quantile μ t * quantile π t - ψ (quantile π t) := by
    intro t ht haS
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun b hb => by
        obtain ⟨_, hb1, hb2⟩ := Finset.mem_filter.mp hb
        exact key t ht haS b hb1 hb2
    · exact Finset.le_sup' (fun b => quantile μ t * b - ψ b)
        (Finset.mem_filter.mpr ⟨hSA _ haS, S.min'_le _ haS, S.le_max' _ haS⟩)
  have hpair : AEMeasurable (fun t => (quantile μ t, quantile π t)) vol' :=
    (quantile_aemeasurable μ).prodMk (quantile_aemeasurable π)
  have hγQ := γQ_mem μ π
  have hγQP : IsProbabilityMeasure (γQ μ π) := hγQ.1
  have hval : ∑ b ∈ A, π.real {b} * ψ b + ∫ c, conjA I hI ψ c ∂μ = ∫ p, p.1 * p.2 ∂(γQ μ π) := by
    have e1 : ∫ c, conjA I hI ψ c ∂μ = ∫ t, conjA I hI ψ (quantile μ t) ∂vol' := by
      conv_lhs => rw [← map_quantile μ]
      rw [integral_map (quantile_aemeasurable μ) (conjA_measurable I hI ψ).aestronglyMeasurable]
    have e2 : ∫ t, conjA I hI ψ (quantile μ t) ∂vol' =
        ∫ t, (quantile μ t * quantile π t - psiHat A ψ (quantile π t)) ∂vol' := by
      refine integral_congr_ae ?_
      filter_upwards [aeS, aeIoo] with t h1 h2
      rw [hconjIn t h2 h1, psiHat_eq A ψ (hSA _ h1)]
    have e3 : ∫ t, (quantile μ t * quantile π t - psiHat A ψ (quantile π t)) ∂vol' =
        ∫ p, (p.1 * p.2 - psiHat A ψ p.2) ∂(γQ μ π) := by
      rw [γQ, integral_map hpair]
      exact ((measurable_fst.mul measurable_snd).sub
        ((psiHat_measurable A ψ).comp measurable_snd)).aestronglyMeasurable
    have hI2 : Integrable (fun p : ℝ × ℝ => psiHat A ψ p.2) (γQ μ π) :=
      Integrable.of_bound ((psiHat_measurable A ψ).comp measurable_snd).aestronglyMeasurable
        (∑ b ∈ A, |ψ b|) (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact psiHat_abs_le A ψ p.2)
    have e4 : ∫ p, (p.1 * p.2 - psiHat A ψ p.2) ∂(γQ μ π) =
        ∫ p, p.1 * p.2 ∂(γQ μ π) - ∑ b ∈ A, π.real {b} * ψ b := by
      rw [integral_sub (integrable_mul_coupling μ π hμ A hπA _ hγQ) hI2]
      congr 1
      rw [← integral_psiHat A ψ π]
      conv_rhs => rw [← hγQ.2.2]
      rw [integral_map measurable_snd.aemeasurable (psiHat_measurable A ψ).aestronglyMeasurable]
    rw [e1, e2, e3, e4]; ring
  -- penalised potentials
  set pen : ℝ → ℝ := fun b => max 0 (amin - b) + max 0 (b - amax) with hpendef
  have hpen_nn : ∀ b, 0 ≤ pen b := fun b => add_nonneg (le_max_left _ _) (le_max_left _ _)
  have hpen0 : ∀ b, amin ≤ b → b ≤ amax → pen b = 0 := fun b h1 h2 => by
    simp only [pen]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  have hpenpos : ∀ b, ¬ (amin ≤ b ∧ b ≤ amax) → 0 < pen b := fun b hb => by
    simp only [pen]
    rcases not_and_or.mp hb with h | h
    · have h' : 0 < amin - b := by linarith [not_le.mp h]
      linarith [le_max_right 0 (amin - b), le_max_left 0 (b - amax)]
    · have h' : 0 < b - amax := by linarith [not_le.mp h]
      linarith [le_max_right 0 (b - amax), le_max_left 0 (amin - b)]
  set ψM : ℕ → ℝ → ℝ := fun M b => ψ b + M * pen b with hψMdef
  have hsumM : ∀ M : ℕ, ∑ b ∈ A, π.real {b} * ψM M b = ∑ b ∈ A, π.real {b} * ψ b := by
    intro M
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hbS : b ∈ S
    · simp only [ψM]
      rw [hpen0 b (S.min'_le _ hbS) (S.le_max' _ hbS)]; ring
    · rw [measureReal_def, hS0 b hb hbS]; simp
  have hlow : ∀ (M : ℕ) c, conjA I hI ψ c ≤ conjA A hA (ψM M) c := fun M c =>
    Finset.sup'_le _ _ fun b hb => by
      obtain ⟨hbA, hb1, hb2⟩ := Finset.mem_filter.mp hb
      have := Finset.le_sup' (fun b => c * b - ψM M b) hbA
      simp only [ψM, hpen0 b hb1 hb2, mul_zero, add_zero] at this
      exact this
  have hup : ∀ (M : ℕ) c, conjA A hA (ψM M) c ≤ conjA A hA ψ c := fun M c =>
    Finset.sup'_le _ _ fun b hb => by
      have := Finset.le_sup' (fun b => c * b - ψ b) hb
      have h2 : 0 ≤ (M : ℝ) * pen b := mul_nonneg (Nat.cast_nonneg _) (hpen_nn b)
      simp only [ψM]
      exact le_trans (by linarith) this
  have hlim : ∀ c, Tendsto (fun M : ℕ => conjA A hA (ψM M) c) atTop (𝓝 (conjA I hI ψ c)) := by
    intro c
    set r : ℝ → ℝ := fun b => (c * b - ψ b - conjA I hI ψ c) / pen b
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑ b ∈ A, |r b| ≤ N := ⟨⌈∑ b ∈ A, |r b|⌉₊, Nat.le_ceil _⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    refine le_antisymm (hlow M c) (Finset.sup'_le _ _ fun b hb => ?_)
    by_cases hbI : amin ≤ b ∧ b ≤ amax
    · have hbI' : b ∈ I := Finset.mem_filter.mpr ⟨hb, hbI⟩
      have := Finset.le_sup' (fun b => c * b - ψ b) hbI'
      simp only [ψM, hpen0 b hbI.1 hbI.2, mul_zero, add_zero]
      exact this
    · have hp := hpenpos b hbI
      have h1 : r b ≤ M := by
        have : |r b| ≤ ∑ b ∈ A, |r b| :=
          Finset.single_le_sum (f := fun b => |r b|) (fun _ _ => abs_nonneg _) hb
        have hM' : (N : ℝ) ≤ M := by exact_mod_cast hM
        linarith [le_abs_self (r b)]
      have h2 : r b * pen b = c * b - ψ b - conjA I hI ψ c := by
        simp only [r]; field_simp
      have h3 : r b * pen b ≤ M * pen b := mul_le_mul_of_nonneg_right h1 hp.le
      simp only [ψM]
      linarith
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun M c => conjA A hA (ψM M) c) (f := conjA I hI ψ)
    (fun c => |conjA A hA ψ c| + |conjA I hI ψ c|)
    (fun M => (conjA_measurable A hA (ψM M)).aestronglyMeasurable)
    ((conjA_integrable A hA ψ μ hμ).abs.add (conjA_integrable I hI ψ μ hμ).abs)
    (fun M => Filter.Eventually.of_forall fun c => by
      rw [Real.norm_eq_abs, abs_le]
      have h1 := hlow M c
      have h2 := hup M c
      constructor
      · linarith [neg_abs_le (conjA I hI ψ c), abs_nonneg (conjA A hA ψ c)]
      · linarith [le_abs_self (conjA A hA ψ c), abs_nonneg (conjA I hI ψ c)])
    (Filter.Eventually.of_forall hlim)
  obtain ⟨M, hM⟩ := (hdom.eventually (Iio_mem_nhds (lt_add_of_pos_right
    (∫ c, conjA I hI ψ c ∂μ) hε))).exists
  refine ⟨ψM M, ?_⟩
  rw [hsumM M]
  have hM' : ∫ c, conjA A hA (ψM M) c ∂μ < ∫ c, conjA I hI ψ c ∂μ + ε := hM
  linarith

end MDROq

open MDROq in
theorem kant_int {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ν : 𝒳 → ℝ) (hν : ν ∈ stdSimplex ℝ 𝒳) (i : Fin n) :
    ∃ m : ℝ,
      IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m ∧
      IsGLB {s | ∃ φ ψ : ℝ → ℝ, Integrable φ (μ i) ∧
        (∀ c : ℝ, ∀ a ∈ proj 𝒳 i, c * a ≤ φ c + ψ a) ∧
        s = ∫ c, φ c ∂(μ i) + ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i)} m ∧
      IsGLB (Set.range fun ψ : ℝ → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i)) m := by
  classical
  have hμ : Integrable id (μ i) := hint i
  set π := margMeasure 𝒳 ν i with hπdef
  set A := proj 𝒳 i with hAdef
  have hA : A.Nonempty := h𝒳.image _
  have hν0 : ∀ x, 0 ≤ ν x := hν.1
  have hπP : IsProbabilityMeasure π := by
    constructor
    rw [hπdef, margMeasure, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hν0 x), hν.2, ENNReal.ofReal_one]
  have hπA : π (↑A)ᶜ = 0 := by
    rw [hπdef, margMeasure, Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (Finset.measurableSet _).compl]
    have : ((x : Fin n → ℝ) i) ∈ A := Finset.mem_image_of_mem _ x.2
    simp [this]
  have hπreal : ∀ b, π.real {b} = ∑ x : 𝒳, if (x : Fin n → ℝ) i = b then ν x else 0 := by
    intro b
    rw [measureReal_def, hπdef, margMeasure, Measure.finsetSum_apply,
      ENNReal.toReal_sum (fun x _ => by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton b), smul_eq_mul]
    by_cases hx : (x : Fin n → ℝ) i = b
    · simp [hx, hν0 x]
    · simp [hx]
  have hsum : ∀ ψ : ℝ → ℝ, ∑ b ∈ A, π.real {b} * ψ b = ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) := by
    intro ψ
    simp_rw [hπreal, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hxA : ((x : Fin n → ℝ) i) ∈ A := Finset.mem_image_of_mem _ x.2
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq A]
    simp [hxA]
  have hconj : ∀ ψ : ℝ → ℝ, conj 𝒳 h𝒳 ψ i = conjA A hA ψ := fun ψ => rfl
  set m := ∫ p, p.1 * p.2 ∂(γQ (μ i) π) with hm
  have hγQ := γQ_mem (μ i) π
  have hlow : ∀ ψ : ℝ → ℝ, m ≤ ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) := by
    intro ψ
    rw [← hsum, hconj]
    exact weak_duality (μ i) π hμ A hA hπA _ hγQ ψ
  have happ : ∀ ε > 0, ∃ ψ : ℝ → ℝ,
      ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) ≤ m + ε := by
    intro ε hε
    obtain ⟨ψ, hψ⟩ := dual_approx (μ i) π hμ A hA hπA ε hε
    exact ⟨ψ, by rw [← hsum, hconj]; exact hψ⟩
  refine ⟨m, ⟨⟨_, hγQ, rfl⟩, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨ψ, hψ⟩ := happ ε hε
    have := weak_duality (μ i) π hμ A hA hπA γ hγ ψ
    rw [hsum, ← hconj] at this
    linarith
  · rintro _ ⟨φ, ψ, hφ, hfeas, rfl⟩
    have h1 : ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) ≤ ∫ c, φ c ∂(μ i) := by
      rw [hconj]
      refine integral_mono (conjA_integrable A hA ψ _ hμ) hφ fun c => ?_
      exact Finset.sup'_le _ _ fun a ha => by linarith [hfeas c a ha]
    linarith [hlow ψ]
  · intro b hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨ψ, hψ⟩ := happ ε hε
    have hmem : ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) + ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) ∈
        {s | ∃ φ ψ : ℝ → ℝ, Integrable φ (μ i) ∧
          (∀ c : ℝ, ∀ a ∈ proj 𝒳 i, c * a ≤ φ c + ψ a) ∧
          s = ∫ c, φ c ∂(μ i) + ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i)} := by
      refine ⟨conj 𝒳 h𝒳 ψ i, ψ, ?_, fun c a ha => ?_, rfl⟩
      · rw [hconj]; exact conjA_integrable A hA ψ _ hμ
      · have : c * a - ψ a ≤ conj 𝒳 h𝒳 ψ i c := by
          rw [hconj]; exact Finset.le_sup' (fun b => c * b - ψ b) ha
        linarith
    have := hb hmem
    linarith
  · rintro _ ⟨ψ, rfl⟩
    exact hlow ψ
  · intro b hb
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨ψ, hψ⟩ := happ ε hε
    have := hb ⟨ψ, rfl⟩
    linarith

theorem lower_int {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ν : 𝒳 → ℝ) (hν : ν ∈ stdSimplex ℝ 𝒳) (γ : Fin n → Measure (ℝ × ℝ))
    (hγ : ∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) :
    ∃ θ ∈ frechetClass μ, ∑ i, ∫ p, p.1 * p.2 ∂(γ i) ≤ ∫ c, Z 𝒳 h𝒳 c ∂θ := by
  classical
  have hγP : ∀ i, IsProbabilityMeasure (γ i) := fun i => (hγ i).1
  set γ' : Fin n → Measure (ℝ × ℝ) := fun i => (γ i).map Prod.swap with hγ'
  have hγ'P : ∀ i, IsProbabilityMeasure (γ' i) := fun i =>
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  set κ : Fin n → Kernel ℝ ℝ := fun i => (γ' i).condKernel with hκ
  have hfst : ∀ i, (γ' i).fst = margMeasure 𝒳 ν i := by
    intro i
    rw [Measure.fst, hγ', Measure.map_map measurable_fst measurable_swap]
    exact (hγ i).2.2
  have hdis : ∀ i, (γ' i).fst ⊗ₘ κ i = γ' i := fun i => Measure.disintegrate _ _
  have hν0 : ∀ x, 0 ≤ ν x := hν.1
  -- (F1) mixture representation of μ i
  have hμ : ∀ i, μ i = ∑ x : 𝒳, ENNReal.ofReal (ν x) • κ i ((x : Fin n → ℝ) i) := by
    intro i
    have h1 : μ i = (γ' i).snd := by
      rw [Measure.snd, hγ', Measure.map_map measurable_snd measurable_swap]
      exact (hγ i).2.1.symm
    rw [h1, ← hdis i, Measure.snd_compProd, hfst]
    ext s hs
    rw [Measure.bind_apply hs (κ i).aemeasurable, margMeasure, lintegral_finset_sum_measure,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac, Measure.smul_apply, smul_eq_mul]
  -- integrability of the coupling objective
  have hμint : ∀ i, Integrable id (μ i) := hint
  set B : Fin n → ℝ := fun i => ∑ y ∈ 𝒳, |y i| with hB
  have hxB : ∀ i, ∀ x ∈ 𝒳, |x i| ≤ B i := fun i x hx =>
    Finset.single_le_sum (f := fun y : Fin n → ℝ => |y i|) (fun y _ => abs_nonneg _) hx
  have hγint : ∀ i, Integrable (fun p : ℝ × ℝ => p.1 * p.2) (γ i) := by
    intro i
    have h1 : Integrable (fun p : ℝ × ℝ => p.1) (γ i) := by
      have := hμint i
      rw [← (hγ i).2.1] at this
      exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).mp this
    refine h1.mul_bdd (c := B i) measurable_snd.aestronglyMeasurable ?_
    have h2 : ∀ᵐ y ∂((γ i).map Prod.snd), ‖y‖ ≤ B i := by
      rw [(hγ i).2.2, ae_iff, margMeasure, Measure.finsetSum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Measure.smul_apply, Measure.dirac_apply]
      have : |(x : Fin n → ℝ) i| ≤ B i := hxB i x x.2
      simp [Real.norm_eq_abs, this]
    exact ae_of_ae_map measurable_snd.aemeasurable h2
  -- (F2) the coupling value through the disintegration
  have hval : ∀ i, ∫ p, p.1 * p.2 ∂(γ i) =
      ∑ x : 𝒳, ν x * ((x : Fin n → ℝ) i * ∫ c, c ∂(κ i ((x : Fin n → ℝ) i))) := by
    intro i
    have h1 : ∫ p, p.1 * p.2 ∂(γ i) = ∫ q, q.2 * q.1 ∂(γ' i) := by
      rw [show γ' i = (γ i).map Prod.swap from rfl,
        integral_map (f := fun q : ℝ × ℝ => q.2 * q.1) measurable_swap.aemeasurable
        (continuous_snd.mul continuous_fst).aestronglyMeasurable]
      rfl
    have hint' : Integrable (fun q : ℝ × ℝ => q.2 * q.1) (γ' i) := by
      rw [show γ' i = (γ i).map Prod.swap from rfl]
      exact (integrable_map_measure (continuous_snd.mul continuous_fst).aestronglyMeasurable
        measurable_swap.aemeasurable).mpr (hγint i)
    rw [h1, ← hdis i] at *
    rw [Measure.integral_compProd hint', hfst, margMeasure, integral_finset_sum_measure]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hν0 x), smul_eq_mul,
        integral_mul_const, mul_comm (∫ c, c ∂(κ i ((x : Fin n → ℝ) i)))]
    · intro x _
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  -- (F3) integrability of the conditional laws charged by ν
  have hκint : ∀ i, ∀ x : 𝒳, ν x ≠ 0 → Integrable id (κ i ((x : Fin n → ℝ) i)) := by
    intro i x hx
    have hle : ENNReal.ofReal (ν x) • κ i ((x : Fin n → ℝ) i) ≤ μ i := by
      rw [hμ i]
      intro s
      rw [Measure.coe_finset_sum, Finset.sum_apply]
      exact Finset.single_le_sum (f := fun y : 𝒳 => (ENNReal.ofReal (ν y) • κ i ((y : Fin n → ℝ) i)) s)
        (fun _ _ => zero_le) (Finset.mem_univ x)
    have h1 := ((hμint i).mono_measure hle).smul_measure (c := (ENNReal.ofReal (ν x))⁻¹)
      (ENNReal.inv_ne_top.mpr (by
        rw [ENNReal.ofReal_ne_zero_iff]; exact lt_of_le_of_ne (hν0 x) (Ne.symm hx)))
    rwa [smul_smul, ENNReal.inv_mul_cancel (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact lt_of_le_of_ne (hν0 x) (Ne.symm hx))
      ENNReal.ofReal_ne_top, one_smul] at h1
  -- the joint law
  set P : 𝒳 → Measure (Fin n → ℝ) := fun x => Measure.pi (fun i => κ i ((x : Fin n → ℝ) i)) with hP
  have hPP : ∀ x, IsProbabilityMeasure (P x) := fun x => by rw [hP]; infer_instance
  set θ : Measure (Fin n → ℝ) := ∑ x : 𝒳, ENNReal.ofReal (ν x) • P x with hθ
  have hPmap : ∀ x : 𝒳, ∀ i, (P x).map (fun c => c i) = κ i ((x : Fin n → ℝ) i) := by
    intro x i
    have := Measure.pi_map_eval (μ := fun i => κ i ((x : Fin n → ℝ) i)) i
    simp only [measure_univ, Finset.prod_const_one, one_smul] at this
    exact this
  refine ⟨θ, ⟨?_, ?_⟩, ?_⟩
  · constructor
    rw [hθ, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hν0 x), hν.2, ENNReal.ofReal_one]
  · intro i
    rw [hμ i]
    ext s hs
    rw [Measure.map_apply (measurable_pi_apply i) hs, hθ, Measure.finsetSum_apply,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Measure.smul_apply, Measure.smul_apply, ← hPmap x i,
      Measure.map_apply (measurable_pi_apply i) hs]
  · have hZm : Measurable (fun c => Z 𝒳 h𝒳 c) := by
      have : (fun c => Z 𝒳 h𝒳 c) = 𝒳.sup' h𝒳 (fun y (c : Fin n → ℝ) => ∑ i, c i * y i) := by
        funext c; simp [Z, Finset.sup'_apply]
      rw [this]
      exact Finset.measurable_sup' h𝒳 fun y _ => by fun_prop
    have hcint : ∀ x : 𝒳, ν x ≠ 0 → ∀ i, Integrable (fun c : Fin n → ℝ => c i) (P x) := by
      intro x hx i
      have := hκint i x hx
      rw [← hPmap x i] at this
      exact (integrable_map_measure aestronglyMeasurable_id
        (measurable_pi_apply i).aemeasurable).mp this
    have hZint : ∀ x : 𝒳, ν x ≠ 0 → Integrable (fun c => Z 𝒳 h𝒳 c) (P x) := by
      intro x hx
      refine Integrable.mono' (g := fun c : Fin n → ℝ => ∑ i, B i * |c i|)
        (integrable_finset_sum _ fun i _ => (hcint x hx i).abs.const_mul (B i))
        hZm.aestronglyMeasurable (Filter.Eventually.of_forall fun c => ?_)
      obtain ⟨y, hy, hZy⟩ := Finset.exists_mem_eq_sup' h𝒳 (fun y : Fin n → ℝ => ∑ i, c i * y i)
      rw [Real.norm_eq_abs, Z, hZy]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hxB i y hy) (abs_nonneg _)
    rw [Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_comm, hθ,
      integral_finset_sum_measure]
    · refine Finset.sum_le_sum fun x _ => ?_
      rw [integral_smul_measure, ENNReal.toReal_ofReal (hν0 x), smul_eq_mul, ← Finset.mul_sum]
      by_cases hx : ν x = 0
      · simp [hx]
      refine mul_le_mul_of_nonneg_left ?_ (hν0 x)
      have h1 : ∀ i, (x : Fin n → ℝ) i * ∫ c, c ∂(κ i ((x : Fin n → ℝ) i)) =
          ∫ c, c i * (x : Fin n → ℝ) i ∂(P x) := by
        intro i
        have hm : Measurable (fun c : Fin n → ℝ => c i) := measurable_pi_apply i
        rw [← hPmap x i, integral_map (f := fun c : ℝ => c) hm.aemeasurable
          aestronglyMeasurable_id, integral_mul_const, mul_comm]
      rw [Finset.sum_congr rfl (fun i _ => h1 i), ← integral_finset_sum _
        (fun i _ => (hcint x hx i).mul_const _)]
      refine integral_mono (integrable_finset_sum _ fun i _ => (hcint x hx i).mul_const _)
        (hZint x hx) fun c => ?_
      exact Finset.le_sup' (fun y : Fin n → ℝ => ∑ i, c i * y i) x.2
    · intro x _
      by_cases hx : ν x = 0
      · simp [hx]
      · exact (hZint x hx).smul_measure ENNReal.ofReal_ne_top

lemma mdro_eq_sum_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : Measure α) (S : Finset α) (h : m (↑S)ᶜ = 0) :
    m = ∑ x ∈ S, m {x} • Measure.dirac x := by
  classical
  ext s hs
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  rw [← measure_inter_conull (s := s) h]
  have : s ∩ (↑S : Set α) = ↑(S.filter (· ∈ s)) := by
    ext x; simp [and_comm]
  rw [this, ← sum_measure_singleton, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ s <;> simp [hx]

theorem upper_int {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (θ : Measure (Fin n → ℝ)) (hθ : θ ∈ frechetClass μ)
    (xstar : (Fin n → ℝ) → (Fin n → ℝ)) (hxm : Measurable xstar)
    (hxmem : ∀ c, xstar c ∈ 𝒳) (hxopt : ∀ c, ∀ x ∈ 𝒳, ∑ i, c i * x i ≤ ∑ i, c i * xstar c i) :
    (fun x : 𝒳 => (θ.map xstar {(x : Fin n → ℝ)}).toReal) ∈ stdSimplex ℝ 𝒳 ∧
      (∀ i, θ.map (fun c => (c i, xstar c i)) ∈
        couplings (μ i) (margMeasure 𝒳 (fun x : 𝒳 => (θ.map xstar {(x : Fin n → ℝ)}).toReal) i)) ∧
      ∫ c, Z 𝒳 h𝒳 c ∂θ = ∑ i, ∫ p, p.1 * p.2 ∂(θ.map (fun c => (c i, xstar c i))) := by
  classical
  obtain ⟨hθP, hθm⟩ := hθ
  set m := θ.map xstar with hm
  have : IsProbabilityMeasure m := Measure.isProbabilityMeasure_map hxm.aemeasurable
  have hcompl : m (↑𝒳)ᶜ = 0 := by
    rw [hm, Measure.map_apply hxm (Finset.measurableSet _).compl]
    have : xstar ⁻¹' (↑𝒳 : Set (Fin n → ℝ))ᶜ = ∅ := by
      ext c; simp [hxmem c]
    rw [this, measure_empty]
  have hdecomp := mdro_eq_sum_dirac m 𝒳 hcompl
  have hsum : ∑ x ∈ 𝒳, m {x} = 1 := by
    rw [sum_measure_singleton, ← Set.univ_inter (↑𝒳 : Set (Fin n → ℝ)),
      measure_inter_conull hcompl]
    simp
  have hfin : ∀ x, m {x} ≠ ⊤ := fun x => measure_ne_top m _
  refine ⟨⟨fun x => ENNReal.toReal_nonneg, ?_⟩, ?_, ?_⟩
  · rw [Finset.sum_coe_sort 𝒳 (fun x => (m {x}).toReal), ← ENNReal.toReal_sum (fun x _ => hfin x),
      hsum, ENNReal.toReal_one]
  · intro i
    have hf : Measurable (fun c : Fin n → ℝ => (c i, xstar c i)) :=
      (measurable_pi_apply i).prodMk ((measurable_pi_apply i).comp hxm)
    refine ⟨Measure.isProbabilityMeasure_map hf.aemeasurable, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hf]
      exact hθm i
    · rw [Measure.map_map measurable_snd hf]
      have : (Prod.snd ∘ fun c : Fin n → ℝ => (c i, xstar c i)) = (fun y => y i) ∘ xstar := rfl
      rw [this, ← Measure.map_map (measurable_pi_apply i) hxm, ← hm]
      ext s hs
      rw [Measure.map_apply (measurable_pi_apply i) hs, hdecomp, Measure.finsetSum_apply,
        margMeasure, Measure.finsetSum_apply]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_toReal (hfin _)]
      rw [← Finset.sum_coe_sort 𝒳]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Measure.dirac_apply' _ ((measurable_pi_apply i) hs), Measure.dirac_apply' _ hs]
      simp [Set.indicator_apply]
  · have hZ : ∀ c, Z 𝒳 h𝒳 c = ∑ i, c i * xstar c i := fun c =>
      le_antisymm (Finset.sup'_le _ _ (hxopt c)) (Finset.le_sup' (fun x => ∑ i, c i * x i) (hxmem c))
    have hint : ∀ i, Integrable (fun c : Fin n → ℝ => c i * xstar c i) θ := by
      intro i
      have hμi : Integrable id (μ i) := hint i
      rw [← hθm i] at hμi
      have hci : Integrable (fun c : Fin n → ℝ => c i) θ :=
        (integrable_map_measure aestronglyMeasurable_id
          (measurable_pi_apply i).aemeasurable).mp hμi
      refine hci.mul_bdd (c := ∑ x ∈ 𝒳, |x i|)
        ((measurable_pi_apply i).comp hxm).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
      intro c
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun x : Fin n → ℝ => |x i|) (fun x _ => abs_nonneg _)
        (hxmem c)
    simp_rw [hZ]
    rw [integral_finset_sum _ (fun i _ => hint i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hf : Measurable (fun c : Fin n → ℝ => (c i, xstar c i)) :=
      (measurable_pi_apply i).prodMk ((measurable_pi_apply i).comp hxm)
    rw [integral_map (f := fun p : ℝ × ℝ => p.1 * p.2) hf.aemeasurable
      (continuous_fst.mul continuous_snd).aestronglyMeasurable]

namespace MDROaux

variable {n : ℕ}

lemma proj_mem {𝒳 : Finset (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ 𝒳) (i : Fin n) :
    x i ∈ proj 𝒳 i := Finset.mem_image_of_mem _ hx

lemma mem_proj {𝒳 : Finset (Fin n → ℝ)} {i : Fin n} {a : ℝ} (ha : a ∈ proj 𝒳 i) :
    ∃ x ∈ 𝒳, x i = a := by simpa [proj] using ha

lemma sup'_le_sup'_add {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f g : ι → ℝ) (d : ℝ)
    (h : ∀ i ∈ s, f i ≤ g i + d) : s.sup' hs f ≤ s.sup' hs g + d :=
  Finset.sup'_le _ _ fun i hi => (h i hi).trans (by linarith [Finset.le_sup' g hi])

lemma sup'_sub_const {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (k : ℝ) :
    s.sup' hs (fun i => f i - k) = s.sup' hs f - k := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i hi => by linarith [Finset.le_sup' f hi]
  · have := sup'_le_sup'_add hs f (fun i => f i - k) k (fun i _ => by simp)
    linarith

lemma proj_nonempty {𝒳 : Finset (Fin n → ℝ)} (h𝒳 : 𝒳.Nonempty) (i : Fin n) :
    (proj 𝒳 i).Nonempty := h𝒳.image _

lemma conj_def (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) (c : ℝ) :
    conj 𝒳 h𝒳 ψi i c = (proj 𝒳 i).sup' (proj_nonempty h𝒳 i) (fun a => c * a - ψi a) := rfl

lemma conj_eq_fun (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) :
    conj 𝒳 h𝒳 ψi i = (proj 𝒳 i).sup' (proj_nonempty h𝒳 i) (fun a (c : ℝ) => c * a - ψi a) := by
  funext c; rw [Finset.sup'_apply]; rfl

lemma conj_measurable (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) :
    Measurable (conj 𝒳 h𝒳 ψi i) := by
  rw [conj_eq_fun]
  exact Finset.measurable_sup' _ fun a _ => by fun_prop

lemma conj_abs_le (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n) (c : ℝ) :
    |conj 𝒳 h𝒳 ψi i c| ≤ |c| * (∑ a ∈ proj 𝒳 i, |a|) + ∑ a ∈ proj 𝒳 i, |ψi a| := by
  obtain ⟨a, ha, hca⟩ := Finset.exists_mem_eq_sup' (proj_nonempty h𝒳 i)
    (fun a => c * a - ψi a)
  rw [conj_def, hca]
  have h1 : |a| ≤ ∑ a ∈ proj 𝒳 i, |a| :=
    Finset.single_le_sum (f := fun a : ℝ => |a|) (fun _ _ => abs_nonneg _) ha
  have h2 : |ψi a| ≤ ∑ a ∈ proj 𝒳 i, |ψi a| :=
    Finset.single_le_sum (f := fun a : ℝ => |ψi a|) (fun _ _ => abs_nonneg _) ha
  calc |c * a - ψi a| ≤ |c * a| + |ψi a| := abs_sub _ _
    _ = |c| * |a| + |ψi a| := by rw [abs_mul]
    _ ≤ _ := by gcongr

lemma conj_integrable (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψi : ℝ → ℝ) (i : Fin n)
    (m : Measure ℝ) [IsFiniteMeasure m] (hm : Integrable id m) :
    Integrable (conj 𝒳 h𝒳 ψi i) m := by
  refine Integrable.mono' (g := fun c => |c| * (∑ a ∈ proj 𝒳 i, |a|) + ∑ a ∈ proj 𝒳 i, |ψi a|)
    ((hm.abs.mul_const _).add (integrable_const _))
    (conj_measurable 𝒳 h𝒳 ψi i).aestronglyMeasurable (Filter.Eventually.of_forall fun c => ?_)
  rw [Real.norm_eq_abs]; exact conj_abs_le 𝒳 h𝒳 ψi i c

lemma conj_le_add (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ ψ' : ℝ → ℝ) (i : Fin n) (d : ℝ)
    (h : ∀ a ∈ proj 𝒳 i, ψ' a ≤ ψ a + d) (c : ℝ) :
    conj 𝒳 h𝒳 ψ i c ≤ conj 𝒳 h𝒳 ψ' i c + d :=
  sup'_le_sup'_add _ _ _ _ fun a ha => by linarith [h a ha]

lemma conj_congr (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ ψ' : ℝ → ℝ) (i : Fin n)
    (h : ∀ a ∈ proj 𝒳 i, ψ a = ψ' a) : conj 𝒳 h𝒳 ψ i = conj 𝒳 h𝒳 ψ' i := by
  funext c
  apply le_antisymm
  · simpa using conj_le_add 𝒳 h𝒳 ψ ψ' i 0 (fun a ha => by rw [h a ha]; simp) c
  · simpa using conj_le_add 𝒳 h𝒳 ψ' ψ i 0 (fun a ha => by rw [h a ha]; simp) c

lemma conj_sub_const (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ : ℝ → ℝ) (i : Fin n) (k : ℝ)
    (c : ℝ) : conj 𝒳 h𝒳 (fun a => ψ a - k) i c = conj 𝒳 h𝒳 ψ i c + k := by
  have := sup'_sub_const (proj_nonempty h𝒳 i) (fun a => c * a - ψ a) (-k)
  simp only [sub_neg_eq_add] at this
  rw [conj_def, conj_def, show (fun a => c * a - (ψ a - k)) = (fun a => c * a - ψ a + k) by funext a; ring, this]

/-- The dual objective `sup_ν L(ψ, ν)`. -/
noncomputable def D (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) : ℝ :=
  𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) + ∑ i, ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i)

lemma lagrangian_eq (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (ν : 𝒳 → ℝ) :
    lagrangian μ 𝒳 h𝒳 ψ ν = ∑ x : 𝒳, ν x * ∑ i, ψ i ((x : Fin n → ℝ) i) +
      ∑ i, ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i) := by
  simp only [lagrangian, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma isGreatest_D (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) :
    IsGreatest ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) (D μ 𝒳 h𝒳 ψ) := by
  classical
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_mem_eq_sup' h𝒳 (fun x => ∑ i, ψ i (x i))
  constructor
  · refine ⟨Pi.single ⟨x0, hx0⟩ 1, single_mem_stdSimplex ℝ _, ?_⟩
    simp only [lagrangian_eq, D, hmax]
    congr 1
    rw [Finset.sum_eq_single ⟨x0, hx0⟩]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rintro _ ⟨ν, hν, rfl⟩
    simp only [lagrangian_eq, D]
    gcongr
    calc ∑ x : 𝒳, ν x * ∑ i, ψ i ((x : Fin n → ℝ) i)
        ≤ ∑ x : 𝒳, ν x * 𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun x : Fin n → ℝ => ∑ i, ψ i (x i)) x.2) (hν.1 x)
      _ = _ := by rw [← Finset.sum_mul, hν.2, one_mul]

lemma D_congr (μ : Fin n → Measure ℝ) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ ψ' : Fin n → ℝ → ℝ) (h : ∀ i, ∀ a ∈ proj 𝒳 i, ψ i a = ψ' i a) :
    D μ 𝒳 h𝒳 ψ = D μ 𝒳 h𝒳 ψ' := by
  simp only [D]
  congr 1
  · exact Finset.sup'_congr _ rfl fun x hx =>
      Finset.sum_congr rfl fun i _ => h i (x i) (proj_mem hx i)
  · exact Finset.sum_congr rfl fun i _ => by rw [conj_congr 𝒳 h𝒳 (ψ i) (ψ' i) i (h i)]

lemma D_shift (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (k : Fin n → ℝ) :
    D μ 𝒳 h𝒳 (fun i a => ψ i a - k i) = D μ 𝒳 h𝒳 ψ := by
  simp only [D]
  have h1 : 𝒳.sup' h𝒳 (fun x => ∑ i, (ψ i (x i) - k i)) =
      𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) - ∑ i, k i := by
    rw [← sup'_sub_const]
    exact Finset.sup'_congr _ rfl fun x _ => Finset.sum_sub_distrib _ _
  have h2 : ∀ i, ∫ c, conj 𝒳 h𝒳 (fun a => ψ i a - k i) i c ∂(μ i) =
      ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i) + k i := by
    intro i
    simp_rw [conj_sub_const]
    rw [integral_add (conj_integrable 𝒳 h𝒳 _ i _ (hint i)) (integrable_const _),
      integral_const]
    simp
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib]
  ring

lemma D_lower (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (hnn : ∀ i, ∀ a ∈ proj 𝒳 i, 0 ≤ ψ i a)
    (hz : ∀ i, ∃ a ∈ proj 𝒳 i, ψ i a = 0) (i0 : Fin n) (a : ℝ) (ha : a ∈ proj 𝒳 i0) :
    ψ i0 a ≤ D μ 𝒳 h𝒳 ψ + ∑ i, (∫ c, |c| ∂(μ i)) * ∑ b ∈ proj 𝒳 i, |b| := by
  obtain ⟨x, hx, rfl⟩ := mem_proj ha
  have h1 : ψ i0 (x i0) ≤ 𝒳.sup' h𝒳 (fun x => ∑ i, ψ i (x i)) :=
    (Finset.single_le_sum (f := fun i => ψ i (x i)) (fun i _ => hnn i _ (proj_mem hx i))
      (Finset.mem_univ i0)).trans (Finset.le_sup' (fun x : Fin n → ℝ => ∑ i, ψ i (x i)) hx)
  have h2 : ∀ i, -((∫ c, |c| ∂(μ i)) * ∑ b ∈ proj 𝒳 i, |b|) ≤
      ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i) := by
    intro i
    obtain ⟨a0, ha0, hz0⟩ := hz i
    rw [← neg_mul, ← integral_neg, ← integral_mul_const]
    refine integral_mono ((hint i).abs.neg.mul_const _) (conj_integrable 𝒳 h𝒳 _ i _ (hint i))
      fun c => ?_
    have h3 : c * a0 - ψ i a0 ≤ conj 𝒳 h𝒳 (ψ i) i c := by
      rw [conj_def]; exact Finset.le_sup' (fun a => c * a - ψ i a) ha0
    have h4 : |a0| ≤ ∑ b ∈ proj 𝒳 i, |b| :=
      Finset.single_le_sum (f := fun b : ℝ => |b|) (fun _ _ => abs_nonneg _) ha0
    have h5 : -(|c| * |a0|) ≤ c * a0 := by rw [← abs_mul]; exact neg_abs_le _
    have h6 : |c| * |a0| ≤ |c| * ∑ b ∈ proj 𝒳 i, |b| := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    simp only [Pi.neg_apply, id]
    rw [hz0] at h3
    linarith
  have h7 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
  simp only [Finset.sum_neg_distrib] at h7
  simp only [D]
  linarith

lemma conj_convex (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) (ψ₁ ψ₂ : ℝ → ℝ) (i : Fin n)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) (c : ℝ) :
    conj 𝒳 h𝒳 (fun a => t * ψ₁ a + s * ψ₂ a) i c ≤
      t * conj 𝒳 h𝒳 ψ₁ i c + s * conj 𝒳 h𝒳 ψ₂ i c := by
  rw [conj_def]
  refine Finset.sup'_le _ _ fun a ha => ?_
  have h1 : c * a - ψ₁ a ≤ conj 𝒳 h𝒳 ψ₁ i c := by
    rw [conj_def]; exact Finset.le_sup' (fun a => c * a - ψ₁ a) ha
  have h2 : c * a - ψ₂ a ≤ conj 𝒳 h𝒳 ψ₂ i c := by
    rw [conj_def]; exact Finset.le_sup' (fun a => c * a - ψ₂ a) ha
  have e : c * a - (t * ψ₁ a + s * ψ₂ a) = t * (c * a - ψ₁ a) + s * (c * a - ψ₂ a) := by
    have : c * a = (t + s) * (c * a) := by rw [hts, one_mul]
    linarith [this]
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ht) (mul_le_mul_of_nonneg_left h2 hs)

end MDROaux

open MDROaux in
theorem dual_int {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ ψstar : Fin n → ℝ → ℝ, ∃ s : ℝ,
      IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψstar ν) '' stdSimplex ℝ 𝒳) s ∧
      ∀ (ψ : Fin n → ℝ → ℝ) (s' : ℝ),
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s' → s ≤ s' := by
  classical
  -- finite-dimensional parametrisation of the relevant values of ψ
  let ext : ((i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ) → Fin n → ℝ → ℝ :=
    fun φ i a => if h : a ∈ proj 𝒳 i then φ ⟨i, a, h⟩ else 0
  have hext : ∀ φ i a (h : a ∈ proj 𝒳 i), ext φ i a = φ ⟨i, a, h⟩ := fun φ i a h => dif_pos h
  let f : ((i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ) → ℝ := fun φ => D μ 𝒳 h𝒳 (ext φ)
  have hlip : ∀ φ φ', f φ ≤ f φ' + (2 * n) * dist φ φ' := by
    intro φ φ'
    have hd : ∀ i, ∀ a ∈ proj 𝒳 i, |ext φ i a - ext φ' i a| ≤ dist φ φ' := by
      intro i a ha
      rw [hext φ i a ha, hext φ' i a ha, ← Real.dist_eq]
      exact dist_le_pi_dist φ φ' _
    have h1 : 𝒳.sup' h𝒳 (fun x => ∑ i, ext φ i (x i)) ≤
        𝒳.sup' h𝒳 (fun x => ∑ i, ext φ' i (x i)) + n * dist φ φ' := by
      refine sup'_le_sup'_add _ _ _ _ fun x hx => ?_
      have : ∑ i, ext φ i (x i) ≤ ∑ i, (ext φ' i (x i) + dist φ φ') :=
        Finset.sum_le_sum fun i _ => by
          linarith [(abs_le.mp (hd i (x i) (proj_mem hx i))).2]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      exact this
    have h2 : ∀ i, ∫ c, conj 𝒳 h𝒳 (ext φ i) i c ∂(μ i) ≤
        ∫ c, conj 𝒳 h𝒳 (ext φ' i) i c ∂(μ i) + dist φ φ' := by
      intro i
      have hI := conj_integrable 𝒳 h𝒳 (ext φ i) i _ (hint i)
      have hI' := conj_integrable 𝒳 h𝒳 (ext φ' i) i _ (hint i)
      calc ∫ c, conj 𝒳 h𝒳 (ext φ i) i c ∂(μ i)
          ≤ ∫ c, (conj 𝒳 h𝒳 (ext φ' i) i c + dist φ φ') ∂(μ i) :=
            integral_mono hI (hI'.add (integrable_const (dist φ φ')))
              (conj_le_add 𝒳 h𝒳 (ext φ i) (ext φ' i) i (dist φ φ') (fun a ha => by
                linarith [(abs_le.mp (hd i a ha)).1]))
        _ = ∫ c, conj 𝒳 h𝒳 (ext φ' i) i c ∂(μ i) + dist φ φ' := by
            rw [integral_add hI' (integrable_const _), integral_const]; simp
    have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h3
    simp only [f, D]
    nlinarith
  have hfc : Continuous f := (LipschitzWith.of_le_add_mul' (2 * n) hlip).continuous
  set C : ℝ := ∑ i, (∫ c, |c| ∂(μ i)) * ∑ b ∈ proj 𝒳 i, |b| with hC
  set R : ℝ := max 0 (f 0 + C) with hR
  have h0K : (0 : (i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ) ∈ Set.Icc 0 (fun _ => R) :=
    ⟨le_rfl, fun _ => le_max_left _ _⟩
  obtain ⟨φs, hφsK, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨_, h0K⟩ hfc.continuousOn
  refine ⟨ext φs, D μ 𝒳 h𝒳 (ext φs), (isGreatest_D μ 𝒳 h𝒳 _).isLUB, fun ψ s' hs' => ?_⟩
  rw [hs'.unique (isGreatest_D μ 𝒳 h𝒳 ψ).isLUB]
  -- normalise ψ
  set k : Fin n → ℝ := fun i => (proj 𝒳 i).inf' (proj_nonempty h𝒳 i) (ψ i) with hk
  set ψt : Fin n → ℝ → ℝ := fun i a => ψ i a - k i with hψt
  have hDt : D μ 𝒳 h𝒳 ψt = D μ 𝒳 h𝒳 ψ := D_shift μ hint 𝒳 h𝒳 ψ k
  have hnn : ∀ i, ∀ a ∈ proj 𝒳 i, 0 ≤ ψt i a := fun i a ha => by
    simp only [ψt, k]; linarith [Finset.inf'_le (ψ i) ha]
  have hz : ∀ i, ∃ a ∈ proj 𝒳 i, ψt i a = 0 := fun i => by
    obtain ⟨a, ha, h⟩ := Finset.exists_mem_eq_inf' (proj_nonempty h𝒳 i) (ψ i)
    exact ⟨a, ha, by simp only [ψt, k]; rw [h]; ring⟩
  rw [← hDt]
  by_cases hbox : ∀ i, ∀ a ∈ proj 𝒳 i, ψt i a ≤ R
  · let φ : (i : Fin n) × {a // a ∈ proj 𝒳 i} → ℝ := fun e => ψt e.1 e.2.1
    have hφK : φ ∈ Set.Icc 0 (fun _ => R) :=
      ⟨fun e => hnn e.1 e.2.1 e.2.2, fun e => hbox e.1 e.2.1 e.2.2⟩
    have : f φ = D μ 𝒳 h𝒳 ψt := D_congr μ 𝒳 h𝒳 _ _ fun i a ha => hext φ i a ha
    rw [← this]
    exact hmin hφK
  · simp only [not_forall, not_le] at hbox
    obtain ⟨i, a, ha, hlt⟩ := hbox
    have h1 := D_lower μ hint 𝒳 h𝒳 ψt hnn hz i a ha
    have h2 : f φs ≤ f 0 := hmin h0K
    have h3 : f 0 + C ≤ R := le_max_right _ _
    show f φs ≤ _
    linarith

open MDROaux in
theorem minimax_int {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳,
        IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s} v ∧
      IsGLB {s | ∃ ψ : Fin n → ℝ → ℝ,
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s} v := by
  classical
  obtain ⟨ψs, s, hsLUB, hsmin⟩ := dual_int μ hint 𝒳 h𝒳
  have hs : s = D μ 𝒳 h𝒳 ψs := hsLUB.unique (isGreatest_D μ 𝒳 h𝒳 ψs).isLUB
  have hαle : ∀ ψ, s ≤ D μ 𝒳 h𝒳 ψ := fun ψ => hsmin ψ _ (isGreatest_D μ 𝒳 h𝒳 ψ).isLUB
  -- values at the vertices
  let g : (Fin n → ℝ → ℝ) → 𝒳 → ℝ := fun ψ x =>
    ∑ i, ψ i ((x : Fin n → ℝ) i) + ∑ i, ∫ c, conj 𝒳 h𝒳 (ψ i) i c ∂(μ i)
  have hLg : ∀ ψ, ∀ ν ∈ stdSimplex ℝ 𝒳, lagrangian μ 𝒳 h𝒳 ψ ν = ∑ x, ν x * g ψ x := by
    intro ψ ν hν
    rw [lagrangian_eq]
    simp only [g, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hν.2, one_mul]
  have hgD : ∀ ψ, ∀ x : 𝒳, g ψ x ≤ D μ 𝒳 h𝒳 ψ := fun ψ x => by
    simp only [g, D]
    gcongr
    exact Finset.le_sup' (fun x : Fin n → ℝ => ∑ i, ψ i (x i)) x.2
  have hDg : ∀ ψ, ∃ x : 𝒳, D μ 𝒳 h𝒳 ψ = g ψ x := fun ψ => by
    obtain ⟨x, hx, h⟩ := Finset.exists_mem_eq_sup' h𝒳 (fun x : Fin n → ℝ => ∑ i, ψ i (x i))
    exact ⟨⟨x, hx⟩, by simp only [D, g, h]⟩
  -- the open convex set
  let U : Set (𝒳 → ℝ) := {y | ∃ ψ, ∀ x, g ψ x < y x}
  have hUopen : IsOpen U := by
    have : U = ⋃ ψ, Set.pi Set.univ (fun x => Set.Ioi (g ψ x)) := by
      ext y; simp [U]
    rw [this]
    exact isOpen_iUnion fun ψ => isOpen_set_pi Set.finite_univ fun x _ => isOpen_Ioi
  have hUconv : Convex ℝ U := by
    rintro y₁ ⟨ψ₁, h₁⟩ y₂ ⟨ψ₂, h₂⟩ t u ht hu htu
    refine ⟨fun i a => t * ψ₁ i a + u * ψ₂ i a, fun x => ?_⟩
    have hI : ∀ i, ∫ c, conj 𝒳 h𝒳 (fun a => t * ψ₁ i a + u * ψ₂ i a) i c ∂(μ i) ≤
        t * ∫ c, conj 𝒳 h𝒳 (ψ₁ i) i c ∂(μ i) + u * ∫ c, conj 𝒳 h𝒳 (ψ₂ i) i c ∂(μ i) := by
      intro i
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul t)
        ((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul u)]
      exact integral_mono (conj_integrable 𝒳 h𝒳 _ i _ (hint i))
        (((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul t).add
          ((conj_integrable 𝒳 h𝒳 _ i _ (hint i)).const_mul u))
        (fun c => conj_convex 𝒳 h𝒳 (ψ₁ i) (ψ₂ i) i t u ht hu htu c)
    have hle : g (fun i a => t * ψ₁ i a + u * ψ₂ i a) x ≤ t * g ψ₁ x + u * g ψ₂ x := by
      simp only [g]
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hI i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
      have e : ∑ i, (t * ψ₁ i ((x : Fin n → ℝ) i) + u * ψ₂ i ((x : Fin n → ℝ) i)) =
          t * ∑ i, ψ₁ i ((x : Fin n → ℝ) i) + u * ∑ i, ψ₂ i ((x : Fin n → ℝ) i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [e]; nlinarith
    have hlt : t * g ψ₁ x + u * g ψ₂ x < t * y₁ x + u * y₂ x := by
      rcases ht.lt_or_eq with ht' | ht'
      · nlinarith [h₁ x, h₂ x]
      · subst ht'
        have : u = 1 := by linarith
        subst this
        simpa using h₂ x
    calc _ ≤ _ := hle
      _ < _ := hlt
      _ = (t • y₁ + u • y₂) x := by simp
  have hpU : (fun _ => s) ∉ U := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨x, hx⟩ := hDg ψ
    have := hαle ψ
    have := hψ x
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hUconv hUopen hpU
  set w : 𝒳 → ℝ := fun x => f (Pi.single x 1) with hw
  have hfw : ∀ y : 𝒳 → ℝ, f y = ∑ x, y x * w x := by
    intro y
    have : y = ∑ x, y x • (Pi.single x 1 : 𝒳 → ℝ) := by
      ext z; simp [Pi.single_apply]
    conv_lhs => rw [this]
    rw [map_sum]
    simp [w]
  have hgU : ∀ ψ, ∀ ε > 0, (fun x => g ψ x + ε) ∈ U := fun ψ ε hε =>
    ⟨ψ, fun x => by simp only; linarith⟩
  -- the normal vector is nonpositive
  have hw0 : ∀ x, w x ≤ 0 := by
    intro x0
    by_contra hpos
    have hpos : 0 < w x0 := lt_of_not_ge hpos
    set y0 : 𝒳 → ℝ := fun x => g ψs x + 1
    set T : ℝ := (f (fun _ => s) - f y0) / w x0 + 1
    have hT : 0 ≤ T := by
      have := hf y0 (hgU ψs 1 one_pos)
      have : 0 ≤ (f (fun _ => s) - f y0) / w x0 := div_nonneg (by linarith) hpos.le
      linarith
    have hmem : y0 + T • (Pi.single x0 1 : 𝒳 → ℝ) ∈ U := by
      refine ⟨ψs, fun x => ?_⟩
      have h1 : 0 ≤ (T • (Pi.single x0 1 : 𝒳 → ℝ)) x := by
        by_cases hx : x = x0
        · subst hx; simp [hT]
        · simp [hx]
      simp only [Pi.add_apply, y0] at h1 ⊢
      linarith
    have := hf _ hmem
    rw [map_add, map_smul, smul_eq_mul] at this
    have e : T * f (Pi.single x0 1) = T * w x0 := rfl
    rw [e] at this
    have : T * w x0 = (f (fun _ => s) - f y0) + w x0 := by
      simp only [T]; field_simp
    linarith
  set W : ℝ := ∑ x, -w x with hW
  have hWpos : 0 < W := by
    rcases (Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) => neg_nonneg.mpr (hw0 x)).lt_or_eq
      with h | h
    · exact h
    · exfalso
      have hz : ∀ x, w x = 0 := by
        intro x
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun x (_ : x ∈ Finset.univ) => neg_nonneg.mpr (hw0 x))).mp h.symm x (Finset.mem_univ x)
        linarith
      have := hf _ (hgU ψs 1 one_pos)
      rw [hfw, hfw] at this
      simp [hz] at this
  set ν : 𝒳 → ℝ := fun x => -w x / W with hν
  have hνΔ : ν ∈ stdSimplex ℝ 𝒳 := by
    refine ⟨fun x => div_nonneg (neg_nonneg.mpr (hw0 x)) hWpos.le, ?_⟩
    simp only [ν, ← Finset.sum_div]
    exact div_self hWpos.ne'
  -- every ψ gives L(ψ, ν) ≥ s
  have hLν : ∀ ψ, s ≤ lagrangian μ 𝒳 h𝒳 ψ ν := by
    intro ψ
    rw [hLg ψ ν hνΔ]
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h1 := hf _ (hgU ψ ε hε)
    rw [hfw, hfw] at h1
    have h2 : ∑ x, (g ψ x + ε) * w x = -W * (∑ x, ν x * g ψ x + ε) := by
      have hνw : ∀ x, -W * ν x = w x := by
        intro x; simp only [ν]; field_simp
      rw [mul_add, Finset.mul_sum]
      simp_rw [← mul_assoc, hνw]
      rw [hW, Finset.sum_neg_distrib, neg_neg, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have h3 : ∑ x, s * w x = -W * s := by
      rw [← Finset.mul_sum, hW, Finset.sum_neg_distrib]; ring
    rw [h2, h3] at h1
    nlinarith
  have hLs : lagrangian μ 𝒳 h𝒳 ψs ν ≤ s := by
    rw [hs]; exact (isGreatest_D μ 𝒳 h𝒳 ψs).2 ⟨ν, hνΔ, rfl⟩
  have hglb : IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s := by
    refine ⟨?_, fun b hb => ?_⟩
    · rintro _ ⟨ψ, rfl⟩; exact hLν ψ
    · exact (hb ⟨ψs, rfl⟩).trans hLs
  refine ⟨s, ⟨⟨ν, hνΔ, hglb⟩, ?_⟩, ⟨?_, fun b hb => hb ⟨ψs, hsLUB⟩⟩⟩
  · rintro _ ⟨ν', hν', h'⟩
    refine (h'.1 ⟨ψs, rfl⟩).trans ?_
    rw [hs]; exact (isGreatest_D μ 𝒳 h𝒳 ψs).2 ⟨ν', hν', rfl⟩
  · rintro _ ⟨ψ, h⟩
    rw [h.unique (isGreatest_D μ 𝒳 h𝒳 ψ).isLUB]
    exact hαle ψ

namespace MDROq

lemma qf_eq (m π : Measure ℝ) [IsProbabilityMeasure m] [IsProbabilityMeasure π]
    (hm : Integrable id m) (A : Finset ℝ) (hπA : π (↑A)ᶜ = 0) :
    ∫ p, p.1 * p.2 ∂(γQ m π) =
      ∑ a ∈ A, a * ∫ t in (π (Iio a)).toReal..(π (Iic a)).toReal, quantile m t := by
  classical
  set vol' := volume.restrict (Ioo (0 : ℝ) 1) with hvol'
  set lo : ℝ → ℝ := fun a => (π (Iio a)).toReal with hlo
  set hi : ℝ → ℝ := fun a => (π (Iic a)).toReal with hhi
  have hlo0 : ∀ a, 0 ≤ lo a := fun a => ENNReal.toReal_nonneg
  have hhi1 : ∀ a, hi a ≤ 1 := fun a => by
    simp only [hi]; rw [← measureReal_def]; exact measureReal_le_one
  have hhicdf : ∀ a, hi a = cdf π a := fun a => by
    simp only [hi]; rw [cdf_eq_real, measureReal_def]
  have hdiff : ∀ a, hi a - lo a = π.real {a} := fun a => by
    have hd : Disjoint (Iio a) {a} := by simp
    have := measureReal_union (μ := π) hd (measurableSet_singleton a)
    rw [Iio_union_right] at this
    simp only [hi, lo, ← measureReal_def]
    linarith
  have hlohi : ∀ a, lo a ≤ hi a := fun a => by
    have := hdiff a; have : 0 ≤ π.real {a} := measureReal_nonneg; linarith
  have hsub : ∀ a, Ioo (lo a) (hi a) ⊆ quantile π ⁻¹' {a} ∩ Ioo 0 1 := by
    intro a t ht
    have ht0 : 0 < t := lt_of_le_of_lt (hlo0 a) ht.1
    have ht1 : t < 1 := lt_of_lt_of_le ht.2 (hhi1 a)
    refine ⟨?_, ht0, ht1⟩
    simp only [mem_preimage, mem_singleton_iff]
    apply le_antisymm
    · exact quantile_le_of_lt π ht0 (by rw [← hhicdf]; exact ht.2)
    · by_contra hlt
      have hlt : quantile π t < a := not_le.mp hlt
      have h1 := le_cdf_of_quantile_le π ht1 (le_refl (quantile π t))
      rw [cdf_eq_real] at h1
      have h2 : π.real (Iic (quantile π t)) ≤ π.real (Iio a) :=
        measureReal_mono (Iic_subset_Iio.mpr hlt)
      have h3 : lo a = π.real (Iio a) := by simp only [lo, measureReal_def]
      linarith [ht.1]
  have hnull : ∀ a, vol' (quantile π ⁻¹' {a} \ Ioo (lo a) (hi a)) = 0 := by
    intro a
    have h1 : vol' (quantile π ⁻¹' {a}) = π {a} := by
      rw [← Measure.map_apply_of_aemeasurable (quantile_aemeasurable π)
        (measurableSet_singleton a), map_quantile]
    have h2 : vol' (Ioo (lo a) (hi a)) = π {a} := by
      rw [hvol', Measure.restrict_apply measurableSet_Ioo,
        inter_eq_left.mpr (fun t ht => (hsub a ht).2), Real.volume_Ioo, hdiff,
        ofReal_measureReal]
    rw [measure_sdiff (fun t ht => (hsub a ht).1) measurableSet_Ioo.nullMeasurableSet
      (by rw [h2]; exact measure_ne_top _ _), h1, h2, tsub_self]
  have aeA : ∀ᵐ t ∂vol', quantile π t ∈ A := by
    refine ae_of_ae_map (quantile_aemeasurable π) ?_
    rw [map_quantile, ae_iff]; exact hπA
  have hae : ∀ᵐ t ∂vol', quantile m t * quantile π t =
      ∑ a ∈ A, a * (Ioo (lo a) (hi a)).indicator (quantile m) t := by
    have hall : ∀ᵐ t ∂vol', ∀ a ∈ A, t ∉ quantile π ⁻¹' {a} \ Ioo (lo a) (hi a) :=
      (eventually_all_finset A).mpr fun a _ => (measure_eq_zero_iff_ae_notMem.mp (hnull a))
    filter_upwards [aeA, hall] with t ht1 ht2
    rw [Finset.sum_eq_single (quantile π t)]
    · have : t ∈ Ioo (lo (quantile π t)) (hi (quantile π t)) := by
        by_contra h; exact ht2 _ ht1 ⟨rfl, h⟩
      rw [indicator_of_mem this]; ring
    · intro a _ hab
      rw [indicator_of_notMem, mul_zero]
      intro h
      exact hab (((hsub a h).1 : quantile π t = a)).symm
    · intro h; exact absurd ht1 h
  have hQm : Integrable (quantile m) vol' :=
    (integrable_map_measure aestronglyMeasurable_id (quantile_aemeasurable m)).mp
      (by rw [map_quantile]; exact hm)
  have hpair : AEMeasurable (fun t => (quantile m t, quantile π t)) vol' :=
    (quantile_aemeasurable m).prodMk (quantile_aemeasurable π)
  rw [γQ, integral_map (f := fun p : ℝ × ℝ => p.1 * p.2) hpair
    (continuous_fst.mul continuous_snd).aestronglyMeasurable, integral_congr_ae hae,
    integral_finset_sum _ (fun a _ => (hQm.indicator measurableSet_Ioo).const_mul a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, integral_indicator measurableSet_Ioo, hvol',
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (fun t ht => (hsub a ht).2),
    intervalIntegral.integral_of_le (hlohi a), integral_Ioc_eq_integral_Ioo]

end MDROq

open MDROq MDROaux in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ θ ∈ frechetClass μ, s = ∫ c, Z 𝒳 h𝒳 c ∂θ} v ∧
      (∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i, ∃ m : ℝ,
        IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m) ∧
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳, ∃ γ : Fin n → Measure (ℝ × ℝ),
        (∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) ∧ s = ∑ i, ∫ p, p.1 * p.2 ∂(γ i)} v ∧
      IsGreatest ((fun ν => quantileForm μ 𝒳 ν) '' stdSimplex ℝ 𝒳) v ∧
      (∀ νrel ∈ stdSimplex ℝ 𝒳, quantileForm μ 𝒳 νrel = v →
        ∃ θ ∈ frechetClass μ, ∫ c, Z 𝒳 h𝒳 c ∂θ = v) := by
  classical
  obtain ⟨v, hv4, -⟩ := minimax_int μ hint 𝒳 h𝒳
  -- the projected laws
  have hπP : ∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i, IsProbabilityMeasure (margMeasure 𝒳 ν i) := by
    intro ν hν i
    constructor
    rw [margMeasure, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hν.1 x), hν.2, ENNReal.ofReal_one]
  have hπA : ∀ ν : 𝒳 → ℝ, ∀ i, margMeasure 𝒳 ν i (↑(proj 𝒳 i))ᶜ = 0 := by
    intro ν i
    rw [margMeasure, Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (Finset.measurableSet _).compl]
    have : ((x : Fin n → ℝ) i) ∈ proj 𝒳 i := Finset.mem_image_of_mem _ x.2
    simp [this]
  set cv : (𝒳 → ℝ) → Fin n → ℝ := fun ν i =>
    ∫ p, p.1 * p.2 ∂(γQ (μ i) (margMeasure 𝒳 ν i)) with hcv
  have hK : ∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i,
      IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} (cv ν i) ∧
      IsGLB (Set.range fun ψ : ℝ → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i)) (cv ν i) := by
    intro ν hν i
    have := hπP ν hν i
    have hG : IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i),
        s = ∫ p, p.1 * p.2 ∂γ} (cv ν i) := by
      refine ⟨⟨_, γQ_mem _ _, rfl⟩, ?_⟩
      rintro _ ⟨γ, hγ, rfl⟩
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨ψ, hψ⟩ := dual_approx (μ i) _ (hint i) (proj 𝒳 i) (h𝒳.image _) (hπA ν i) ε hε
      have := weak_duality (μ i) _ (hint i) (proj 𝒳 i) (h𝒳.image _) (hπA ν i) γ hγ ψ
      linarith
    obtain ⟨m, h1, _, h3⟩ := kant_int μ hint 𝒳 h𝒳 ν hν i
    rw [hG.unique h1]
    exact ⟨h1, h3⟩
  have hqf : ∀ ν ∈ stdSimplex ℝ 𝒳, quantileForm μ 𝒳 ν = ∑ i, cv ν i := by
    intro ν hν
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hπP ν hν i
    rw [hcv]
    exact (qf_eq (μ i) _ (hint i) (proj 𝒳 i) (hπA ν i)).symm
  -- the Lagrangian infimum is the sum of coupling values
  have hL : ∀ ν ∈ stdSimplex ℝ 𝒳,
      IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) (∑ i, cv ν i) := by
    intro ν hν
    set f : Fin n → (ℝ → ℝ) → ℝ := fun i ψ =>
      ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) with hf
    have hLf : ∀ ψ : Fin n → ℝ → ℝ, lagrangian μ 𝒳 h𝒳 ψ ν = ∑ i, f i (ψ i) := fun ψ => rfl
    constructor
    · rintro _ ⟨ψ, rfl⟩
      simp only [hLf]
      exact Finset.sum_le_sum fun i _ => (hK ν hν i).2.1 ⟨ψ i, rfl⟩
    · intro b hb
      by_contra hcon'
      have hcon : ∑ i, cv ν i < b := not_le.mp hcon'
      set ε := (b - ∑ i, cv ν i) / (n + 1) with hε
      have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
      have hex : ∀ i, ∃ ψi : ℝ → ℝ, f i ψi < cv ν i + ε := by
        intro i
        obtain ⟨_, ⟨ψi, rfl⟩, h⟩ :=
          ((hK ν hν i).2).exists_between (by linarith : cv ν i < cv ν i + ε)
        exact ⟨ψi, h.2⟩
      choose ψ hψ using hex
      have h1 := hb ⟨ψ, rfl⟩
      simp only [hLf] at h1
      have h2 : ∑ i, f i (ψ i) ≤ ∑ i, (cv ν i + ε) := Finset.sum_le_sum fun i _ => (hψ i).le
      have h2' : ∑ i, (cv ν i + ε) = ∑ i, cv ν i + n * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have h3 : (n : ℝ) * ε < b - ∑ i, cv ν i := by
        rw [hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  obtain ⟨⟨ν0, hν0, hν0glb⟩, hvub⟩ := hv4
  have hv0 : ∑ i, cv ν0 i = v := (hL ν0 hν0).unique hν0glb
  have hle : ∀ ν ∈ stdSimplex ℝ 𝒳, ∑ i, cv ν i ≤ v := fun ν hν => hvub ⟨ν, hν, hL ν hν⟩
  have h3 : IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳, ∃ γ : Fin n → Measure (ℝ × ℝ),
      (∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) ∧ s = ∑ i, ∫ p, p.1 * p.2 ∂(γ i)} v := by
    constructor
    · have hex : ∀ i, ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν0 i),
          cv ν0 i = ∫ p, p.1 * p.2 ∂γ := fun i => (hK ν0 hν0 i).1.1
      choose γ hγ hγv using hex
      exact ⟨ν0, hν0, γ, hγ, by rw [← hv0]; exact Finset.sum_congr rfl fun i _ => hγv i⟩
    · rintro _ ⟨ν, hν, γ, hγ, rfl⟩
      exact le_trans (Finset.sum_le_sum fun i _ => (hK ν hν i).1.2 ⟨γ i, hγ i, rfl⟩) (hle ν hν)
  have hub1 : ∀ θ ∈ frechetClass μ, ∫ c, Z 𝒳 h𝒳 c ∂θ ≤ v := by
    intro θ hθ
    obtain ⟨xs, hxm, hxs⟩ := sec_3_1_measurable_selection 𝒳 h𝒳
    obtain ⟨hνs, hγs, heq⟩ := upper_int μ hint 𝒳 h𝒳 θ hθ xs hxm (fun c => (hxs c).1)
      (fun c => (hxs c).2)
    rw [heq]
    exact h3.2 ⟨_, hνs, _, hγs, rfl⟩
  -- attaining θ from any optimal ν
  have hθ : ∀ ν ∈ stdSimplex ℝ 𝒳, ∑ i, cv ν i = v →
      ∃ θ ∈ frechetClass μ, ∫ c, Z 𝒳 h𝒳 c ∂θ = v := by
    intro ν hν hνv
    have hex : ∀ i, ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i),
        cv ν i = ∫ p, p.1 * p.2 ∂γ := fun i => (hK ν hν i).1.1
    choose γ hγ hγv using hex
    obtain ⟨θ, hθ, hθle⟩ := lower_int μ hint 𝒳 h𝒳 ν hν γ hγ
    refine ⟨θ, hθ, le_antisymm (hub1 θ hθ) ?_⟩
    rw [← hνv, Finset.sum_congr rfl fun i _ => hγv i]
    exact hθle
  refine ⟨v, ⟨?_, ?_⟩, fun ν hν i => ⟨_, (hK ν hν i).1⟩, h3, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨θ, hθm, hθv⟩ := hθ ν0 hν0 hv0
    exact ⟨θ, hθm, hθv.symm⟩
  · rintro _ ⟨θ, hθ, rfl⟩; exact hub1 θ hθ
  · exact ⟨ν0, hν0, by show quantileForm μ 𝒳 ν0 = v; rw [hqf ν0 hν0, hv0]⟩
  · rintro _ ⟨ν, hν, rfl⟩
    show quantileForm μ 𝒳 ν ≤ v
    rw [hqf ν hν]; exact hle ν hν
  · intro νrel hν hq
    exact hθ νrel hν (by rw [← hqf νrel hν]; exact hq)
