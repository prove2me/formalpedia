-- Prove2me | solution 1 for MarginalDRO.Lagrange.proof_thm2_kantorovich
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:16:31.733579+00:00
-- url     : https://prove2.me/submissions/77b31ee5-686f-4b3d-873b-17444344197e

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

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
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ν : 𝒳 → ℝ) (hν : ν ∈ stdSimplex ℝ 𝒳) (i : Fin n) :
    ∃ m : ℝ,
      IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m ∧
      IsGLB {s | ∃ φ ψ : ℝ → ℝ, Integrable φ (μ i) ∧
        (∀ c : ℝ, ∀ a ∈ proj 𝒳 i, c * a ≤ φ c + ψ a) ∧
        s = ∫ c, φ c ∂(μ i) + ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i)} m ∧
      IsGLB (Set.range fun ψ : ℝ → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i)) m := by
  classical
  have hμ : Integrable id (μ i) := (hvar i).integrable (by norm_num)
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
