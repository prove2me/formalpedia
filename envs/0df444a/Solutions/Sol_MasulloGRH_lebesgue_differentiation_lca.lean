-- Prove2me | solution 1 for MasulloGRH.lebesgue_differentiation_lca
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:42:55.446445+00:00
-- url     : https://prove2.me/submissions/37c86801-f7d5-4240-a3ac-d6e84101427a

import Mathlib.Topology.Metrizable.Urysohn
import Definitions.Def_MasulloGRH_DSequences
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set MeasureTheory Filter
open scoped Pointwise ENNReal

private theorem scale_index {k j : ℕ} (h : (1/3 : ℝ)^k ≤ 2 * (1/3 : ℝ)^j) : j ≤ k := by
  by_contra! hkj
  have hsmall := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (1/3:ℝ) ≤ 1) (show k+1 ≤ j by omega)
  rw [pow_succ] at hsmall
  linarith [pow_pos (by norm_num : (0:ℝ) < 1/3) k]

private theorem weak_cover {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ≥0∞)
    (hmem : ∀ k, (1:G) ∈ U k) (hm : ∀ k, NullMeasurableSet (U k) μ)
    (hpos : ∀ k, 0 < μ (U k)) (hanti : Antitone U)
    (hd : ∀ k, μ (U k * (U k)⁻¹) ≤ C * μ (U k))
    (f : G → ℝ≥0∞) (a : ℝ≥0∞) :
    a * μ {x : G | ∃ k, a * μ (U k) < ∫⁻ y in x • U k, f y ∂μ} ≤ C * ∫⁻ y, f y ∂μ := by
  classical
  let ν := μ.withDensity f
  let B (i : G × ℕ) : Set G := i.1 • U i.2
  let E (i : G × ℕ) : Set G := i.1 • (U i.2 * (U i.2)⁻¹)
  let t := {i : G × ℕ | a * μ (U i.2) < ν (B i)}
  have hb (i : G × ℕ) : NullMeasurableSet (B i) μ := (hm _).smul _
  have hν (i : G × ℕ) : ν (B i) = ∫⁻ y in i.1 • U i.2, f y ∂μ :=
    withDensity_apply₀ _ (hb i)
  obtain ⟨s, hs, hdis, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement B t
    (fun i => (1/3 : ℝ)^i.2) 2 (by norm_num) (fun _ _ => by positivity) 1
    (fun i _ => pow_le_one₀ (by norm_num) (by norm_num))
    (fun i _ => ⟨_, Set.smul_mem_smul_set (hmem _)⟩)
  have hBs : Pairwise (fun i j : s => Disjoint (B i) (B j)) := hdis.subtype _
  have hc : Countable s := by
    have h := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ)
      (fun i : s => hb i) (fun _ _ h => (hBs h).aedisjoint)
    apply Set.countable_univ_iff.mp
    apply h.mono
    intro i _
    change 0 < μ (i.val.1 • U i.val.2)
    simpa only [measure_smul] using hpos i.val.2
  let := hc
  have hcover' : {x : G | ∃ k, a * μ (U k) < ∫⁻ y in x • U k, f y ∂μ} ⊆ ⋃ b : s, E ↑b := by
    rintro x ⟨k,hk⟩
    obtain ⟨b,hbs,⟨z,hz1,hz2⟩,hz⟩ := hcover (x,k) (by simpa [t,hν] using hk)
    refine Set.mem_iUnion.mpr ⟨⟨b,hbs⟩, ?_⟩
    obtain ⟨v,hv,hvx⟩ := hz1
    obtain ⟨w,hw,hwx⟩ := hz2
    change x * v = z at hvx
    change b.1 * w = z at hwx
    have hmem' : v ∈ U b.2 := hanti (scale_index hz) hv
    refine ⟨w * v⁻¹, Set.mul_mem_mul hw (Set.inv_mem_inv.mpr hmem'), ?_⟩
    change b.1 * (w * v⁻¹) = x
    rw [← mul_assoc, hwx, ← hvx, mul_inv_cancel_right]
  have hsum : ∑' b : s, ν (B b) ≤ ν Set.univ := by
    rw [← measure_iUnion₀ (fun _ _ hij => (hBs hij).aedisjoint)
      (fun b : s => (hb b).mono_ac (withDensity_absolutelyContinuous μ f))]
    exact measure_mono (Set.subset_univ _)
  have hE (b : s) : μ (E b) ≤ C * μ (U b.val.2) := by
    simpa only [E, measure_smul] using hd b.val.2
  calc
    _ ≤ a * ∑' b : s, μ (E b) :=
      mul_le_mul_of_nonneg_left ((measure_mono hcover').trans (measure_iUnion_le _)) zero_le
    _ ≤ a * ∑' b : s, C * μ (U b.val.2) :=
      mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hE) zero_le
    _ = C * ∑' b : s, a * μ (U b.val.2) := by
      simp only [ENNReal.tsum_mul_left]; ac_rfl
    _ ≤ C * ∑' b : s, ν (B b) := mul_le_mul_of_nonneg_left
      (ENNReal.tsum_le_tsum fun b => (hs b.property : a * μ (U b.val.2) < ν (B b)).le) zero_le
    _ ≤ C * ν Set.univ := mul_le_mul_of_nonneg_left hsum zero_le
    _ = _ := by simp [ν]

open MasulloGRH
open scoped Topology

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] {U : ℕ → Set G} {C : ℝ}

private theorem eventually_translate_subset (hU : IsDPrimeSequence μ U C) (x : G) {V : Set G}
    (hV : V ∈ 𝓝 x) : ∀ᶠ k : ℕ in atTop, x • U k ⊆ V := by
  obtain ⟨m,hm⟩ := hU.2 ((fun u => x*u) ⁻¹' V)
    ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV))
  filter_upwards [eventually_ge_atTop m] with k hk
  rintro y ⟨u,hu,rfl⟩
  exact hm ((antitone_nat_of_succ_le hU.1.antitone) hk hu)

private theorem continuous_tendsto_dAverage (hU : IsDPrimeSequence μ U C)
    {g : G → ℂ} (hg : Continuous g) (hgi : Integrable g μ) (x : G) :
    Tendsto (fun k => dAverage μ U g k x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf := half_pos hε
  have hnear := hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (g x) hhalf)
  filter_upwards [eventually_translate_subset hU x hnear] with k hk
  let s := x • U k
  have hμs : μ s = μ (U k) := measure_smul μ x _
  have hfin : μ s < ⊤ := hμs ▸ hU.1.measure_lt_top k
  have hv : 0 < (μ (U k)).toReal := ENNReal.toReal_pos (hU.1.measure_pos k).ne' (hU.1.measure_lt_top k).ne
  have eq : dAverage μ U g k x - g x = ((μ (U k)).toReal)⁻¹ • ∫ y in s, g y - g x ∂μ := by
    rw [integral_sub hgi.integrableOn (integrableOn_const hfin.ne),setIntegral_const, smul_sub,
      smul_smul, measureReal_def, hμs, inv_mul_cancel₀ hv.ne', one_smul]
    rfl
  have hb := norm_setIntegral_le_of_norm_le_const (f := fun y => g y - g x) hfin
    (fun y hy => (show ‖g y - g x‖ < ε/2 from (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hk hy)).le)
  rw [dist_eq_norm,eq,norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]
  rw [measureReal_def,hμs] at hb
  have hl : ((μ (U k)).toReal)⁻¹ * ‖∫ y in s, g y - g x ∂μ‖ ≤ ε/2 := by
    calc _ ≤ ((μ (U k)).toReal)⁻¹ * ((ε/2) * (μ (U k)).toReal) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hv.le)
         _ = ε/2 := by field_simp
  linarith

private theorem dAverage_error (hU : IsDPrimeSequence μ U C) {f g : G → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) (x : G) (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hh : ∫⁻ y in x • U k, ‖f y - g y‖ₑ ∂μ ≤ ENNReal.ofReal δ * μ (U k)) :
    dist (dAverage μ U f k x) (dAverage μ U g k x) ≤ δ := by
  have mf := hU.1.measure_lt_top k
  have hv : 0 < (μ (U k)).toReal := ENNReal.toReal_pos (hU.1.measure_pos k).ne' mf.ne
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top mf.ne) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hδ] at ht
  have hin := (norm_integral_le_lintegral_norm (μ := μ.restrict (x • U k)) (fun y => f y-g y))
  simp only [ofReal_norm] at hin
  rw [dist_eq_norm,dAverage,dAverage,← smul_sub,← integral_sub hf.integrableOn hg.integrableOn,
    norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]
  calc _ ≤ ((μ (U k)).toReal)⁻¹ * (δ * (μ (U k)).toReal) :=
       mul_le_mul_of_nonneg_left (hin.trans ht) (inv_nonneg.mpr hv.le)
       _ = δ := by field_simp

private theorem ae_global_dAverage (hU : IsDPrimeSequence μ U C) {f : G → ℂ}
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun k => dAverage μ U f k x) atTop (𝓝 (f x)) := by
  have hdel (δ : ℝ) (hδ : 0 < δ) :
      ∀ᵐ x ∂μ, ∀ᶠ k in atTop, dist (dAverage μ U f k x) (f x) < 4*δ := by
    let a := ENNReal.ofReal δ
    let c := ENNReal.ofReal C
    have ha : a ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
    let D := {x | ¬ ∀ᶠ k in atTop, dist (dAverage μ U f k x) (f x) < 4*δ}
    suffices a * μ D = 0 by
      exact ae_iff.mpr ((mul_eq_zero.mp this).resolve_left ha)
    apply le_antisymm _ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    let ε : ℝ≥0∞ := (η : ℝ≥0∞) / (c+1)
    have hc0 : c+1 ≠ 0 := by simp
    have hct : c+1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
    have hε : ε ≠ 0 := (ENNReal.div_pos (by exact_mod_cast hη.ne') hct).ne'
    obtain ⟨g,_,happ,hgc,hgi⟩ := hf.exists_hasCompactSupport_lintegral_sub_le hε
    let e : G → ℝ≥0∞ := fun y => ‖f y-g y‖ₑ
    let A := {x : G | ∃ k, a * μ (U k) < ∫⁻ y in x • U k, e y ∂μ}
    let B := {x : G | a ≤ e x}
    have hcover : D ⊆ A ∪ B := by
      intro x hx
      by_contra! hn
      have hnA : x ∉ A := fun hh => hn (Or.inl hh)
      have hnB : e x < a := lt_of_not_ge (fun hh => hn (Or.inr hh))
      apply hx
      have hg := (Metric.tendsto_nhds.mp (continuous_tendsto_dAverage hU hgc hgi x) δ hδ)
      filter_upwards [hg] with k hk
      have herr := dAverage_error hU hf hgi x k δ hδ.le
        (le_of_not_gt (fun hh => hnA ⟨k,hh⟩))
      have he : dist (f x) (g x) < δ := by
        simpa only [dist_eq_norm] using (ENNReal.ofReal_lt_ofReal_iff hδ).mp
          (by simpa [e,a] using hnB)
      linarith [dist_triangle (dAverage μ U f k x) (dAverage μ U g k x) (f x),
        dist_triangle (dAverage μ U g k x) (g x) (f x),dist_comm (f x) (g x)]
    have h1 : a * μ A ≤ c * ∫⁻ y, e y ∂μ :=
      weak_cover μ U c hU.1.one_mem hU.1.nullMeasurable hU.1.measure_pos
        (antitone_nat_of_succ_le hU.1.antitone) (fun k => (hU.1.doubling k).2.le) e a
    have h2 : a * μ B ≤ ∫⁻ y, e y ∂μ :=
      mul_meas_ge_le_lintegral₀ ((hf.sub hgi).aestronglyMeasurable.enorm) a
    calc a * μ D ≤ a * (μ A + μ B) :=
          mul_le_mul_of_nonneg_left ((measure_mono hcover).trans (measure_union_le A B)) zero_le
         _ ≤ (c+1) * (∫⁻ y, e y ∂μ) := by rw [mul_add,add_mul,one_mul]; exact add_le_add h1 h2
         _ ≤ (c+1) * ε := mul_le_mul_of_nonneg_left happ zero_le
         _ = _ := by simp only [ε, ENNReal.mul_div_cancel hc0 hct, zero_add]
  have hAll : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ᶠ k in atTop,
      dist (dAverage μ U f k x) (f x) < 4*(1/((n:ℝ)+1)) :=
    ae_all_iff.mpr (fun n => hdel _ (by positivity))
  filter_upwards [hAll] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < ε/4 by positivity)
  filter_upwards [hx n] with k hk
  linarith
end

open MasulloGRH in
theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (f : G → ℂ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun k : ℕ => dAverage μ U f k x) Filter.atTop (nhds (f x)) := by
  classical
  let K := CompactExhaustion.choice G
  let g (n : ℕ) := (K n).indicator f
  have hgi (n : ℕ) : Integrable (g n) μ :=
    (integrable_indicator_iff (K.isCompact n).measurableSet).mpr (hf.integrableOn_isCompact (K.isCompact n))
  have hall : ∀ᵐ x ∂μ, ∀ n, Tendsto (fun k => dAverage μ U (g n) k x) atTop (𝓝 (g n x)) :=
    ae_all_iff.mpr (fun n => ae_global_dAverage hU (hgi n))
  filter_upwards [hall] with x hx
  obtain ⟨n,hn⟩ := K.exists_mem_nhds x
  have hxe : g n x = f x := Set.indicator_of_mem (mem_of_mem_nhds hn) _
  rw [← hxe]
  apply (hx n).congr'
  filter_upwards [eventually_translate_subset hU x hn] with k hk
  unfold dAverage
  congr 1
  apply setIntegral_congr_fun₀ ((hU.1.nullMeasurable k).smul x)
  intro y hy
  exact Set.indicator_of_mem (hk hy) _
