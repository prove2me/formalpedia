-- Prove2me | solution 1 for MasulloRH.hilbert_kernel_weighted_skew_rectangle_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:55:04.329169+00:00
-- url     : https://prove2.me/submissions/df8cf09f-a924-4a01-b146-a524d0895d12

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem eventually_translate_subset (hU : IsDPrimeSequence μ U C) (x : G) {V : Set G}
    (hV : V ∈ 𝓝 x) : ∀ᶠ k : ℕ in atTop, x • U k ⊆ V := by
  obtain ⟨m,hm⟩ := hU.2 ((fun u => x*u) ⁻¹' V)
    ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV))
  filter_upwards [eventually_ge_atTop m] with k hk
  rintro y ⟨u,hu,rfl⟩
  exact hm ((antitone_nat_of_succ_le hU.1.antitone) hk hu)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private noncomputable def vectorAverage (μ : Measure G) (U : ℕ → Set G) (f : G → E) (k : ℕ) (x : G) : E :=
  ((μ (U k)).toReal)⁻¹ • ∫ y in x • U k, f y ∂μ

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
private theorem continuous_tendsto_vectorAverage (hU : IsDPrimeSequence μ U C)
    {g : G → E} (hg : Continuous g) (hgi : Integrable g μ) (x : G) :
    Tendsto (fun k => vectorAverage μ U g k x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf := half_pos hε
  have hnear := hg.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (g x) hhalf)
  filter_upwards [eventually_translate_subset hU x hnear] with k hk
  let s := x • U k
  have hμs : μ s = μ (U k) := measure_smul μ x _
  have hfin : μ s < ⊤ := hμs ▸ hU.1.measure_lt_top k
  have hv : 0 < (μ (U k)).toReal := ENNReal.toReal_pos (hU.1.measure_pos k).ne' (hU.1.measure_lt_top k).ne
  have eq : vectorAverage μ U g k x - g x = ((μ (U k)).toReal)⁻¹ • ∫ y in s, g y - g x ∂μ := by
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

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace E] in
private theorem vectorAverage_error (hU : IsDPrimeSequence μ U C) {f g : G → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (x : G) (k : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hh : ∫⁻ y in x • U k, ‖f y - g y‖ₑ ∂μ ≤ ENNReal.ofReal δ * μ (U k)) :
    dist (vectorAverage μ U f k x) (vectorAverage μ U g k x) ≤ δ := by
  have mf := hU.1.measure_lt_top k
  have hv : 0 < (μ (U k)).toReal := ENNReal.toReal_pos (hU.1.measure_pos k).ne' mf.ne
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top mf.ne) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hδ] at ht
  have hin := (norm_integral_le_lintegral_norm (μ := μ.restrict (x • U k)) (fun y => f y-g y))
  simp only [ofReal_norm] at hin
  rw [dist_eq_norm,vectorAverage,vectorAverage,← smul_sub,← integral_sub hf.integrableOn hg.integrableOn,
    norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]
  calc _ ≤ ((μ (U k)).toReal)⁻¹ * (δ * (μ (U k)).toReal) :=
       mul_le_mul_of_nonneg_left (hin.trans ht) (inv_nonneg.mpr hv.le)
       _ = δ := by field_simp

private theorem ae_global_vectorAverage (hU : IsDPrimeSequence μ U C) {f : G → E}
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun k => vectorAverage μ U f k x) atTop (𝓝 (f x)) := by
  have hdel (δ : ℝ) (hδ : 0 < δ) :
      ∀ᵐ x ∂μ, ∀ᶠ k in atTop, dist (vectorAverage μ U f k x) (f x) < 4*δ := by
    let a := ENNReal.ofReal δ
    let c := ENNReal.ofReal C
    have ha : a ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
    let D := {x | ¬ ∀ᶠ k in atTop, dist (vectorAverage μ U f k x) (f x) < 4*δ}
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
      have hg := (Metric.tendsto_nhds.mp (continuous_tendsto_vectorAverage hU hgc hgi x) δ hδ)
      filter_upwards [hg] with k hk
      have herr := vectorAverage_error hU hf hgi x k δ hδ.le
        (le_of_not_gt (fun hh => hnA ⟨k,hh⟩))
      have he : dist (f x) (g x) < δ := by
        simpa only [dist_eq_norm] using (ENNReal.ofReal_lt_ofReal_iff hδ).mp
          (by simpa [e,a] using hnB)
      linarith [dist_triangle (vectorAverage μ U f k x) (vectorAverage μ U g k x) (f x),
        dist_triangle (vectorAverage μ U g k x) (g x) (f x),dist_comm (f x) (g x)]
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
      dist (vectorAverage μ U f k x) (f x) < 4*(1/((n:ℝ)+1)) :=
    ae_all_iff.mpr (fun n => hdel _ (by positivity))
  filter_upwards [hAll] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < ε/4 by positivity)
  filter_upwards [hx n] with k hk
  linarith
end

open MasulloGRH in
private theorem vector_differentiation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (f : G → E) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun k : ℕ => vectorAverage μ U f k x) Filter.atTop (nhds (f x)) := by
  classical
  let K := CompactExhaustion.choice G
  let g (n : ℕ) := (K n).indicator f
  have hgi (n : ℕ) : Integrable (g n) μ :=
    (integrable_indicator_iff (K.isCompact n).measurableSet).mpr (hf.integrableOn_isCompact (K.isCompact n))
  have hall : ∀ᵐ x ∂μ, ∀ n, Tendsto (fun k => vectorAverage μ U (g n) k x) atTop (𝓝 (g n x)) :=
    ae_all_iff.mpr (fun n => ae_global_vectorAverage hU (hgi n))
  filter_upwards [hall] with x hx
  obtain ⟨n,hn⟩ := K.exists_mem_nhds x
  have hxe : g n x = f x := Set.indicator_of_mem (mem_of_mem_nhds hn) _
  rw [← hxe]
  apply (hx n).congr'
  filter_upwards [eventually_translate_subset hU x hn] with k hk
  unfold vectorAverage
  congr 1
  apply setIntegral_congr_fun₀ ((hU.1.nullMeasurable k).smul x)
  intro y hy
  exact Set.indicator_of_mem (hk hy) _

open MasulloGRH ComplexConjugate in
private theorem pairing_rectangle
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (a b : G → E) (ha : LocallyIntegrable a μ) (hb : LocallyIntegrable b μ)
    (K : G × G → ℂ) (hK : K =ᵐ[μ.prod μ] (fun z => inner ℂ (a z.1) (b z.2)))
    {J : Type*} [Countable J] (σ : J → G → G) (hσ : ∀ j, Measure.QuasiMeasurePreserving (σ j) μ μ) :
    ∀ᵐ x ∂μ, ∀ j, Tendsto
      (fun kl : ℕ × ℕ => (((μ (U kl.1)).toReal)⁻¹ * ((μ (U kl.2)).toReal)⁻¹) •
        ∫ z in (x • U kl.1) ×ˢ ((σ j x) • U kl.2), K z ∂μ.prod μ)
      atTop (𝓝 (inner ℂ (a x) (b (σ j x)))) := by
  have hda := vector_differentiation μ U C hU a ha
  have hdb := vector_differentiation μ U C hU b hb
  have hdb' : ∀ᵐ x ∂μ, ∀ j, Tendsto (fun k => vectorAverage μ U b k (σ j x)) atTop
      (𝓝 (b (σ j x))) := ae_all_iff.mpr (fun j => (hσ j).tendsto_ae hdb)
  filter_upwards [hda,hdb'] with x hax hbx
  intro j
  have hav : ∀ᶠ k in atTop, IntegrableOn a (x • U k) μ := by
    obtain ⟨s,hs,his⟩ := ha x
    exact (eventually_translate_subset hU x hs).mono (fun k hk => his.mono_set hk)
  have hbv : ∀ᶠ k in atTop, IntegrableOn b ((σ j x) • U k) μ := by
    obtain ⟨s,hs,his⟩ := hb (σ j x)
    exact (eventually_translate_subset hU (σ j x) hs).mono (fun k hk => his.mono_set hk)
  have hfst : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop (n,n)).mono fun _ h => h.1
  have hsnd : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop (n,n)).mono fun _ h => h.2
  have hav' : ∀ᶠ kl : ℕ × ℕ in atTop, IntegrableOn a (x • U kl.1) μ := hfst hav
  have hbv' : ∀ᶠ kl : ℕ × ℕ in atTop, IntegrableOn b (σ j x • U kl.2) μ := hsnd hbv
  apply ((hax.comp hfst).inner (𝕜 := ℂ) ((hbx j).comp hsnd)).congr'
  filter_upwards [hav',hbv'] with kl hi hj
  let A := x • U kl.1
  let B := σ j x • U kl.2
  change IntegrableOn a A μ at hi
  change IntegrableOn b B μ at hj
  let Q := fun z : G × G => inner ℂ (a z.1) (b z.2)
  have hiQ : IntegrableOn Q (A ×ˢ B) (μ.prod μ) := by
    rw [IntegrableOn,← Measure.prod_restrict]
    exact Integrable.op_fst_snd (op := inner ℂ)
      (continuous_fst.inner continuous_snd) ⟨1,fun v w => by simpa using norm_inner_le_norm (𝕜 := ℂ) v w⟩ hi hj
  have hprod : (∫ z in A ×ˢ B, K z ∂μ.prod μ) =
      inner ℂ (∫ u in A, a u ∂μ) (∫ v in B, b v ∂μ) := by
    calc
      _ = ∫ z in A ×ˢ B, Q z ∂μ.prod μ := integral_congr_ae (hK.filter_mono ae_restrict_le)
      _ = ∫ u in A, ∫ v in B, inner ℂ (a u) (b v) ∂μ ∂μ := setIntegral_prod _ hiQ
      _ = ∫ u in A, inner ℂ (a u) (∫ v in B, b v ∂μ) ∂μ := integral_congr_ae (ae_of_all _ (fun u => integral_inner (𝕜 := ℂ) hj (a u)))
      _ = inner ℂ (∫ u in A, a u ∂μ) (∫ v in B, b v ∂μ) := by
        rw [← inner_conj_symm]
        conv_lhs => enter [2,u]; rw [← inner_conj_symm]
        rw [integral_conj,integral_inner hi]
  change inner ℂ (vectorAverage μ U a kl.1 x) (vectorAverage μ U b kl.2 (σ j x)) =
    _ • (∫ z in A ×ˢ B, K z ∂μ.prod μ)
  rw [hprod]
  simp only [vectorAverage,inner_smul_left_eq_smul,inner_smul_right_eq_smul,smul_smul,A,B]
  rw [mul_comm]

open MasulloGRH in
private theorem rectangle_bounds
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (a b : G → E) (ha : LocallyIntegrable a μ) (hb : LocallyIntegrable b μ)
    (K : G × G → ℂ) (hK : K =ᵐ[μ.prod μ] (fun z => inner ℂ (a z.1) (b z.2)))
    {J : Type*} [Countable J] (σ : J → G → G) (hσ : ∀ j, Measure.QuasiMeasurePreserving (σ j) μ μ) :
    ∀ᵐ x ∂μ, ∀ j, (Tendsto
      (fun kl : ℕ × ℕ => (((μ (U kl.1)).toReal)⁻¹ * ((μ (U kl.2)).toReal)⁻¹) •
        ∫ z in (x • U kl.1) ×ˢ ((σ j x) • U kl.2), K z ∂μ.prod μ)
      atTop (𝓝 (inner ℂ (a x) (b (σ j x))))) ∧
      ∀ᶠ kl : ℕ × ℕ in atTop, (((μ (U kl.1)).toReal)⁻¹ * ((μ (U kl.2)).toReal)⁻¹) *
        (∫ z in (x • U kl.1) ×ˢ ((σ j x) • U kl.2), ‖K z‖ ∂μ.prod μ)
          < ‖a x‖ * ‖b (σ j x)‖ + 1 := by

  have hmain := pairing_rectangle μ U C hU a b ha hb K hK σ hσ
  have hna := vector_differentiation μ U C hU (fun y => ‖a y‖)
    (locallyIntegrableOn_univ.mp (ha.locallyIntegrableOn univ).norm)
  have hnb := vector_differentiation μ U C hU (fun y => ‖b y‖)
    (locallyIntegrableOn_univ.mp (hb.locallyIntegrableOn univ).norm)
  have hnb' : ∀ᵐ x ∂μ, ∀ j, Tendsto (fun k => vectorAverage μ U (fun y => ‖b y‖) k (σ j x)) atTop
      (𝓝 ‖b (σ j x)‖) := ae_all_iff.mpr (fun j => (hσ j).tendsto_ae hnb)
  filter_upwards [hmain,hna,hnb'] with x hmx hax hbx
  intro j
  refine ⟨hmx j, ?_⟩
  have hfst : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop (n,n)).mono fun _ h => h.1
  have hsnd : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop (n,n)).mono fun _ h => h.2
  have hav : ∀ᶠ k in atTop, IntegrableOn a (x • U k) μ := by
    obtain ⟨s,hs,his⟩ := ha x
    exact (eventually_translate_subset hU x hs).mono (fun k hk => his.mono_set hk)
  have hbv : ∀ᶠ k in atTop, IntegrableOn b ((σ j x) • U k) μ := by
    obtain ⟨s,hs,his⟩ := hb (σ j x)
    exact (eventually_translate_subset hU (σ j x) hs).mono (fun k hk => his.mono_set hk)
  have hav' : ∀ᶠ kl : ℕ × ℕ in atTop, IntegrableOn a (x • U kl.1) μ := hfst hav
  have hbv' : ∀ᶠ kl : ℕ × ℕ in atTop, IntegrableOn b (σ j x • U kl.2) μ := hsnd hbv
  have hlim := (hax.comp hfst).mul ((hbx j).comp hsnd)
  have hlt := hlim.eventually_lt_const (show ‖a x‖ * ‖b (σ j x)‖ < ‖a x‖ * ‖b (σ j x)‖ + 1 by linarith)
  filter_upwards [hav',hbv',hlt] with kl hi hj ht
  let A := x • U kl.1
  let B := σ j x • U kl.2
  change IntegrableOn a A μ at hi
  change IntegrableOn b B μ at hj
  have hJ : IntegrableOn (fun z : G × G => ‖a z.1‖*‖b z.2‖) (A ×ˢ B) (μ.prod μ) := by
    rw [IntegrableOn,← Measure.prod_restrict]
    exact hi.norm.mul_prod hj.norm
  have hi' : (∫ z in A ×ˢ B, ‖K z‖ ∂μ.prod μ) ≤
      (∫ u in A, ‖a u‖ ∂μ) * (∫ v in B, ‖b v‖ ∂μ) := by
    rw [← setIntegral_prod_mul (fun y => ‖a y‖) (fun y => ‖b y‖)]
    apply integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hJ
    filter_upwards [hK.filter_mono ae_restrict_le] with z hz
    rw [hz]
    exact norm_inner_le_norm (𝕜 := ℂ) _ _
  have hpos : 0 ≤ ((μ (U kl.1)).toReal)⁻¹ * ((μ (U kl.2)).toReal)⁻¹ := by positivity
  have hx := mul_le_mul_of_nonneg_left hi' hpos
  apply lt_of_le_of_lt hx
  convert ht using 1
  simp [vectorAverage,A,B,smul_eq_mul]
  ring

open MasulloGRH in
theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (a b : G → E) (ha : LocallyIntegrable a μ) (hb : LocallyIntegrable b μ)
    (K : G × G → ℂ) (hK : K =ᵐ[μ.prod μ] (fun z => inner ℂ (a z.1) (b z.2)))
    {J : Type*} [Countable J] (σ : J → G → G) (hσ : ∀ j, Measure.QuasiMeasurePreserving (σ j) μ μ) :
    ∀ᵐ x ∂μ, ∀ j, ∀ (q : G × G → ℂ), Continuous q → Tendsto
      (fun kl : ℕ × ℕ => (((μ (U kl.1)).toReal)⁻¹ * ((μ (U kl.2)).toReal)⁻¹) •
        ∫ z in (x • U kl.1) ×ˢ ((σ j x) • U kl.2), q z * K z ∂μ.prod μ)
      atTop (𝓝 (q (x, σ j x) * inner ℂ (a x) (b (σ j x)))) := by
  filter_upwards [rectangle_bounds μ U C hU a b ha hb K hK σ hσ] with x hx
  intro j q hq
  rcases hx j with ⟨hL,habs⟩
  let y := σ j x
  let q₀ := q (x,y)
  let c := fun i : ℕ × ℕ => ((μ (U i.1)).toReal)⁻¹ * ((μ (U i.2)).toReal)⁻¹
  let R := fun i : ℕ × ℕ => (x • U i.1) ×ˢ (y • U i.2)
  let e := fun z => (q z - q₀) * K z
  have hfst : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop (n,n)).mono fun _ h => h.1
  have hsnd : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) atTop :=
    tendsto_atTop.mpr fun n => (eventually_ge_atTop (n,n)).mono fun _ h => h.2
  have shrink {V : Set (G × G)} (hV : V ∈ 𝓝 (x,y)) :
      ∀ᶠ i in (atTop : Filter (ℕ × ℕ)), R i ⊆ V := by
    obtain ⟨Vx,hVx,Vy,hVy,hVV⟩ := mem_nhds_prod_iff.mp hV
    have h₁ : ∀ᶠ i : ℕ × ℕ in atTop, x • U i.1 ⊆ Vx := hfst (eventually_translate_subset hU x hVx)
    have h₂ : ∀ᶠ i : ℕ × ℕ in atTop, y • U i.2 ⊆ Vy := hsnd (eventually_translate_subset hU y hVy)
    filter_upwards [h₁,h₂] with i hx hy
    exact (Set.prod_mono hx hy).trans hVV
  have good (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ i in (atTop : Filter (ℕ × ℕ)), ∀ᵐ z ∂(μ.prod μ).restrict (R i), ‖q z - q₀‖ ≤ δ := by
    have hc : (q ⁻¹' Metric.ball q₀ δ) ∈ 𝓝 (x,y) :=
      hq.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hδ)
    filter_upwards [shrink hc] with i hi
    have hm : NullMeasurableSet (R i) (μ.prod μ) :=
      ((hU.1.nullMeasurable i.1).smul x).prod ((hU.1.nullMeasurable i.2).smul y)
    filter_upwards [ae_restrict_mem₀ hm] with z hz
    simpa [Metric.mem_ball,dist_eq_norm] using (show dist (q z) q₀ ≤ δ from (hi hz).le)
  have hKi : ∀ᶠ i : ℕ × ℕ in atTop, IntegrableOn K (R i) (μ.prod μ) := by
    obtain ⟨u,hu,hi⟩ := ha x
    obtain ⟨v,hv,hj⟩ := hb y
    have h₁ : ∀ᶠ i : ℕ × ℕ in atTop, x • U i.1 ⊆ u := hfst (eventually_translate_subset hU x hu)
    have h₂ : ∀ᶠ i : ℕ × ℕ in atTop, y • U i.2 ⊆ v := hsnd (eventually_translate_subset hU y hv)
    filter_upwards [h₁,h₂] with i hu hv
    apply ((integrable_congr (hK.filter_mono ae_restrict_le)).mpr)
    change IntegrableOn _ ((x • U i.1) ×ˢ (y • U i.2)) (μ.prod μ)
    rw [IntegrableOn,← Measure.prod_restrict]
    exact Integrable.op_fst_snd (op := inner ℂ)
      (continuous_fst.inner continuous_snd) ⟨1,fun v w => by simpa using norm_inner_le_norm (𝕜 := ℂ) v w⟩
      (hi.mono_set hu) (hj.mono_set hv)
  have hsm : ∀ i, AEStronglyMeasurable (fun z => q z - q₀) ((μ.prod μ).restrict (R i)) :=
    fun _ => (hq.sub continuous_const).aestronglyMeasurable
  have hE : Tendsto (fun i => c i • ∫ z in R i, e z ∂μ.prod μ) atTop (𝓝 (0:ℂ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let M := ‖a x‖ * ‖b y‖ + 1
    have hM : 0 < M := by dsimp [M]; positivity
    let δ := ε/M
    have hδ : 0 < δ := div_pos hε hM
    filter_upwards [good δ hδ,hKi,habs] with i hg hi hbound
    have hei : IntegrableOn e (R i) (μ.prod μ) := hi.bdd_mul (hsm i) hg
    have hc : 0 ≤ c i := by dsimp [c]; positivity
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
    have cmp : (∫ z in R i, ‖e z‖ ∂μ.prod μ) ≤ δ * ∫ z in R i, ‖K z‖ ∂μ.prod μ := by
      rw [← integral_const_mul]
      apply integral_mono_ae hei.norm (hi.norm.const_mul _)
      filter_upwards [hg] with z hz
      simpa [e,norm_mul] using mul_le_mul_of_nonneg_right hz (norm_nonneg (K z))
    calc
      _ ≤ c i * (∫ z in R i, ‖e z‖ ∂μ.prod μ) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc
      _ ≤ c i * (δ * ∫ z in R i, ‖K z‖ ∂μ.prod μ) := mul_le_mul_of_nonneg_left cmp hc
      _ = δ * (c i * ∫ z in R i, ‖K z‖ ∂μ.prod μ) := by ring
      _ < δ * M := mul_lt_mul_of_pos_left hbound hδ
      _ = ε := div_mul_cancel₀ _ hM.ne'
  have hh := (hL.const_mul q₀).add hE
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [hKi,good 1 one_pos] with i hi hg
  have hei : IntegrableOn e (R i) (μ.prod μ) := hi.bdd_mul (hsm i) hg
  change q₀ * (c i • ∫ z in R i, K z ∂μ.prod μ) + (c i • ∫ z in R i, e z ∂μ.prod μ) =
    c i • ∫ z in R i, q z * K z ∂μ.prod μ
  rw [mul_smul_comm, ← smul_add, ← integral_const_mul, ← integral_add (hi.const_mul _) hei]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by dsimp [e]; ring)
