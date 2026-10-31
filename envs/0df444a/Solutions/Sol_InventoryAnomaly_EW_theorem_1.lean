-- Prove2me | solution 1 for InventoryAnomaly.EW.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:25:40.726298+00:00
-- url     : https://prove2.me/submissions/dc4e7475-ae17-486f-9015-07312a69221b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model
import Theorems.Thm_InventoryAnomaly_EW_lemma_3
import Theorems.Thm_InventoryAnomaly_EW_step4_excess_cost

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat
open InventoryAnomaly.EW

open Classical in
lemma IA1_bind_mk_apply {α β : Type} (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    (p.bind fun x => (f x).map (Prod.mk x)) (a, b) = p a * f a b := by
  rw [PMF.bind_apply]
  have : ∀ x, ((f x).map (Prod.mk x)) (a, b) = if a = x then f a b else 0 := by
    intro x
    rw [PMF.map_apply]
    by_cases h : a = x
    · subst h
      rw [tsum_eq_single b]
      · simp
      · intro b' hb'; simp [Ne.symm hb']
    · simp [h]
  simp_rw [this, mul_ite, mul_zero]
  rw [tsum_eq_single a (fun x hx => by simp [Ne.symm hx])]; simp

lemma IA1_decouple {ι β : Type} [Fintype ι] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β]
    (ρ : Measure Bool) [IsProbabilityMeasure ρ] (ν : ι → Measure β)
    [∀ i, IsProbabilityMeasure (ν i)] (f : ι → β → ℝ) (hf0 : ∀ i y, 0 ≤ f i y)
    (hf1 : ∀ i y, f i y ≤ 1) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i, ∫ y, f i y ∂ν i ≤ B) :
    ∫ ω, (1 / ((Finset.univ.filter fun i => (ω i).1 = true).card : ℝ)) *
        ∑ i ∈ Finset.univ.filter (fun i => (ω i).1 = true), f i (ω i).2
      ∂(Measure.pi fun i => ρ.prod (ν i)) ≤ B := by
  classical
  set g : (ι → Bool) × (ι → β) → ℝ := fun p =>
    (1 / ((Finset.univ.filter fun i => p.1 i = true).card : ℝ)) *
      ∑ i ∈ Finset.univ.filter (fun i => p.1 i = true), f i (p.2 i) with hg
  have hmp := measurePreserving_arrowProdEquivProdArrow Bool β ι (fun _ => ρ) ν
  have hrw : ∀ ω : ι → Bool × β, (1 / ((Finset.univ.filter fun i => (ω i).1 = true).card : ℝ)) *
        ∑ i ∈ Finset.univ.filter (fun i => (ω i).1 = true), f i (ω i).2 =
      g (MeasurableEquiv.arrowProdEquivProdArrow Bool β ι ω) := fun ω => rfl
  simp_rw [hrw]
  rw [hmp.integral_comp' g]
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    simp only [hg]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hf0 _ _)
  have hg1 : ∀ p, g p ≤ 1 := fun p => by
    simp only [hg]
    set S := Finset.univ.filter fun i => p.1 i = true
    have : ∑ i ∈ S, f i (p.2 i) ≤ S.card := by
      calc ∑ i ∈ S, f i (p.2 i) ≤ ∑ i ∈ S, (1 : ℝ) := Finset.sum_le_sum fun i _ => hf1 _ _
        _ = S.card := by simp
    rcases Nat.eq_zero_or_pos S.card with h | h
    · simp [h]
    · rw [one_div, inv_mul_le_iff₀ (by exact_mod_cast h)]; linarith
  have hint : Integrable g ((Measure.pi fun _ : ι => ρ).prod (Measure.pi ν)) := by
    refine Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 p)]; exact hg1 p
  rw [integral_prod g hint]
  have hinner : ∀ o : ι → Bool, ∫ y, g (o, y) ∂(Measure.pi ν) ≤ B := by
    intro o
    set S := Finset.univ.filter fun i => o i = true
    simp only [hg]
    rw [integral_const_mul, integral_finset_sum]
    · have hS : ∀ i ∈ S, ∫ y : ι → β, f i (y i) ∂(Measure.pi ν) ≤ B := by
        intro i _
        rw [integral_comp_eval (Measurable.of_discrete).aestronglyMeasurable]
        exact hB i
      have hsum : ∑ i ∈ S, ∫ y : ι → β, f i (y i) ∂(Measure.pi ν) ≤ S.card * B := by
        calc _ ≤ ∑ i ∈ S, B := Finset.sum_le_sum hS
          _ = S.card * B := by simp
      rcases Nat.eq_zero_or_pos S.card with h | h
      · have hS0 : (Finset.univ.filter fun i => o i = true) = ∅ := Finset.card_eq_zero.mp h
        simp [hS0, hB0]
      · rw [one_div, inv_mul_le_iff₀ (by exact_mod_cast h)]; exact hsum
    · intro i _
      refine Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _ _)]; exact hf1 _ _
  calc ∫ o, ∫ y, g (o, y) ∂(Measure.pi ν) ∂(Measure.pi fun _ : ι => ρ)
      ≤ ∫ o, B ∂(Measure.pi fun _ : ι => ρ) :=
        integral_mono Integrable.of_finite (integrable_const B) hinner
    _ = B := by simp

lemma IA1_mix (p0 : ℝ≥0) (h : p0 ≤ 1) (src : Bool → PMF ℕ) :
    ((PMF.bernoulli p0 h).bind fun b => (src b).map (Prod.mk b)).toMeasure =
      (p0 : ENNReal) • ((src true).toMeasure.map (Prod.mk true)) +
        ((1 - p0 : ℝ≥0) : ENNReal) • ((src false).toMeasure.map (Prod.mk false)) := by
  rw [Measure.ext_iff_singleton]
  rintro ⟨b, k⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), IA1_bind_mk_apply,
    PMF.bernoulli_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_prodMk_left (measurableSet_singleton _),
    Measure.map_apply measurable_prodMk_left (measurableSet_singleton _)]
  cases b
  · have h1 : Prod.mk true ⁻¹' {((false, k) : Bool × ℕ)} = ∅ := by ext; simp
    have h2 : Prod.mk false ⁻¹' {((false, k) : Bool × ℕ)} = {k} := by ext; simp
    rw [h1, h2, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp
  · have h1 : Prod.mk true ⁻¹' {((true, k) : Bool × ℕ)} = {k} := by ext; simp
    have h2 : Prod.mk false ⁻¹' {((true, k) : Bool × ℕ)} = ∅ := by ext; simp
    rw [h1, h2, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp

lemma IA1_int_mix (p0 : ℝ≥0) (h : p0 ≤ 1) (src : Bool → PMF ℕ) (G : Bool × ℕ → ℝ)
    (h1 : Integrable (fun k => G (true, k)) (src true).toMeasure)
    (h2 : Integrable (fun k => G (false, k)) (src false).toMeasure) :
    ∫ y, G y ∂((PMF.bernoulli p0 h).bind fun b => (src b).map (Prod.mk b)).toMeasure =
      (p0 : ℝ) * ∫ k, G (true, k) ∂(src true).toMeasure +
        (1 - (p0 : ℝ)) * ∫ k, G (false, k) ∂(src false).toMeasure := by
  rw [IA1_mix]
  have i1 : Integrable G ((src true).toMeasure.map (Prod.mk true)) :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 h1
  have i2 : Integrable G ((src false).toMeasure.map (Prod.mk false)) :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 h2
  rw [integral_add_measure (i1.smul_measure ENNReal.coe_ne_top)
      (i2.smul_measure ENNReal.coe_ne_top), integral_smul_measure, integral_smul_measure,
    integral_map measurable_prodMk_left.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    integral_map measurable_prodMk_left.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  have e1 : (((1 - p0 : ℝ≥0) : ENNReal)).toReal = 1 - (p0 : ℝ) := by
    rw [ENNReal.coe_toReal, NNReal.coe_sub h, NNReal.coe_one]
  rw [e1, ENNReal.coe_toReal, smul_eq_mul, smul_eq_mul]

lemma IA1_tail (μ : Measure ℕ) [IsProbabilityMeasure μ] (F : ℕ → ℝ) (hF0 : ∀ k, 0 ≤ F k)
    (hF1 : ∀ k, F k ≤ 1) (T : ℝ) (hT : 0 < T) (N : ℕ)
    (hint : Integrable (fun k : ℕ => Real.exp (k / T)) μ) :
    ∫ k, F k ∂μ ≤ ∑ j ∈ Finset.range (N + 1), F j * μ.real {j} +
      Real.exp (-(N : ℝ) / T) * ∫ k, Real.exp (k / T) ∂μ := by
  have hpt : ∀ k : ℕ, F k ≤ ∑ j ∈ Finset.range (N + 1), F j * ({j} : Set ℕ).indicator 1 k +
      Real.exp (-(N : ℝ) / T) * Real.exp (k / T) := by
    intro k
    by_cases hk : k ≤ N
    · have hs : ∑ j ∈ Finset.range (N + 1), F j * ({j} : Set ℕ).indicator 1 k = F k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj; simp [Set.indicator_apply, Ne.symm hj]
        · intro hk'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'
      rw [hs]; have := Real.exp_pos (-(N : ℝ) / T); have := Real.exp_pos ((k : ℝ) / T)
      nlinarith
    · have hs : ∑ j ∈ Finset.range (N + 1), F j * ({j} : Set ℕ).indicator 1 k = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have : k ≠ j := by
          intro h; subst h; exact hk (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
        simp [Set.indicator_apply, this]
      rw [hs, zero_add, ← Real.exp_add]
      have : (0 : ℝ) ≤ -(N : ℝ) / T + k / T := by
        rw [← add_div]; apply div_nonneg _ hT.le
        have : (N : ℝ) < k := by exact_mod_cast (not_le.1 hk)
        linarith
      exact (hF1 k).trans (Real.one_le_exp this)
  have hFint : Integrable F μ :=
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 k)]; exact hF1 k)
  have hind : ∀ j : ℕ, Integrable (fun k => F j * ({j} : Set ℕ).indicator 1 k) μ := fun j =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton j) |>.const_mul (F j) |>.congr
      (Filter.Eventually.of_forall fun k => by simp [Set.indicator_apply])
  calc ∫ k, F k ∂μ ≤ ∫ k, (∑ j ∈ Finset.range (N + 1), F j * ({j} : Set ℕ).indicator 1 k +
      Real.exp (-(N : ℝ) / T) * Real.exp (k / T)) ∂μ := by
        refine integral_mono hFint ?_ hpt
        exact (integrable_finset_sum _ fun j _ => hind j).add (hint.const_mul _)
    _ = _ := by
        rw [integral_add (integrable_finset_sum _ fun j _ => hind j) (hint.const_mul _),
          integral_finset_sum _ fun j _ => hind j, integral_const_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, integral_indicator_one (measurableSet_singleton j)]

lemma IA1_toMeasure_pois (lam : ℝ≥0) : (poissonPMF lam).toMeasure = poissonMeasure lam := by
  rw [Measure.ext_iff_singleton]
  intro a
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), poissonMeasure_singleton,
    ← poissonPMFReal_ofReal_eq_poissonPMF]
  rfl

lemma IA1_pois_hasSum (lam : ℝ≥0) (s : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n)!) * Real.exp (n * s))
      (Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp s)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp s)).mul_left
    (Real.exp (-(lam : ℝ)))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : (fun n : ℕ => (Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / (n)!) * Real.exp (n * s)) =
      fun i : ℕ => Real.exp (-(lam : ℝ)) * (((lam : ℝ) * Real.exp s) ^ i / (i)!) := by
    funext n
    rw [Real.exp_nat_mul, mul_pow]
    ring
  rw [e]; exact h

lemma IA1_pois_mgf (M Lp : ℝ) (hM : M ≤ Lp) (hLp : 0 ≤ Lp) :
    Integrable (fun k : ℕ => Real.exp (k / (4 * Lp + 1))) (poissonPMF M.toNNReal).toMeasure ∧
      ∫ k, Real.exp ((k : ℝ) / (4 * Lp + 1)) ∂(poissonPMF M.toNNReal).toMeasure ≤ 2 := by
  set lam := M.toNNReal
  have hl : (0 : ℝ) ≤ lam := lam.2
  have hlL : (lam : ℝ) ≤ Lp := by
    rw [Real.coe_toNNReal']; exact max_le hM hLp
  set t : ℝ := 4 * Lp + 1 with ht
  have htpos : 0 < t := by positivity
  set s : ℝ := 1 / t with hs
  have hspos : 0 < s := by positivity
  have hs1 : s ≤ 1 := by rw [hs, div_le_one htpos]; linarith
  have hfun : (fun k : ℕ => Real.exp (k / t)) = fun k : ℕ => Real.exp (k * s) := by
    funext k; rw [hs, mul_one_div]
  have hHS := IA1_pois_hasSum lam s
  have hint : Integrable (fun k : ℕ => Real.exp (k / t)) (poissonPMF lam).toMeasure := by
    rw [hfun, IA1_toMeasure_pois, integrable_poissonMeasure_iff]
    refine hHS.summable.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨hint, ?_⟩
  have hval : ∫ k, Real.exp ((k : ℝ) / t) ∂(poissonPMF lam).toMeasure =
      Real.exp (-(lam : ℝ)) * Real.exp ((lam : ℝ) * Real.exp s) := by
    have hint' := hint
    rw [hfun, IA1_toMeasure_pois] at hint' ⊢
    rw [integral_poissonMeasure' hint']
    simpa [smul_eq_mul] using hHS.tsum_eq
  rw [hval, ← Real.exp_add]
  have he : Real.exp s ≤ 1 + s + s ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_pos hspos]; exact hs1)
    linarith [le_abs_self (Real.exp s - 1 - s)]
  have hls : (lam : ℝ) * s ≤ 1 / 4 := by
    rw [hs, mul_one_div, div_le_iff₀ htpos]; linarith
  have h1 : -(lam : ℝ) + lam * Real.exp s ≤ 1 / 2 := by
    have : (lam : ℝ) * Real.exp s ≤ lam * (1 + s + s ^ 2) := mul_le_mul_of_nonneg_left he hl
    have h2 : (lam : ℝ) * s ^ 2 ≤ lam * s := by
      have : s ^ 2 ≤ s := by nlinarith
      exact mul_le_mul_of_nonneg_left this hl
    nlinarith
  calc Real.exp (-(lam : ℝ) + lam * Real.exp s) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 h1
    _ ≤ 2 := by
      have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
      norm_num at this ⊢; linarith

lemma IA1_anom_mgf (P : PMF ℕ) (L T : ℝ)
    (hex : ∃ t > 0, Integrable (fun k : ℕ => Real.exp (|(k : ℝ)| / t)) P.toMeasure ∧
      ∫ k, Real.exp (|(k : ℝ)| / t) ∂P.toMeasure ≤ 2)
    (hle : HighDimProb.Concentration.subexponentialNorm P.toMeasure (fun k : ℕ => (k : ℝ)) ≤ L)
    (hT : L < T) :
    Integrable (fun k : ℕ => Real.exp (k / T)) P.toMeasure ∧
      ∫ k, Real.exp ((k : ℝ) / T) ∂P.toMeasure ≤ 2 := by
  unfold HighDimProb.Concentration.subexponentialNorm at hle
  obtain ⟨t, ⟨htpos, hti, ht2⟩, htT⟩ := exists_lt_of_csInf_lt (by
    obtain ⟨t, ht, h⟩ := hex; exact ⟨t, ht, h⟩) (lt_of_le_of_lt hle hT)
  have hpt : ∀ k : ℕ, Real.exp ((k : ℝ) / T) ≤ Real.exp (|(k : ℝ)| / t) := by
    intro k
    rw [abs_of_nonneg (Nat.cast_nonneg k)]
    exact Real.exp_le_exp.2 (div_le_div_of_nonneg_left (Nat.cast_nonneg k) htpos htT.le)
  have hint : Integrable (fun k : ℕ => Real.exp (k / T)) P.toMeasure :=
    hti.mono' Measurable.of_discrete.aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt k)
  exact ⟨hint, (integral_mono hint hti hpt).trans ht2⟩

lemma IA1_entry_bound (p0 : ℝ≥0) (h : p0 ≤ 1) (src : Bool → PMF ℕ) (c T : ℝ) (hc : 0 ≤ c)
    (hT : 0 < T) (N : ℕ)
    (hmgf : ∀ b, Integrable (fun k : ℕ => Real.exp (k / T)) (src b).toMeasure ∧
      ∫ k, Real.exp ((k : ℝ) / T) ∂(src b).toMeasure ≤ 2) :
    ∫ y, min (c / ((p0 : ℝ) * (src true y.2).toReal + (1 - (p0 : ℝ)) * (src false y.2).toReal)) 1
      ∂((PMF.bernoulli p0 h).bind fun b => (src b).map (Prod.mk b)).toMeasure ≤
      (N + 1) * c + 2 * Real.exp (-(N : ℝ) / T) := by
  set q : ℕ → ℝ := fun k => (p0 : ℝ) * (src true k).toReal + (1 - (p0 : ℝ)) * (src false k).toReal
    with hq
  have hp0 : (0 : ℝ) ≤ p0 := p0.2
  have hp1 : (p0 : ℝ) ≤ 1 := by exact_mod_cast h
  have hq0 : ∀ k, 0 ≤ q k := fun k =>
    add_nonneg (mul_nonneg hp0 ENNReal.toReal_nonneg) (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
  set F : ℕ → ℝ := fun k => min (c / q k) 1 with hF
  have hF0 : ∀ k, 0 ≤ F k := fun k => le_min (div_nonneg hc (hq0 k)) zero_le_one
  have hF1 : ∀ k, F k ≤ 1 := fun k => min_le_right _ _
  have hFint : ∀ b, Integrable F (src b).toMeasure := fun b =>
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 k)]; exact hF1 k)
  have hmix := IA1_int_mix p0 h src (fun y => F y.2) (hFint true) (hFint false)
  simp only at hmix
  change ∫ y : Bool × ℕ, F y.2 ∂_ ≤ _
  rw [hmix]
  have ht := fun b => IA1_tail (src b).toMeasure F hF0 hF1 T hT N (hmgf b).1
  have hreal : ∀ b j, (src b).toMeasure.real {j} = (src b j).toReal := fun b j => by
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  simp only [hreal] at ht
  have hFq : ∀ j, F j * q j ≤ c := by
    intro j
    rcases eq_or_lt_of_le (hq0 j) with h0 | hpos
    · rw [← h0, mul_zero]; exact hc
    · calc F j * q j ≤ c / q j * q j := mul_le_mul_of_nonneg_right (min_le_left _ _) (hq0 j)
        _ = c := div_mul_cancel₀ c hpos.ne'
  have hE := Real.exp_pos (-(N : ℝ) / T)
  calc (p0 : ℝ) * ∫ k, F k ∂(src true).toMeasure + (1 - (p0 : ℝ)) * ∫ k, F k ∂(src false).toMeasure
      ≤ (p0 : ℝ) * (∑ j ∈ Finset.range (N + 1), F j * (src true j).toReal +
          Real.exp (-(N : ℝ) / T) * 2) +
        (1 - (p0 : ℝ)) * (∑ j ∈ Finset.range (N + 1), F j * (src false j).toReal +
          Real.exp (-(N : ℝ) / T) * 2) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hp0
          exact (ht true).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hmgf true).2 hE.le) _)
        · apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact (ht false).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hmgf false).2 hE.le) _)
    _ = ∑ j ∈ Finset.range (N + 1), F j * q j + 2 * Real.exp (-(N : ℝ) / T) := by
        have hs : ∑ j ∈ Finset.range (N + 1), F j * q j =
            (p0 : ℝ) * ∑ j ∈ Finset.range (N + 1), F j * (src true j).toReal +
              (1 - (p0 : ℝ)) * ∑ j ∈ Finset.range (N + 1), F j * (src false j).toReal := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hq]; ring
        rw [hs]; ring
    _ ≤ ∑ j ∈ Finset.range (N + 1), c + 2 * Real.exp (-(N : ℝ) / T) := by
        gcongr with j; exact hFq j
    _ = (N + 1) * c + 2 * Real.exp (-(N : ℝ) / T) := by simp

lemma IA1_mul4 {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B) : a * b ≤ A * B :=
  mul_le_mul hA hB hb (ha.trans hA)

lemma IA1_arith (K L κ μ r pO C C' cmax : ℝ) (n m : ℕ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hκ : 1 ≤ κ) (hμ : 0 ≤ μ) (hr : 1 ≤ r) (hpO0 : 0 ≤ pO) (hpO1 : pO ≤ 1)
    (hC : 0 < C) (hC' : 0 < C') (hcmax : 0 ≤ cmax) (hm : 2 ≤ m) (hnm : m ≤ n) :
    2 * cmax * (((⌈(4 * L + 1) * Real.log m / 2⌉₊ : ℕ) + 1 : ℝ) *
        (C * ((K + L) ^ 3 * L * (κ ^ 4 * μ * r * L * Real.sqrt (Real.log m / (pO * m))))) +
        2 * Real.exp (-((⌈(4 * L + 1) * Real.log m / 2⌉₊ : ℕ) : ℝ) / (4 * L + 1)) +
        C' / (n * m)) ≤
      cmax * (2 * (6 * C + 6 + 3 * C')) * (1 + K + L + κ + μ + r + 1 / pO) ^ 13 *
        Real.log m ^ ((3 : ℝ) / 2) / Real.sqrt m := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (m : ℝ) ≤ n := by exact_mod_cast hnm
  have hinvpO : 0 ≤ 1 / pO := by positivity
  generalize hP : 1 + K + L + κ + μ + r + 1 / pO = P
  generalize hℓ : Real.log m = ℓ
  generalize hT : 4 * L + 1 = T
  generalize hN : ⌈T * ℓ / 2⌉₊ = N
  generalize hsm : Real.sqrt m = sm
  have hP1 : 1 ≤ P := by rw [← hP]; linarith
  have hP0 : 0 ≤ P := by linarith
  have hKLP : K + L ≤ P := by rw [← hP]; linarith
  have hLP : L ≤ P := by rw [← hP]; linarith
  have hκP : κ ≤ P := by rw [← hP]; linarith
  have hμP : μ ≤ P := by rw [← hP]; linarith
  have hrP : r ≤ P := by rw [← hP]; linarith
  have hpP : 1 / pO ≤ P := by rw [← hP]; linarith
  have hTpos : 0 < T := by rw [← hT]; linarith
  have hℓ2 : 1 / 2 ≤ ℓ := by
    have : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hmR
    have := Real.log_two_gt_d9
    rw [← hℓ]; linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hsm1 : 1 ≤ sm := by rw [← hsm, Real.one_le_sqrt]; linarith
  have hsm0 : 0 < sm := by linarith
  have hsℓ0 : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg _
  have hsℓ : (7 : ℝ) / 10 ≤ Real.sqrt ℓ := by
    rw [Real.le_sqrt (by norm_num) hℓ0]; linarith
  have hpow : ℓ ^ ((3 : ℝ) / 2) = ℓ * Real.sqrt ℓ := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hℓ0 (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hLS : 0 ≤ ℓ * Real.sqrt ℓ := mul_nonneg hℓ0 hsℓ0
  have hone : 1 ≤ 3 * (ℓ * Real.sqrt ℓ) := by
    have := mul_le_mul hℓ2 hsℓ (by norm_num) hℓ0
    linarith
  have hP13 : 1 ≤ P ^ 13 := one_le_pow₀ hP1
  have hPone : 1 ≤ P ^ 13 * (3 * (ℓ * Real.sqrt ℓ)) := one_le_mul_of_one_le_of_one_le hP13 hone
  -- the three error terms
  have hN1 : (N : ℝ) + 1 ≤ 6 * P * ℓ := by
    have h1 : (N : ℝ) < T * ℓ / 2 + 1 := by rw [← hN]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : T ≤ 4 * P := by rw [← hT]; linarith
    have h3 : T * ℓ ≤ 4 * P * ℓ := mul_le_mul_of_nonneg_right h2 hℓ0
    have h4 : 1 * (1 / 2) ≤ P * ℓ := mul_le_mul hP1 hℓ2 (by norm_num) hP0
    linarith
  have hexp : Real.exp (-(N : ℝ) / T) ≤ 1 / sm := by
    have hNT : ℓ / 2 ≤ N / T := by
      rw [le_div_iff₀ hTpos]
      have := Nat.le_ceil (T * ℓ / 2)
      rw [hN] at this
      linarith
    have hsm_exp : sm = Real.exp (ℓ / 2) := by
      rw [← hsm, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith), hℓ]; ring_nf
    rw [hsm_exp, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    rw [neg_div]; linarith
  have hsq : Real.sqrt (ℓ / (pO * m)) ≤ Real.sqrt ℓ * P / sm := by
    rcases eq_or_lt_of_le hpO0 with h0 | hpos
    · rw [← h0]; simp only [zero_mul, div_zero, Real.sqrt_zero]
      exact div_nonneg (mul_nonneg hsℓ0 hP0) hsm0.le
    · rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul hpos.le, hsm]
      have hspO : pO ≤ Real.sqrt pO := by
        rw [Real.le_sqrt hpos.le hpos.le]
        calc pO ^ 2 = pO * pO := sq pO
          _ ≤ pO * 1 := mul_le_mul_of_nonneg_left hpO1 hpos.le
          _ = pO := mul_one _
      have hspO0 : 0 < Real.sqrt pO := Real.sqrt_pos.2 hpos
      rw [div_le_div_iff₀ (mul_pos hspO0 hsm0) hsm0]
      have hPp1 : 1 ≤ P * pO := by have := (div_le_iff₀ hpos).1 hpP; linarith
      have hPp : 1 ≤ P * Real.sqrt pO :=
        hPp1.trans (mul_le_mul_of_nonneg_left hspO hP0)
      have : Real.sqrt ℓ ≤ Real.sqrt ℓ * (P * Real.sqrt pO) := le_mul_of_one_le_right hsℓ0 hPp
      calc Real.sqrt ℓ * sm ≤ Real.sqrt ℓ * (P * Real.sqrt pO) * sm :=
            mul_le_mul_of_nonneg_right this hsm0.le
        _ = Real.sqrt ℓ * P * (Real.sqrt pO * sm) := by ring
  have hKL0 : 0 ≤ K + L := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hA : (K + L) ^ 3 * L * (κ ^ 4 * μ * r * L * Real.sqrt (ℓ / (pO * m))) ≤
      P ^ 3 * P * (P ^ 4 * P * P * P * (Real.sqrt ℓ * P / sm)) := by
    apply IA1_mul4 (by positivity) (by positivity)
    · exact IA1_mul4 (by positivity) hL (pow_le_pow_left₀ hKL0 hKLP 3) hLP
    · apply IA1_mul4 (by positivity) (Real.sqrt_nonneg _) _ hsq
      apply IA1_mul4 (by positivity) hL _ hLP
      apply IA1_mul4 (by positivity) hr0 _ hrP
      apply IA1_mul4 (by positivity) hμ _ hμP
      exact pow_le_pow_left₀ hκ0 hκP 4
  have hA0 : 0 ≤ (K + L) ^ 3 * L * (κ ^ 4 * μ * r * L * Real.sqrt (ℓ / (pO * m))) := by
    positivity
  have hmain : ((N : ℝ) + 1) * (C * ((K + L) ^ 3 * L * (κ ^ 4 * μ * r * L *
      Real.sqrt (ℓ / (pO * m))))) ≤ 6 * C * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by
    calc ((N : ℝ) + 1) * (C * ((K + L) ^ 3 * L * (κ ^ 4 * μ * r * L *
          Real.sqrt (ℓ / (pO * m))))) ≤ (6 * P * ℓ) * (C * (P ^ 3 * P * (P ^ 4 * P * P * P *
            (Real.sqrt ℓ * P / sm)))) :=
          IA1_mul4 (by positivity) (mul_nonneg hC.le hA0) hN1 (mul_le_mul_of_nonneg_left hA hC.le)
      _ = 6 * C * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by
          field_simp
  have h2 : 2 * Real.exp (-(N : ℝ) / T) ≤ 6 * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by
    calc 2 * Real.exp (-(N : ℝ) / T) ≤ 2 * (1 / sm) := by linarith
      _ ≤ 6 * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by
          rw [mul_one_div, div_le_div_iff_of_pos_right hsm0]; linarith
  have h3 : C' / (n * m) ≤ 3 * C' * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by
    have hsmm : sm ≤ m := by
      rw [← hsm, Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith
    have hnm' : sm ≤ (n : ℝ) * m := hsmm.trans (le_mul_of_one_le_left (by linarith) (by linarith))
    calc C' / (n * m) ≤ C' / sm := div_le_div_of_nonneg_left hC'.le hsm0 hnm'
      _ ≤ 3 * C' * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by
          rw [div_le_div_iff_of_pos_right hsm0]
          have := le_mul_of_one_le_right hC'.le hPone
          linarith
  rw [hpow]
  calc 2 * cmax * (((N : ℝ) + 1) * (C * ((K + L) ^ 3 * L * (κ ^ 4 * μ * r * L *
        Real.sqrt (ℓ / (pO * m))))) + 2 * Real.exp (-(N : ℝ) / T) + C' / (n * m))
      ≤ 2 * cmax * (6 * C * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm +
          6 * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm + 3 * C' * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = cmax * (2 * (6 * C + 6 + 3 * C')) * P ^ 13 * (ℓ * Real.sqrt ℓ) / sm := by ring


/-- Law of the sales value of entry `(i,j)` given the anomaly indicator `b`. -/
noncomputable def IA1_src {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) (b : Bool) : PMF ℕ :=
  if b then I.model.anom I.αstar (I.Mstar ij.1 ij.2).toNNReal
  else poissonPMF (I.Mstar ij.1 ij.2).toNNReal

/-- Joint law of (anomaly indicator, sales) of entry `(i,j)`. -/
noncomputable def IA1_D {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) : PMF (Bool × ℕ) :=
  (PMF.bernoulli (min I.pAstar 1) (min_le_right _ _)).bind fun b => (IA1_src I ij b).map (Prod.mk b)

lemma IA1_entry {d : ℕ} (I : Instance d) (ij : Fin I.n × Fin I.m) :
    (I.entryPMF ij).toMeasure =
      (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).toMeasure.prod (IA1_D I ij).toMeasure := by
  have hE : I.entryPMF ij = (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).bind
      fun o => (IA1_D I ij).map (Prod.mk o) := by
    unfold Instance.entryPMF
    congr 1
    funext o
    simp only [IA1_D, PMF.map_bind, PMF.map_comp]
    rfl
  rw [Measure.ext_iff_singleton]
  rintro ⟨o, y⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), hE, IA1_bind_mk_apply]

theorem solution (d : ℕ) (cM cA CRC : ℝ) (hcM : 0 < cM) (hcA : 0 < cA) (hcA1 : cA < 1)
    (hCRC : 0 < CRC) :
    ∃ Csp C₀ : ℝ, ∃ k : ℕ, 0 < Csp ∧ 0 < C₀ ∧
      ∀ (I : Instance d) (K L μ cmax : ℝ) (hI : I.Model cM cA Csp K L μ),
        I.Regular hI.r_pos cA CRC K L μ → I.CostBound cmax →
        ∀ (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
          (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))),
        IsBestRankApprox I.r svdr → I.ThetaSel cA svdr θhat →
        ∫ ω, (I.costEW svdr θhat (I.obs ω) - I.costStar (I.obs ω)) ∂I.law ≤
          cmax * C₀ * (1 + K + L + I.κ hI.r_pos + μ + I.r + 1 / (I.pO : ℝ)) ^ k *
            Real.log I.m ^ ((3 : ℝ) / 2) / Real.sqrt I.m := by
  classical
  obtain ⟨Csp, C, C', hCsp, hC, hC', H3⟩ := lemma_3 d cM cA CRC hcM hcA hcA1 hCRC
  refine ⟨Csp, 2 * (6 * C + 6 + 3 * C'), 13, hCsp, by positivity, ?_⟩
  intro I K L μ cmax hI hReg hcost svdr θhat hsvd hsel
  have h3 := H3 I K L μ hI hReg svdr θhat hsvd hsel
  -- elementary consequences of the standing assumptions
  have hm2 := hI.two_le_m
  have hmn := hI.m_le_n
  have hm0 : 0 < I.m := by omega
  have hn0 : 0 < I.n := by omega
  have hL : 0 ≤ L := (abs_nonneg _).trans (hI.max_ub ⟨0, hn0⟩ ⟨0, hm0⟩)
  have hK : 0 ≤ K := by
    have := hI.smooth 0 (I.αstar, 0) ⟨hI.α_mem, Set.mem_Ici.2 le_rfl⟩ (I.αstar, 1) ⟨hI.α_mem, Set.mem_Ici.2 zero_le_one⟩
    have hd : dist ((I.αstar, (0 : ℝ))) (I.αstar, (1 : ℝ)) = 1 := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [hd, mul_one] at this
    exact (abs_nonneg _).trans this
  have hκ : 1 ≤ I.κ hI.r_pos := by
    unfold Instance.κ
    have h1 := hI.σ_pos ⟨I.r - 1, by have := hI.r_pos; omega⟩
    have h2 : I.σ ⟨I.r - 1, by have := hI.r_pos; omega⟩ ≤ I.σ ⟨0, hI.r_pos⟩ :=
      hI.σ_anti (Fin.mk_le_mk.2 (Nat.zero_le _))
    rw [one_le_div h1]; exact h2
  have hμ : 0 ≤ μ := by
    have h := hI.incoh_U ⟨0, hn0⟩
    have h0 : 0 ≤ ∑ k, I.U ⟨0, hn0⟩ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_contra hneg'
    have hneg : μ < 0 := lt_of_not_ge hneg'
    have hr' : (0 : ℝ) < I.r := by exact_mod_cast hI.r_pos
    have hn' : (0 : ℝ) < I.n := by exact_mod_cast hn0
    have : μ * I.r / I.n < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hr') hn'
    linarith
  have hr : (1 : ℝ) ≤ I.r := by exact_mod_cast hI.r_pos
  have hpO1 : (I.pO : ℝ) ≤ 1 := by exact_mod_cast hI.pO_le
  have hpO0 : (0 : ℝ) ≤ I.pO := I.pO.2
  have hcmax : 0 ≤ cmax := (hcost ⟨0, hn0⟩ ⟨0, hm0⟩).1.trans (hcost ⟨0, hn0⟩ ⟨0, hm0⟩).2.1
  have hpA1 : (I.pAstar : ℝ) < 1 := by have := hI.pA_le; linarith
  have hpA0 : (0 : ℝ) ≤ I.pAstar := I.pAstar.2
  have hpAle : I.pAstar ≤ 1 := by exact_mod_cast hpA1.le
  have hminpA : ((min I.pAstar 1 : ℝ≥0) : ℝ) = I.pAstar := by rw [min_eq_left hpAle]
  -- the constants of the bound
  set c : ℝ := C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) with hcdef
  have hδ'0 : 0 ≤ I.δ' hI.r_pos μ L := by
    unfold Instance.δ'
    have : 0 ≤ I.κ hI.r_pos := by linarith
    have : (0 : ℝ) ≤ I.r := by linarith
    positivity
  have hc0 : 0 ≤ c := by
    have : 0 ≤ K + L := by linarith
    positivity
  set T : ℝ := 4 * L + 1 with hT
  have hTpos : 0 < T := by rw [hT]; linarith
  set N : ℕ := ⌈(4 * L + 1) * Real.log I.m / 2⌉₊ with hN
  set B : ℝ := (N + 1) * c + 2 * Real.exp (-(N : ℝ) / T) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the per-entry function
  set f : Fin I.n × Fin I.m → Bool × ℕ → ℝ := fun ij y =>
    min (c / (((min I.pAstar 1 : ℝ≥0) : ℝ) * (IA1_src I ij true y.2).toReal +
      (1 - ((min I.pAstar 1 : ℝ≥0) : ℝ)) * (IA1_src I ij false y.2).toReal)) 1 with hf
  have hden0 : ∀ ij (y : Bool × ℕ), 0 ≤ ((min I.pAstar 1 : ℝ≥0) : ℝ) *
      (IA1_src I ij true y.2).toReal + (1 - ((min I.pAstar 1 : ℝ≥0) : ℝ)) *
        (IA1_src I ij false y.2).toReal := by
    intro ij y
    rw [hminpA]
    exact add_nonneg (mul_nonneg hpA0 ENNReal.toReal_nonneg)
      (mul_nonneg (by linarith) ENNReal.toReal_nonneg)
  have hf0 : ∀ ij y, 0 ≤ f ij y := fun ij y => le_min (div_nonneg hc0 (hden0 ij y)) zero_le_one
  have hf1 : ∀ ij y, f ij y ≤ 1 := fun ij y => min_le_right _ _
  -- per-entry expectation bound
  have hBent : ∀ ij, ∫ y, f ij y ∂(IA1_D I ij).toMeasure ≤ B := by
    intro ij
    apply IA1_entry_bound (min I.pAstar 1) (min_le_right _ _) (IA1_src I ij) c T hc0 hTpos N
    intro b
    cases b
    · have hM : I.Mstar ij.1 ij.2 ≤ L := (le_abs_self _).trans (hI.max_ub ij.1 ij.2)
      simpa [IA1_src, hT] using IA1_pois_mgf (I.Mstar ij.1 ij.2) L hM hL
    · simpa [IA1_src, hT] using IA1_anom_mgf _ L T (hI.subexp ij.1 ij.2) (hI.subexp_le ij.1 ij.2)
        (by rw [hT]; linarith)
  -- the decoupled average
  set W : I.Sample → ℝ := fun ω =>
    (1 / ((Finset.univ.filter fun ij => (ω ij).1 = true).card : ℝ)) *
      ∑ ij ∈ Finset.univ.filter (fun ij => (ω ij).1 = true), f ij (ω ij).2 with hW
  have hlaw : I.law = Measure.pi fun ij =>
      (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).toMeasure.prod (IA1_D I ij).toMeasure := by
    unfold Instance.law
    congr 1
    funext ij
    exact IA1_entry I ij
  have hWint : ∫ ω, W ω ∂I.law ≤ B := by
    rw [hlaw]
    exact IA1_decouple _ (fun ij => (IA1_D I ij).toMeasure) f hf0 hf1 B hB0 hBent
  -- the good event of Lemma 3
  set G : Set I.Sample := {ω | ∀ ij ∈ I.omega (I.obs ω),
      |I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2| ≤
        min (C * ((K + L) ^ 3 * L * I.δ' hI.r_pos μ L) /
          (I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2)) 1} with hG
  have hΩ : ∀ ω : I.Sample, I.omega (I.obs ω) = Finset.univ.filter fun ij => (ω ij).1 = true := by
    intro ω; ext ij; simp [Instance.omega, Instance.obs]
  -- on observed entries, `x* + y*` is the denominator of `f`
  have hden : ∀ ω : I.Sample, ∀ ij, (ω ij).1 = true →
      I.xstar (I.obs ω) ij.1 ij.2 + I.ystar (I.obs ω) ij.1 ij.2 =
        ((min I.pAstar 1 : ℝ≥0) : ℝ) * (IA1_src I ij true (ω ij).2.2).toReal +
          (1 - ((min I.pAstar 1 : ℝ≥0) : ℝ)) * (IA1_src I ij false (ω ij).2.2).toReal := by
    intro ω ij h1
    have hobs : I.obs ω (ij.1, ij.2) = some (ω ij).2.2 := by simp [Instance.obs, h1]
    rw [hminpA]
    simp only [Instance.xstar, Instance.ystar, hobs, Option.getD_some, IA1_src, if_true,
      Bool.false_eq_true, if_false, AnomModel.pmf, poisPmf]
    congr 2
    rw [← poissonPMFReal_ofReal_eq_poissonPMF, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  have hc' : ∀ i j, 0 ≤ I.c0 i j ∧ 0 ≤ I.c1 i j := fun i j => ⟨(hcost i j).1, (hcost i j).2.2.1⟩
  -- pointwise bound on the excess cost
  have hpt : ∀ ω : I.Sample, I.costEW svdr θhat (I.obs ω) - I.costStar (I.obs ω) ≤
      2 * cmax * (W ω + Gᶜ.indicator 1 ω) := by
    intro ω
    have hs4 := (step4_excess_cost I hc' svdr θhat (I.obs ω)).2
    simp only at hs4
    refine hs4.trans ?_
    have hind0 : 0 ≤ Gᶜ.indicator (1 : I.Sample → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hterm : ∀ ij ∈ I.omega (I.obs ω),
        |-I.c1 ij.1 ij.2 + (I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) * I.fhat svdr θhat (I.obs ω) ij.1 ij.2 -
          (-I.c1 ij.1 ij.2 + (I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) * I.fstar (I.obs ω) ij.1 ij.2)| ≤
        2 * cmax * (f ij (ω ij).2 + Gᶜ.indicator 1 ω) := by
      intro ij hij
      have h1 : (ω ij).1 = true := by rw [hΩ] at hij; simpa using hij
      obtain ⟨hc0', hc0m, hc1', hc1m⟩ := hcost ij.1 ij.2
      have hfd : |I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2| ≤
          f ij (ω ij).2 + Gᶜ.indicator 1 ω := by
        by_cases hω : ω ∈ G
        · have := hω ij hij
          rw [hden ω ij h1, ← hcdef] at this
          rw [Set.indicator_of_notMem (show ω ∉ Gᶜ from fun h => h hω), add_zero]
          exact this
        · rw [Set.indicator_of_mem (show ω ∈ Gᶜ from hω), Pi.one_apply]
          have hxs : 0 ≤ I.xstar (I.obs ω) ij.1 ij.2 :=
            mul_nonneg hpA0 ENNReal.toReal_nonneg
          have hys : 0 ≤ I.ystar (I.obs ω) ij.1 ij.2 := by
            unfold Instance.ystar poisPmf poissonPMFReal
            exact mul_nonneg (by linarith) (by positivity)
          have hfs0 : 0 ≤ I.fstar (I.obs ω) ij.1 ij.2 := div_nonneg hys (add_nonneg hxs hys)
          have hfs1 : I.fstar (I.obs ω) ij.1 ij.2 ≤ 1 :=
            div_le_one_of_le₀ (by linarith) (add_nonneg hxs hys)
          have hxh : 0 ≤ I.xhat svdr θhat (I.obs ω) ij.1 ij.2 := le_max_right _ _
          have hyh : 0 ≤ I.yhat svdr θhat (I.obs ω) ij.1 ij.2 := le_max_right _ _
          have hfh0 : 0 ≤ I.fhat svdr θhat (I.obs ω) ij.1 ij.2 := div_nonneg hyh (add_nonneg hxh hyh)
          have hfh1 : I.fhat svdr θhat (I.obs ω) ij.1 ij.2 ≤ 1 :=
            div_le_one_of_le₀ (by linarith) (add_nonneg hxh hyh)
          have := hf0 ij (ω ij).2
          rw [abs_le]; constructor <;> linarith
      have heq : -I.c1 ij.1 ij.2 + (I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) *
            I.fhat svdr θhat (I.obs ω) ij.1 ij.2 -
          (-I.c1 ij.1 ij.2 + (I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) * I.fstar (I.obs ω) ij.1 ij.2) =
          -((I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) *
            (I.fstar (I.obs ω) ij.1 ij.2 - I.fhat svdr θhat (I.obs ω) ij.1 ij.2)) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_nonneg (add_nonneg hc0' hc1')]
      have hsum : I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2 ≤ 2 * cmax := by linarith
      exact mul_le_mul hsum hfd (abs_nonneg _) (by linarith)
    rw [hΩ ω] at hterm ⊢
    set S := Finset.univ.filter fun ij => (ω ij).1 = true with hS
    have hW' : W ω = (1 / (S.card : ℝ)) * ∑ ij ∈ S, f ij (ω ij).2 := rfl
    rw [hW']
    have hW0 : 0 ≤ (1 / (S.card : ℝ)) * ∑ ij ∈ S, f ij (ω ij).2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun ij _ => hf0 ij _)
    calc (1 / (S.card : ℝ)) * ∑ ij ∈ S, |-I.c1 ij.1 ij.2 + (I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) *
            I.fhat svdr θhat (I.obs ω) ij.1 ij.2 -
          (-I.c1 ij.1 ij.2 + (I.c0 ij.1 ij.2 + I.c1 ij.1 ij.2) * I.fstar (I.obs ω) ij.1 ij.2)|
        ≤ (1 / (S.card : ℝ)) * ∑ ij ∈ S, 2 * cmax * (f ij (ω ij).2 + Gᶜ.indicator 1 ω) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ ≤ 2 * cmax * ((1 / (S.card : ℝ)) * ∑ ij ∈ S, f ij (ω ij).2 + Gᶜ.indicator 1 ω) := by
          rcases Nat.eq_zero_or_pos S.card with h0 | hpos
          · rw [h0]; simp only [Nat.cast_zero, div_zero, zero_mul]
            exact mul_nonneg (by linarith) (by linarith)
          · rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            have hSc : (0 : ℝ) < S.card := by exact_mod_cast hpos
            have : (1 / (S.card : ℝ)) * (S.card * Gᶜ.indicator (1 : I.Sample → ℝ) ω) =
                Gᶜ.indicator 1 ω := by field_simp
            rw [mul_left_comm, mul_add, this]
  -- integrate
  have hP : IsProbabilityMeasure I.law := by unfold Instance.law; infer_instance
  have hWintg : Integrable W I.law :=
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun ij _ => hf0 ij _))]
        have : W ω ≤ 1 := by
          simp only [hW]
          set S := Finset.univ.filter fun ij => (ω ij).1 = true
          rcases Nat.eq_zero_or_pos S.card with h0 | hpos
          · rw [h0]; simp
          · have hSc : (0 : ℝ) < S.card := by exact_mod_cast hpos
            rw [one_div, inv_mul_le_iff₀ hSc, mul_one]
            calc ∑ ij ∈ S, f ij (ω ij).2 ≤ ∑ ij ∈ S, (1 : ℝ) := Finset.sum_le_sum fun ij _ => hf1 ij _
              _ = S.card := by simp
        exact this)
  have hIint : Integrable (Gᶜ.indicator (1 : I.Sample → ℝ)) I.law :=
    (integrable_const (1 : ℝ)).indicator MeasurableSet.of_discrete
  have hGc : I.law.real Gᶜ ≤ C' / (I.n * I.m) := by
    rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ]
    linarith
  calc ∫ ω, (I.costEW svdr θhat (I.obs ω) - I.costStar (I.obs ω)) ∂I.law
      ≤ ∫ ω, 2 * cmax * (W ω + Gᶜ.indicator 1 ω) ∂I.law := by
        by_cases hi : Integrable (fun ω => I.costEW svdr θhat (I.obs ω) - I.costStar (I.obs ω)) I.law
        · exact integral_mono hi ((hWintg.add hIint).const_mul _) hpt
        · rw [integral_undef hi]
          refine integral_nonneg fun ω => mul_nonneg (by linarith) (add_nonneg ?_ ?_)
          · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun ij _ => hf0 ij _)
          · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    _ = 2 * cmax * (∫ ω, W ω ∂I.law + I.law.real Gᶜ) := by
        rw [integral_const_mul, integral_add hWintg hIint,
          integral_indicator_one MeasurableSet.of_discrete]
    _ ≤ 2 * cmax * (B + C' / (I.n * I.m)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
    _ ≤ _ := by
        have := IA1_arith K L (I.κ hI.r_pos) μ I.r I.pO C C' cmax I.n I.m hK hL hκ hμ hr hpO0 hpO1
          hC hC' hcmax hm2 hmn
        simp only [hB, hcdef, hT, hN, Instance.δ']
        convert this using 2
