-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFiniteOffspringMeanRatioConvergesAE
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:30:47.104646+00:00
-- url     : https://prove2.me/submissions/10854cf7-e90d-4735-9a29-0c91706cbbc1

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace RatioAux

lemma identDistrib_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Z : ℕ → Ω → ℝ} {L : Measure ℝ} (hm : ∀ n, Measurable (Z n)) (hl : ∀ n, HasLaw (Z n) L Q)
    (n : ℕ) : IdentDistrib (Z n) (Z 0) Q Q :=
  ⟨(hm n).aemeasurable, (hm 0).aemeasurable, by rw [(hl n).map_eq, (hl 0).map_eq]⟩

lemma integrable_id_jumpLaw (offspring : PMF ℕ)
    (hFiniteMean : Summable (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    Integrable (fun x : ℝ => x) jumpLaw := by
  set A : Set ℝ := Set.range (fun k : ℕ => (k : ℝ) - 1) with hA
  have hAeq : {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = A := by
    ext x; simp [hA, eq_comm]
  have hAc : jumpLaw Aᶜ = 0 := by
    have hAm : MeasurableSet A := (Set.countable_range _).measurableSet
    rw [measure_compl hAm (measure_ne_top _ _), ← hAeq, hSupport]; simp
  have hinj : Function.Injective (fun k : ℕ => (k : ℝ) - 1) := by
    intro a b h; simpa using h
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hrestr : jumpLaw.restrict A = jumpLaw := Measure.restrict_eq_self_of_ae_mem
    (ae_iff.2 hAc)
  rw [← hrestr, lintegral_countable _ (Set.countable_range _)]
  rw [tsum_range (fun x : ℝ => ‖x‖ₑ * jumpLaw {x}) hinj]
  simp only [hJumpMass]
  have hsum : Summable (fun k : ℕ => (offspring k).toReal * ((k : ℝ) + 1)) := by
    have h2 : Summable (fun k : ℕ => (offspring k).toReal) :=
      ENNReal.summable_toReal (by rw [PMF.tsum_coe]; simp)
    simpa [mul_add] using hFiniteMean.add h2
  have hle : ∀ k : ℕ, ‖((k : ℝ) - 1)‖ₑ * offspring k ≤
      ENNReal.ofReal ((offspring k).toReal * ((k : ℝ) + 1)) := by
    intro k
    have hne : offspring k ≠ ⊤ := PMF.apply_ne_top offspring k
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne, mul_comm]
    gcongr
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  calc ∑' k : ℕ, ‖((k : ℝ) - 1)‖ₑ * offspring k
      ≤ ∑' k : ℕ, ENNReal.ofReal ((offspring k).toReal * ((k : ℝ) + 1)) := ENNReal.tsum_le_tsum hle
    _ = ENNReal.ofReal (∑' k : ℕ, (offspring k).toReal * ((k : ℝ) + 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top


lemma integrable_exp (r : ℝ) (hr : 0 < r) : Integrable (fun x : ℝ => x) (expMeasure r) := by
  have heq : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  have hmf : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [heq, integrable_withDensity_iff (g := fun x : ℝ => x) hmf
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hfun : (fun x : ℝ => x * (exponentialPDF r x).toReal) =
      (Ioi (0:ℝ)).indicator (fun x => r * (x ^ (1:ℝ) * Real.exp (-r * x ^ (1:ℝ)))) := by
    ext x
    by_cases hx : 0 < x
    · simp only [Set.indicator, Set.mem_Ioi, hx, if_true]
      rw [exponentialPDF_of_nonneg hx.le,
        ENNReal.toReal_ofReal (by positivity)]
      simp only [Real.rpow_one]; ring_nf
    · simp only [Set.indicator, Set.mem_Ioi, hx, if_false]
      rcases (not_lt.1 hx).lt_or_eq with h | h
      · rw [exponentialPDF_of_neg h]; simp
      · subst h; simp
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hr).const_mul r

lemma ren (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) (a : ℝ) (ha : 0 < a)
    (hT : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, τ i) atTop (nhds a)) :
    Tendsto (fun t : ℝ≥0 => jumpCount (fun n => ∑ i ∈ Finset.range (n + 1), τ i) t) atTop atTop ∧
    Tendsto (fun t : ℝ≥0 =>
      (jumpCount (fun n => ∑ i ∈ Finset.range (n + 1), τ i) t : ℝ) / (1 + (t : ℝ)))
      atTop (nhds a⁻¹) := by
  set T : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), τ i with hTdef
  have hT1 : Tendsto (fun n : ℕ => T n / ((n : ℝ) + 1)) atTop (nhds a) := by
    have := hT.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp, smul_eq_mul, hTdef]
    push_cast; rw [div_eq_inv_mul]
  have hmono : StrictMono T := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [hTdef]
    rw [Finset.sum_range_succ _ (n + 1)]
    linarith [hτ (n + 1)]
  have hT0 : ∀ n, 0 ≤ T n := fun n =>
    Finset.sum_nonneg fun i _ => (hτ i).le
  have hTinf : Tendsto T atTop atTop := by
    have h := Tendsto.pos_mul_atTop ha hT1
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine h.congr fun n => ?_
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hne : ∀ t : ℝ, ({n | t < T n} : Set ℕ).Nonempty := fun t =>
    (hTinf.eventually_gt_atTop t).exists
  have hNlt : ∀ t : ℝ, t < T (jumpCount T t) := fun t => Nat.sInf_mem (hne t)
  have hNge : ∀ t : ℝ, 1 ≤ jumpCount T t → T (jumpCount T t - 1) ≤ t := by
    intro t h1
    have hlt : jumpCount T t - 1 < sInf {n | t < T n} := by
      show jumpCount T t - 1 < jumpCount T t; omega
    have := Nat.notMem_of_lt_sInf hlt
    simpa using this
  have hNinf : Tendsto (fun t : ℝ≥0 => jumpCount T t) atTop atTop := by
    rw [tendsto_atTop]
    intro n
    filter_upwards [eventually_ge_atTop (Real.toNNReal (T n))] with t ht
    by_contra h
    push Not at h
    have h1 := hmono h
    have h2 : T n ≤ (t : ℝ) := (Real.toNNReal_le_iff_le_coe).1 ht
    linarith [hNlt (t : ℝ)]
  refine ⟨hNinf, ?_⟩
  -- f k = k/(1+T k) → a⁻¹, g k = k/(1+T(k-1)) → a⁻¹
  have hq : Tendsto (fun k : ℕ => (1 + T k) / ((k : ℝ) + 1)) atTop (nhds a) := by
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := h0.add hT1
    rw [zero_add] at this
    refine this.congr fun k => ?_
    rw [add_div]
  have hf : Tendsto (fun k : ℕ => (k : ℝ) / (1 + T k)) atTop (nhds a⁻¹) := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + 1)) atTop (nhds 1) :=
      tendsto_natCast_div_add_atTop (1:ℝ)
    have := h1.div hq ha.ne'
    rw [one_div] at this
    refine this.congr fun k => ?_
    have : (k : ℝ) + 1 ≠ 0 := by positivity
    have : 1 + T k ≠ 0 := by linarith [hT0 k]
    simp only [Pi.div_apply]
    field_simp
  have hg : Tendsto (fun k : ℕ => (k : ℝ) / (1 + T (k - 1))) atTop (nhds a⁻¹) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have := hq.inv₀ ha.ne'
    refine this.congr fun k => ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [inv_div]
  have hev : ∀ᶠ t : ℝ≥0 in atTop, 1 ≤ jumpCount T t := hNinf.eventually_ge_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hf.comp hNinf) (hg.comp hNinf) ?_ ?_
  · filter_upwards with t
    simp only [Function.comp]
    have ht0 : (0:ℝ) < 1 + t := by positivity
    apply div_le_div_of_nonneg_left (by positivity) ht0
    linarith [hNlt (t : ℝ)]
  · filter_upwards [hev] with t ht
    simp only [Function.comp]
    have hpos : (0:ℝ) < 1 + T (jumpCount T t - 1) := by linarith [hT0 (jumpCount T t - 1)]
    apply div_le_div_of_nonneg_left (by positivity) hpos
    linarith [hNge (t : ℝ) ht]

lemma rislln (S : ℕ → ℝ) (N : ℝ≥0 → ℕ) (mu rate : ℝ)
    (hS : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * S n) atTop (nhds mu))
    (hN : Tendsto N atTop atTop)
    (hRate : Tendsto (fun t : ℝ≥0 => (N t : ℝ) / (1 + (t : ℝ))) atTop (nhds rate)) :
    Tendsto (fun t : ℝ≥0 => S (N t) / (1 + (t : ℝ))) atTop (nhds (mu * rate)) := by
  have h1 : Tendsto (fun t : ℝ≥0 => (N t : ℝ)⁻¹ * S (N t)) atTop (nhds mu) := hS.comp hN
  have h2 := h1.mul hRate
  refine h2.congr' ?_
  have hev : ∀ᶠ t in atTop, 1 ≤ N t := hN.eventually_ge_atTop 1
  filter_upwards [hev] with t ht
  have hNpos : (0 : ℝ) < N t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < 1 + (t : ℝ) := by positivity
  field_simp

end RatioAux

open RatioAux in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (hFiniteMean : Summable (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ᵐ ω ∂Q, ∃ L : ℝ,
      Tendsto (fun t : ℝ≥0 =>
        ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω /
          (1 + (t : ℝ))) atTop (nhds L) := by
  -- marks: SLLN
  have hmI : Integrable (marks 0) Q := by
    have hJ := integrable_id_jumpLaw offspring hFiniteMean jumpLaw hSupport hJumpMass
    rw [← (hdriver.law_mark 0).map_eq] at hJ
    exact (integrable_map_measure (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
      (hdriver.measurable_mark 0).aemeasurable).1 hJ
  have hmInd : iIndepFun marks Q := by
    have h := ProbabilityTheory.iIndepFun.precomp (g := Sum.inr) Sum.inr_injective hdriver.indep
    exact h
  have hSL := strong_law_ae marks hmI (fun i j hij => hmInd.indepFun hij)
    (identDistrib_of_hasLaw hdriver.measurable_mark hdriver.law_mark)
  -- interarrivals: truncated SLLN
  set m : ℕ → Ω → ℝ := fun i ω => max (min (arrival i ω) 1) 0 with hm
  have hmeas_m : ∀ i, Measurable (m i) := fun i =>
    ((hdriver.measurable_interarrival i).min measurable_const).max measurable_const
  have hτInd : iIndepFun arrival Q := by
    have h := ProbabilityTheory.iIndepFun.precomp (g := Sum.inl) Sum.inl_injective hdriver.indep
    exact h
  have hmIndep : iIndepFun m Q :=
    hτInd.comp (fun _ x => max (min x 1) 0) (fun _ => (measurable_id.min measurable_const).max
      measurable_const)
  have hmId : ∀ i, IdentDistrib (m i) (m 0) Q Q := fun i =>
    (identDistrib_of_hasLaw hdriver.measurable_interarrival hdriver.law_interarrival i).comp
      ((measurable_id.min measurable_const).max measurable_const)
  have hmInt : Integrable (m 0) Q := by
    refine Integrable.mono' (integrable_const (1:ℝ)) (hmeas_m 0).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [hm, Real.norm_eq_abs]
    rw [abs_le]; constructor
    · linarith [le_max_right (min (arrival 0 ω) 1) 0]
    · exact max_le (min_le_right _ _) zero_le_one
  have hpos := hdriver.ae_interarrival_pos hrate
  have hmean : 0 < ∫ ω, m 0 ω ∂Q := by
    have hnn : 0 ≤ᵐ[Q] m 0 := Eventually.of_forall fun ω => le_max_right _ _
    rw [integral_pos_iff_support_of_nonneg_ae hnn hmInt]
    have hnull : Q (Function.support (m 0))ᶜ = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hpos)
      intro ω hω
      simp only [mem_compl_iff, Function.mem_support, not_not, hm] at hω
      simp only [Set.mem_ofPred_eq, not_forall, not_lt]
      refine ⟨0, ?_⟩
      by_contra h
      push Not at h
      have : 0 < min (arrival 0 ω) 1 := lt_min h one_pos
      have := le_max_left (min (arrival 0 ω) 1) 0
      linarith
    by_contra h
    push Not at h
    have h0 : Q (Function.support (m 0)) = 0 := le_antisymm h zero_le
    have : Q univ = 0 := by
      rw [← union_compl_self (Function.support (m 0))]
      exact measure_union_null h0 hnull
    simp at this
  have hτI : Integrable (arrival 0) Q := by
    have hJ := integrable_exp (rate : ℝ) (by exact_mod_cast hrate)
    rw [← (hdriver.law_interarrival 0).map_eq] at hJ
    exact (integrable_map_measure (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
      (hdriver.measurable_interarrival 0).aemeasurable).1 hJ
  have hτL := strong_law_ae arrival hτI (fun i j hij => hτInd.indepFun hij)
    (identDistrib_of_hasLaw hdriver.measurable_interarrival hdriver.law_interarrival)
  have hmle : m 0 ≤ᵐ[Q] arrival 0 := by
    filter_upwards [hpos] with ω hp
    exact max_le (min_le_left _ _) (hp 0).le
  have ha : 0 < ∫ ω, arrival 0 ω ∂Q :=
    lt_of_lt_of_le hmean (integral_mono_ae hmInt hτI hmle)
  filter_upwards [hSL, hτL, hpos] with ω hS hT hp
  obtain ⟨hN, hR⟩ := ren (fun i => arrival i ω) hp _ ha hT
  refine ⟨(∫ ω, marks 0 ω ∂Q) * (∫ ω, arrival 0 ω ∂Q)⁻¹, ?_⟩
  have := rislln (fun n => ∑ i ∈ Finset.range n, marks i ω) _ _ _
    (by simpa only [smul_eq_mul] using hS) hN hR
  refine this.congr fun t => ?_
  unfold ProbabilityTheory.compoundPoisson piecewisePath
  simp [ProbabilityTheory.arrival]
