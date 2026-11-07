-- Prove2me | solution 1 for HedgePSNV.lemma_ec_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:58:34.890198+00:00
-- url     : https://prove2.me/submissions/230a5c3a-e2f7-4a0d-9e98-b605a75990df

import Mathlib
import Definitions.Def_HedgePSNV_Newsvendor
import Definitions.Def_StochasticOrders_Usual_UsualOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNVEc6

/-- An upper set of reals has a smaller measure under the smaller measure of the usual order. -/
lemma usual_upper {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : Measurable X)
    (h : StochasticOrders.Usual.UsualOrder μ ν X X) (U : Set ℝ) (hU : IsUpperSet U) :
    μ (X ⁻¹' U) ≤ ν (X ⁻¹' U) := by
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · simp [hU0]
  by_cases hbdd : BddBelow U
  · set a := sInf U with ha
    have hIoi : Set.Ioi a ⊆ U := by
      intro c hc
      obtain ⟨u, huU, hu⟩ := exists_lt_of_csInf_lt hUne (show sInf U < c from hc)
      exact hU hu.le huU
    have hIci : U ⊆ Set.Ici a := fun c hc => csInf_le hbdd hc
    by_cases haU : a ∈ U
    · have hUeq : U = Set.Ici a := by
        refine le_antisymm hIci ?_
        intro c hc
        rcases (show a ≤ c from hc).lt_or_eq with h' | h'
        · exact hIoi h'
        · exact h' ▸ haU
      rw [hUeq]
      -- X⁻¹(Ici a) = ⋂ n, X⁻¹(Ioi (a - 1/(n+1)))
      let s : ℕ → Set Ω := fun n => {ω | a - 1 / ((n : ℝ) + 1) < X ω}
      have hs_meas : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt measurable_const hX
      have hanti : Antitone s := by
        intro n m hnm ω hω
        simp only [s, Set.mem_setOf_eq] at hω ⊢
        have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have h2 : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
        have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
        linarith
      have hinter : (⋂ n, s n) = X ⁻¹' Set.Ici a := by
        ext ω
        simp only [s, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
        constructor
        · intro hω
          by_contra hlt
          push Not at hlt
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
          have := hω n
          linarith
        · intro hω n
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
      have tμ := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hs_meas n).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      have tν := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hs_meas n).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      rw [hinter] at tμ tν
      exact le_of_tendsto_of_tendsto' tμ tν (fun n => h _)
    · have hUeq : U = Set.Ioi a := by
        refine le_antisymm ?_ hIoi
        intro c hc
        rcases (show a ≤ c from hIci hc).lt_or_eq with h' | h'
        · exact h'
        · exact absurd (h' ▸ hc) haU
      rw [hUeq]
      exact h a
  · have hUeq : U = Set.univ := by
      refine Set.eq_univ_of_forall fun c => ?_
      obtain ⟨u, huU, hu⟩ : ∃ u ∈ U, u < c := by
        by_contra hcon
        push Not at hcon
        exact hbdd ⟨c, fun u hu => hcon u hu⟩
      exact hU hu.le huU
    subst hUeq
    simp

/-- Monotone functionals are ordered under the usual stochastic order. -/
lemma usual_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (hX : Measurable X)
    (h : StochasticOrders.Usual.UsualOrder μ ν X X) (g : ℝ → ℝ≥0∞) (hg : Monotone g)
    (hgt : ∀ c, g c ≠ ∞) :
    ∫⁻ ω, g (X ω) ∂μ ≤ ∫⁻ ω, g (X ω) ∂ν := by
  set f : ℝ → ℝ := fun c => (g c).toReal with hf
  have hfm : Monotone f := fun a b hab => ENNReal.toReal_mono (hgt b) (hg hab)
  have hgf : ∀ c, g c = ENNReal.ofReal (f c) := fun c => (ENNReal.ofReal_toReal (hgt c)).symm
  simp_rw [hgf]
  have hmeas : Measurable fun ω => f (X ω) := hfm.measurable.comp hX
  rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg)
      hmeas.aemeasurable]
  refine lintegral_mono fun t => ?_
  exact usual_upper μ ν X hX h {c | t < f c} (fun a b hab hb => lt_of_lt_of_le hb (hfm hab))


lemma usual_neg (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hord : StochasticOrders.Usual.UsualOrder ν₁ ν₂ id id) :
    StochasticOrders.Usual.UsualOrder ν₂ ν₁ (fun a : ℝ => -a) (fun a : ℝ => -a) := by
  intro x
  have hset : {a : ℝ | x < -a} = (Set.Ici (-x))ᶜ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Ici, not_le]
    constructor <;> intro h <;> linarith
  have hU := usual_upper ν₁ ν₂ id measurable_id hord (Set.Ici (-x)) (isUpperSet_Ici (-x))
  simp only [Set.preimage_id] at hU
  rw [hset, prob_compl_eq_one_sub measurableSet_Ici, prob_compl_eq_one_sub measurableSet_Ici]
  exact tsub_le_tsub_left hU _

/-- Antitone functionals are reversed by the usual order. -/
lemma anti_lintegral (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hord : StochasticOrders.Usual.UsualOrder ν₁ ν₂ id id) (g : ℝ → ℝ≥0∞) (hg : Antitone g)
    (hgt : ∀ c, g c ≠ ∞) :
    ∫⁻ a, g a ∂ν₂ ≤ ∫⁻ a, g a ∂ν₁ := by
  have h := usual_lintegral ν₂ ν₁ (fun a : ℝ => -a) measurable_neg (usual_neg ν₁ ν₂ hord)
    (fun c => g (-c)) (fun x y hxy => hg (neg_le_neg hxy)) (fun c => hgt _)
  simpa using h

lemma anti_integral (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hord : StochasticOrders.Usual.UsualOrder ν₁ ν₂ id id) (f : ℝ → ℝ) (hf : Antitone f)
    (hf0 : ∀ a, 0 ≤ f a) (hi₁ : Integrable f ν₁) :
    Integrable f ν₂ ∧ ∫ a, f a ∂ν₂ ≤ ∫ a, f a ∂ν₁ := by
  have hle := anti_lintegral ν₁ ν₂ hord (fun a => ENNReal.ofReal (f a))
    (fun x y hxy => ENNReal.ofReal_le_ofReal (hf hxy)) (fun _ => ENNReal.ofReal_ne_top)
  have hfin₁ : ∫⁻ a, ENNReal.ofReal (f a) ∂ν₁ < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).1 hi₁.2
  have hi₂ : Integrable f ν₂ :=
    ⟨hf.measurable.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).2 (hle.trans_lt hfin₁)⟩
  refine ⟨hi₂, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.measurable.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hf.measurable.aestronglyMeasurable]
  exact ENNReal.toReal_mono hfin₁.ne hle

lemma pos_int (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a => max (-a) 0) ν) (R : ℝ) :
    Integrable (fun a => max (R - a) 0) ν := by
  refine (hint.add (integrable_const |R|)).mono' (by fun_prop) (Filter.Eventually.of_forall fun a => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  have h1 := le_max_left (-a) 0
  have h0 := le_max_right (-a) 0
  have h2 := le_abs_self R
  have h3 := abs_nonneg R
  exact max_le (by linarith) (by linarith)

lemma nv_eq (p : HedgePSNV.Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a => max (-a) 0) ν) (P R : ℝ) :
    HedgePSNV.nvValue p ν id P R =
      (P - p.c) * (R - p.b * P) - (P - p.s) * ∫ a, max (R - a) 0 ∂ν := by
  unfold HedgePSNV.nvValue HedgePSNV.payoff
  simp only [id]
  rw [integral_sub (integrable_const _) ((pos_int ν hint R).const_mul _), integral_const,
    integral_const_mul]
  simp

lemma k_anti (R R' : ℝ) (hRR' : R ≤ R') : Antitone fun a : ℝ => max (R' - a) 0 - max (R - a) 0 := by
  intro x y hxy
  simp only
  rcases le_total R' x with h1 | h1 <;> rcases le_total R' y with h2 | h2 <;>
    rcases le_total R x with h3 | h3 <;> rcases le_total R y with h4 | h4 <;>
    simp only [max_eq_left, max_eq_right, sub_nonneg, sub_nonpos, h1, h2, h3, h4] <;>
    linarith

end HedgePSNVEc6

open MeasureTheory ProbabilityTheory HedgePSNV in
theorem solution (p : Params) (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂]
    (hint₁ : Integrable (fun a => max (-a) 0) ν₁)
    (h1₁ : Assumption1 ν₁) (h1₂ : Assumption1 ν₂)
    (hord : StochasticOrders.Usual.UsualOrder ν₁ ν₂ id id)
    (P₂ R₂ : ℝ) (hNV₂ : IsNVMaximizer p ν₂ id P₂ R₂)
    (huniq₂ : ∀ P R : ℝ, IsNVMaximizer p ν₂ id P R → P = P₂ ∧ R = R₂) :
    (∀ P₁ R₁ : ℝ, IsNVMaximizer p ν₁ id P₁ R₁ → P₁ ≤ P₂ ∧ R₁ ≤ R₂) ∧
    ∀ P R : ℝ, p.s ≤ P → nvValue p ν₁ id P R ≤ nvValue p ν₂ id P R := by
  -- integrability under ν₂
  obtain ⟨hint₂, -⟩ := HedgePSNVEc6.anti_integral ν₁ ν₂ hord (fun a => max (-a) 0)
    (fun x y hxy => max_le_max (neg_le_neg hxy) le_rfl) (fun _ => le_max_right _ _) hint₁
  set G₁ : ℝ → ℝ := fun R => ∫ a, max (R - a) 0 ∂ν₁ with hG₁
  set G₂ : ℝ → ℝ := fun R => ∫ a, max (R - a) 0 ∂ν₂ with hG₂
  have hv₁ : ∀ P R, nvValue p ν₁ id P R = (P - p.c) * (R - p.b * P) - (P - p.s) * G₁ R :=
    fun P R => HedgePSNVEc6.nv_eq p ν₁ hint₁ P R
  have hv₂ : ∀ P R, nvValue p ν₂ id P R = (P - p.c) * (R - p.b * P) - (P - p.s) * G₂ R :=
    fun P R => HedgePSNVEc6.nv_eq p ν₂ hint₂ P R
  -- G₂ ≤ G₁
  have hge : ∀ R, G₂ R ≤ G₁ R := fun R =>
    (HedgePSNVEc6.anti_integral ν₁ ν₂ hord (fun a => max (R - a) 0)
      (fun x y (hxy : x ≤ y) => max_le_max (by linarith : R - y ≤ R - x) (le_refl (0 : ℝ)))
      (fun _ => le_max_right _ _) (HedgePSNVEc6.pos_int ν₁ hint₁ R)).2
  -- increments
  have hdiff : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable (fun a => max (-a) 0) ν → ∀ R R',
      ∫ a, (max (R' - a) 0 - max (R - a) 0) ∂ν =
        ∫ a, max (R' - a) 0 ∂ν - ∫ a, max (R - a) 0 ∂ν := by
    intro ν _ hi R R'
    exact integral_sub (HedgePSNVEc6.pos_int ν hi R') (HedgePSNVEc6.pos_int ν hi R)
  have hinc : ∀ R R', R ≤ R' → G₂ R' - G₂ R ≤ G₁ R' - G₁ R := by
    intro R R' hRR'
    have hk0 : ∀ a, 0 ≤ max (R' - a) 0 - max (R - a) 0 := by
      intro a
      have := max_le_max (show R - a ≤ R' - a by linarith) (le_refl (0 : ℝ))
      linarith
    have h := (HedgePSNVEc6.anti_integral ν₁ ν₂ hord (fun a => max (R' - a) 0 - max (R - a) 0)
      (HedgePSNVEc6.k_anti R R' hRR') hk0
      ((HedgePSNVEc6.pos_int ν₁ hint₁ R').sub (HedgePSNVEc6.pos_int ν₁ hint₁ R))).2
    rw [hdiff ν₁ hint₁, hdiff ν₂ hint₂] at h
    exact h
  have hlip : ∀ R R', R ≤ R' → G₁ R' - G₁ R ≤ R' - R := by
    intro R R' hRR'
    have h : ∫ a, (max (R' - a) 0 - max (R - a) 0) ∂ν₁ ≤ ∫ a, (R' - R) ∂ν₁ := by
      refine integral_mono ((HedgePSNVEc6.pos_int ν₁ hint₁ R').sub
        (HedgePSNVEc6.pos_int ν₁ hint₁ R)) (integrable_const _) fun a => ?_
      simp only
      rcases le_total (R' - a) 0 with h1 | h1 <;> rcases le_total (R - a) 0 with h2 | h2 <;>
        simp only [max_eq_left, max_eq_right, h1, h2] <;> linarith
    rw [hdiff ν₁ hint₁] at h
    simpa using h
  refine ⟨fun P₁ R₁ hNV₁ => ?_, fun P R hP => ?_⟩
  · obtain ⟨⟨hc₁, hb₁⟩, hmax₁⟩ := hNV₁
    obtain ⟨⟨hc₂, hb₂⟩, hmax₂⟩ := hNV₂
    have hb := p.hb
    have hsc := p.hsc
    -- the meet and join lie in the domain
    have hmeet : (min P₁ P₂, min R₁ R₂) ∈ HedgePSNV.decisionDomain p := by
      refine ⟨le_min hc₁ hc₂, ?_⟩
      show p.b * min P₁ P₂ ≤ min R₁ R₂
      refine le_min ?_ ?_
      · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hb.le).trans hb₁
      · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hb.le).trans hb₂
    have hjoin : (max P₁ P₂, max R₁ R₂) ∈ HedgePSNV.decisionDomain p := by
      refine ⟨le_trans hc₁ (le_max_left _ _), ?_⟩
      show p.b * max P₁ P₂ ≤ max R₁ R₂
      rcases le_total P₁ P₂ with h | h
      · rw [max_eq_right h]; exact hb₂.trans (le_max_right _ _)
      · rw [max_eq_left h]; exact hb₁.trans (le_max_left _ _)
    have h1 := hmax₁ _ _ hmeet
    -- supermodularity of the ν₁ value
    have hsup : nvValue p ν₁ id (max P₁ P₂) (max R₁ R₂) - nvValue p ν₁ id P₂ R₂ ≥
        nvValue p ν₁ id P₁ R₁ - nvValue p ν₁ id (min P₁ P₂) (min R₁ R₂) := by
      rw [hv₁, hv₁, hv₁, hv₁]
      rcases le_total P₁ P₂ with hP | hP <;> rcases le_total R₁ R₂ with hR | hR <;>
        simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, hP, hR]
      · linarith
      · have := hlip R₂ R₁ hR
        nlinarith [mul_nonneg (sub_nonneg.2 hP) (show 0 ≤ (R₁ - R₂) - (G₁ R₁ - G₁ R₂) by linarith)]
      · have := hlip R₁ R₂ hR
        nlinarith [mul_nonneg (sub_nonneg.2 hP) (show 0 ≤ (R₂ - R₁) - (G₁ R₂ - G₁ R₁) by linarith)]
      · linarith
    -- the difference d = π₂ - π₁ is nondecreasing
    have hd : nvValue p ν₂ id (max P₁ P₂) (max R₁ R₂) - nvValue p ν₂ id P₂ R₂ ≥
        nvValue p ν₁ id (max P₁ P₂) (max R₁ R₂) - nvValue p ν₁ id P₂ R₂ := by
      rw [hv₁, hv₁, hv₂, hv₂]
      have hPm : P₂ ≤ max P₁ P₂ := le_max_right _ _
      have hRm : R₂ ≤ max R₁ R₂ := le_max_right _ _
      have h3 := hinc R₂ (max R₁ R₂) hRm
      have h4 := hge R₂
      have h5 : 0 ≤ P₂ - p.s := by linarith
      nlinarith [mul_nonneg h5 (show 0 ≤ (G₁ (max R₁ R₂) - G₁ R₂) - (G₂ (max R₁ R₂) - G₂ R₂) by
        linarith), mul_nonneg (sub_nonneg.2 hPm) (show 0 ≤ G₁ (max R₁ R₂) - G₂ (max R₁ R₂) by
        linarith [hge (max R₁ R₂)])]
    have hjmax : HedgePSNV.IsNVMaximizer p ν₂ id (max P₁ P₂) (max R₁ R₂) := by
      refine ⟨hjoin, fun P' R' hD => ?_⟩
      have := hmax₂ P' R' hD
      linarith [hsup, hd, h1, this]
    obtain ⟨hPe, hRe⟩ := huniq₂ _ _ hjmax
    exact ⟨max_eq_right_iff.1 hPe, max_eq_right_iff.1 hRe⟩
  · rw [hv₁, hv₂]
    have := hge R
    have h5 : 0 ≤ P - p.s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h5]
