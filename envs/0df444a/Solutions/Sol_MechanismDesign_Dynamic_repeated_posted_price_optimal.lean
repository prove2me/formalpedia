-- Prove2me | solution 1 for MechanismDesign.Dynamic.repeated_posted_price_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:06:10.945777+00:00
-- url     : https://prove2.me/submissions/b095c605-8a28-4ed9-a061-39f18d94aa04

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_RepeatedSale

open MeasureTheory Set

namespace MechanismDesign.Dynamic

def ICg (a b : ℝ) (Q T : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Icc a b, ∀ θ' ∈ Icc a b, θ * Q θ' - T θ' ≤ θ * Q θ - T θ

section Gen
variable {a b : ℝ} {Q T : ℝ → ℝ}

lemma ICg.subgrad (h : ICg a b Q T) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (x * Q x - T x) + (y - x) * Q x ≤ y * Q y - T y := by
  have := h y hy x hx; linarith

lemma ICg.mono (h : ICg a b Q T) : MonotoneOn Q (Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  by_contra hc
  push_neg at hc
  have h1 := h.subgrad hx hy
  have h2 := h.subgrad hy hx
  nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hc)]

lemma ICg.bound (h : ICg a b Q T) {x : ℝ} (hx : x ∈ Icc a b) : |Q x| ≤ |Q a| + |Q b| := by
  have hab : a ≤ b := hx.1.trans hx.2
  have h1 := h.mono ⟨le_rfl, hab⟩ hx hx.1
  have h2 := h.mono hx ⟨hab, le_rfl⟩ hx.2
  rw [abs_le]
  constructor <;> linarith [abs_nonneg (Q a), abs_nonneg (Q b), neg_abs_le (Q a), le_abs_self (Q b)]

lemma ICg.lip (h : ICg a b Q T) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |(y * Q y - T y) - (x * Q x - T x)| ≤ (|Q a| + |Q b|) * |y - x| := by
  have h1 := h.subgrad hx hy
  have h2 := h.subgrad hy hx
  have bx := abs_le.1 (h.bound hx)
  have by' := abs_le.1 (h.bound hy)
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    constructor <;> nlinarith
  · rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_le]
    constructor <;> nlinarith

lemma ICg.lipschitzOnWith (h : ICg a b Q T) :
    LipschitzOnWith (Real.toNNReal (|Q a| + |Q b|)) (fun θ => θ * Q θ - T θ) (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact h.lip hy hx

lemma ICg.hasDerivAt (h : ICg a b Q T) {x : ℝ} (hx : x ∈ Ioo a b)
    (hc : ContinuousWithinAt Q (Icc a b) x) :
    HasDerivAt (fun θ => θ * Q θ - T θ) (Q x) x := by
  have hxI : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hnhds : Icc a b ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have hca : ContinuousAt Q x := hc.continuousAt hnhds
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc0
  have hev : ∀ᶠ y in nhds x, dist (Q y) (Q x) < c := (Metric.tendsto_nhds.1 hca) c hc0
  filter_upwards [hev, hnhds] with y hy hyI
  have h1 := h.subgrad hxI hyI
  have h2 := h.subgrad hyI hxI
  rw [Real.dist_eq] at hy
  simp only [Real.norm_eq_abs, smul_eq_mul]
  have hq := abs_lt.1 hy
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    constructor <;> nlinarith
  · rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_le]
    constructor <;> nlinarith

lemma ICg.rep (h : ICg a b Q T) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    θ * Q θ - T θ = (a * Q a - T a) + ∫ x in a..θ, Q x := by
  have hcount := h.mono.countable_not_continuousWithinAt
  have hcont : ContinuousOn (fun θ => θ * Q θ - T θ) (Icc a θ) :=
    h.lipschitzOnWith.continuousOn.mono (Icc_subset_Icc le_rfl hθ.2)
  have hint : IntervalIntegrable Q volume a θ := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hθ.1]
    exact h.mono.mono (Icc_subset_Icc le_rfl hθ.2)
  have := integral_eq_of_hasDerivAt_off_countable_of_le (fun θ => θ * Q θ - T θ) Q hθ.1
    hcount hcont ?_ hint
  · linarith
  · rintro x ⟨hx, hxs⟩
    have hxI : x ∈ Ioo a b := ⟨hx.1, hx.2.trans_le hθ.2⟩
    apply h.hasDerivAt hxI
    by_contra hc
    exact hxs ⟨Ioo_subset_Icc_self hxI, hc⟩

end Gen

lemma swap_tri {a b : ℝ} (hab : a ≤ b) {Q h : ℝ → ℝ} {C : ℝ} (hQ : Measurable Q)
    (hB : ∀ x, |Q x| ≤ C) (hh : IntervalIntegrable h volume a b) :
    ∫ θ in a..b, (∫ x in a..θ, Q x) * h θ = ∫ x in a..b, Q x * ∫ θ in x..b, h θ := by
  set μ := volume.restrict (Ioc a b) with hμ
  have hhi : Integrable h μ := hh.1
  let F : ℝ → ℝ → ℝ := fun θ x => (if x ≤ θ then Q x else 0) * h θ
  have hF : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hg : Integrable (fun p : ℝ × ℝ => h p.1) (μ.prod μ) := hhi.comp_fst μ
    refine hg.bdd_mul (c := C) ?_ ?_
    · exact (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hQ.comp measurable_snd) measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Real.norm_eq_abs]
      split_ifs
      · exact hB _
      · simpa using (abs_nonneg (Q 0)).trans (hB 0)
  have hsw := integral_integral_swap hF
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  calc ∫ θ in Ioc a b, (∫ x in a..θ, Q x) * h θ = ∫ θ, ∫ x, F θ x ∂μ ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro θ hθ
        simp only [F]
        rw [integral_mul_const]
        congr 1
        rw [intervalIntegral.integral_of_le hθ.1.le]
        have : (fun x => if x ≤ θ then Q x else 0) = indicator (Iic θ) Q := by
          ext x; simp [indicator]
        rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hθ.2]
    _ = ∫ x, ∫ θ, F θ x ∂μ ∂μ := hsw
    _ = ∫ x in Ioc a b, Q x * ∫ θ in x..b, h θ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        simp only [F]
        have : (fun θ => (if x ≤ θ then Q x else 0) * h θ) =
            fun θ => Q x * indicator (Ici x) h θ := by
          ext θ; by_cases hxθ : x ≤ θ <;> simp [indicator, hxθ]
        rw [this, integral_const_mul, setIntegral_indicator measurableSet_Ici,
          intervalIntegral.integral_of_le hx.2]
        congr 1
        have hs : Ioc a b ∩ Ici x = Icc x b := by
          ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨hx.1.trans_le h1, h2⟩, h1⟩
        rw [hs, integral_Icc_eq_integral_Ioc]

lemma ii_bdd_mul {a b C : ℝ} (hab : a ≤ b) {Q g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b)
    (hQ : Measurable Q) (hB : ∀ x, |Q x| ≤ C) :
    IntervalIntegrable (fun x => Q x * g x) volume a b := by
  refine ⟨hg.1.bdd_mul (c := C) hQ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x), ?_⟩
  rw [Ioc_eq_empty (not_lt.2 hab)]; exact integrableOn_empty

lemma layer {a b S M : ℝ} (hab : a ≤ b) {Q φ : ℝ → ℝ} (hQm : Monotone Q)
    (hQ : ∀ x, Q x ∈ Icc 0 S) (hφ : IntervalIntegrable φ volume a b) (hM0 : 0 ≤ M)
    (hΦ : ∀ c ∈ Icc a b, ∫ x in c..b, φ x ≤ M) : ∫ x in a..b, Q x * φ x ≤ S * M := by
  have hS : 0 ≤ S := (hQ a).1.trans (hQ a).2
  set μ := volume.restrict (Ioc a b) with hμ
  set ν := volume.restrict (Ioc 0 S) with hν
  have hQmeas := hQm.measurable
  let F : ℝ → ℝ → ℝ := fun x s => (if s < Q x then 1 else 0) * φ x
  have hF : Integrable (Function.uncurry F) (μ.prod ν) := by
    have hg : Integrable (fun p : ℝ × ℝ => φ p.1) (μ.prod ν) := hφ.1.comp_fst ν
    refine hg.bdd_mul (c := 1) ?_ ?_
    · exact (Measurable.ite (measurableSet_lt measurable_snd (hQmeas.comp measurable_fst))
        measurable_const measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      split_ifs <;> simp
  have hsw := integral_integral_swap hF
  rw [intervalIntegral.integral_of_le hab]
  have step1 : ∫ x in Ioc a b, Q x * φ x = ∫ x, ∫ s, F x s ∂ν ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    simp only [F]
    rw [integral_mul_const]
    congr 1
    have : (fun s => if s < Q x then (1:ℝ) else 0) = indicator (Iio (Q x)) (fun _ => 1) := by
      ext s; simp [indicator]
    rw [this, setIntegral_indicator measurableSet_Iio]
    have hs : Ioc 0 S ∩ Iio (Q x) = Ioo 0 (Q x) := by
      ext s; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le.trans (hQ x).2⟩, h2⟩
    rw [hs]
    simp [(hQ x).1]
  have hinner : ∀ s, ∫ x, F x s ∂μ ≤ M := by
    intro s
    set A := {x | s < Q x} with hA
    have hAm : MeasurableSet A := measurableSet_lt measurable_const hQmeas
    have : (fun x => F x s) = indicator A φ := by
      ext x; simp only [F, indicator, hA, mem_setOf_eq]; split_ifs <;> simp
    rw [this, setIntegral_indicator hAm]
    by_cases hne : (Ioc a b ∩ A).Nonempty
    · have hbdd : BddBelow (Ioc a b ∩ A) := ⟨a, fun y hy => hy.1.1.le⟩
      set c := sInf (Ioc a b ∩ A) with hc
      have hac : a ≤ c := le_csInf hne (fun y hy => hy.1.1.le)
      have hcb : c ≤ b := by
        obtain ⟨y, hy⟩ := hne
        exact (csInf_le hbdd hy).trans hy.1.2
      have hsub1 : Ioc c b ⊆ Ioc a b ∩ A := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne hx.1
        refine ⟨⟨hac.trans_lt hx.1, hx.2⟩, ?_⟩
        exact lt_of_lt_of_le hy.2 (hQm hyx.le)
      have hsub2 : Ioc a b ∩ A ⊆ Icc c b := fun x hx => ⟨csInf_le hbdd hx, hx.1.2⟩
      have hae : (Ioc a b ∩ A : Set ℝ) =ᵐ[volume] (Ioc c b : Set ℝ) :=
        Filter.EventuallyLE.antisymm
          (hsub2.eventuallyLE.trans (Ioc_ae_eq_Icc (a := c) (b := b)).symm.le)
          hsub1.eventuallyLE
      rw [setIntegral_congr_set hae, ← intervalIntegral.integral_of_le hcb]
      exact hΦ c ⟨hac, hcb⟩
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp [hM0]
  have hint2 : Integrable (fun s => ∫ x, F x s ∂μ) ν := hF.integral_prod_right
  calc ∫ x in Ioc a b, Q x * φ x = ∫ s, ∫ x, F x s ∂μ ∂ν := step1.trans hsw
    _ ≤ ∫ s, M ∂ν := integral_mono hint2 (integrable_const M) hinner
    _ = S * M := by simp [hν, hS]

namespace RepVal
variable {θlo θhi : ℝ}

lemma tail (D : ValuationDist θlo θhi) {x : ℝ} (hx : x ∈ Icc θlo θhi) :
    ∫ θ in x..θhi, D.f θ = 1 - D.F x := by
  have h1 : IntervalIntegrable D.f volume θlo x :=
    D.f_integrable.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (hx.1.trans hx.2)]; exact Icc_subset_Icc le_rfl hx.2)
  have h2 : IntervalIntegrable D.f volume x θhi :=
    D.f_integrable.mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le (hx.1.trans hx.2)]; exact Icc_subset_Icc hx.1 le_rfl)
  rw [D.F_eq x hx, ← D.f_total, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

lemma fint (D : ValuationDist θlo θhi) {c d : ℝ} (hc : θlo ≤ c) (hcd : c ≤ d) (hd : d ≤ θhi) :
    IntervalIntegrable D.f volume c d :=
  D.f_integrable.mono_set (by
    rw [uIcc_of_le hcd, uIcc_of_le (hc.trans (hcd.trans hd))]; exact Icc_subset_Icc hc hd)

/-- `∫_c^b (x f(x) - (1 - F(x))) dx = c (1 - F c)`. -/
lemma phi_tail (D : ValuationDist θlo θhi) {c : ℝ} (hc : c ∈ Icc θlo θhi) :
    ∫ x in c..θhi, (x * D.f x - ∫ θ in x..θhi, D.f θ) = c * (1 - D.F c) := by
  have hfi := fint D hc.1 hc.2 le_rfl
  have hxf : IntervalIntegrable (fun x => x * D.f x) volume c θhi :=
    hfi.continuousOn_mul continuousOn_id
  have htc : ContinuousOn (fun x => ∫ θ in x..θhi, D.f θ) (uIcc c θhi) :=
    intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').1 hfi)
  have hti : IntervalIntegrable (fun x => ∫ θ in x..θhi, D.f θ) volume c θhi :=
    htc.intervalIntegrable
  have hsw := swap_tri hc.2 (Q := fun _ => (1:ℝ)) (C := 1) measurable_const (by simp) hfi
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, one_mul] at hsw
  rw [intervalIntegral.integral_sub hxf hti, ← hsw]
  have : ∫ θ in c..θhi, (θ - c) * D.f θ = (∫ θ in c..θhi, θ * D.f θ) - c * ∫ θ in c..θhi, D.f θ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hxf
      (hfi.const_mul c)]
    congr 1; ext θ; ring
  rw [this, tail D hc]; ring

end RepVal

open RepVal in
theorem rpp_core {θlo θhi : ℝ} (D : ValuationDist θlo θhi) (T : ℕ)
    (hT : 0 < T) (δ : ℝ) (hδ : δ ∈ Set.Ico (0 : ℝ) 1) (pstar : ℝ)
    (hp : pstar ∈ Set.Icc θlo θhi)
    (hmax : IsMaxOn (fun p => p * (1 - D.F p)) (Set.Icc θlo θhi) pstar) :
    (repeatedPostedPrice T θlo θhi pstar).Admissible ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIC δ ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIR δ ∧
      ∀ m : RepMechanism T θlo θhi, m.Admissible → m.IsIC δ → m.IsIR δ →
        m.revenue D δ ≤ (repeatedPostedPrice T θlo θhi pstar).revenue D δ := by
  have hab : θlo ≤ θhi := D.lo_lt_hi.le
  have hδ0 : 0 ≤ δ := hδ.1
  set S : ℝ := ∑ k : Fin T, δ ^ (k : ℕ) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => pow_nonneg hδ0 _
  have hpay : ∀ (m : RepMechanism T θlo θhi) θ θ', m.payoff δ θ θ' =
      θ * (∑ k : Fin T, δ ^ (k : ℕ) * m.q k θ') - ∑ k : Fin T, δ ^ (k : ℕ) * m.t k θ' := by
    intro m θ θ'
    unfold RepMechanism.payoff
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k θ _
    simp only [repeatedPostedPrice]
    split_ifs <;> norm_num
  · intro k
    exact ⟨Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
      measurable_const, Measurable.ite (measurableSet_le measurable_const measurable_id)
      measurable_const measurable_const⟩
  · intro θ _ θ' _
    unfold RepMechanism.u RepMechanism.payoff
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ0 _)
    simp only [repeatedPostedPrice]
    split_ifs with h1 h2 h2 <;> linarith
  · intro θ _
    unfold RepMechanism.u RepMechanism.payoff
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (pow_nonneg hδ0 _)
    simp only [repeatedPostedPrice]
    split_ifs with h1 <;> linarith
  intro m hm hic hir
  -- revenue of the posted price
  have hrev_star : (repeatedPostedPrice T θlo θhi pstar).revenue D δ =
      S * (pstar * (1 - D.F pstar)) := by
    unfold RepMechanism.revenue
    have : (fun θ => (∑ k : Fin T, δ ^ (k : ℕ) * (repeatedPostedPrice T θlo θhi pstar).t k θ) *
        D.f θ) = fun θ => (S * pstar) * indicator (Ici pstar) D.f θ := by
      ext θ
      simp only [repeatedPostedPrice, indicator, mem_Ici, hSdef]
      split_ifs <;> simp [Finset.sum_mul]
    rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hab,
      setIntegral_indicator measurableSet_Ici]
    have hs : (Ioc θlo θhi ∩ Ici pstar : Set ℝ) =ᵐ[volume] (Ioc pstar θhi : Set ℝ) := by
      have h1 : Ioc pstar θhi ⊆ Ioc θlo θhi ∩ Ici pstar :=
        fun x hx => ⟨⟨hp.1.trans_lt hx.1, hx.2⟩, hx.1.le⟩
      have h2 : Ioc θlo θhi ∩ Ici pstar ⊆ Icc pstar θhi := fun x hx => ⟨hx.2, hx.1.2⟩
      exact Filter.EventuallyLE.antisymm
        (h2.eventuallyLE.trans (Ioc_ae_eq_Icc (a := pstar) (b := θhi)).symm.le) h1.eventuallyLE
    rw [setIntegral_congr_set hs, ← intervalIntegral.integral_of_le hp.2, tail D hp]
    ring
  rw [hrev_star]
  -- aggregate mechanism
  set Qs : ℝ → ℝ := fun θ => ∑ k : Fin T, δ ^ (k : ℕ) * m.q k θ with hQs
  set Ts : ℝ → ℝ := fun θ => ∑ k : Fin T, δ ^ (k : ℕ) * m.t k θ with hTs
  have G : ICg θlo θhi Qs Ts := by
    intro θ hθ θ' hθ'
    have := hic θ hθ θ' hθ'
    unfold RepMechanism.u at this
    rw [hpay, hpay] at this
    exact this
  have hQsI : ∀ θ ∈ Icc θlo θhi, Qs θ ∈ Icc 0 S := by
    intro θ hθ
    constructor
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hδ0 _) (hm.1 k θ hθ).1
    · rw [hSdef]
      apply Finset.sum_le_sum
      intro k _
      have := (hm.1 k θ hθ).2
      nlinarith [pow_nonneg hδ0 (k : ℕ)]
  set Q' : ℝ → ℝ := fun x => Qs (projIcc θlo θhi hab x) with hQ'
  have hQ'mono : Monotone Q' := fun x y hxy =>
    G.mono (projIcc θlo θhi hab x).2 (projIcc θlo θhi hab y).2 (monotone_projIcc hab hxy)
  have hQ'I : ∀ x, Q' x ∈ Icc 0 S := fun x => hQsI _ (projIcc θlo θhi hab x).2
  have hQ'B : ∀ x, |Q' x| ≤ S := fun x => by
    rw [abs_le]; constructor <;> linarith [(hQ'I x).1, (hQ'I x).2]
  have hQ'eq : ∀ x ∈ Icc θlo θhi, Q' x = Qs x := by
    intro x hx; simp [hQ', projIcc_of_mem hab hx]
  set V0 := θlo * Qs θlo - Ts θlo with hV0
  have hV0nn : 0 ≤ V0 := by
    have := hir θlo ⟨le_rfl, hab⟩
    unfold RepMechanism.u at this
    rw [hpay] at this
    exact this
  set W : ℝ → ℝ := fun θ => ∫ x in θlo..θ, Q' x with hW
  have hWc : Continuous W := intervalIntegral.continuous_primitive
    (fun _ _ => hQ'mono.intervalIntegrable) θlo
  have hTsr : ∀ θ ∈ Icc θlo θhi, Ts θ = θ * Q' θ - V0 - W θ := by
    intro θ hθ
    have hr := G.rep hθ
    have hWθ : W θ = ∫ x in θlo..θ, Qs x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hθ.1] at hx
      exact hQ'eq x ⟨hx.1, hx.2.trans hθ.2⟩
    rw [hWθ, hQ'eq θ hθ]
    linarith
  have hfi := D.f_integrable
  have hxf : IntervalIntegrable (fun x => x * D.f x) volume θlo θhi :=
    hfi.continuousOn_mul continuousOn_id
  have i1 : IntervalIntegrable (fun x => Q' x * (x * D.f x)) volume θlo θhi :=
    ii_bdd_mul hab hxf hQ'mono.measurable hQ'B
  have i3 : IntervalIntegrable (fun x => W x * D.f x) volume θlo θhi :=
    hfi.continuousOn_mul hWc.continuousOn
  have htc : ContinuousOn (fun x => ∫ θ in x..θhi, D.f θ) (uIcc θlo θhi) :=
    intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').1 hfi)
  have i4 : IntervalIntegrable (fun x => Q' x * ∫ θ in x..θhi, D.f θ) volume θlo θhi :=
    ii_bdd_mul hab htc.intervalIntegrable hQ'mono.measurable hQ'B
  have hrev : m.revenue D δ = (∫ x in θlo..θhi, Q' x * (x * D.f x - ∫ θ in x..θhi, D.f θ)) - V0 := by
    unfold RepMechanism.revenue
    have e1 : ∫ θ in θlo..θhi, (∑ k : Fin T, δ ^ (k : ℕ) * m.t k θ) * D.f θ =
        ∫ θ in θlo..θhi, (Q' θ * (θ * D.f θ) - V0 * D.f θ - W θ * D.f θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le hab] at hθ
      have := hTsr θ hθ
      simp only [hTs] at this
      simp only
      rw [this]; ring
    rw [e1, intervalIntegral.integral_sub (i1.sub (hfi.const_mul V0)) i3,
      intervalIntegral.integral_sub i1 (hfi.const_mul V0), intervalIntegral.integral_const_mul,
      D.f_total, swap_tri hab hQ'mono.measurable hQ'B hfi]
    have : ∫ x in θlo..θhi, Q' x * (x * D.f x - ∫ θ in x..θhi, D.f θ) =
        (∫ x in θlo..θhi, Q' x * (x * D.f x)) - ∫ x in θlo..θhi, Q' x * ∫ θ in x..θhi, D.f θ := by
      rw [← intervalIntegral.integral_sub i1 i4]
      congr 1; ext x; ring
    rw [this]; ring
  rw [hrev]
  have hφ : IntervalIntegrable (fun x => x * D.f x - ∫ θ in x..θhi, D.f θ) volume θlo θhi :=
    hxf.sub htc.intervalIntegrable
  have hM0 : 0 ≤ pstar * (1 - D.F pstar) := by
    have := hmax (show θhi ∈ Icc θlo θhi from ⟨hab, le_rfl⟩)
    simp only [mem_setOf_eq] at this
    have hF1 : D.F θhi = 1 := by rw [D.F_eq θhi ⟨hab, le_rfl⟩, D.f_total]
    rw [hF1] at this
    linarith
  have hL := layer hab hQ'mono hQ'I hφ hM0 (fun c hc => by
    rw [phi_tail D hc]
    exact hmax hc)
  linarith

end MechanismDesign.Dynamic

open MechanismDesign.Dynamic


theorem solution {θlo θhi : ℝ} (D : ValuationDist θlo θhi) (T : ℕ)
    (hT : 0 < T) (δ : ℝ) (hδ : δ ∈ Set.Ico (0 : ℝ) 1) (pstar : ℝ)
    (hp : pstar ∈ Set.Icc θlo θhi)
    (hmax : IsMaxOn (fun p => p * (1 - D.F p)) (Set.Icc θlo θhi) pstar) :
    (repeatedPostedPrice T θlo θhi pstar).Admissible ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIC δ ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIR δ ∧
      ∀ m : RepMechanism T θlo θhi, m.Admissible → m.IsIC δ → m.IsIR δ →
        m.revenue D δ ≤ (repeatedPostedPrice T θlo θhi pstar).revenue D δ := by
  exact rpp_core D T hT δ hδ pstar hp hmax
