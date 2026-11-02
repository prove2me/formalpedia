-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.consumption_investment_structure_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:21:30.031454+00:00
-- url     : https://prove2.me/submissions/1d5b5cf1-22f3-4815-93c3-a7560c19710a

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

structure Good (u : ℝ → ℝ) : Prop where
  mono : StrictMonoOn u (Set.Ici 0)
  conc : StrictConcaveOn ℝ (Set.Ici 0) u
  cont : ContinuousOn u (Set.Ici 0)

noncomputable def tl (u : ℝ → ℝ) (y : ℝ) : ℝ := u (max y 0)

lemma tl_of_nonneg {u : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y) : tl u y = u y := by simp [tl, hy]

lemma tl_cont {u : ℝ → ℝ} (h : Good u) : Continuous (tl u) :=
  h.cont.comp_continuous (by fun_prop) (fun y => Set.mem_Ici.2 (le_max_right _ _))

lemma tl_ge {u : ℝ → ℝ} (h : Good u) (y : ℝ) : u 0 ≤ tl u y :=
  h.mono.monotoneOn (Set.self_mem_Ici) (Set.mem_Ici.2 (le_max_right _ _)) (le_max_right _ _)

lemma good_upper {u : ℝ → ℝ} (h : Good u) {z : ℝ} (hz : 0 ≤ z) :
    u z ≤ u 0 + (u 1 - u 0) * (1 + z) := by
  have hL : u 0 < u 1 := h.mono (by simp) (by simp) (by norm_num)
  rcases le_total z 1 with h1 | h1
  · have := h.mono.monotoneOn (Set.mem_Ici.2 hz) (Set.mem_Ici.2 zero_le_one) h1
    nlinarith
  · have hz0 : 0 < z := by linarith
    rcases eq_or_lt_of_le h1 with h2 | h2
    · subst h2; nlinarith
    have h3 := h.conc.concaveOn.2 (Set.mem_Ici.2 hz) (Set.mem_Ici.2 le_rfl)
      (show (0 : ℝ) ≤ 1 / z by positivity)
      (show (0 : ℝ) ≤ 1 - 1 / z by rw [sub_nonneg, div_le_one hz0]; exact h1) (by ring)
    have h4 : (1 / z) • z + (1 - 1 / z) • (0 : ℝ) = 1 := by
      simp only [smul_eq_mul]; field_simp; simp
    rw [h4] at h3
    simp only [smul_eq_mul] at h3
    have h5 : z * ((1 / z) * u z + (1 - 1 / z) * u 0) ≤ z * u 1 :=
      mul_le_mul_of_nonneg_left h3 hz
    have h6 : z * ((1 / z) * u z + (1 - 1 / z) * u 0) = u z + (z - 1) * u 0 := by
      field_simp
    rw [h6] at h5
    nlinarith

lemma tl_bound {u : ℝ → ℝ} (h : Good u) (y : ℝ) :
    |tl u y| ≤ |u 0| + (u 1 - u 0) * (1 + |y|) := by
  have hL : u 0 < u 1 := h.mono (by simp) (by simp) (by norm_num)
  have h1 := tl_ge h y
  have h2 := good_upper h (le_max_right y 0)
  have h3 : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have h4 : (u 1 - u 0) * (1 + max y 0) ≤ (u 1 - u 0) * (1 + |y|) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h5 : tl u y = u (max y 0) := rfl
  have h6 : 0 ≤ (u 1 - u 0) * (1 + |y|) := mul_nonneg (by linarith) (by positivity)
  rw [abs_le]
  constructor
  · have := neg_abs_le (u 0); linarith
  · have := le_abs_self (u 0); linarith

abbrev dot {d : ℕ} (a u : Fin d → ℝ) : ℝ := ∑ k, a k * u k

lemma dot_bound {d : ℕ} (a u : Fin d → ℝ) : |dot a u| ≤ ‖a‖ * ∑ k, |u k| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm a k) (abs_nonneg _)

lemma dot_cont {d : ℕ} (u : Fin d → ℝ) : Continuous (fun a : Fin d → ℝ => dot a u) := by
  unfold dot; fun_prop

lemma dot_meas {d : ℕ} (a : Fin d → ℝ) : Measurable (fun u : Fin d → ℝ => dot a u) := by
  unfold dot; fun_prop

lemma dot_add {d : ℕ} (a b u : Fin d → ℝ) : dot (a + b) u = dot a u + dot b u := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_sub {d : ℕ} (a b u : Fin d → ℝ) : dot (a - b) u = dot a u - dot b u := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul {d : ℕ} (t : ℝ) (a u : Fin d → ℝ) : dot (t • a) u = t * dot a u := by
  simp [dot, Finset.mul_sum, mul_assoc]

section OneStep

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {R : Ω → Fin d → ℝ}

lemma int_ok (hRm : Measurable R) (hRi : Integrable (fun ω => ∑ k, |R ω k|) P)
    {h : ℝ → ℝ} (hc : Continuous h) {A B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, |h y| ≤ A + B * |y|)
    (t : ℝ) (a : Fin d → ℝ) : Integrable (fun ω => h (t + dot a (R ω))) P := by
  have hm : Measurable (fun ω => h (t + dot a (R ω))) :=
    hc.measurable.comp (measurable_const.add ((dot_meas a).comp hRm))
  refine Integrable.mono' (g := fun ω => A + B * (|t| + ‖a‖ * ∑ k, |R ω k|))
    ((integrable_const _).add (((integrable_const _).add (hRi.const_mul _)).const_mul _))
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (hb _).trans ?_
  have h1 := abs_add_le t (dot a (R ω))
  have h2 := dot_bound a (R ω)
  have h3 : |t + dot a (R ω)| ≤ |t| + ‖a‖ * ∑ k, |R ω k| := by linarith
  have := mul_le_mul_of_nonneg_left h3 hB
  linarith

lemma int_cont (hRm : Measurable R) (hRi : Integrable (fun ω => ∑ k, |R ω k|) P)
    {h : ℝ → ℝ} (hc : Continuous h) {A B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, |h y| ≤ A + B * |y|) :
    Continuous (fun p : ℝ × (Fin d → ℝ) => ∫ ω, h (p.1 + dot p.2 (R ω)) ∂P) := by
  rw [continuous_iff_continuousAt]
  intro p0
  refine continuousAt_of_dominated
    (bound := fun ω => A + B * ((‖p0‖ + 1) * (1 + ∑ k, |R ω k|))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p =>
      (hc.measurable.comp (measurable_const.add ((dot_meas p.2).comp hRm))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds p0 one_pos] with p hp
    refine Filter.Eventually.of_forall fun ω => ?_
    have hp' : ‖p‖ ≤ ‖p0‖ + 1 := by
      have := norm_le_norm_add_norm_sub p0 p
      have h2 : ‖p - p0‖ < 1 := by simpa [dist_eq_norm] using hp
      have := norm_le_norm_add_norm_sub' p p0
      linarith
    rw [Real.norm_eq_abs]
    refine (hb _).trans ?_
    have h1 := abs_add_le p.1 (dot p.2 (R ω))
    have h2 := dot_bound p.2 (R ω)
    have h3 : |p.1| ≤ ‖p‖ := norm_fst_le p
    have h4 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
    have hS : 0 ≤ ∑ k, |R ω k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h5 : ‖p.2‖ * ∑ k, |R ω k| ≤ (‖p0‖ + 1) * ∑ k, |R ω k| :=
      mul_le_mul_of_nonneg_right (h4.trans hp') hS
    have h6 : |p.1 + dot p.2 (R ω)| ≤ (‖p0‖ + 1) * (1 + ∑ k, |R ω k|) := by
      nlinarith
    have := mul_le_mul_of_nonneg_left h6 hB
    linarith
  · exact (integrable_const _).add (((integrable_const _).add hRi).const_mul _ |>.const_mul _)
  · refine Filter.Eventually.of_forall fun ω => Continuous.continuousAt ?_
    have := dot_cont (R ω)
    exact hc.comp (continuous_fst.add (this.comp continuous_snd))

noncomputable def psi (P : Measure Ω) (R : Ω → Fin d → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  ∫ ω, max (-(p.1 + dot p.2 (R ω))) 0 ∂P

lemma neg_bd (y : ℝ) : |max (-y) 0| ≤ 0 + 1 * |y| := by
  rw [abs_of_nonneg (le_max_right _ _), zero_add, one_mul]
  exact max_le (neg_le_abs y) (abs_nonneg y)

lemma psi_cont (hRm : Measurable R) (hRi : Integrable (fun ω => ∑ k, |R ω k|) P) :
    Continuous (psi P R) :=
  int_cont (h := fun y => max (-y) 0) hRm hRi (by fun_prop) zero_le_one neg_bd

lemma psi_zero_iff (hRm : Measurable R) (hRi : Integrable (fun ω => ∑ k, |R ω k|) P)
    (p : ℝ × (Fin d → ℝ)) : psi P R p = 0 ↔ ∀ᵐ ω ∂P, 0 ≤ p.1 + dot p.2 (R ω) := by
  unfold psi
  have h := integral_eq_zero_iff_of_nonneg (μ := P)
    (f := fun ω => max (-(p.1 + dot p.2 (R ω))) 0) (fun ω => le_max_right _ _)
    (int_ok (h := fun y => max (-y) 0) hRm hRi (by fun_prop) zero_le_one neg_bd p.1 p.2)
  rw [h]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun ω => ?_)
  show max (-(p.1 + dot p.2 (R ω))) 0 = 0 ↔ _
  rw [max_eq_right_iff]
  constructor <;> intro h' <;> linarith

def Ker (P : Measure Ω) (R : Ω → Fin d → ℝ) : Submodule ℝ (Fin d → ℝ) where
  carrier := {a | ∀ᵐ ω ∂P, dot a (R ω) = 0}
  add_mem' := by
    intro a b ha hb
    have ha' : ∀ᵐ ω ∂P, dot a (R ω) = 0 := ha
    have hb' : ∀ᵐ ω ∂P, dot b (R ω) = 0 := hb
    show ∀ᵐ ω ∂P, dot (a + b) (R ω) = 0
    filter_upwards [ha', hb'] with ω h1 h2
    rw [dot_add, h1, h2, add_zero]
  zero_mem' := by simp [dot]
  smul_mem' := by
    intro t a ha
    have ha' : ∀ᵐ ω ∂P, dot a (R ω) = 0 := ha
    show ∀ᵐ ω ∂P, dot (t • a) (R ω) = 0
    filter_upwards [ha'] with ω h1
    rw [dot_smul, h1, mul_zero]

lemma na_zero (hNA : NoArbitrageOnePeriodCI P R) {a : Fin d → ℝ}
    (h : ∀ᵐ ω ∂P, 0 ≤ dot a (R ω)) : ∀ᵐ ω ∂P, dot a (R ω) = 0 := by
  have h0 : P {ω | 0 < dot a (R ω)} = 0 := by
    by_contra hne
    exact hNA ⟨a, h, pos_iff_ne_zero.2 hne⟩
  have h2 : ∀ᵐ ω ∂P, ¬ 0 < dot a (R ω) := by rw [ae_iff]; simpa using h0
  filter_upwards [h, h2] with ω h3 h4
  exact le_antisymm (not_lt.1 h4) h3

structure Ctx (P : Measure Ω) (R : Ω → Fin d → ℝ) (q : ℝ) (Uc w : ℝ → ℝ)
    (K' : Submodule ℝ (Fin d → ℝ)) : Prop where
  hRm : Measurable R
  hRi : Integrable (fun ω => ∑ k, |R ω k|) P
  hNA : NoArbitrageOnePeriodCI P R
  hq : 0 < q
  hU : Good Uc
  hw : Good w
  hK : IsCompl (Ker P R) K'

variable {q : ℝ} {Uc w : ℝ → ℝ} {K' : Submodule ℝ (Fin d → ℝ)}

lemma psi_nonneg (p : ℝ × (Fin d → ℝ)) : 0 ≤ psi P R p :=
  integral_nonneg fun _ => le_max_right _ _

lemma psi_homog (t : ℝ) (ht : 0 ≤ t) (a : Fin d → ℝ) :
    psi P R (0, t • a) = t * psi P R (0, a) := by
  unfold psi
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [dot_smul, zero_add]
  rw [mul_max_of_nonneg _ _ ht]
  simp

lemma Ctx.ker_eq_zero (C : Ctx P R q Uc w K') {a : Fin d → ℝ} (h : a ∈ K')
    (h0 : ∀ᵐ ω ∂P, dot a (R ω) = 0) : a = 0 :=
  (Submodule.disjoint_def.1 C.hK.disjoint) a h0 h

lemma Ctx.psi_pos (C : Ctx P R q Uc w K') {a : Fin d → ℝ} (h : a ∈ K') (hne : a ≠ 0) :
    0 < psi P R (0, a) := by
  refine lt_of_le_of_ne (psi_nonneg _) fun h0 => hne ?_
  have := (psi_zero_iff C.hRm C.hRi (0, a)).1 h0.symm
  refine C.ker_eq_zero h (na_zero C.hNA ?_)
  simpa using this

lemma Ctx.bound (C : Ctx P R q Uc w K') :
    ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K', m * ‖a‖ ≤ psi P R (0, a) := by
  have hcomp : IsCompact (Metric.sphere (0 : Fin d → ℝ) 1 ∩ K') :=
    (isCompact_sphere 0 1).inter_right K'.closed_of_finiteDimensional
  have hf : Continuous (fun a : Fin d → ℝ => psi P R (0, a)) :=
    (psi_cont C.hRm C.hRi).comp (by fun_prop)
  have hsph : ∀ a ∈ K', a ≠ 0 → (‖a‖⁻¹ • a) ∈ Metric.sphere (0 : Fin d → ℝ) 1 ∩ K' := by
    intro a ha hne
    refine ⟨?_, K'.smul_mem _ ha⟩
    have : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 hne
    simp [norm_smul, this]
  have hdec : ∀ a : Fin d → ℝ, a ≠ 0 → psi P R (0, a) = ‖a‖ * psi P R (0, ‖a‖⁻¹ • a) := by
    intro a hne
    rw [← psi_homog _ (norm_nonneg _), smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hne), one_smul]
  rcases (Metric.sphere (0 : Fin d → ℝ) 1 ∩ K').eq_empty_or_nonempty with hE | hE
  · refine ⟨1, one_pos, fun a ha => ?_⟩
    by_cases hne : a = 0
    · simpa [hne] using psi_nonneg _
    · have := hsph a ha hne
      rw [hE] at this
      exact this.elim
  · obtain ⟨a0, ha0, hmin⟩ := hcomp.exists_isMinOn hE hf.continuousOn
    have ha0ne : a0 ≠ 0 := by
      intro h
      have := ha0.1
      simp [h] at this
    refine ⟨_, C.psi_pos ha0.2 ha0ne, fun a ha => ?_⟩
    by_cases hne : a = 0
    · simpa [hne] using psi_nonneg _
    · rw [hdec a hne, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hsph a ha hne)) (norm_nonneg _)

lemma psi_le (hRm : Measurable R) (hRi : Integrable (fun ω => ∑ k, |R ω k|) P)
    {t : ℝ} {a : Fin d → ℝ} (ht : 0 ≤ t)
    (h : ∀ᵐ ω ∂P, 0 ≤ t + dot a (R ω)) : psi P R (0, a) ≤ t := by
  have : psi P R (0, a) ≤ ∫ _ω, t ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => le_max_right _ _)
      (integrable_const _) ?_
    filter_upwards [h] with ω hω
    refine max_le ?_ ht
    simp only [zero_add]
    linarith
  simpa using this

noncomputable def Ja (P : Measure Ω) (R : Ω → Fin d → ℝ) (q : ℝ) (w : ℝ → ℝ) (x c : ℝ)
    (a : Fin d → ℝ) : ℝ := ∫ ω, tl w (q * (x - c + dot a (R ω))) ∂P

noncomputable def Jt (P : Measure Ω) (R : Ω → Fin d → ℝ) (q : ℝ) (Uc w : ℝ → ℝ) (x c : ℝ)
    (a : Fin d → ℝ) : ℝ := tl Uc c + Ja P R q w x c a

lemma tlq_bd {w : ℝ → ℝ} (hw : Good w) (hq : 0 < q) (y : ℝ) :
    |tl w (q * y)| ≤ (|w 0| + (w 1 - w 0)) + ((w 1 - w 0) * q) * |y| := by
  refine (tl_bound hw _).trans (le_of_eq ?_)
  rw [abs_mul, abs_of_pos hq]; ring

lemma L_nonneg {w : ℝ → ℝ} (hw : Good w) (hq : 0 < q) : 0 ≤ (w 1 - w 0) * q := by
  have hL : w 0 < w 1 := hw.mono (by simp) (by simp) (by norm_num)
  exact mul_nonneg (by linarith) hq.le

lemma Ctx.Ja_int (C : Ctx P R q Uc w K') (t : ℝ) (a : Fin d → ℝ) :
    Integrable (fun ω => tl w (q * (t + dot a (R ω)))) P :=
  int_ok (h := fun y => tl w (q * y)) C.hRm C.hRi
    ((tl_cont C.hw).comp (by fun_prop)) (L_nonneg C.hw C.hq) (tlq_bd C.hw C.hq) t a

lemma Ctx.Jt_cont (C : Ctx P R q Uc w K') :
    Continuous (fun p : ℝ × ℝ × (Fin d → ℝ) => Jt P R q Uc w p.1 p.2.1 p.2.2) := by
  have h1 := int_cont (h := fun y => tl w (q * y)) C.hRm C.hRi
    ((tl_cont C.hw).comp (by fun_prop)) (L_nonneg C.hw C.hq) (tlq_bd C.hw C.hq)
  have h2 : Continuous (fun p : ℝ × ℝ × (Fin d → ℝ) => ((p.1 - p.2.1, p.2.2) : ℝ × (Fin d → ℝ))) := by
    fun_prop
  exact ((tl_cont C.hU).comp (by fun_prop)).add (h1.comp h2)

def Feas (P : Measure Ω) (R : Ω → Fin d → ℝ) (x c : ℝ) (a : Fin d → ℝ) : Prop :=
  0 ≤ c ∧ c ≤ x ∧ ∀ᵐ ω ∂P, 0 ≤ x - c + dot a (R ω)

lemma conc_pt {u : ℝ → ℝ} (hu : Good u) {y1 y2 s t : ℝ} (h1 : 0 ≤ y1) (h2 : 0 ≤ y2)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    s * u y1 + t * u y2 ≤ u (s * y1 + t * y2) ∧
      (y1 ≠ y2 → s * u y1 + t * u y2 < u (s * y1 + t * y2)) := by
  constructor
  · simpa using hu.conc.concaveOn.2 (Set.mem_Ici.2 h1) (Set.mem_Ici.2 h2) hs.le ht.le hst
  · intro hne
    simpa using hu.conc.2 (Set.mem_Ici.2 h1) (Set.mem_Ici.2 h2) hne hs ht hst

lemma Ctx.sc (C : Ctx P R q Uc w K') {x1 c1 x2 c2 s t : ℝ} {a1 a2 : Fin d → ℝ}
    (h1 : Feas P R x1 c1 a1) (h2 : Feas P R x2 c2 a2) (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
    (hne : ¬ (c1 = c2 ∧ ∀ᵐ ω ∂P, x1 - c1 + dot a1 (R ω) = x2 - c2 + dot a2 (R ω))) :
    s * Jt P R q Uc w x1 c1 a1 + t * Jt P R q Uc w x2 c2 a2 <
      Jt P R q Uc w (s * x1 + t * x2) (s * c1 + t * c2) (s • a1 + t • a2) := by
  set F1 : Ω → ℝ := fun ω => tl w (q * (x1 - c1 + dot a1 (R ω))) with hF1
  set F2 : Ω → ℝ := fun ω => tl w (q * (x2 - c2 + dot a2 (R ω))) with hF2
  set F : Ω → ℝ := fun ω => tl w (q * ((s * x1 + t * x2) - (s * c1 + t * c2) +
    dot (s • a1 + t • a2) (R ω))) with hF
  have i1 : Integrable F1 P := C.Ja_int _ _
  have i2 : Integrable F2 P := C.Ja_int _ _
  have i : Integrable F P := C.Ja_int _ _
  have key : ∀ᵐ ω ∂P, s * F1 ω + t * F2 ω ≤ F ω ∧
      (x1 - c1 + dot a1 (R ω) ≠ x2 - c2 + dot a2 (R ω) → s * F1 ω + t * F2 ω < F ω) := by
    filter_upwards [h1.2.2, h2.2.2] with ω hω1 hω2
    have y1 := mul_nonneg C.hq.le hω1
    have y2 := mul_nonneg C.hq.le hω2
    have hc := conc_pt C.hw y1 y2 hs ht hst
    have e1 : F1 ω = w (q * (x1 - c1 + dot a1 (R ω))) := tl_of_nonneg y1
    have e2 : F2 ω = w (q * (x2 - c2 + dot a2 (R ω))) := tl_of_nonneg y2
    have e3 : q * ((s * x1 + t * x2) - (s * c1 + t * c2) + dot (s • a1 + t • a2) (R ω)) =
        s * (q * (x1 - c1 + dot a1 (R ω))) + t * (q * (x2 - c2 + dot a2 (R ω))) := by
      rw [dot_add, dot_smul, dot_smul]; ring
    have e4 : F ω = w (s * (q * (x1 - c1 + dot a1 (R ω))) + t * (q * (x2 - c2 + dot a2 (R ω)))) := by
      simp only [hF]
      rw [e3, tl_of_nonneg (add_nonneg (mul_nonneg hs.le y1) (mul_nonneg ht.le y2))]
    rw [e1, e2, e4]
    refine ⟨hc.1, fun hn => hc.2 fun he => hn ?_⟩
    exact mul_left_cancel₀ C.hq.ne' he
  have hG0 : 0 ≤ᵐ[P] fun ω => F ω - (s * F1 ω + t * F2 ω) := by
    filter_upwards [key] with ω hω
    simpa using hω.1
  have hGi : Integrable (fun ω => F ω - (s * F1 ω + t * F2 ω)) P :=
    i.sub ((i1.const_mul s).add (i2.const_mul t))
  have hGe : ∫ ω, (F ω - (s * F1 ω + t * F2 ω)) ∂P =
      Ja P R q w (s * x1 + t * x2) (s * c1 + t * c2) (s • a1 + t • a2) -
        (s * Ja P R q w x1 c1 a1 + t * Ja P R q w x2 c2 a2) := by
    have a1 := integral_sub i ((i1.const_mul s).add (i2.const_mul t))
    have a2 := integral_add (i1.const_mul s) (i2.const_mul t)
    rw [integral_const_mul, integral_const_mul] at a2
    simp only [Pi.add_apply] at a1
    rw [a1, a2]
    rfl
  have hG : 0 ≤ ∫ ω, (F ω - (s * F1 ω + t * F2 ω)) ∂P := integral_nonneg_of_ae hG0
  have c1' : tl Uc c1 = Uc c1 := tl_of_nonneg h1.1
  have c2' : tl Uc c2 = Uc c2 := tl_of_nonneg h2.1
  have c3' : tl Uc (s * c1 + t * c2) = Uc (s * c1 + t * c2) :=
    tl_of_nonneg (add_nonneg (mul_nonneg hs.le h1.1) (mul_nonneg ht.le h2.1))
  have hcU := conc_pt C.hU h1.1 h2.1 hs ht hst
  unfold Jt
  rw [c1', c2', c3']
  by_cases hc : c1 = c2
  · have hpos : 0 < ∫ ω, (F ω - (s * F1 ω + t * F2 ω)) ∂P := by
      refine lt_of_le_of_ne hG fun h0 => hne ⟨hc, ?_⟩
      have := (integral_eq_zero_iff_of_nonneg_ae hG0 hGi).1 h0.symm
      filter_upwards [this, key] with ω hω hk
      by_contra hn
      have := hk.2 hn
      simp only [Pi.zero_apply] at hω
      linarith
    rw [hGe] at hpos
    nlinarith [hcU.1]
  · have := hcU.2 hc
    rw [hGe] at hG
    nlinarith

def Kset (P : Measure Ω) (R : Ω → Fin d → ℝ) (K' : Submodule ℝ (Fin d → ℝ)) :
    Set (ℝ × (Fin d → ℝ)) :=
  {y | 0 ≤ y.1 ∧ y.1 ≤ 1 ∧ y.2 ∈ K' ∧ psi P R (1 - y.1, y.2) = 0}

noncomputable def Phi (P : Measure Ω) (R : Ω → Fin d → ℝ) (q : ℝ) (Uc w : ℝ → ℝ) (x : ℝ)
    (y : ℝ × (Fin d → ℝ)) : ℝ := Jt P R q Uc w x (x * y.1) (x • y.2)

lemma Ctx.K_compact (C : Ctx P R q Uc w K') : IsCompact (Kset P R K') := by
  obtain ⟨m, hm, hb⟩ := C.bound
  refine Metric.isCompact_of_isClosed_isBounded ?_
    ((Metric.isBounded_closedBall (x := (0 : ℝ × (Fin d → ℝ))) (r := max 1 (1 / m))).subset ?_)
  · have e : Kset P R K' = {y | 0 ≤ y.1} ∩ ({y | y.1 ≤ 1} ∩ ({y | y.2 ∈ K'} ∩
        {y | psi P R (1 - y.1, y.2) = 0})) := Set.ext fun _ => Iff.rfl
    rw [e]
    refine (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
      ((K'.closed_of_finiteDimensional.preimage continuous_snd).inter
      (isClosed_eq ((psi_cont C.hRm C.hRi).comp (by fun_prop)) continuous_const)))
  · intro y hy
    obtain ⟨h0, h1, h2, h3⟩ := hy
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le_max ?_ ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    · rw [le_div_iff₀ hm, mul_comm]
      have h4 := (psi_zero_iff C.hRm C.hRi _).1 h3
      have := psi_le C.hRm C.hRi (by linarith) h4
      have := hb _ h2
      linarith

lemma Ctx.zero_mem_K (C : Ctx P R q Uc w K') : ((0, 0) : ℝ × (Fin d → ℝ)) ∈ Kset P R K' := by
  refine ⟨le_rfl, zero_le_one, K'.zero_mem, ?_⟩
  rw [psi_zero_iff C.hRm C.hRi]
  simp [dot]

lemma Ctx.scale (C : Ctx P R q Uc w K') {x : ℝ} (hx : 0 ≤ x) {y : ℝ × (Fin d → ℝ)}
    (hy : y ∈ Kset P R K') : Feas P R x (x * y.1) (x • y.2) := by
  obtain ⟨h0, h1, _, h3⟩ := hy
  refine ⟨mul_nonneg hx h0, by nlinarith, ?_⟩
  filter_upwards [(psi_zero_iff C.hRm C.hRi _).1 h3] with ω hω
  rw [dot_smul]
  have := mul_nonneg hx hω
  linarith

lemma Ctx.Phi_cont (C : Ctx P R q Uc w K') : Continuous (Function.uncurry (Phi P R q Uc w)) :=
  C.Jt_cont.comp (f := fun p : ℝ × (ℝ × (Fin d → ℝ)) => (p.1, p.1 * p.2.1, p.1 • p.2.2))
    (by fun_prop)

lemma sup_att {β : Type*} [TopologicalSpace β] {f : β → ℝ} (hf : Continuous f) {L : Set β}
    (hL : IsCompact L) (hne : L.Nonempty) :
    ∃ y ∈ L, sSup (f '' L) = f y ∧ ∀ y' ∈ L, f y' ≤ f y := by
  obtain ⟨y, hy, hmax⟩ := hL.exists_isMaxOn hne hf.continuousOn
  refine ⟨y, hy, ?_, fun y' hy' => hmax hy'⟩
  exact IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨y', hy', rfl⟩; exact hmax hy'⟩

lemma sup_eq {β : Type*} {f : β → ℝ} {L : Set β} {y : β} (hy : y ∈ L)
    (h : ∀ y' ∈ L, f y' ≤ f y) : sSup (f '' L) = f y :=
  IsGreatest.csSup_eq ⟨⟨y, hy, rfl⟩, by rintro _ ⟨y', hy', rfl⟩; exact h y' hy'⟩

lemma Jt_congr {x c : ℝ} {a b : Fin d → ℝ} (h : ∀ᵐ ω ∂P, dot a (R ω) = dot b (R ω)) :
    Jt P R q Uc w x c a = Jt P R q Uc w x c b := by
  unfold Jt Ja
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

lemma Ctx.reduce (C : Ctx P R q Uc w K') {x c : ℝ} {a : Fin d → ℝ} (h : Feas P R x c a) :
    ∃ y ∈ Kset P R K', Jt P R q Uc w x c a = Phi P R q Uc w x y := by
  obtain ⟨h0, h1, h2⟩ := h
  have hx : 0 ≤ x := h0.trans h1
  rcases hx.eq_or_lt with rfl | hx
  · have hc : c = 0 := le_antisymm h1 h0
    subst hc
    refine ⟨(0, 0), C.zero_mem_K, ?_⟩
    have : ∀ᵐ ω ∂P, dot a (R ω) = dot (0 : Fin d → ℝ) (R ω) := by
      filter_upwards [na_zero C.hNA (a := a) (by simpa using h2)] with ω hω
      simp [hω, dot]
    simp only [Phi, zero_mul, zero_smul]
    exact Jt_congr this
  · have ha : a ∈ Ker P R ⊔ K' := by rw [C.hK.sup_eq_top]; trivial
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Submodule.mem_sup.1 ha
    have ha1' : ∀ᵐ ω ∂P, dot a1 (R ω) = 0 := ha1
    have e : ∀ᵐ ω ∂P, dot (a1 + a2) (R ω) = dot a2 (R ω) := by
      filter_upwards [ha1'] with ω hω
      rw [dot_add, hω, zero_add]
    refine ⟨(c / x, x⁻¹ • a2), ⟨by positivity, (div_le_one hx).2 h1, K'.smul_mem _ ha2, ?_⟩, ?_⟩
    · rw [psi_zero_iff C.hRm C.hRi]
      filter_upwards [h2, e] with ω hω he
      rw [he] at hω
      simp only [dot_smul]
      have := mul_nonneg (inv_nonneg.2 hx.le) hω
      have e2 : x⁻¹ * (x - c + dot a2 (R ω)) = 1 - c / x + x⁻¹ * dot a2 (R ω) := by
        field_simp
      rwa [e2] at this
    · simp only [Phi]
      rw [mul_div_cancel₀ _ hx.ne', smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
      exact Jt_congr e

lemma Feas_conv {x1 c1 x2 c2 s t : ℝ} {a1 a2 : Fin d → ℝ}
    (h1 : Feas P R x1 c1 a1) (h2 : Feas P R x2 c2 a2) (hs : 0 < s) (ht : 0 < t) :
    Feas P R (s * x1 + t * x2) (s * c1 + t * c2) (s • a1 + t • a2) := by
  refine ⟨add_nonneg (mul_nonneg hs.le h1.1) (mul_nonneg ht.le h2.1),
    add_le_add (mul_le_mul_of_nonneg_left h1.2.1 hs.le) (mul_le_mul_of_nonneg_left h2.2.1 ht.le), ?_⟩
  filter_upwards [h1.2.2, h2.2.2] with ω h3 h4
  rw [dot_add, dot_smul, dot_smul]
  have := add_nonneg (mul_nonneg hs.le h3) (mul_nonneg ht.le h4)
  linarith

theorem Ctx.onestep (C : Ctx P R q Uc w K') :
    ∃ (v : ℝ → ℝ) (g : ℝ → ℝ × (Fin d → ℝ)), Good v ∧ Measurable g ∧ ∀ x, 0 ≤ x →
      Feas P R x (g x).1 (g x).2 ∧ Jt P R q Uc w x (g x).1 (g x).2 = v x ∧
      ∀ c a, Feas P R x c a → Jt P R q Uc w x c a ≤ v x := by
  have hK := C.K_compact
  have hKne : (Kset P R K').Nonempty := ⟨_, C.zero_mem_K⟩
  have hPhix : ∀ x, Continuous (Phi P R q Uc w x) := fun x =>
    C.Phi_cont.comp (Continuous.prodMk_right x)
  set v : ℝ → ℝ := fun x => sSup (Phi P R q Uc w x '' Kset P R K') with hv
  have hvc : Continuous v := hK.continuous_sSup C.Phi_cont
  have hatt : ∀ x, ∃ y ∈ Kset P R K', Phi P R q Uc w x y = v x ∧
      ∀ y' ∈ Kset P R K', Phi P R q Uc w x y' ≤ Phi P R q Uc w x y := by
    intro x
    obtain ⟨y, hy, h1, h2⟩ := sup_att (hPhix x) hK hKne
    exact ⟨y, hy, h1.symm, h2⟩
  have hle : ∀ x c a, Feas P R x c a → Jt P R q Uc w x c a ≤ v x := by
    intro x c a h
    obtain ⟨y, hy, e⟩ := C.reduce h
    obtain ⟨y0, _, h0, h1⟩ := hatt x
    rw [e, ← h0]
    exact h1 y hy
  have hmono : StrictMonoOn v (Set.Ici 0) := by
    intro x1 hx1 x2 _ hlt
    obtain ⟨y, hy, h0, _⟩ := hatt x1
    have hF := C.scale hx1 hy
    set c := x1 * y.1
    set a := x1 • y.2
    have hF2 : Feas P R x2 (c + (x2 - x1)) a := by
      refine ⟨by linarith [hF.1], by linarith [hF.2.1], ?_⟩
      filter_upwards [hF.2.2] with ω hω
      linarith
    have hlt2 : Jt P R q Uc w x1 c a < Jt P R q Uc w x2 (c + (x2 - x1)) a := by
      unfold Jt
      have e : Ja P R q w x2 (c + (x2 - x1)) a = Ja P R q w x1 c a := by
        unfold Ja
        congr 1
        funext ω
        congr 2
        ring
      rw [e, tl_of_nonneg hF.1, tl_of_nonneg hF2.1]
      have := C.hU.mono (Set.mem_Ici.2 hF.1) (Set.mem_Ici.2 hF2.1)
        (show c < c + (x2 - x1) by linarith)
      linarith
    calc v x1 = Jt P R q Uc w x1 c a := h0.symm
      _ < _ := hlt2
      _ ≤ v x2 := hle _ _ _ hF2
  have hconc : StrictConcaveOn ℝ (Set.Ici 0) v := by
    refine ⟨convex_Ici 0, fun x1 hx1 x2 hx2 hne s t hs ht hst => ?_⟩
    simp only [smul_eq_mul]
    obtain ⟨y1, hy1, h1, _⟩ := hatt x1
    obtain ⟨y2, hy2, h2, _⟩ := hatt x2
    have hF1 := C.scale hx1 hy1
    have hF2 := C.scale hx2 hy2
    have hsc := C.sc hF1 hF2 hs ht hst ?_
    · refine lt_of_lt_of_le ?_ (hle _ _ _ (Feas_conv hF1 hF2 hs ht))
      have e1 : Jt P R q Uc w x1 (x1 * y1.1) (x1 • y1.2) = v x1 := h1
      have e2 : Jt P R q Uc w x2 (x2 * y2.1) (x2 • y2.2) = v x2 := h2
      rwa [e1, e2] at hsc
    · rintro ⟨hc, hW⟩
      have aux : ∀ (b : Fin d → ℝ) (δ : ℝ), 0 < δ → (∀ᵐ ω ∂P, dot b (R ω) = δ) → False := by
        intro b δ hδ hb
        have := na_zero C.hNA (a := b) (by filter_upwards [hb] with ω hω; rw [hω]; exact hδ.le)
        obtain ⟨ω, h3, h4⟩ := (hb.and this).exists
        linarith
      rcases lt_or_gt_of_ne hne with hl | hl
      · refine aux (x1 • y1.2 - x2 • y2.2) (x2 - x1) (by linarith) ?_
        filter_upwards [hW] with ω hω
        rw [dot_sub]
        linarith
      · refine aux (x2 • y2.2 - x1 • y1.2) (x1 - x2) (by linarith) ?_
        filter_upwards [hW] with ω hω
        rw [dot_sub]
        linarith
  have huniq : ∀ x, 0 < x → ∀ y1 ∈ Kset P R K', ∀ y2 ∈ Kset P R K',
      Phi P R q Uc w x y1 = v x → Phi P R q Uc w x y2 = v x → y1 = y2 := by
    intro x hx y1 hy1 y2 hy2 h1 h2
    by_contra hne
    have hF1 := C.scale hx.le hy1
    have hF2 := C.scale hx.le hy2
    have hsc := C.sc hF1 hF2 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num) ?_
    · have h3 := hle _ _ _ (Feas_conv hF1 hF2 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num))
      have e1 : Jt P R q Uc w x (x * y1.1) (x • y1.2) = v x := h1
      have e2 : Jt P R q Uc w x (x * y2.1) (x • y2.2) = v x := h2
      have e3 : (1 / 2 : ℝ) * x + 1 / 2 * x = x := by ring
      rw [e1, e2] at hsc
      rw [e3] at h3
      rw [e3] at hsc
      linarith
    · rintro ⟨hc, hW⟩
      apply hne
      have hc' : y1.1 = y2.1 := mul_left_cancel₀ hx.ne' hc
      have hz : x • y1.2 - x • y2.2 = 0 := by
        refine C.ker_eq_zero (K'.sub_mem (K'.smul_mem _ hy1.2.2.1) (K'.smul_mem _ hy2.2.2.1)) ?_
        filter_upwards [hW] with ω hω
        rw [dot_sub, hc] at *
        linarith
      have hz2 : y1.2 = y2.2 := smul_right_injective _ hx.ne' (sub_eq_zero.1 hz)
      exact Prod.ext hc' hz2
  choose ys hys hys1 hys2 using hatt
  let yst : ℝ → ℝ × (Fin d → ℝ) := fun x => if 0 < x then ys x else (0, 0)
  have hyst_meas : Measurable yst := by
    refine measurable_of_isClosed fun F hF => ?_
    have hA : ∃ A : Set ℝ, MeasurableSet A ∧ ∀ x, 0 < x → (ys x ∈ F ↔ x ∈ A) := by
      rcases (Kset P R K' ∩ F).eq_empty_or_nonempty with hE | hE
      · refine ⟨∅, MeasurableSet.empty, fun x _ => ?_⟩
        simp only [Set.mem_empty_iff_false, iff_false]
        intro h
        have : ys x ∈ Kset P R K' ∩ F := ⟨hys x, h⟩
        rw [hE] at this
        exact this
      · have hLc : IsCompact (Kset P R K' ∩ F) := hK.inter_right hF
        have hc2 : Continuous fun x => sSup (Phi P R q Uc w x '' (Kset P R K' ∩ F)) :=
          hLc.continuous_sSup C.Phi_cont
        refine ⟨{x | sSup (Phi P R q Uc w x '' (Kset P R K' ∩ F)) = v x},
          (isClosed_eq hc2 hvc).measurableSet, fun x hx => ?_⟩
        constructor
        · intro h
          show sSup (Phi P R q Uc w x '' (Kset P R K' ∩ F)) = v x
          rw [sup_eq (f := Phi P R q Uc w x) (L := Kset P R K' ∩ F) (y := ys x) ⟨hys x, h⟩
            (fun y' hy' => hys2 x y' hy'.1), hys1]
        · intro h
          have h' : sSup (Phi P R q Uc w x '' (Kset P R K' ∩ F)) = v x := h
          obtain ⟨y, hy, h1, _⟩ := sup_att (hPhix x) hLc hE
          have := huniq x hx y hy.1 (ys x) (hys x) (by rw [← h1, h']) (hys1 x)
          rw [← this]
          exact hy.2
    obtain ⟨A, hAm, hAe⟩ := hA
    have e : yst ⁻¹' F = ({x | 0 < x} ∩ A) ∪ ({x | x ≤ 0} ∩ {_x | (0, 0) ∈ F}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, yst]
      by_cases hx : 0 < x
      · simp [hx, hAe x hx, not_le.2 hx]
      · simp [hx, not_lt.1 hx]
    rw [e]
    exact (((measurableSet_lt measurable_const measurable_id).inter hAm)).union
      ((measurableSet_le measurable_id measurable_const).inter (MeasurableSet.const _))
  refine ⟨v, fun x => (x * (yst x).1, x • (yst x).2), ⟨hmono, hconc, hvc.continuousOn⟩,
    (measurable_id.mul hyst_meas.fst).prodMk (measurable_id.smul hyst_meas.snd), fun x hx => ?_⟩
  have hystK : yst x ∈ Kset P R K' := by
    by_cases h : 0 < x
    · simp only [yst, h, if_true]; exact hys x
    · simp only [yst, h, if_false]; exact C.zero_mem_K
  refine ⟨C.scale hx hystK, ?_, hle x⟩
  rcases hx.eq_or_lt with rfl | hx'
  · have := hys1 0
    simp only [Phi, zero_mul, zero_smul] at this ⊢
    exact this
  · simp only [yst, hx', if_true]
    exact hys1 x

end OneStep

open scoped ENNReal

noncomputable def Fhat {d : ℕ} (h : ℕ → ℝ → ℝ≥0∞) (g : ℝ → ℝ≥0∞)
    (τ : ℕ → ℝ → (Fin d → ℝ) → ℝ) : ℕ → ℕ → ℝ → (ℕ → Fin d → ℝ) → ℝ≥0∞
  | 0, _, x, _ => g x
  | k + 1, n, x, r => h n x + Fhat h g τ k (n + 1) (τ n x (r (n + 1))) r

lemma Fhat_dep {d : ℕ} (h : ℕ → ℝ → ℝ≥0∞) (g : ℝ → ℝ≥0∞) (τ : ℕ → ℝ → (Fin d → ℝ) → ℝ)
    (k : ℕ) : ∀ (n : ℕ) (x : ℝ) (r r' : ℕ → Fin d → ℝ), (∀ j, n < j → j ≤ n + k → r j = r' j) →
      Fhat h g τ k n x r = Fhat h g τ k n x r' := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro n x r r' hr
    simp only [Fhat]
    rw [hr (n + 1) (by omega) (by omega)]
    congr 1
    exact ih _ _ _ _ fun j h1 h2 => hr j (by omega) (by omega)

lemma Fhat_meas {d : ℕ} {h : ℕ → ℝ → ℝ≥0∞} {g : ℝ → ℝ≥0∞} {τ : ℕ → ℝ → (Fin d → ℝ) → ℝ}
    (hg : Measurable g) (k : ℕ) : ∀ n : ℕ, (∀ j, n ≤ j → j < n + k → Measurable (h j)) →
      (∀ j, n ≤ j → j < n + k → Measurable (Function.uncurry (τ j))) →
      Measurable (fun p : ℝ × (ℕ → Fin d → ℝ) => Fhat h g τ k n p.1 p.2) := by
  induction k with
  | zero => intro n _ _; exact hg.comp measurable_fst
  | succ k ih =>
    intro n h1 h2
    simp only [Fhat]
    refine ((h1 n le_rfl (by omega)).comp measurable_fst).add ?_
    have h3 := ih (n + 1) (fun j a b => h1 j (by omega) (by omega))
      (fun j a b => h2 j (by omega) (by omega))
    have h4 : Measurable (fun p : ℝ × (ℕ → Fin d → ℝ) => τ n p.1 (p.2 (n + 1))) :=
      (h2 n le_rfl (by omega)).comp
        (f := fun p : ℝ × (ℕ → Fin d → ℝ) => (p.1, p.2 (n + 1)))
        (measurable_fst.prodMk ((measurable_pi_apply (n + 1)).comp measurable_snd))
    exact h3.comp (f := fun p : ℝ × (ℕ → Fin d → ℝ) => (τ n p.1 (p.2 (n + 1)), p.2))
      (h4.prodMk measurable_snd)

section Market

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

attribute [local instance] ConsumptionInvestmentMarket.isProb

lemma indep_step (M : ConsumptionInvestmentMarket Ω d) {n : ℕ} (hn : n < M.N) :
    IndepFun (M.R (n + 1))
      (fun ω (j : ℕ) => if n + 1 < j ∧ j ≤ M.N then M.R j ω else (0 : Fin d → ℝ)) M.measIP := by
  classical
  have hmeas : ∀ i : Fin M.N, Measurable (fun ω => M.R (i.val + 1) ω) := fun i =>
    M.hR_meas _ (by omega) (by omega)
  have hS := iIndepFun.indepFun_finset (S := {(⟨n, hn⟩ : Fin M.N)})
    (T := Finset.univ.filter (fun i : Fin M.N => n < i.val))
    (by
      rw [Finset.disjoint_left]
      intro i hi hi2
      simp only [Finset.mem_singleton] at hi
      simp [hi] at hi2)
    M.hR_indep hmeas
  have hφ : Measurable (fun v : (↥({(⟨n, hn⟩ : Fin M.N)} : Finset (Fin M.N))) → Fin d → ℝ =>
      v ⟨⟨n, hn⟩, by simp⟩) := measurable_pi_apply _
  have hψ : Measurable (fun (v : (↥(Finset.univ.filter (fun i : Fin M.N => n < i.val))) →
      Fin d → ℝ) (j : ℕ) => if h : n + 1 < j ∧ j ≤ M.N then
      v ⟨⟨j - 1, by omega⟩, by simp; omega⟩ else (0 : Fin d → ℝ)) := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases h : n + 1 < j ∧ j ≤ M.N
    · simp only [h, and_self, dite_true]
      exact measurable_pi_apply _
    · simp only [h, dite_false]
      exact measurable_const
  have := hS.comp hφ hψ
  convert this using 1
  · rfl
  funext ω j
  by_cases h : n + 1 < j ∧ j ≤ M.N
  · have e : j - 1 + 1 = j := by omega
    simp [h, e]
  · simp [h]

lemma fub (M : ConsumptionInvestmentMarket Ω d) {h : ℕ → ℝ → ℝ≥0∞} {g : ℝ → ℝ≥0∞}
    {τ : ℕ → ℝ → (Fin d → ℝ) → ℝ} {k n : ℕ} (hnk : n + (k + 1) = M.N) (hg : Measurable g)
    (hh : ∀ j, n ≤ j → j < M.N → Measurable (h j))
    (hτ : ∀ j, n ≤ j → j < M.N → Measurable (Function.uncurry (τ j))) (x : ℝ) :
    ∫⁻ ω, Fhat h g τ (k + 1) n x (fun j => M.R j ω) ∂M.measIP =
      h n x + ∫⁻ ω, (∫⁻ ω', Fhat h g τ k (n + 1) (τ n x (M.R (n + 1) ω))
        (fun j => M.R j ω') ∂M.measIP) ∂M.measIP := by
  have hn : n < M.N := by omega
  set X := M.R (n + 1) with hX
  set Y : Ω → ℕ → Fin d → ℝ :=
    fun ω j => if n + 1 < j ∧ j ≤ M.N then M.R j ω else 0 with hY
  have hXm : Measurable X := M.hR_meas _ (by omega) (by omega)
  have hYm : Measurable Y := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : n + 1 < j ∧ j ≤ M.N
    · simp only [hY, hj, and_self, if_true]
      exact M.hR_meas _ (by omega) hj.2
    · simp only [hY, hj, if_false]
      exact measurable_const
  have hind : IndepFun X Y M.measIP := indep_step M hn
  haveI : IsProbabilityMeasure (M.measIP.map X) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  haveI : IsProbabilityMeasure (M.measIP.map Y) :=
    Measure.isProbabilityMeasure_map hYm.aemeasurable
  have hdep : ∀ y ω, Fhat h g τ k (n + 1) y (fun j => M.R j ω) =
      Fhat h g τ k (n + 1) y (Y ω) := by
    intro y ω
    refine Fhat_dep _ _ _ _ _ _ _ _ fun j h1 h2 => ?_
    have : n + 1 < j ∧ j ≤ M.N := ⟨h1, by omega⟩
    simp only [hY, this, and_self, if_true]
  have hF := Fhat_meas (h := h) (τ := τ) hg k (n + 1)
    (fun j a b => hh j (by omega) (by omega)) (fun j a b => hτ j (by omega) (by omega))
  have hτx : Measurable (τ n x) :=
    (hτ n le_rfl hn).comp (f := fun u : Fin d → ℝ => (x, u)) (by fun_prop)
  have hG : Measurable (fun p : (Fin d → ℝ) × (ℕ → Fin d → ℝ) =>
      Fhat h g τ k (n + 1) (τ n x p.1) p.2) :=
    hF.comp (f := fun p : (Fin d → ℝ) × (ℕ → Fin d → ℝ) => (τ n x p.1, p.2))
      ((hτx.comp measurable_fst).prodMk measurable_snd)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).1 hind
  have step1 : ∫⁻ ω, Fhat h g τ k (n + 1) (τ n x (X ω)) (Y ω) ∂M.measIP =
      ∫⁻ ω, (∫⁻ ω', Fhat h g τ k (n + 1) (τ n x (X ω)) (Y ω') ∂M.measIP) ∂M.measIP := by
    have e1 := lintegral_map hG (hXm.prodMk hYm) (μ := M.measIP)
    rw [← e1, hprod, lintegral_prod _ hG.aemeasurable,
      lintegral_map hG.lintegral_prod_right' hXm]
    refine lintegral_congr fun ω => ?_
    exact lintegral_map (hF.comp (f := fun v => (τ n x (X ω), v)) (by fun_prop)) hYm
  simp only [Fhat]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  congr 1
  simp only [hdep]
  exact step1

lemma ereal_congr {E : Type*} [MeasurableSpace E] {μ : Measure E} {f g : E → EReal}
    (h : ∀ᵐ x ∂μ, f x = g x) : erealIntegral μ f = erealIntegral μ g := by
  unfold erealIntegral
  have e1 : ∫⁻ x, (f x ⊔ 0).toENNReal ∂μ = ∫⁻ x, (g x ⊔ 0).toENNReal ∂μ :=
    lintegral_congr_ae (by filter_upwards [h] with x hx; rw [hx])
  have e2 : ∫⁻ x, ((-f x) ⊔ 0).toENNReal ∂μ = ∫⁻ x, ((-g x) ⊔ 0).toENNReal ∂μ :=
    lintegral_congr_ae (by filter_upwards [h] with x hx; rw [hx])
  rw [e1, e2]

lemma coe_pos_part (y : ℝ) : (((y : EReal) ⊔ 0).toENNReal) = ENNReal.ofReal y := by
  rcases le_total y 0 with h | h
  · have : (y : EReal) ⊔ 0 = 0 := sup_eq_right.2 (by exact_mod_cast h)
    rw [this]
    simp [ENNReal.ofReal_of_nonpos h]
  · have : (y : EReal) ⊔ 0 = y := sup_eq_left.2 (by exact_mod_cast h)
    rw [this, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma coe_ennreal_real {A : ℝ≥0∞} (h : A ≠ ⊤) : ((A : ℝ≥0∞) : EReal) = ((A.toReal : ℝ) : EReal) := by
  lift A to NNReal using h
  rfl

lemma ereal_int {E : Type*} [MeasurableSpace E] {μ : Measure E} {f : E → ℝ}
    (hf : Integrable f μ) : erealIntegral μ (fun x => (f x : EReal)) = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  unfold erealIntegral
  have e2 : ∀ x, (-(f x : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (-f x) := fun x => by
    rw [← EReal.coe_neg]; exact coe_pos_part _
  simp only [coe_pos_part, e2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    coe_ennreal_real hf.lintegral_lt_top.ne,
    coe_ennreal_real (show ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤ from hf.neg.lintegral_lt_top.ne),
    EReal.coe_sub]
  rfl

noncomputable def tau (M : ConsumptionInvestmentMarket Ω d) (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (j : ℕ)
    (x : ℝ) (u : Fin d → ℝ) : ℝ := (1 + M.i (j + 1)) * (x - (π j x).1 + dot (π j x).2 u)

lemma tau_meas (M : ConsumptionInvestmentMarket Ω d) {π : ℕ → ℝ → ℝ × (Fin d → ℝ)} {j : ℕ}
    (hπ : Measurable (π j)) : Measurable (Function.uncurry (tau M π j)) := by
  have h1 : Measurable fun p : ℝ × (Fin d → ℝ) => π j p.1 := hπ.comp measurable_fst
  refine measurable_const.mul ((measurable_fst.sub h1.fst).add
    (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp h1.snd).mul
      ((measurable_pi_apply k).comp measurable_snd)))

noncomputable def gb (x : ℝ) : ℝ≥0∞ := if x < 0 then 1 else 0

lemma gb_meas : Measurable gb :=
  Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

noncomputable def hr (M : ConsumptionInvestmentMarket Ω d) (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (j : ℕ)
    (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (tl M.Uc (π j x).1 - M.Uc 0)

noncomputable def gr (M : ConsumptionInvestmentMarket Ω d) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (tl M.Up x - M.Up 0)

noncomputable abbrev Fb (M : ConsumptionInvestmentMarket Ω d) (π : ℕ → ℝ → ℝ × (Fin d → ℝ))
    (k n : ℕ) (x : ℝ) (ω : Ω) : ℝ≥0∞ := Fhat (fun _ => gb) gb (tau M π) k n x (fun j => M.R j ω)

noncomputable abbrev Fr (M : ConsumptionInvestmentMarket Ω d) (π : ℕ → ℝ → ℝ × (Fin d → ℝ))
    (k n : ℕ) (x : ℝ) (ω : Ω) : ℝ≥0∞ := Fhat (hr M π) (gr M) (tau M π) k n x (fun j => M.R j ω)

noncomputable def bb (M : ConsumptionInvestmentMarket Ω d) (k : ℕ) : ℝ := k * M.Uc 0 + M.Up 0

structure Setup (M : ConsumptionInvestmentMarket Ω d) (W : ℕ → ℝ → ℝ)
    (f : ℕ → ℝ → ℝ × (Fin d → ℝ)) : Prop where
  hdom : M.domU = Set.Ici (0 : ℝ)
  hWg : ∀ n ≤ M.N, Good (W n)
  hWN : W M.N = M.Up
  hfm : ∀ n < M.N, Measurable (f n)
  hff : ∀ n < M.N, ∀ x, 0 ≤ x → Feas M.measIP (M.R (n + 1)) x (f n x).1 (f n x).2
  hfJ : ∀ n < M.N, ∀ x, 0 ≤ x → Jt M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) M.Uc (W (n + 1)) x
    (f n x).1 (f n x).2 = W n x
  hfle : ∀ n < M.N, ∀ x, 0 ≤ x → ∀ c a, Feas M.measIP (M.R (n + 1)) x c a →
    Jt M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) M.Uc (W (n + 1)) x c a ≤ W n x
  hRi : M.FM2

lemma goodUc (M : ConsumptionInvestmentMarket Ω d) (h : M.domU = Set.Ici (0 : ℝ)) : Good M.Uc :=
  ⟨h ▸ M.hUc_mono, h ▸ M.hUc_concave, h ▸ M.hUc_cont⟩

lemma goodUp (M : ConsumptionInvestmentMarket Ω d) (h : M.domU = Set.Ici (0 : ℝ)) : Good M.Up :=
  ⟨h ▸ M.hUp_mono, h ▸ M.hUp_concave, h ▸ M.hUp_cont⟩

lemma qpos (M : ConsumptionInvestmentMarket Ω d) {n : ℕ} (hn : n < M.N) : 0 < 1 + M.i (n + 1) :=
  M.hi_pos _ (by omega) (by omega)

lemma D_feas (M : ConsumptionInvestmentMarket Ω d) (h : M.domU = Set.Ici (0 : ℝ)) {n : ℕ}
    (hn : n < M.N) {x : ℝ} {ca : ℝ × (Fin d → ℝ)} :
    ca ∈ M.D n x ↔ Feas M.measIP (M.R (n + 1)) x ca.1 ca.2 := by
  have hq := qpos M hn
  unfold ConsumptionInvestmentMarket.D Feas
  rw [h]
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨h1, h2, _, h4⟩
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h4] with ω hω
    exact (mul_nonneg_iff_of_pos_left hq).1 hω
  · rintro ⟨h1, h2, h4⟩
    refine ⟨h1, h2, h1, ?_⟩
    filter_upwards [h4] with ω hω
    exact mul_nonneg hq.le hω

variable {M : ConsumptionInvestmentMarket Ω d} {W : ℕ → ℝ → ℝ} {f π : ℕ → ℝ → ℝ × (Fin d → ℝ)}

lemma Setup.tau_nonneg (S : Setup M W f) {n : ℕ} (hn : n < M.N) (hπ : M.IsAdmissible n π) {x : ℝ}
    (hx : 0 ≤ x) : ∀ᵐ ω ∂M.measIP, 0 ≤ tau M π n x (M.R (n + 1) ω) := by
  have h1 : Feas M.measIP (M.R (n + 1)) x (π n x).1 (π n x).2 :=
    (D_feas M S.hdom hn).1 ((hπ n le_rfl hn).1 x (S.hdom ▸ hx))
  filter_upwards [h1.2.2] with ω hω
  exact mul_nonneg (qpos M hn).le hω

lemma adm_succ {n : ℕ} (hπ : M.IsAdmissible n π) : M.IsAdmissible (n + 1) π :=
  fun k h1 h2 => hπ k (by omega) h2

lemma Setup.bad_zero (S : Setup M W f) (k : ℕ) : ∀ n, n + k = M.N → ∀ {π : ℕ → ℝ → ℝ × (Fin d → ℝ)},
    M.IsAdmissible n π → ∀ x, 0 ≤ x → ∫⁻ ω, Fb M π k n x ω ∂M.measIP = 0 := by
  induction k with
  | zero =>
    intro n _ π _ x hx
    simp [Fb, Fhat, gb, not_lt.2 hx]
  | succ k ih =>
    intro n hnk π hπ x hx
    have hn : n < M.N := by omega
    rw [fub M hnk gb_meas (fun _ _ _ => gb_meas) (fun j a b => tau_meas M (hπ j a b).2)]
    have : gb x = 0 := by simp [gb, not_lt.2 hx]
    rw [this, zero_add]
    rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
    filter_upwards [S.tau_nonneg hn hπ hx] with ω hω
    exact ih (n + 1) (by omega) (adm_succ hπ) _ hω

lemma Setup.path (S : Setup M W f) (ω : Ω) (k : ℕ) : ∀ n, n + k = M.N →
    ∀ {π : ℕ → ℝ → ℝ × (Fin d → ℝ)}, M.IsAdmissible n π → ∀ x, Fb M π k n x ω = 0 →
    0 ≤ (M.stateAcc π k n x ω).2 + M.Up (M.stateAcc π k n x ω).1 - bb M k ∧
    Fr M π k n x ω = ENNReal.ofReal
      ((M.stateAcc π k n x ω).2 + M.Up (M.stateAcc π k n x ω).1 - bb M k) := by
  have hUp := goodUp M S.hdom
  have hUc := goodUc M S.hdom
  induction k with
  | zero =>
    intro n _ π _ x hb
    have hb' : gb x = 0 := hb
    have hx : 0 ≤ x := by
      by_contra hn
      simp [gb, not_le.1 hn] at hb'
    have e : M.stateAcc π 0 n x ω = (x, 0) := rfl
    have e2 : Fr M π 0 n x ω = gr M x := rfl
    rw [e, e2, gr, tl_of_nonneg hx, bb]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    exact ⟨sub_nonneg.2 (hUp.mono.monotoneOn Set.self_mem_Ici (Set.mem_Ici.2 hx) hx), trivial⟩
  | succ k ih =>
    intro n hnk π hπ x hb
    have hn : n < M.N := by omega
    have hb2 : gb x + Fb M π k (n + 1) (tau M π n x (M.R (n + 1) ω)) ω = 0 := hb
    obtain ⟨hb3, hb4⟩ := add_eq_zero.1 hb2
    have hx : 0 ≤ x := by
      by_contra hn
      simp [gb, not_le.1 hn] at hb3
    obtain ⟨h1, h2⟩ := ih (n + 1) (by omega) (adm_succ hπ) _ hb4
    have hF : Feas M.measIP (M.R (n + 1)) x (π n x).1 (π n x).2 :=
      (D_feas M S.hdom hn).1 ((hπ n le_rfl hn).1 x (S.hdom ▸ hx))
    have hc := hF.1
    have e : M.stateAcc π (k + 1) n x ω =
        ((M.stateAcc π k (n + 1) (tau M π n x (M.R (n + 1) ω)) ω).1,
          M.Uc (π n x).1 + (M.stateAcc π k (n + 1) (tau M π n x (M.R (n + 1) ω)) ω).2) := rfl
    have e2 : Fr M π (k + 1) n x ω = hr M π n x +
        Fr M π k (n + 1) (tau M π n x (M.R (n + 1) ω)) ω := rfl
    have hU0 : 0 ≤ M.Uc (π n x).1 - M.Uc 0 :=
      sub_nonneg.2 (hUc.mono.monotoneOn Set.self_mem_Ici (Set.mem_Ici.2 hc) hc)
    set st := M.stateAcc π k (n + 1) (tau M π n x (M.R (n + 1) ω)) ω
    have e3 : M.Uc (π n x).1 + st.2 + M.Up st.1 - bb M (k + 1) =
        (M.Uc (π n x).1 - M.Uc 0) + (st.2 + M.Up st.1 - bb M k) := by
      simp only [bb, Nat.cast_add, Nat.cast_one]; ring
    rw [e, e2, h2, hr, tl_of_nonneg hc]
    simp only
    rw [e3, ENNReal.ofReal_add hU0 h1]
    exact ⟨add_nonneg hU0 h1, rfl⟩

lemma Setup.W_ge (S : Setup M W f) (k : ℕ) : ∀ n, n + k = M.N → ∀ x, 0 ≤ x → bb M k ≤ W n x := by
  have hUp := goodUp M S.hdom
  induction k with
  | zero =>
    intro n hn x hx
    have : n = M.N := by omega
    subst this
    rw [S.hWN, bb]
    simpa using hUp.mono.monotoneOn Set.self_mem_Ici (Set.mem_Ici.2 hx) hx
  | succ k ih =>
    intro n hnk x hx
    have hn : n < M.N := by omega
    have hq := qpos M hn
    have hF : Feas M.measIP (M.R (n + 1)) x 0 0 :=
      ⟨le_rfl, hx, Filter.Eventually.of_forall fun ω => by simpa [dot] using hx⟩
    have h1 := S.hfle n hn x hx 0 0 hF
    have h2 := ih (n + 1) (by omega) _ (mul_nonneg hq.le hx)
    have e : Jt M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) M.Uc (W (n + 1)) x 0 0 =
        M.Uc 0 + W (n + 1) ((1 + M.i (n + 1)) * x) := by
      unfold Jt Ja
      rw [tl_of_nonneg le_rfl]
      simp [dot, tl_of_nonneg (mul_nonneg hq.le hx)]
    rw [e] at h1
    simp only [bb, Nat.cast_add, Nat.cast_one] at h2 ⊢
    linarith

lemma Setup.step (S : Setup M W f) {k n : ℕ} (hnk : n + (k + 1) = M.N)
    (hπ : M.IsAdmissible n π) {x : ℝ} (hx : 0 ≤ x) :
    hr M π n x + ∫⁻ ω, ENNReal.ofReal (W (n + 1) (tau M π n x (M.R (n + 1) ω)) - bb M k) ∂M.measIP =
      ENNReal.ofReal (Jt M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) M.Uc (W (n + 1)) x
        (π n x).1 (π n x).2 - bb M (k + 1)) := by
  have hn : n < M.N := by omega
  have hq := qpos M hn
  have hG := S.hWg (n + 1) (by omega)
  have hUc := goodUc M S.hdom
  have hF : Feas M.measIP (M.R (n + 1)) x (π n x).1 (π n x).2 :=
    (D_feas M S.hdom hn).1 ((hπ n le_rfl hn).1 x (S.hdom ▸ hx))
  have hb0 : bb M k ≤ W (n + 1) 0 := S.W_ge k (n + 1) (by omega) 0 le_rfl
  have hi : Integrable (fun ω => tl (W (n + 1)) ((1 + M.i (n + 1)) *
      (x - (π n x).1 + dot (π n x).2 (M.R (n + 1) ω)))) M.measIP :=
    int_ok (h := fun y => tl (W (n + 1)) ((1 + M.i (n + 1)) * y)) (M.hR_meas _ (by omega) (by omega))
      (S.hRi _ (by omega) (by omega)) ((tl_cont hG).comp (by fun_prop)) (L_nonneg hG hq)
      (tlq_bd hG hq) _ _
  have hnn : ∀ ω, 0 ≤ tl (W (n + 1)) ((1 + M.i (n + 1)) *
      (x - (π n x).1 + dot (π n x).2 (M.R (n + 1) ω))) - bb M k := fun ω =>
    sub_nonneg.2 (hb0.trans (tl_ge hG _))
  have e1 : ∫⁻ ω, ENNReal.ofReal (W (n + 1) (tau M π n x (M.R (n + 1) ω)) - bb M k) ∂M.measIP =
      ENNReal.ofReal (Ja M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) (W (n + 1)) x (π n x).1 (π n x).2
        - bb M k) := by
    have e2 : Ja M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) (W (n + 1)) x (π n x).1 (π n x).2 - bb M k
        = ∫ ω, (tl (W (n + 1)) ((1 + M.i (n + 1)) *
          (x - (π n x).1 + dot (π n x).2 (M.R (n + 1) ω))) - bb M k) ∂M.measIP := by
      rw [integral_sub hi (integrable_const _), integral_const]
      simp [Ja]
    have hi2 : Integrable (fun ω => tl (W (n + 1)) ((1 + M.i (n + 1)) *
        (x - (π n x).1 + dot (π n x).2 (M.R (n + 1) ω))) - bb M k) M.measIP :=
      hi.sub (integrable_const _)
    rw [e2, ofReal_integral_eq_lintegral_ofReal hi2 (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr_ae ?_
    filter_upwards [S.tau_nonneg hn hπ hx] with ω hω
    have e3 : tl (W (n + 1)) (tau M π n x (M.R (n + 1) ω)) = W (n + 1) (tau M π n x (M.R (n + 1) ω)) :=
      tl_of_nonneg hω
    rw [← e3]
    rfl
  have hJa : 0 ≤ Ja M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) (W (n + 1)) x (π n x).1 (π n x).2
      - bb M k := by
    have e2 := integral_sub hi (integrable_const (bb M k))
    rw [integral_const] at e2
    simp only [probReal_univ, one_smul] at e2
    have : 0 ≤ ∫ ω, (tl (W (n + 1)) ((1 + M.i (n + 1)) *
          (x - (π n x).1 + dot (π n x).2 (M.R (n + 1) ω))) - bb M k) ∂M.measIP :=
      integral_nonneg hnn
    rw [e2] at this
    exact this
  have hU0 : 0 ≤ M.Uc (π n x).1 - M.Uc 0 :=
    sub_nonneg.2 (hUc.mono.monotoneOn Set.self_mem_Ici (Set.mem_Ici.2 hF.1) hF.1)
  rw [e1, hr, tl_of_nonneg hF.1, ← ENNReal.ofReal_add hU0 hJa]
  congr 1
  unfold Jt
  rw [tl_of_nonneg hF.1]
  simp only [bb, Nat.cast_add, Nat.cast_one]
  ring

lemma Setup.f_adm (S : Setup M W f) (n : ℕ) : M.IsAdmissible n f := fun k _ hk =>
  ⟨fun x hx => (D_feas M S.hdom hk).2
    (S.hff k hk x (by have h := hx; rw [S.hdom] at h; exact h)), S.hfm k hk⟩

lemma Setup.gr_meas (S : Setup M W f) : Measurable (gr M) :=
  ENNReal.measurable_ofReal.comp ((tl_cont (goodUp M S.hdom)).measurable.sub_const _)

lemma Setup.hr_meas (S : Setup M W f) {j : ℕ} (hπ : Measurable (π j)) : Measurable (hr M π j) :=
  ENNReal.measurable_ofReal.comp
    (((tl_cont (goodUc M S.hdom)).measurable.comp hπ.fst).sub_const _)

lemma Setup.main (S : Setup M W f) (k : ℕ) : ∀ n, n + k = M.N →
    (∀ {π : ℕ → ℝ → ℝ × (Fin d → ℝ)}, M.IsAdmissible n π → ∀ x, 0 ≤ x →
      ∫⁻ ω, Fr M π k n x ω ∂M.measIP ≤ ENNReal.ofReal (W n x - bb M k)) ∧
    (∀ x, 0 ≤ x → ∫⁻ ω, Fr M f k n x ω ∂M.measIP = ENNReal.ofReal (W n x - bb M k)) := by
  have hUp := goodUp M S.hdom
  induction k with
  | zero =>
    intro n hn
    have hn' : n = M.N := by omega
    subst hn'
    have key : ∀ {π : ℕ → ℝ → ℝ × (Fin d → ℝ)} (x : ℝ), 0 ≤ x →
        ∫⁻ ω, Fr M π 0 M.N x ω ∂M.measIP = ENNReal.ofReal (W M.N x - bb M 0) := by
      intro π x hx
      have : ∀ ω, Fr M π 0 M.N x ω = ENNReal.ofReal (W M.N x - bb M 0) := fun ω => by
        show gr M x = _
        rw [gr, tl_of_nonneg hx, S.hWN, bb]
        simp
      simp [this]
    exact ⟨fun _ x hx => (key x hx).le, fun x hx => key x hx⟩
  | succ k ih =>
    intro n hnk
    have hn : n < M.N := by omega
    obtain ⟨ih1, ih2⟩ := ih (n + 1) (by omega)
    constructor
    · intro π hπ x hx
      rw [fub M hnk S.gr_meas (fun j a b => S.hr_meas (hπ j a b).2)
        (fun j a b => tau_meas M (hπ j a b).2)]
      have hF : Feas M.measIP (M.R (n + 1)) x (π n x).1 (π n x).2 :=
        (D_feas M S.hdom hn).1 ((hπ n le_rfl hn).1 x (S.hdom ▸ hx))
      refine (add_le_add le_rfl (lintegral_mono_ae ?_)).trans ((S.step hnk hπ hx).le.trans
        (ENNReal.ofReal_le_ofReal (sub_le_sub_right (S.hfle n hn x hx _ _ hF) _)))
      filter_upwards [S.tau_nonneg hn hπ hx] with ω hω
      exact ih1 (adm_succ hπ) _ hω
    · intro x hx
      have hf := S.f_adm n
      rw [fub M hnk S.gr_meas (fun j a b => S.hr_meas (hf j a b).2)
        (fun j a b => tau_meas M (hf j a b).2), ← S.hfJ n hn x hx, ← S.step hnk hf hx]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [S.tau_nonneg hn hf hx] with ω hω
      exact ih2 _ hω

lemma Fhat_ω_meas (M : ConsumptionInvestmentMarket Ω d) {h : ℕ → ℝ → ℝ≥0∞} {g : ℝ → ℝ≥0∞}
    {τ : ℕ → ℝ → (Fin d → ℝ) → ℝ} {k n : ℕ} (hnk : n + k = M.N) (hg : Measurable g)
    (hh : ∀ j, n ≤ j → j < M.N → Measurable (h j))
    (hτ : ∀ j, n ≤ j → j < M.N → Measurable (Function.uncurry (τ j))) (x : ℝ) :
    Measurable (fun ω => Fhat h g τ k n x (fun j => M.R j ω)) := by
  have e : (fun ω => Fhat h g τ k n x (fun j => M.R j ω)) = fun ω => Fhat h g τ k n x
      (fun j => if n < j ∧ j ≤ M.N then M.R j ω else 0) := by
    funext ω
    refine Fhat_dep _ _ _ _ _ _ _ _ fun j h1 h2 => ?_
    have : n < j ∧ j ≤ M.N := ⟨h1, by omega⟩
    simp only [this, and_self, if_true]
  rw [e]
  have h0 := Fhat_meas (h := h) (τ := τ) hg k n (fun j a b => hh j a (by omega))
    (fun j a b => hτ j a (by omega))
  refine h0.comp (f := fun ω => (x, fun j => if n < j ∧ j ≤ M.N then M.R j ω else 0))
    (measurable_const.prodMk (measurable_pi_lambda _ fun j => ?_))
  by_cases hj : n < j ∧ j ≤ M.N
  · simp only [hj, and_self, if_true]
    exact M.hR_meas _ (by omega) hj.2
  · simp only [hj, if_false]
    exact measurable_const

lemma Setup.Vpi_val (S : Setup M W f) {k n : ℕ} (hnk : n + k = M.N)
    (hπ : M.IsAdmissible n π) {x : ℝ} (hx : 0 ≤ x)
    (hfin : ∫⁻ ω, Fr M π k n x ω ∂M.measIP ≠ ⊤) :
    M.Vpi π n x = ((bb M k + (∫⁻ ω, Fr M π k n x ω ∂M.measIP).toReal : ℝ) : EReal) := by
  have hk : M.N - n = k := by omega
  have hmF : Measurable (fun ω => Fr M π k n x ω) :=
    Fhat_ω_meas M hnk S.gr_meas (fun j a b => S.hr_meas (hπ j a b).2)
      (fun j a b => tau_meas M (hπ j a b).2) x
  have hmB : Measurable (fun ω => Fb M π k n x ω) :=
    Fhat_ω_meas M hnk gb_meas (fun _ _ _ => gb_meas)
      (fun j a b => tau_meas M (hπ j a b).2) x
  have hb0 := (lintegral_eq_zero_iff hmB).1 (S.bad_zero k n hnk hπ x hx)
  have hae : ∀ᵐ ω ∂M.measIP, ((((M.stateAcc π k n x ω).2 + M.Up (M.stateAcc π k n x ω).1 : ℝ)) : EReal)
      = ((bb M k + (Fr M π k n x ω).toReal : ℝ) : EReal) := by
    filter_upwards [hb0] with ω hω
    obtain ⟨h1, h2⟩ := S.path ω k n hnk hπ x hω
    rw [h2, ENNReal.toReal_ofReal h1]
    congr 1
    ring
  have hint : Integrable (fun ω => bb M k + (Fr M π k n x ω).toReal) M.measIP :=
    (integrable_const _).add (integrable_toReal_of_lintegral_ne_top hmF.aemeasurable hfin)
  unfold ConsumptionInvestmentMarket.Vpi
  rw [hk, ereal_congr hae, ereal_int hint, integral_add (integrable_const _)
    (integrable_toReal_of_lintegral_ne_top hmF.aemeasurable hfin), integral_const,
    integral_toReal hmF.aemeasurable (ae_lt_top hmF hfin)]
  simp

lemma Setup.V_eq (S : Setup M W f) {n : ℕ} (hn : n ≤ M.N) {x : ℝ} (hx : 0 ≤ x) :
    M.V n x = (W n x : EReal) ∧ M.Vpi f n x = (W n x : EReal) := by
  have hnk : n + (M.N - n) = M.N := by omega
  obtain ⟨ih1, ih2⟩ := S.main (M.N - n) n hnk
  have hb := S.W_ge (M.N - n) n hnk x hx
  have hVf : M.Vpi f n x = (W n x : EReal) := by
    rw [S.Vpi_val hnk (S.f_adm n) hx (by rw [ih2 x hx]; exact ENNReal.ofReal_ne_top), ih2 x hx,
      ENNReal.toReal_ofReal (sub_nonneg.2 hb)]
    congr 1
    ring
  refine ⟨le_antisymm ?_ ?_, hVf⟩
  · refine iSup₂_le fun π hπ => ?_
    have hle := ih1 hπ x hx
    rw [S.Vpi_val hnk hπ hx (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)]
    refine EReal.coe_le_coe_iff.2 ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (sub_nonneg.2 hb)] at this
    linarith
  · exact le_iSup₂_of_le f (S.f_adm n) hVf.ge

lemma Setup.val (S : Setup M W f) {n : ℕ} (hn : n < M.N) {x c : ℝ} {a : Fin d → ℝ}
    (hF : Feas M.measIP (M.R (n + 1)) x c a) :
    (M.Uc c : EReal) + erealIntegral M.measIP (fun ω => M.V (n + 1) ((1 + M.i (n + 1)) *
      (x - c + ∑ k, a k * M.R (n + 1) ω k))) =
    ((Jt M.measIP (M.R (n + 1)) (1 + M.i (n + 1)) M.Uc (W (n + 1)) x c a : ℝ) : EReal) := by
  have hq := qpos M hn
  have hG := S.hWg (n + 1) (by omega)
  have hi : Integrable (fun ω => tl (W (n + 1)) ((1 + M.i (n + 1)) *
      (x - c + dot a (M.R (n + 1) ω)))) M.measIP :=
    int_ok (h := fun y => tl (W (n + 1)) ((1 + M.i (n + 1)) * y)) (M.hR_meas _ (by omega) (by omega))
      (S.hRi _ (by omega) (by omega)) ((tl_cont hG).comp (by fun_prop)) (L_nonneg hG hq)
      (tlq_bd hG hq) _ _
  have hae : ∀ᵐ ω ∂M.measIP, M.V (n + 1) ((1 + M.i (n + 1)) *
      (x - c + ∑ k, a k * M.R (n + 1) ω k)) = ((tl (W (n + 1)) ((1 + M.i (n + 1)) *
      (x - c + dot a (M.R (n + 1) ω))) : ℝ) : EReal) := by
    filter_upwards [hF.2.2] with ω hω
    have h0 := mul_nonneg hq.le hω
    rw [tl_of_nonneg h0]
    exact (S.V_eq (by omega) h0).1
  rw [ereal_congr hae, ereal_int hi]
  unfold Jt
  rw [tl_of_nonneg hF.1, EReal.coe_add]
  rfl

theorem exists_setup (M : ConsumptionInvestmentMarket Ω d) (hdom : M.domU = Set.Ici (0 : ℝ))
    (hFM : M.FM2) : ∃ (W : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ × (Fin d → ℝ)), Setup M W f := by
  have step : ∀ (j : ℕ) (w : {w : ℝ → ℝ // Good w}), ∃ v : {w : ℝ → ℝ // Good w},
      ∃ g : ℝ → ℝ × (Fin d → ℝ), j < M.N → (Measurable g ∧ ∀ x, 0 ≤ x →
        Feas M.measIP (M.R (j + 1)) x (g x).1 (g x).2 ∧
        Jt M.measIP (M.R (j + 1)) (1 + M.i (j + 1)) M.Uc w.1 x (g x).1 (g x).2 = v.1 x ∧
        ∀ c a, Feas M.measIP (M.R (j + 1)) x c a →
          Jt M.measIP (M.R (j + 1)) (1 + M.i (j + 1)) M.Uc w.1 x c a ≤ v.1 x) := by
    intro j w
    by_cases hj : j < M.N
    · obtain ⟨K', hK'⟩ := Submodule.exists_isCompl (Ker M.measIP (M.R (j + 1)))
      have C : Ctx M.measIP (M.R (j + 1)) (1 + M.i (j + 1)) M.Uc w.1 K' :=
        ⟨M.hR_meas _ (by omega) (by omega), hFM _ (by omega) (by omega),
          M.hNA _ (by omega) (by omega), qpos M hj, goodUc M hdom, w.2, hK'⟩
      obtain ⟨v, g, hv, hg, h⟩ := C.onestep
      exact ⟨⟨v, hv⟩, g, fun _ => ⟨hg, h⟩⟩
    · exact ⟨w, fun _ => 0, fun h => absurd h hj⟩
  choose SS G hS using step
  let seq : ℕ → {w : ℝ → ℝ // Good w} := fun k =>
    Nat.rec ⟨M.Up, goodUp M hdom⟩ (fun k w => SS (M.N - 1 - k) w) k
  have e : ∀ n, n < M.N → seq (M.N - n) = SS n (seq (M.N - (n + 1))) := by
    intro n hn
    have h1 : M.N - n = (M.N - (n + 1)) + 1 := by omega
    rw [h1]
    show SS (M.N - 1 - (M.N - (n + 1))) _ = _
    have h2 : M.N - 1 - (M.N - (n + 1)) = n := by omega
    rw [h2]
  have hW : ∀ n, n < M.N → (seq (M.N - n)).1 = (SS n (seq (M.N - (n + 1)))).1 := by
    intro n hn
    rw [e n hn]
  refine ⟨fun n => (seq (M.N - n)).1, fun n => G n (seq (M.N - (n + 1))), ⟨hdom, fun n _ => (seq _).2, ?_,
    fun n hn => (hS n _ hn).1, fun n hn x hx => ((hS n _ hn).2 x hx).1, ?_, ?_, hFM⟩⟩
  · show (seq (M.N - M.N)).1 = M.Up
    rw [Nat.sub_self]
    rfl
  · intro n hn x hx
    show _ = (seq (M.N - n)).1 x
    rw [hW n hn]
    exact ((hS n _ hn).2 x hx).2.1
  · intro n hn x hx c a hF
    show _ ≤ (seq (M.N - n)).1 x
    rw [hW n hn]
    exact ((hS n _ hn).2 x hx).2.2 c a hF

end Market

end MDPFinance.ConsumptionInvestment

open MDPFinance.ConsumptionInvestment in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2) :
    (∀ n ≤ M.N, StrictMonoOn (M.V n) M.domU ∧ StrictConcaveOnEReal M.domU (M.V n) ∧
        ContinuousOn (M.V n) M.domU) ∧
      (∀ x ∈ M.domU, M.V M.N x = (M.Up x : EReal)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU,
        M.V n x = ⨆ ca ∈ M.D n x,
          (M.Uc ca.1 : EReal) + erealIntegral M.measIP (fun ω => M.V (n + 1) ((1 + M.i (n + 1)) *
            (x - ca.1 + ∑ k, ca.2 k * M.R (n + 1) ω k)))) ∧
      (∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x ∈ M.domU,
          (M.Uc (fstar n x).1 : EReal) + erealIntegral M.measIP (fun ω => M.V (n + 1)
            ((1 + M.i (n + 1)) * (x - (fstar n x).1 + ∑ k, (fstar n x).2 k * M.R (n + 1) ω k))) =
            M.V n x) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x) := by
  obtain ⟨W, f, S⟩ := exists_setup M hdomU hFM2
  rw [hdomU]
  refine ⟨?_, ?_, ?_, f, S.f_adm 0, ?_, ?_⟩
  · intro n hn
    have G := S.hWg n hn
    refine ⟨?_, ⟨convex_Ici 0, ?_⟩, ?_⟩
    · intro x hx y hy hl
      rw [(S.V_eq hn hx).1, (S.V_eq hn hy).1]
      exact EReal.coe_lt_coe_iff.2 (G.mono hx hy hl)
    · intro x hx y hy hne a b ha hb hab
      have hxy : (0 : ℝ) ≤ a * x + b * y :=
        add_nonneg (mul_nonneg ha.le hx) (mul_nonneg hb.le hy)
      rw [(S.V_eq hn hx).1, (S.V_eq hn hy).1, (S.V_eq hn hxy).1, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_add]
      have := G.conc.2 hx hy hne ha hb hab
      simp only [smul_eq_mul] at this
      exact EReal.coe_lt_coe_iff.2 this
    · exact (continuous_coe_real_ereal.comp_continuousOn G.cont).congr
        (fun x hx => (S.V_eq hn hx).1)
  · intro x hx
    rw [(S.V_eq le_rfl hx).1, S.hWN]
  · intro n hn x hx
    have hx' : (0 : ℝ) ≤ x := hx
    rw [(S.V_eq hn.le hx').1]
    refine le_antisymm ?_ ?_
    · refine le_iSup₂_of_le (f n x) ((D_feas M hdomU hn).2 (S.hff n hn x hx')) ?_
      rw [S.val hn (S.hff n hn x hx'), S.hfJ n hn x hx']
    · refine iSup₂_le fun ca hca => ?_
      have hF := (D_feas M hdomU hn).1 hca
      rw [S.val hn hF]
      exact EReal.coe_le_coe_iff.2 (S.hfle n hn x hx' _ _ hF)
  · intro n hn x hx
    have hx' : (0 : ℝ) ≤ x := hx
    rw [S.val hn (S.hff n hn x hx'), S.hfJ n hn x hx', (S.V_eq hn.le hx').1]
  · intro x hx
    have h := S.V_eq (Nat.zero_le M.N) (x := x) hx
    rw [h.1, h.2]
