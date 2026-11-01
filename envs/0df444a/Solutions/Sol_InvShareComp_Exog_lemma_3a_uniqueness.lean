-- Prove2me | solution 1 for InvShareComp.Exog.lemma_3a_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:12:49.304+00:00
-- url     : https://prove2.me/submissions/773f275b-7f7e-49fc-8bdf-e9f313ddf90d

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

open MeasureTheory Classical

namespace InvShareAux
open MeasureTheory InvShareComp.Exog

theorem ae_supp {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) :
    ∀ᵐ ω ∂ν, ω ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
  rw [ae_iff]; exact hν.support

theorem int_cont {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : Integrable f ν := by
  have := hν.prob
  have hrestr : ν.restrict (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_supp hν)
  rw [← hrestr]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem int_ite {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (p : ℝ × ℝ → Prop)
    [DecidablePred p] (hp : MeasurableSet {ω | p ω}) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : Integrable (fun ω => if p ω then f ω else 0) ν := by
  have h := (int_cont hν f hf).indicator hp
  have e : (fun ω => if p ω then f ω else 0) = {ω | p ω}.indicator f := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [e]; exact h

theorem swap_eq {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (g : ℝ × ℝ → ℝ) :
    ∫ ω, g (ω.2, ω.1) ∂ν = ∫ ω, g ω ∂ν := by
  have h := integral_map_equiv (μ := ν) (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) g
  have hm : Measure.map (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) ν = ν := hν.exch
  rw [hm] at h
  rw [h]; rfl

end InvShareAux
namespace InvShareAux2
open MeasureTheory InvShareComp.Exog Filter Topology

theorem vol_fst (c : ℝ) : (volume : Measure (ℝ × ℝ)) {ω | ω.1 = c} = 0 := by
  have : {ω : ℝ × ℝ | ω.1 = c} = {c} ×ˢ Set.univ := by ext ω; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

theorem vol_snd (c : ℝ) : (volume : Measure (ℝ × ℝ)) {ω | ω.2 = c} = 0 := by
  have : {ω : ℝ × ℝ | ω.2 = c} = Set.univ ×ˢ {c} := by ext ω; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

theorem vol_sum (c : ℝ) : (volume : Measure (ℝ × ℝ)) {ω | ω.1 + ω.2 = c} = 0 := by
  rw [Measure.volume_eq_prod, Measure.measure_prod_null
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  apply Filter.Eventually.of_forall
  intro x
  have : Prod.mk x ⁻¹' {ω : ℝ × ℝ | ω.1 + ω.2 = c} = {c - x} := by
    ext y; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor <;> intro h <;> linarith
  simp [this]

theorem ae_ne_fst {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (c : ℝ) : ∀ᵐ ω ∂ν, ω.1 ≠ c :=
  hν.density.ae_le (show ∀ᵐ ω ∂(volume : Measure (ℝ × ℝ)), ω.1 ≠ c by
    rw [ae_iff]; simpa using vol_fst c)

theorem ae_ne_snd {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (c : ℝ) : ∀ᵐ ω ∂ν, ω.2 ≠ c :=
  hν.density.ae_le (show ∀ᵐ ω ∂(volume : Measure (ℝ × ℝ)), ω.2 ≠ c by
    rw [ae_iff]; simpa using vol_snd c)

theorem ae_ne_sum {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (c : ℝ) :
    ∀ᵐ ω ∂ν, ω.1 + ω.2 ≠ c :=
  hν.density.ae_le (show ∀ᵐ ω ∂(volume : Measure (ℝ × ℝ)), ω.1 + ω.2 ≠ c by
    rw [ae_iff]; simpa using vol_sum c)

theorem ev_feasible (β s : ℝ) : ∀ᶠ s' in 𝓝 s, Feasible β s' s := by
  have h1 : ∀ᶠ s' in 𝓝 s, (0:ℝ) < dDet β s' s := by
    apply ContinuousAt.eventually_lt continuousAt_const
    · unfold dDet; fun_prop
    · unfold dDet; norm_num
  have h2 : ∀ᶠ s' in 𝓝 s, (0:ℝ) < dDet β s s' := by
    apply ContinuousAt.eventually_lt continuousAt_const
    · unfold dDet; fun_prop
    · unfold dDet; norm_num
  filter_upwards [h1, h2] with s' a b
  exact ⟨a.le, b.le⟩

/-- local affinity gives the derivative -/
theorem deriv_of_local (F : ℝ → ℝ) (c d : ℝ) (Q : ℝ → Prop) (hQ : ∀ᶠ u in 𝓝 (0:ℝ), Q u)
    (hF : ∀ u, Q u → F u = c + d * u) : HasDerivAt F d 0 := by
  have h : HasDerivAt (fun u : ℝ => c + d * u) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul d).const_add c
  apply h.congr_of_eventuallyEq
  filter_upwards [hQ] with u hu
  exact hF u hu

theorem ev_pos (α γ : ℝ) (h : 0 < α) : ∀ᶠ u in 𝓝 (0:ℝ), 0 < α + γ * u := by
  apply ContinuousAt.eventually_lt continuousAt_const (by fun_prop)
  simpa using h

theorem ev_neg (α γ : ℝ) (h : α < 0) : ∀ᶠ u in 𝓝 (0:ℝ), α + γ * u < 0 := by
  apply ContinuousAt.eventually_lt (by fun_prop) continuousAt_const
  simpa using h

end InvShareAux2

namespace InvShareAux3
open MeasureTheory InvShareComp.Exog Filter Topology

/-- the pointwise derivative of the sharing payoff (the integrand of `pμ - A - B`) -/
noncomputable def DS (P : Params) (t I : ℝ) (ω : ℝ × ℝ) : ℝ :=
  P.p * ω.1 - ((if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then (t + P.δ) * ω.1 else 0)
    + (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1
        then P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2 else 0))
  - ((if 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2 then t * ω.2 else 0)
    + (if 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I then t * ω.1 else 0)
    + (if 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1 then P.cbar * ω.1 else 0))

theorem mm_bound (a b c d L : ℝ) (h1 : |a - c| ≤ L) (h2 : |b - d| ≤ L) :
    |max (min a b) 0 - max (min c d) 0| ≤ L :=
  (abs_max_sub_max_le_abs _ _ 0).trans ((abs_min_sub_min_le_max a b c d).trans (max_le h1 h2))

theorem mm2_bound (a b c d L : ℝ) (h1 : |a - c| ≤ L) (h2 : |b - d| ≤ L) :
    |max (max a 0 - max b 0) 0 - max (max c 0 - max d 0) 0| ≤ 2 * L := by
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have e1 := (abs_max_sub_max_le_abs a c 0).trans h1
  have e2 := (abs_max_sub_max_le_abs b d 0).trans h2
  calc |max a 0 - max b 0 - (max c 0 - max d 0)|
      = |(max a 0 - max c 0) - (max b 0 - max d 0)| := by ring_nf
    _ ≤ |max a 0 - max c 0| + |max b 0 - max d 0| := abs_sub _ _
    _ ≤ 2 * L := by linarith

section regions
variable (P : Params) (t I d1 d2 e e' : ℝ)

theorem ps_i (hX : 0 < e * d1 - I) (hY : 0 < I - e' * d2) (hXY : e * d1 - I < I - e' * d2) :
    payShare P t I I d1 d2 e e' = P.p * (e * d1) - (t + P.δ) * (e * d1 - I) := by
  unfold payShare
  rw [max_eq_right (min_le_of_left_le (by linarith)), min_eq_left hXY.le,
    max_eq_left hX.le, max_eq_left hY.le, max_eq_right (by linarith)]
  ring

theorem ps_ii (hX : 0 < e * d1 - I) (hY : 0 < I - e' * d2) (hXY : I - e' * d2 < e * d1 - I) :
    payShare P t I I d1 d2 e e'
      = P.p * (e * d1) - (t + P.δ) * (I - e' * d2) - P.cbar * ((e * d1 - I) - (I - e' * d2)) := by
  unfold payShare
  rw [max_eq_right (min_le_of_left_le (by linarith)), min_eq_right hXY.le,
    max_eq_left hY.le, max_eq_left hX.le, max_eq_left (by linarith)]
  ring

theorem ps_iii (hX : 0 < e * d1 - I) (hY : I - e' * d2 < 0) :
    payShare P t I I d1 d2 e e' = P.p * (e * d1) - P.cbar * (e * d1 - I) := by
  unfold payShare
  rw [max_eq_right (min_le_of_left_le (by linarith)), max_eq_right (min_le_of_right_le hY.le),
    max_eq_left hX.le, max_eq_right hY.le, sub_zero, max_eq_left hX.le]
  ring

theorem ps_iv (hX : e * d1 - I < 0) (hY : 0 < I - e' * d2) :
    payShare P t I I d1 d2 e e' = P.p * (e * d1) := by
  unfold payShare
  rw [max_eq_right (min_le_of_right_le (by linarith)), max_eq_right (min_le_of_left_le hX.le),
    max_eq_right hX.le, max_eq_left hY.le, max_eq_right (by linarith)]
  ring

theorem ps_v (hX : e * d1 - I < 0) (hY : I - e' * d2 < 0) (hXY : e * d1 - I < I - e' * d2) :
    payShare P t I I d1 d2 e e' = P.p * (e * d1) + t * (-(I - e' * d2)) := by
  unfold payShare
  rw [min_eq_right (by linarith : e' * d2 - I ≤ I - e * d1), max_eq_left (by linarith),
    max_eq_right (min_le_of_left_le hX.le), max_eq_right hX.le, max_eq_right hY.le,
    sub_zero, max_eq_left (le_refl 0)]
  ring

theorem ps_vi (hX : e * d1 - I < 0) (hY : I - e' * d2 < 0) (hXY : I - e' * d2 < e * d1 - I) :
    payShare P t I I d1 d2 e e' = P.p * (e * d1) + t * (-(e * d1 - I)) := by
  unfold payShare
  rw [min_eq_left (by linarith : I - e * d1 ≤ e' * d2 - I), max_eq_left (by linarith),
    max_eq_right (min_le_of_left_le hX.le), max_eq_right hX.le, max_eq_right hY.le,
    sub_zero, max_eq_left (le_refl 0)]
  ring

end regions

end InvShareAux3

open InvShareComp.Exog InvShareAux InvShareAux2 InvShareAux3 Filter Topology in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) (s : ℝ) :
    IsSymEqShare P ν t I s → s = sHat P ν t I := by
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  obtain ⟨ht0, ht1⟩ := ht
  have := hν.prob
  rintro ⟨h1, -⟩
  have m1 : MeasurableSet {ω : ℝ × ℝ | ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2} := by
    measurability
  have m2 : MeasurableSet {ω : ℝ × ℝ | ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1} := by measurability
  have m3 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2} := by measurability
  have m4 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I} := by
    measurability
  have m5 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1} := by measurability
  have i1 := int_ite hν _ m1 (fun ω => (t + P.δ) * ω.1) (by fun_prop)
  have i2 := int_ite hν _ m2 (fun ω => P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2) (by fun_prop)
  have i3 := int_ite hν _ m3 (fun ω => t * ω.2) (by fun_prop)
  have i4 := int_ite hν _ m4 (fun ω => t * ω.1) (by fun_prop)
  have i5 := int_ite hν _ m5 (fun ω => P.cbar * ω.1) (by fun_prop)
  have ip := (int_cont hν _ continuous_fst).const_mul P.p
  have hDint : Integrable (DS P t I) ν := (ip.sub (i1.add i2)).sub ((i3.add i4).add i5)
  have hDI : ∫ ω, DS P t I ω ∂ν = SVal P ν t I := by
    have j1 := integral_sub (ip.sub (i1.add i2)) ((i3.add i4).add i5)
    have j2 := integral_sub ip (i1.add i2)
    simp only [Pi.add_apply, Pi.sub_apply] at j1 j2
    unfold DS SVal Aval Bval mean
    rw [j1, j2, integral_const_mul]
  have hk2 : 0 < 2 * P.k := by linarith
  set K : ℝ := P.p + t + (t + P.δ) + P.cbar * 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; nlinarith
  set Φ : ℝ → ℝ := fun u => ∫ ω, payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2 ∂ν with hΦ
  have hcF : ∀ u : ℝ, Continuous fun ω : ℝ × ℝ =>
      payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2 := by
    intro u; unfold payShare; fun_prop
  have hΦd : HasDerivAt Φ (SVal P ν t I) 0 := by
    rw [← hDI]
    have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := ν)
      (F := fun u ω => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2)
      (F' := DS P t I)
      (x₀ := 0) (bound := fun _ => K) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall (fun u => (hcF u).aestronglyMeasurable))
      (int_cont hν _ (hcF 0))
      hDint.aestronglyMeasurable ?lip (integrable_const _) ?diff
    · exact key.2
    case lip =>
      filter_upwards [ae_supp hν] with ω hω
      obtain ⟨⟨he0, he1⟩, ⟨hf0, hf1⟩⟩ := hω
      apply LipschitzOnWith.of_dist_le_mul
      intro u _ v _
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hK0]
      have huv := abs_nonneg (u - v)
      have b1 : |(I - ω.1 * (1 / 2 + u)) - (I - ω.1 * (1 / 2 + v))| ≤ |u - v| := by
        rw [show (I - ω.1 * (1 / 2 + u)) - (I - ω.1 * (1 / 2 + v)) = ω.1 * (v - u) by ring,
          abs_mul, abs_of_nonneg he0, abs_sub_comm]; nlinarith
      have b2 : |(ω.2 * (1 / 2 - u) - I) - (ω.2 * (1 / 2 - v) - I)| ≤ |u - v| := by
        rw [show (ω.2 * (1 / 2 - u) - I) - (ω.2 * (1 / 2 - v) - I) = ω.2 * (v - u) by ring,
          abs_mul, abs_of_nonneg hf0, abs_sub_comm]; nlinarith
      have b3 : |(ω.1 * (1 / 2 + u) - I) - (ω.1 * (1 / 2 + v) - I)| ≤ |u - v| := by
        rw [show (ω.1 * (1 / 2 + u) - I) - (ω.1 * (1 / 2 + v) - I) = ω.1 * (u - v) by ring,
          abs_mul, abs_of_nonneg he0]; nlinarith
      have b4 : |(I - ω.2 * (1 / 2 - u)) - (I - ω.2 * (1 / 2 - v))| ≤ |u - v| := by
        rw [show (I - ω.2 * (1 / 2 - u)) - (I - ω.2 * (1 / 2 - v)) = ω.2 * (u - v) by ring,
          abs_mul, abs_of_nonneg hf0]; nlinarith
      have T1 := abs_le.mp (mm_bound _ _ _ _ _ b1 b2)
      have T2 := abs_le.mp (mm_bound _ _ _ _ _ b3 b4)
      have T3 := abs_le.mp (mm2_bound _ _ _ _ _ b3 b4)
      have T0 : |P.p * (ω.1 * (1 / 2 + u)) - P.p * (ω.1 * (1 / 2 + v))| ≤ P.p * |u - v| := by
        rw [show P.p * (ω.1 * (1 / 2 + u)) - P.p * (ω.1 * (1 / 2 + v))
            = P.p * ω.1 * (u - v) by ring, abs_mul, abs_mul, abs_of_nonneg he0,
          abs_of_nonneg (by linarith : 0 ≤ P.p)]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ P.p) huv,
          mul_nonneg (sub_nonneg.2 he1) (mul_nonneg (by linarith : (0:ℝ) ≤ P.p) huv)]
      have T0' := abs_le.mp T0
      have p1a := mul_le_mul_of_nonneg_left T1.1 ht0
      have p1b := mul_le_mul_of_nonneg_left T1.2 ht0
      have p2a := mul_le_mul_of_nonneg_left T2.1 (by linarith : 0 ≤ t + P.δ)
      have p2b := mul_le_mul_of_nonneg_left T2.2 (by linarith : 0 ≤ t + P.δ)
      have p3a := mul_le_mul_of_nonneg_left T3.1 (by linarith : 0 ≤ P.cbar)
      have p3b := mul_le_mul_of_nonneg_left T3.2 (by linarith : 0 ≤ P.cbar)
      unfold payShare
      rw [abs_le, hK]
      constructor
      · linarith
      · linarith
    case diff =>
      filter_upwards [ae_ne_fst hν (2 * I), ae_ne_snd hν (2 * I), ae_ne_sum hν (4 * I)]
        with ω n1 n2 n3
      rcases lt_or_gt_of_ne n1 with a1 | a1 <;> rcases lt_or_gt_of_ne n2 with a2 | a2 <;>
        rcases lt_or_gt_of_ne n3 with a3 | a3
      · have h := deriv_of_local
            (fun u => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2) (P.p * ω.1 / 2) (P.p * ω.1)
            (fun u => (ω.1 / 2 - I + ω.1 * u < 0) ∧ (0 < I - ω.2 / 2 + ω.2 * u))
            (by filter_upwards [ev_neg _ ω.1 (by linarith : ω.1 / 2 - I < 0), ev_pos _ ω.2 (by linarith : (0:ℝ) < I - ω.2 / 2)] with u hu1 hu2; exact ⟨hu1, hu2⟩)
            (fun u hu => by
              obtain ⟨hu1, hu2⟩ := hu
              rw [ps_iv P t I _ _ _ _ (by linarith [hu1]) (by linarith [hu2])]; ring)
        refine h.congr_deriv ?_
        have f1 := (a2 : ω.2 < 2 * I)
        have f2 := (a1 : ω.1 < 2 * I)
        have f3 := (by linarith : ω.1 < 4 * I - ω.2)
        unfold DS
        simp only [← not_lt]
        simp only [f1, f2, f3, not_true_eq_false, not_false_eq_true, and_true, true_and,
          and_false, false_and, if_true, if_false]
        ring
      · exfalso; linarith
      · have h := deriv_of_local
            (fun u => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2) (P.p * ω.1 / 2 - t * (I - ω.2 / 2)) (P.p * ω.1 - t * ω.2)
            (fun u => (ω.1 / 2 - I + ω.1 * u < 0) ∧ (I - ω.2 / 2 + ω.2 * u < 0) ∧ (0 < I - ω.2 / 2 - (ω.1 / 2 - I) + (ω.2 - ω.1) * u))
            (by filter_upwards [ev_neg _ ω.1 (by linarith : ω.1 / 2 - I < 0), ev_neg _ ω.2 (by linarith : I - ω.2 / 2 < 0), ev_pos _ (ω.2 - ω.1) (by linarith : (0:ℝ) < I - ω.2 / 2 - (ω.1 / 2 - I))] with u hu1 hu2 hu3; exact ⟨hu1, hu2, hu3⟩)
            (fun u hu => by
              obtain ⟨hu1, hu2, hu3⟩ := hu
              rw [ps_v P t I _ _ _ _ (by linarith [hu1]) (by linarith [hu2]) (by linarith [hu3])]; ring)
        refine h.congr_deriv ?_
        have f1 := (not_lt.mpr a2.le : ¬ ω.2 < 2 * I)
        have f2 := (a1 : ω.1 < 2 * I)
        have f3 := (by linarith : ω.1 < 4 * I - ω.2)
        unfold DS
        simp only [← not_lt]
        simp only [f1, f2, f3, not_true_eq_false, not_false_eq_true, and_true, true_and,
          and_false, false_and, if_true, if_false]
        ring
      · have h := deriv_of_local
            (fun u => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2) (P.p * ω.1 / 2 - t * (ω.1 / 2 - I)) (P.p * ω.1 - t * ω.1)
            (fun u => (ω.1 / 2 - I + ω.1 * u < 0) ∧ (I - ω.2 / 2 + ω.2 * u < 0) ∧ (I - ω.2 / 2 - (ω.1 / 2 - I) + (ω.2 - ω.1) * u < 0))
            (by filter_upwards [ev_neg _ ω.1 (by linarith : ω.1 / 2 - I < 0), ev_neg _ ω.2 (by linarith : I - ω.2 / 2 < 0), ev_neg _ (ω.2 - ω.1) (by linarith : I - ω.2 / 2 - (ω.1 / 2 - I) < 0)] with u hu1 hu2 hu3; exact ⟨hu1, hu2, hu3⟩)
            (fun u hu => by
              obtain ⟨hu1, hu2, hu3⟩ := hu
              rw [ps_vi P t I _ _ _ _ (by linarith [hu1]) (by linarith [hu2]) (by linarith [hu3])]; ring)
        refine h.congr_deriv ?_
        have f1 := (not_lt.mpr a2.le : ¬ ω.2 < 2 * I)
        have f2 := (a1 : ω.1 < 2 * I)
        have f3 := (by intro h; linarith : ¬ ω.1 < 4 * I - ω.2)
        unfold DS
        simp only [← not_lt]
        simp only [f1, f2, f3, not_true_eq_false, not_false_eq_true, and_true, true_and,
          and_false, false_and, if_true, if_false]
        ring
      · have h := deriv_of_local
            (fun u => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2) (P.p * ω.1 / 2 - (t + P.δ) * (ω.1 / 2 - I)) (P.p * ω.1 - (t + P.δ) * ω.1)
            (fun u => (0 < ω.1 / 2 - I + ω.1 * u) ∧ (0 < I - ω.2 / 2 + ω.2 * u) ∧ (0 < I - ω.2 / 2 - (ω.1 / 2 - I) + (ω.2 - ω.1) * u))
            (by filter_upwards [ev_pos _ ω.1 (by linarith : (0:ℝ) < ω.1 / 2 - I), ev_pos _ ω.2 (by linarith : (0:ℝ) < I - ω.2 / 2), ev_pos _ (ω.2 - ω.1) (by linarith : (0:ℝ) < I - ω.2 / 2 - (ω.1 / 2 - I))] with u hu1 hu2 hu3; exact ⟨hu1, hu2, hu3⟩)
            (fun u hu => by
              obtain ⟨hu1, hu2, hu3⟩ := hu
              rw [ps_i P t I _ _ _ _ (by linarith [hu1]) (by linarith [hu2]) (by linarith [hu3])]; ring)
        refine h.congr_deriv ?_
        have f1 := (a2 : ω.2 < 2 * I)
        have f2 := (not_lt.mpr a1.le : ¬ ω.1 < 2 * I)
        have f3 := (by linarith : ω.1 < 4 * I - ω.2)
        unfold DS
        simp only [← not_lt]
        simp only [f1, f2, f3, not_true_eq_false, not_false_eq_true, and_true, true_and,
          and_false, false_and, if_true, if_false]
        ring
      · have h := deriv_of_local
            (fun u => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2) (P.p * ω.1 / 2 - (t + P.δ) * (I - ω.2 / 2) - P.cbar * ((ω.1 / 2 - I) - (I - ω.2 / 2))) (P.p * ω.1 - (t + P.δ) * ω.2 - P.cbar * (ω.1 - ω.2))
            (fun u => (0 < ω.1 / 2 - I + ω.1 * u) ∧ (0 < I - ω.2 / 2 + ω.2 * u) ∧ (I - ω.2 / 2 - (ω.1 / 2 - I) + (ω.2 - ω.1) * u < 0))
            (by filter_upwards [ev_pos _ ω.1 (by linarith : (0:ℝ) < ω.1 / 2 - I), ev_pos _ ω.2 (by linarith : (0:ℝ) < I - ω.2 / 2), ev_neg _ (ω.2 - ω.1) (by linarith : I - ω.2 / 2 - (ω.1 / 2 - I) < 0)] with u hu1 hu2 hu3; exact ⟨hu1, hu2, hu3⟩)
            (fun u hu => by
              obtain ⟨hu1, hu2, hu3⟩ := hu
              rw [ps_ii P t I _ _ _ _ (by linarith [hu1]) (by linarith [hu2]) (by linarith [hu3])]; ring)
        refine h.congr_deriv ?_
        have f1 := (a2 : ω.2 < 2 * I)
        have f2 := (not_lt.mpr a1.le : ¬ ω.1 < 2 * I)
        have f3 := (by intro h; linarith : ¬ ω.1 < 4 * I - ω.2)
        unfold DS
        simp only [← not_lt]
        simp only [f1, f2, f3, not_true_eq_false, not_false_eq_true, and_true, true_and,
          and_false, false_and, if_true, if_false]
        ring
      · exfalso; linarith
      · have h := deriv_of_local
            (fun u => payShare P t I I (1 / 2 + u) (1 / 2 - u) ω.1 ω.2) (P.p * ω.1 / 2 - P.cbar * (ω.1 / 2 - I)) (P.p * ω.1 - P.cbar * ω.1)
            (fun u => (0 < ω.1 / 2 - I + ω.1 * u) ∧ (I - ω.2 / 2 + ω.2 * u < 0))
            (by filter_upwards [ev_pos _ ω.1 (by linarith : (0:ℝ) < ω.1 / 2 - I), ev_neg _ ω.2 (by linarith : I - ω.2 / 2 < 0)] with u hu1 hu2; exact ⟨hu1, hu2⟩)
            (fun u hu => by
              obtain ⟨hu1, hu2⟩ := hu
              rw [ps_iii P t I _ _ _ _ (by linarith [hu1]) (by linarith [hu2])]; ring)
        refine h.congr_deriv ?_
        have f1 := (not_lt.mpr a2.le : ¬ ω.2 < 2 * I)
        have f2 := (not_lt.mpr a1.le : ¬ ω.1 < 2 * I)
        have f3 := (by intro h; linarith : ¬ ω.1 < 4 * I - ω.2)
        unfold DS
        simp only [← not_lt]
        simp only [f1, f2, f3, not_true_eq_false, not_false_eq_true, and_true, true_and,
          and_false, false_and, if_true, if_false]
        ring
  have hf : ∀ s1, profitShare1 P ν t I I s1 s
      = Φ (P.β * (s1 - s)) - P.k * s1 ^ 2 - P.c * I := by
    intro s1
    unfold profitShare1
    rw [show dDet P.β s1 s = 1 / 2 + P.β * (s1 - s) by unfold dDet; ring,
      show dDet P.β s s1 = 1 / 2 - P.β * (s1 - s) by unfold dDet; ring]
  have hfd : HasDerivAt (fun s1 => Φ (P.β * (s1 - s)) - P.k * s1 ^ 2 - P.c * I)
      (SVal P ν t I * P.β - P.k * (2 * s)) s := by
    have hlin : HasDerivAt (fun s1 => P.β * (s1 - s)) P.β s := by
      simpa using ((hasDerivAt_id s).sub_const s).const_mul P.β
    have hΦ' : HasDerivAt Φ (SVal P ν t I) (P.β * (s - s)) := by simpa using hΦd
    have hc := hΦ'.comp s hlin
    have hsq : HasDerivAt (fun s1 => P.k * s1 ^ 2) (P.k * (2 * s)) s := by
      simpa using (hasDerivAt_pow 2 s).const_mul P.k
    exact (hc.sub hsq).sub_const _
  have hmax : IsLocalMax (fun s1 => Φ (P.β * (s1 - s)) - P.k * s1 ^ 2 - P.c * I) s := by
    filter_upwards [ev_feasible P.β s] with s' hs'
    have := h1 s' hs'
    rw [hf, hf] at this
    exact this
  have h0 := hmax.hasDerivAt_eq_zero hfd
  unfold sHat
  field_simp
  linarith
