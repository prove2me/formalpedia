-- Prove2me | solution 1 for InvShareComp.Exog.lemma_2a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:07:39.544382+00:00
-- url     : https://prove2.me/submissions/3eefb061-3c65-4bb0-a5db-9a56e789b9ce

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

open InvShareComp.Exog InvShareAux InvShareAux2 Filter Topology in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1) (s : ℝ) :
    IsSymEqNoShare P ν I s ↔ s = sHatN P ν I := by
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  have := hν.prob
  have m6 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.1} := by measurability
  have ie := int_ite hν _ m6 (fun ω => ω.1) (by fun_prop)
  set N := P.p * mean ν - P.cbar * ∫ ω, (if 2 * I ≤ ω.1 then ω.1 else 0) ∂ν with hN
  have hdd : ∀ a b : ℝ, dDet P.β a b = 1 / 2 + P.β * (a - b) := by
    intro a b; unfold dDet; ring
  have hg_int : Integrable
      (fun ω : ℝ × ℝ => P.p * ω.1 - P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0)) ν :=
    ((int_cont hν _ continuous_fst).const_mul P.p).sub (ie.const_mul P.cbar)
  have hgI : ∫ ω, (P.p * ω.1 - P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0)) ∂ν = N := by
    rw [integral_sub ((int_cont hν _ continuous_fst).const_mul P.p) (ie.const_mul P.cbar),
      integral_const_mul, integral_const_mul]; rfl
  have hk2 : 0 < 2 * P.k := by linarith
  constructor
  · rintro ⟨h1, -⟩
    set Φ : ℝ → ℝ := fun u => ∫ ω, payNo P I (1 / 2 + u) ω.1 ∂ν with hΦ
    have hΦd : HasDerivAt Φ N 0 := by
      rw [← hgI]
      have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := ν)
        (F := fun u ω => payNo P I (1 / 2 + u) ω.1)
        (F' := fun ω => P.p * ω.1 - P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0))
        (x₀ := 0) (bound := fun _ => P.p + P.cbar) (s := Set.univ) Filter.univ_mem
        (Filter.Eventually.of_forall (fun u =>
          (Continuous.aestronglyMeasurable (by unfold payNo; fun_prop))))
        (int_cont hν _ (by unfold payNo; fun_prop))
        hg_int.aestronglyMeasurable ?lip (integrable_const _) ?diff
      · exact key.2
      case lip =>
        filter_upwards [ae_supp hν] with ω hω
        obtain ⟨⟨he0, he1⟩, -⟩ := hω
        apply LipschitzOnWith.of_dist_le_mul
        intro u _ v _
        rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
          abs_of_nonneg (by linarith : 0 ≤ P.p + P.cbar)]
        unfold payNo
        have hm := abs_max_sub_max_le_abs (ω.1 * (1 / 2 + u) - I) (ω.1 * (1 / 2 + v) - I) 0
        rw [show ω.1 * (1 / 2 + u) - I - (ω.1 * (1 / 2 + v) - I) = ω.1 * (u - v) by ring,
          abs_mul, abs_of_nonneg he0] at hm
        have huv := abs_nonneg (u - v)
        have hw : ω.1 * |u - v| ≤ |u - v| := by nlinarith
        have hA := abs_le.mp (hm.trans hw)
        have hB : |P.p * ω.1 * (u - v)| ≤ P.p * |u - v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg he0, abs_of_nonneg (by linarith : 0 ≤ P.p)]
          nlinarith
        have hB' := abs_le.mp hB
        rw [abs_le]
        constructor <;> nlinarith
      case diff =>
        filter_upwards [ae_ne_fst hν (2 * I)] with ω hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h := deriv_of_local (fun u => payNo P I (1 / 2 + u) ω.1) (P.p * ω.1 / 2) (P.p * ω.1)
            (fun u => ω.1 / 2 - I + ω.1 * u < 0) (ev_neg _ _ (by linarith))
            (fun u hu => by
              simp only [payNo]
              rw [max_eq_right (by linarith)]; ring)
          refine h.congr_deriv ?_
          show _ = P.p * ω.1 - P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0)
          rw [if_neg (not_le.mpr hlt)]; ring
        · have h := deriv_of_local (fun u => payNo P I (1 / 2 + u) ω.1)
            (P.p * ω.1 / 2 - P.cbar * (ω.1 / 2 - I)) (P.p * ω.1 - P.cbar * ω.1)
            (fun u => 0 < ω.1 / 2 - I + ω.1 * u) (ev_pos _ _ (by linarith))
            (fun u hu => by
              simp only [payNo]
              rw [max_eq_left (by linarith)]; ring)
          refine h.congr_deriv ?_
          show _ = P.p * ω.1 - P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0)
          rw [if_pos hgt.le]
    have hf : ∀ s1, profitNo1 P ν I I s1 s
        = Φ (P.β * (s1 - s)) - P.k * s1 ^ 2 - P.c * I := by
      intro s1; unfold profitNo1; simp only [hΦ, hdd]
    have hfd : HasDerivAt (fun s1 => Φ (P.β * (s1 - s)) - P.k * s1 ^ 2 - P.c * I)
        (N * P.β - P.k * (2 * s)) s := by
      have hlin : HasDerivAt (fun s1 => P.β * (s1 - s)) P.β s := by
        simpa using ((hasDerivAt_id s).sub_const s).const_mul P.β
      have hΦ' : HasDerivAt Φ N (P.β * (s - s)) := by simpa using hΦd
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
    unfold sHatN
    rw [← hN]
    field_simp
    linarith
  · intro hs
    have hsN : P.β * N = 2 * P.k * s := by
      rw [hs]; unfold sHatN; rw [← hN]; field_simp
    have hpt : ∀ (x w : ℝ), P.p * (x * (1 / 2 + w)) - P.cbar * max (x * (1 / 2 + w) - I) 0
        ≤ P.p * (x * (1 / 2 + P.β * (s - s))) - P.cbar * max (x * (1 / 2 + P.β * (s - s)) - I) 0
          + (P.p * x - P.cbar * (if 2 * I ≤ x then x else 0)) * w := by
      intro x w
      have hin : max (x / 2 - I) 0 + (if 2 * I ≤ x then x else 0) * w
          ≤ max (x * (1 / 2 + w) - I) 0 := by
        split_ifs with hx
        · rw [max_eq_left (by linarith)]
          have := le_max_left (x * (1 / 2 + w) - I) 0
          nlinarith
        · rw [max_eq_right (by linarith)]
          simp
      have := mul_le_mul_of_nonneg_left hin (by linarith : 0 ≤ P.cbar)
      simp only [sub_self, mul_zero, add_zero]
      rw [show x * (1 / 2) - I = x / 2 - I by ring]
      nlinarith
    have hcont : ∀ w : ℝ, Continuous fun ω : ℝ × ℝ =>
        P.p * (ω.1 * (1 / 2 + w)) - P.cbar * max (ω.1 * (1 / 2 + w) - I) 0 := by
      intro w; fun_prop
    have hcont2 : ∀ w : ℝ, Continuous fun ω : ℝ × ℝ =>
        P.p * (ω.2 * (1 / 2 + w)) - P.cbar * max (ω.2 * (1 / 2 + w) - I) 0 := by
      intro w; fun_prop
    -- swapped version of the supergradient integral
    have hgI2 : ∫ ω, (P.p * ω.2 - P.cbar * (if 2 * I ≤ ω.2 then ω.2 else 0)) ∂ν = N := by
      rw [← hgI]
      exact swap_eq hν (fun ω => P.p * ω.1 - P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0))
    have hg_int2 : Integrable
        (fun ω : ℝ × ℝ => P.p * ω.2 - P.cbar * (if 2 * I ≤ ω.2 then ω.2 else 0)) ν := by
      have m7 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2} := by measurability
      exact ((int_cont hν _ continuous_snd).const_mul P.p).sub
        ((int_ite hν _ m7 (fun ω => ω.2) (by fun_prop)).const_mul P.cbar)
    constructor
    · intro s' _
      unfold profitNo1
      simp only [hdd, payNo]
      have hI1 := integral_mono (int_cont hν _ (hcont (P.β * (s' - s))))
        ((int_cont hν _ (hcont (P.β * (s - s)))).add (hg_int.mul_const (P.β * (s' - s))))
        (fun ω => hpt ω.1 (P.β * (s' - s)))
      simp only [Pi.add_apply] at hI1
      rw [integral_add (int_cont hν _ (hcont (P.β * (s - s))))
        (hg_int.mul_const (P.β * (s' - s))), integral_mul_const, hgI] at hI1
      have e : N * (P.β * (s' - s)) = 2 * P.k * s * (s' - s) := by
        rw [← mul_assoc, mul_comm N, hsN]
      nlinarith [mul_nonneg hk.le (sq_nonneg (s' - s))]
    · intro s' _
      unfold profitNo2
      simp only [hdd, payNo]
      have hI1 := integral_mono (int_cont hν _ (hcont2 (P.β * (s' - s))))
        ((int_cont hν _ (hcont2 (P.β * (s - s)))).add (hg_int2.mul_const (P.β * (s' - s))))
        (fun ω => hpt ω.2 (P.β * (s' - s)))
      simp only [Pi.add_apply] at hI1
      rw [integral_add (int_cont hν _ (hcont2 (P.β * (s - s))))
        (hg_int2.mul_const (P.β * (s' - s))), integral_mul_const, hgI2] at hI1
      have e : N * (P.β * (s' - s)) = 2 * P.k * s * (s' - s) := by
        rw [← mul_assoc, mul_comm N, hsN]
      nlinarith [mul_nonneg hk.le (sq_nonneg (s' - s))]
