-- Prove2me | solution 1 for GlobalTheory.ZeroFreePrincipal.zero_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:13:18.060843+00:00
-- url     : https://prove2.me/submissions/3bc3f2ee-74e1-427e-890b-970683a151e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Theorems.Thm_GlobalTheory_ZetaLocal_logDeriv_riemannZeta_local
import Theorems.Thm_GlobalTheory_logDerivativeThreeFourOne_three_four_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
namespace GlobalTheory.ZeroFreePrincipal
open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
open Filter Topology in
private lemma one_le_analyticOrderNatAt_riemannZeta_of_eq_zero {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz' =>
    (differentiableAt_riemannZeta hz').differentiableWithinAt
  have han : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := hd.analyticOnNhd hU
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    have : analyticOrderAt riemannZeta 2 = 0 :=
      analyticOrderAt_eq_zero.2 (Or.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num)))
    simp [this]
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected hconn (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
      hρ h2
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := analyticOrderAt_ne_zero.2 ⟨han ρ hρ, hz⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have : analyticOrderNatAt riemannZeta ρ = n := by simp [analyticOrderNatAt, ← hn]
  rw [this]
  rcases Nat.eq_zero_or_pos n with h | h
  · exact absurd (by rw [← hn, h]; rfl) hne
  · exact h
open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
open Filter Topology in
private lemma neg_re_logDeriv_riemannZeta_le_sub_inv_dist_zero_add_log {C : ℝ}
    (hC : ∀ (t : ℝ) (s : ℂ), ‖s - (3 / 2 + ↑t * I)‖ ≤ 2 / 3 → s ≠ 1 → riemannZeta s ≠ 0 →
      {w | ‖w - (3 / 2 + ↑t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
        ∑ᶠ (w : ℂ) (_ : w ∈ {w | ‖w - (3 / 2 + ↑t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0}),
          ↑(analyticOrderNatAt riemannZeta w) / (s - w)‖ ≤ C * Real.log (|t| + 2))
    (t σ : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (r : ℝ)
    (hr : r = 0 ∨ ∃ β : ℝ, riemannZeta (β + t * I) = 0 ∧ 2 / 3 ≤ β ∧ r = 1 / (σ - β)) :
    -(deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)).re ≤
      (1 / ((σ : ℂ) + t * I - 1)).re - r + C * Real.log (|t| + 2) := by
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : ‖s - (3 / 2 + ↑t * I)‖ ≤ 2 / 3 := by
    have : s - (3 / 2 + ↑t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hs]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hne1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; linarith)
  obtain ⟨hfin, hb⟩ := hC t s hs1 hne1 hζ
  set Z := {w | ‖w - (3 / 2 + ↑t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZ
  have hsum : (∑ᶠ (w : ℂ) (_ : w ∈ Z), (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) =
      ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [hsum] at hb
  have hterm : ∀ w ∈ hfin.toFinset, ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re =
      analyticOrderNatAt riemannZeta w * (s - w).re / Complex.normSq (s - w) := by
    intro w _
    rw [div_eq_mul_inv, ← ofReal_natCast, re_ofReal_mul, inv_re]
    ring
  have hnonneg : ∀ w ∈ hfin.toFinset, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    rw [hterm w hw]
    have hwZ : w ∈ Z := hfin.mem_toFinset.1 hw
    have hwre : w.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h) hwZ.2.2
    have : 0 < (s - w).re := by rw [sub_re, hsre]; linarith
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) this.le) (Complex.normSq_nonneg _)
  set S := ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hS
  have hSre : S.re = ∑ w ∈ hfin.toFinset, ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re :=
    Complex.re_sum _ _
  have hrS : r ≤ S.re := by
    rcases hr with rfl | ⟨β, hβ, hβ1, rfl⟩
    · rw [hSre]; exact Finset.sum_nonneg hnonneg
    · have hβ2 : β < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (by simpa using not_lt.1 h) hβ
      set ρ : ℂ := β + t * I with hρ
      have hρ1 : ρ ≠ 1 := by
        intro h; have := congrArg Complex.re h; simp [hρ] at this; linarith
      have hρZ : ρ ∈ Z := by
        refine ⟨?_, hρ1, hβ⟩
        have : ρ - (3 / 2 + ↑t * I) = ((β - 3 / 2 : ℝ) : ℂ) := by
          rw [hρ]; push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have hρmem : ρ ∈ hfin.toFinset := hfin.mem_toFinset.2 hρZ
      have hsρ : s - ρ = ((σ - β : ℝ) : ℂ) := by rw [hs, hρ]; push_cast; ring
      have hm := one_le_analyticOrderNatAt_riemannZeta_of_eq_zero hρ1 hβ
      have hval : ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re =
          analyticOrderNatAt riemannZeta ρ / (σ - β) := by
        rw [hsρ, ← ofReal_natCast, ← ofReal_div, ofReal_re]
      rw [hSre]
      refine le_trans ?_ (Finset.single_le_sum hnonneg hρmem)
      rw [hval]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (by linarith)
  have hX := (abs_le.1 ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [sub_re, add_re] at hX
  linarith
open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
open Filter Topology in
private lemma three_four_one_neg_re_logDeriv_riemannZeta_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ -(3 * (deriv riemannZeta σ / riemannZeta σ).re +
      4 * (deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)).re +
      (deriv riemannZeta (σ + 2 * t * I) / riemannZeta (σ + 2 * t * I)).re) := by
  have := _root_.GlobalTheory.logDerivativeThreeFourOne.three_four_one 1 (1 : DirichletCharacter ℂ 1) σ t hσ
  simpa using this
open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
open Filter Topology in
private lemma re_one_div_le_re_of_re_pos_of_one_le_abs_im {z : ℂ} (hre : 0 < z.re) (him : 1 ≤ |z.im|) :
    (1 / z).re ≤ z.re := by
  rw [one_div, inv_re, Complex.normSq_apply]
  have h1 : 1 ≤ z.im * z.im := by nlinarith [abs_mul_abs_self z.im, abs_nonneg z.im]
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith
open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
open Filter Topology in
private lemma exists_re_lt_one_sub_div_log_of_riemannZeta_eq_zero : ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ,
    riemannZeta s = 0 → 1 ≤ |s.im| → s.re < 1 - c / Real.log (|s.im| + 2) := by
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local
  set K : ℝ := 9 * C + 5 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨1 / (28 * K), by positivity, fun s hs hγ => ?_⟩
  by_contra hcon
  push_neg at hcon
  set γ := s.im with hγdef
  set β := s.re with hβdef
  set L := Real.log (|γ| + 2) with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hβ1 : β < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h) hs
  have hcL : 1 / (28 * K) / L ≤ 1 / 140 := by
    rw [div_le_iff₀ (by linarith)]
    have : 1 / (28 * K) ≤ 1 / 140 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  have hβ23 : 2 / 3 ≤ β := by linarith
  set δ : ℝ := 1 / (2 * K) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 10 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set σ : ℝ := 1 + δ / L with hσdef
  have hδL : δ / L ≤ δ := div_le_self hδ0.le hL
  have hδL0 : 0 < δ / L := by positivity
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have hsβ : s = β + γ * I := (Complex.re_add_im s).symm
  clear_value σ δ L β γ K
  have hA := neg_re_logDeriv_riemannZeta_le_sub_inv_dist_zero_add_log hC 0 σ hσ1 hσ2 0 (Or.inl rfl)
  have hB := neg_re_logDeriv_riemannZeta_le_sub_inv_dist_zero_add_log hC γ σ hσ1 hσ2 (1 / (σ - β))
    (Or.inr ⟨β, by rw [← hsβ]; exact hs, hβ23, rfl⟩)
  have hD := neg_re_logDeriv_riemannZeta_le_sub_inv_dist_zero_add_log hC (2 * γ) σ hσ1 hσ2 0 (Or.inl rfl)
  have hineq := three_four_one_neg_re_logDeriv_riemannZeta_nonneg σ γ hσ1
  have e0 : (σ : ℂ) + ((0 : ℝ) : ℂ) * I = σ := by simp
  have e2 : (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I = σ + 2 * γ * I := by push_cast; ring
  rw [e0] at hA
  rw [e2] at hD
  have hA' : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_one, ← ofReal_div,
      ofReal_re]
  have hB' : (1 / ((σ : ℂ) + γ * I - 1)).re ≤ σ - 1 := by
    have := re_one_div_le_re_of_re_pos_of_one_le_abs_im (z := (σ : ℂ) + γ * I - 1) (by simp; linarith)
      (by simpa using hγ)
    simpa using this
  have hD' : (1 / ((σ : ℂ) + 2 * γ * I - 1)).re ≤ σ - 1 := by
    have h2 : 1 ≤ |2 * γ| := by rw [abs_mul]; norm_num; linarith
    have := re_one_div_le_re_of_re_pos_of_one_le_abs_im (z := (σ : ℂ) + 2 * γ * I - 1) (by simp; linarith)
      (by simpa using h2)
    simpa using this
  have hlog0 : Real.log (|(0 : ℝ)| + 2) ≤ L := by
    rw [abs_zero, zero_add, hLdef]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ])
  have hlog2 : Real.log (|2 * γ| + 2) ≤ 2 * L := by
    have h2L : Real.log 2 ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ])
    have : Real.log (|2 * γ| + 2) ≤ Real.log (2 * (|γ| + 2)) := by
      apply Real.log_le_log (by positivity)
      rw [abs_mul]; norm_num; linarith [abs_nonneg γ]
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    linarith
  have hy : 0 < σ - β := by linarith
  have hCL0 : C * Real.log (|(0 : ℝ)| + 2) ≤ C * L := mul_le_mul_of_nonneg_left hlog0 hC0.le
  have hCL2 : C * Real.log (|2 * γ| + 2) ≤ C * (2 * L) := mul_le_mul_of_nonneg_left hlog2 hC0.le
  have hmain : 4 / (σ - β) ≤ 3 / (σ - 1) + K * L := by
    have h4 : 4 / (σ - β) = 4 * (1 / (σ - β)) := by ring
    have h3 : 3 / (σ - 1) = 3 * (1 / (σ - 1)) := by ring
    have hσL : σ - 1 ≤ L := by linarith
    rw [h4, h3, hK]
    have hLeq : C * Real.log (|γ| + 2) = C * L := by rw [hLdef]
    rw [hLeq] at hB
    rw [hA'] at hA
    have t1 : 0 ≤ 3 * (1 / (σ - 1) - 0 + C * Real.log (|(0:ℝ)| + 2)) + 4 * ((1 / ((σ : ℂ) + γ * I - 1)).re - 1 / (σ - β) + C * L) + ((1 / ((σ : ℂ) + 2 * γ * I - 1)).re - 0 + C * Real.log (|2 * γ| + 2)) := by linarith
    have t2 : 4 * (1 / (σ - β)) ≤ 3 * (1 / (σ - 1)) + 3 * (C * L) + 4 * (σ - 1) + 4 * (C * L) + (σ - 1) + 2 * (C * L) := by
      generalize (1 / ((σ : ℂ) + γ * I - 1)).re = B1 at t1 hB' ⊢
      generalize (1 / ((σ : ℂ) + 2 * γ * I - 1)).re = D1 at t1 hD' ⊢
      generalize Real.log (|(0:ℝ)| + 2) = l0 at t1 hCL0 ⊢
      generalize Real.log (|2 * γ| + 2) = l2 at t1 hCL2 ⊢
      generalize 1 / (σ - β) = r at t1 ⊢
      generalize 1 / (σ - 1) = a at t1 ⊢
      linarith
    have h5 : σ - 1 ≤ L := hσL
    have t3 : 4 * (1 / (σ - β)) ≤ 3 * (1 / (σ - 1)) + 9 * (C * L) + 5 * L := by
      have h6 : 4 * (σ - 1) + (σ - 1) ≤ 5 * L := by linarith
      linarith [t2, h6]
    calc 4 * (1 / (σ - β)) ≤ 3 * (1 / (σ - 1)) + 9 * (C * L) + 5 * L := t3
      _ = 3 * (1 / (σ - 1)) + (9 * C + 5) * L := by ring
  have hσ1' : σ - 1 = δ / L := by rw [hσdef]; ring
  have h3eq : 3 / (σ - 1) = 6 * K * L := by
    rw [hσ1', hδ]; field_simp; ring
  rw [h3eq] at hmain
  have hmain' : 4 ≤ 7 * K * L * (σ - β) := by
    rw [div_le_iff₀ hy] at hmain
    nlinarith
  have hyL : L * (σ - β) ≤ δ + 1 / (28 * K) := by
    have : σ - β ≤ δ / L + 1 / (28 * K) / L := by linarith
    calc L * (σ - β) ≤ L * (δ / L + 1 / (28 * K) / L) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = δ + 1 / (28 * K) := by field_simp
  have hfin : 7 * K * (δ + 1 / (28 * K)) = 15 / 4 := by
    rw [hδ]; field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hyL (by linarith : (0 : ℝ) ≤ 7 * K)]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory in
open Filter Topology in
private lemma exists_riemannZeta_ne_zero_near_one_of_abs_im_le_one :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℂ, s ≠ 1 → |s.im| ≤ 1 → 1 - η < s.re → riemannZeta s ≠ 0 := by
  let g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  have hg : Continuous g := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    rcases eq_or_ne s 1 with rfl | hs
    · exact continuousAt_update_same.2 riemannZeta_residue_one
    · exact (continuousAt_update_of_ne hs).2
        ((continuousAt_id.sub continuousAt_const).mul (differentiableAt_riemannZeta hs).continuousAt)
  let K : Set ℂ := (fun y : ℝ => (1 : ℂ) + y * I) '' Set.Icc (-1) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen {s | g s ≠ 0} := isOpen_ne_fun hg continuous_const
  have hKU : K ⊆ {s | g s ≠ 0} := by
    rintro _ ⟨y, -, rfl⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp [g]
    · have h1 : (1 : ℂ) + y * I ≠ 1 := by
        intro h
        apply hy
        have := congrArg Complex.im h
        simpa using this
      simp only [Set.mem_setOf_eq, g, Function.update_of_ne h1]
      refine mul_ne_zero (sub_ne_zero.2 h1) (riemannZeta_ne_zero_of_one_le_re (by simp))
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, fun s hs him hre => ?_⟩
  rcases le_or_gt 1 s.re with h | h
  · exact riemannZeta_ne_zero_of_one_le_re h
  have hp : (1 : ℂ) + s.im * I ∈ K := ⟨s.im, ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩, rfl⟩
  have hdist : dist s (1 + s.im * I) < δ := by
    rw [Complex.dist_eq]
    have : s - (1 + s.im * I) = ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hmem : s ∈ Metric.thickening δ K := Metric.mem_thickening_iff.2 ⟨_, hp, hdist⟩
  have hgs : g s ≠ 0 := hsub hmem
  simp only [g, Function.update_of_ne hs] at hgs
  exact right_ne_zero_of_mul hgs
end GlobalTheory.ZeroFreePrincipal
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZeroFreePrincipal
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
namespace GlobalTheory.ZeroFreePrincipal
namespace _root_.GlobalTheory.ZeroFreePrincipal
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
    s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
    s.re < 1 - c / Real.log (q * (|s.im| + 2)) := by
  obtain ⟨c1, hc1, h1⟩ := exists_re_lt_one_sub_div_log_of_riemannZeta_eq_zero
  obtain ⟨η, hη, h2⟩ := exists_riemannZeta_ne_zero_near_one_of_abs_im_le_one
  refine ⟨min (min c1 (η / 2)) (1 / 2), by positivity, fun q _ s hs hL => ?_⟩
  set c := min (min c1 (η / 2)) (1 / 2) with hc
  have hc0 : 0 < c := by positivity
  have hcc1 : c ≤ c1 := (min_le_left _ _).trans (min_le_left _ _)
  have hcη : c ≤ η / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hch : c ≤ 1 / 2 := min_le_right _ _
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  have habs := abs_nonneg s.im
  have hln2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog2 : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hL2 : Real.log (|s.im| + 2) ≤ Real.log (q * (|s.im| + 2)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  set L := Real.log (q * (|s.im| + 2)) with hLdef
  have hLpos : 1 / 2 < L := by linarith
  have hcL : c / L < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hcLη : c / L < η := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have he : LFunction (1 : DirichletCharacter ℂ q) s =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
    LFunctionTrivChar_eq_mul_riemannZeta hs
  rw [he] at hL
  rcases mul_eq_zero.1 hL with hp | hz
  · obtain ⟨p, hpq, hp0⟩ := Finset.prod_eq_zero_iff.1 hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    have h1p : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 hp0).symm
    have hnorm := congrArg norm h1p
    rw [norm_natCast_cpow_of_pos hpp.pos, norm_one, neg_re,
      Real.rpow_def_of_pos (by exact_mod_cast hpp.pos), Real.exp_eq_one_iff] at hnorm
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hre : s.re = 0 := by
      rcases mul_eq_zero.1 hnorm with h | h
      · linarith
      · linarith
    rw [hre]; linarith
  · by_cases hγ : 1 ≤ |s.im|
    · have h := h1 s hz hγ
      have hlogpos : 0 < Real.log (|s.im| + 2) := by linarith
      have : c / L ≤ c1 / Real.log (|s.im| + 2) :=
        div_le_div₀ hc1.le hcc1 hlogpos hL2
      linarith
    · have hre : s.re ≤ 1 - η := by
        by_contra h
        exact h2 s hs (by linarith) (by linarith) hz
      linarith
end _root_.GlobalTheory.ZeroFreePrincipal
end GlobalTheory.ZeroFreePrincipal
