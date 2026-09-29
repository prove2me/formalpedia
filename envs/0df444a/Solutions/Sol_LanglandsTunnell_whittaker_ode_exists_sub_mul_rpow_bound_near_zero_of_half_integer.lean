-- Prove2me | solution 1 for LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/954c9185-3e76-5852-acda-3a18b6771823

import Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer

set_option autoImplicit false

open Real Complex Filter Topology MeasureTheory Set intervalIntegral

noncomputable section

namespace FrobChi

def P (r : ℝ) (y : ℝ) : ℂ := ((y ^ r : ℝ) : ℂ)

theorem P_mul {r s : ℝ} {y : ℝ} (hy : 0 < y) : P r y * P s y = P (r + s) y := by
  unfold P; rw [← ofReal_mul, ← Real.rpow_add hy]

theorem P_zero (y : ℝ) : P 0 y = 1 := by unfold P; rw [Real.rpow_zero]; simp

theorem P_one (y : ℝ) : P 1 y = (y : ℂ) := by unfold P; rw [Real.rpow_one]

theorem norm_P {r : ℝ} {y : ℝ} (hy : 0 < y) : ‖P r y‖ = y ^ r := by
  unfold P; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy r)]

theorem P_ne_zero {r : ℝ} {y : ℝ} (hy : 0 < y) : P r y ≠ 0 := by
  unfold P; exact ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy r).ne'

theorem P_eq_cpow {r : ℝ} {y : ℝ} (hy : 0 < y) (c : ℂ) (hc : c = (r : ℂ)) : (y : ℂ) ^ c = P r y := by
  unfold P; rw [hc, Complex.ofReal_cpow hy.le]

theorem hasDerivAt_P (r : ℝ) {y : ℝ} (hy : 0 < y) : HasDerivAt (P r) ((r : ℂ) * P (r - 1) y) y := by
  unfold P
  have h := (Real.hasDerivAt_rpow_const (x := y) (p := r) (Or.inl hy.ne')).ofReal_comp
  simpa using h

theorem continuousOn_P (r : ℝ) : ContinuousOn (P r) (Set.Ioi 0) := by
  intro y hy
  exact (hasDerivAt_P r hy).continuousAt.continuousWithinAt

theorem bound_of_deriv_large {φ φ' : ℝ → ℂ} {M r : ℝ} (hr : 1 < r) (hM : 0 ≤ M)
    (hφ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.Ioc 0 1))
    (hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖φ' t‖ ≤ M * t ^ (-r)) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖φ y‖ ≤ (‖φ 1‖ + M / (r - 1)) * y ^ (1 - r) := by
  intro y hy
  obtain ⟨hy0, hy1⟩ := hy
  have hsub : Set.uIcc y 1 ⊆ Set.Ioc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hy1]; intro t ht; exact ⟨lt_of_lt_of_le hy0 ht.1, ht.2⟩
  have hFTC : ∫ t in y..1, φ' t = φ 1 - φ y :=
    integral_eq_sub_of_hasDerivAt (fun t ht => hφ t (hsub ht))
      ((hφ'.mono (by rw [← Set.uIcc_of_le hy1]; exact hsub)).intervalIntegrable_of_Icc hy1)
  have hint : ‖∫ t in y..1, φ' t‖ ≤ ∫ t in y..1, M * t ^ (-r) := by
    refine norm_integral_le_of_norm_le hy1 ?_ ?_
    · exact Filter.Eventually.of_forall fun t ht => hb t ⟨hy0.trans ht.1, ht.2⟩
    · exact ((intervalIntegrable_rpow (Or.inr (by
        rw [Set.uIcc_of_le hy1]; exact fun h => (lt_irrefl (0 : ℝ)) (lt_of_lt_of_le hy0 h.1)))).const_mul M)
  have hval : ∫ t in y..1, M * t ^ (-r) = M * ((1 - y ^ (1 - r)) / (1 - r)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hy1]; exact fun h => (lt_irrefl (0 : ℝ)) (lt_of_lt_of_le hy0 h.1)⟩)]
    congr 1
    rw [Real.one_rpow, show -r + 1 = 1 - r by ring]
  have hypow : 1 ≤ y ^ (1 - r) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by linarith)
  have hr1 : 0 < r - 1 := by linarith
  calc ‖φ y‖ = ‖φ 1 - (φ 1 - φ y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖φ 1‖ + ‖φ 1 - φ y‖ := norm_sub_le _ _
    _ = ‖φ 1‖ + ‖∫ t in y..1, φ' t‖ := by rw [hFTC]
    _ ≤ ‖φ 1‖ + M * ((1 - y ^ (1 - r)) / (1 - r)) := by rw [← hval]; gcongr
    _ = ‖φ 1‖ + M / (r - 1) * (y ^ (1 - r) - 1) := by
        have : (1 - y ^ (1 - r)) / (1 - r) = (y ^ (1 - r) - 1) / (r - 1) := by
          rw [← neg_sub (y ^ (1 - r)) 1, ← neg_sub r 1, neg_div_neg_eq]
        rw [this]; ring
    _ ≤ ‖φ 1‖ * y ^ (1 - r) + M / (r - 1) * y ^ (1 - r) := by
        have h1 : ‖φ 1‖ ≤ ‖φ 1‖ * y ^ (1 - r) := le_mul_of_one_le_right (norm_nonneg _) hypow
        have h2 : M / (r - 1) * (y ^ (1 - r) - 1) ≤ M / (r - 1) * y ^ (1 - r) := by
          have : 0 ≤ M / (r - 1) := div_nonneg hM hr1.le
          nlinarith
        linarith
    _ = (‖φ 1‖ + M / (r - 1)) * y ^ (1 - r) := by ring

theorem tendsto_of_rate {ψ : ℝ → ℂ} {L : ℂ} {K e : ℝ} (he : 0 < e) (hK : 0 ≤ K)
    (h : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖ψ y - L‖ ≤ K * y ^ e) : Tendsto ψ (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ (K + 1) * δ ^ e < ε := by
    refine ⟨(ε / (K + 1)) ^ (1 / e) / 2, by positivity, ?_⟩
    have hpos : 0 < ε / (K + 1) := by positivity
    have h1 : ((ε / (K + 1)) ^ (1 / e) / 2) ^ e < ((ε / (K + 1)) ^ (1 / e)) ^ e := by
      apply Real.rpow_lt_rpow (by positivity) (by linarith [Real.rpow_pos_of_pos hpos (1 / e)]) he
    rw [← Real.rpow_mul hpos.le, one_div_mul_cancel he.ne', Real.rpow_one] at h1
    calc (K + 1) * ((ε / (K + 1)) ^ (1 / e) / 2) ^ e
        < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left h1 (by positivity)
      _ = ε := by field_simp
  refine ⟨min δ 1, by positivity, fun y hy hdist => ?_⟩
  have hy0 : 0 < y := hy
  rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_pos hy0] at hdist
  have hy1 : y ≤ 1 := (lt_of_lt_of_le hdist (min_le_right _ _)).le
  have hyδ : y < δ := lt_of_lt_of_le hdist (min_le_left _ _)
  rw [dist_eq_norm]
  calc ‖ψ y - L‖ ≤ K * y ^ e := h y ⟨hy0, hy1⟩
    _ ≤ (K + 1) * y ^ e := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hy0.le _)
    _ ≤ (K + 1) * δ ^ e := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le hyδ.le he.le) (by positivity)
    _ < ε := hδε

theorem limit_of_deriv_small {φ φ' : ℝ → ℂ} {M r : ℝ} (hr : r < 1) (hM : 0 ≤ M)
    (hφ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.Ioc 0 1))
    (hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖φ' t‖ ≤ M * t ^ (-r)) :
    ∃ φ₀ : ℂ, Tendsto φ (𝓝[>] 0) (𝓝 φ₀) ∧
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, φ y - φ₀ = ∫ t in (0 : ℝ)..y, φ' t) ∧
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖φ y - φ₀‖ ≤ M / (1 - r) * y ^ (1 - r)) ∧
      IntegrableOn φ' (Set.Ioc 0 1) := by

  have hmeas : AEStronglyMeasurable φ' (volume.restrict (Set.Ioc 0 1)) :=
    hφ'.aestronglyMeasurable measurableSet_Ioc
  have hdom : IntegrableOn (fun t : ℝ => M * t ^ (-r)) (Set.Ioc 0 1) := by
    have := (intervalIntegrable_rpow' (a := 0) (b := 1) (show -1 < -r by linarith)).const_mul M
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
  have hint : IntegrableOn φ' (Set.Ioc 0 1) :=
    Integrable.mono' hdom hmeas ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hb))
  have hii : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable φ' volume a b := by
    intro a b ha hab hb1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint.mono_set (Set.Ioc_subset_Ioc ha hb1)
  set φ₀ : ℂ := φ 1 - ∫ t in (0 : ℝ)..1, φ' t with hφ₀

  have hprim : ∀ y ∈ Set.Ioc (0 : ℝ) 1, φ y - φ₀ = ∫ t in (0 : ℝ)..y, φ' t := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hsub : Set.uIcc y 1 ⊆ Set.Ioc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le hy1]; intro t ht; exact ⟨lt_of_lt_of_le hy0 ht.1, ht.2⟩
    have hFTC : ∫ t in y..1, φ' t = φ 1 - φ y :=
      integral_eq_sub_of_hasDerivAt (fun t ht => hφ t (hsub ht)) (hii y 1 hy0.le hy1 le_rfl)
    have hadd : (∫ t in (0 : ℝ)..y, φ' t) + ∫ t in y..1, φ' t = ∫ t in (0 : ℝ)..1, φ' t :=
      integral_add_adjacent_intervals (hii 0 y le_rfl hy0.le hy1) (hii y 1 hy0.le hy1 le_rfl)
    rw [hφ₀, ← hadd, hFTC]
    ring

  have hrate : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖φ y - φ₀‖ ≤ M / (1 - r) * y ^ (1 - r) := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    rw [hprim y ⟨hy0, hy1⟩]
    have hint2 : ‖∫ t in (0 : ℝ)..y, φ' t‖ ≤ ∫ t in (0 : ℝ)..y, M * t ^ (-r) := by
      refine norm_integral_le_of_norm_le hy0.le ?_ ?_
      · exact Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1, ht.2.trans hy1⟩
      · exact (intervalIntegrable_rpow' (show -1 < -r by linarith)).const_mul M
    have hval : ∫ t in (0 : ℝ)..y, M * t ^ (-r) = M / (1 - r) * y ^ (1 - r) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), show (-r + 1) = 1 - r by ring,
        Real.zero_rpow (by linarith : (1 - r) ≠ 0), sub_zero]
      ring
    rw [← hval]
    exact hint2
  refine ⟨φ₀, ?_, hprim, hrate, hint⟩
  have hr1 : 0 < 1 - r := by linarith
  exact tendsto_of_rate hr1 (div_nonneg hM hr1.le) hrate

def gF (β : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ := (y : ℂ) * deriv f y - (β : ℂ) * f y

def GF (α β : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ := P (-α) y * gF β f y

def FF (β : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ := P (-β) y * f y

theorem hasDerivAt_ofReal' (y : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
  simpa using (hasDerivAt_id y).ofReal_comp

theorem hasDerivAt_GF (α β : ℝ) (f : ℝ → ℂ) (φc : ℝ → ℂ) (hab : α + β = 1) {y : ℝ} (hy : 0 < y)
    (hdf : HasDerivAt f (deriv f y) y) (hddf : HasDerivAt (deriv f) (deriv (deriv f) y) y)
    (hode : (y : ℂ) ^ 2 * deriv (deriv f) y = -(((α : ℂ) * (β : ℂ)) * f y) - φc y * f y) :
    HasDerivAt (GF α β f) (-(P (-α - 1) y * (φc y * f y))) y := by
  have hg : HasDerivAt (gF β f) (1 * deriv f y + (y : ℂ) * deriv (deriv f) y - (β : ℂ) * deriv f y) y :=
    ((hasDerivAt_ofReal' y).mul hddf).sub (hdf.const_mul (β : ℂ))
  have hP := hasDerivAt_P (-α) hy
  have h := hP.mul hg
  refine h.congr_deriv ?_
  have hsplit : P (-α) y = P (-α - 1) y * (y : ℂ) := by
    rw [← P_one y, P_mul hy]; congr 1; ring
  have habC : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hab
  simp only [gF]
  rw [show (-α - 1 : ℝ) = -α - 1 from rfl] at *
  rw [hsplit]
  push_cast
  linear_combination (P (-α - 1) y) * hode - (P (-α - 1) y * (y : ℂ) * deriv f y) * habC

theorem hasDerivAt_FF (α β : ℝ) (f : ℝ → ℂ) {y : ℝ} (hy : 0 < y) (hdf : HasDerivAt f (deriv f y) y) :
    HasDerivAt (FF β f) (P (α - β - 1) y * GF α β f y) y := by
  have hP := hasDerivAt_P (-β) hy
  have h := hP.mul hdf
  refine h.congr_deriv ?_
  simp only [GF, gF]
  have hsplit : P (-β) y = P (-β - 1) y * (y : ℂ) := by
    rw [← P_one y, P_mul hy]; congr 1; ring
  have hprod : P (α - β - 1) y * P (-α) y = P (-β - 1) y := by
    rw [P_mul hy]; congr 1; ring
  rw [hsplit, ← mul_assoc, hprod]
  push_cast
  ring

theorem F_bound (n : ℕ) {G F F' : ℝ → ℂ} (hFd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hF'c : ContinuousOn F' (Set.Ioc 0 1))
    (hF' : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F' t‖ = t ^ ((n : ℝ) - 1) * ‖G t‖) (hF0 : Tendsto F (𝓝[>] 0) (𝓝 0))
    {M r : ℝ} (hM : 0 ≤ M) (hrn : r < n) (hGb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t‖ ≤ M * t ^ (-r)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F t‖ ≤ M / (n - r) * t ^ ((n : ℝ) - r) := by
  have hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F' t‖ ≤ M * t ^ (-(r - n + 1)) := by
    intro t ht
    rw [hF' t ht]
    calc t ^ ((n : ℝ) - 1) * ‖G t‖ ≤ t ^ ((n : ℝ) - 1) * (M * t ^ (-r)) :=
          mul_le_mul_of_nonneg_left (hGb t ht) (Real.rpow_nonneg ht.1.le _)
      _ = M * t ^ (-(r - n + 1)) := by
          rw [mul_left_comm, ← Real.rpow_add ht.1]; congr 2; ring
  obtain ⟨c, hc, -, hrate, -⟩ := limit_of_deriv_small (show r - n + 1 < 1 by linarith) hM hFd hF'c hb
  have hc0 : c = 0 := tendsto_nhds_unique hc hF0
  intro t ht
  have := hrate t ht
  rw [hc0, sub_zero] at this
  convert this using 2
  · ring
  · congr 1; ring

theorem round (n : ℕ) {G G' F F' : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hGd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt G (G' t) t) (hG'c : ContinuousOn G' (Set.Ioc 0 1))
    (hFd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t) (hF'c : ContinuousOn F' (Set.Ioc 0 1))
    (hF' : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F' t‖ = t ^ ((n : ℝ) - 1) * ‖G t‖)
    (hG'F : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G' t‖ ≤ A * t ^ (-(n : ℝ)) * ‖F t‖)
    (hF0 : Tendsto F (𝓝[>] 0) (𝓝 0))
    {M r : ℝ} (hM : 0 ≤ M) (hr : 1 < r) (hrn : r < n) (hGb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t‖ ≤ M * t ^ (-r)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t‖ ≤ K * t ^ (-(r - 1)) := by
  have hFb := F_bound n hFd hF'c hF' hF0 hM hrn hGb
  have hnr : 0 < (n : ℝ) - r := by linarith
  have hG'b : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G' t‖ ≤ (A * (M / (n - r))) * t ^ (-r) := by
    intro t ht
    calc ‖G' t‖ ≤ A * t ^ (-(n : ℝ)) * ‖F t‖ := hG'F t ht
      _ ≤ A * t ^ (-(n : ℝ)) * (M / (n - r) * t ^ ((n : ℝ) - r)) :=
          mul_le_mul_of_nonneg_left (hFb t ht) (mul_nonneg hA (Real.rpow_nonneg ht.1.le _))
      _ = (A * (M / (n - r))) * t ^ (-r) := by
          rw [show A * t ^ (-(n : ℝ)) * (M / (n - r) * t ^ ((n : ℝ) - r)) =
            (A * (M / (n - r))) * (t ^ (-(n : ℝ)) * t ^ ((n : ℝ) - r)) by ring, ← Real.rpow_add ht.1]
          congr 2; ring
  have hAM : 0 ≤ A * (M / (n - r)) := mul_nonneg hA (div_nonneg hM hnr.le)
  have hres := bound_of_deriv_large hr hAM hGd hG'c hG'b
  refine ⟨‖G 1‖ + A * (M / (n - r)) / (r - 1), by
    have : 0 ≤ A * (M / (n - r)) / (r - 1) := div_nonneg hAM (by linarith); positivity, fun t ht => ?_⟩
  have := hres t ht
  rwa [show (1 - r : ℝ) = -(r - 1) by ring] at this

theorem final_round (n : ℕ) (hn : 1 ≤ n) {G G' F F' : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hGd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt G (G' t) t) (hG'c : ContinuousOn G' (Set.Ioc 0 1))
    (hFd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t) (hF'c : ContinuousOn F' (Set.Ioc 0 1))
    (hF' : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F' t‖ = t ^ ((n : ℝ) - 1) * ‖G t‖)
    (hG'F : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G' t‖ ≤ A * t ^ (-(n : ℝ)) * ‖F t‖)
    (hF0 : Tendsto F (𝓝[>] 0) (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hGb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t‖ ≤ M * t ^ (-(1 / 2 : ℝ))) :
    ∃ (G₀ : ℂ) (K : ℝ), 0 ≤ K ∧ Tendsto G (𝓝[>] 0) (𝓝 G₀) ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t - G₀‖ ≤ K * t ^ (1 / 2 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrn : (1 / 2 : ℝ) < n := by linarith
  have hFb := F_bound n hFd hF'c hF' hF0 hM hrn hGb
  have hnr : 0 < (n : ℝ) - 1 / 2 := by linarith
  have hG'b : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G' t‖ ≤ (A * (M / (n - 1 / 2))) * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    calc ‖G' t‖ ≤ A * t ^ (-(n : ℝ)) * ‖F t‖ := hG'F t ht
      _ ≤ A * t ^ (-(n : ℝ)) * (M / (n - 1 / 2) * t ^ ((n : ℝ) - 1 / 2)) :=
          mul_le_mul_of_nonneg_left (hFb t ht) (mul_nonneg hA (Real.rpow_nonneg ht.1.le _))
      _ = (A * (M / (n - 1 / 2))) * t ^ (-(1 / 2 : ℝ)) := by
          rw [show A * t ^ (-(n : ℝ)) * (M / (n - 1 / 2) * t ^ ((n : ℝ) - 1 / 2)) =
            (A * (M / (n - 1 / 2))) * (t ^ (-(n : ℝ)) * t ^ ((n : ℝ) - 1 / 2)) by ring, ← Real.rpow_add ht.1]
          congr 2; ring
  have hAM : 0 ≤ A * (M / (n - 1 / 2)) := mul_nonneg hA (div_nonneg hM hnr.le)
  obtain ⟨G₀, hlim, -, hrate, -⟩ := limit_of_deriv_small (show (1 / 2 : ℝ) < 1 by norm_num) hAM hGd hG'c hG'b
  refine ⟨G₀, A * (M / (n - 1 / 2)) / (1 - 1 / 2), div_nonneg hAM (by norm_num), hlim, fun t ht => ?_⟩
  have := hrate t ht
  rwa [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at this ⊢

theorem main (n : ℕ) (hn : 1 ≤ n) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - c * (y : ℂ) ^ (1 / 2 - ν)‖ ≤ C * y ^ (1 / 2 - (n : ℝ) / 2 + δ)) ∧
      (c = 0 →
        (∃ L : ℂ, Tendsto (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 + ν)) * f y) (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto (fun y : ℝ => (y : ℂ) ^ (1 / 2 - ν) * (deriv f y - (1 / 2 + ν) / (y : ℂ) * f y)) (𝓝[>] 0) (𝓝 0) ∧
        ∃ C' : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C' * y ^ (1 / 2 + (n : ℝ) / 2)) := by

  set α : ℝ := 1 / 2 + n / 2 with hα
  set β : ℝ := 1 / 2 - n / 2 with hβ
  have hab : α + β = 1 := by rw [hα, hβ]; ring
  have hamb : α - β = n := by rw [hα, hβ]; ring
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hνC : ν = ((n : ℝ) : ℂ) / 2 := by rw [hν]; push_cast; rfl

  set φc : ℝ → ℂ := fun y => 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 with hφc
  have hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y = -(((α : ℂ) * (β : ℂ)) * f y) - φc y * f y := by
    intro y hy
    have h := hfeq y hy
    have hprod : (α : ℂ) * (β : ℂ) = 1 / 4 - ν ^ 2 := by
      rw [hνC, hα, hβ]; push_cast; ring
    rw [hprod]
    simp only [hφc]
    linear_combination h

  have hdf : ∀ y : ℝ, 0 < y → HasDerivAt f (deriv f y) y := fun y hy =>
    (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hddf : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y hy =>
    (hf'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt

  set G : ℝ → ℂ := GF α β f with hGdef
  set G' : ℝ → ℂ := fun y => -(P (-α - 1) y * (φc y * f y)) with hG'def
  set F : ℝ → ℂ := FF β f with hFdef
  set F' : ℝ → ℂ := fun y => P (α - β - 1) y * G y with hF'def
  have hGd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt G (G' t) t := fun t ht =>
    hasDerivAt_GF α β f φc hab ht.1 (hdf t ht.1) (hddf t ht.1) (hode t ht.1)
  have hFd : ∀ t ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t := fun t ht =>
    hasDerivAt_FF α β f ht.1 (hdf t ht.1)
  have hfc : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  have hf'c : ContinuousOn (deriv f) (Set.Ioi 0) := hf'.continuousOn
  have hφcont : Continuous φc := by
    simp only [hφc]; fun_prop
  have hG'c : ContinuousOn G' (Set.Ioc 0 1) := by
    have : ContinuousOn G' (Set.Ioi 0) :=
      ((continuousOn_P (-α - 1)).mul (hφcont.continuousOn.mul hfc)).neg
    exact this.mono Set.Ioc_subset_Ioi_self
  have hGc : ContinuousOn G (Set.Ioi 0) := by
    simp only [hGdef, GF, gF]
    exact (continuousOn_P (-α)).mul ((Complex.continuous_ofReal.continuousOn.mul hf'c).sub
      (continuousOn_const.mul hfc))
  have hF'c : ContinuousOn F' (Set.Ioc 0 1) :=
    ((continuousOn_P (α - β - 1)).mul hGc).mono Set.Ioc_subset_Ioi_self

  have hfF : ∀ y : ℝ, 0 < y → f y = P β y * F y := by
    intro y hy
    simp only [hFdef, FF]
    rw [← mul_assoc, P_mul hy, show β + -β = 0 by ring, P_zero, one_mul]
  have hF'norm : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F' t‖ = t ^ ((n : ℝ) - 1) * ‖G t‖ := by
    intro t ht
    simp only [hF'def]
    rw [norm_mul, norm_P ht.1, hamb]
  set A : ℝ := 2 * π * |κ| + 4 * π ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hφb : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖φc y‖ ≤ A * y := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    simp only [hφc]
    have h1 : ‖2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ)‖ = 2 * π * |κ| * y := by
      rw [show (2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ)) = ((2 * π * κ * y : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hy0, abs_of_pos Real.pi_pos,
        abs_of_pos two_pos]
    have h2 : ‖4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2‖ = 4 * π ^ 2 * y ^ 2 := by
      rw [show (4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) = ((4 * π ^ 2 * y ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2‖
        ≤ ‖2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ)‖ + ‖4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = 2 * π * |κ| * y + 4 * π ^ 2 * y ^ 2 := by rw [h1, h2]
      _ ≤ 2 * π * |κ| * y + 4 * π ^ 2 * y := by
          have : y ^ 2 ≤ y := by nlinarith
          have : 0 ≤ 4 * π ^ 2 := by positivity
          nlinarith
      _ = A * y := by rw [hA]; ring
  have hG'F : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G' t‖ ≤ A * t ^ (-(n : ℝ)) * ‖F t‖ := by
    intro t ht
    simp only [hG'def]
    rw [norm_neg, norm_mul, norm_mul, norm_P ht.1, hfF t ht.1, norm_mul, norm_P ht.1]
    have hpow : t ^ (-α - 1) * t * t ^ β = t ^ (-(n : ℝ)) := by
      rw [show t ^ (-α - 1) * t = t ^ (-α - 1) * t ^ (1 : ℝ) by rw [Real.rpow_one], ← Real.rpow_add ht.1,
        ← Real.rpow_add ht.1]
      congr 1; linarith
    calc t ^ (-α - 1) * (‖φc t‖ * (t ^ β * ‖F t‖)) ≤ t ^ (-α - 1) * ((A * t) * (t ^ β * ‖F t‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hφb t ht)
            (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))) (Real.rpow_nonneg ht.1.le _)
      _ = A * (t ^ (-α - 1) * t * t ^ β) * ‖F t‖ := by ring
      _ = A * t ^ (-(n : ℝ)) * ‖F t‖ := by rw [hpow]

  have hν0 : ν ≠ 0 := by
    rw [hνC]; exact div_ne_zero (by exact_mod_cast (show (n : ℝ) ≠ 0 by positivity)) two_ne_zero
  obtain ⟨C₀, hC₀⟩ := (LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode ν κ f hf hf' hfeq).1 hν0
  have hνre : |ν.re| = (n : ℝ) / 2 := by
    rw [hνC]; simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / 2)]
  have hfb : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖f y‖ ≤ max C₀ 0 * y ^ β := by
    intro y hy
    have := hC₀ y hy.1 hy.2
    rw [hνre] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.1.le _))

  have hG'b0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G' t‖ ≤ (A * max C₀ 0) * t ^ (-((n : ℝ) + 1 / 2)) := by
    intro t ht
    have hFt : ‖F t‖ ≤ max C₀ 0 := by
      have h1 : ‖F t‖ = t ^ (-β) * ‖f t‖ := by simp only [hFdef, FF]; rw [norm_mul, norm_P ht.1]
      rw [h1]
      calc t ^ (-β) * ‖f t‖ ≤ t ^ (-β) * (max C₀ 0 * t ^ β) :=
            mul_le_mul_of_nonneg_left (hfb t ht) (Real.rpow_nonneg ht.1.le _)
        _ = max C₀ 0 := by
            rw [mul_left_comm, ← Real.rpow_add ht.1, show -β + β = 0 by ring, Real.rpow_zero, mul_one]
    calc ‖G' t‖ ≤ A * t ^ (-(n : ℝ)) * ‖F t‖ := hG'F t ht
      _ ≤ A * t ^ (-(n : ℝ)) * max C₀ 0 := mul_le_mul_of_nonneg_left hFt (mul_nonneg hA0 (Real.rpow_nonneg ht.1.le _))
      _ ≤ A * t ^ (-((n : ℝ) + 1 / 2)) * max C₀ 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)) hA0) (le_max_right _ _)
      _ = (A * max C₀ 0) * t ^ (-((n : ℝ) + 1 / 2)) := by ring
  have hM0 : 0 ≤ A * max C₀ 0 := mul_nonneg hA0 (le_max_right _ _)
  have hGb0 := bound_of_deriv_large (show (1 : ℝ) < n + 1 / 2 by linarith) hM0 hGd hG'c hG'b0
  set K₀ : ℝ := ‖G 1‖ + A * max C₀ 0 / ((n : ℝ) + 1 / 2 - 1) with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have : 0 ≤ A * max C₀ 0 / ((n : ℝ) + 1 / 2 - 1) := div_nonneg hM0 (by linarith)
    positivity

  have hF'b : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F' t‖ ≤ K₀ * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    rw [hF'norm t ht]
    calc t ^ ((n : ℝ) - 1) * ‖G t‖ ≤ t ^ ((n : ℝ) - 1) * (K₀ * t ^ (1 - ((n : ℝ) + 1 / 2))) :=
          mul_le_mul_of_nonneg_left (hGb0 t ht) (Real.rpow_nonneg ht.1.le _)
      _ = K₀ * t ^ (-(1 / 2 : ℝ)) := by
          rw [mul_left_comm, ← Real.rpow_add ht.1]; congr 2; ring
  obtain ⟨c, hFlim, hFprim, hFrate, hF'int⟩ :=
    limit_of_deriv_small (show (1 / 2 : ℝ) < 1 by norm_num) hK₀0 hFd hF'c hF'b
  refine ⟨c, 1 / 2, by norm_num, ⟨K₀ / (1 - 1 / 2), fun y hy0 hy1 => ?_⟩, fun hc0 => ?_⟩
  ·
    have hcpow : (y : ℂ) ^ (1 / 2 - ν) = P β y := P_eq_cpow hy0 _ (by rw [hνC, hβ]; push_cast; ring)
    rw [hcpow, hfF y hy0, show P β y * F y - c * P β y = P β y * (F y - c) by ring, norm_mul, norm_P hy0]
    calc y ^ β * ‖F y - c‖ ≤ y ^ β * (K₀ / (1 - 1 / 2) * y ^ (1 - 1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hFrate y ⟨hy0, hy1⟩) (Real.rpow_nonneg hy0.le _)
      _ = K₀ / (1 - 1 / 2) * y ^ (1 / 2 - (n : ℝ) / 2 + 1 / 2) := by
          rw [mul_left_comm, ← Real.rpow_add hy0]; congr 2; rw [hβ]; ring
  ·
    rw [hc0] at hFlim

    have hrounds : ∀ k : ℕ, k ≤ n - 1 → ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t‖ ≤ M * t ^ (-((n : ℝ) - 1 / 2 - k)) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨K₀, hK₀0, fun t ht => ?_⟩
        have := hGb0 t ht
        convert this using 2
        push_cast; ring
      | succ k ih =>
        intro hk
        obtain ⟨M, hM, hGb⟩ := ih (Nat.le_of_succ_le hk)
        have hk' : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) - 1 := by
          have : k + 1 ≤ n - 1 := hk
          have h2 : ((k + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
          rw [Nat.cast_sub hn] at h2; push_cast at h2; linarith
        obtain ⟨K, hK, hGb'⟩ := round n hA0 hGd hG'c hFd hF'c hF'norm hG'F hFlim hM
          (show (1 : ℝ) < (n : ℝ) - 1 / 2 - k by linarith) (show (n : ℝ) - 1 / 2 - k < n by
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) hGb
        refine ⟨K, hK, fun t ht => ?_⟩
        have := hGb' t ht
        convert this using 2
        push_cast; ring
    obtain ⟨M, hM, hGbM⟩ := hrounds (n - 1) le_rfl
    have hGb12 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖G t‖ ≤ M * t ^ (-(1 / 2 : ℝ)) := by
      intro t ht
      have := hGbM t ht
      rw [Nat.cast_sub hn] at this
      convert this using 2
      push_cast; ring
    obtain ⟨G₀, K, hK, hGlim, hGrate⟩ := final_round n hn hA0 hGd hG'c hFd hF'c hF'norm hG'F hFlim hM hGb12

    have hnpos : (0 : ℝ) < n := by linarith
    have hPn1 : ∀ t : ℝ, P (α - β - 1) t = P ((n : ℝ) - 1) t := by intro t; rw [hamb]
    have hFasym : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y - G₀ * (y : ℂ) ^ n / n‖ ≤ K / (n + 1 / 2) * y ^ ((n : ℝ) + 1 / 2) := by
      intro y hy
      obtain ⟨hy0, hy1⟩ := hy
      have h1 : F y = ∫ t in (0 : ℝ)..y, F' t := by
        have := hFprim y ⟨hy0, hy1⟩; rw [hc0, sub_zero] at this; exact this
      have hii : IntervalIntegrable F' volume 0 y := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy0.le]
        exact hF'int.mono_set (Set.Ioc_subset_Ioc le_rfl hy1)
      have hPcont : Continuous fun t : ℝ => P ((n : ℝ) - 1) t * G₀ := by
        unfold P
        exact (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by linarith))).mul continuous_const
      have hPint : IntervalIntegrable (fun t : ℝ => P ((n : ℝ) - 1) t * G₀) volume 0 y :=
        hPcont.intervalIntegrable 0 y
      have h2 : ∫ t in (0 : ℝ)..y, P ((n : ℝ) - 1) t * G₀ = G₀ * (y : ℂ) ^ n / n := by
        rw [intervalIntegral.integral_mul_const]
        unfold P
        rw [intervalIntegral.integral_ofReal, integral_rpow (Or.inl (by linarith)),
          show ((n : ℝ) - 1 + 1) = n by ring, Real.zero_rpow hnpos.ne', sub_zero, Real.rpow_natCast]
        push_cast
        ring
      have h3 : F y - G₀ * (y : ℂ) ^ n / n = ∫ t in (0 : ℝ)..y, P ((n : ℝ) - 1) t * (G t - G₀) := by
        rw [h1, ← h2, ← intervalIntegral.integral_sub hii hPint]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [hF'def, hPn1]
        ring
      rw [h3]
      have hbound : ‖∫ t in (0 : ℝ)..y, P ((n : ℝ) - 1) t * (G t - G₀)‖ ≤ ∫ t in (0 : ℝ)..y, K * t ^ ((n : ℝ) - 1 / 2) := by
        refine norm_integral_le_of_norm_le hy0.le ?_ ?_
        · refine Filter.Eventually.of_forall fun t ht => ?_
          have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hy1⟩
          rw [norm_mul, norm_P ht.1]
          calc t ^ ((n : ℝ) - 1) * ‖G t - G₀‖ ≤ t ^ ((n : ℝ) - 1) * (K * t ^ (1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (hGrate t ht') (Real.rpow_nonneg ht.1.le _)
            _ = K * t ^ ((n : ℝ) - 1 / 2) := by
                rw [mul_left_comm, ← Real.rpow_add ht.1]; congr 2; ring
        · exact (intervalIntegrable_rpow' (show (-1 : ℝ) < n - 1 / 2 by linarith)).const_mul K
      have hval : ∫ t in (0 : ℝ)..y, K * t ^ ((n : ℝ) - 1 / 2) = K / (n + 1 / 2) * y ^ ((n : ℝ) + 1 / 2) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
          show ((n : ℝ) - 1 / 2 + 1) = n + 1 / 2 by ring, Real.zero_rpow (by linarith), sub_zero]
        field_simp
      rw [← hval]
      exact hbound

    set ψ : ℝ → ℂ := fun y => P (-(n : ℝ)) y * F y with hψ
    have hψrate : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖ψ y - G₀ / n‖ ≤ K / (n + 1 / 2) * y ^ (1 / 2 : ℝ) := by
      intro y hy
      obtain ⟨hy0, hy1⟩ := hy
      have hyn : (y : ℂ) ^ n = P (n : ℝ) y := by
        unfold P; rw [Real.rpow_natCast]; push_cast; rfl
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show (n : ℕ) ≠ 0 by omega)
      have hkey : ψ y - G₀ / n = P (-(n : ℝ)) y * (F y - G₀ * (y : ℂ) ^ n / n) := by
        simp only [hψ]
        rw [hyn, mul_sub, show P (-(n : ℝ)) y * (G₀ * P (n : ℝ) y / n) = (P (-(n : ℝ)) y * P (n : ℝ) y) * G₀ / n by ring,
          P_mul hy0, show (-(n : ℝ) + n) = 0 by ring, P_zero]
        ring
      rw [hkey, norm_mul, norm_P hy0]
      calc y ^ (-(n : ℝ)) * ‖F y - G₀ * (y : ℂ) ^ n / n‖ ≤ y ^ (-(n : ℝ)) * (K / (n + 1 / 2) * y ^ ((n : ℝ) + 1 / 2)) :=
            mul_le_mul_of_nonneg_left (hFasym y ⟨hy0, hy1⟩) (Real.rpow_nonneg hy0.le _)
        _ = K / (n + 1 / 2) * y ^ (1 / 2 : ℝ) := by
            rw [mul_left_comm, ← Real.rpow_add hy0]; congr 2; ring
    have hKn : 0 ≤ K / (n + 1 / 2) := div_nonneg hK (by linarith)
    have hψlim : Tendsto ψ (𝓝[>] 0) (𝓝 (G₀ / n)) := tendsto_of_rate (by norm_num) hKn hψrate

    have hQ1 : ∀ y : ℝ, 0 < y → P β y = P (β - 1) y * (y : ℂ) := by
      intro y hy; rw [← P_one y, P_mul hy]; congr 1; ring
    have hQ2 : ∀ y : ℝ, P (-α) y = P (β - 1) y := by
      intro y; congr 1; linarith
    have hQ3 : ∀ y : ℝ, 0 < y → P (-(n : ℝ)) y * P (-β) y = P (β - 1) y := by
      intro y hy; rw [P_mul hy]; congr 1; linarith
    have hQ4 : ∀ y : ℝ, 0 < y → P (-α) y * P β y = P (-(n : ℝ)) y := by
      intro y hy; rw [P_mul hy]; congr 1; linarith
    refine ⟨⟨G₀ / n, ?_⟩, ?_, ?_⟩
    ·
      refine hψlim.congr' ?_
      refine eventually_nhdsWithin_of_forall fun y hy => ?_
      have hy0 : 0 < y := hy
      simp only [hψ]
      rw [P_eq_cpow (r := -α) hy0 _ (by rw [hνC, hα]; push_cast; ring), hfF y hy0, ← mul_assoc, hQ4 y hy0]
    ·
      have hlim2 : Tendsto (fun y => G y - (n : ℂ) * ψ y) (𝓝[>] 0) (𝓝 (G₀ - (n : ℂ) * (G₀ / n))) :=
        hGlim.sub (hψlim.const_mul (n : ℂ))
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show (n : ℕ) ≠ 0 by omega)
      rw [show G₀ - (n : ℂ) * (G₀ / n) = 0 by field_simp; ring] at hlim2
      refine hlim2.congr' ?_
      refine eventually_nhdsWithin_of_forall fun y hy => ?_
      have hy0 : 0 < y := hy
      have hyC : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
      have hαC : (1 / 2 + ν : ℂ) = (α : ℂ) := by rw [hνC, hα]; push_cast; ring
      simp only [hψ, hGdef, hFdef, GF, gF, FF]
      rw [P_eq_cpow (r := β) hy0 _ (by rw [hνC, hβ]; push_cast; ring), hαC, hQ1 y hy0, hQ2 y,
        ← mul_assoc (P (-(n : ℝ)) y) (P (-β) y) (f y), hQ3 y hy0]
      have hba : (β : ℂ) + (n : ℂ) = (α : ℂ) := by
        have : β + n = α := by linarith
        exact_mod_cast this
      have hdiv : P (β - 1) y * (y : ℂ) * ((α : ℂ) / (y : ℂ) * f y) = P (β - 1) y * (α : ℂ) * f y := by
        field_simp
      rw [mul_sub (P (β - 1) y * (y : ℂ)), hdiv]
      linear_combination (-(P (β - 1) y * f y)) * hba
    ·
      refine ⟨‖G₀‖ / n + K / (n + 1 / 2), fun y hy0 hy1 => ?_⟩
      rw [hfF y hy0, norm_mul, norm_P hy0]
      have hFn : ‖F y‖ ≤ (‖G₀‖ / n + K / (n + 1 / 2)) * y ^ (n : ℝ) := by
        have h1 : ‖G₀ * (y : ℂ) ^ n / n‖ = ‖G₀‖ / n * y ^ (n : ℝ) := by
          rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
            Complex.norm_natCast, Real.rpow_natCast]
          ring
        have h2 : y ^ ((n : ℝ) + 1 / 2) ≤ y ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
        calc ‖F y‖ = ‖G₀ * (y : ℂ) ^ n / n + (F y - G₀ * (y : ℂ) ^ n / n)‖ := by rw [add_sub_cancel]
          _ ≤ ‖G₀ * (y : ℂ) ^ n / n‖ + ‖F y - G₀ * (y : ℂ) ^ n / n‖ := norm_add_le _ _
          _ ≤ ‖G₀‖ / n * y ^ (n : ℝ) + K / (n + 1 / 2) * y ^ ((n : ℝ) + 1 / 2) := by
              rw [h1]; exact add_le_add le_rfl (hFasym y ⟨hy0, hy1⟩)
          _ ≤ ‖G₀‖ / n * y ^ (n : ℝ) + K / (n + 1 / 2) * y ^ (n : ℝ) := by
              have := mul_le_mul_of_nonneg_left h2 hKn; linarith
          _ = (‖G₀‖ / n + K / (n + 1 / 2)) * y ^ (n : ℝ) := by ring
      calc y ^ β * ‖F y‖ ≤ y ^ β * ((‖G₀‖ / n + K / (n + 1 / 2)) * y ^ (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hFn (Real.rpow_nonneg hy0.le _)
        _ = (‖G₀‖ / n + K / (n + 1 / 2)) * y ^ (1 / 2 + (n : ℝ) / 2) := by
            rw [mul_left_comm, ← Real.rpow_add hy0]; congr 2; rw [hβ]; ring

end FrobChi

end

theorem solution
    (n : ℕ) (hn : 1 ≤ n) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - c * (y : ℂ) ^ (1 / 2 - ν)‖ ≤ C * y ^ (1 / 2 - (n : ℝ) / 2 + δ)) ∧
      (c = 0 →
        (∃ L : ℂ, Tendsto (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 + ν)) * f y) (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto (fun y : ℝ => (y : ℂ) ^ (1 / 2 - ν) * (deriv f y - (1 / 2 + ν) / (y : ℂ) * f y)) (𝓝[>] 0) (𝓝 0) ∧
        ∃ C' : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C' * y ^ (1 / 2 + (n : ℝ) / 2)) :=
  FrobChi.main n hn ν hν κ f hf hf' hfeq

end S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
end P2MW
export P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer (solution)
