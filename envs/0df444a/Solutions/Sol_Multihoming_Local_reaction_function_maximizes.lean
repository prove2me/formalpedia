-- Prove2me | solution 1 for Multihoming.Local.reaction_function_maximizes
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:55:44.941172+00:00
-- url     : https://prove2.me/submissions/6d870839-a00b-4a85-ba01-998f373fc0a4

import Mathlib
import Definitions.Def_Multihoming_Local_Model
set_option autoImplicit false


open Multihoming.Local

lemma ml_out (t μ ei ej : ℝ) (ht : 0 < t) (h1 : -t < μ) (h2 : μ < t) :
    outM t μ ei ej =
      (μ * (2 * t + μ) * (t - μ) + (2 * t ^ 2 - μ ^ 2) * ei - t * μ * ej) /
          ((t ^ 2 - μ ^ 2) * (4 * t ^ 2 - μ ^ 2)) * t := by
  have a1 : t + μ ≠ 0 := by linarith
  have a2 : t - μ ≠ 0 := by linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a4 : 2 * t + μ ≠ 0 := by linarith
  have e1 : t * 2 - μ ≠ 0 := by linarith
  have e2 : t * 2 + μ ≠ 0 := by linarith
  have h5 : t ^ 2 - μ ^ 2 = (t - μ) * (t + μ) := by ring
  have h6 : 4 * t ^ 2 - μ ^ 2 = (2 * t - μ) * (2 * t + μ) := by ring
  unfold outM demandM priceM
  rw [h5, h6]
  field_simp
  ring

lemma ml_single (t μ ei ej : ℝ) (ht : 0 < t) (h1 : -t < μ) (h2 : μ < t) :
    singleM t μ ei ej =
      ((2 * t ^ 2 - μ ^ 2) * ((t - μ) * (μ + 2 * t) - ej * t) + ei * μ * t ^ 2) /
          (μ ^ 4 - 5 * μ ^ 2 * t ^ 2 + 4 * t ^ 4) := by
  have a1 : t + μ ≠ 0 := by linarith
  have a2 : t - μ ≠ 0 := by linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a4 : 2 * t + μ ≠ 0 := by linarith
  have e1 : t * 2 - μ ≠ 0 := by linarith
  have e2 : t * 2 + μ ≠ 0 := by linarith
  have h5 : t ^ 2 - μ ^ 2 = (t - μ) * (t + μ) := by ring
  have h6 : 4 * t ^ 2 - μ ^ 2 = (2 * t - μ) * (2 * t + μ) := by ring
  have h7 : μ ^ 4 - 5 * μ ^ 2 * t ^ 2 + 4 * t ^ 4 =
      (t - μ) * (t + μ) * ((2 * t - μ) * (2 * t + μ)) := by ring
  unfold singleM
  rw [ml_out t μ ej ei ht h1 h2, h7, h5, h6]
  field_simp
  ring

lemma ml_multi (t μ ei ej : ℝ) (ht : 0 < t) (h1 : -t < μ) (h2 : μ < t) :
    multiM t μ ei ej = ((ei + ej) * t + μ ^ 2 - 2 * t ^ 2 + μ * t) / ((2 * t - μ) * (μ + t)) := by
  have a1 : t + μ ≠ 0 := by linarith
  have a2 : t - μ ≠ 0 := by linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a4 : 2 * t + μ ≠ 0 := by linarith
  have a5 : μ + t ≠ 0 := by linarith
  have e1 : t * 2 - μ ≠ 0 := by linarith
  have e2 : t * 2 + μ ≠ 0 := by linarith
  have h7 : μ ^ 4 - 5 * μ ^ 2 * t ^ 2 + 4 * t ^ 4 =
      (t - μ) * (t + μ) * ((2 * t - μ) * (2 * t + μ)) := by ring
  unfold multiM
  rw [ml_single t μ ei ej ht h1 h2, ml_single t μ ej ei ht h1 h2, h7]
  field_simp
  ring

lemma ml_react (t μ ei ej pj : ℝ) (ht : 0 < t) (h1 : -t < μ) (h2 : μ < t) :
    ∀ p : ℝ, p * demandM t μ ei ej p pj ≤
      reactM t μ ei ej pj * demandM t μ ei ej (reactM t μ ei ej pj) pj := by
  intro p
  have a1 : t + μ ≠ 0 := by linarith
  have a2 : t - μ ≠ 0 := by linarith
  have hg : 0 < t / (t ^ 2 - μ ^ 2) := by
    apply div_pos ht; nlinarith
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = t / (t ^ 2 - μ ^ 2) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = μ / (t + μ) + t * ei / (t ^ 2 - μ ^ 2) - μ * (ej - pj) / (t ^ 2 - μ ^ 2) :=
    ⟨_, rfl⟩
  have hD : ∀ x, demandM t μ ei ej x pj = κ - γ * x := by
    intro x; unfold demandM; rw [hκ, hγ]; ring
  have hR : reactM t μ ei ej pj * (2 * γ) = κ := by
    have h5 : t ^ 2 - μ ^ 2 = (t - μ) * (t + μ) := by ring
    unfold reactM
    rw [hκ, hγ, h5]
    field_simp
    ring
  rw [hD, hD]
  set R := reactM t μ ei ej pj
  have : R * (κ - γ * R) - p * (κ - γ * p) = γ * (p - R) ^ 2 := by
    rw [← hR]; ring
  have h3 : 0 ≤ γ * (p - R) ^ 2 := mul_nonneg (by rw [hγ]; exact hg.le) (sq_nonneg _)
  linarith

lemma ml_hd_out (t ei ej : ℝ) (ht : 0 < t) :
    HasDerivAt (fun μ => outM t μ ei ej) ((2 * t - ej) / (4 * t ^ 2)) 0 := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id' (0 : ℝ)
  have A1 := hid.mul (hid.const_add (2 * t))
  have A2 := A1.mul (hid.const_sub t)
  have B := (((hasDerivAt_const (0 : ℝ) (2 * t ^ 2)).sub (hasDerivAt_pow 2 (0 : ℝ))).mul_const ei)
  have C := ((hid.const_mul t).mul_const ej)
  have hN := (A2.add B).sub C
  have D1 := (hasDerivAt_const (0 : ℝ) (t ^ 2)).sub (hasDerivAt_pow 2 (0 : ℝ))
  have D2 := (hasDerivAt_const (0 : ℝ) (4 * t ^ 2)).sub (hasDerivAt_pow 2 (0 : ℝ))
  have hD := D1.mul D2
  have hne : (t ^ 2 - 0 ^ 2) * (4 * t ^ 2 - 0 ^ 2) ≠ 0 := by
    have e : (t ^ 2 - 0 ^ 2) * (4 * t ^ 2 - 0 ^ 2) = 4 * t ^ 4 := by ring
    rw [e]; positivity
  have hq := (hN.div hD hne).mul_const t
  have hq' : HasDerivAt (fun μ : ℝ =>
      (μ * (2 * t + μ) * (t - μ) + (2 * t ^ 2 - μ ^ 2) * ei - t * μ * ej) /
          ((t ^ 2 - μ ^ 2) * (4 * t ^ 2 - μ ^ 2)) * t) ((2 * t - ej) / (4 * t ^ 2)) 0 := by
    refine hq.congr_deriv ?_
    have : t ≠ 0 := ht.ne'
    simp
    field_simp
  refine hq'.congr_of_eventuallyEq ?_
  have hmem : Set.Ioo (-t) t ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) ht
  filter_upwards [hmem] with μ hμ
  exact ml_out t μ ei ej ht hμ.1 hμ.2

lemma ml_hd_single (t ei ej : ℝ) (ht : 0 < t) :
    HasDerivAt (fun μ => singleM t μ ei ej) (-(2 * t - ei) / (4 * t ^ 2)) 0 := by
  have := (ml_hd_out t ej ei ht).const_sub 1
  refine this.congr_deriv ?_
  ring

lemma ml_hd_price (t ei ej : ℝ) (ht : 0 < t) :
    HasDerivAt (fun μ => priceM t μ ei ej) (1 / 2 - ej / (4 * t)) 0 := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id' (0 : ℝ)
  have n1 : (2 * t - 0 : ℝ) ≠ 0 := by have := ht.ne'; simpa using this
  have q1 := ((hid.const_sub t).div (hid.const_sub (2 * t)) n1).mul (hid.add_const ei)
  have n2 : (4 * t ^ 2 - 0 ^ 2 : ℝ) ≠ 0 := by
    have e : (4 * t ^ 2 - 0 ^ 2 : ℝ) = 4 * t ^ 2 := by ring
    rw [e]; positivity
  have q2 := ((hid.mul_const t).div
    ((hasDerivAt_const (0 : ℝ) (4 * t ^ 2)).sub (hasDerivAt_pow 2 (0 : ℝ))) n2).mul_const (ei - ej)
  have := q1.add q2
  refine this.congr_deriv ?_
  have : t ≠ 0 := ht.ne'
  simp
  field_simp
  ring

lemma ml_price0 (t ei ej : ℝ) (ht : 0 < t) : priceM t 0 ei ej = ei / 2 := by
  have : t ≠ 0 := ht.ne'
  unfold priceM
  field_simp
  ring

lemma ml_out0 (t ei ej : ℝ) (ht : 0 < t) : outM t 0 ei ej = ei / (2 * t) := by
  have : t ≠ 0 := ht.ne'
  rw [ml_out t 0 ei ej ht (by linarith) ht]
  field_simp
  ring

theorem solution (t μ ei ej pj : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    ∀ p : ℝ, p * demandM t μ ei ej p pj ≤
      reactM t μ ei ej pj * demandM t μ ei ej (reactM t μ ei ej pj) pj :=
  ml_react t μ ei ej pj ht (by linarith) hμt
