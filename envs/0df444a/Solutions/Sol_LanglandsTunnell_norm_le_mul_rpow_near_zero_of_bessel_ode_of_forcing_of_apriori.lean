-- Prove2me | solution 1 for LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0b74f4ec-17f6-56e5-9b27-19dcf75f94b7

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori

set_option autoImplicit false

open scoped Real

namespace Gap41

open Real Set Filter Topology

theorem odeC (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by
  set β : ℝ := b.re with hβ
  set A' : ℝ := max A 0 with hA'
  set c : ℝ := max (β - σ) 0 with hc
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hc0 : 0 ≤ c := le_max_right _ _

  set F : ℝ → ℂ := fun s => f (Real.exp (-s)) with hF
  set G : ℝ → ℂ := fun s => Complex.exp (b * (s : ℂ)) * F s with hG

  have hGd : ∀ s : ℝ, HasDerivAt G (-(Complex.exp (b * (s : ℂ)) * h (Real.exp (-s)))) s := by
    intro s
    have hy : 0 < Real.exp (-s) := Real.exp_pos _
    have hfd : HasDerivAt f (deriv f (Real.exp (-s))) (Real.exp (-s)) :=
      (hf.differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
    have hu : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
      have h__af := (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
      simp at h__af
      exact h__af
    have hFd : HasDerivAt F ((-Real.exp (-s)) • deriv f (Real.exp (-s))) s := hfd.scomp s hu
    have he : HasDerivAt (fun s : ℝ => Complex.exp (b * (s : ℂ))) (Complex.exp (b * (s : ℂ)) * b) s := by
      have h1 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul b
      exact (Complex.hasDerivAt_exp (b * (s : ℂ))).comp s h1
    have h := he.mul hFd
    convert h using 1 <;> try with_reducible_and_instances rfl

    have key := hfeq (Real.exp (-s)) hy
    rw [Complex.real_smul, Complex.ofReal_neg]
    linear_combination Complex.exp (b * (s : ℂ)) * key

  have hG'bound : ∀ S : ℝ, 0 ≤ S → ∀ τ ∈ Icc 0 S,
      ‖-(Complex.exp (b * (τ : ℂ)) * h (Real.exp (-τ)))‖ ≤ A' * Real.exp (c * S) := by
    intro S hS τ hτ
    obtain ⟨hτ0, hτS⟩ := hτ
    have hy : 0 < Real.exp (-τ) := Real.exp_pos _
    have hy1 : Real.exp (-τ) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    rw [norm_neg, norm_mul, Complex.norm_exp]
    have hre : (b * (τ : ℂ)).re = β * τ := by simp [hβ, Complex.mul_re]
    rw [hre]
    have h1 : ‖h (Real.exp (-τ))‖ ≤ A' * Real.exp (-(σ * τ)) := by
      calc ‖h (Real.exp (-τ))‖ ≤ A * Real.exp (-τ) ^ σ := hh _ hy hy1
        _ ≤ A' * Real.exp (-τ) ^ σ := by gcongr; exact le_max_left _ _
        _ = A' * Real.exp (-(σ * τ)) := by rw [← Real.exp_mul]; ring_nf
    calc Real.exp (β * τ) * ‖h (Real.exp (-τ))‖
        ≤ Real.exp (β * τ) * (A' * Real.exp (-(σ * τ))) := by gcongr
      _ = A' * Real.exp ((β - σ) * τ) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf
      _ ≤ A' * Real.exp (c * S) := by
          have hexp : (β - σ) * τ ≤ c * S :=
            calc (β - σ) * τ ≤ c * τ := by gcongr; exact le_max_left _ _
              _ ≤ c * S := by gcongr
          gcongr

  have hMV : ∀ S : ℝ, 0 ≤ S → ‖G S - G 0‖ ≤ A' * Real.exp (c * S) * S := by
    intro S hS
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := G) (s := Icc 0 S) (C := A' * Real.exp (c * S))
      (fun τ _ => (hGd τ).hasDerivWithinAt) (hG'bound S hS) (convex_Icc 0 S)
      (left_mem_Icc.mpr hS) (right_mem_Icc.mpr hS)
    simpa [Real.norm_eq_abs, abs_of_nonneg hS] using h

  refine ⟨‖f 1‖ + A' / ε, fun y hy hy1 => ?_⟩
  set S : ℝ := -Real.log y with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef, neg_nonneg]; exact Real.log_nonpos hy.le hy1
  have hyS : Real.exp (-S) = y := by rw [hSdef, neg_neg, Real.exp_log hy]
  have hG0 : G 0 = f 1 := by simp [hG, hF]
  have hFS : F S = f y := by simp [hF, hyS]

  have hexp1 : 1 ≤ Real.exp ((c + ε) * S) := Real.one_le_exp (by positivity)
  have hSle : S ≤ Real.exp (ε * S) / ε := by
    rw [le_div_iff₀ hε]
    have := Real.add_one_le_exp (ε * S)
    nlinarith
  have hGS : ‖G S‖ ≤ (‖f 1‖ + A' / ε) * Real.exp ((c + ε) * S) := by
    have h1 : ‖G S‖ ≤ ‖G 0‖ + ‖G S - G 0‖ := norm_le_insert' _ _
    have h2 := hMV S hS0
    rw [hG0] at h1 h2
    calc ‖G S‖ ≤ ‖f 1‖ + A' * Real.exp (c * S) * S := by linarith
      _ ≤ ‖f 1‖ + A' * Real.exp (c * S) * (Real.exp (ε * S) / ε) := by gcongr
      _ = ‖f 1‖ + A' / ε * Real.exp ((c + ε) * S) := by rw [add_mul, Real.exp_add]; ring
      _ ≤ ‖f 1‖ * Real.exp ((c + ε) * S) + A' / ε * Real.exp ((c + ε) * S) := by
          gcongr; exact le_mul_of_one_le_right (norm_nonneg _) hexp1
      _ = (‖f 1‖ + A' / ε) * Real.exp ((c + ε) * S) := by ring

  have hfy : ‖f y‖ = Real.exp (-(β * S)) * ‖G S‖ := by
    rw [← hFS, hG]
    simp only
    rw [norm_mul, Complex.norm_exp, show (b * (S : ℂ)).re = β * S by simp [hβ, Complex.mul_re], ← mul_assoc,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

  have hpow : Real.exp (-(β * S)) * Real.exp ((c + ε) * S) = y ^ (min β σ - ε) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hy, hSdef]
    congr 1
    have : min β σ = β - c := by
      rw [hc]
      rcases le_total β σ with hle | hle
      · rw [min_eq_left hle, max_eq_right (by linarith)]; ring
      · rw [min_eq_right hle, max_eq_left (by linarith)]; ring
    rw [this]
    ring
  calc ‖f y‖ = Real.exp (-(β * S)) * ‖G S‖ := hfy
    _ ≤ Real.exp (-(β * S)) * ((‖f 1‖ + A' / ε) * Real.exp ((c + ε) * S)) := by gcongr
    _ = (‖f 1‖ + A' / ε) * (Real.exp (-(β * S)) * Real.exp ((c + ε) * S)) := by ring
    _ = (‖f 1‖ + A' / ε) * y ^ (min β σ - ε) := by rw [hpow]

theorem gapC (b : ℂ) (m K r B : ℝ) (hr : b.re < r) (f u : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hu : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖u y‖ ≤ K * y ^ m)
    (hap : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + u y) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ m := by
  set β : ℝ := b.re with hβ
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  rcases le_or_gt m β with hm | hm
  ·
    refine ⟨max B 0, fun y hy hy1 => ?_⟩
    calc ‖f y‖ ≤ B * y ^ r := hap y hy hy1
      _ ≤ max B 0 * y ^ r := by gcongr; exact le_max_left _ _
      _ ≤ max B 0 * y ^ m := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) hB0
  ·
    set F : ℝ → ℂ := fun s => f (Real.exp (-s)) with hF
    set G : ℝ → ℂ := fun s => Complex.exp (b * (s : ℂ)) * F s with hG
    have hGd : ∀ s : ℝ, HasDerivAt G (-(Complex.exp (b * (s : ℂ)) * u (Real.exp (-s)))) s := by
      intro s
      have hy : 0 < Real.exp (-s) := Real.exp_pos _
      have hfd : HasDerivAt f (deriv f (Real.exp (-s))) (Real.exp (-s)) :=
        (hf.differentiableAt (isOpen_Ioi.mem_nhds hy)).hasDerivAt
      have hu' : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
        convert (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s) using 1 <;>
          first | with_reducible_and_instances rfl | rfl | simp
      have hFd : HasDerivAt F ((-Real.exp (-s)) • deriv f (Real.exp (-s))) s := hfd.scomp s hu'
      have he : HasDerivAt (fun s : ℝ => Complex.exp (b * (s : ℂ))) (Complex.exp (b * (s : ℂ)) * b) s := by
        have h1 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul b
        exact (Complex.hasDerivAt_exp (b * (s : ℂ))).comp s h1
      have h := he.mul hFd
      convert h using 1 <;> try with_reducible_and_instances rfl
      have key := hfeq (Real.exp (-s)) hy
      rw [Complex.real_smul, Complex.ofReal_neg]
      linear_combination Complex.exp (b * (s : ℂ)) * key

    have hG'b : ∀ τ : ℝ, 0 ≤ τ → ‖-(Complex.exp (b * (τ : ℂ)) * u (Real.exp (-τ)))‖ ≤ max K 0 * Real.exp ((β - m) * τ) := by
      intro τ hτ
      have hy : 0 < Real.exp (-τ) := Real.exp_pos _
      have hy1 : Real.exp (-τ) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      rw [norm_neg, norm_mul, Complex.norm_exp, show (b * (τ : ℂ)).re = β * τ by simp [hβ, Complex.mul_re]]
      calc Real.exp (β * τ) * ‖u (Real.exp (-τ))‖ ≤ Real.exp (β * τ) * (max K 0 * Real.exp (-τ) ^ m) := by
            gcongr
            calc ‖u (Real.exp (-τ))‖ ≤ K * Real.exp (-τ) ^ m := hu _ hy hy1
              _ ≤ max K 0 * Real.exp (-τ) ^ m := by gcongr; exact le_max_left _ _
        _ = max K 0 * Real.exp ((β - m) * τ) := by
            rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]; ring_nf

    have hmβ : 0 < m - β := by linarith
    set K' : ℝ := max K 0 with hK'
    have hseg : ∀ s T : ℝ, 0 ≤ s → s ≤ T →
        ‖G T - G s‖ ≤ K' / (m - β) * (Real.exp ((β - m) * s) - Real.exp ((β - m) * T)) := by
      intro s T hs hsT
      set φ : ℝ → ℂ := fun τ => G τ - G s with hφ
      set Bf : ℝ → ℝ := fun τ => K' / (m - β) * (Real.exp ((β - m) * s) - Real.exp ((β - m) * τ)) with hBf
      have hφc : ContinuousOn φ (Icc s T) := fun τ _ =>
        (((hGd τ).continuousAt).sub continuousAt_const).continuousWithinAt
      have hφd : ∀ τ ∈ Ico s T, HasDerivWithinAt φ (-(Complex.exp (b * (τ : ℂ)) * u (Real.exp (-τ)))) (Ici τ) τ :=
        fun τ _ => ((hGd τ).sub_const (G s)).hasDerivWithinAt
      have hφs : ‖φ s‖ ≤ Bf s := by simp [hφ, hBf]
      have hBd : ∀ τ : ℝ, HasDerivAt Bf (K' * Real.exp ((β - m) * τ)) τ := by
        intro τ
        have h1 : HasDerivAt (fun τ : ℝ => Real.exp ((β - m) * τ)) (Real.exp ((β - m) * τ) * (β - m)) τ := by
          have hl : HasDerivAt (fun τ : ℝ => (β - m) * τ) (β - m) τ := by
            simpa using (hasDerivAt_id τ).const_mul (β - m)
          exact (Real.hasDerivAt_exp _).comp τ hl
        have h2 := (h1.const_sub (Real.exp ((β - m) * s))).const_mul (K' / (m - β))
        have hmβ' : m - β ≠ 0 := hmβ.ne'
        convert h2 using 1 <;> try with_reducible_and_instances rfl
        all_goals try rfl
        field_simp
        ring
      have hbound : ∀ τ ∈ Ico s T, ‖-(Complex.exp (b * (τ : ℂ)) * u (Real.exp (-τ)))‖ ≤ K' * Real.exp ((β - m) * τ) :=
        fun τ hτ => hG'b τ (hs.trans hτ.1)
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary hφc hφd hφs hBd hbound
        (right_mem_Icc.mpr hsT)
      simpa [hφ, hBf] using this

    have hGT : ∀ T : ℝ, 0 ≤ T → ‖G T‖ ≤ max B 0 * Real.exp ((β - r) * T) := by
      intro T hT
      have hy : 0 < Real.exp (-T) := Real.exp_pos _
      have hy1 : Real.exp (-T) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      simp only [hG, hF]
      rw [norm_mul, Complex.norm_exp, show (b * (T : ℂ)).re = β * T by simp [hβ, Complex.mul_re]]
      calc Real.exp (β * T) * ‖f (Real.exp (-T))‖ ≤ Real.exp (β * T) * (max B 0 * Real.exp (-T) ^ r) := by
            gcongr
            calc ‖f (Real.exp (-T))‖ ≤ B * Real.exp (-T) ^ r := hap _ hy hy1
              _ ≤ max B 0 * Real.exp (-T) ^ r := by gcongr; exact le_max_left _ _
        _ = max B 0 * Real.exp ((β - r) * T) := by
            rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]; ring_nf
    have htend : ∀ s : ℝ, Tendsto (fun T : ℝ => K' / (m - β) * (Real.exp ((β - m) * s) - Real.exp ((β - m) * T)) +
        max B 0 * Real.exp ((β - r) * T)) atTop (𝓝 (K' / (m - β) * (Real.exp ((β - m) * s) - 0) + max B 0 * 0)) := by
      intro s
      have h1 : Tendsto (fun T : ℝ => Real.exp ((β - m) * T)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun T : ℝ => (β - m) * T) atTop atBot :=
          (tendsto_id.const_mul_atTop_of_neg (show β - m < 0 by linarith))
        exact Real.tendsto_exp_atBot.comp hlin
      have h2 : Tendsto (fun T : ℝ => Real.exp ((β - r) * T)) atTop (𝓝 0) := by
        have hlin : Tendsto (fun T : ℝ => (β - r) * T) atTop atBot :=
          (tendsto_id.const_mul_atTop_of_neg (show β - r < 0 by linarith))
        exact Real.tendsto_exp_atBot.comp hlin
      exact ((tendsto_const_nhds.sub h1).const_mul _).add (h2.const_mul _)
    have hGs : ∀ s : ℝ, 0 ≤ s → ‖G s‖ ≤ K' / (m - β) * Real.exp ((β - m) * s) := by
      intro s hs
      have hlim := htend s
      simp only [sub_zero, mul_zero, add_zero] at hlim
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop s] with T hT
      have h1 : ‖G s‖ ≤ ‖G T - G s‖ + ‖G T‖ := by
        have := norm_sub_le (G T - G s) (G T); simp only [sub_sub_cancel_left, norm_neg] at this; exact this
      linarith [hseg s T hs hT, hGT T (hs.trans hT)]

    refine ⟨K' / (m - β), fun y hy hy1 => ?_⟩
    set s : ℝ := -Real.log y with hsdef
    have hs0 : 0 ≤ s := by rw [hsdef, neg_nonneg]; exact Real.log_nonpos hy.le hy1
    have hys : Real.exp (-s) = y := by rw [hsdef, neg_neg, Real.exp_log hy]
    have hfy : ‖f y‖ = Real.exp (-(β * s)) * ‖G s‖ := by
      rw [show f y = F s by simp [hF, hys], hG]
      simp only
      rw [norm_mul, Complex.norm_exp, show (b * (s : ℂ)).re = β * s by simp [hβ, Complex.mul_re], ← mul_assoc,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have hpow : Real.exp (-(β * s)) * Real.exp ((β - m) * s) = y ^ m := by
      rw [← Real.exp_add, Real.rpow_def_of_pos hy, hsdef]; ring_nf
    calc ‖f y‖ = Real.exp (-(β * s)) * ‖G s‖ := hfy
      _ ≤ Real.exp (-(β * s)) * (K' / (m - β) * Real.exp ((β - m) * s)) := by gcongr; exact hGs s hs0
      _ = K' / (m - β) * y ^ m := by rw [← hpow]; ring

theorem twoTermAp (ν : ℂ) (σ A ρ B : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hap : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ ρ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (ρ + 2) - ε) := by
  have hO : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  set u : ℝ → ℂ := fun y => (y : ℂ) * deriv f y - (1 / 2 - ν) * f y with hu
  set h₂ : ℝ → ℂ := fun y => h y + 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y with hh₂
  have hud : ∀ y : ℝ, 0 < y →
      HasDerivAt u (deriv f y + (y : ℂ) * deriv (deriv f) y - (1 / 2 - ν) * deriv f y) y := by
    intro y hy
    have h1 : HasDerivAt f (deriv f y) y := (hf.differentiableAt (hO.mem_nhds hy)).hasDerivAt
    have h2 : HasDerivAt (deriv f) (deriv (deriv f) y) y := (hf'.differentiableAt (hO.mem_nhds hy)).hasDerivAt
    have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
    have h3 := (hc.mul h2).sub (h1.const_mul (1 / 2 - ν))
    convert h3 using 1 <;> try with_reducible_and_instances rfl
    all_goals try rfl
    ring
  have hudiff : DifferentiableOn ℝ u (Ioi 0) := fun y hy => (hud y hy).differentiableAt.differentiableWithinAt
  have hueq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv u y = (1 / 2 + ν) * u y + h₂ y := by
    intro y hy
    rw [(hud y hy).deriv]
    simp only [hu, hh₂]
    linear_combination hfeq y hy
  set σ₂ : ℝ := min σ (ρ + 2) with hσ₂
  set A₂ : ℝ := max A 0 + 4 * π ^ 2 * max B 0 with hA₂
  have hh₂b : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h₂ y‖ ≤ A₂ * y ^ σ₂ := by
    intro y hy hy1
    have e1 : y ^ σ ≤ y ^ σ₂ := Real.rpow_le_rpow_of_exponent_ge hy hy1 (min_le_left _ _)
    have e2 : y ^ 2 * y ^ ρ ≤ y ^ σ₂ := by
      rw [show (y ^ 2 : ℝ) = y ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hy]
      exact Real.rpow_le_rpow_of_exponent_ge hy hy1 (by rw [hσ₂, add_comm]; exact min_le_right _ _)
    have hn : ‖(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y‖ = 4 * π ^ 2 * y ^ 2 * ‖f y‖ := by
      rw [show (4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y = ((4 * π ^ 2 * y ^ 2 : ℝ) : ℂ) * f y by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖h₂ y‖ ≤ ‖h y‖ + ‖(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * f y‖ := norm_add_le _ _
      _ ≤ A * y ^ σ + 4 * π ^ 2 * y ^ 2 * (B * y ^ ρ) := by
          rw [hn]
          gcongr
          · exact hh y hy hy1
          · exact hap y hy hy1
      _ ≤ max A 0 * y ^ σ₂ + 4 * π ^ 2 * (max B 0 * y ^ σ₂) := by
          refine add_le_add ?_ ?_
          · calc A * y ^ σ ≤ max A 0 * y ^ σ := by gcongr; exact le_max_left _ _
              _ ≤ max A 0 * y ^ σ₂ := by gcongr
          · calc 4 * π ^ 2 * y ^ 2 * (B * y ^ ρ)
                = 4 * π ^ 2 * (B * (y ^ 2 * y ^ ρ)) := by ring
              _ ≤ 4 * π ^ 2 * (max B 0 * (y ^ 2 * y ^ ρ)) := by
                  gcongr; exact le_max_left _ _
              _ ≤ 4 * π ^ 2 * (max B 0 * y ^ σ₂) := by gcongr
      _ = A₂ * y ^ σ₂ := by rw [hA₂]; ring
  obtain ⟨C, hC⟩ := odeC (1 / 2 + ν) σ₂ A₂ u h₂ hudiff hh₂b hueq ε hε
  have hre : (1 / 2 + ν).re = 1 / 2 + ν.re := by simp
  refine ⟨C, fun y hy hy1 => ?_⟩
  have := hC y hy hy1
  rw [hre, hσ₂, ← min_assoc] at this
  exact this

theorem round (ν : ℂ) (σ A r B ρ Bρ : ℝ) (hr : 1 / 2 - ν.re < r) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hapρ : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ Bρ * y ^ ρ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (ρ + 2) - ε) := by
  obtain ⟨C, hC⟩ := twoTermAp ν σ A ρ Bρ f h hf hf' hh hapρ hfeq ε hε
  have hfeq1 : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = (1 / 2 - ν) * f y +
      ((y : ℂ) * deriv f y - (1 / 2 - ν) * f y) := fun y _ => by ring
  have hr' : (1 / 2 - ν).re < r := by simpa using hr
  exact gapC (1 / 2 - ν) _ C r B hr' f _ hf hC hapriori hfeq1

end Gap41

open Gap41

theorem solution
    (ν : ℂ) (hν : 0 ≤ ν.re) (σ A r B : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (r + 2) - ε)) ∧
    (1 / 2 - ν.re < r → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε) ∧
      ‖(y : ℂ) * deriv f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε)) := by
  set M : ℝ := min (1 / 2 + ν.re) σ with hM
  refine ⟨fun ε hε => twoTermAp ν σ A r B f h hf hf' hh hapriori hfeq ε hε, fun hr => ?_⟩

  have hind : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min M (r + 2 * k) - ε) := by
    intro k
    induction k with
    | zero =>
      intro ε hε
      refine ⟨max B 0, fun y hy hy1 => ?_⟩
      calc ‖f y‖ ≤ B * y ^ r := hapriori y hy hy1
        _ ≤ max B 0 * y ^ r := by gcongr; exact le_max_left _ _
        _ ≤ max B 0 * y ^ (min M (r + 2 * (0 : ℕ)) - ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1
              (by simp only [Nat.cast_zero, mul_zero, add_zero]; linarith [min_le_right M r])) (le_max_right _ _)
    | succ k ih =>
      intro ε hε
      obtain ⟨Bρ, hBρ⟩ := ih (ε / 2) (by linarith)
      obtain ⟨C, hC⟩ := round ν σ A r B (min M (r + 2 * k) - ε / 2) Bρ hr f h hf hf' hh hapriori hBρ hfeq (ε / 2) (by linarith)
      refine ⟨max C 0, fun y hy hy1 => ?_⟩
      have hexp : min M (r + 2 * ((k + 1 : ℕ) : ℝ)) - ε ≤ min (min (1 / 2 + ν.re) σ) (min M (r + 2 * k) - ε / 2 + 2) - ε / 2 := by
        rw [← hM]
        push_cast
        have hkey : min M (r + 2 * ((k : ℝ) + 1)) - ε / 2 ≤ min M (min M (r + 2 * k) - ε / 2 + 2) := by
          refine le_min (by linarith [min_le_left M (r + 2 * ((k : ℝ) + 1))]) ?_
          have : min M (r + 2 * ((k : ℝ) + 1)) ≤ min M (r + 2 * k) + 2 := by
            rw [← min_add_add_right]
            exact min_le_min (by linarith) (by linarith)
          linarith
        linarith
      calc ‖f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (min M (r + 2 * k) - ε / 2 + 2) - ε / 2) := hC y hy hy1
        _ ≤ max C 0 * y ^ (min (min (1 / 2 + ν.re) σ) (min M (r + 2 * k) - ε / 2 + 2) - ε / 2) := by
            gcongr; exact le_max_left _ _
        _ ≤ max C 0 * y ^ (min M (r + 2 * ((k + 1 : ℕ) : ℝ)) - ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hexp) (le_max_right _ _)

  obtain ⟨k, hk⟩ : ∃ k : ℕ, M ≤ r + 2 * k := by
    obtain ⟨k, hk⟩ := exists_nat_ge ((M - r) / 2)
    exact ⟨k, by linarith [hk, (div_le_iff₀ (show (0:ℝ) < 2 by norm_num)).mp (le_refl ((M - r) / 2))]⟩
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hind k (ε / 2) (by linarith)
  have hmin : min M (r + 2 * k) = M := min_eq_left hk
  rw [hmin] at hC₁

  obtain ⟨C₂, hC₂⟩ := twoTermAp ν σ A (M - ε / 2) C₁ f h hf hf' hh hC₁ hfeq (ε / 2) (by linarith)
  have hexp2 : M - ε ≤ min (min (1 / 2 + ν.re) σ) (M - ε / 2 + 2) - ε / 2 := by
    rw [← hM]
    have : M - ε / 2 ≤ min M (M - ε / 2 + 2) := le_min (by linarith) (by linarith)
    linarith
  refine ⟨max C₁ 0 + (max C₂ 0 + ‖(1 / 2 : ℂ) - ν‖ * max C₁ 0), fun y hy hy1 => ?_⟩
  have hyM : 0 ≤ y ^ (M - ε) := (Real.rpow_pos_of_pos hy _).le
  have hf1 : ‖f y‖ ≤ max C₁ 0 * y ^ (M - ε) :=
    calc ‖f y‖ ≤ C₁ * y ^ (M - ε / 2) := hC₁ y hy hy1
      _ ≤ max C₁ 0 * y ^ (M - ε / 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C₁ 0 * y ^ (M - ε) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)) (le_max_right _ _)
  have hu1 : ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ max C₂ 0 * y ^ (M - ε) :=
    calc ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C₂ * y ^ (min (min (1 / 2 + ν.re) σ) (M - ε / 2 + 2) - ε / 2) := hC₂ y hy hy1
      _ ≤ max C₂ 0 * y ^ (min (min (1 / 2 + ν.re) σ) (M - ε / 2 + 2) - ε / 2) := by gcongr; exact le_max_left _ _
      _ ≤ max C₂ 0 * y ^ (M - ε) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hexp2) (le_max_right _ _)
  constructor
  · calc ‖f y‖ ≤ max C₁ 0 * y ^ (M - ε) := hf1
      _ ≤ (max C₁ 0 + (max C₂ 0 + ‖(1 / 2 : ℂ) - ν‖ * max C₁ 0)) * y ^ (M - ε) := by
          gcongr; nlinarith [le_max_right C₂ 0, le_max_right C₁ 0, norm_nonneg ((1 / 2 : ℂ) - ν)]
  · have : (y : ℂ) * deriv f y = ((y : ℂ) * deriv f y - (1 / 2 - ν) * f y) + (1 / 2 - ν) * f y := by ring
    rw [this]
    calc ‖((y : ℂ) * deriv f y - (1 / 2 - ν) * f y) + (1 / 2 - ν) * f y‖
        ≤ ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ + ‖(1 / 2 - ν) * f y‖ := norm_add_le _ _
      _ ≤ max C₂ 0 * y ^ (M - ε) + ‖(1 / 2 : ℂ) - ν‖ * (max C₁ 0 * y ^ (M - ε)) := by
          rw [norm_mul]; gcongr
      _ ≤ (max C₁ 0 + (max C₂ 0 + ‖(1 / 2 : ℂ) - ν‖ * max C₁ 0)) * y ^ (M - ε) := by
          nlinarith [le_max_right C₁ 0, hyM]

end S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
end P2MW
export P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori (solution)
