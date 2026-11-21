-- Prove2me | solution 1 for MasulloRH.smoothed_prime_ramp_upper_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:44:54.733358+00:00
-- url     : https://prove2.me/submissions/3c8e4b99-5273-4283-8885-6e19371b0b02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_fourth_power_prime_ramp_upper_windows
import Theorems.Thm_MasulloRH_prime_ramp_chord_and_fourth_power_bound
import Mathlib
open Finset ArithmeticFunction MasulloRH

theorem solution :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
          ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0) -
          y * (Real.log y - 1 - Real.eulerMascheroniConstant) ≤ C * y ^ θ := by
  intro θ hhalf hone
  obtain ⟨δ,C,hδ,hC,hdisc⟩ := fourth_power_prime_ramp_upper_windows θ hhalf hone
  refine ⟨δ,C+225/4,hδ,by positivity,fun X hX => ?_⟩
  let m := max 1 ⌈X⌉₊
  obtain ⟨K,hK,h⟩ := hdisc m (le_max_left ..)
  have hK1 : 1 ≤ K := (show 1 ≤ m from le_max_left ..).trans hK
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK1
  have hXK : X ≤ K := (Nat.le_ceil X).trans (by exact_mod_cast (show ⌈X⌉₊ ≤ m from le_max_right ..).trans hK)
  have hY : X ≤ (K:ℝ)^4 := hXK.trans (le_self_pow₀ hK' (by norm_num))
  refine ⟨(K:ℝ)^4,hY,fun y hy => ?_⟩
  have hy0 : 0 ≤ y := (pow_nonneg (Nat.cast_nonneg K) _).trans hy.1
  let r := y ^ ((4:ℝ)⁻¹)
  have hr : 0 ≤ r := Real.rpow_nonneg hy0 _
  have hr4 : r^4=y := Real.rpow_inv_natCast_pow hy0 (by decide : (4:ℕ)≠0)
  let k := ⌊r⌋₊
  have hkR : (k:ℝ)≤r := Nat.floor_le hr
  have hrk : r < (k:ℝ)+1 := Nat.lt_floor_add_one r
  have hKk : K≤k := Nat.le_floor <| le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) hr (hr4.symm ▸ hy.1)
  have hpow : ((K:ℝ)^4)^(1+δ) = ((K:ℝ)^(1+δ))^4 := by
    rw [←Real.rpow_natCast_mul (Nat.cast_nonneg K),←Real.rpow_mul_natCast (Nat.cast_nonneg K)]
    congr 1;ring
  have htop : r ≤ (K:ℝ)^(1+δ) := le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) (by positivity) (hr4 ▸ (hy.2.trans_eq hpow))
  have hkr := hkR.trans htop
  have hnext : ((k+1:ℕ):ℝ) ≤ (K:ℝ)^(1+δ)+1 := by push_cast; linarith
  have hright := h (k+1) (hKk.trans (Nat.le_succ k)) hnext
  push_cast at hright
  apply prime_ramp_chord_and_fourth_power_bound.2 k (hK1.trans hKk) θ C hhalf.le hone.le hC (h k hKk (by linarith only [hkr])) hright
  · exact (pow_le_pow_left₀ (Nat.cast_nonneg k) hkR 4).trans_eq hr4
  · exact hr4 ▸ pow_le_pow_left₀ hr hrk.le 4
