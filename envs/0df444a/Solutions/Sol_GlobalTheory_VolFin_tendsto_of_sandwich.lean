-- Prove2me | solution 1 for GlobalTheory.VolFin.tendsto_of_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:54.367267+00:00
-- url     : https://prove2.me/submissions/56f1402c-4e2d-4526-a04d-1524066ba26e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
namespace GlobalTheory.VolFin
theorem _root_.solution (h h' : ℕ → ℕ) (D g c c' : ℕ) (δ : ℝ)
    (hh : Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 δ))
    (lo : ∀ e, D * h e ≤ h' (e + c)) (up : ∀ e, h' e ≤ D * h (e + c')) :
    Tendsto (fun e : ℕ => (h' e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 (D * δ)) := by
  have hr : ∀ k : ℕ, Tendsto (fun e : ℕ => (((e + k : ℕ) : ℝ) / (e : ℝ)) ^ g) atTop (𝓝 1) := by
    intro k
    have h2 := ((tendsto_natCast_div_add_atTop (k : ℝ)).inv₀ one_ne_zero).pow g
    rw [inv_one, one_pow] at h2
    refine h2.congr fun e => ?_
    rw [inv_div, Nat.cast_add]
  refine (tendsto_add_atTop_iff_nat c).1 ?_
  have hL : Tendsto (fun e : ℕ => (D : ℝ) * ((h e : ℝ) / (e : ℝ) ^ g) /
      (((e + c : ℕ) : ℝ) / (e : ℝ)) ^ g) atTop (𝓝 (D * δ)) := by
    have := (hh.const_mul (D : ℝ)).div (hr c) one_ne_zero
    rwa [div_one] at this
  have hU : Tendsto (fun e : ℕ => (D : ℝ) * ((h (e + (c + c')) : ℝ) /
      ((e + (c + c') : ℕ) : ℝ) ^ g) * ((((e + c) + c' : ℕ) : ℝ) / ((e + c : ℕ) : ℝ)) ^ g)
      atTop (𝓝 (D * δ)) := by
    have := ((hh.comp (tendsto_add_atTop_nat (c + c'))).const_mul (D : ℝ)).mul
      ((hr c').comp (tendsto_add_atTop_nat c))
    rw [mul_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hcast : ((D * h e : ℕ) : ℝ) ≤ (h' (e + c) : ℝ) := by exact_mod_cast lo e
    push_cast at hcast ⊢
    have hc0 : (0 : ℝ) < (e : ℝ) + c := by positivity
    have heq : (D : ℝ) * ((h e : ℝ) / (e : ℝ) ^ g) / (((e : ℝ) + c) ^ g / (e : ℝ) ^ g)
        = (D : ℝ) * (h e : ℝ) / ((e : ℝ) + c) ^ g := by
      field_simp
    rw [div_pow, heq]
    gcongr
  · filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hcast : (h' (e + c) : ℝ) ≤ ((D * h (e + c + c') : ℕ) : ℝ) := by exact_mod_cast up (e + c)
    rw [show e + (c + c') = e + c + c' from (add_assoc _ _ _).symm]
    push_cast at hcast ⊢
    have hc0 : (0 : ℝ) < (e : ℝ) + c := by positivity
    have hcc0 : (0 : ℝ) < (e : ℝ) + c + c' := by positivity
    have heq : (D : ℝ) * ((h (e + c + c') : ℝ) / ((e : ℝ) + c + c') ^ g) *
        (((e : ℝ) + c + c') ^ g / ((e : ℝ) + c) ^ g)
        = (D : ℝ) * (h (e + c + c') : ℝ) / ((e : ℝ) + c) ^ g := by
      field_simp
    rw [div_pow, heq]
    gcongr
end GlobalTheory.VolFin
