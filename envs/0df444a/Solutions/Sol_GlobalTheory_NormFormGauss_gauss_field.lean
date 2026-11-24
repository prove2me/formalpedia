-- Prove2me | solution 1 for GlobalTheory.NormFormGauss.gauss_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:09.348586+00:00
-- url     : https://prove2.me/submissions/ab4abb7a-0580-4dc3-b3bf-1191623b3ffa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Theorems.Thm_GlobalTheory_NormFormGauss_card_eq_sq
import Theorems.Thm_GlobalTheory_NormFormGauss_sum_norm_units
import Theorems.Thm_GlobalTheory_NormFormGauss_sum_eq_zero_add_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss
namespace GlobalTheory.NormFormGauss
theorem _root_.solution {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) (f : k → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b) (h0 : f 0 = 1)
    (u : k) (hu : s u = u) (hfu : f u ≠ 1) :
    ∑ x : k, f (x * s x) = -(Real.sqrt (Fintype.card k) : ℂ) := by
  obtain ⟨m, hm, hsum⟩ := sum_norm_units s hs r hr
  have hq := card_eq_sq s hs r hr
  set q := (Finset.univ.filter (fun x : k => s x = x)).card with hqdef
  set a := (Finset.univ.filter (fun x : kˣ => s x = x)).card with hadef
  have hqa : q = 1 + a := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then (1 : ℕ) else 0)
    rw [hqdef, hadef, Finset.card_filter, Finset.card_filter, this, if_pos (map_zero s)]
  have ha : 0 < a := Finset.card_pos.2 ⟨1, by simp⟩
  have hcard : Fintype.card k = 1 + Fintype.card kˣ := by
    have := sum_eq_zero_add_units (fun _ : k => (1 : ℕ))
    simpa using this
  have hmq : m = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_right ha
    rw [hm, hq, hqa] at hcard
    rw [hqa]
    nlinarith
  have hz : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f (u + y) =
        ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y := by
      refine Finset.sum_equiv (Equiv.addLeft u) ?_ ?_
      · intro i; simp [hu]
      · intro i _; rfl
    simp only [hadd, ← Finset.mul_sum] at h1
    have h2 : (f u - 1) * ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hfu)
  have hu1 : ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y = -1 := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then f x else 0)
    rw [← Finset.sum_filter, hz, ← Finset.sum_filter] at this
    simp only [map_zero, if_true, h0] at this
    linear_combination -this
  rw [sum_eq_zero_add_units, hsum, hu1, hq, hmq]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg q)]
  simp [h0]
end GlobalTheory.NormFormGauss
