-- Prove2me | solution 1 for GlobalTheory.CharFormDeriv.seminorm_rem_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:57:42.597332+00:00
-- url     : https://prove2.me/submissions/b13325bc-51ac-4d5f-b826-e390d88a2aff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Theorems.Thm_GlobalTheory_CharFormDeriv_contDiff_rem
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_iteratedFDeriv_rem_comp_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv
namespace GlobalTheory.CharFormDeriv
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (f u : SchwartzMap V ℂ) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1)
    (hu : ∀ x, u x = rem t (L x) * f x) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n u ≤ |t| * (3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) := by
  set S := 2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hS
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  refine SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_
  have hu' : (⇑u) = fun x => rem t (L x) * f x := funext hu
  rw [hu']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_rem t).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) * S)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i :=
      norm_iteratedFDeriv_rem_comp_le L ht0 ht1 i x
    have h2 : (1 + ‖x‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + 2, n)) le_rfl (Nat.sub_le n i) f x
    have h3 : (1 + ‖L‖ * ‖x‖) ^ 2 ≤ (1 + ‖L‖) ^ 2 * (1 + ‖x‖) ^ 2 := by
      rw [← mul_pow]; gcongr; nlinarith
    have h4 : ‖L‖ ^ i ≤ (1 + ‖L‖) ^ n :=
      calc ‖L‖ ^ i ≤ (1 + ‖L‖) ^ i := by gcongr; linarith
        _ ≤ (1 + ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi'
    have h5 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    have hA : ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖
        ≤ 3 * |t| * ((1 + ‖L‖) ^ 2 * (1 + ‖x‖) ^ 2) * (1 + ‖L‖) ^ n :=
      h1.trans (by gcongr)
    have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + ‖x‖) ^ k *
          (3 * |t| * ((1 + ‖L‖) ^ 2 * (1 + ‖x‖) ^ 2) * (1 + ‖L‖) ^ n) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) *
          ((1 + ‖x‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) f x‖))) := by ring
      _ ≤ (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) * S)) := by gcongr
  have hfun : (fun x => rem t (L x) * f x) = fun y => (rem t ∘ ⇑L) y * f y := rfl
  rw [hfun]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (rem t ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (rem t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (|t| * (3 * (1 + ‖L‖) ^ (n + 2) * S)) :=
        Finset.sum_le_sum hterm
    _ = |t| * (3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) * S) := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring
end GlobalTheory.CharFormDeriv
