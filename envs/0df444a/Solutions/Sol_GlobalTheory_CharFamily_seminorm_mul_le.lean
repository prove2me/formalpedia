-- Prove2me | solution 1 for GlobalTheory.CharFamily.seminorm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:53.51626+00:00
-- url     : https://prove2.me/submissions/addff84d-980e-4ae5-a529-ba78f890632f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CharFamily
theorem _root_.solution (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h g : SchwartzMap E ℂ)
    (hg : ∀ x, g x = c x * h x) (k n m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcb : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i c x‖ ≤ M * (1 + ‖x‖) ^ m) :
    SchwartzMap.seminorm ℂ k n g ≤ 2 ^ n * M *
      (2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h) := by
  set S := 2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h
    with hS
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℂ k n g (by positivity) fun x => ?_
  have hg' : (⇑g) = fun x => c x * h x := funext hg
  rw [hg']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hc (h.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        ≤ (n.choose i : ℝ) * (M * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hcb i hi' x
    have h2 : (1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + m, n)) le_rfl (Nat.sub_le n i) h x
    have h5 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + ‖x‖) ^ k * (M * (1 + ‖x‖) ^ m) *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by gcongr
      _ = (n.choose i : ℝ) * (M * ((1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖)) := by
            ring
      _ ≤ (n.choose i : ℝ) * (M * S) := by gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => c y * h y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * S) := Finset.sum_le_sum hterm
    _ = 2 ^ n * M * S := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring
end GlobalTheory.CharFamily
