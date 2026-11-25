-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:47.682185+00:00
-- url     : https://prove2.me/submissions/d9cffc44-1425-4d31-a84b-c2d70f385e10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummable
import Theorems.Thm_P2M_GlobalTheory_SchwartzTranslateSum_summable_one_add_norm_inv_pow__68b39a97649f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap
noncomputable section
open GlobalTheory GlobalTheory.SchwartzTranslateSum
namespace GlobalTheory.SchwartzTranslateSum
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall (0 : V)
  set N := Module.finrank ℤ Λ + 1 with hNdef
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hSdef
  set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h
    with hAdef
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  clear_value D A S R' N
  refine (hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)
  have hfun : (u l : V → ℂ) = fun y => h (y + l) * f y := funext (hu l)
  rw [hfun]
  have hsh : ContDiff ℝ n (fun y => h (y + (l : V))) :=
    ((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)
  have hsf : ContDiff ℝ n (f : V → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_add_right] at hleib
  by_cases hx : x + (l : V) ∈ tsupport h
  · have hxl : ‖x + (l : V)‖ ≤ R' := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (hR'def ▸ le_max_left _ _)
    have hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖) := by
      have : ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖ := by
        calc ‖(l : V)‖ = ‖(x + (l : V)) - x‖ := by simp
          _ ≤ ‖x + (l : V)‖ + ‖x‖ := norm_sub_le _ _
      have hn' : ‖l‖ = ‖(l : V)‖ := rfl
      nlinarith [norm_nonneg x]
    have hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N := by
      intro m hm
      have h1 := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m)
        le_rfl hm f x
      have h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S := by rw [hSdef]; exact h1
      have hpos : 0 < (1 + ‖l‖) ^ N := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ * (1 + ‖l‖) ^ N
          ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ * ((1 + R') * (1 + ‖x‖)) ^ N := by
            gcongr
            linarith [norm_nonneg x]
        _ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr
        _ = D := by rw [hDdef]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h (x + l)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h (x + l)‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h *
            (D * ((1 + ‖l‖)⁻¹) ^ N) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity))
              (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)
      _ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by
            rw [hAdef, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
  · have hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0 := fun i =>
      Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib
    have : ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0 :=
      le_antisymm hleib (norm_nonneg _)
    rw [this, mul_zero]
    exact mul_nonneg (mul_nonneg hA0 hD0) (by positivity)
end GlobalTheory.SchwartzTranslateSum
