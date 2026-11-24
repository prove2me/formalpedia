-- Prove2me | solution 1 for GlobalTheory.RealZeros.LFunction_chi8_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:04.090403+00:00
-- url     : https://prove2.me/submissions/b568e562-111c-4c5f-8b18-dac65ce047b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_summable_br
import Theorems.Thm_GlobalTheory_RealZeros_differentiableOn_tsum_br
import Theorems.Thm_GlobalTheory_RealZeros_br_ofReal
import Theorems.Thm_GlobalTheory_RealZeros_convex_re_pos
import Theorems.Thm_GlobalTheory_RealZeros_strictAntiOn_diff
import Theorems.Thm_GlobalTheory_RealZeros_LFunction_eq_of_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution (χ : DirichletCharacter ℂ 8)
    (hχ : ∀ a : ZMod 8, χ a = ((ZMod.χ₈ a : ℤ) : ℂ)) (σ : ℝ) (h0 : 0 < σ) :
    DirichletCharacter.LFunction χ σ ≠ 0 := by
  have hne : χ ≠ 1 := by
    intro h
    have h3 := hχ 3
    have hu : IsUnit (3 : ZMod 8) := by decide
    have e3 : ZMod.χ₈ (3 : ZMod 8) = -1 := by decide
    rw [h, MulChar.one_apply hu, e3] at h3
    norm_num at h3
  have ho : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hne).differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ (fun s => ∑' k, br 8 1 3 k s - ∑' k, br 8 5 7 k s) {s | 0 < s.re} :=
    ((differentiableOn_tsum_br (by norm_num) le_rfl (by norm_num)).sub
      (differentiableOn_tsum_br (by norm_num) (by norm_num) (by norm_num))).analyticOnNhd ho
  have hA := hF.eqOn_of_preconnected_of_eventuallyEq hG convex_re_pos.isPreconnected
    (z₀ := 2) (by simp)
    (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz using LFunction_eq_of_one_lt χ hχ hz)
  have hs0 : 0 < (σ : ℂ).re := by simpa using h0
  have key : DirichletCharacter.LFunction χ σ = ∑' k, br 8 1 3 k σ - ∑' k, br 8 5 7 k σ := hA hs0
  have s1 := summable_br (N := 8) (c := 1) (d := 3) (by norm_num) le_rfl (by norm_num) hs0
  have s2 := summable_br (N := 8) (c := 5) (d := 7) (by norm_num) (by norm_num) (by norm_num) hs0
  simp only [br_ofReal] at key s1 s2
  rw [summable_ofReal] at s1 s2
  rw [← ofReal_tsum, ← ofReal_tsum, ← ofReal_sub] at key
  rw [key, ofReal_ne_zero]
  have hlt : ∀ k : ℕ, ((8 * k + 5 : ℕ) : ℝ) ^ (-σ) - ((8 * k + 7 : ℕ) : ℝ) ^ (-σ) <
      ((8 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((8 * k + 3 : ℕ) : ℝ) ^ (-σ) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := strictAntiOn_diff h0 (a := 8 * k + 1) (b := 8 * k + 5)
      (by rw [Set.mem_Ioi]; linarith) (by rw [Set.mem_Ioi]; linarith) (by linarith)
    simp only at this
    push_cast
    rw [show (8 * k + 7 : ℝ) = 8 * k + 5 + 2 by ring, show (8 * k + 3 : ℝ) = 8 * k + 1 + 2 by ring]
    exact this
  exact (sub_pos.mpr (s2.tsum_lt_tsum (i := 0) (fun k => (hlt k).le) (hlt 0) s1)).ne'
end GlobalTheory.RealZeros
