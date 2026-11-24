-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.step_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:10.25385+00:00
-- url     : https://prove2.me/submissions/3f3a4068-eddd-4880-bf64-e97a7e953ef4

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_nonarch_mat
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_kill_loc
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (hc : ∀ a ≠ 0, c a ≠ 0) {n d : ℕ} {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hz : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0 := by
  have := nonarch_mat (k := k) (n + 1) (d + 1)
  intro φ hφ h0
  refine kill_loc l hφ fun x hx => ?_
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (fun h => hx (h0 x h) : x 0 ≠ 0)
  refine ⟨{X | X 0 j ≠ 0}, (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds hj, fun ψ hψ hψ0 => ?_⟩
  have hh : (swap k 0 j).det ≠ 0 := (isUnit_det_of_left_inverse (swap_mul_self 0 j)).ne_zero
  obtain ⟨t, pt, ht⟩ := hl _ hh
  have a := ht ψ hψ
  rw [hz _ (sb_right hψ hh) fun X hX => hψ0 _ (by simpa [mul_swap_apply_right] using hX)] at a
  exact (mul_eq_zero.1 a.symm).resolve_left (mul_ne_zero (hc _ hh) (by exact_mod_cast pt.ne'))
end GlobalTheory.ThK.Dbl.LD
