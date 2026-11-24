-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.Eqv.unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:21.174231+00:00
-- url     : https://prove2.me/submissions/3e9d1b19-ba60-4638-b957-81e7b7e5a6fc

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_det_blk
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_blk_comm
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
variable {k : Type} [Field k] {n d : ℕ}
variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
namespace GlobalTheory.ThK.Dbl.LD
namespace Eqv
theorem _root_.solution {c : k → ℂ} (hc : ∀ a ≠ 0, c a ≠ 0) {ϖ : k} (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {m : Type}
    {l : (Matrix m (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} [Fintype m] (hl : Eqv c l) (b : Fin d → k) :
    ∀ φ ∈ SB _, l (fun y => φ (y * blk 1 b 1)) = l φ := by
  have hu : ∀ b : Fin d → k, (blk 1 b 1).det ≠ 0 := fun b => by simp [det_blk]
  have hD : (blk ϖ (0 : Fin d → k) 1).det ≠ 0 := by simp [det_blk, h0]
  obtain ⟨t₁, -, e₁⟩ := hl _ (hu b)
  obtain ⟨t₂, p₂, e₂⟩ := hl _ (hu ((ϖ - 1)⁻¹ • b))
  obtain ⟨t₃, p₃, e₃⟩ := hl _ hD
  intro φ hφ
  have a := e₃ _ (sb_right hφ (hu ((ϖ - 1)⁻¹ • b)))
  have a' := e₁ _ (sb_right (sb_right hφ hD) (hu ((ϖ - 1)⁻¹ • b)))
  simp only [Matrix.mul_assoc] at a a'
  rw [blk_comm ϖ b _ (by rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.2 h1), one_smul]), a', e₂ _ hφ] at a
  have a2 := e₂ _ (sb_right hφ hD)
  simp only [Matrix.mul_assoc] at a2
  rw [a2, e₃ _ hφ] at a
  rw [e₁ _ hφ]
  have n2 : c (blk 1 ((ϖ - 1)⁻¹ • b) 1).det * t₂ ≠ 0 := mul_ne_zero (hc _ (hu _)) (by exact_mod_cast p₂.ne')
  have n3 : c (blk ϖ (0 : Fin d → k) 1).det * t₃ ≠ 0 := mul_ne_zero (hc _ hD) (by exact_mod_cast p₃.ne')
  apply mul_left_cancel₀ (mul_ne_zero n2 n3)
  linear_combination a
end Eqv
end GlobalTheory.ThK.Dbl.LD
