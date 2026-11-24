-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.eq_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:58.646841+00:00
-- url     : https://prove2.me/submissions/25be0231-2d4a-4cc7-aa02-a43343419a05

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_val
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_top_cell
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_vanish
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_left

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
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t)
    (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) (g : GL (Fin d) k) :
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by
  let P : Matrix (Fin d) (Fin d) k → Prop := fun M => ∀ g : GL (Fin d) k, g.1 = M →
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ
  have sym : ∀ M, Mᵀ = M → P M := by
    rintro _ hg g rfl φ hφ
    refine sub_eq_zero.1 (vanish ξ ϖ hξ (l ∘ₗ LinearMap.funLeft ℂ ℂ (g.1 * ·) - (ξ (GeneralLinearGroup.det g) : ℂ) • l)
      (fun ψ hψ h => ?_) (fun ψ hψ h0 => sub_eq_zero.2 (top_cell ξ l hl hg hψ fun X hX => h0 X ?_)) φ hφ)
    · have a := hl _ (sb_left hψ g) h
      simp only [← Matrix.mul_assoc] at a
      show (l fun y => ψ (g.1 * y * h.1)) - _ * (l fun y => ψ (y * h.1)) = _ * ((l fun y => ψ (g.1 * y)) - _ * l ψ)
      rw [a, hl ψ hψ h]; ring
    · exact exists_mulVec_eq_zero_iff.2 hX
  have mul : ∀ A B : Matrix (Fin d) (Fin d) k, A.det ≠ 0 → B.det ≠ 0 → P A → P B → P (A * B) := by
    intro A B hA hB pA pB g hg φ hφ
    have e : g = toGL A * toGL B := Units.ext (by rw [hg, Units.val_mul, toGL_val hA, toGL_val hB])
    have a := pB _ (toGL_val hB) _ (sb_left hφ (toGL A))
    rw [pA _ (toGL_val hA) _ hφ] at a
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [a]; ring
  refine diagonal_transvection_induction_of_det_ne_zero P g.1 g.det_ne_zero (fun D _ => sym _ (diagonal_transpose D))
    (fun t => ?_) mul g rfl
  have hs : (swap k t.i t.j).det ≠ 0 := (isUnit_det_of_left_inverse (swap_mul_self _ _)).ne_zero
  have := mul _ (swap k t.i t.j * t.toMatrix) hs (by rw [det_mul, t.det, mul_one]; exact hs) (sym _ (transpose_swap _ _))
    (sym _ ?_)
  · rwa [← Matrix.mul_assoc, swap_mul_self, Matrix.one_mul] at this
  have e : swap k t.i t.j * single t.i t.j t.c = single t.j t.j t.c := by
    ext a b
    by_cases h1 : a = t.i
    · rw [h1, swap_mul_apply_left]; simp [single_apply, t.hij, t.hij.symm]
    by_cases h2 : a = t.j
    · rw [h2, swap_mul_apply_right]; simp [single_apply]
    · rw [swap_mul_of_ne h1 h2]; simp [single_apply, Ne.symm h1, Ne.symm h2]
  rw [TransvectionStruct.toMatrix, transvection, Matrix.mul_add, Matrix.mul_one, e, transpose_add, transpose_swap,
    transpose_single]
end GlobalTheory.ThK.Dbl.LD
