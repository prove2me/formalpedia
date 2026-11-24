-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.top_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:11.130576+00:00
-- url     : https://prove2.me/submissions/c066e313-0bfe-4bad-adbf-67f6b604aee3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_cont_invT
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_val
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_coe
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_cont_toGL
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_left_of_right
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_chart


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
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    {g : GL (Fin d) k} (hg : g.1ᵀ = g.1) {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X.det = 0 → φ X = 0) :
    l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by
  classical
  have hU : IsOpen {X : Matrix (Fin d) (Fin d) k | X.det ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  let m : (GL (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => if X.det ≠ 0 then ψ (toGL X) else 0
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; by_cases h : z.det = 0 <;> simp [h]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; by_cases h : z.det = 0 <;> simp [h] }
  have hm : ∀ ψ, m ψ = l fun X => if X.det ≠ 0 then ψ (toGL X) else 0 := fun _ => rfl
  have a := left_of_right ((Units.coeHom ℂ).comp (ξ.comp GeneralLinearGroup.det)) invT cont_invT
    (fun x => Units.ext (transpose_transpose _)) (g := g)
    (inv_injective (Units.ext hg)) m (fun ψ hψ h => ?_) (φ := fun x => φ x.1)
    (sb_chart (U := Set.univ) (T := {X : Matrix (Fin d) (Fin d) k | X.det ≠ 0}) isOpen_univ Units.continuous_val.continuousOn cont_toGL
      (fun x _ => toGL_coe x) (fun _ _ => trivial) hφ (fun X hX => h0 X (not_not.1 hX)) (fun _ _ => rfl)
      fun _ h => absurd trivial h)
  · rw [hm, hm] at a
    convert a using 3 with X
    · split_ifs with h
      · rw [Units.val_mul, toGL_val h]
      · exact h0 _ (by rw [det_mul, not_not.1 h, mul_zero])
    · rfl
    · ext X
      split_ifs with h
      · rw [toGL_val h]
      · exact h0 _ (not_not.1 h)
  · rw [hm, hm]
    refine Eq.trans ?_ (hl (fun X => if X.det ≠ 0 then ψ (toGL X) else 0) (sb_chart (T := Set.univ) hU cont_toGL Units.continuous_val.continuousOn (fun X hX => toGL_val hX)
      (fun x _ => x.det_ne_zero) hψ (fun _ h => absurd trivial h) (fun X hX => if_pos hX) fun X hX => if_neg hX) h)
    congr 1; ext X
    by_cases hX : X.det = 0
    · simp [hX]
    · have : (X * h.1).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hX h.det_ne_zero
      rw [if_pos hX, if_pos this]
      congr 1; apply Units.ext
      rw [Units.val_mul, toGL_val hX, toGL_val this]
end GlobalTheory.ThK.Dbl.LD
