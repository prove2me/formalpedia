-- Prove2me | solution 1 for GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:54.112469+00:00
-- url     : https://prove2.me/submissions/8be2a82e-e09b-4649-b714-48642c377b56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZero
import Theorems.Thm_GlobalTheory_PrinTwo_bchar_one
import Theorems.Thm_GlobalTheory_PrinTwo_coordL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_evL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_ev_bor
import Theorems.Thm_GlobalTheory_PrinTwo_ext_ev
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.bchar_one
attribute [local simp] GlobalTheory.PrinTwo.coordL_apply
attribute [local simp] GlobalTheory.PrinTwo.evL_apply
attribute [local simp] GlobalTheory.PrinTwo.val_bor
attribute [local simp] GlobalTheory.PrinTwo.val_nL
attribute [local simp] GlobalTheory.PrinTwo.val_nU
attribute [local simp] GlobalTheory.PrinTwo.val_tD
attribute [local simp] GlobalTheory.PrinTwo.val_wE



set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PrinTwo
namespace GlobalTheory.PrinTwo
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) (h1 : ev f 1 = 0)
    (hc : ∀ x : k, coord f x = 0) : f = 0 := by
  apply ext_ev
  intro g
  have hz : ev (0 : PSp μ₁ μ₂) g = 0 := by
    have := ev_smul (0 : ℂ) (0 : PSp μ₁ μ₂) g
    simpa using this
  rw [hz]
  have hdet : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hr : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 = 0
  · rw [hr, mul_zero, sub_zero] at hdet
    have hp : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hs : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hg : g = bor (Units.mk0 _ hp) (Units.mk0 _ hs) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1) * 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hr]
    rw [hg, ev_bor, h1, mul_zero]
  · set D := (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 -
      (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 with hD
    have hA : -D / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 hdet) hr
    have hg : g = bor (Units.mk0 _ hA) (Units.mk0 _ hr) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0) *
        (wE * nU ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hD] <;> field_simp <;> ring
    rw [hg, ev_bor]
    have := hc ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)
    rw [coord] at this
    rw [this, mul_zero]
end GlobalTheory.PrinTwo
