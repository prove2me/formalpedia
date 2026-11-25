-- Prove2me | solution 1 for GlobalTheory.DiagBlock.rowDeg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:32.440801+00:00
-- url     : https://prove2.me/submissions/6332d977-f41b-4a7b-b471-d947192440ae

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_det_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {C : Type} [Field C] {n : ℕ} (a b : ℕ) (m : PVar n →₀ ℕ)
    (hm : MvPolynomial.coeff m (detL C n ^ a * detR C n ^ b) ≠ 0) (ρ : Fin n) :
    rowDegZ m ρ = a ∧ rowDegZ' m ρ = b := by
  classical
  let wL : PVar n → ℕ := Sum.elim (fun p => if p.1 = ρ then 1 else 0) (fun _ => 0)
  let wR : PVar n → ℕ := Sum.elim (fun _ => 0) (fun p => if p.1 = ρ then 1 else 0)
  have hLL : (detL C n).IsWeightedHomogeneous wL 1 := by
    have := det_homog (C := C) wL (fun b c => Sum.inl (b, c)) (fun b => if b = ρ then 1 else 0)
      (fun b c => rfl)
    simpa [detL] using this
  have hRL : (detR C n).IsWeightedHomogeneous wL 0 := by
    have := det_homog (C := C) wL (fun b c => Sum.inr (b, c)) (fun _ => 0) (fun b c => rfl)
    simpa [detR] using this
  have hLR : (detL C n).IsWeightedHomogeneous wR 0 := by
    have := det_homog (C := C) wR (fun b c => Sum.inl (b, c)) (fun _ => 0) (fun b c => rfl)
    simpa [detL] using this
  have hRR : (detR C n).IsWeightedHomogeneous wR 1 := by
    have := det_homog (C := C) wR (fun b c => Sum.inr (b, c)) (fun b => if b = ρ then 1 else 0)
      (fun b c => rfl)
    simpa [detR] using this
  have h1 := ((hLL.pow a).mul (hRL.pow b)) hm
  have h2 := ((hLR.pow a).mul (hRR.pow b)) hm
  have hwL : Finsupp.weight wL m = rowDegZ m ρ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [rowDegZ, Fintype.sum_sum_type, Fintype.sum_prod_type, wL]
    rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ ρ) h)]
    simp
  have hwR : Finsupp.weight wR m = rowDegZ' m ρ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [rowDegZ', Fintype.sum_sum_type, Fintype.sum_prod_type, wR]
    rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ ρ) h)]
    simp
  rw [hwL] at h1
  rw [hwR] at h2
  simp at h1 h2
  exact ⟨h1, h2⟩
end GlobalTheory.DiagBlock
