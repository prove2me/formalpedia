-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsLowerUni.eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:23.286336+00:00
-- url     : https://prove2.me/submissions/8f3ed7cf-abd2-4f95-987b-332fc264bdbb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace IsLowerUni
theorem _root_.solution {L U : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (hU : U.BlockTriangular id)
    (h' : IsLowerUni (L * U)) : U = 1 := by
  have hd : IsUnit L.det := by rw [h.det]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet L hd
  have h1 : L.BlockTriangular OrderDual.toDual := fun a b e => h.2 _ _ e
  have h2 : (L * U).BlockTriangular OrderDual.toDual := fun a b e => h'.2 _ _ e
  have h3 : U.BlockTriangular OrderDual.toDual := by
    have := (blockTriangular_inv_of_blockTriangular h1).mul h2
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  have h4 : ∀ a b, a ≠ b → U a b = 0 := fun a b e => by
    rcases lt_or_gt_of_ne e with e | e
    · exact h3 e
    · exact hU e
  ext a b
  by_cases e : a = b
  · subst e
    have := h'.1 a
    rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [h4 c a hc, mul_zero]) (by simp), h.1,
      one_mul] at this
    rw [this, Matrix.one_apply_eq]
  · rw [h4 a b e, Matrix.one_apply_ne e]
end IsLowerUni
end GlobalTheory.CompanionTheory.Ar.PB
