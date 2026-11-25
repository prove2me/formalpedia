-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_fromCols_of_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:43.002235+00:00
-- url     : https://prove2.me/submissions/952213c0-7bab-4a73-ab10-8b05d6eb665e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_minor_le_nF
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_le_of_minors
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_add
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_mul_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_sel_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_fromCols_sel_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (D : Matrix ι κ K) (C : Matrix ι κ' K)
    (s : κ → ι) (hD : D.submatrix s id = 1) (hint : ∀ i j, ‖D i j‖ ≤ 1)
    (hC : C.submatrix s id = 0) : nF (fromCols D C) = nF C := by
  have hs : Function.Injective s := by
    intro a b hab
    by_contra hne
    have h1 := congrFun (congrFun hD a) a
    have h2 := congrFun (congrFun hD b) a
    simp only [submatrix_apply, id, hab, one_apply_eq] at h1
    rw [submatrix_apply, id, one_apply_ne (Ne.symm hne)] at h2
    exact one_ne_zero (h1.symm.trans h2)
  set E := (1 : Matrix ι ι K).submatrix s id with hE
  have hEE : E * Eᵀ = 1 := by
    rw [hE, sel_mul]
    ext a b
    simp [one_apply, hs.eq_iff, eq_comm]
  have hEC : E * C = 0 := by rw [hE, sel_mul, hC]
  have hEint : ∀ i j, ‖E i j‖ ≤ 1 := fun i j => int_one _ _
  have hEtint : ∀ i j, ‖Eᵀ i j‖ ≤ 1 := fun i j => int_one _ _
  apply le_antisymm
  · have hk : (1 + (D - Eᵀ) * E) * fromCols Eᵀ C = fromCols D C := by
      rw [mul_fromCols]
      congr 1
      · rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hEE, Matrix.mul_one]
        abel
      · rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hEC, Matrix.mul_zero, add_zero]
    rw [← hk]
    exact (nF_mul_le hM _ _ (int_add int_one (int_mul (int_sub hint hEtint) hEint))).trans
      (nF_fromCols_sel_le s C hs hC)
  · refine nF_le_of_minors _ (nF_nonneg' _) fun t => ?_
    have hb : (fromCols D C).submatrix (Sum.elim s t) id =
        fromBlocks 1 0 (D.submatrix t id) (C.submatrix t id) := by
      ext (a | a) (b | b)
      · simpa using congrFun (congrFun hD a) b
      · simpa using congrFun (congrFun hC a) b
      · simp
      · simp
    have := minor_le_nF (fromCols D C) (Sum.elim s t)
    rwa [hb, det_fromBlocks_zero₁₂, det_one, one_mul] at this
end GlobalTheory.CompanionTheory.Wedge
