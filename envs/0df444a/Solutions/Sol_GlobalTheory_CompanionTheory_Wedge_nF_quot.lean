-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:04:40.783038+00:00
-- url     : https://prove2.me/submissions/6e268d44-9114-4fbc-9265-916aaf284e90

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_minor_le_nF
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_exists_minor_eq_nF
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_mul_le
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_sel_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_entry_eq_minor
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_fromCols_of_id
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_ne_zero_iff

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
    [DecidableEq κ] (B : Matrix ι κ K) (hB : LinearIndependent K Bᵀ) :
    ∃ Y : Matrix κ ι K, ∀ (κ' : Type) [Fintype κ'] [DecidableEq κ'] (C : Matrix ι κ' K),
      nF (fromCols B C) = nF B * nF ((1 - B * Y) * C) ∧ nF ((1 - B * Y) * C) ≤ nF C ∧
        (1 - B * Y) * B = 0 := by
  have hne := (nF_ne_zero_iff hM B).2 hB
  obtain ⟨s, hs⟩ := exists_minor_eq_nF B hne
  set Bs := B.submatrix s id with hBs
  have hdet : Bs.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    exact hne hs.symm
  have hu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hdet
  set E := (1 : Matrix ι ι K).submatrix s id with hE
  have hEint : ∀ i j, ‖E i j‖ ≤ 1 := fun i j => int_one _ _
  have hEB : E * B = Bs := by rw [hE, sel_mul]
  set B0 := B * Bs⁻¹ with hB0
  have hB0s : B0.submatrix s id = 1 := by
    have : B0.submatrix s id = Bs * Bs⁻¹ := by
      rw [← sel_mul, hB0, ← Matrix.mul_assoc, ← hE, hEB]
    rw [this, mul_nonsing_inv _ hu]
  have hEB0 : E * B0 = 1 := by rw [hE, sel_mul, hB0s]
  have hnB0 : nF B0 = 1 := by
    have h1 : ‖Bs.det‖ * ‖(Bs⁻¹).det‖ = 1 := by
      rw [← norm_mul, ← det_mul, mul_nonsing_inv _ hu, det_one, norm_one]
    rw [hB0, (hM K ι ι κ B).2.1, ← hs, h1]
  have hB0int : ∀ i j, ‖B0 i j‖ ≤ 1 := by
    intro i k
    rw [entry_eq_minor B0 s hB0s i k, ← hnB0]
    exact minor_le_nF B0 _
  have hBs1 : B0 * Bs = B := by
    rw [hB0, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨Bs⁻¹ * E, fun κ' _ _ C => ?_⟩
  have hBY : B * (Bs⁻¹ * E) = B0 * E := by rw [hB0, Matrix.mul_assoc]
  rw [hBY]
  set P := 1 - B0 * E with hP
  have hPint : ∀ i j, ‖P i j‖ ≤ 1 := int_sub int_one (int_mul hB0int hEint)
  have hEP : E * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hEB0, Matrix.one_mul, sub_self]
  have hPC : (P * C).submatrix s id = 0 := by
    rw [← sel_mul, ← hE, ← Matrix.mul_assoc, hEP, Matrix.zero_mul]
  have hfact : fromCols B C = fromCols B0 (P * C) *
      (fromBlocks Bs (E * C) 0 1 : Matrix (κ ⊕ κ') (κ ⊕ κ') K) := by
    rw [fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, Matrix.mul_one, hBs1,
      ← Matrix.mul_assoc, hP, Matrix.sub_mul, Matrix.one_mul]
    simp
  refine ⟨?_, nF_mul_le hM _ _ hPint, ?_⟩
  · rw [hfact, (hM K ι ι (κ ⊕ κ') _).2.1, det_fromBlocks_zero₂₁, det_one, mul_one, hs,
      nF_fromCols_of_id hM B0 (P * C) s hB0s hB0int hPC, mul_comm]
  · rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hEB, hBs1, sub_self]
end GlobalTheory.CompanionTheory.Wedge
