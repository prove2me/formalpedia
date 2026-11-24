-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:53.440806+00:00
-- url     : https://prove2.me/submissions/72625764-91d1-4f6d-8576-f66b7932b520

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_eq_mul_of_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution : MulF → PairF := by
  intro hM
  unfold PairF
  intro K ι κ _ _ _ _ _ U W
  classical
  have hsz0 : ∀ {a b : Type} (g : Matrix a b K), 0 ≤ sz g := by
    intro a b g
    unfold sz
    exact Real.iSup_nonneg (fun p => norm_nonneg _)
  have hnF0 : ∀ (X : Matrix ι κ K), 0 ≤ nF X := by
    intro X
    unfold nF
    exact Real.iSup_nonneg (fun s => norm_nonneg _)
  have hdetT : (Uᵀ * W).det = (Wᵀ * U).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  by_cases h : ∃ s : κ → ι, (U.submatrix s id).det ≠ 0
  · haveI : Nonempty (κ → ι) := ⟨h.choose⟩
    obtain ⟨s₀, hs₀⟩ := Finite.exists_max (fun s : κ → ι => ‖(U.submatrix s id).det‖)
    have hd : (U.submatrix s₀ id).det ≠ 0 := by
      obtain ⟨s, hs⟩ := h
      intro h0
      have h1 := hs₀ s
      simp only [h0, norm_zero] at h1
      exact hs (norm_le_zero_iff.mp h1)
    have hnU : nF U = ‖(U.submatrix s₀ id).det‖ := by
      unfold nF
      apply le_antisymm
      · exact ciSup_le hs₀
      · exact le_ciSup (f := fun s : κ → ι => ‖(U.submatrix s id).det‖)
          (Set.finite_range _).bddAbove s₀
    set G : Matrix ι κ K := Matrix.of fun i k => (U.submatrix s₀ id).det⁻¹ *
      (U.submatrix (Function.update s₀ k i) id).det with hG
    have hUG : U = G * U.submatrix s₀ id := eq_mul_of_det_ne_zero U s₀ hd
    have hszG : sz Gᵀ ≤ 1 := by
      unfold sz
      apply Real.iSup_le ?_ zero_le_one
      intro p
      simp only [Matrix.transpose_apply, hG, Matrix.of_apply, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hd), mul_one]
      exact hs₀ _
    have hmain : ‖(Gᵀ * W).det‖ ≤ nF W := by
      have h1 := (hM K ι κ κ W).1 Gᵀ
      have h2 := (hM K ι κ κ W).2.2 (Gᵀ * W)
      rw [h2] at h1
      calc ‖(Gᵀ * W).det‖ ≤ sz Gᵀ ^ Fintype.card κ * nF W := h1
        _ ≤ 1 * nF W := by
          apply mul_le_mul_of_nonneg_right _ (hnF0 W)
          exact pow_le_one₀ (hsz0 _) hszG
        _ = nF W := one_mul _
    have hfac : (Uᵀ * W).det = (U.submatrix s₀ id).det * (Gᵀ * W).det := by
      conv_lhs => rw [hUG]
      rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.det_mul, Matrix.det_transpose]
    rw [hfac, norm_mul, hnU]
    exact mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
  · simp only [not_exists, not_not] at h
    have hnU : nF U = 0 := by
      unfold nF
      simp only [h, norm_zero]
      first
        | exact Real.iSup_const_zero
        | simp
    have h1 := (hM K ι κ κ U).1 Wᵀ
    have h2 := (hM K ι κ κ U).2.2 (Wᵀ * U)
    rw [h2, hnU, mul_zero] at h1
    rw [hdetT, hnU, zero_mul]
    exact h1
end GlobalTheory.CompanionTheory.Wedge
