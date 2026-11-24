-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.decomp_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:29.78885+00:00
-- url     : https://prove2.me/submissions/901fd44b-8fb6-4996-b749-345ab5b3c3b9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Iso_mul
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_map_one__0ae7550c3513
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_iso_Wm
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_iso_n
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_iso_col
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_exists_skew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
theorem _root_.solution [IsLocalRing A] (hσ : ∀ z, σ (σ z) = z) {w : A} (hw : w + σ w = 1) {z : A} (hz : IsUnit (z - σ z))
    {h : Matrix (β ⊕ β) (β ⊕ β) A} (hh : Iso σ (Wm A β) (Wm A β) h) :
    ∃ s u t b d : Matrix β β A, Iso σ (Wm A β) (Wm A β) (fromBlocks 1 s 0 1) ∧
      Iso σ (Wm A β) (Wm A β) (fromBlocks 1 u 0 1) ∧ Iso σ (Wm A β) (Wm A β) (fromBlocks t b 0 d) ∧ IsUnit t.det ∧
      h = fromBlocks 1 s 0 1 * (Wm A β * fromBlocks 1 u 0 1 * Wm A β) * fromBlocks t b 0 d := by
  rw [← fromBlocks_toBlocks h] at hh ⊢
  generalize h.toBlocks₁₁ = a at *
  generalize h.toBlocks₁₂ = b at *
  generalize h.toBlocks₂₁ = c at *
  generalize h.toBlocks₂₂ = d at *
  obtain ⟨s, hs, ha⟩ := exists_skew hσ hw hz hh
  have h1 := (iso_n hs).mul hh
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add] at h1
  set a' := a + s * c with ha'
  have h2 := iso_col h1
  have i1 : a' * a'⁻¹ = 1 := mul_nonsing_inv _ ha
  have i2 : a'⁻¹ * a' = 1 := nonsing_inv_mul _ ha
  have i3 : a'.map σ * a'⁻¹.map σ = 1 := by rw [← Matrix.map_mul, i1, map_one']
  have i4 : a'⁻¹ᵀ * a'ᵀ = 1 := by rw [← transpose_mul, i1, transpose_one]
  have hu : (c * a'⁻¹).map σ = -(c * a'⁻¹)ᵀ := by
    have := congrArg (fun m => a'⁻¹ᵀ * m * a'⁻¹.map σ) h2
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, i4, Matrix.mul_assoc _ (a'.map σ), i3] at this
    rw [Matrix.map_mul, transpose_mul, eq_neg_iff_add_eq_zero, add_comm]
    simpa using this
  have hs' : (-s).map σ = -(-s)ᵀ := by rw [Matrix.map_neg _ (map_neg σ), hs, transpose_neg]
  have hu' : (-(c * a'⁻¹)).map σ = -(-(c * a'⁻¹))ᵀ := by rw [Matrix.map_neg _ (map_neg σ), hu, transpose_neg]
  have h3 := ((iso_Wm.mul (iso_n hu')).mul iso_Wm).mul h1
  have e3 : Wm A β * fromBlocks 1 (-(c * a'⁻¹)) 0 1 * Wm A β * fromBlocks a' (b + s * d) c d =
      fromBlocks a' (b + s * d) 0 (d - c * a'⁻¹ * (b + s * d)) := by
    simp [Wm, fromBlocks_multiply, Matrix.mul_assoc, i2, sub_eq_neg_add]
  rw [e3] at h3
  refine ⟨-s, c * a'⁻¹, a', _, _, iso_n hs', iso_n hu, h3, ha, ?_⟩
  rw [Matrix.mul_assoc]
  have e4 : Wm A β * fromBlocks 1 (c * a'⁻¹) 0 1 * Wm A β * fromBlocks a' (b + s * d) 0 (d - c * a'⁻¹ * (b + s * d)) =
      fromBlocks a' (b + s * d) c d := by
    simp [Wm, fromBlocks_multiply, Matrix.mul_assoc, i2]
  rw [e4]
  simp [fromBlocks_multiply, ha']
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
