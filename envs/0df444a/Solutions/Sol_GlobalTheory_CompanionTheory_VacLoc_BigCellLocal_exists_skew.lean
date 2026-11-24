-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.exists_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:27.728384+00:00
-- url     : https://prove2.me/submissions/934429f2-2fde-44dd-b4d9-6c5e235478e8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Iso_isUnit_det
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Wm_det
import Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_iso_col
import Theorems.Thm_GlobalTheory_CompanionTheory_CommonTransversal_exists_skew_isUnit_det


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
    {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    ∃ s : Matrix β β A, s.map σ = -sᵀ ∧ IsUnit (a + s * c).det := by
  haveI : IsLocalHom σ := ⟨fun x hx => by simpa [hσ] using hx.map σ⟩
  set π := IsLocalRing.residue A with hπ
  set τ := IsLocalRing.ResidueField.map σ with hτ
  have hc : ∀ x, τ (π x) = π (σ x) := fun x => IsLocalRing.ResidueField.map_residue σ x
  have hm : ∀ m : Matrix β β A, (m.map π).map τ = (m.map σ).map π := fun m => by
    ext i j; simp [hc]
  have hdet := (h.isUnit_det Wm_det).map π
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map] at hdet
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.CommonTransversal.exists_skew_isUnit_det τ (a.map π)ᵀ (c.map π)ᵀ
    (fun x => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rw [← hπ, hc, hc, hσ])
    ⟨π z, fun e => by
      have := hz.map π
      rw [map_sub, ← hc, e, sub_self] at this
      exact not_isUnit_zero this⟩
    (by
      have := congrArg (fun m => m.map π) (iso_col h)
      simp only [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_zero _ (map_zero π)] at this
      rw [transpose_map, transpose_map, transpose_transpose, transpose_transpose, hm, hm, add_comm]
      exact this)
    (fun v h1 h2 => by
      rw [vecMul_transpose] at h1 h2
      have h3 : fromBlocks (a.map π) (b.map π) (c.map π) (d.map π) *ᵥ Sum.elim v 0 = 0 := by
        rw [fromBlocks_mulVec]
        simp [h1, h2]
      have h4 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero h3
      ext i
      exact congrFun h4 (Sum.inl i))
  choose f hf using (IsLocalRing.residue_surjective (R := A))
  refine ⟨Matrix.of fun i j => w * f (s j i) - σ (w * f (s i j)), ?_, ?_⟩
  · ext i j
    simp [hσ]
  · have e : (Matrix.of fun i j => w * f (s j i) - σ (w * f (s i j))).map π = sᵀ := by
      ext i j
      have h5 : τ (s i j) = - s j i := congrFun (congrFun hs1 j) i
      have h6 : π w + τ (π w) = 1 := by rw [hc, ← map_add, hw, map_one]
      have hf' : ∀ x, π (f x) = x := hf
      simp only [map_apply, of_apply, map_sub, ← hc, map_mul, hf', h5, transpose_apply]
      linear_combination s j i * h6
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_add _ (map_add π), Matrix.map_mul, e, ← det_transpose, transpose_add, transpose_mul, transpose_transpose]
    exact hs2.ne_zero
end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
