-- Prove2me | solution 1 for GlobalTheory.KeyKa.torsSq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:15.851623+00:00
-- url     : https://prove2.me/submissions/7a55879f-c957-428b-847f-08ad0db2a331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Theorems.Thm_GlobalTheory_KeyKa_graded_inv
import Theorems.Thm_GlobalTheory_KeyKa_submatrix_mul_of_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (G G' : Matrix Ix Ix R) (t : R), (∀ p q, deg p ≠ deg q → G p q = 0) → G * G' = 1 → IsCx deg D → TorsSq deg D t → ∃ t', TorsSq deg (G' * D * G) t' ∧ t' * (G.submatrix (fun p : {p // Even (deg p)} => p.1) (fun p : {p // Even (deg p)} => p.1)).det ^ 2 = t * (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1) (fun p : {p // ¬ Even (deg p)} => p.1)).det ^ 2 := by
  intro R Ix _ _ _ deg D G G' t hG hGG _ hT
  obtain ⟨h, hh, hDh, e, rfl⟩ := hT
  have hG' := graded_inv deg G G' hG hGG
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  have hev : ∀ (p : {p // Even (deg p)}) r,
      r ∉ Set.range (fun p : {p // Even (deg p)} => p.1) → deg p.1 ≠ deg r := by
    intro p r hr hd
    exact hr ⟨⟨r, hd ▸ p.2⟩, rfl⟩
  have hod : ∀ (p : {p // Even (deg p)}) r,
      r ∉ Set.range (fun p : {p // Even (deg p)} => (e p).1) → deg r ≠ deg (e p).1 := by
    intro p r hr hd
    exact hr ⟨e.symm ⟨r, hd ▸ (e p).2⟩, by simp⟩
  refine ⟨_, ⟨G' * h * G, ?_, ?_, e, rfl⟩, ?_⟩
  · intro p q hpq
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : deg r = deg q
    · rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases hs : deg p = deg s
      · rw [hh s r (by omega)]; simp
      · rw [hG' p s hs]; simp
    · rw [hG r q hr]; simp
  · calc G' * D * G * (G' * h * G) + G' * h * G * (G' * D * G)
        = G' * (D * (G * G') * h + h * (G * G') * D) * G := by noncomm_ring
      _ = 1 := by rw [hGG, Matrix.mul_one, Matrix.mul_one, hDh, Matrix.mul_one, hGG']
  · have e1 : G' * D * G + G' * h * G = G' * (D + h) * G := by noncomm_ring
    have e2 : (G' * (D + h) * G).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1)
        = G'.submatrix (fun p : {p // Even (deg p)} => p.1) (fun p : {p // Even (deg p)} => p.1) *
          (D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) *
          G.submatrix (fun p => (e p).1) (fun p => (e p).1) := by
      rw [submatrix_mul_of_support (G' * (D + h)) G _ _ (fun p => (e p).1)
          (Subtype.val_injective.comp e.injective)
          (fun p q r hr => by rw [hG _ _ (hod q r hr), mul_zero]),
        submatrix_mul_of_support G' (D + h) _ _ (fun p : {p // Even (deg p)} => p.1)
          Subtype.val_injective (fun p q r hr => by rw [hG' _ _ (hev p r hr), zero_mul])]
    have e3 : (G.submatrix (fun p => (e p).1) (fun p => (e p).1)).det =
        (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1)
          (fun p : {p // ¬ Even (deg p)} => p.1)).det := by
      rw [← Matrix.det_submatrix_equiv_self e]; rfl
    have e4 : (G'.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det *
        (G.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det = 1 := by
      rw [← Matrix.det_mul, ← submatrix_mul_of_support G' G _ _ (fun p : {p // Even (deg p)} => p.1)
          Subtype.val_injective (fun p q r hr => by rw [hG' _ _ (hev p r hr), zero_mul]), hGG',
        Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
    rw [e1, e2, Matrix.det_mul, Matrix.det_mul, e3]
    set a := (G'.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det
    set b := (G.submatrix (fun p : {p // Even (deg p)} => p.1)
          (fun p : {p // Even (deg p)} => p.1)).det
    set c := (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1)
          (fun p : {p // ¬ Even (deg p)} => p.1)).det
    set d := ((D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1)).det
    calc (a * d * c) ^ 2 * b ^ 2 = (a * b) ^ 2 * (d ^ 2 * c ^ 2) := by ring
      _ = _ := by rw [e4]; ring
end GlobalTheory.KeyKa
