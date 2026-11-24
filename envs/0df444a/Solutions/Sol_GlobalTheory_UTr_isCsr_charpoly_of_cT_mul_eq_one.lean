-- Prove2me | solution 1 for GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:01.213823+00:00
-- url     : https://prove2.me/submissions/3df692b2-526f-45b9-8859-6421c0d0aed7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjugateSelfReciprocalCharpoly
import Theorems.Thm_GlobalTheory_UTr_IsCyc_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.UTr
namespace GlobalTheory.UTr
theorem _root_.solution : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  intro R _ s n M hM
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  set N := cT s M with hNdef
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdegN : N.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmap : M.charpoly.map s = N.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose]; rfl
  have hrev : (M.charpoly.map s).reflect n = N.charpolyRev := by
    rw [hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]
  have hdetN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hM, Matrix.det_one]
  have hNd : N.det = s M.det := by
    rw [hNdef, cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det := by
    rw [h0, map_mul, map_pow, map_neg, map_one, hNd]
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [hdeg, hrev, Matrix.charpolyRev, hs0]
  have hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hM, Matrix.map_one _ (map_zero C) (map_one C),
      charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]; rfl
  have e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]; rfl
  have e2 : C N.det * C M.det = (1 : R[X]) := by rw [← C_mul, hdetN, C_1]
  rw [C_mul, C_pow, C_neg, C_1]
  linear_combination (-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2
end GlobalTheory.UTr
