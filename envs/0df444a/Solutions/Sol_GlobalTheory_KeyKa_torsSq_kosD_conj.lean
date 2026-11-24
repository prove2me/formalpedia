-- Prove2me | solution 1 for GlobalTheory.KeyKa.torsSq_kosD_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:16.556622+00:00
-- url     : https://prove2.me/submissions/df507527-98e7-440b-a9ca-b709134fe32b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_one
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_graded
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_det_sub
import Theorems.Thm_GlobalTheory_KeyKa_kosBlock_mul_kosD
import Theorems.Thm_GlobalTheory_KeyKa_torsSq_conj


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (g d : ℕ) (N : ℕ → ℕ) (m m' : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R) (B : ∀ j, (Matrix (Fin (N j)) (Fin (N j)) R)ˣ) (Pm : (Matrix (Fin d) (Fin d) R)ˣ) (t : Rˣ), (∀ i j, j < g → (B j).val * m' i j (j + 1) = m i j (j + 1) * (B (j + 1)).val) → Pm.val * ev' 0 = ev 0 * (B 0).val → IsCx kdeg (kosD m ev) → TorsSq kdeg (kosD m ev) (t : R) → ∃ t' : Rˣ, TorsSq kdeg (kosD m' ev') (t' : R) ∧ t' * (Matrix.GeneralLinearGroup.det Pm) ^ 2 = t * ∏ j ∈ Finset.range (g + 1), (Matrix.GeneralLinearGroup.det (B j)) ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)) := by
  intro R _ g d N m m' ev ev' B Pm t hm he hC hT
  set G : Matrix (KIx g d N) (KIx g d N) R := kosBlock (fun j => (B j).val) Pm.val with hG
  set G' : Matrix (KIx g d N) (KIx g d N) R := kosBlock (fun j => ((B j)⁻¹).val) (Pm⁻¹).val with hG'
  have hGG : G * G' = 1 := by
    rw [hG, hG', kosBlock_mul]; simp only [Units.mul_inv]; exact kosBlock_one
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  have hD : G' * kosD m ev * G = kosD m' ev' := by
    rw [Matrix.mul_assoc, ← kosBlock_mul_kosD m m' ev ev' _ _ hm he, ← Matrix.mul_assoc, hGG',
      Matrix.one_mul]
  obtain ⟨t', h1, h2⟩ := torsSq_conj R _ kdeg (kosD m ev) G G' t (kosBlock_graded _ _) hGG hC hT
  rw [hD] at h1
  rw [hG, kosBlock_det_sub _ _ Even, kosBlock_det_sub _ _ (fun n => ¬ Even n)] at h2
  set u : ℕ → Rˣ := fun j => Matrix.GeneralLinearGroup.det (B j) ^ g.choose j with hu
  set E : Rˣ := ∏ j ∈ Finset.range (g + 1), if Even (j + 1) then u j else 1 with hE
  set O : Rˣ := ∏ j ∈ Finset.range (g + 1), if ¬ Even (j + 1) then u j else 1 with hO
  set p : Rˣ := Matrix.GeneralLinearGroup.det Pm with hp
  have h3 : t' * ((E * p) ^ 2 : Rˣ) = ((t * O ^ 2 : Rˣ) : R) := by
    simp only [Even.zero, if_true, not_true, if_false, mul_one] at h2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hE, hO, hp, hu, Units.coe_prod,
      apply_ite Units.val, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
    exact h2
  have h4 : ((t * O ^ 2 * ((E * p) ^ 2)⁻¹ : Rˣ) : R) = t' := by
    rw [Units.val_mul, ← h3, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨t * O ^ 2 * ((E * p) ^ 2)⁻¹, h4 ▸ h1, ?_⟩
  have h5 : ∏ j ∈ Finset.range (g + 1),
      (Matrix.GeneralLinearGroup.det (B j)) ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)) =
      O ^ 2 * (E ^ 2)⁻¹ := by
    rw [hE, hO, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rcases Nat.even_or_odd j with hj | hj
    · have : ¬ Even (j + 1) := by rw [Nat.even_add_one]; simpa using hj
      rw [if_pos this, if_neg this, hj.neg_one_pow, one_pow, inv_one, mul_one, mul_one, hu,
        ← pow_mul, ← zpow_natCast]
      congr 1; push_cast; ring
    · have : Even (j + 1) := hj.add_one
      rw [if_pos this, if_neg (not_not.mpr this), hj.neg_one_pow, one_pow, one_mul, hu,
        ← pow_mul, ← zpow_natCast, ← zpow_neg]
      congr 1; push_cast; ring
  rw [h5, mul_pow, mul_inv, ← mul_assoc, mul_assoc _ (p ^ 2)⁻¹, inv_mul_cancel, mul_one, mul_assoc]
end GlobalTheory.KeyKa
