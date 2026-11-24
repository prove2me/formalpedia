-- Prove2me | solution 1 for GlobalTheory.ClassFin.HermiteReduction.exists_reduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:38:52.615217+00:00
-- url     : https://prove2.me/submissions/eef9983e-7a00-49af-b1ee-19cdd69b827d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IwasawaDecompositionRealMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DetLeadingMinorGramIwasawaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramMinorSwapAdjacentColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis
import Theorems.Thm_GlobalTheory_ClassFin_HermiteReduction_exists_lt_two_mul
import Theorems.Thm_GlobalTheory_ClassFin_HermiteReduction_mul_upper
import Theorems.Thm_GlobalTheory_ClassFin_HermiteReduction_le_of_swap
import Theorems.Thm_GlobalTheory_T_det_leading_minor_gram_iwasawa
import Theorems.Thm_GlobalTheory_T_gram_leading_minor_lower_bound_integral
import Theorems.Thm_GlobalTheory_T_iwasawa_decomposition_real_matrix
import Theorems.Thm_GlobalTheory_T_unipotent_upper_size_reduction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HermiteReduction
namespace GlobalTheory.ClassFin.HermiteReduction
theorem _root_.solution : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (γ : Matrix (Fin N) (Fin N) ℤ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ (∀ i j, i < j → |n i j| ≤ 1 / 2) ∧ (∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  intro N g hg
  obtain ⟨c, hc, hcb⟩ := GlobalTheory.T.gram_leading_minor_lower_bound_integral N g hg
  let S := {γ : Matrix (Fin N) (Fin N) ℤ // γ.det = 1 ∨ γ.det = -1}
  have : Nonempty S := ⟨⟨1, Or.inl Matrix.det_one⟩⟩
  have hdet0 : ∀ γ : S, γ.1.det ≠ 0 := fun γ => by
    rcases γ.2 with h | h <;> rw [h] <;> norm_num
  have hbound : ∀ γ : S, c ^ (N + 1) ≤ ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j := by
    intro γ
    calc c ^ (N + 1) = ∏ _j : Fin (N + 1), c := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hc.le)
          (fun j _ => hcb γ.1 (hdet0 γ) j (Nat.lt_succ_iff.mp j.2))
  obtain ⟨γ0, hγ0⟩ := exists_lt_two_mul
    (fun γ : S => ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j) (c ^ (N + 1)) (pow_pos hc _) hbound
  have hgd : (g * γ0.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero hg ?_
    rw [← Int.cast_det]
    exact_mod_cast hdet0 γ0
  obtain ⟨k, a, n, hk, ha, hn1, hn0, hgk⟩ := GlobalTheory.T.iwasawa_decomposition_real_matrix N _ hgd
  obtain ⟨ν, hν1, hν0, hνb⟩ := GlobalTheory.T.unipotent_upper_size_reduction N n hn1 hn0
  have hνR1 : ∀ i, ν.map (Int.cast : ℤ → ℝ) i i = 1 := fun i => by simp [hν1]
  have hνR0 : ∀ i j, j < i → ν.map (Int.cast : ℤ → ℝ) i j = 0 := fun i j h => by simp [hν0 i j h]
  obtain ⟨hn'1, hn'0⟩ := mul_upper n _ hn1 hn0 hνR1 hνR0
  have hνdet : ν.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hν0 i j h)]
    simp [hν1]
  have hγdet : (γ0.1 * ν).det = 1 ∨ (γ0.1 * ν).det = -1 := by
    rw [Matrix.det_mul, hνdet, mul_one]
    exact γ0.2
  have hmap : (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      γ0.1.map (Int.cast : ℤ → ℝ) * ν.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have heq : g * (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ)) := by
    rw [hmap, ← Matrix.mul_assoc, hgk, Matrix.mul_assoc (k * diagonal a)]
  have hΦ : ∏ j, gramMinor (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))) j =
      ∏ j, gramMinor (g * γ0.1.map (Int.cast : ℤ → ℝ)) j := by
    rw [hgk]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold gramMinor
    rw [GlobalTheory.T.det_leading_minor_gram_iwasawa N k a _ hk hn'1 hn'0 j _, GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _]
  refine ⟨γ0.1 * ν, k, a, n * ν.map (Int.cast : ℤ → ℝ), hγdet, hk, ha, hn'1, hn'0, hνb,
    fun p q hq => ?_, heq⟩
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  let γ' : S := ⟨(γ0.1 * ν).submatrix id (Equiv.swap p q), by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hpq]
    rcases hγdet with h | h <;> simp [h]⟩
  have hsw : g * γ'.1.map (Int.cast : ℤ → ℝ) =
      (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))).submatrix id (Equiv.swap p q) := by
    rw [← heq]
    ext i j
    rfl
  refine le_of_swap k a _ hk ha hn'1 hn'0 hνb p q hq ?_
  rw [hΦ, ← hsw]
  exact hγ0 γ'
end GlobalTheory.ClassFin.HermiteReduction
