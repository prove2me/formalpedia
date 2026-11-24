-- Prove2me | solution 1 for GlobalTheory.SW.Parab.isSB_parChar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:05.309262+00:00
-- url     : https://prove2.me/submissions/90ea57d7-d134-47a6-b900-d27bcaa06b4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma exists_pos_nat_mul_eq_int {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ T : Matrix ι ι ℤ, ∀ i j, (T i j : ℚ) = d * S i j := by
  refine ⟨∏ i, ∏ j, (S i j).den, Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (S i j).den_pos, ?_⟩
  have key : ∀ i j, ∃ t : ℤ, (t : ℚ) = ((∏ i, ∏ j, (S i j).den : ℕ) : ℚ) * S i j := by
    intro i j
    obtain ⟨m, hm⟩ : (S i j).den ∣ ∏ i, ∏ j, (S i j).den :=
      (Finset.dvd_prod_of_mem (fun j => (S i j).den) (Finset.mem_univ j)).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ j, (S i j).den) (Finset.mem_univ i))
    refine ⟨m * (S i j).num, ?_⟩
    rw [hm]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose T hT using key
  exact ⟨T, hT⟩
open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma isIntegral_int_rat_iff_exists_int (q : ℚ) : IsIntegral ℤ q ↔ ∃ n : ℤ, (n : ℚ) = q := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  simp
end GlobalTheory.SW.Parab
end

set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
namespace _root_.GlobalTheory.SW.Parab
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι] (S : Matrix ι ι ℚ)
    (φ : Matrix κ ι ℚ → ℂ) (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB fun x => _root_.GlobalTheory.SW.Parab.parChar S x * φ x := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  obtain ⟨d, hd, T, hT⟩ := exists_pos_nat_mul_eq_int S
  refine ⟨2 * d * R, by positivity, ?_, ?_⟩
  · intro x hx
    have hint := hsupp x (right_ne_zero_of_mul hx)
    intro k i
    obtain ⟨n, hn⟩ := (isIntegral_int_rat_iff_exists_int _).1 (hint k i)
    refine (isIntegral_int_rat_iff_exists_int _).2 ⟨2 * d * n, ?_⟩
    simp only [Matrix.smul_apply, smul_eq_mul] at hn ⊢
    push_cast at hn ⊢
    linear_combination (2 * d : ℚ) * hn

  · intro x y hy
    have hy' : _root_.GlobalTheory.SW.IntM (((2 * d : ℕ) : ℚ) • y) := by
      intro k i
      obtain ⟨n, hn⟩ := (isIntegral_int_rat_iff_exists_int _).1 (hy k i)
      refine (isIntegral_int_rat_iff_exists_int _).2 ⟨2 * d * n, ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul]
      push_cast
      rw [hn]
    have hφ : φ (x + ((2 * d * R : ℕ) : ℚ) • y) = φ x := by
      rw [← hper x _ hy', smul_smul]
      push_cast
      ring_nf
    simp only
    rw [hφ]
    by_cases h0 : φ x = 0
    · simp [h0]
    congr 1
    have hU : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
      simpa using (isIntegral_int_rat_iff_exists_int _).1 (hsupp x h0 k i)
    choose U hU using hU
    have hY : ∀ k i, ∃ n : ℤ, (n : ℚ) = y k i := fun k i =>
      (isIntegral_int_rat_iff_exists_int _).1 (hy k i)
    choose Y hY using hY
    have hQ : ∑ k, (x + ((2 * d * R : ℕ) : ℚ) • y) k ⬝ᵥ S *ᵥ (x + ((2 * d * R : ℕ) : ℚ) • y) k =
        ∑ k, x k ⬝ᵥ S *ᵥ x k + 2 * ((∑ k, ∑ i, ∑ j, (U k i * T i j * Y k j + Y k i * T i j * U k j +
          2 * d * R ^ 2 * Y k i * T i j * Y k j) : ℤ) : ℚ) := by
      push_cast
      simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hR' : (R : ℚ) ≠ 0 := by positivity
      have hd' : (d : ℚ) ≠ 0 := by positivity
      have hx1 : x k i = U k i / R := by rw [hU]; field_simp
      have hx2 : x k j = U k j / R := by rw [hU]; field_simp
      have hS : S i j = T i j / d := by rw [hT]; field_simp
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      rw [hx1, hx2, hS, ← hY k i, ← hY k j]
      field_simp
      ring
    unfold _root_.GlobalTheory.SW.Parab.parChar
    rw [hQ]
    set m : ℤ := ∑ k, ∑ i, ∑ j, (U k i * T i j * Y k j + Y k i * T i j * U k j +
          2 * d * R ^ 2 * Y k i * T i j * Y k j)
    have : -(↑π * I * (((∑ k, x k ⬝ᵥ S *ᵥ x k + 2 * (m : ℚ) : ℚ)) : ℂ)) =
        -(↑π * I * ((∑ k, x k ⬝ᵥ S *ᵥ x k : ℚ) : ℂ)) + ((-m : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
