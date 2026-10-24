-- Prove2me | solution 1 for ModernConvex.Relaxations.nesterov_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T22:18:57.555477+00:00
-- url     : https://prove2.me/submissions/0a4e8151-3b43-490d-b6a0-36a05e22d441

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_ModernConvex_Relaxations_opt_ge_asin_bound
import Theorems.Thm_ModernConvex_Relaxations_asin_matrix_ge

open Matrix

namespace NT98
open ModernConvex.Relaxations

lemma trace_vecMulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (A * vecMulVec v v).trace = v ⬝ᵥ (A *ᵥ v) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma trace_mul_nonneg {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hM : M.PosSemidef) : 0 ≤ (A * M).trace := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hM
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have := hA.dotProduct_mulVec_nonneg (v i)
  simp only [star_trivial] at this ⊢
  rw [trace_vecMulVec]; exact this

lemma abs_le_one {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsUnitDiagPSD X) (i j : Fin n) :
    |X i j| ≤ 1 := by
  have hs : X j i = X i j := by simpa using hX.1.1.apply i j
  have key : ∀ s : ℝ, 0 ≤ 1 + s * X i j + s * X j i + s ^ 2 := by
    intro s
    have h := hX.1.dotProduct_mulVec_nonneg (Pi.single i 1 + s • Pi.single j 1)
    simp only [star_trivial, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, mulVec_single_one, dotProduct_single, single_dotProduct,
      smul_eq_mul, one_mul, mul_one] at h
    have h1 : X i i = 1 := hX.2 i
    have h2 : X j j = 1 := hX.2 j
    simp only [col_apply] at h
    nlinarith [h1, h2]
  rw [hs] at key
  have k1 := key 1; have k2 := key (-1)
  rw [abs_le]; constructor <;> nlinarith

end NT98

open ModernConvex.Relaxations in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (OPT SDP : ℝ)
    (hOPT : IsLUB ((fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x)) ''
      {x | ∀ i, x i = 1 ∨ x i = -1}) OPT)
    (hSDP : IsLUB ((fun X : Matrix (Fin n) (Fin n) ℝ => (A * X).trace) ''
      {X | X.PosSemidef ∧ ∀ i, X i i = 1}) SDP) :
    OPT ≤ SDP ∧ 2 / Real.pi * SDP ≤ OPT := by
  have hpi := Real.pi_pos
  constructor
  · refine hOPT.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine hSDP.1 ⟨vecMulVec x x, ⟨?_, fun i => ?_⟩, NT98.trace_vecMulVec A x⟩
    · refine Matrix.posSemidef_iff_eq_sum_vecMulVec.2 ⟨1, fun _ => x, ?_⟩
      simp
    · rw [vecMulVec_apply]; rcases hx i with h | h <;> rw [h] <;> norm_num
  · have hQP : IsSignQPValue A OPT := hOPT
    obtain ⟨hb, -⟩ := opt_ge_asin_bound A hA.1 OPT hQP
    have hup : SDP ≤ Real.pi / 2 * OPT := by
      refine hSDP.2 ?_
      rintro _ ⟨X, hX, rfl⟩
      have hX' : IsUnitDiagPSD X := hX
      have h1 := hb X hX'
      have hge := asin_matrix_ge X hX.1 (NT98.abs_le_one X hX')
      have h2 := NT98.trace_mul_nonneg A _ hA hge
      rw [Matrix.mul_sub, trace_sub] at h2
      have h3 : (A * asinMatrix X).trace = ∑ i, ∑ j, A i j * Real.arcsin (X i j) := by
        simp only [trace, diag, mul_apply, asinMatrix, of_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hs : X j i = X i j := by simpa using hX.1.1.apply i j
        rw [hs]
      rw [h3] at h2
      have : ∑ i, ∑ j, A i j * Real.arcsin (X i j) ≤ Real.pi / 2 * OPT := by
        have h4 : 2 / Real.pi * (∑ i, ∑ j, A i j * Real.arcsin (X i j)) * (Real.pi / 2) ≤
            OPT * (Real.pi / 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
        have h5 : 2 / Real.pi * (∑ i, ∑ j, A i j * Real.arcsin (X i j)) * (Real.pi / 2) =
            ∑ i, ∑ j, A i j * Real.arcsin (X i j) := by field_simp
        linarith
      linarith
    have h6 : 2 / Real.pi * SDP ≤ 2 / Real.pi * (Real.pi / 2 * OPT) :=
      mul_le_mul_of_nonneg_left hup (by positivity)
    have h7 : 2 / Real.pi * (Real.pi / 2 * OPT) = OPT := by field_simp
    linarith
