-- Prove2me | solution 1 for MayersBC.binary_kolmogorov_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:17:10.637054+00:00
-- url     : https://prove2.me/submissions/a0b2c9ce-159c-4760-ba27-1fad0cc8d22c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersBC_guessError
import Definitions.Def_MayersBC_outcomeDist
import Definitions.Def_MayersBC_binaryPOVM
import Definitions.Def_MayersBC_kolmogorov
open QAlgorithms

/-- For a density matrix, `Tr((I - Q) ρ) = 1 - Tr(Q ρ)`. -/
private lemma effectProb_one_sub {ι : Type} [Fintype ι] [DecidableEq ι] (Q ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) : effectProb (1 - Q) ρ = 1 - effectProb Q ρ := by
  simp only [effectProb, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    hρ.2, Complex.one_re]

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 Q : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) (hQ : IsEffect Q) :
    MayersBC.kolmogorov (MayersBC.outcomeDist (MayersBC.binaryPOVM Q) ρ0)
        (MayersBC.outcomeDist (MayersBC.binaryPOVM Q) ρ1) =
      4 * |MayersBC.guessError ρ0 ρ1 Q - 1 / 2| := by
  simp only [MayersBC.kolmogorov, MayersBC.outcomeDist, MayersBC.binaryPOVM, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, MayersBC.guessError,
    effectProb_one_sub Q ρ0 h0, effectProb_one_sub Q ρ1 h1]
  have e1 : 1 - effectProb Q ρ0 - (1 - effectProb Q ρ1) = -(effectProb Q ρ0 - effectProb Q ρ1) := by
    ring
  have e2 : 1 / 2 * (1 - effectProb Q ρ0) + 1 / 2 * effectProb Q ρ1 - 1 / 2 =
      -(1 / 2) * (effectProb Q ρ0 - effectProb Q ρ1) := by ring
  rw [e1, e2, abs_neg, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring
