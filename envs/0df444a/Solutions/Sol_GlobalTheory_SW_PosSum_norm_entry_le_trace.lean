-- Prove2me | solution 1 for GlobalTheory.SW.PosSum.norm_entry_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:44:39.134351+00:00
-- url     : https://prove2.me/submissions/bcf01a43-b0fb-40bb-a11a-c278c8453985

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.PosSum
namespace GlobalTheory.SW.PosSum
theorem _root_.solution {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (i j : Fin N) : ‖A i j‖ ≤ A.trace.re := by
  have hd : ∀ k, 0 ≤ (A k k).re := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).1
  have hi : ∀ k, (A k k).im = 0 := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).2.symm
  have ht : ∀ k, (A k k).re ≤ A.trace.re := fun k => by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.single_le_sum (f := fun k => (A k k).re) (fun k _ => hd k) (Finset.mem_univ k)
  have h2 := (Complex.nonneg_iff.1 (hA.submatrix ![i, j]).det_nonneg).1
  have hji : A j i = conj (A i j) := by
    have := hA.1.apply j i
    simpa using this.symm
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hji,
    Complex.mul_conj, Complex.sub_re, Complex.mul_re, hi, Complex.ofReal_re, mul_zero, sub_zero,
    Matrix.cons_val_fin_one] at h2
  have h0 : 0 ≤ A.trace.re := (hd i).trans (ht i)
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [Complex.sq_norm, sq]
  have := mul_le_mul (ht i) (ht j) (hd j) h0
  linarith
end GlobalTheory.SW.PosSum
