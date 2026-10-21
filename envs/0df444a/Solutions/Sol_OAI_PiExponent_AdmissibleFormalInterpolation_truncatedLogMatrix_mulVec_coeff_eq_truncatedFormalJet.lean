-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.truncatedLogMatrix_mulVec_coeff_eq_truncatedFormalJet
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:27:27.991796+00:00
-- url     : https://prove2.me/submissions/fb7dadbd-c444-44f2-8802-2d6e726a3dbd

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnCombination_eq_matrix_mulVec

/-!
# The truncated logarithmic interpolation matrix computes truncated formal jets

For a weighted polynomial `P : WeightedPolynomial w0 w H`, the truncated-log
interpolation matrix `truncatedLogMatrix K w0 v0 θ w H r T` acting on the vector
of simplex coefficients of `P` produces exactly the row-wise coefficients of the
truncated formal jet of `P`:
`(truncatedLogMatrix ...).mulVecLin (fun c => coeff (exponentVector c) P) rho`
is `coeff (exponentVector rho.2) (truncatedFormalJet T (fun i => rho.1 * r i) P)`.

The proof uses the already-proved platform lemma
`weightedSeriesJet_columnCombination_eq_matrix_mulVec`, which identifies the
matrix-vector product with the weighted series jet of the *column combination*
`columnCombination w0 w H x = ∑ c, x c • monomial (exponentVector c) 1`.
It remains to show that the column combination formed from the coefficient
function of `P` reconstructs `P`.  This is the content of
`columnCombination_coeff_eq`: every exponent in the support of `P` lies in the
weighted simplex `realWeightedSimplex (columnWeights w0 w) H` (the positivity of
the weights converts the weighted bound into the coordinate bounds), and all
other coefficients vanish.
-/

open scoped BigOperators

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

noncomputable section

namespace JetCoeff

open InterpolationMatrix

lemma exponentVector_coe {m : ℕ} (b : Fin (m + 1) →₀ ℕ) :
    InterpolationMatrix.exponentVector (fun i => b i) = b := by
  ext i
  rfl

lemma columnWeights_pos {m : ℕ} {w0 : ℝ} {w : Fin m → ℝ} (hw0 : 0 < w0)
    (hw : ∀ i, 0 < w i) (i : Fin (m + 1)) :
    0 < InterpolationMatrix.columnWeights w0 w i := by
  cases i using Fin.cases with
  | zero => simpa [InterpolationMatrix.columnWeights] using hw0
  | succ j => simpa [InterpolationMatrix.columnWeights] using hw j

lemma support_mem_realWeightedSimplex {m : ℕ} {w0 : ℝ} {w : Fin m → ℝ} {H : ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (P : WeightedPolynomial w0 w H) :
    ∀ b ∈ P.val.support,
      (fun i => b i) ∈ OAI.PiExponent.realWeightedSimplex
        (InterpolationMatrix.columnWeights w0 w) H := by
  intro b hb
  rw [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter]
  constructor
  · rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hwpos : 0 < InterpolationMatrix.columnWeights w0 w i :=
      columnWeights_pos hw0 hw i
    have hnonneg : ∀ j : Fin (m + 1),
        0 ≤ InterpolationMatrix.columnWeights w0 w j * (b j : ℝ) := by
      intro j
      have := columnWeights_pos hw0 hw j
      positivity
    have hle : (b i : ℝ) * InterpolationMatrix.columnWeights w0 w i ≤ H := by
      calc (b i : ℝ) * InterpolationMatrix.columnWeights w0 w i
          = InterpolationMatrix.columnWeights w0 w i * (b i : ℝ) := by ring
        _ ≤ ∑ j, InterpolationMatrix.columnWeights w0 w j * (b j : ℝ) :=
            Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
        _ ≤ H := P.2 b hb
    have hbd : (b i : ℝ) ≤ H / InterpolationMatrix.columnWeights w0 w i := by
      rw [le_div_iff₀ hwpos]
      linarith
    exact Nat.le_floor hbd
  · exact P.2 b hb

lemma columnCombination_coeff_eq {m : ℕ} {w0 : ℝ} {w : Fin m → ℝ} {H : ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (P : WeightedPolynomial w0 w H) :
    columnCombination w0 w H
        (fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.1) P.val) =
      P.val := by
  classical
  rw [columnCombination]
  have hterm : ∀ c : InterpolationMatrix.Column w0 w H,
      MvPolynomial.C (MvPolynomial.coeff (InterpolationMatrix.exponentVector c.1) P.val) *
          columnMonomial w0 w H c =
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector c.1) P.val) := by
    intro c
    rw [columnMonomial, MvPolynomial.C_mul_monomial, mul_one]
  simp only [hterm]
  have hsum : (∑ c : InterpolationMatrix.Column w0 w H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector c.1) P.val))
      = ∑ f ∈ OAI.PiExponent.realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector f)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val) :=
    Finset.sum_coe_sort
      (OAI.PiExponent.realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H)
      (fun f => MvPolynomial.monomial (InterpolationMatrix.exponentVector f)
        (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val))
  rw [hsum]
  -- keep only the terms whose exponent lies in the support of P
  have hfilter : (∑ f ∈ (OAI.PiExponent.realWeightedSimplex
        (InterpolationMatrix.columnWeights w0 w) H).filter
        (fun f => InterpolationMatrix.exponentVector f ∈ P.val.support),
        MvPolynomial.monomial (InterpolationMatrix.exponentVector f)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val))
      = ∑ f ∈ OAI.PiExponent.realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector f)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val) := by
    apply Finset.sum_filter_of_ne
    intro f hf hne
    rw [MvPolynomial.mem_support_iff]
    intro hzero
    exact hne (by rw [hzero]; exact MvPolynomial.monomial_zero)
  rw [← hfilter]
  -- the filtered set is the image of the support under `b ↦ (fun i => b i)`
  have himage : (OAI.PiExponent.realWeightedSimplex
        (InterpolationMatrix.columnWeights w0 w) H).filter
        (fun f => InterpolationMatrix.exponentVector f ∈ P.val.support)
      = P.val.support.image (fun b => fun i => b i) := by
    ext f
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hfsupp⟩
      refine ⟨InterpolationMatrix.exponentVector f, hfsupp, ?_⟩
      funext i
      rfl
    · rintro ⟨b, hb, rfl⟩
      refine ⟨support_mem_realWeightedSimplex hw0 hw P b hb, ?_⟩
      rw [exponentVector_coe]
      exact hb
  rw [himage]
  have hsum_image : (∑ f ∈ P.val.support.image (fun b => fun i => b i),
        MvPolynomial.monomial (InterpolationMatrix.exponentVector f)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val))
      = ∑ b ∈ P.val.support,
        MvPolynomial.monomial b (MvPolynomial.coeff b P.val) := by
    have h1 : (∑ f ∈ P.val.support.image (fun b => fun i => b i),
          MvPolynomial.monomial (InterpolationMatrix.exponentVector f)
            (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val))
        = ∑ b ∈ P.val.support,
          MvPolynomial.monomial (InterpolationMatrix.exponentVector (fun i => b i))
            (MvPolynomial.coeff (InterpolationMatrix.exponentVector (fun i => b i)) P.val) :=
      Finset.sum_image (s := P.val.support)
        (f := fun f => MvPolynomial.monomial
          (InterpolationMatrix.exponentVector f)
          (MvPolynomial.coeff (InterpolationMatrix.exponentVector f) P.val))
        (g := fun b => fun i => b i) (by
          intro b1 _ b2 _ h
          ext i
          exact congr_fun h i)
    refine h1.trans ?_
    apply Finset.sum_congr rfl
    intro b hb
    rw [exponentVector_coe]
  rw [hsum_image, ← MvPolynomial.as_sum]

end JetCoeff

open JetCoeff in
theorem solution {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) P.val) =
      (fun rho : InterpolationMatrix.Row K v0 theta w H =>
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val)) := by
  classical
  funext rho
  show ((InterpolationMatrix.matrix K w0 v0 theta w H r
      (fun i => InterpolationMatrix.truncatedLog (T i))).mulVecLin
        (fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) P.val)) rho =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
        (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val)
  rw [← weightedSeriesJet_columnCombination_eq_matrix_mulVec
    (G := fun i => InterpolationMatrix.truncatedLog (T i))]
  rw [columnCombination_coeff_eq (P := P) hw0 hw]
  rfl
