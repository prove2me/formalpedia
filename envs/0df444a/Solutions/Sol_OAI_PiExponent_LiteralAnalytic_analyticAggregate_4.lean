-- Prove2me | solution 4 for OAI.PiExponent.LiteralAnalytic.analyticAggregate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:14:47.128493+00:00
-- url     : https://prove2.me/submissions/a7e10d7a-567a-44d9-aa30-6a639d0a6de1

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

section
-- inlined definitions Def_OAI_PiExponent_AnalyticRemainder

noncomputable section
namespace OAI.PiExponent.DeterminantContradiction

-- Real polynomial majorant of TranslationCountLimit.translationTermCount.
def translationEnvelope (m : ℕ) (v H : ℝ) : ℝ :=
  (H + 1) ^ (2 * m) * (H / v + 1)

-- CollisionExponential.collisionRemainder, plus the translation entropy.
def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  (Real.log (actualRowCount d H : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
    Real.log (translationEnvelope d.m d.v0 H) / H

end OAI.PiExponent.DeterminantContradiction
end

section
-- inlined definitions Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators

noncomputable section

namespace OAI.PiExponent.DeterminantContradiction.FiniteTranslation

-- Function-indexed translation data for the FixedDeterminantFamily bundle.
-- The older LiteralAnalytic interface redeclares the parent constants in a
-- different definition bundle and cannot be imported alongside this one.
abbrev Index {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ↥(realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H)

abbrev Choice {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :=
  Σ a : Index d H,
    (∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) × Fin (r.2.1 0 + 1)

abbrev Family {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  ∀ r : Row d H, Choice d H r

def weight {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : Index d H) : ℝ :=
  ∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i * (a.1 i : ℝ)

def periodModel {m : ℕ} (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (MvPolynomial.C
      (PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + PowerSeries.log ℂ) +
      MvPolynomial.X i) ^ a i

def scalar {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : Choice d H r) : ℂ :=
  ((∏ i : Fin d.m, (t.1.1 i).choose (r.2.1 i.succ) *
      (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
    (∏ i : Fin d.m,
      ((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i)) *
    PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^ (t.2.1 i : ℕ))

def coefficientMatrix {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : Family d H) :
    Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((periodModel r.1.val ((selection c).1 0)
      (fun i => (selection c).1 i.succ)).coeff
        (InterpolationMatrix.exponentVector (f r).1.1))

def term {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : Family d H) : ℂ :=
  (∏ r : Row d H, scalar d r (f r)) * (coefficientMatrix d selection f).det

def collisionAllowance (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log (M : ℝ) + Real.log 2 / 4 -
    Real.log (1 - Real.exp (-Real.log 2 / 2))) / H

end OAI.PiExponent.DeterminantContradiction.FiniteTranslation
end

section
-- inlined definitions Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators

noncomputable section

namespace OAI.PiExponent.DeterminantContradiction.FiniteTranslation

/-- Positive degree compositions, represented by bounded Nat-valued tuples.
Every entry of a positive tuple summing to `k` is at most `k`. -/
noncomputable def logMajorantCompositions (q k : ℕ) : Finset (Fin q → ℕ) := by
  classical
  exact
    ((Finset.univ : Finset (Fin q → Fin (k + 1))).image
      (fun a i => (a i : ℕ))).filter
      (fun a => (∀ i, 0 < a i) ∧ ∑ i : Fin q, a i = k)

end OAI.PiExponent.DeterminantContradiction.FiniteTranslation
end

section
-- inlined definitions Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators

namespace OAI.PiExponent.FinitePeriodCollision

/-- The normalized Taylor coefficient, measured on the circle of radius 1/2. -/
noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)

/-- The entire column function obtained after taking a transverse coefficient. -/
noncomputable def analyticColumn {m : ℕ} (h : ℕ)
    (a A : Fin m → ℕ) (z : ℂ) : ℂ :=
  ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
    Complex.exp ((h : ℂ) * z) * z ^ (∑ i, (a i - A i))

end OAI.PiExponent.FinitePeriodCollision
end

section
-- OAI.PiExponent.InterpolationMatrix.affinePower_coeff_translate (76fa0d9e-733b-4f2f-bcd7-dbc933dcd0de)

open scoped BigOperators
open OAI.PiExponent
theorem h41_uni {R : Type*} [CommSemiring R] (n b : ℕ) (z e : R) :
    ∑ a ∈ Finset.range (n + 1), ((a.choose b : ℕ) : R) * e ^ (a - b) *
      (((n.choose a : ℕ) : R) * z ^ (n - a)) = ((n.choose b : ℕ) : R) * (z + e) ^ (n - b) := by
  by_cases hbn : n < b
  · rw [Nat.choose_eq_zero_of_lt hbn]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro a ha
    have : a < b := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hbn
    simp [Nat.choose_eq_zero_of_lt this]
  push Not at hbn
  have hsplit : n + 1 = b + (n - b + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h0 : ∑ a ∈ Finset.range b, ((a.choose b : ℕ) : R) * e ^ (a - b) *
      (((n.choose a : ℕ) : R) * z ^ (n - a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp ha)]
  rw [h0, zero_add, add_comm z e, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : b + j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hc := @Nat.choose_mul n (b + j) b (Nat.le_add_right b j)
  rw [Nat.add_sub_cancel_left] at hc
  have hc' : ((n.choose (b + j) : ℕ) : R) * (((b + j).choose b : ℕ) : R) =
      ((n.choose b : ℕ) : R) * (((n - b).choose j : ℕ) : R) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hc]
  have he : n - (b + j) = n - b - j := by omega
  rw [Nat.add_sub_cancel_left, he]
  calc _ = (((n.choose (b + j) : ℕ) : R) * (((b + j).choose b : ℕ) : R)) * (e ^ j * z ^ (n - b - j)) := by ring
    _ = (((n.choose b : ℕ) : R) * (((n - b).choose j : ℕ) : R)) * (e ^ j * z ^ (n - b - j)) := by rw [hc']
    _ = _ := by ring

theorem h41_expand {R : Type*} [CommSemiring R] {m : ℕ} (c : Fin m → R) (n : Fin m → ℕ) :
    (∏ i, (MvPolynomial.C (c i) + MvPolynomial.X i) ^ n i : MvPolynomial (Fin m) R) =
      ∑ k ∈ Fintype.piFinset (fun i => Finset.range (n i + 1)),
        MvPolynomial.monomial (InterpolationMatrix.exponentVector k)
          (∏ i, ((n i).choose (k i) : R) * c i ^ (n i - k i)) := by
  classical
  have h1 : ∀ i, (MvPolynomial.C (c i) + MvPolynomial.X i : MvPolynomial (Fin m) R) ^ n i =
      ∑ k ∈ Finset.range (n i + 1),
        MvPolynomial.C (((n i).choose k : R) * c i ^ (n i - k)) * MvPolynomial.X i ^ k := by
    intro i
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    simp only [map_mul, map_pow, map_natCast]
    ring
  simp_rw [h1]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [MvPolynomial.monomial_eq, Finset.prod_mul_distrib, ← map_prod]
  congr 1
  simp only [InterpolationMatrix.exponentVector]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i; simp

theorem h41_coeff {R : Type*} [CommSemiring R] {m : ℕ} (c : Fin m → R) (n a : Fin m → ℕ) :
    (∏ i, (MvPolynomial.C (c i) + MvPolynomial.X i) ^ n i : MvPolynomial (Fin m) R).coeff
      (InterpolationMatrix.exponentVector a) = ∏ i, ((n i).choose (a i) : R) * c i ^ (n i - a i) := by
  classical
  rw [h41_expand, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  have hinj : ∀ k, InterpolationMatrix.exponentVector k = InterpolationMatrix.exponentVector a ↔ k = a := by
    intro k
    simp [InterpolationMatrix.exponentVector]
  simp only [hinj]
  rw [Finset.sum_ite_eq']
  split_ifs with ha
  · rfl
  · rw [Fintype.mem_piFinset] at ha
    push Not at ha
    obtain ⟨i, hi⟩ := ha
    have : n i < a i := by have := Finset.mem_range.not.mp hi; omega
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt this]

theorem OAI.PiExponent.InterpolationMatrix.affinePower_coeff_translate
    {R : Type*} [CommSemiring R] {m : ℕ}
    (f : R) (z e : Fin m → R) (n b : Fin m → ℕ)
    (S : Finset (Fin m → ℕ))
    (hS : ∀ a : Fin m → ℕ, (∀ i, a i ≤ n i) → a ∈ S) :
    (MvPolynomial.C f *
      ∏ i, (MvPolynomial.C (z i + e i) + MvPolynomial.X i) ^ n i).coeff
        (InterpolationMatrix.exponentVector b) =
      ∑ a : ↥S,
        ((∏ i, (a.1 i).choose (b i) : ℕ) : R) *
          (∏ i, e i ^ (a.1 i - b i)) *
          (MvPolynomial.C f *
            ∏ i, (MvPolynomial.C (z i) + MvPolynomial.X i) ^ n i).coeff
              (InterpolationMatrix.exponentVector a.1) := by
  classical
  rw [MvPolynomial.coeff_C_mul, h41_coeff]
  simp_rw [MvPolynomial.coeff_C_mul, h41_coeff]
  rw [Finset.sum_coe_sort S (fun a => ((∏ i, (a i).choose (b i) : ℕ) : R) * (∏ i, e i ^ (a i - b i)) *
      (f * ∏ i, ((n i).choose (a i) : R) * z i ^ (n i - a i)))]
  have hsub : Fintype.piFinset (fun i => Finset.range (n i + 1)) ⊆ S := by
    intro a ha
    rw [Fintype.mem_piFinset] at ha
    exact hS a (fun i => Nat.lt_succ_iff.mp (Finset.mem_range.mp (ha i)))
  rw [← Finset.sum_subset hsub]
  · have : ∀ a : Fin m → ℕ, ((∏ i, (a i).choose (b i) : ℕ) : R) * (∏ i, e i ^ (a i - b i)) *
        (f * ∏ i, ((n i).choose (a i) : R) * z i ^ (n i - a i)) =
        f * ∏ i, (((a i).choose (b i) : ℕ) : R) * e i ^ (a i - b i) *
          (((n i).choose (a i) : ℕ) : R) * z i ^ (n i - a i) := by
      intro a
      rw [Nat.cast_prod]
      simp only [Finset.prod_mul_distrib]
      ring
    simp_rw [this]
    rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun i => Finset.range (n i + 1))
      (fun i k => ((k.choose (b i) : ℕ) : R) * e i ^ (k - b i) * ((n i).choose k : ℕ) * z i ^ (n i - k))]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← h41_uni]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro a _ ha
    rw [Fintype.mem_piFinset] at ha
    push Not at ha
    obtain ⟨i, hi⟩ := ha
    have : n i < a i := by have := Finset.mem_range.not.mp hi; omega
    have hz : ∏ i, ((n i).choose (a i) : R) * z i ^ (n i - a i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt this])
    rw [hz]; simp

end

section
-- OAI.PiExponent.InterpolationMatrix.prod_add_pow_fin (a13a27de-6b23-4b91-95af-062b53ed0fcf)

open scoped BigOperators


theorem OAI.PiExponent.InterpolationMatrix.prod_add_pow_fin
    {R : Type*} [CommSemiring R] {m : ℕ}
    (x y : Fin m → R) (k : Fin m → ℕ) :
    (∏ i, (x i + y i) ^ k i) =
      ∑ u : (∀ i : Fin m, Fin (k i + 1)),
        ((∏ i, (k i).choose (u i : ℕ) : ℕ) : R) *
          (∏ i, x i ^ (k i - (u i : ℕ))) *
          ∏ i, y i ^ (u i : ℕ) := by
  have h1 : ∀ i, (x i + y i) ^ k i = ∑ u : Fin (k i + 1),
      ((k i).choose (u : ℕ) : R) * x i ^ (k i - (u : ℕ)) * y i ^ (u : ℕ) := by
    intro i
    rw [add_comm, add_pow, Fin.sum_univ_eq_sum_range (fun u => ((k i).choose u : R) * x i ^ (k i - u) * y i ^ u)]
    refine Finset.sum_congr rfl (fun u _ => by ring)
  simp_rw [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Nat.cast_prod]

end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actualMatrix_entry_translation (ac1b06e9-1691-4a1d-9c14-93006e5196e3)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

private theorem transverse_box_mem
    {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 ≤ w0) (hw : ∀ i, 0 ≤ w i)
    (c : InterpolationMatrix.Column w0 w H)
    (a : Fin m → ℕ) (ha : ∀ i, a i ≤ c.1 i.succ) :
    a ∈ realWeightedSimplex w H := by
  classical
  have hcbox := Fintype.mem_piFinset.mp (Finset.mem_filter.mp c.2).1
  have hcweight := (Finset.mem_filter.mp c.2).2
  apply Finset.mem_filter.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro i
    have hi : c.1 i.succ < ⌊H / w i⌋₊ + 1 := by
      simpa only [InterpolationMatrix.columnWeights, Fin.cases_succ,
        Finset.mem_range] using hcbox i.succ
    exact Finset.mem_range.mpr (lt_of_le_of_lt (ha i) hi)
  · calc
      ∑ i, w i * (a i : ℝ) ≤ ∑ i, w i * (c.1 i.succ : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (ha i)) (hw i)
      _ ≤ w0 * (c.1 0 : ℝ) + ∑ i, w i * (c.1 i.succ : ℝ) :=
        le_add_of_nonneg_left (mul_nonneg hw0 (Nat.cast_nonneg _))
      _ ≤ H := by
        simpa only [Fin.sum_univ_succ, InterpolationMatrix.columnWeights,
          Fin.cases_zero, Fin.cases_succ] using hcweight

private theorem coeff_constant_mul_convolution
    (s : ℕ) (q : ℂ) (F G : PowerSeries ℂ) :
    PowerSeries.coeff s (PowerSeries.C q * F * G) =
      ∑ k : Fin (s + 1),
        (q * PowerSeries.coeff (k : ℕ) F) *
          PowerSeries.coeff (s - (k : ℕ)) G := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum,
    Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  exact (mul_assoc _ _ _).symm

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actualMatrix_entry_translation
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (c : Column d H) :
    actualMatrix d H r c =
      ∑ t : Choice d H r, scalar d r t *
        PowerSeries.coeff (r.2.1 0 - (t.2.2 : ℕ))
          ((periodModel r.1.val (c.1 0) (fun i => c.1 i.succ)).coeff
            (InterpolationMatrix.exponentVector t.1.1)) := by
  classical
  let b : Fin d.m → ℕ := fun i => r.2.1 i.succ
  let n : Fin d.m → ℕ := fun i => c.1 i.succ
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  let S := realWeightedSimplex w H
  let centers := MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  let T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0
  let delta : Fin d.m → ℂ := fun i =>
    (r.1.val : ℂ) * (centers i - 2 * (Real.pi : ℂ) * Complex.I)
  let D : Fin d.m → PowerSeries ℂ := fun i =>
    (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ
  let z : Fin d.m → PowerSeries ℂ := fun _ =>
    PowerSeries.C ((r.1.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + PowerSeries.log ℂ
  let f : PowerSeries ℂ := (1 + PowerSeries.X) ^ (c.1 0)
  let P : MvPolynomial (Fin d.m) (PowerSeries ℂ) :=
    periodModel r.1.val (c.1 0) n
  let Q : MvPolynomial (Fin d.m) (Polynomial ℂ) :=
    InterpolationMatrix.monomialImage centers
      (fun i => InterpolationMatrix.truncatedLog (T i)) r.1.val (c.1 0) n
  let Qs := MvPolynomial.map (Polynomial.coeToPowerSeries.ringHom :
    Polynomial ℂ →+* PowerSeries ℂ) Q
  have hS : ∀ a : Fin d.m → ℕ, (∀ i, a i ≤ n i) → a ∈ S := by
    intro a ha
    exact transverse_box_mem d.w0_pos.le
      (fun i => by dsimp [w, MatrixArithmetic.logWeights]; exact Nat.cast_nonneg _) c a ha
  have hcenter (i : Fin d.m) :
      z i + (PowerSeries.C (delta i) + D i) =
        PowerSeries.C ((r.1.val : ℂ) * centers i) +
          (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) := by
    dsimp [z, delta, D]
    simp only [mul_sub, map_sub]
    ring
  have hQs : Qs = MvPolynomial.C f *
      ∏ i, (MvPolynomial.C (z i + (PowerSeries.C (delta i) + D i)) +
        MvPolynomial.X i) ^ n i := by
    simp only [Qs, Q, InterpolationMatrix.monomialImage, map_add, map_mul, map_prod,
      map_pow, MvPolynomial.map_C, MvPolynomial.map_X,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add,
      Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_X,
      Polynomial.coe_C, InterpolationMatrix.truncatedLog, hcenter, f]
  have hentry : actualMatrix d H r c =
      PowerSeries.coeff (r.2.1 0) (Qs.coeff (InterpolationMatrix.exponentVector b)) := by
    change (Q.coeff (InterpolationMatrix.exponentVector b)).coeff (r.2.1 0) = _
    simp only [Qs, MvPolynomial.coeff_map, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeff_coe]
  have htranslate := InterpolationMatrix.affinePower_coeff_translate
    f z (fun i => PowerSeries.C (delta i) + D i) n b S hS
  have hseries : Qs.coeff (InterpolationMatrix.exponentVector b) =
      ∑ a : Index d H,
        ∑ u : (∀ i : Fin d.m, Fin (a.1 i - b i + 1)),
          PowerSeries.C
            (((∏ i : Fin d.m,
                (a.1 i).choose (b i) * (a.1 i - b i).choose (u i : ℕ) : ℕ) : ℂ) *
              ∏ i : Fin d.m, delta i ^ (a.1 i - b i - (u i : ℕ))) *
            (∏ i : Fin d.m, D i ^ (u i : ℕ)) *
            P.coeff (InterpolationMatrix.exponentVector a.1) := by
    rw [hQs]
    calc
      _ = ∑ a : Index d H,
          ((∏ i, (a.1 i).choose (b i) : ℕ) : PowerSeries ℂ) *
            (∏ i, (PowerSeries.C (delta i) + D i) ^ (a.1 i - b i)) *
            P.coeff (InterpolationMatrix.exponentVector a.1) := by
        exact htranslate
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [InterpolationMatrix.prod_add_pow_fin]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        simp only [map_mul, map_prod, map_pow, map_natCast,
          Nat.cast_prod, Nat.cast_mul, Finset.prod_mul_distrib]
        ring
  rw [hentry, hseries]
  simp only [map_sum]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [coeff_constant_mul_convolution]
  apply Finset.sum_congr rfl
  intro k _
  rfl
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_card_le_translationEnvelope (a33bb642-369b-40d6-a82b-5e59cedae056)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
theorem h41_index_coord_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (a : Index d H) (i : Fin d.m) : ((a.1 i : ℕ) : ℝ) ≤ H := by
  have ha := a.2
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at ha
  have h1 := Nat.lt_succ_iff.mp (ha.1 i)
  have hw : MatrixArithmetic.logWeights (finiteDenominators d) i =
      ((⌈Real.log (finiteDenominators d i)⌉₊ : ℕ) : ℝ) := rfl
  rcases Nat.eq_zero_or_pos (⌈Real.log (finiteDenominators d i)⌉₊) with h0 | hpos
  · rw [hw, h0] at h1
    simp at h1
    rw [h1]; simp; exact hH.le
  · have hw1 : (1 : ℝ) ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
      rw [hw]; exact_mod_cast hpos
    calc ((a.1 i : ℕ) : ℝ) ≤ (⌊H / MatrixArithmetic.logWeights (finiteDenominators d) i⌋₊ : ℝ) := by
          exact_mod_cast h1
      _ ≤ H / MatrixArithmetic.logWeights (finiteDenominators d) i :=
          Nat.floor_le (div_nonneg hH.le (by linarith))
      _ ≤ H := div_le_self hH.le hw1

theorem h41_row0_le {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) : ((r.2.1 0 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hr := r.2.2
  simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at hr
  have h1 := Nat.lt_succ_iff.mp (hr.1.1 0)
  have hv : InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
      (MatrixArithmetic.logWeights (finiteDenominators d)) 0 = d.v0 := rfl
  rw [hv] at h1
  calc ((r.2.1 0 : ℕ) : ℝ) ≤ (⌊H / (d.v0 : ℝ)⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ H / (d.v0 : ℝ) := Nat.floor_le (div_nonneg hH.le d.v0_pos.le)

theorem h41_index_card {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Fintype.card (Index d H) : ℝ) ≤ (H + 1) ^ d.m := by
  classical
  rw [Fintype.card_coe]
  have hsub : realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H ⊆
      Fintype.piFinset (fun _ : Fin d.m => Finset.range (⌊H⌋₊ + 1)) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have := h41_index_coord_le d hH ⟨a, ha⟩ i
    exact Nat.le_floor this
  have h2 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h2
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  calc ((realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d)) H).card : ℝ)
      ≤ ((⌊H⌋₊ + 1) ^ d.m : ℕ) := by exact_mod_cast h2
    _ ≤ (H + 1) ^ d.m := by
        push_cast
        gcongr
        exact Nat.floor_le hH.le

theorem h41_fiber_card {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (a : Index d H) :
    (Fintype.card
      ((∀ i : Fin d.m, Fin (a.1 i - r.2.1 i.succ + 1)) ×
        Fin (r.2.1 0 + 1)) : ℝ) ≤
      (H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1) := by
  rw [Fintype.card_prod, Fintype.card_pi]
  simp only [Fintype.card_fin]
  push_cast
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · calc _ ≤ ∏ _i : Fin d.m, (H + 1) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _
            have h1 := h41_index_coord_le d hH a i
            have : ((a.1 i - r.2.1 i.succ : ℕ) : ℝ) ≤ (a.1 i : ℝ) := by
              exact_mod_cast Nat.sub_le _ _
            linarith
      _ = (H + 1) ^ d.m := by simp
  · linarith [h41_row0_le d hH r]

theorem h41_choice_card {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) :
    (Fintype.card (Choice d H r) : ℝ) ≤
      (Fintype.card (Index d H) : ℝ) *
        ((H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1)) := by
  rw [Fintype.card_sigma]
  push_cast
  calc _ ≤ ∑ _a : Index d H, ((H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro a _
        exact_mod_cast h41_fiber_card d hH r a
    _ = _ := by simp

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.choice_card_le_translationEnvelope
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) :
    (Fintype.card (Choice d H r) : ℝ) ≤
      translationEnvelope d.m d.v0 H := by
  have h1 := h41_choice_card d hH r
  have h2 := h41_index_card d hH
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  have h3 : 0 ≤ (H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1) := by positivity
  unfold translationEnvelope
  calc _ ≤ _ := h1
    _ ≤ (H + 1) ^ d.m * ((H + 1) ^ d.m * (H / (d.v0 : ℝ) + 1)) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by ring

end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.expansion_and_card (7ca5efcc-c3fa-4367-a774-afc4e2610fba)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.expansion_and_card
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det = (∑ f : Family d H, term d selection f) ∧
      (Fintype.card (Family d H) : ℝ) ≤
        translationEnvelope d.m d.v0 H ^ actualRowCount d H := by
  classical
  constructor
  · let C : (r : Row d H) → Choice d H r → Row d H → ℂ :=
      fun r t c => PowerSeries.coeff (r.2.1 0 - (t.2.2 : ℕ))
        ((periodModel r.1.val ((selection c).1 0)
          (fun i => (selection c).1 i.succ)).coeff
            (InterpolationMatrix.exponentVector t.1.1))
    have hrows : actualMinor d H selection =
        (fun r => ∑ t : Choice d H r, scalar d r t • C r t) := by
      funext r c
      change actualMatrix d H r (selection c) = _
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, C] using
        (actualMatrix_entry_translation d hH r (selection c))
    calc
      (actualMinor d H selection).det =
          Matrix.det (fun r => ∑ t : Choice d H r, scalar d r t • C r t) :=
        congrArg Matrix.det hrows
      _ = ∑ f : Family d H,
          Matrix.det (fun r => scalar d r (f r) • C r (f r)) :=
        (Matrix.detRowAlternating :
          (Row d H → ℂ) [⋀^Row d H]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
            (fun r t => scalar d r t • C r t)
      _ = ∑ f : Family d H, term d selection f := by
        apply Finset.sum_congr rfl
        intro f _
        exact Matrix.det_mul_column (fun r => scalar d r (f r))
          (coefficientMatrix d selection f)
  · calc
      (Fintype.card (Family d H) : ℝ) =
          ∏ r : Row d H, (Fintype.card (Choice d H r) : ℝ) := by
        simp only [Family, Fintype.card_pi, Nat.cast_prod]
      _ ≤ ∏ _r : Row d H, translationEnvelope d.m d.v0 H :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          (fun r _ => choice_card_le_translationEnvelope d hH r)
      _ = translationEnvelope d.m d.v0 H ^ actualRowCount d H := by
        simp only [Finset.prod_const, Finset.card_univ, actualRowCount]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.low_simplex_nonempty (c321ebe1-8965-4370-bb2b-c7b69e307c9e)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.low_simplex_nonempty
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) := by
  classical
  have hA : 0 < (d.base.A : ℝ) := lt_trans d.base.theta_pos d.base.theta_lt_A
  have hcut : 0 ≤ (d.base.A : ℝ) * H := le_of_lt (mul_pos hA hH)
  let z : Fin d.m → ℕ := fun _ => 0
  have hz : z ∈ realWeightedSimplex
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((d.base.A : ℝ) * H) := by
    rw [realWeightedSimplex]
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro i
      simp [z]
    · simpa [z] using hcut
  unfold lowIndexCount
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨z, hz⟩)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_weights_nonneg (43ba954d-c39e-42d8-8c70-b05a7a7831e7)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_weights_nonneg {nu : ℝ} (d : FixedData nu) {H : ℝ} :
    ∀ a : Index d H, 0 ≤ weight d a := by
  intro a
  unfold weight
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.realWeightedSimplex_mem_of_pos_weighted_sum_le (0edf71a8-bcb4-4e57-8090-97606033216a)

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.realWeightedSimplex_mem_of_pos_weighted_sum_le
    {m : ℕ} (w : Fin m → ℝ) {T : ℝ} (a : Fin m → ℕ)
    (hT : 0 < T) (hw : ∀ i, 0 < w i)
    (ha : ∑ i, w i * (a i : ℝ) ≤ T) :
    a ∈ realWeightedSimplex w T := by
  classical
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  refine ⟨?_, ha⟩
  intro i
  have hterm : w i * (a i : ℝ) ≤ T := by
    have hle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin m => w j * (a j : ℝ))
      (fun j hj => mul_nonneg (le_of_lt (hw j)) (Nat.cast_nonneg _))
      (Finset.mem_univ i)
    exact le_trans hle ha
  have hratio : (a i : ℝ) ≤ T / w i := by
    rw [le_div_iff₀ (hw i)]
    simpa [mul_comm] using hterm
  exact Nat.lt_succ_of_le (Nat.le_floor hratio)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.finite_logWeights_pos (0aa2ab88-99f6-46de-bfd8-d21590fcaf8e)

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.finite_logWeights_pos
    {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
  change (0 : ℝ) < (Nat.ceil (Real.log (d.q i.val : ℝ)) : ℝ)
  rw [← d.x_log i.val]
  exact lt_of_lt_of_le zero_lt_one (d.x_one_le (i.val + 1))
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex (2b76aa41-354a-4a1f-a04b-55bac276ee22)


open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (Finset.univ.filter
      (fun a : Index d H => weight d a ≤ (d.base.A : ℝ) * H)).image
        (fun a => a.1) ⊆
      realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
        ((d.base.A : ℝ) * H) := by
  classical
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact realWeightedSimplex_mem_of_pos_weighted_sum_le
    (a := a.1)
    (hT := mul_pos (show 0 < (d.base.A : ℝ) by
      exact d.base.theta_pos.trans d.base.theta_lt_A) hH)
    (hw := fun i => finite_logWeights_pos d i)
    (ha := by simpa [weight] using (Finset.mem_filter.mp ha).2)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality (a43e9071-6307-4c25-b550-048e0e54438c)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
      (∀ a : Index d H, 0 ≤ weight d a) ∧
      (((Finset.univ : Finset (Index d H)).filter
        (fun a => weight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
          (lowIndexCount d H : ℝ) := by
  constructor
  · exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.low_simplex_nonempty
      d hH
  constructor
  · exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_weights_nonneg d
  · classical
    let S : Finset (Index d H) := Finset.univ.filter
      (fun a => weight d a ≤ (d.base.A : ℝ) * H)
    have himage :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.small_weight_indices_image_subset_low_simplex
        d hH
    have hcard : (S.image Subtype.val).card = S.card := by
      apply Finset.card_image_iff.mpr
      intro x hx y hy hxy
      exact Subtype.ext hxy
    change (S.card : ℝ) ≤ (lowIndexCount d H : ℝ)
    rw [← hcard]
    change ((S.image Subtype.val).card : ℝ) ≤
      ((realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
        ((d.base.A : ℝ) * H)).card : ℝ)
    exact_mod_cast Finset.card_le_card (by simpa [S] using himage)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight (258b2bf8-e926-4c75-b917-4b0de2b881e2)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : Family d H)
    (hf : (∏ r : Row d H, scalar d r (f r)) ≠ 0)
    (r : Row d H) :
    ∑ i : Fin d.m,
        (r.2.1 i.succ : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i ≤
      weight d (f r).1 := by
  classical
  have hscalar : scalar d r (f r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hf r (Finset.mem_univ r)
  have hcoord : ∀ i : Fin d.m, r.2.1 i.succ ≤ (f r).1.1 i := by
    intro i
    apply le_of_not_gt
    intro hlt
    have hprod :
        (∏ j : Fin d.m,
          ((f r).1.1 j).choose (r.2.1 j.succ) *
            ((f r).1.1 j - r.2.1 j.succ).choose ((f r).2.1 j) : ℕ) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]
    exact hscalar (by simp only [scalar, hprod, Nat.cast_zero, zero_mul])
  unfold weight
  apply Finset.sum_le_sum
  intro i hi
  have hcoordR : (r.2.1 i.succ : ℝ) ≤ ((f r).1.1 i : ℝ) :=
    Nat.cast_le.mpr (hcoord i)
  have hweight : 0 ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    unfold MatrixArithmetic.logWeights
    exact Nat.cast_nonneg _
  calc
    (r.2.1 i.succ : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i ≤
        ((f r).1.1 i : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i :=
      mul_le_mul_of_nonneg_right hcoordR hweight
    _ = MatrixArithmetic.logWeights (finiteDenominators d) i * ((f r).1.1 i : ℝ) :=
      mul_comm _ _
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum (5c287ccb-2663-4c5b-a59e-5e11a8a6e593)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : Family d H)
    (hf : (∏ r : Row d H, scalar d r (f r)) ≠ 0) :
    MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H ≤
      ∑ r : Row d H, weight d (f r).1 := by
  classical
  unfold MatrixArithmetic.rowWeightedSum
  apply Finset.sum_le_sum
  intro r hr
  exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight
    d f hf r
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization (74affad9-92c9-47ae-afdd-e666c59c91c7)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (actualRowCount d H : ℝ) * H * actualMean d H =
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H := by
  classical
  have hrow : Nonempty (Row d H) := by
    refine ⟨(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩,
      ⟨fun _ : Fin (d.m + 1) => 0, ?_⟩)⟩
    change (fun _ : Fin (d.m + 1) => 0) ∈
      strictWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))) H
    simp [strictWeightedSimplex, realWeightedSimplex, hH.le, hH]
  have hcard : (Fintype.card (Row d H) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr hrow))
  rw [actualRowCount, actualMean, MatrixArithmetic.meanRowWeight]
  field_simp [hcard, ne_of_gt hH]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry (b4f231e7-6800-4b74-8869-4fac56bca1d9)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < (lowIndexCount d H : ℝ) ∧
      (∀ a : Index d H, 0 ≤ weight d a) ∧
      (((Finset.univ : Finset (Index d H)).filter
        (fun a => weight d a ≤ (d.base.A : ℝ) * H)).card : ℝ) ≤
          (lowIndexCount d H : ℝ) ∧
      (∀ f : Family d H, (∏ r : Row d H, scalar d r (f r)) ≠ 0 →
        (actualRowCount d H : ℝ) * H * actualMean d H ≤
          ∑ r : Row d H, weight d (f r).1) := by
  obtain ⟨hcount, hweight, hcapacity⟩ :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.index_geometry_cardinality d hH
  refine ⟨hcount, hweight, hcapacity, ?_⟩
  intro f hf
  calc
    (actualRowCount d H : ℝ) * H * actualMean d H =
        MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization d hH
    _ ≤ ∑ r : Row d H, weight d (f r).1 :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum d f hf
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error (c48ff820-62cf-46be-8759-170e49dff715)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error
    {nu : ℝ} (p : ℤ) (q k K : ℕ) (hnu : 0 ≤ nu)
    (hq : 0 < q) (hk : k ≤ K)
    (herr : |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ‖((k : ℂ) *
      (2 * Complex.I * (p : ℂ) / (q : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I))‖ ≤
      2 * (K : ℝ) * (q : ℝ) ^ (-nu) := by
  let e : ℝ := (p : ℝ) / (q : ℝ) - Real.pi
  have herror : |e| ≤ (q : ℝ) ^ (-nu) := by
    dsimp [e]
    simpa [abs_sub_comm] using herr
  have hfactor :
      2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * (Real.pi : ℂ) * Complex.I =
        (2 * Complex.I) * (e : ℂ) := by
    dsimp [e]
    push_cast
    ring
  have hnorm :
      ‖((k : ℂ) *
        (2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * (Real.pi : ℂ) * Complex.I))‖ =
        2 * (k : ℝ) * |e| := by
    rw [hfactor]
    simp [norm_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  rw [hnorm]
  have hkreal : (k : ℝ) ≤ K := by exact_mod_cast hk
  calc
    2 * (k : ℝ) * |e| ≤ 2 * (K : ℝ) * |e| := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkreal (by norm_num)) (abs_nonneg e)
    _ ≤ 2 * (K : ℝ) * (q : ℝ) ^ (-nu) := by
      exact mul_le_mul_of_nonneg_left herror (by positivity)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log (53c007d7-ca66-48db-8fd9-c4374b07280c)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log
    {nu : ℝ} (q K : ℕ) (hnu : 0 ≤ nu)
    (hq : 2 ≤ q) (hK : 1 ≤ K) :
    2 * (K : ℝ) * (q : ℝ) ^ (-nu) ≤
      Real.exp
        (Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    have hq_ge : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hA_pos : (0 : ℝ) < 2 * (K : ℝ) := by
    have hK_ge : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    positivity
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by
    have hq_one : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
    exact_mod_cast hq_one
  have hlog_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq_ge_one
  have hceil :
      (Nat.ceil (Real.log (q : ℝ)) : ℝ) ≤ Real.log (q : ℝ) + 1 :=
    (Nat.ceil_lt_add_one hlog_nonneg).le
  have hceil_mul := mul_le_mul_of_nonneg_left hceil hnu
  have hexp :
      Real.log (2 * (K : ℝ)) + Real.log (q : ℝ) * (-nu) ≤
        Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ) := by
    nlinarith
  rw [Real.rpow_def_of_pos hq_pos]
  calc
    2 * (K : ℝ) * Real.exp (Real.log (q : ℝ) * (-nu)) =
        Real.exp (Real.log (2 * (K : ℝ)) + Real.log (q : ℝ) * (-nu)) := by
          rw [Real.exp_add, Real.exp_log hA_pos]
    _ ≤ Real.exp
        (Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ)) :=
      Real.exp_le_exp.mpr hexp
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_factor_bound_of_approximation (6e2ab0ae-9040-435c-b1be-a422bcc7e752)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_factor_bound_of_approximation
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) (i : Fin d.m) :
    ‖((r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
      Real.exp
        (Real.log (2 * (d.K : ℝ)) + nu -
          nu * MatrixArithmetic.logWeights (finiteDenominators d) i) := by
  have ha := d.approximations i.val
  have hk : r.1.val ≤ d.K := Nat.le_of_lt r.1.isLt
  have hq : 2 ≤ d.q i.val := ha.1
  calc
    ‖((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
        2 * (d.K : ℝ) * (d.q i.val : ℝ) ^ (-nu) := by
      simpa [MatrixArithmetic.rationalCenters, finiteNumerators,
        finiteDenominators] using
        (OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error
          (d.p i.val) (d.q i.val) r.1.val d.K hnu
          (Nat.lt_of_lt_of_le (by decide : 0 < 2) hq) hk ha.2.2)
    _ ≤ Real.exp
        (Real.log (2 * (d.K : ℝ)) + nu -
          nu * MatrixArithmetic.logWeights (finiteDenominators d) i) := by
      simpa [MatrixArithmetic.logWeights, finiteDenominators] using
        (OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log
          (d.q i.val) d.K hnu hq d.K_pos)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_weighted_product (1671d8bb-81c3-4fb4-b4af-e16cd13f0e98)

open scoped BigOperators

private theorem exp_pow_nat (x : ℝ) (n : ℕ) :
    Real.exp x ^ n = Real.exp (x * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

private theorem exp_prod_sum {α : Type} (s : Finset α) (f : α → ℝ) :
    (∏ i ∈ s, Real.exp (f i)) = Real.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, Real.exp_add]

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_weighted_product {m : ℕ} (z : Fin m → ℂ) (w : Fin m → ℝ) (e : Fin m → ℕ)
    (C nu : ℝ) (hnu : 0 ≤ nu) (hC : 0 ≤ C)
    (hcenter : ∀ i : Fin m, ‖z i‖ ≤ Real.exp (C - nu * w i)) :
    ‖∏ i : Fin m, (z i) ^ (e i)‖ ≤
      Real.exp (C * (∑ i : Fin m, (e i : ℝ)) -
        nu * (∑ i : Fin m, w i * (e i : ℝ))) := by
  have hfactor (i : Fin m) :
      ‖z i‖ ^ (e i) ≤ Real.exp ((C - nu * w i) * (e i : ℝ)) := by
    calc
      ‖z i‖ ^ (e i) ≤ Real.exp (C - nu * w i) ^ (e i) :=
        pow_le_pow_left₀ (norm_nonneg _) (hcenter i) _
      _ = Real.exp ((C - nu * w i) * (e i : ℝ)) := exp_pow_nat _ _
  calc
    ‖∏ i : Fin m, (z i) ^ (e i)‖ = ∏ i : Fin m, ‖z i‖ ^ (e i) := by simp
    _ ≤ ∏ i : Fin m, Real.exp ((C - nu * w i) * (e i : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hfactor i
    _ = Real.exp (∑ i : Fin m, (C - nu * w i) * (e i : ℝ)) := by
      simpa using (exp_prod_sum (Finset.univ : Finset (Fin m))
        (fun i => (C - nu * w i) * (e i : ℝ)))
    _ = Real.exp (C * (∑ i : Fin m, (e i : ℝ)) -
        nu * (∑ i : Fin m, w i * (e i : ℝ))) := by
      congr 1
      simp only [Finset.sum_sub_distrib, sub_mul, ← mul_assoc, Finset.mul_sum]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_exponent_budget (763b64d9-a686-4834-83bf-b360a096f141)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_exponent_budget {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) :
    (Real.log (2 * (d.K : ℝ)) + nu) *
        (∑ i : Fin d.m, ((t.1.1 i - r.2.1 i.succ - t.2.1 i : ℕ) : ℝ)) -
      nu * (∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i *
          ((t.1.1 i - r.2.1 i.succ - t.2.1 i : ℕ) : ℝ)) ≤
      -nu * (weight d t.1 - ∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
      H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar) := by
  classical
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  let a : Fin d.m → ℕ := t.1.1
  let u : Fin d.m → ℕ := fun i => r.2.1 i.succ
  let b : Fin d.m → ℕ := fun i => (t.2.1 i : ℕ)
  let e : Fin d.m → ℕ := fun i => a i - u i - b i
  let T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0
  let C : ℝ := Real.log (2 * (d.K : ℝ)) + nu
  have hw (i : Fin d.m) : d.wstar ≤ w i := by
    calc
      d.wstar ≤ d.x (i.val + 1) := d.wstar_lower i
      _ = w i := by
        simpa only [w, MatrixArithmetic.logWeights, finiteDenominators] using d.x_log i.val
  have hw0 (i : Fin d.m) : 0 ≤ w i := d.wstar_pos.le.trans (hw i)

  -- The column simplex bounds the total remaining exponent mass.
  have hcol : (∑ i : Fin d.m, w i * (a i : ℝ)) ≤ H := by
    have hm : a ∈ realWeightedSimplex w H := t.1.property
    exact (Finset.mem_filter.mp hm).2
  have hmass : (∑ i : Fin d.m, (e i : ℝ)) ≤ H / d.wstar := by
    apply (le_div_iff₀ d.wstar_pos).mpr
    have hm : d.wstar * (∑ i : Fin d.m, (e i : ℝ)) ≤
        ∑ i : Fin d.m, w i * (a i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hea : e i ≤ a i := by
        dsimp only [e]
        omega
      calc
        d.wstar * (e i : ℝ) ≤ w i * (e i : ℝ) :=
          mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
        _ ≤ w i * (a i : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hea) (hw0 i)
    nlinarith only [hm, hcol]

  -- The support budget and ceiling inequality control the weighted tail.
  have hrow : (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
      (∑ i : Fin d.m, (w i / (d.base.theta : ℝ)) * (u i : ℝ)) < H := by
    have hh : (∑ j : Fin (d.m + 1),
        InterpolationMatrix.rowWeights d.v0 d.base.theta w j * (r.2.1 j : ℝ)) < H :=
      (Finset.mem_filter.mp r.2.property).2
    rw [Fin.sum_univ_succ] at hh
    simpa [InterpolationMatrix.rowWeights, u] using hh
  have hrow0 : (d.v0 : ℝ) * (r.2.1 0 : ℝ) ≤ H := by
    have hrest : 0 ≤ ∑ i : Fin d.m,
        (w i / (d.base.theta : ℝ)) * (u i : ℝ) :=
      Finset.sum_nonneg fun i hi =>
        mul_nonneg (div_nonneg (hw0 i) d.base.theta_pos.le) (Nat.cast_nonneg _)
    linarith only [hrow, hrest]
  have hbudget : (∑ i : Fin d.m, (T i : ℝ) * (b i : ℝ)) ≤ (r.2.1 0 : ℝ) := by
    have hs : (∑ i : Fin d.m, (T i : ℝ) * (b i : ℝ)) ≤
        ((t.2.2 : ℕ) : ℝ) := by
      exact_mod_cast hsupport
    have hl : (t.2.2 : ℕ) ≤ r.2.1 0 := Nat.le_of_lt_succ t.2.2.isLt
    exact hs.trans (by exact_mod_cast hl)
  have hT (i : Fin d.m) : d.F0 * w i ≤ (d.v0 : ℝ) * (T i : ℝ) := by
    have hc : d.F0 * w i / (d.v0 : ℝ) ≤ (T i : ℝ) := Nat.le_ceil _
    have hm := (div_le_iff₀ d.v0_pos).mp hc
    nlinarith only [hm]
  have htail : (∑ i : Fin d.m, w i * (b i : ℝ)) ≤ H / d.F0 := by
    have hFT : d.F0 * (∑ i : Fin d.m, w i * (b i : ℝ)) ≤
        (d.v0 : ℝ) * (∑ i : Fin d.m, (T i : ℝ) * (b i : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hm := mul_le_mul_of_nonneg_right (hT i)
        (Nat.cast_nonneg (b i) : (0 : ℝ) ≤ (b i : ℝ))
      nlinarith only [hm]
    have hv := mul_le_mul_of_nonneg_left hbudget d.v0_pos.le
    apply (le_div_iff₀ d.F0_pos).mpr
    nlinarith only [hFT, hv, hrow0]

  -- Natural subtraction yields a lower bound, even when a row coordinate exceeds a.
  have hdecomp : weight d t.1 - (∑ i : Fin d.m, w i * (u i : ℝ)) -
      (∑ i : Fin d.m, w i * (b i : ℝ)) ≤
      ∑ i : Fin d.m, w i * (e i : ℝ) := by
    calc
      weight d t.1 - (∑ i : Fin d.m, w i * (u i : ℝ)) -
          (∑ i : Fin d.m, w i * (b i : ℝ)) =
          ∑ i : Fin d.m, w i * ((a i : ℝ) - (u i : ℝ) - (b i : ℝ)) := by
        change (∑ i : Fin d.m, w i * (a i : ℝ)) -
          (∑ i : Fin d.m, w i * (u i : ℝ)) -
          (∑ i : Fin d.m, w i * (b i : ℝ)) = _
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin d.m, w i * (e i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hn : a i ≤ u i + b i + e i := by
          dsimp only [e]
          omega
        have hr : (a i : ℝ) ≤ (u i : ℝ) + (b i : ℝ) + (e i : ℝ) := by
          exact_mod_cast hn
        exact mul_le_mul_of_nonneg_left (by linarith only [hr]) (hw0 i)

  have hC : 0 ≤ C := by
    have hK : (1 : ℝ) ≤ (d.K : ℝ) := by exact_mod_cast d.K_pos
    have hlog : 0 ≤ Real.log (2 * (d.K : ℝ)) :=
      Real.log_nonneg (by linarith only [hK])
    exact add_nonneg hlog hnu
  have hm := mul_le_mul_of_nonneg_left hmass hC
  have ht := mul_le_mul_of_nonneg_left htail hnu
  have hd := mul_le_mul_of_nonneg_left hdecomp hnu
  change C * (∑ i : Fin d.m, (e i : ℝ)) -
      nu * (∑ i : Fin d.m, w i * (e i : ℝ)) ≤
    -nu * (weight d t.1 - ∑ i : Fin d.m, w i * (u i : ℝ)) +
      H * (nu / d.F0 + C / d.wstar)
  have heq : H * (nu / d.F0 + C / d.wstar) =
      nu * (H / d.F0) + C * (H / d.wstar) := by ring
  rw [heq]
  nlinarith only [hm, ht, hd]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds (760d3b56-c46a-405c-94ca-c66c7b058488)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ))
    (hcenter :
      ∀ i : Fin d.m,
        ‖((r.1.val : ℂ) *
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I))‖ ≤
          Real.exp
            (Real.log (2 * (d.K : ℝ)) + nu -
              nu * MatrixArithmetic.logWeights (finiteDenominators d) i)) :
    ‖∏ i : Fin d.m,
      (((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))‖ ≤
      Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by
  let z : Fin d.m → ℂ := fun i =>
    (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)
  let w : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteDenominators d)
  let e : Fin d.m → ℕ := fun i => t.1.1 i - r.2.1 i.succ - t.2.1 i
  let C : ℝ := Real.log (2 * (d.K : ℝ)) + nu
  have hK : (1 : ℝ) ≤ (d.K : ℝ) := by
    exact_mod_cast d.K_pos
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (Real.log_nonneg (by nlinarith)) hnu
  have hagg :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_weighted_product
      z w e C nu hnu hC (by
        intro i
        simpa [z, w, C] using hcenter i)
  have hbudget :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds_exponent_budget
      d hnu hH r t hsupport
  calc
    ‖∏ i : Fin d.m, (z i) ^ (e i)‖ ≤
        Real.exp (C * (∑ i : Fin d.m, (e i : ℝ)) -
          nu * (∑ i : Fin d.m, w i * (e i : ℝ))) := by
      exact hagg
    _ ≤ Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by
      apply Real.exp_le_exp.mpr
      simpa [z, w, e, C, weight] using hbudget
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_estimate_of_tail_support (2e7580d0-7019-4868-9876-875fbd35a525)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_estimate_of_tail_support
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hsupport :
      (∑ i : Fin d.m,
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
          (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) :
    ‖∏ i : Fin d.m,
      (((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))‖ ≤
      Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) := by
  apply OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_product_aggregate_of_center_factor_bounds
    d hnu hH r t hsupport
  intro i
  exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_factor_bound_of_approximation
    d hnu hH r t i
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support (c4b94905-9647-41ef-8bc4-afb44639d101)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

private theorem coeff_prod_pow_support_aux
    {ι : Type*} [Fintype ι] (T k : ι → ℕ) (f : ι → PowerSeries ℂ)
    (hf : ∀ i n, n < T i → PowerSeries.coeff n (f i) = 0)
    (n : ℕ) (hne : PowerSeries.coeff n (∏ i, (f i) ^ k i) ≠ 0) :
    (∑ i, T i * k i) ≤ n := by
  classical
  have hord (i : ι) : (T i : ℕ∞) ≤ (f i).order :=
    PowerSeries.nat_le_order (f i) (T i) (hf i)
  have hpow (i : ι) : ((T i * k i : ℕ) : ℕ∞) ≤ ((f i) ^ k i).order := by
    calc
      ((T i * k i : ℕ) : ℕ∞) = k i • (T i : ℕ∞) := by
        rw [nsmul_eq_mul, Nat.cast_mul]
        exact mul_comm _ _
      _ ≤ k i • (f i).order := nsmul_le_nsmul_right (hord i) (k i)
      _ ≤ ((f i) ^ k i).order := PowerSeries.le_order_pow (f i) (k i)
  have hprod : ((∑ i, T i * k i : ℕ) : ℕ∞) ≤
      (∏ i, (f i) ^ k i).order := by
    calc
      ((∑ i, T i * k i : ℕ) : ℕ∞) =
          ∑ i, ((T i * k i : ℕ) : ℕ∞) := by rw [Nat.cast_sum]
      _ ≤ ∑ i, ((f i) ^ k i).order := Finset.sum_le_sum (fun i _ => hpow i)
      _ ≤ (∏ i, (f i) ^ k i).order :=
        PowerSeries.le_order_prod (fun i => (f i) ^ k i) Finset.univ
  exact ENat.natCast_le_natCast.mp (hprod.trans (PowerSeries.order_le n hne))

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hne : PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ)) ≠ 0) :
    (∑ i : Fin d.m,
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
        (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ) := by
  refine coeff_prod_pow_support_aux
    (T := fun i => MatrixArithmetic.truncationOrders
      (finiteDenominators d) d.F0 d.v0 i)
    (k := fun i => (t.2.1 i : ℕ))
    (f := fun i =>
      (PowerSeries.trunc
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
        (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ)
    ?_ (t.2.2 : ℕ) hne
  intro i n hn
  rw [map_sub, PowerSeries.coeff_coe_trunc_of_lt hn, sub_self]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound (0aacb82f-e0cd-41ba-8b7c-52ef0e6c7c7a)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ ≤
      Real.exp (Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ)) := by
  let a : Fin d.m → ℕ := fun i => t.1.1 i
  let b : Fin d.m → ℕ := fun i => r.2.1 i.succ
  let c : Fin d.m → ℕ := fun i => t.2.1 i
  have hfactor (i : Fin d.m) :
      (a i).choose (b i) * (a i - b i).choose (c i) ≤ 4 ^ a i := by
    have hfirst : (a i).choose (b i) ≤ 2 ^ a i :=
      Nat.choose_le_two_pow _ _
    have hsecond : (a i - b i).choose (c i) ≤ 2 ^ a i :=
      (Nat.choose_le_two_pow _ _).trans
        (pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) (Nat.sub_le _ _))
    calc
      (a i).choose (b i) * (a i - b i).choose (c i) ≤
          2 ^ a i * 2 ^ a i := Nat.mul_le_mul hfirst hsecond
      _ = 4 ^ a i := by rw [← mul_pow]; rfl
  have hprod :
      (∏ i : Fin d.m, (a i).choose (b i) * (a i - b i).choose (c i)) ≤
        4 ^ (∑ i : Fin d.m, a i) := by
    calc
      (∏ i : Fin d.m, (a i).choose (b i) * (a i - b i).choose (c i)) ≤
          ∏ i : Fin d.m, 4 ^ a i :=
        Finset.prod_le_prod' (fun i _ => hfactor i)
      _ = 4 ^ (∑ i : Fin d.m, a i) :=
        Finset.prod_pow_eq_pow_sum Finset.univ a 4
  calc
    ‖((∏ i : Fin d.m,
        (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) : ℂ)‖ =
        ((∏ i : Fin d.m,
          (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) : ℝ) :=
      Complex.norm_natCast _
    _ ≤ ((4 ^ (∑ i : Fin d.m, a i) : ℕ) : ℝ) := Nat.cast_le.mpr hprod
    _ = (4 : ℝ) ^ (∑ i : Fin d.m, a i) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    _ = Real.exp (Real.log 4 * ∑ i : Fin d.m, (a i : ℝ)) := by
      rw [← Nat.cast_sum, mul_comm, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound (492c085c-67c3-44e6-b0bf-4787ad83b08b)

open scoped BigOperators
open OAI.PiExponent

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound
    {m : ℕ} (w : Fin m → ℝ) (H wstar : ℝ) (hwstar : 0 < wstar)
    (hw : ∀ i : Fin m, wstar ≤ w i) (a : Fin m → ℕ)
    (ha : a ∈ realWeightedSimplex w H) :
    (∑ i : Fin m, (a i : ℝ)) ≤ H / wstar := by
  classical
  unfold realWeightedSimplex at ha
  have hweighted : (∑ i : Fin m, w i * (a i : ℝ)) ≤ H :=
    (Finset.mem_filter.mp ha).2
  have hsum : wstar * (∑ i : Fin m, (a i : ℝ)) ≤ H := by
    calc
      wstar * (∑ i : Fin m, (a i : ℝ)) =
          ∑ i : Fin m, wstar * (a i : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin m, w i * (a i : ℝ) := by
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg (a i)))
      _ ≤ H := hweighted
  apply (le_div_iff₀ hwstar).2
  simpa only [mul_comm] using hsum
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound (49e484c4-5310-49ff-9ad0-8fa822eec869)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
  have h := d.wstar_lower i
  rw [d.x_log i.val] at h
  simpa [MatrixArithmetic.logWeights, finiteDenominators] using h
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound (6cb3b5ac-d4fe-40d4-8ae3-77b9c88c3acf)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    (∑ i : Fin d.m, (t.1.1 i : ℝ)) ≤ H / d.wstar := by
  exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound
    (MatrixArithmetic.logWeights (finiteDenominators d)) H d.wstar d.wstar_pos
    (by
      intro i
      exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound d i)
    t.1.1 t.1.2
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound (1ea7b4ab-3e5f-4a37-8a5d-d526c25e2264)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar)) := by
  have hprod :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_product_bound
      d hnu hH r t
  have hsum :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound
      d hnu hH r t
  have hlog : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
  have hexp : Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ) ≤
      H * (Real.log 4 / d.wstar) := by
    calc
      Real.log 4 * ∑ i : Fin d.m, (t.1.1 i : ℝ) ≤
          Real.log 4 * (H / d.wstar) := mul_le_mul_of_nonneg_left hsum hlog
      _ = H * (Real.log 4 / d.wstar) := by ring
  exact hprod.trans (Real.exp_le_exp.mpr hexp)
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_le_majorant (97b9d57b-2b96-4dca-afc3-cc1c540ae97e)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_le_majorant (N n : ℕ) :
    ‖PowerSeries.coeff n
      ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ)‖ ≤
    ‖PowerSeries.coeff n
      (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹))‖ := by
  by_cases h0 : n = 0
  · subst n
    simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log, PowerSeries.coeff_mk]
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    by_cases hcut : n < N
    · have htail : PowerSeries.coeff n
          ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) -
            PowerSeries.log ℂ) = 0 := by
        simp [PowerSeries.coeff_trunc, hcut]
      rw [htail]
      simpa using (norm_nonneg (PowerSeries.coeff n
        (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹))))
    · have htail : PowerSeries.coeff n
          ((PowerSeries.trunc N (PowerSeries.log ℂ) : PowerSeries ℂ) -
            PowerSeries.log ℂ) = - PowerSeries.coeff n (PowerSeries.log ℂ) := by
        simp [PowerSeries.coeff_trunc, hcut]
      rw [htail]
      simp [PowerSeries.coeff_log, PowerSeries.coeff_mk, h0,
        Complex.norm_div, Complex.norm_pow, Complex.norm_natCast, hn]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coefficientwise_majorant_products (fd6521bd-e234-414d-90ec-eaef6a5e2816)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

-- Keep the nonnegative real coefficient and the norm bound together, so that
-- multiplication carries both parts of the induction invariant.
private theorem majorant_one :
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (1 : PowerSeries ℂ) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (1 : PowerSeries ℂ)‖ ≤ x := by
  intro n
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_le_one, ?_, ?_⟩ <;> simp
  · refine ⟨0, le_rfl, ?_, ?_⟩ <;> simp [PowerSeries.coeff_one, hn]

private theorem majorant_mul
    {F G U V : PowerSeries ℂ}
    (hF : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n U = (x : ℂ) ∧ ‖PowerSeries.coeff n F‖ ≤ x)
    (hG : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n V = (x : ℂ) ∧ ‖PowerSeries.coeff n G‖ ≤ x) :
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (U * V) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (F * G)‖ ≤ x := by
  classical
  choose u hu hU hFu using hF
  choose v hv hV hGv using hG
  intro n
  refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p.1 * v p.2,
    Finset.sum_nonneg (fun p _ => mul_nonneg (hu p.1) (hv p.2)), ?_, ?_⟩
  · rw [PowerSeries.coeff_mul, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hU p.1, hV p.2, Complex.ofReal_mul]
  · rw [PowerSeries.coeff_mul]
    calc
      ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ ≤
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p.1 * v p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        exact mul_le_mul (hFu p.1) (hGv p.2) (norm_nonneg _) (hu p.1)

private theorem majorant_pow
    {B C : PowerSeries ℂ}
    (h : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n C = (x : ℂ) ∧ ‖PowerSeries.coeff n B‖ ≤ x)
    (q : ℕ) :
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (C ^ q) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (B ^ q)‖ ≤ x := by
  induction q with
  | zero => simpa only [pow_zero] using majorant_one
  | succ q ih => simpa only [pow_succ] using majorant_mul ih h

private theorem majorant_prod
    {α : Type*} (s : Finset α) (F G : α → PowerSeries ℂ) :
    (∀ i ∈ s, ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (G i) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (F i)‖ ≤ x) →
    ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (∏ i ∈ s, G i) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (∏ i ∈ s, F i)‖ ≤ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simpa only [Finset.prod_empty] using majorant_one
  | insert i s hi ih =>
    intro h
    have h₁ := h i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using majorant_mul h₁ h₂

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coefficientwise_majorant_products
    {m : ℕ} (C B : Fin m → PowerSeries ℂ)
    (q : Fin m → ℕ) (k : ℕ)
    (hC : ∀ i n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n (C i) = (x : ℂ))
    (hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n (C i)‖) :
    ‖PowerSeries.coeff k (∏ i : Fin m, B i ^ q i)‖ ≤
      ‖PowerSeries.coeff k (∏ i : Fin m, C i ^ q i)‖ := by
  have hbase (i : Fin m) : ∀ n, ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n (C i) = (x : ℂ) ∧
      ‖PowerSeries.coeff n (B i)‖ ≤ x := by
    intro n
    obtain ⟨x, hx, hCx⟩ := hC i n
    refine ⟨x, hx, hCx, ?_⟩
    calc
      ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n (C i)‖ := hB i n
      _ = x := by rw [hCx, Complex.norm_of_nonneg hx]
  have h := majorant_prod (Finset.univ : Finset (Fin m))
    (fun i => B i ^ q i) (fun i => C i ^ q i)
    (fun i _ => majorant_pow (hbase i) (q i))
  obtain ⟨x, hx, hCx, hBx⟩ := h k
  rw [hCx, Complex.norm_of_nonneg hx]
  exact hBx
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.powerSeries_coeff_product_pow_majorant (92539db6-6c10-4720-8380-6c89f0623f90)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.powerSeries_coeff_product_pow_majorant
    {m : ℕ} (L : PowerSeries ℂ) (B : Fin m → PowerSeries ℂ)
    (q : Fin m → ℕ) (k : ℕ)
    (hL : ∀ n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n L = (x : ℂ))
    (hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤ ‖PowerSeries.coeff n L‖) :
    ‖PowerSeries.coeff k (∏ i : Fin m, B i ^ q i)‖ ≤
      ‖PowerSeries.coeff k (L ^ (∑ i : Fin m, q i))‖ := by
  have h := coefficientwise_majorant_products
    (C := fun _ : Fin m => L) (B := B) (q := q) (k := k)
    (hC := by intro i n; exact hL n) (hB := hB)
  simpa [Finset.prod_pow_eq_pow_sum] using h
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_coeff_nonnegative (54e1263c-5034-45fd-bddc-d67508156296)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_coeff_nonnegative (n : ℕ) :
    ∃ x : ℝ, 0 ≤ x ∧
      PowerSeries.coeff n
        (PowerSeries.mk (fun j : ℕ => if j = 0 then 0 else (j : ℂ)⁻¹)) = (x : ℂ) := by
  refine ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [PowerSeries.coeff_mk, hn]
  · simp [PowerSeries.coeff_mk, hn, map_inv₀]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coeff_pow_eq_bounded_fin_tuple_sum_generic (426b330f-c8a3-47d1-b5ab-60afd9ebb17b)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coeff_pow_eq_bounded_fin_tuple_sum_generic (q k : ℕ) (f : ℕ → ℂ) :
    PowerSeries.coeff k ((PowerSeries.mk f) ^ q) =
      ∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i) := by
  classical
  have hpow : (PowerSeries.mk f) ^ q = ∏ _j : Fin q, PowerSeries.mk f := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk]
  have hle : ∀ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin q)) k, ∀ i, l i < k + 1 := by
    intro l hl i
    rw [Finset.mem_finsuppAntidiag] at hl
    obtain ⟨hs, -⟩ := hl
    rw [← hs]
    exact Nat.lt_succ_of_le (Finset.single_le_sum (f := fun j => l j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  refine Finset.sum_nbij' (fun l => fun i => if h : l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin q)) k
      then ⟨l i, hle l h i⟩ else 0)
    (fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dif_pos hl]
    exact (Finset.mem_finsuppAntidiag.mp hl).1
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    simpa using ha
  · intro l hl
    have hs := (Finset.mem_finsuppAntidiag.mp hl).1
    ext i
    simp [hs]
  · intro a ha
    have hm : Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)) ∈
        Finset.finsuppAntidiag (Finset.univ : Finset (Fin q)) k := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [Finset.mem_finsuppAntidiag]
      refine ⟨?_, by simp⟩
      simpa using ha
    have hs : ∑ i, ((a i : ℕ)) = k := by simpa using ha
    funext i
    simp [hs]
  · intro l hl
    have hs := (Finset.mem_finsuppAntidiag.mp hl).1
    simp [hs]

end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic (babd1206-ae5a-4a43-91f8-fa96c2fd128d)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
          (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i) := by
  classical
  symm
  apply Finset.sum_filter_of_ne
  intro a _ hne i
  by_contra h
  apply hne
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have : (a i : ℕ) = 0 := by omega
  rw [this, h0]

end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic (0ad6b240-92ab-4e57-8efd-8703c0241e4f)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic (q k : ℕ) (f : ℕ → ℂ) :
    (∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
        (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by
  classical
  have hinj : Function.Injective (fun (a : Fin q → Fin (k + 1)) (i : Fin q) => (a i : ℕ)) := by
    intro a b h
    funext i
    exact Fin.ext (congrFun h i)
  unfold logMajorantCompositions
  rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h), Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro a _
  simp only [Function.comp]
  exact and_comm

end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic (ec28cf27-38de-4577-93f9-c170cf6c3a49)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
      (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by
  calc
    (∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i)) =
        ∑ a ∈ ((Finset.univ : Finset (Fin q → Fin (k + 1))).filter
          (fun a => (∑ i : Fin q, (a i : ℕ)) = k)).filter
            (fun a => ∀ i : Fin q, 0 < (a i : ℕ)), ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_positive_bounded_sum_generic
        q k f h0
    _ = ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_bounded_sum_eq_logMajorant_composition_sum_generic
        q k f
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.logMajorant_power_coeff_eq_composition_sum_generic (c6a026b6-ff12-49ca-ba52-f83942d98e19)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.logMajorant_power_coeff_eq_composition_sum_generic (q k : ℕ) (f : ℕ → ℂ) (h0 : f 0 = 0) :
    PowerSeries.coeff k ((PowerSeries.mk f) ^ q) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) := by
  calc
    PowerSeries.coeff k ((PowerSeries.mk f) ^ q) =
        ∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
          (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coeff_pow_eq_bounded_fin_tuple_sum_generic
        q k f
    _ = ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, f (a i) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.bounded_sum_eq_logMajorant_composition_sum_generic
        q k f h0
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_eq_composition_sum (f27019a3-33a5-4896-b1a7-a445780f7925)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_eq_composition_sum (q k : ℕ) :
    PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q) =
      ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹) := by
  have hgeneric :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.logMajorant_power_coeff_eq_composition_sum_generic
      q k (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹) rfl
  calc
    PowerSeries.coeff k
        ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q) =
        ∑ a ∈ logMajorantCompositions q k,
          ∏ i : Fin q, (if a i = 0 then 0 else (a i : ℂ)⁻¹) := by
      simpa [PowerSeries.coeff_mk] using hgeneric
    _ = ∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.prod_congr rfl
      intro i hi
      have hpos : 0 < a i := (Finset.mem_filter.mp ha).2.1 i
      simp [Nat.ne_of_gt hpos]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_composition_reciprocal_sum_bound (78d815ba-6063-431a-9a9f-8c6715791040)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_composition_reciprocal_sum_bound (q k : ℕ) :
    ‖(∑ a ∈ logMajorantCompositions q k, ∏ i : Fin q, ((a i : ℂ)⁻¹))‖ ≤
      ((logMajorantCompositions q k).card : ℝ) := by
  classical
  let S := logMajorantCompositions q k
  have hpos (a : Fin q → ℕ) (ha : a ∈ S) (i : Fin q) : 0 < a i := by
    have hm : a ∈
        (((Finset.univ : Finset (Fin q → Fin (k + 1))).image
          (fun b i => (b i : ℕ))).filter
          (fun b => (∀ i, 0 < b i) ∧ ∑ i : Fin q, b i = k)) := by
      simpa [S, logMajorantCompositions] using ha
    exact (Finset.mem_filter.mp hm).2.1 i
  have hterm (a : Fin q → ℕ) (ha : a ∈ S) :
      ‖∏ i : Fin q, ((a i : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [norm_inv, Complex.norm_natCast]
      have hp : (0 : ℝ) < (a i : ℝ) := Nat.cast_pos.mpr (hpos a ha i)
      have hle : (1 : ℝ) ≤ (a i : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (hpos a ha i))
      exact (inv_le_one₀ hp).2 hle
  calc
    ‖∑ a ∈ S, ∏ i : Fin q, ((a i : ℂ)⁻¹)‖ ≤
        ∑ a ∈ S, ‖∏ i : Fin q, ((a i : ℂ)⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hterm a ha
    _ = (S.card : ℝ) := by simp [S]
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_composition_card (ee768a70-473b-48c5-bcf9-8819e4bdcce1)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_composition_card (q k : ℕ) :
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
      ((logMajorantCompositions q k).card : ℝ) := by
  rw [log_majorant_power_coeff_eq_composition_sum]
  exact log_majorant_composition_reciprocal_sum_bound q k
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.degenerate_positive_composition_cut_code (16cf32e2-c2b8-4e5a-a068-2e5caada1747)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.degenerate_positive_composition_cut_code (q k : ℕ) (h : q = 0 ∨ k = 0 ∨ q = 1) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by
  classical
  letI : Subsingleton {a // a ∈ logMajorantCompositions q k} := by
    constructor
    intro a b
    rcases h with hq | hk | hq
    · subst q
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    · subst k
      cases q with
      | zero =>
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
      | succ q' =>
          have parts (x : {a // a ∈ logMajorantCompositions (q' + 1) 0}) :
              (∀ i, 0 < x.val i) ∧ (∑ i : Fin (q' + 1), x.val i = 0) := by
            have hx := x.property
            simp only [logMajorantCompositions, Finset.mem_filter] at hx
            exact hx.2
          have hpos : 0 < ∑ i : Fin (q' + 1), a.val i :=
            Finset.sum_pos (fun i _ => (parts a).1 i) ⟨0, Finset.mem_univ _⟩
          exact False.elim ((Nat.ne_of_gt hpos) (parts a).2)
    · subst q
      have parts (x : {a // a ∈ logMajorantCompositions 1 k}) :
          (∀ i, 0 < x.val i) ∧ (∑ i : Fin 1, x.val i = k) := by
        have hx := x.property
        simp only [logMajorantCompositions, Finset.mem_filter] at hx
        exact hx.2
      have ha : a.val 0 = k := by simpa using (parts a).2
      have hb : b.val 0 = k := by simpa using (parts b).2
      apply Subtype.ext
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi, ha, hb]
  refine ⟨fun _ => ∅, ?_⟩
  intro a b _
  exact Subsingleton.elim a b
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.nontrivial_positive_composition_cut_code (26541077-d128-4fe7-940e-867612fb16c9)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.nontrivial_positive_composition_cut_code (q k : ℕ) (hq : 0 < q) (hk : 0 < k) (hqne : q ≠ 1) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by
  classical
  -- Realize a positive tuple as Mathlib's list-based composition.
  let toComposition : {a // a ∈ logMajorantCompositions q k} → Composition k :=
    fun a =>
      { blocks := List.ofFn a.val
        blocks_pos := by
          intro i hi
          obtain ⟨j, hj⟩ := (List.mem_ofFn' a.val i).mp hi
          rw [← hj]
          exact (Finset.mem_filter.mp a.property).2.1 j
        blocks_sum := by
          rw [List.sum_ofFn]
          exact (Finset.mem_filter.mp a.property).2.2 }
  have hcomp : Function.Injective toComposition := by
    intro a b hab
    apply Subtype.ext
    apply List.ofFn_injective
    exact congrArg Composition.blocks hab
  -- The standard cut equivalence records the proper boundaries minus one.
  let cuts : Composition k ≃ Finset (Fin (k - 1)) :=
    (compositionEquiv k).trans (compositionAsSetEquiv k)
  let inclusion : Fin (k - 1) ↪ Fin k := Fin.castLEEmb (Nat.sub_le k 1)
  refine ⟨fun a => (cuts (toComposition a)).map inclusion, ?_⟩
  intro a b hab
  apply hcomp
  apply cuts.injective
  exact (Finset.map_injective inclusion) hab
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_injective_cut_code (12384e68-be14-42fb-8aad-c28056c8098e)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_injective_cut_code (q k : ℕ) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by
  classical
  by_cases hdeg : q = 0 ∨ k = 0 ∨ q = 1
  · exact degenerate_positive_composition_cut_code q k hdeg
  · have hq : 0 < q := by omega
    have hk : 0 < k := by omega
    have hqne : q ≠ 1 := by omega
    exact nontrivial_positive_composition_cut_code q k hq hk hqne
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_card_le_two_pow (f2f2c1a3-7ce7-4bbd-b642-b5d636178e6d)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_card_le_two_pow (q k : ℕ) :
    (logMajorantCompositions q k).card ≤ 2 ^ k := by
  obtain ⟨f, hf⟩ :=
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_injective_cut_code q k
  calc
    (logMajorantCompositions q k).card =
        Fintype.card {a // a ∈ logMajorantCompositions q k} :=
      (Fintype.card_coe (logMajorantCompositions q k)).symm
    _ ≤ Fintype.card (Finset (Fin k)) := Fintype.card_le_of_injective f hf
    _ = 2 ^ k := by simp
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_two_pow (62d48af9-6b42-4390-835e-f62df6adddf6)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_two_pow (q k : ℕ) :
    ‖PowerSeries.coeff k
      ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
      (2 : ℝ) ^ k := by
  calc
    ‖PowerSeries.coeff k
        ((PowerSeries.mk (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)) ^ q)‖ ≤
        ((logMajorantCompositions q k).card : ℝ) :=
      OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_majorant_power_coeff_le_composition_card q k
    _ ≤ (2 : ℝ) ^ k := by
      exact_mod_cast
        OAI.PiExponent.DeterminantContradiction.FiniteTranslation.positive_composition_card_le_two_pow q k
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound (49110251-8a92-483d-9613-037fc6b4d9fd)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ))‖ ≤
      Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
  classical
  let L : PowerSeries ℂ := PowerSeries.mk
    (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)
  let B : Fin d.m → PowerSeries ℂ := fun i =>
    ((PowerSeries.trunc
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
      (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ)
  have hL : ∀ n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n L = (x : ℂ) := by
    exact log_majorant_coeff_nonnegative
  have hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤
      ‖PowerSeries.coeff n L‖ := by
    intro i n
    exact translation_log_tail_coeff_le_majorant
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) n
  have hprod := powerSeries_coeff_product_pow_majorant L B
    (fun i => (t.2.1 i : ℕ)) (t.2.2 : ℕ) hL hB
  have hlog := log_majorant_power_coeff_le_two_pow
    (∑ i : Fin d.m, (t.2.1 i : ℕ)) (t.2.2 : ℕ)
  have hrow :
      (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
        (∑ i : Fin d.m,
          (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
            (r.2.1 i.succ : ℝ)) < H := by
    have hsum :
        (∑ j : Fin (d.m + 1),
          InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
            (MatrixArithmetic.logWeights (finiteDenominators d)) j *
              (r.2.1 j : ℝ)) < H :=
      (Finset.mem_filter.mp r.2.property).2
    simpa only [Fin.sum_univ_succ, InterpolationMatrix.rowWeights,
      Fin.cases_zero, Fin.cases_succ] using hsum
  have hrest : 0 ≤
      ∑ i : Fin d.m,
        (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
          (r.2.1 i.succ : ℝ) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · apply div_nonneg
      · unfold MatrixArithmetic.logWeights
        exact Nat.cast_nonneg _
      · exact le_of_lt d.base.theta_pos
    · exact Nat.cast_nonneg _
  have hr0 : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith [hrow, hrest]
  have hk0 : (t.2.2 : ℕ) ≤ r.2.1 0 :=
    Nat.le_of_lt_succ t.2.2.isLt
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) :=
    le_trans (by exact_mod_cast hk0) hr0
  have hallow : (2 : ℝ) ^ (t.2.2 : ℕ) ≤
      Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
    calc
      (2 : ℝ) ^ (t.2.2 : ℕ) =
          Real.exp (((t.2.2 : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp ((H / (d.v0 : ℝ)) * Real.log 2) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hk (Real.log_nonneg (by norm_num)))
      _ = Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
        congr 1
        ring
  simpa only [L, B] using le_trans (le_trans hprod hlog) hallow
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_prefactor_bound (25b13752-f7e0-41dc-8a97-4ff2031cfdea)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_prefactor_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖(((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
      PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ)))‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by
  have hb := OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound
    d hnu hH r t
  have hc := OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
    d hnu hH r t
  rw [norm_mul]
  calc
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ *
        ‖PowerSeries.coeff (t.2.2 : ℕ)
          (∏ i : Fin d.m,
            ((PowerSeries.trunc
              (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
              (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
                (t.2.1 i : ℕ))‖
        ≤ Real.exp (H * (Real.log 4 / d.wstar)) *
            Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) :=
      mul_le_mul hb hc (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support_and_prefactor_estimate (b7dd2d56-47cf-402b-be39-8527f8b3e554)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support_and_prefactor_estimate
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r)
    (hne : PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ)) ≠ 0) :
    ((∑ i : Fin d.m,
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i *
        (t.2.1 i : ℕ)) ≤ (t.2.2 : ℕ)) ∧
    ‖(((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
      PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ)))‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by
  exact ⟨
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support
      d hnu hH r t hne,
    OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_prefactor_bound
      d hnu hH r t⟩
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_bound_each_row (81ebda5b-c226-4105-8f4a-587356aaf1ee)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_bound_each_row
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖scalar d r t‖ ≤ Real.exp
      (-nu * (weight d t.1 -
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
        H * d.translationError) := by
  let P : ℂ :=
    ((∏ i : Fin d.m, (t.1.1 i).choose (r.2.1 i.succ) *
      (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)
  let C : ℂ :=
    ∏ i : Fin d.m,
      (((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))
  let L : ℂ :=
    PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ))
  have hfac : scalar d r t = P * C * L := by rfl
  by_cases hL : L = 0
  · rw [hfac, hL, mul_zero, norm_zero]
    exact Real.exp_nonneg _
  have htail := translation_tail_support_and_prefactor_estimate d hnu hH r t hL
  have hcenter := center_product_estimate_of_tail_support d hnu hH r t htail.1
  have htailnorm := htail.2
  change ‖C‖ ≤ _ at hcenter
  change ‖P * L‖ ≤ _ at htailnorm
  rw [hfac]
  calc
    ‖P * C * L‖ = ‖P * L‖ * ‖C‖ := by
      rw [show P * C * L = (P * L) * C by ring, norm_mul]
    _ ≤ Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) *
        Real.exp (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) :=
        mul_le_mul htailnorm hcenter (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) + H * d.translationError) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [AdmissibleParameters.translationError]
        ring
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean (7f9e81a3-de02-4c00-939d-d86720b4aa06)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H,
      ∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) =
      (actualRowCount d H : ℝ) * H * actualMean d H := by
  classical
  have hzero : (fun _ : Fin (d.m + 1) => 0) ∈
      OAI.PiExponent.strictWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    simp [OAI.PiExponent.strictWeightedSimplex,
      OAI.PiExponent.realWeightedSimplex, hH.le, hH]
  let r : Row d H :=
    ⟨⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 1) d.K_pos⟩,
      ⟨(fun _ : Fin (d.m + 1) => 0), hzero⟩⟩
  have hcard : 0 < actualRowCount d H :=
    Fintype.card_pos_iff.mpr ⟨r⟩
  have hsum :
      (∑ r : Row d H,
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) =
        MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H := by
    unfold MatrixArithmetic.rowWeightedSum
    refine Finset.sum_congr rfl ?_
    intro r hr
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  rw [hsum]
  unfold actualMean actualRowCount MatrixArithmetic.meanRowWeight
  have hden :
      ((Fintype.card (Row d H) : ℝ) * H) ≠ 0 :=
    ne_of_gt (mul_pos (by exact_mod_cast hcard) hH)
  calc
    _ = (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H /
          ((Fintype.card (Row d H) : ℝ) * H)) *
          ((Fintype.card (Row d H) : ℝ) * H) :=
      (div_mul_cancel₀ _ hden).symm
    _ = _ := mul_comm _ _
end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_product_bound (a513ea30-1736-4a9b-9be1-0c8d2ff886e2)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_product_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (f : Family d H) :
    ‖∏ r : Row d H, scalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, weight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  classical
  rw [norm_prod]
  calc
    (∏ r : Row d H, ‖scalar d r (f r)‖) ≤
        ∏ r : Row d H,
          Real.exp (-nu * (weight d (f r).1 -
            ∑ i : Fin d.m,
              MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
            H * d.translationError) := by
      apply Finset.prod_le_prod
      · intro r hr
        exact norm_nonneg _
      · intro r hr
        exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_bound_each_row
          d hnu (H := H) hH r (f r)
    _ = Real.exp (∑ r : Row d H,
          (-nu * (weight d (f r).1 -
            ∑ i : Fin d.m,
              MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
            H * d.translationError)) := by rw [← Real.exp_sum]
    _ = Real.exp (-nu * ((∑ r : Row d H, weight d (f r).1) -
          (actualRowCount d H : ℝ) * H * actualMean d H) +
          (actualRowCount d H : ℝ) * H * d.translationError) := by
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean d hH]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
      ring
end

section
-- OAI.PiExponent.FinitePeriodCollision.analytic_collision_factor_bound (3ff69a88-721b-46a6-8c83-c6e69ebab695)

open scoped BigOperators Topology
open Complex Filter MeasureTheory
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

/-!
# The analytic collision factor bound

This file proves the analytic collision bound for Cauchy row tests of translated entire
functions: the determinant of the matrix of row tests is bounded by a factorial, the row orders
captured by `2 ^ (∑ ell r)`, a collision factor `s ^ (∑ choose(multiplicity, 2))` and a geometric
factor `(1 - s)⁻¹ ^ card`.  The proof ports the analytic collision estimate from the upstream
formalization into the `FinitePeriodCollision` definition bundle.
-/

namespace P2MCollisionPort

/-! ## Collision combinatorics -/

theorem p2m_choose_card_le_sum (s : Finset ℕ) : s.card.choose 2 ≤ ∑ d ∈ s, d := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by
      intro h
      exact (lt_irrefl a) (hmax a h)
    have hsub : s ⊆ Finset.range a := by
      intro x hx
      exact Finset.mem_range.mpr (hmax x hx)
    have hcard : s.card ≤ a := by
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rw [show s.card + 1 = s.card.succ from rfl,
      Nat.choose_succ_succ s.card 1, Nat.choose_one_right]
    exact Nat.add_le_add hcard ih

theorem p2m_choose_card_le_sum_of_injOn {ι : Type*} (s : Finset ι)
    (degree : ι → ℕ) (hinj : Set.InjOn degree (s : Set ι)) :
    s.card.choose 2 ≤ ∑ i ∈ s, degree i := by
  have h := p2m_choose_card_le_sum (s.image degree)
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at h
  exact h

/-- The multiplicity of a group value among the rows. -/
def p2m_multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

theorem p2m_sum_choose_multiplicity_le_sum_degree {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) (degree : ι → ℕ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups)
    (hinj : Set.InjOn (fun i => (group i, degree i)) (rows : Set ι)) :
    (∑ a ∈ groups, (p2m_multiplicity rows group a).choose 2) ≤
      ∑ i ∈ rows, degree i := by
  calc
    (∑ a ∈ groups, (p2m_multiplicity rows group a).choose 2) ≤
        ∑ a ∈ groups, ∑ i ∈ rows.filter (fun i => group i = a), degree i := by
      apply Finset.sum_le_sum
      intro a _
      apply p2m_choose_card_le_sum_of_injOn
      intro i hi j hj hdegree
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      apply hinj hi'.1 hj'.1
      exact Prod.ext (hi'.2.trans hj'.2.symm) hdegree
    _ = ∑ i ∈ rows, degree i :=
      Finset.sum_fiberwise_of_maps_to hgroups degree

theorem p2m_sum_choose_multiplicity_le_sum_degree_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (degree : ι → ℕ)
    (hinj : Function.Injective (fun i => (group i, degree i))) :
    (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) ≤ ∑ i, degree i := by
  exact p2m_sum_choose_multiplicity_le_sum_degree Finset.univ Finset.univ group degree
    (by simp) hinj.injOn

/-! ## Geometric series estimates -/

theorem p2m_sum_pow_fin_le_inv_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (N : ℕ) : (∑ k : Fin N, s ^ (k : ℕ)) ≤ (1 - s)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => s ^ k), ← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hs1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hs0 N)

theorem p2m_sum_pow_degree_assignments_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) =
      (∑ k : Fin N, s ^ (k : ℕ)) ^ Fintype.card ι := by
  classical
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin N) => s ^ (k : ℕ))]
  simp

theorem p2m_sum_pow_degree_assignments_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) ≤
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  rw [p2m_sum_pow_degree_assignments_eq]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => pow_nonneg hs0 _)
    (p2m_sum_pow_fin_le_inv_one_sub hs0 hs1 N) _

theorem p2m_collision_geometric_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f ∈ (Finset.univ : Finset (ι → Fin N)).filter
        (fun f => Function.Injective (fun i => (group i, (f i : ℕ)))),
      (s * s) ^ (∑ i, (f i : ℕ))) ≤
      s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let C := ∑ a, (p2m_multiplicity Finset.univ group a).choose 2
  have hpoint : ∀ f ∈ good,
      (s * s) ^ (∑ i, (f i : ℕ)) ≤ s ^ C * s ^ (∑ i, (f i : ℕ)) := by
    intro f hf
    have hinj := (Finset.mem_filter.mp hf).2
    have hdeg : C ≤ ∑ i, (f i : ℕ) :=
      p2m_sum_choose_multiplicity_le_sum_degree_univ group (fun i => (f i : ℕ)) hinj
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1.le hdeg)
      (pow_nonneg hs0 _)
  calc
    _ ≤ ∑ f ∈ good, s ^ C * s ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum hpoint
    _ = s ^ C * ∑ f ∈ good, s ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ s ^ C * ∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs0 C)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro f _ _
      exact pow_nonneg hs0 _
    _ ≤ _ := mul_le_mul_of_nonneg_left (p2m_sum_pow_degree_assignments_le hs0 hs1 N)
      (pow_nonneg hs0 C)

/-! ## Cauchy coefficient and row-test estimates -/

noncomputable def p2m_normalizedTaylorCoeff (f : ℂ → ℂ) (R : ℝ) (d : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))

theorem p2m_norm_normalizedTaylorCoeff_le {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
    ‖p2m_normalizedTaylorCoeff f R d‖ ≤ D := by
  unfold p2m_normalizedTaylorCoeff
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * D) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, norm_inv, hzR, div_self (ne_of_gt hR),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (hD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by field_simp

theorem p2m_norm_rowTest_le {f : ℂ → ℂ} {D : ℝ}
    (hD : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f t‖ ≤ D) (ell : ℕ) :
    ‖rowTest ell f‖ ≤ (2 : ℝ) ^ ell * D := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem p2m_norm_shifted_log_div_le_half {center t : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

theorem p2m_norm_rowTest_shifted_power_le {center : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  apply p2m_norm_rowTest_le
  intro t ht
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) (p2m_norm_shifted_log_div_le_half hR hc _)
  simpa only [Metric.mem_sphere, dist_zero_right] using ht.le

/-- The terms `cauchyPowerSeries f 0 R d (fun _ => z)` are the normalized Taylor coefficients
multiplied by `(z / R) ^ d`. -/
theorem p2m_cauchyPowerSeries_const_eq (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (z : ℂ) (d : ℕ) :
    cauchyPowerSeries f 0 R d (fun _ => z) =
      p2m_normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  rw [p2m_normalizedTaylorCoeff, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [div_pow, div_eq_mul_inv]
  field_simp

theorem p2m_hasSum_normalizedTaylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) (z : ℂ) :
    HasSum (fun d => p2m_normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d) (f z) := by
  have hs : HasSum (fun d => cauchyPowerSeries f 0 (R : ℝ) d (fun _ => z)) (f z) := by
    have h := (hf.hasFPowerSeriesOnBall 0 hR).hasSum (y := z) (by simp)
    simpa only [zero_add] using h
  have heq : (fun d => cauchyPowerSeries f 0 (R : ℝ) d (fun _ => z)) =
      (fun d => p2m_normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d) := by
    funext d
    exact p2m_cauchyPowerSeries_const_eq f (by exact_mod_cast hR) z d
  rw [heq] at hs
  exact hs

/-! ## Row-test series of dominated convergent families -/

theorem p2m_hasSum_rowTest {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {bound : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n z, z ∈ Metric.sphere (0 : ℂ) (1 / 2) → ‖F n z‖ ≤ bound n)
    (hsum : Summable bound)
    (hpoint : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), HasSum (fun n => F n z) (f z))
    (ell : ℕ) : HasSum (fun n => rowTest ell (F n)) (rowTest ell f) := by
  simp only [rowTest, cauchyPowerSeries_apply]
  apply HasSum.const_smul
  change HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • F n (circleMap 0 (1 / 2) θ)))
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • f (circleMap 0 (1 / 2) θ)))
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => (2 : ℝ) ^ ell * bound n)
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [deriv_circleMap]
    exact (by fun_prop)
  · intro n
    apply Eventually.of_forall
    intro θ _
    have hb := hbound n (circleMap 0 (1 / 2) θ) (circleMap_mem_sphere 0 (by norm_num) θ)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_I, mul_one, sub_zero,
      norm_pow, norm_div, norm_one, norm_inv, norm_circleMap_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div, inv_div, div_one]
    calc
      _ = (2 : ℝ) ^ ell * ‖F n (circleMap 0 (1 / 2) θ)‖ := by ring
      _ ≤ (2 : ℝ) ^ ell * bound n := mul_le_mul_of_nonneg_left hb (by positivity)
  · exact Eventually.of_forall fun _ _ => hsum.mul_left _
  · simpa only [tsum_mul_left] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (2 : ℝ) ^ ell * ∑' n, bound n)
        volume 0 (2 * Real.pi))
  · apply Eventually.of_forall
    intro θ _
    exact (((hpoint _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul _).const_smul _).const_smul _

theorem p2m_rowTest_const_mul (ell : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    rowTest ell (fun t => c * f t) = c * rowTest ell f := by
  simp only [rowTest, cauchyPowerSeries_apply, smul_eq_mul]
  have heq : (fun z : ℂ => (1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * (c * f z))) =
      (fun z : ℂ => c * ((1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * f z))) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

theorem p2m_hasSum_translated_row {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    {center : ℂ} (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum (fun d => rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
      p2m_normalizedTaylorCoeff f R d)
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by
  have h := p2m_hasSum_rowTest
    (F := fun d t => p2m_normalizedTaylorCoeff f R d *
      ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)
    (f := fun t => f (center + Complex.log (1 + t)))
    (bound := fun d => D * (1 / 2 : ℝ) ^ d)
    (by intro d; fun_prop) ?_ ?_ ?_ ell
  · convert h using 1
    funext d
    rw [p2m_rowTest_const_mul, mul_comm]
  · intro d t ht
    rw [norm_mul, norm_pow]
    apply mul_le_mul (p2m_norm_normalizedTaylorCoeff_le hR hfD d)
    · apply pow_le_pow_left₀ (norm_nonneg _) (p2m_norm_shifted_log_div_le_half hR hc _)
      simpa only [Metric.mem_sphere, dist_zero_right] using ht.le
    · positivity
    · exact hD
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left D
  · intro t _
    exact p2m_hasSum_normalizedTaylorCoeff hf hR _


/-! ## Determinant bounds -/

theorem p2m_det_finite_row_sum {ι κ δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] (group : ι → κ) (B : ι → δ → ℂ) (C : κ → δ → ι → ℂ) :
    Matrix.det (fun i j => ∑ d, B i d * C (group i) d j) =
      ∑ f : ι → δ, (∏ i, B i (f i)) *
        Matrix.det (fun i j => C (group i) (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i d => B i d • C (group i) d)
  calc
    _ = Matrix.det (fun i => ∑ d, B i d • C (group i) d) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : ι → δ, Matrix.det (fun i => B i (f i) • C (group i) (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C (group i) (f i) j)

theorem p2m_norm_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {D : ℝ} (hD : 0 ≤ D) (hA : ∀ i j, ‖A i j‖ ≤ D) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * D ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖σ.sign • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, D ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _index : ι, |D| := Finset.prod_le_prod
          (fun index _ => norm_nonneg _) (fun index _ => (hA (σ index) index).trans (le_abs_self D))
        _ = D ^ Fintype.card ι := by simp [abs_of_nonneg hD]
    _ = _ := by simp [Fintype.card_perm]

theorem p2m_finite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d) (N : ℕ) :
    ‖Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j)‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let Q := (Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      (Finset.prod_nonneg fun i _ => hL i)
  have hexpand : Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j) =
      ∑ f ∈ good, (∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j) := by
    rw [p2m_det_finite_row_sum group (fun i (d : Fin N) => B i d)
      (fun a (d : Fin N) j => C a d j)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hn : ¬ Function.Injective (fun i => (group i, (f i : ℕ))) := by
      simpa [good] using hf
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hn
    have hg : group i = group j := congrArg Prod.fst hij
    have hd : (f i : ℕ) = (f j : ℕ) := congrArg Prod.snd hij
    have hz : Matrix.det (fun r c => C (group r) (f r) c) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext c
      simp only [hg, hd]
    simp [hz]
  have hterm (f : ι → Fin N) :
      ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ ≤
        Q * (s * s) ^ (∑ i, (f i : ℕ)) := by
    have hbp : (∏ i, ‖B i (f i)‖) ≤ ∏ i, L i * (s * s) ^ (f i : ℕ) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hB i (f i))
    have hcp := p2m_norm_det_le_factorial_mul_pow
      (fun i j => C (group i) (f i) j) hD (fun i j => hC _ _ _)
    rw [norm_mul, norm_prod]
    calc
      _ ≤ (∏ i, L i * (s * s) ^ (f i : ℕ)) *
          ((Fintype.card ι).factorial * D ^ Fintype.card ι) :=
        mul_le_mul hbp hcp (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
          mul_nonneg (hL i) (pow_nonneg (mul_self_nonneg s) _))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        dsimp [Q]
        ring
  rw [hexpand]
  calc
    _ ≤ ∑ f ∈ good,
        ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f ∈ good, Q * (s * s) ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum (fun f _ => hterm f)
    _ = Q * ∑ f ∈ good, (s * s) ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ Q * (s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι) :=
      mul_le_mul_of_nonneg_left (p2m_collision_geometric_sum_le group hs0 hs1 N) hQ
    _ = _ := by dsimp [Q]; ring

/-! ## Passage to infinite determinantal expansions -/

theorem p2m_norm_det_le_of_entrywise_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hlim : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (T i j)))
    (hbound : ∀ N, ‖(A N).det‖ ≤ B) : ‖T.det‖ ≤ B := by
  have hmatrix : Tendsto A atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (hlim i)
  have hdet : Tendsto (fun N => (A N).det) atTop (𝓝 T.det) :=
    (continuous_id.matrix_det.tendsto T).comp hmatrix
  exact le_of_tendsto' hdet.norm hbound

theorem p2m_norm_det_le_of_entrywise_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ℕ → ι → ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => C i d j) (T i j))
    (hbound : ∀ N, ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, C i d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact p2m_norm_det_le_of_entrywise_limit
    (fun N i j => ∑ d ∈ Finset.range N, C i d j) T
    (fun i j => (hsum i j).tendsto_sum_nat) hbound

theorem p2m_norm_det_le_of_tested_series_hasSum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (group : ι → κ) (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => test i d * coeff (group i) d j) (T i j))
    (hbound : ∀ N,
      ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, test i d * coeff (group i) d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact p2m_norm_det_le_of_entrywise_hasSum
    (fun i d j => test i d * coeff (group i) d j) T hsum hbound

theorem p2m_infinite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (p2m_multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  apply p2m_norm_det_le_of_tested_series_hasSum group C B T hsum
  intro N
  have hmatrix : (fun i j => ∑ d ∈ Finset.range N, B i d * C (group i) d j) =
      (fun i j => ∑ d : Fin N, B i d * C (group i) d j) := by
    funext i j
    exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => B i d * C (group i) d j) N).symm
  rw [hmatrix]
  exact p2m_finite_collision_bound group B C D s L hD hs0 hs1
    hL hC hB N

end P2MCollisionPort

open P2MCollisionPort

/-- **Analytic collision factor bound.**  Entire column functions bounded by `D` on the circle of
radius `R`, whose translated logarithmic tests have centers in the half-radius region, satisfy the
explicit factorial, row-order and within-group collision determinant estimate. -/
theorem OAI.PiExponent.FinitePeriodCollision.analytic_collision_factor_bound
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ)
    (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hss : s * s = 1 / 2)
    (hf : ∀ b c, Differentiable ℂ (f b c))
    (hfD : ∀ b c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f b c z‖ ≤ D)
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
      s ^ (∑ b : κ,
        (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  let B : ι → ℕ → ℂ := fun i d => rowTest (ell i)
    (fun t => ((center i + Complex.log (1 + t)) / (R : ℂ)) ^ d)
  let C : κ → ℕ → ι → ℂ := fun a d j => p2m_normalizedTaylorCoeff (f a j) R d
  have hb := p2m_infinite_collision_bound (group := group) (B := B) (C := C) (D := D) (s := s)
    (L := fun i => (2 : ℝ) ^ ell i) hD hs0 hs1 (fun _ => by positivity)
    (fun a d j => p2m_norm_normalizedTaylorCoeff_le (by exact_mod_cast hR) (hfD a j) d)
    (fun i d => by
      dsimp only [B]
      rw [hss]
      exact p2m_norm_rowTest_shifted_power_le (by exact_mod_cast hR) (hc i) (ell i) d)
    (T := fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))
    (fun i j => p2m_hasSum_translated_row (hf (group i) j) hR hD (hfD (group i) j) (hc i) (ell i))
  simpa only [Finset.prod_pow_eq_pow_sum, p2m_multiplicity] using hb
end

section
-- OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support (1ef632e4-993c-41e0-b786-9a25a6ea93a3)

open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support
    {m : ℕ} (a : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    ∀ (i : Fin m) (s : Fin m →₀ ℕ),
      ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff s ≠ 0 →
        ∀ j : Fin m, s j ≠ 0 → j = i := by
  intro i s hs j hj
  set p : MvPolynomial (Fin m) (PowerSeries ℂ) :=
    MvPolynomial.C (b i) + MvPolynomial.X i with hp_def
  -- The single factor `C (b i) + X i` lives on the coordinate axis through `i`.
  have hp : ∀ t : Fin m →₀ ℕ, p.coeff t ≠ 0 → ∀ j : Fin m, t j ≠ 0 → j = i := by
    intro t ht j hj
    by_contra hji
    apply ht
    have h0 : t ≠ 0 := by intro h; rw [h] at hj; simp at hj
    have hst : Finsupp.single i 1 ≠ t := by
      intro h
      have hz : (Finsupp.single i 1 : Fin m →₀ ℕ) j = 0 :=
        Finsupp.single_eq_of_ne' (Ne.symm hji)
      rw [h] at hz
      exact hj hz
    rw [hp_def, MvPolynomial.coeff_add, MvPolynomial.coeff_C, MvPolynomial.coeff_X,
      if_neg (Ne.symm h0), if_neg hst, add_zero]
  -- Every power keeps the support on the same coordinate axis.
  have key : ∀ n : ℕ, ∀ t : Fin m →₀ ℕ,
      (p ^ n).coeff t ≠ 0 → ∀ j : Fin m, t j ≠ 0 → j = i := by
    intro n
    induction n with
    | zero =>
      intro t ht j hj
      have h0 : t ≠ 0 := by intro h; rw [h] at hj; simp at hj
      have hz : (p ^ 0).coeff t = 0 := by
        rw [pow_zero, MvPolynomial.coeff_one, if_neg (Ne.symm h0)]
      exact absurd hz ht
    | succ n ih =>
      intro t ht j hj
      by_contra hji
      apply ht
      rw [pow_succ, MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      have hxmem : x.1 + x.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      by_cases h1 : (p ^ n).coeff x.1 = 0
      · simp [h1]
      · by_cases h2 : p.coeff x.2 = 0
        · simp [h2]
        · exfalso
          have hxj1 : x.1 j = 0 := by
            by_contra hne
            exact hji (ih x.1 h1 j hne)
          have hxj2 : x.2 j = 0 := by
            by_contra hne
            exact hji (hp x.2 h2 j hne)
          have htj : t j = 0 := by
            rw [← hxmem, Finsupp.add_apply, hxj1, hxj2, add_zero]
          exact hj htj
  exact key (a i) s hs j hj
end

section
-- OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum (bade84e7-10c9-4f4f-8fe9-05ee452fde02)

open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum
    {σ : Type} [DecidableEq σ] {R : Type} [CommSemiring R]
    (p : MvPolynomial σ R) (i : σ)
    (hsupport : ∀ (s : σ →₀ ℕ), p.coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) :
    p = ∑ n ∈ p.support.image (fun s => s i),
      MvPolynomial.monomial (Finsupp.single i n)
        (p.coeff (Finsupp.single i n)) := by
  classical
  have hsingle : ∀ s ∈ p.support, s = Finsupp.single i (s i) := by
    intro s hs
    have hcoeff : p.coeff s ≠ 0 := by
      rwa [MvPolynomial.mem_support_iff] at hs
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · have hz : s j = 0 := by
        by_contra hne
        exact hj (hsupport s hcoeff j hne)
      rw [hz, Finsupp.single_eq_of_ne' (Ne.symm hj)]
  trans ∑ v ∈ p.support, MvPolynomial.monomial v (p.coeff v)
  · exact MvPolynomial.as_sum p
  have hinj : Set.InjOn (fun s : σ →₀ ℕ => s i) ↑p.support := by
    intro s hs t ht hst
    rw [hsingle s hs, hsingle t ht]
    exact congrArg (Finsupp.single i) hst
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro s hs
  have h := hsingle s hs
  conv_lhs => rw [h]
end

section
-- OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff (ec56064f-6f82-45a6-a8a8-6b1f86b39fbb)

theorem OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
    {σ : Type} [DecidableEq σ] {R : Type} [CommSemiring R]
    (p : MvPolynomial σ R) (i : σ)
    (hsupport : ∀ (s : σ →₀ ℕ), p.coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) (n : ℕ) :
    n ∈ p.support.image (fun s => s i) ↔
      p.coeff (Finsupp.single i n) ≠ 0 := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨s, hs, hsi⟩
    have hcoeff : p.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hsingle : s = Finsupp.single i n := by
      ext j
      by_cases hj0 : s j = 0
      · by_cases hji : j = i
        · subst j
          simp [hsi, hj0]
        · simp [Finsupp.single_apply, hji, hj0]
      · have hji : j = i := hsupport s hcoeff j hj0
        subst j
        simp [hsi]
    simpa [hsingle] using hcoeff
  · intro hcoeff
    apply Finset.mem_image.mpr
    refine ⟨Finsupp.single i n, MvPolynomial.mem_support_iff.mpr hcoeff, ?_⟩
    simp
end

section
-- OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum (ef3deb73-9470-49c7-8887-3e217b1df693)

open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (S : σ → Finset ℕ) (c : σ → ℕ → R) (A : σ → ℕ) :
    (∏ i, ∑ n ∈ S i,
      MvPolynomial.monomial (Finsupp.single i n) (c i n)).coeff
        (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, if A i ∈ S i then c i (A i) else 0 := by
  classical
  -- The finite support `Finsupp.equivFunOnFinite.symm x` is the sum of the
  -- single-coordinate finsupps.
  have hsum : ∀ x : σ → ℕ,
      (Finsupp.equivFunOnFinite.symm x : σ →₀ ℕ) = ∑ i, Finsupp.single i (x i) := by
    intro x
    ext j
    simp [Finsupp.single_apply]
  -- A product of single-coordinate monomials is the monomial at the summed finsupp.
  have hprod : ∀ x : σ → ℕ,
      (∏ i, MvPolynomial.monomial (Finsupp.single i (x i)) (c i (x i)) :
          MvPolynomial σ R) =
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm x) (∏ i, c i (x i)) := by
    intro x
    rw [hsum x]
    exact (MvPolynomial.monomial_sum_prod Finset.univ
      (fun i => Finsupp.single i (x i)) (fun i => c i (x i))).symm
  -- Expand the product of finite sums into a sum over choice functions.
  rw [Finset.prod_univ_sum]
  rw [MvPolynomial.coeff_sum]
  simp only [hprod, MvPolynomial.coeff_monomial]
  -- Only the choice function `x = A` can contribute.
  have hiff : ∀ x : σ → ℕ,
      Finsupp.equivFunOnFinite.symm x = Finsupp.equivFunOnFinite.symm A ↔ x = A := by
    intro x
    exact Finsupp.equivFunOnFinite.symm.injective.eq_iff
  simp only [hiff]
  rw [Finset.sum_ite_eq']
  simp only [Fintype.mem_piFinset]
  by_cases h : ∀ i, A i ∈ S i
  · simp only [if_pos h]
    exact Finset.prod_congr rfl fun i _ => (if_pos (h i)).symm
  · simp only [if_neg h]
    simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
end

section
-- OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support (0ab53423-e7f3-45e3-8355-2f1454996875)

open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (f : σ → MvPolynomial σ R) (A : σ → ℕ)
    (hsupport : ∀ (i : σ) (s : σ →₀ ℕ), (f i).coeff s ≠ 0 →
      ∀ j : σ, s j ≠ 0 → j = i) :
    (∏ i, f i).coeff (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, (f i).coeff (Finsupp.single i (A i)) := by
  classical
  let S : σ → Finset ℕ := fun i => (f i).support.image (fun s => s i)
  have hexp (i : σ) :
      f i = ∑ n ∈ S i,
        MvPolynomial.monomial (Finsupp.single i n)
          ((f i).coeff (Finsupp.single i n)) := by
    exact OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_as_sum
      (f i) i (fun s hs => hsupport i s hs)
  have hprod : (∏ i, f i) = ∏ i, ∑ n ∈ S i,
      MvPolynomial.monomial (Finsupp.single i n)
        ((f i).coeff (Finsupp.single i n)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hexp i
  rw [hprod]
  rw [OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
    S (fun i n => (f i).coeff (Finsupp.single i n)) A]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : A i ∈ S i
  · have hne : (f i).coeff (Finsupp.single i (A i)) ≠ 0 :=
      (OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
        (f i) i (fun s hs => hsupport i s hs) (A i)).mp hmem
    simp [hmem, hne]
  · have hz : (f i).coeff (Finsupp.single i (A i)) = 0 := by
      by_contra hne
      exact hmem ((OAI.PiExponent.FinitePeriodCollision.single_coordinate_support_mem_iff
        (f i) i (fun s hs => hsupport i s hs) (A i)).mpr hne)
    simp [hmem, hz]
end

section
-- OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors (3740ed69-880a-441f-bfdb-db58a3a4c8a5)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors
    {m : ℕ} (a A : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    (∏ i, (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (InterpolationMatrix.exponentVector A) =
      ∏ i, ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (Finsupp.single i (A i)) := by
  have hs := OAI.PiExponent.FinitePeriodCollision.coordinate_factor_support a b
  simpa [InterpolationMatrix.exponentVector] using
    (OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_support
      (σ := Fin m) (R := PowerSeries ℂ)
      (f := fun i => (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i) A hs)
end

section
-- OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff (bc8672bf-8fa6-4fcc-aed8-d1cabcd86d20)

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff
    {m : ℕ} (i : Fin m) (p : Polynomial (PowerSeries ℂ)) (k : ℕ) :
    (Polynomial.eval₂
        (MvPolynomial.C : PowerSeries ℂ →+* MvPolynomial (Fin m) (PowerSeries ℂ))
        (MvPolynomial.X i) p).coeff (Finsupp.single i k) = p.coeff k := by
  classical
  have hsingle (n : ℕ) :
      (Finsupp.single i n : Fin m →₀ ℕ) = Finsupp.single i k ↔ n = k := by
    constructor
    · intro h
      exact Finsupp.single_injective i h
    · intro h
      exact congrArg (Finsupp.single i) h
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
    hsingle, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro n hn hnk
    simp only [hnk, if_false]
  · intro hk
    simp [Polynomial.notMem_support_iff.mp hk]
end

section
-- OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial (1b97c74e-fc1c-4b81-b459-719a44f6e761)

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial
    {m : ℕ} (i : Fin m) (n k : ℕ) (b : Fin m → PowerSeries ℂ) :
    ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ n).coeff
        (Finsupp.single i k) =
      PowerSeries.C (((n.choose k : ℕ) : ℂ)) * b i ^ (n - k) := by
  have hp :
      Polynomial.eval₂ (MvPolynomial.C : PowerSeries ℂ →+* MvPolynomial (Fin m) (PowerSeries ℂ))
        (MvPolynomial.X i)
        ((Polynomial.X + Polynomial.C (b i)) ^ n) =
      (MvPolynomial.C (b i) + MvPolynomial.X i) ^ n := by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact congrArg (fun z => z ^ n) (add_comm (MvPolynomial.X i) (MvPolynomial.C (b i)))
  rw [← hp, OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff]
  rw [Polynomial.coeff_X_add_C_pow]
  simp [PowerSeries.C, mul_comm]
end

section
-- OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow (06c2e34f-a92d-4085-abd1-8562b2a1ea79)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow
    {m : ℕ} (a A : Fin m → ℕ) (b : Fin m → PowerSeries ℂ) :
    (∏ i, (MvPolynomial.C (b i) + MvPolynomial.X i) ^ a i).coeff
        (InterpolationMatrix.exponentVector A) =
      PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        ∏ i, (b i) ^ (a i - A i) := by
  rw [OAI.PiExponent.FinitePeriodCollision.coeff_product_coordinate_factors]
  simp_rw [OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial]
  simp [map_prod, Finset.prod_mul_distrib, mul_comm, mul_left_comm, mul_assoc]
end

section
-- OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff (2294f89d-37b6-43a1-bcaf-941d17eb29be)

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff
    {m : ℕ} (j h : ℕ) (a A : Fin m → ℕ) :
    (periodModel j h a).coeff (InterpolationMatrix.exponentVector A) =
      PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h *
        ∏ i, (PowerSeries.C ((j : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)) +
          PowerSeries.log ℂ) ^ (a i - A i) := by
  rw [periodModel, MvPolynomial.coeff_C_mul,
    OAI.PiExponent.FinitePeriodCollision.coeff_product_C_add_X_pow]
  ring
end

section
-- OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal (48fb6d1f-e424-4ea5-b2f9-90112cdbf8fa)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
      ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
      PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) := by
  exact congrArg (PowerSeries.coeff ell)
    (OAI.PiExponent.FinitePeriodCollision.periodModel_mv_coeff j h a A)
end

section
-- OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization (16ce493f-f06e-4210-b132-337faa70b799)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) =
      PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (∑ i, (a i - A i))) := by
  let B : PowerSeries ℂ :=
    PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
      PowerSeries.log ℂ
  have hprod : (∏ i : Fin m, B ^ (a i - A i)) =
      B ^ (∑ i : Fin m, (a i - A i)) :=
    Finset.prod_pow_eq_pow_sum Finset.univ _ _
  change PowerSeries.coeff ell
      (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h * ∏ i : Fin m, B ^ (a i - A i)) =
    PowerSeries.coeff ell
      (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
        (1 + PowerSeries.X) ^ h * B ^ (∑ i : Fin m, (a i - A i)))
  rw [hprod]
end

section
-- OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction (daa8517e-9760-461c-9bb3-e1ff149f9da8)

open scoped BigOperators
open Filter Topology

namespace P2MPeriodPort

/-- The coefficients of the formal logarithm are the Taylor coefficients of `log (1 + z)`:
`coeff n (log ℂ) = -(-1)^n/n`. -/
theorem p2m_coeff_log (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.log ℂ) = -(-1 : ℂ) ^ n / n := by
  rw [PowerSeries.coeff_log]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, map_div₀, map_pow]
    rw [pow_succ]
    simp

/-- The formal logarithm evaluates at `z` near the origin to `log (1 + z)`. -/
theorem p2m_hasSum_formal_log_eventually :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
        (Complex.log (1 + z)) := by
  have h := hasFPowerSeriesAt_clog_one_add
  rw [hasFPowerSeriesAt_iff] at h
  filter_upwards [h] with z hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, p2m_coeff_log,
    zero_add, mul_comm] using hz

theorem p2m_hasSum_coeff_C (b z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C b) * z ^ n) b := by
  convert hasSum_ite_eq 0 b using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem p2m_hasSum_coeff_X (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
  convert hasSum_ite_eq 1 z using 1
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem p2m_hasSum_coeff_add {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f + g) * z ^ n) (x + y) := by
  simpa only [map_add, add_mul] using hf.add hg

theorem p2m_hasSum_coeff_one (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

theorem p2m_hasSum_coeff_mul {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * z ^ n) (x * y) := by
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  rw [← heq] at hs
  rw [show (fun n => PowerSeries.coeff n (f * g) * z ^ n) =
      (fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff kl.1 f * z ^ kl.1 *
          (PowerSeries.coeff kl.2 g * z ^ kl.2)) by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    have he : a.1 + a.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
    rw [← he, pow_add]
    ring]
  exact hs

theorem p2m_hasSum_coeff_pow {f : PowerSeries ℂ} {x z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x) (d : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (f ^ d) * z ^ n) (x ^ d) := by
  induction d with
  | zero => simpa only [pow_zero] using p2m_hasSum_coeff_one z
  | succ d hd => simpa only [pow_succ] using p2m_hasSum_coeff_mul hd hf

/-- Near the origin, the period series evaluates to the period function. -/
theorem p2m_hasSum_period_eventually (b center : ℂ) (h d : ℕ) :
    ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => PowerSeries.coeff n
          (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
            (PowerSeries.C center + PowerSeries.log ℂ) ^ d) * z ^ n)
        (b * (1 + z) ^ h * (center + Complex.log (1 + z)) ^ d) := by
  filter_upwards [p2m_hasSum_formal_log_eventually] with z hz
  exact p2m_hasSum_coeff_mul
    (p2m_hasSum_coeff_mul (p2m_hasSum_coeff_C b z)
      (p2m_hasSum_coeff_pow
        (p2m_hasSum_coeff_add (p2m_hasSum_coeff_one z) (p2m_hasSum_coeff_X z)) h))
    (p2m_hasSum_coeff_pow (p2m_hasSum_coeff_add (p2m_hasSum_coeff_C center z) hz) d)

end P2MPeriodPort

theorem OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n =>
        PowerSeries.coeff n
          (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
            (PowerSeries.C center + PowerSeries.log ℂ) ^ d))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [P2MPeriodPort.p2m_hasSum_period_eventually b center h d] with z hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using hz
end

section
-- OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt (a0f3752d-185d-4109-b8c7-4dd46012010a)

open scoped NNReal
open OAI.PiExponent.FinitePeriodCollision

/-- The Cauchy row test extracts the corresponding coefficient of any formal power series that
represents `f` at the origin, provided `f` is complex differentiable on the closed disc of
radius `1/2`. -/
theorem OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt (ell : ℕ) (f : ℂ → ℂ) (s : PowerSeries ℂ)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 (1 / 2)))
    (hp : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n s)) 0) :
    rowTest ell f = PowerSeries.coeff ell s := by
  have hball := hd.hasFPowerSeriesOnBall (R := (1 / 2 : ℝ≥0)) (by norm_num)
  have heq := hball.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p ell (fun _ => 1)) heq
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
end

section
-- OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff (c2e889ed-475d-4031-8783-be2c74514e69)

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff
    (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (fun t => b * (1 + t) ^ h *
        (center + Complex.log (1 + t)) ^ d) =
      PowerSeries.coeff ell
        (PowerSeries.C b * (1 + PowerSeries.X) ^ h *
          (PowerSeries.C center + PowerSeries.log ℂ) ^ d) := by
  have hd : DifferentiableOn ℂ
      (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by
      have hz'' : ‖z‖ ≤ (1 / 2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      linarith
    have ha : AnalyticAt ℂ
        (fun t : ℂ => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d) z := by
      apply AnalyticAt.mul
      · fun_prop
      · exact (analyticAt_const.add
          ((analyticAt_const.add analyticAt_id).clog
            (Complex.mem_slitPlane_of_norm_lt_one hz'))).pow d
    exact ha.differentiableAt.differentiableWithinAt
  exact OAI.PiExponent.FinitePeriodCollision.rowTest_eq_coeff_of_hasFPowerSeriesAt
    ell _ _ hd
    (OAI.PiExponent.FinitePeriodCollision.hasFPowerSeriesAt_periodFunction b center h d)
end

section
-- OAI.PiExponent.FinitePeriodCollision.rowTest_congr_sphere (19348d73-b08a-463c-8511-39d7318304a1)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

/-- The Cauchy row test `rowTest ell f` is the normalized Taylor coefficient of `f` at the centre
`0`, measured on the circle of radius `1/2`; hence it only depends on the values of `f` on that
circle. -/
theorem OAI.PiExponent.FinitePeriodCollision.rowTest_congr_sphere {f g : ℂ → ℂ} (ell : ℕ)
    (hfg : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), f z = g z) :
    rowTest ell f = rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  change (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • f z =
    (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • g z
  rw [hfg z hz]
end

section
-- OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere (5aeee7af-704e-44b6-8606-68eb29bb6e8c)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere
    {m : ℕ} (j h : ℕ) (a A : Fin m → ℕ) :
    ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      (((∏ i, (a i).choose (A i) : ℕ) : ℂ) * (1 + t) ^ h *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ (∑ i, (a i - A i))) =
        analyticColumn h a A
          ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            Complex.log (1 + t)) := by
  intro t ht
  have ht_norm : ‖t‖ = (1 / 2 : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm] using ht
  have ht_ne : 1 + t ≠ 0 := by
    intro hz
    have hsum : t + 1 = 0 := by simpa [add_comm] using hz
    have ht_eq : t = -1 := (add_eq_zero_iff_eq_neg.mp hsum)
    rw [ht_eq, norm_neg, norm_one] at ht_norm
    norm_num at ht_norm
  have hperiod : Complex.exp ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa using Complex.exp_nat_mul_two_pi_mul_I j
  have hexp :
      Complex.exp ((h : ℂ) *
        (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + Complex.log (1 + t))) =
        (1 + t) ^ h := by
    calc
      Complex.exp ((h : ℂ) *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + Complex.log (1 + t))) =
          Complex.exp (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ h := by
              simpa using (Complex.exp_nat_mul
                (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + Complex.log (1 + t)) h)
      _ = (1 + t) ^ h := by
        rw [Complex.exp_add, hperiod, one_mul, Complex.exp_log ht_ne]
  unfold analyticColumn
  rw [hexp]
end

section
-- OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest (2ec46ddb-b84e-4ecb-9f2f-2326337370d4)
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          ∏ i, (PowerSeries.C ((j : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (a i - A i)) =
      rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          Complex.log (1 + t))) := by
  let b : ℂ := ((∏ i, (a i).choose (A i) : ℕ) : ℂ)
  let center : ℂ := (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  let d : ℕ := ∑ i, (a i - A i)
  have hf := OAI.PiExponent.FinitePeriodCollision.formal_coeff_series_normalization
    (j := j) (h := h) (ell := ell) (a := a) (A := A)
  have hc := OAI.PiExponent.FinitePeriodCollision.rowTest_periodFunction_coeff
    b center h d ell
  have hperiod := OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere
    j h a A
  have hcongr := OAI.PiExponent.FinitePeriodCollision.rowTest_congr_sphere
    (f := fun t => b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d)
    (g := fun t => analyticColumn h a A (center + Complex.log (1 + t)))
    ell hperiod
  dsimp [b, center, d] at hf hc hcongr ⊢
  calc
    _ = PowerSeries.coeff ell
        (PowerSeries.C (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
          (1 + PowerSeries.X) ^ h *
          (PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            PowerSeries.log ℂ) ^ (∑ i, (a i - A i))) := hf
    _ = rowTest ell (fun t => ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
          (1 + t) ^ h *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ (∑ i, (a i - A i))) := hc.symm
    _ = rowTest ell (fun t => analyticColumn h a A
          ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            Complex.log (1 + t))) := hcongr
end

section
-- OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_rowTest (7f5cffa2-ad5e-4a14-8651-8cb6f8a00b4d)

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_rowTest
    {m : ℕ} (j h ell : ℕ) (a A : Fin m → ℕ) :
    PowerSeries.coeff ell
      ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
      rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) := by
  calc
    PowerSeries.coeff ell
        ((periodModel j h a).coeff (InterpolationMatrix.exponentVector A)) =
        PowerSeries.coeff ell
          (PowerSeries.C
              (((∏ i, (a i).choose (A i) : ℕ) : ℂ)) *
            (1 + PowerSeries.X) ^ h *
            ∏ i, (PowerSeries.C ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
              PowerSeries.log ℂ) ^ (a i - A i)) :=
      OAI.PiExponent.FinitePeriodCollision.periodModel_coeff_eq_formal
        j h ell a A
    _ = rowTest ell (fun t => analyticColumn h a A
        ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + Complex.log (1 + t))) :=
      OAI.PiExponent.FinitePeriodCollision.formal_coeff_eq_rowTest
        j h ell a A
end

section
-- OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound (9f50dce1-ebeb-4368-a6e5-201121eeba52)

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound (n k : ℕ) :
    ((n.choose k : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by
  have hchoose : ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n k
  calc
    ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := hchoose
    _ = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
end

section
-- OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound (7dd99737-cc67-44d2-b1a7-7aa1c5d99de1)

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound
    {m : ℕ} (x b : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ Real.exp (b i)) :
    (∏ i, x i) ≤ Real.exp (∑ i, b i) := by
  calc
    (∏ i, x i) ≤ ∏ i, Real.exp (b i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact hx i
      · intro i hi
        exact h i
    _ = Real.exp (∑ i, b i) := by
      rw [← Real.exp_sum]
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound (495e5d84-b579-4258-844a-d637fd58d77a)

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound
    {m : ℕ} (a A : Fin m → ℕ) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤
      Real.exp ((∑ i, (a i : ℝ)) * Real.log 2) := by
  let x : Fin m → ℝ := fun i => (((a i).choose (A i) : ℕ) : ℝ)
  let b : Fin m → ℝ := fun i => (a i : ℝ) * Real.log 2
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    simp [x]
  have hfactor : ∀ i, x i ≤ Real.exp (b i) := by
    intro i
    simpa [x, b, mul_comm] using
      OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound
        (a i) (A i)
  have hprod :=
    OAI.PiExponent.FinitePeriodCollision.binomial_exp_product_bound x b hx hfactor
  simpa [x, b, Finset.sum_mul] using hprod
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound (9ce543d6-742c-46c2-ace6-164ede92b64a)

open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound
    (h : ℕ) {R : ℝ} (z : ℂ) (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp ((h : ℂ) * z)‖ ≤ Real.exp ((h : ℝ) * R) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    ((h : ℂ) * z).re = (h : ℝ) * z.re := by simp
    _ ≤ (h : ℝ) * R :=
      mul_le_mul_of_nonneg_left (Complex.re_le_norm z |>.trans hz)
        (Nat.cast_nonneg h)
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound (366c4f4e-da12-4a3a-9db7-503d0205ed1d)

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound
    {m : ℕ} (a A : Fin m → ℕ) {R : ℝ} (z : ℂ)
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖z ^ (∑ i, (a i - A i))‖ ≤
      Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by
  let n : ℕ := ∑ i, (a i - A i)
  let N : ℕ := ∑ i, a i
  have hn : n ≤ N := by
    dsimp [n, N]
    exact Finset.sum_le_sum fun i hi => Nat.sub_le (a i) (A i)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  calc
    ‖z ^ n‖ = ‖z‖ ^ n := norm_pow z n
    _ ≤ R ^ n := by
      exact pow_le_pow_left₀ (norm_nonneg z) hz n
    _ ≤ R ^ N := pow_le_pow_right₀ hR hn
    _ = (Real.exp (Real.log R)) ^ N := by
      rw [Real.exp_log hRpos]
    _ = Real.exp ((N : ℝ) * Real.log R) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by
      simp [N, Nat.cast_sum]
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound (7861891f-61f0-46c0-b8d8-d3576de4882e)

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp ((h : ℝ) * R +
        (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
  have hc := OAI.PiExponent.FinitePeriodCollision.analyticColumn_binomial_product_bound a A
  have he := OAI.PiExponent.FinitePeriodCollision.analyticColumn_exponential_factor_bound h z hR hz
  have hp := OAI.PiExponent.FinitePeriodCollision.analyticColumn_power_factor_bound a A z hR hz
  have hmul1 := mul_le_mul hc he (norm_nonneg _) (Real.exp_nonneg _)
  have hmul2 := mul_le_mul hmul1 hp (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  rw [analyticColumn, norm_mul, norm_mul]
  calc
    ‖((↑(∏ i, (a i).choose (A i)) : ℂ))‖ * ‖Complex.exp ((h : ℂ) * z)‖ * ‖z ^ (∑ i, (a i - A i))‖
        ≤ Real.exp ((∑ i, (a i : ℝ)) * Real.log 2) *
          Real.exp ((h : ℝ) * R) *
          Real.exp ((∑ i, (a i : ℝ)) * Real.log R) := by
            exact hmul2
    _ = Real.exp ((h : ℝ) * R + (∑ i, (a i : ℝ)) * (Real.log 2 + Real.log R)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ = Real.exp ((h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
          congr 1
          rw [Real.log_mul (by norm_num) (by linarith)]
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_factor_bound (29d8829c-1eb7-46e5-b110-0c9aee201899)

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_factor_bound
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ) (w : Fin m → ℝ)
    {R wstar : ℝ}
    (hR : 1 ≤ R) (hws : 0 < wstar) (hw : ∀ i, wstar ≤ w i)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar) := by
  have hunweighted :=
    OAI.PiExponent.FinitePeriodCollision.analyticColumn_unweighted_factor_bound
      h a A hR hz
  have hsum : (∑ i, (a i : ℝ)) ≤ (∑ i, w i * (a i : ℝ)) / wstar := by
    rw [le_div_iff₀' hws]
    calc
      wstar * (∑ i, (a i : ℝ)) = ∑ i, wstar * (a i : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, w i * (a i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg (a i))
  have hlog : 0 ≤ Real.log (2 * R) := by
    apply Real.log_nonneg
    nlinarith [hR]
  have hcompare :
      (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar := by
    calc
      (∑ i, (a i : ℝ)) * Real.log (2 * R) ≤
          ((∑ i, w i * (a i : ℝ)) / wstar) * Real.log (2 * R) :=
        mul_le_mul_of_nonneg_right hsum hlog
      _ = (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar := by ring
  exact hunweighted.trans (Real.exp_le_exp.mpr (add_le_add (le_refl ((h : ℝ) * R)) hcompare))
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_budget_exponent (02483996-008a-4e0a-8917-b6f32ecb8153)

open scoped BigOperators

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_budget_exponent
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (w : Fin m → ℝ)
    {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H) :
    Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar) ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  let S : ℝ := ∑ i, w i * (a i : ℝ)
  have ha (i : Fin m) : 0 ≤ (a i : ℝ) := by positivity
  have hterm (i : Fin m) : 0 ≤ w i * (a i : ℝ) :=
    mul_nonneg (le_trans (le_of_lt hws) (hw i)) (ha i)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => hterm i
  have hbud : w0 * (h : ℝ) + S ≤ H := by
    simpa [S] using hcol
  have hbase : 0 ≤ w0 * (h : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg h)
  have hSle : S ≤ H := by linarith [hbase]
  have hhbound : (h : ℝ) ≤ H / w0 := by
    rw [le_div_iff₀ hw0]
    nlinarith
  have hRpos : 0 ≤ R := le_trans (by norm_num) hR
  have hlog : 0 ≤ Real.log (2 * R) :=
    Real.log_nonneg (by nlinarith)
  have hfirst : (h : ℝ) * R ≤ H * (R / w0) := by
    calc
      (h : ℝ) * R ≤ (H / w0) * R := mul_le_mul_of_nonneg_right hhbound hRpos
      _ = H * (R / w0) := by ring
  have hquot : S / wstar ≤ H / wstar :=
    div_le_div_of_nonneg_right hSle (le_of_lt hws)
  have hsecond : S * Real.log (2 * R) / wstar ≤ H * Real.log (2 * R) / wstar := by
    calc
      S * Real.log (2 * R) / wstar = (S / wstar) * Real.log (2 * R) := by
        ring
      _ ≤ (H / wstar) * Real.log (2 * R) := mul_le_mul_of_nonneg_right hquot hlog
      _ = H * Real.log (2 * R) / wstar := by
        ring
  calc
    Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar)
        ≤ Real.exp (H * (R / w0) + H * Real.log (2 * R) / wstar) := by
          apply Real.exp_le_exp.mpr
          simpa [S] using add_le_add hfirst hsecond
    _ = Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
          congr 1
          ring
end

section
-- OAI.PiExponent.FinitePeriodCollision.analyticColumn_norm_le (b822879c-cebf-4676-9fdf-fb47b11fe741)

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.analyticColumn_norm_le
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ) (w : Fin m → ℝ)
    {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  apply le_trans (analyticColumn_factor_bound h a A w hR hws hw hz)
  exact analyticColumn_budget_exponent h a w hR hH hw0 hws hw hcol
end

section
-- OAI.PiExponent.FinitePeriodCollision.coefficient_determinant_factor_bound (a8ae2f06-a908-4d16-bb3c-7f8172be284c)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem OAI.PiExponent.FinitePeriodCollision.coefficient_determinant_factor_bound
    {m : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (transverse : κ → Fin m → ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * (h c : ℝ) + ∑ i, w i * (a c i : ℝ) ≤ H) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((periodModel (j r) (h c) (a c)).coeff
        (InterpolationMatrix.exponentVector (transverse (group r)))))‖ ≤
      (((Fintype.card ι).factorial : ℝ) *
        (Real.exp (H * (100 * (K : ℝ) / w0 +
          Real.log (200 * (K : ℝ)) / wstar))) ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
      (Real.exp (-Real.log 2 / 2)) ^
        (∑ b : κ, (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - Real.exp (-Real.log 2 / 2))⁻¹) ^ Fintype.card ι := by
  let R : NNReal := ⟨100 * (K : ℝ), by positivity⟩
  have hR : 0 < R := by
    change (0 : ℝ) < 100 * (K : ℝ)
    positivity
  have hK1 : (1 : ℝ) ≤ K := by
    exact_mod_cast (Nat.succ_le_iff.mpr hK)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    change (1 : ℝ) ≤ 100 * (K : ℝ)
    linarith
  have hs0 : 0 ≤ Real.exp (-Real.log 2 / 2) := (Real.exp_pos _).le
  have hs1 : Real.exp (-Real.log 2 / 2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hss : Real.exp (-Real.log 2 / 2) * Real.exp (-Real.log 2 / 2) =
      (1 / 2 : ℝ) := by
    rw [← Real.exp_add]
    have heq : -Real.log 2 / 2 + -Real.log 2 / 2 = -Real.log 2 := by ring
    rw [heq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hf : ∀ b c, Differentiable ℂ
      (analyticColumn (h c) (a c) (transverse b)) := by
    intro b c
    unfold analyticColumn
    exact ((Complex.differentiable_exp.comp
      (differentiable_id.const_mul (h c : ℂ))).const_mul _).mul
        (differentiable_id.pow _)
  have hbound : ∀ b c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖analyticColumn (h c) (a c) (transverse b) z‖ ≤
        Real.exp (H * ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar)) := by
    intro b c z hz
    have hzR : ‖z‖ = (R : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact analyticColumn_norm_le (h c) (a c) (transverse b) w
      hR1 hH.le hw0 hws hw (hcol c) hzR.le
  have hcenter : ∀ r : ι,
      ‖(j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ + 3 / 4 ≤
        (R : ℝ) / 2 := by
    intro r
    have hjK : (j r : ℝ) ≤ K := by exact_mod_cast (hj r).le
    have hnorm : ‖(j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ =
        (j r : ℝ) * (2 * Real.pi) := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
    have hprod : (j r : ℝ) * (2 * Real.pi) ≤ (K : ℝ) * 8 :=
      mul_le_mul hjK hpi (by positivity) (by positivity)
    change ‖(j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ + 3 / 4 ≤
      (100 * (K : ℝ)) / 2
    rw [hnorm]
    linarith
  have hb := analytic_collision_factor_bound group
    (fun b c => analyticColumn (h c) (a c) (transverse b))
    (fun r => (j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ell R hR
    (Real.exp (H * ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar)))
    (Real.exp (-Real.log 2 / 2)) (Real.exp_pos _).le hs0 hs1 hss hf hbound hcenter
  have hRv : (R : ℝ) = 100 * (K : ℝ) := rfl
  have he : 2 * (100 * (K : ℝ)) = 200 * (K : ℝ) := by ring
  rw [hRv, he] at hb
  simpa only [periodModel_coeff_eq_rowTest] using hb
end

section
-- OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp (d1be2bde-0e2c-4139-9af9-9dd1da13a62a)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (ell : ι → ℕ) {H A v : ℝ}
    (hH : 0 < H) (hv : 0 < v)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    (((Fintype.card ι).factorial : ℝ) *
        (Real.exp (H * A)) ^ Fintype.card ι * (2 : ℝ) ^ (∑ r, ell r)) *
      (Real.exp (-Real.log 2 / 2)) ^
        (∑ b : κ, (((Finset.univ : Finset ι).filter (fun r => group r = b)).card).choose 2) *
      ((1 - Real.exp (-Real.log 2 / 2))⁻¹) ^ Fintype.card ι ≤
    Real.exp (-(Real.log 2 / 4) *
      (∑ b : κ, ((((Finset.univ : Finset ι).filter
        (fun r => group r = b)).card : ℝ) ^ 2)) +
      (Fintype.card ι : ℝ) * H *
        (A + Real.log 2 / v + collisionAllowance (Fintype.card ι) H)) := by
  classical
  set M := Fintype.card ι with hM
  set S := ∑ r, ell r with hS
  set n : κ → ℕ := fun b => ((Finset.univ : Finset ι).filter (fun r => group r = b)).card with hn
  set q := Real.exp (-Real.log 2 / 2) with hq
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero, Real.exp_lt_exp]; linarith
  have hq0 : 0 < q := Real.exp_pos _
  have h1q : 0 < 1 - q := by linarith
  have hsumn : ∑ b, (n b : ℝ) = M := by
    have := (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι)) (t := Finset.univ)
      (f := group) (fun _ _ => Finset.mem_univ _))
    rw [hM, ← Finset.card_univ, this]; push_cast; rfl
  have hC : ((∑ b, (n b).choose 2 : ℕ) : ℝ) = ((∑ b, (n b : ℝ) ^ 2) - M) / 2 := by
    push_cast
    simp only [Nat.cast_choose_two]
    rw [← hsumn, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  -- factor bounds
  have hF : ((M.factorial : ℕ) : ℝ) ≤ Real.exp (M * Real.log M) := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0]; simp
    · have : ((M.factorial : ℕ) : ℝ) ≤ (M : ℝ) ^ M := by exact_mod_cast Nat.factorial_le_pow M
      refine this.trans (le_of_eq ?_)
      rw [← Real.exp_log (show (0:ℝ) < (M:ℝ) ^ M by positivity), Real.log_pow]
  have hE : (Real.exp (H * A)) ^ M = Real.exp (M * (H * A)) := by
    rw [← Real.exp_nat_mul]
  have hT : (2 : ℝ) ^ S ≤ Real.exp (M * H * (Real.log 2 / v)) := by
    have : (2 : ℝ) ^ S = Real.exp (S * Real.log 2) := by
      rw [← Real.exp_log (show (0:ℝ) < 2 ^ S by positivity), Real.log_pow]
    rw [this]
    apply Real.exp_le_exp.2
    have h2 : (S : ℝ) ≤ M * H / v := hell
    have : M * H * (Real.log 2 / v) = (M * H / v) * Real.log 2 := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 hl2.le
  have hG : q ^ (∑ b, (n b).choose 2) =
      Real.exp (-(Real.log 2 / 4) * ((∑ b, (n b : ℝ) ^ 2) - M)) := by
    rw [hq, ← Real.exp_nat_mul, hC]
    congr 1; ring
  have hU : ((1 - q)⁻¹) ^ M = Real.exp (-(M * Real.log (1 - q))) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log h1q, inv_pow]
  calc ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ S) * q ^ (∑ b, (n b).choose 2) *
        ((1 - q)⁻¹) ^ M
      ≤ (Real.exp (M * Real.log M) * Real.exp (M * (H * A)) * Real.exp (M * H * (Real.log 2 / v))) *
          Real.exp (-(Real.log 2 / 4) * ((∑ b, (n b : ℝ) ^ 2) - M)) *
          Real.exp (-(M * Real.log (1 - q))) := by
        rw [hG, hU, hE]
        gcongr
    _ = Real.exp (-(Real.log 2 / 4) * (∑ b, (n b : ℝ) ^ 2) +
          (M : ℝ) * H * (A + Real.log 2 / v + collisionAllowance M H)) := by
        simp only [← Real.exp_add]
        congr 1
        unfold collisionAllowance
        rw [← hq]
        field_simp
        ring

end

section
-- OAI.PiExponent.DeterminantContradiction.FiniteTranslation.period_determinant_bound (5e483ac8-7603-4f3c-8061-033d300d33bd)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.FiniteTranslation.period_determinant_bound
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : Family d H) :
    ‖(coefficientMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant *
        (∑ a : Index d H,
          (((Finset.univ : Finset (Row d H)).filter
            (fun r => (f r).1 = a)).card : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + collisionAllowance (actualRowCount d H) H)) := by
  classical
  let ell : Row d H → ℕ := fun r => r.2.1 0 - ((f r).2.2 : ℕ)
  have hw (i : Fin d.m) :
      d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
    simpa only [d.x_log, MatrixArithmetic.logWeights, finiteDenominators]
      using d.wstar_lower i
  have hcol (c : Row d H) :
      (d.w0 : ℝ) * ((selection c).1 0 : ℝ) +
        ∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i *
          ((selection c).1 i.succ : ℝ) ≤ H := by
    have hm := (selection c).2
    change (selection c).1 ∈ realWeightedSimplex
      (InterpolationMatrix.columnWeights (d.w0 : ℝ)
        (MatrixArithmetic.logWeights (finiteDenominators d))) H at hm
    have hs := (Finset.mem_filter.mp hm).2
    simpa only [Fin.sum_univ_succ, InterpolationMatrix.columnWeights,
      Fin.cases_zero, Fin.cases_succ] using hs
  have horder (r : Row d H) : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
    have hm := r.2.2
    change r.2.1 ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
        (MatrixArithmetic.logWeights (finiteDenominators d))) H at hm
    have hs := (Finset.mem_filter.mp hm).2
    have hs' :
        (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
          ∑ i : Fin d.m,
            (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
              (r.2.1 i.succ : ℝ) < H := by
      simpa only [Fin.sum_univ_succ, InterpolationMatrix.rowWeights,
        Fin.cases_zero, Fin.cases_succ] using hs
    have hnonneg : 0 ≤ ∑ i : Fin d.m,
        (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
          (r.2.1 i.succ : ℝ) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg
        (div_nonneg (d.wstar_pos.le.trans (hw i)) d.base.theta_pos.le)
        (Nat.cast_nonneg _)
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith
  have hell :
      ((Finset.univ.sum ell : ℕ) : ℝ) ≤
        (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        change ((r.2.1 0 - ((f r).2.2 : ℕ) : ℕ) : ℝ) ≤ H / (d.v0 : ℝ)
        exact le_trans
          (Nat.cast_le.mpr (Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ))) (horder r)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hb := OAI.PiExponent.FinitePeriodCollision.coefficient_determinant_factor_bound
    (fun r : Row d H => (f r).1) (fun a : Index d H => a.1)
    (fun r : Row d H => r.1.val)
    ell
    (fun c : Row d H => (selection c).1 0)
    (fun (c : Row d H) (i : Fin d.m) => (selection c).1 i.succ)
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (K := d.K) (H := H) (w0 := (d.w0 : ℝ)) (wstar := d.wstar)
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) hH d.w0_pos d.wstar_pos hw
    (fun r => r.1.isLt) hcol
  have he := OAI.PiExponent.FinitePeriodCollision.factor_bound_to_exp
    (fun r : Row d H => (f r).1)
    ell
    (A := 100 * (d.K : ℝ) / (d.w0 : ℝ) +
      Real.log (200 * (d.K : ℝ)) / d.wstar)
    hH d.v0_pos hell
  have ha :
      (100 * (d.K : ℝ) / (d.w0 : ℝ) + Real.log (200 * (d.K : ℝ)) / d.wstar) +
        Real.log 2 / (d.v0 : ℝ) = d.holomorphicError := by
    unfold AdmissibleParameters.holomorphicError
    ring
  rw [ha] at he
  change ‖(coefficientMatrix d selection f).det‖ ≤ _ at hb
  unfold collisionConstant actualRowCount
  exact hb.trans he
end

section
-- OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound (22aa7ac3-9f7d-4cdf-8e57-692601087d27)

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsum :
      (∑ i : ι, weight (group i)) <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta))) :
    eta * (Fintype.card ι : ℝ) ≤
      ∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) := by
  classical
  let good : Finset ι := Finset.univ.filter (fun i => weight (group i) ≤ A * H)
  let bad : Finset ι := Finset.univ.filter (fun i => ¬ weight (group i) ≤ A * H)
  have hcountNat :
      (∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        ((Finset.univ : Finset ι).filter (fun i => group i = a)).card) = good.card := by
    simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset ι)
        ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)) group)
  have hcount :
      (∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) =
        (good.card : ℝ) := by
    simpa only [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℝ)) hcountNat
  rw [hcount]
  have hcardNat : good.card + bad.card = Fintype.card ι := by
    simpa only [good, bad, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
        (fun i => weight (group i) ≤ A * H))
  have hcard : (good.card : ℝ) + (bad.card : ℝ) = (Fintype.card ι : ℝ) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) hcardNat
  have hbad : (bad.card : ℝ) * (A * H) ≤ ∑ i : ι, weight (group i) := by
    calc
      (bad.card : ℝ) * (A * H) = ∑ i ∈ bad, A * H := by simp
      _ ≤ ∑ i ∈ bad, weight (group i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i : ι, weight (group i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro i _ _
          exact hweight (group i)
  have hsum' : (∑ i : ι, weight (group i)) <
      (Fintype.card ι : ℝ) * (A * H) * (1 - eta) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum
  by_contra h
  have hg : (good.card : ℝ) ≤ eta * (Fintype.card ι : ℝ) :=
    le_of_lt (lt_of_not_ge h)
  have hm := mul_le_mul_of_nonneg_right hg (mul_nonneg hA hH.le)
  have hcard_mul := congrArg (fun x : ℝ => x * (A * H)) hcard
  nlinarith only [hsum', hbad, hm, hcard_mul]
end

section
-- OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass (aa0af2c6-eace-4f4b-b38d-ad339bc81ecf)
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta bbar : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsurplus :
      ¬ ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
        (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar)) :
    eta * (Fintype.card ι : ℝ) ≤
      ∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) := by
  have hstrict :
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) :=
    not_le.mp hsurplus
  have hsum :
      (∑ i : ι, weight (group i)) <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta)) := by
    calc
      (∑ i : ι, weight (group i)) =
          ((∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
            (Fintype.card ι : ℝ) * H * bbar := by
        exact (sub_add_cancel _ _).symm
      _ < (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) +
            (Fintype.card ι : ℝ) * H * bbar := add_lt_add_left hstrict _
      _ = (Fintype.card ι : ℝ) * H *
            ((A * (1 - eta) - bbar) + bbar) := by rw [← mul_add]
      _ = (Fintype.card ι : ℝ) * H * (A * (1 - eta)) := by rw [sub_add_cancel]
  exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound
    group weight hH hA heta hweight hsum
end

section
-- OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision (cbb4d5ea-60b7-46b7-baee-a81f8cafcb65)

open scoped BigOperators

universe u v

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (low : Finset κ)
    {eta N : ℝ}
    (heta : 0 ≤ eta) (hN : 0 < N)
    (hcapacity : (low.card : ℝ) ≤ N)
    (hlowMass :
      eta * (Fintype.card ι : ℝ) ≤
        ∑ a ∈ low,
          (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) :
    eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2 := by
  let occ : κ → ℝ := fun a =>
    (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)
  change eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤ ∑ a : κ, occ a ^ 2
  have hmass : eta * (Fintype.card ι : ℝ) ≤ ∑ a ∈ low, occ a := hlowMass
  have hbase : 0 ≤ eta * (Fintype.card ι : ℝ) :=
    mul_nonneg heta (Nat.cast_nonneg _)
  have hmass_sq : (eta * (Fintype.card ι : ℝ)) ^ 2 ≤ (∑ a ∈ low, occ a) ^ 2 :=
    pow_le_pow_left₀ hbase hmass 2
  have hcs : (∑ a ∈ low, occ a) ^ 2 ≤
      (low.card : ℝ) * ∑ a ∈ low, occ a ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hlowSq_nonneg : 0 ≤ ∑ a ∈ low, occ a ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg (occ a))
  have hsumSq : (∑ a ∈ low, occ a ^ 2) ≤ ∑ a : κ, occ a ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
      (fun a _ _ => sq_nonneg (occ a))
  have hbound : eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 ≤
      N * ∑ a : κ, occ a ^ 2 := by
    calc
      eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 =
          (eta * (Fintype.card ι : ℝ)) ^ 2 := (mul_pow _ _ _).symm
      _ ≤ (∑ a ∈ low, occ a) ^ 2 := hmass_sq
      _ ≤ (low.card : ℝ) * ∑ a ∈ low, occ a ^ 2 := hcs
      _ ≤ N * ∑ a ∈ low, occ a ^ 2 :=
        mul_le_mul_of_nonneg_right hcapacity hlowSq_nonneg
      _ ≤ N * ∑ a : κ, occ a ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq hN.le
  exact (div_le_iff₀ hN).2 (hbound.trans_eq (mul_comm _ _))
end

section
-- OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy (5a70a775-13d8-4ed2-9c54-3f1bb27eeeee)
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta N bbar : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hN : 0 < N)
    (hweight : ∀ a, 0 ≤ weight a)
    (hmean : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i : ι, weight (group i))
    (hcapacity : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    (eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2) ∨
    ((Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
      (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) := by
  let low : Finset κ := (Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)
  have hlowcap : (low.card : ℝ) ≤ N := by
    simpa [low] using hcapacity
  by_cases hs :
      (Fintype.card ι : ℝ) * H * (A * (1 - eta) - bbar) ≤
        (∑ i : ι, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar
  · exact Or.inr hs
  · have hlow :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_low_mass
        group weight hH hA heta hweight hs
    have hcollision :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision
        group low heta hN hlowcap hlow
    exact Or.inl hcollision
end

section
-- OAI.PiExponent.DeterminantContradiction.actual_minor_uniform_exp_bound (5c1bf3a1-b882-42ee-8bc3-4ede8ba9371f)

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem OAI.PiExponent.DeterminantContradiction.actual_minor_uniform_exp_bound
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) :
    ‖(actualMinor d H selection).det‖ ≤
      Real.exp ((actualRowCount d H : ℝ) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  let M : ℝ := actualRowCount d H
  let W : ℝ := M * H
  let Q : ℝ := translationEnvelope d.m d.v0 H
  let rho : ℝ := collisionAllowance (actualRowCount d H) H
  let B : ℝ := (d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H
  let R : ℝ := max (-collisionRate d H) (-nu * B)
  let E : ℝ := d.analyticError + rho + R
  have hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) hH.le
  have hv : 0 < (d.v0 : ℝ) := d.v0_pos
  have hQ : 0 < Q := by
    dsimp [Q, translationEnvelope]
    positivity
  have hc : 0 ≤ collisionConstant := by
    unfold collisionConstant
    exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hA : 0 ≤ (d.base.A : ℝ) :=
    (d.base.theta_pos.trans d.base.theta_lt_A).le
  rcases expansion_and_card d hH selection with ⟨hexpansion, hcard⟩
  rcases index_geometry d hH with ⟨hN, hweight, hcapacity, hselected⟩
  have hcollision : W * (-collisionRate d H) =
      -collisionConstant * (d.base.eta ^ 2 * M ^ 2 / (lowIndexCount d H : ℝ)) := by
    dsimp only [W, M]
    unfold collisionRate
    field_simp [ne_of_gt hH, ne_of_gt hN] <;> ring
  have hterm : ∀ f : Family d H, ‖term d selection f‖ ≤ Real.exp (W * E) := by
    intro f
    by_cases hz : (∏ r : Row d H, scalar d r (f r)) = 0
    · rw [term, hz, zero_mul, norm_zero]
      exact (Real.exp_pos _).le
    let S : ℝ := ∑ r : Row d H, weight d (f r).1
    let Z : ℝ := ∑ a : Index d H,
      (((Finset.univ : Finset (Row d H)).filter (fun r => (f r).1 = a)).card : ℝ) ^ 2
    have hmono : W * actualMean d H ≤ S := hselected f hz
    have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsplit :=
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy
        (fun r : Row d H => (f r).1) (fun a : Index d H => weight d a)
        hH hA d.base.eta_pos.le hN hweight (hselected f hz) hcapacity
    change (d.base.eta ^ 2 * M ^ 2 / (lowIndexCount d H : ℝ) ≤ Z) ∨
      (W * B ≤ S - W * actualMean d H) at hsplit
    have hrate : -nu * (S - W * actualMean d H) - collisionConstant * Z ≤ W * R := by
      rcases hsplit with hlow | hhigh
      · have hsc : -nu * (S - W * actualMean d H) ≤ 0 := by
          nlinarith [mul_nonneg hnu (sub_nonneg.mpr hmono)]
        have hcoll : -collisionConstant * Z ≤ W * (-collisionRate d H) := by
          rw [hcollision]
          nlinarith [mul_le_mul_of_nonneg_left hlow hc]
        have hmax : W * (-collisionRate d H) ≤ W * R :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hW
        linarith
      · have hsc : -nu * (S - W * actualMean d H) ≤ W * (-nu * B) := by
          nlinarith [mul_le_mul_of_nonneg_left hhigh hnu]
        have hcoll : -collisionConstant * Z ≤ 0 := by
          nlinarith [mul_nonneg hc hZ]
        have hmax : W * (-nu * B) ≤ W * R :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hW
        linarith
    have hs := scalar_product_bound d hnu hH f
    have hd := period_determinant_bound d hH selection f
    change ‖∏ r : Row d H, scalar d r (f r)‖ ≤
      Real.exp (-nu * (S - W * actualMean d H) + W * d.translationError) at hs
    change ‖(coefficientMatrix d selection f).det‖ ≤
      Real.exp (-collisionConstant * Z + W * (d.holomorphicError + rho)) at hd
    calc
      ‖term d selection f‖ =
          ‖∏ r : Row d H, scalar d r (f r)‖ * ‖(coefficientMatrix d selection f).det‖ := by
        rw [term, norm_mul]
      _ ≤ Real.exp (-nu * (S - W * actualMean d H) + W * d.translationError) *
          Real.exp (-collisionConstant * Z + W * (d.holomorphicError + rho)) :=
        mul_le_mul hs hd (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (W * E) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp only [E]
        rw [AdmissibleParameters.analyticError]
        nlinarith only [hrate]
  have hpower : Q ^ actualRowCount d H = Real.exp (M * Real.log Q) := by
    dsimp only [M]
    rw [Real.exp_nat_mul, Real.exp_log hQ]
  have hrem : analyticRemainder d H = rho + Real.log Q / H := rfl
  calc
    ‖(actualMinor d H selection).det‖ = ‖∑ f : Family d H, term d selection f‖ := by
      rw [hexpansion]
    _ ≤ ∑ f : Family d H, ‖term d selection f‖ := norm_sum_le _ _
    _ ≤ ∑ _f : Family d H, Real.exp (W * E) :=
      Finset.sum_le_sum fun f _ => hterm f
    _ = (Fintype.card (Family d H) : ℝ) * Real.exp (W * E) := by simp
    _ ≤ Q ^ actualRowCount d H * Real.exp (W * E) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (M * Real.log Q + W * E) := by
      rw [hpower, ← Real.exp_add]
    _ = Real.exp ((actualRowCount d H : ℝ) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
      congr 1
      change M * Real.log Q + W * E = W * (d.analyticError + analyticRemainder d H + R)
      rw [hrem]
      dsimp only [E, W]
      field_simp [ne_of_gt hH] <;> ring
end

section
-- OAI.PiExponent.DeterminantContradiction.tendsto_actualRowCount_normalized (936f9606-5863-4abb-9e4d-c55f5f8ef043)
-- Proof adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.

set_option autoImplicit false
open Filter Topology
open scoped BigOperators
noncomputable section

namespace OAI

open Filter Topology

namespace PiExponent

theorem tendsto_natFloor_affine_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => ⌊a * x + b⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id))

theorem tendsto_natFloor_affine_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => (⌊a * x + b⌋₊ : ℝ) / x) atTop (𝓝 a) := by
  have hy : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id)
  have hratio : Tendsto (fun x : ℝ => (a * x + b) / x) atTop (𝓝 a) := by
    have h : Tendsto (fun x : ℝ => a + b * x⁻¹) atTop (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have h := (tendsto_nat_floor_div_atTop.comp hy).mul hratio
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  change (⌊a * x + b⌋₊ : ℝ) / (a * x + b) * ((a * x + b) / x) = _
  field_simp

theorem tendsto_normalized_natFloor_affine {f : ℕ → ℝ} {d : ℕ} {L a : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L))
    (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => f ⌊a * x + b⌋₊ / x ^ d) atTop (𝓝 (L * a ^ d)) := by
  have hfloor := tendsto_natFloor_affine_atTop ha b
  have h := (hf.comp hfloor).mul ((tendsto_natFloor_affine_div ha b).pow d)
  apply h.congr'
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with x hx
  have hn : (⌊a * x + b⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : ⌊a * x + b⌋₊ ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_normalized_natFloor_affine_nat {f : ℕ → ℝ} {d : ℕ} {L a : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L))
    (ha : 0 < a) (b : ℝ) :
    Tendsto (fun N : ℕ => f ⌊a * (N : ℝ) + b⌋₊ / (N : ℝ) ^ d)
      atTop (𝓝 (L * a ^ d)) :=
  (tendsto_normalized_natFloor_affine hf ha b).comp tendsto_natCast_atTop_atTop

end PiExponent

end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent

def unweightedSimplex (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, a i ≤ N)

@[simp] theorem mem_unweightedSimplex {d N : ℕ} {a : Fin d → ℕ} :
    a ∈ unweightedSimplex d N ↔ ∑ i, a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

theorem card_unweightedSimplex (d N : ℕ) :
    (unweightedSimplex d N).card = (N + d).choose d := by
  classical
  let target : Finset (Fin (d + 1) →₀ ℕ) := Finset.univ.finsuppAntidiag N
  have hc : target.card = (N + d).choose d := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show d + 1 + N - 1 = N + d by omega, Nat.choose_symm_add]
  rw [← hc]
  let f : (Fin d → ℕ) → (Fin (d + 1) →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - ∑ i, a i) a)
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    apply Finset.mem_finsuppAntidiag.mpr
    constructor
    · simp only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      exact Nat.sub_add_cancel (mem_unweightedSimplex.mp ha)
    · exact Finset.subset_univ _
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun g : Fin (d + 1) →₀ ℕ => g i.succ) hab
    simpa only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_succ] using h
  · intro b hb
    obtain ⟨hs, _⟩ := Finset.mem_finsuppAntidiag.mp hb
    have hs' : b 0 + ∑ i : Fin d, b i.succ = N := by
      simpa only [Fin.sum_univ_succ] using hs
    refine ⟨fun i => b i.succ, mem_unweightedSimplex.mpr (by omega), ?_⟩
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change N - ∑ j : Fin d, b j.succ = b 0
      omega
    · change b j.succ = b j.succ
      rfl

open Filter Topology Asymptotics

theorem tendsto_choose_normalized (d : ℕ) :
    Tendsto (fun N : ℕ => (N.choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h := (isEquivalent_choose d).div
    (IsEquivalent.refl : (fun N : ℕ => (N : ℝ) ^ d) ~[atTop]
      (fun N : ℕ => (N : ℝ) ^ d))
  apply h.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change 1 / (d.factorial : ℝ) = ((N : ℝ) ^ d / (d.factorial : ℝ)) / (N : ℝ) ^ d
  field_simp

theorem tendsto_choose_add_normalized (d c : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h₁ := (tendsto_choose_normalized d).comp (tendsto_add_atTop_nat c)
  have h₂ : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1 (d := 1) (by norm_num))
  have h := h₁.mul (h₂.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : ((N + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + c ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_card_unweightedSimplex (d : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex] using tendsto_choose_add_normalized d d

theorem tendsto_card_unweightedSimplex_add (d c : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d (N + c)).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex, Nat.add_assoc] using
    tendsto_choose_add_normalized d (c + d)

end PiExponent

end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent

def natWeightedSimplex {d : ℕ} (w : Fin d → ℕ) (N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, w i * a i ≤ N)

theorem mem_natWeightedSimplex {d : ℕ} {w : Fin d → ℕ}
    (hw : ∀ i, 0 < w i) {N : ℕ} {a : Fin d → ℕ} :
    a ∈ natWeightedSimplex w N ↔ ∑ i, w i * a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h₁ : a i ≤ w i * a i := Nat.le_mul_of_pos_left (a i) (hw i)
    have h₂ : w i * a i ≤ ∑ j, w j * a j :=
      Finset.single_le_sum (f := fun j => w j * a j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

def residueRectangle {d : ℕ} (w : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (w i))

@[simp] theorem mem_residueRectangle {d : ℕ} {w r : Fin d → ℕ} :
    r ∈ residueRectangle w ↔ ∀ i, r i < w i := by
  simp [residueRectangle, Fintype.mem_piFinset]

@[simp] theorem card_residueRectangle {d : ℕ} (w : Fin d → ℕ) :
    (residueRectangle w).card = ∏ i, w i := by
  simp [residueRectangle, Fintype.card_piFinset]

theorem simplex_count_lower_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex (fun _ : Fin d => 1) N).card ≤
      (natWeightedSimplex w N).card * ∏ i, w i := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : (Fin d → ℕ) → (Fin d → ℕ) × (Fin d → ℕ) :=
    fun b => (fun i => b i / w i, fun i => b i % w i)
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    apply Finset.mem_product.mpr
    constructor
    · apply (mem_natWeightedSimplex hw).mpr
      have hb' := (mem_natWeightedSimplex (fun _ => by decide)).mp hb
      simp only [one_mul] at hb'
      exact (Finset.sum_le_sum (fun i _ => Nat.mul_div_le (b i) (w i))).trans hb'
    · exact mem_residueRectangle.mpr (fun i => Nat.mod_lt (b i) (hw i))
  · intro a ha b hb hab
    have hq := congrArg Prod.fst hab
    have hr := congrArg Prod.snd hab
    funext i
    have hqi := congrFun hq i
    have hri := congrFun hr i
    change a i / w i = b i / w i at hqi
    change a i % w i = b i % w i at hri
    have ha' := Nat.div_add_mod (a i) (w i)
    have hb' := Nat.div_add_mod (b i) (w i)
    calc
      a i = w i * (a i / w i) + a i % w i := ha'.symm
      _ = w i * (b i / w i) + b i % w i := by rw [hqi, hri]
      _ = b i := hb'

theorem simplex_count_upper_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex w N).card * (∏ i, w i) ≤
      (natWeightedSimplex (fun _ : Fin d => 1) (N + ∑ i, (w i - 1))).card := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : ((Fin d → ℕ) × (Fin d → ℕ)) → (Fin d → ℕ) :=
    fun ar i => w i * ar.1 i + ar.2 i
  apply Finset.card_le_card_of_injOn f
  · intro ar har
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    apply (mem_natWeightedSimplex (fun _ => by decide)).mpr
    simp only [one_mul]
    change ∑ i, (w i * ar.1 i + ar.2 i) ≤ _
    rw [Finset.sum_add_distrib]
    apply Nat.add_le_add ((mem_natWeightedSimplex hw).mp ha)
    apply Finset.sum_le_sum
    intro i hi
    have := mem_residueRectangle.mp hr i
    omega
  · intro ar har bs hbs hab
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    obtain ⟨hb, hs⟩ := Finset.mem_product.mp hbs
    apply Prod.ext
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hdiv := congrArg (fun n => n / w i) hi
      rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (ar.1 i)),
        Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (bs.1 i))] at hdiv
      simpa [Nat.div_eq_of_lt hri, Nat.div_eq_of_lt hsi,
        Nat.mul_div_cancel_left _ (hw i)] using hdiv
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hmod := congrArg (fun n => n % w i) hi
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hri, Nat.mod_eq_of_lt hsi] using hmod

@[simp] theorem natWeightedSimplex_one (d N : ℕ) :
    natWeightedSimplex (fun _ : Fin d => 1) N = unweightedSimplex d N := by
  ext a
  rw [mem_natWeightedSimplex (w := fun _ : Fin d => 1) (fun _ => by decide), mem_unweightedSimplex]
  simp only [one_mul]

open Filter Topology

theorem tendsto_card_natWeightedSimplex {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by
  let P : ℝ := ∏ i, (w i : ℝ)
  have hP : 0 < P := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hs : Tendsto
      (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_card_unweightedSimplex d)
      (tendsto_card_unweightedSimplex_add d (∑ i, (w i - 1)))
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_lower_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_upper_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
  have h := hs.div_const P
  have heq : 1 / (d.factorial : ℝ) / P =
      1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)) := by
    simp only [P, div_div]
  rw [heq] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N => by
    change ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d / P = _
    field_simp)





theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

theorem realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 ≤ H) :
    realWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w ⌊c * H⌋₊ := by
  ext a
  rw [mem_realWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw, Nat.le_floor_iff (mul_nonneg hc.le hH)]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_le_iff₀ hc, mul_comm H c]

theorem strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 < H) :
    strictWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w (⌈c * H⌉₊ - 1) := by
  ext a
  rw [mem_strictWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_lt_iff₀ hc, mul_comm H c, ← Nat.lt_ceil]
  have hp : 0 < ⌈c * H⌉₊ := by
    apply Nat.lt_ceil.mpr
    simpa using mul_pos hc hH
  omega

theorem tendsto_card_realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((realWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have h := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc 0
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [add_zero, realWeightedSimplex_scaled w hw hc hH]

theorem tendsto_card_strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((strictWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have hlo := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc (-1)
  have hhi := tendsto_card_realWeightedSimplex_scaled w hw hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 / c)] with H hH
    have hHpos : 0 < H := (div_pos zero_lt_one hc).trans_le hH
    have hcH : 1 ≤ c * H := by
      have := (div_le_iff₀ hc).mp hH
      nlinarith
    apply div_le_div_of_nonneg_right _ (pow_nonneg hHpos.le d)
    exact_mod_cast (Finset.card_le_card (show
      natWeightedSimplex w ⌊c * H + -1⌋₊ ⊆
      strictWeightedSimplex (fun i => (w i : ℝ) / c) H from by
        intro a ha
        apply (mem_strictWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc)).mpr
        have ha' := (mem_natWeightedSimplex hw).mp ha
        have hs : ((∑ i, w i * a i : ℕ) : ℝ) ≤ c * H + -1 :=
          (Nat.le_floor_iff (by linarith)).mp ha'
        have heq : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
            ((∑ i, w i * a i : ℕ) : ℝ) / c := by
          simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
        rw [heq, div_lt_iff₀ hc]
        nlinarith))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    apply div_le_div_of_nonneg_right _ (pow_nonneg hH d)
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun a : Fin d → ℕ => ∑ i, (w i : ℝ) / c * (a i : ℝ) < H)
      (realWeightedSimplex (fun i => (w i : ℝ) / c) H)))


end PiExponent
end OAI

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem positive_rational_weights_common_denominator {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : Fin d → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ) := by
  classical
  let D : ℕ := ∏ i, (ρ i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (ρ i).den_pos)
  have hd : ∀ i, (ρ i).den ∣ D :=
    fun i => Finset.dvd_prod_of_mem (fun j => (ρ j).den) (Finset.mem_univ i)
  choose k hk using hd
  have hkpos : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have hkzero : k i = 0 := by omega
    have := hk i
    rw [hkzero, mul_zero] at this
    omega
  let w : Fin d → ℕ := fun i => (ρ i).num.toNat * k i
  refine ⟨D, hD, w, ?_, ?_⟩
  · intro i
    have hn : 0 < (ρ i).num := Rat.num_pos.mpr (hρ i)
    exact Nat.mul_pos (by omega) (hkpos i)
  · intro i
    have hnum : (((ρ i).num.toNat : ℕ) : ℝ) = ((ρ i).num : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (Rat.num_pos.mpr (hρ i)).le)
    have hcastD : (D : ℝ) = ((ρ i).den : ℝ) * (k i : ℝ) := by
      exact_mod_cast hk i
    have hkne : (k i : ℝ) ≠ 0 := by exact_mod_cast (hkpos i).ne'
    have hdenne : ((ρ i).den : ℝ) ≠ 0 := by exact_mod_cast (ρ i).den_ne_zero
    rw [Rat.cast_def, hcastD]
    change ((ρ i).num : ℝ) / ((ρ i).den : ℝ) =
      (((ρ i).num.toNat * k i : ℕ) : ℝ) / (((ρ i).den : ℝ) * (k i : ℝ))
    rw [Nat.cast_mul, hnum]
    field_simp

end PiExponent

end OAI

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem common_denominator_simplex_constant {d D : ℕ} {ρ : Fin d → ℚ}
    {w : Fin d → ℕ} (hD : 0 < D) (hw : ∀ i, 0 < w i)
    (hweights : ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ)) :
    (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * (D : ℝ) ^ d =
      1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) := by
  have hprod : (∏ i, (ρ i : ℝ)) = (∏ i, (w i : ℝ)) / (D : ℝ) ^ d := by
    simp_rw [hweights]
    rw [Finset.prod_div_distrib]
    simp
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPne : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [hprod]
  field_simp

theorem tendsto_card_realWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_realWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem tendsto_card_strictWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_strictWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h


end PiExponent
end OAI

namespace OAI.PiExponent.InterpolationMatrix
@[simp] theorem row_card {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) :
    Fintype.card (Row K v0 θ w H) =
      K * (PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H).card := by
  classical
  simp [Row]

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.MatrixArithmetic
theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

end OAI.PiExponent.MatrixArithmetic

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent.MatrixCounting

noncomputable def rowCount {m : ℕ} (K : ℕ) (v0 θ : ℚ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  Fintype.card (InterpolationMatrix.Row K (v0 : ℝ) (θ : ℝ) (MatrixArithmetic.logWeights q) H)

noncomputable def lowIndexCount {m : ℕ} (A : ℚ) (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights q) ((A : ℝ) * H)).card

noncomputable def rationalLogWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℚ :=
  (⌈Real.log (q i)⌉₊ : ℚ)

@[simp] theorem rationalLogWeights_cast {m : ℕ} (q : Fin m → ℕ) (i : Fin m) :
    (rationalLogWeights q i : ℝ) = MatrixArithmetic.logWeights q i := by
  simp [rationalLogWeights, MatrixArithmetic.logWeights]

theorem rationalLogWeights_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (i : Fin m) : 0 < rationalLogWeights q i := by
  have h := MatrixArithmetic.ceil_log_weight_pos (hq i)
  unfold rationalLogWeights
  exact_mod_cast h

theorem tendsto_rowCount_normalized {m : ℕ} (K : ℕ) (v0 θ : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => rowCount K v0 θ q H / H ^ (m + 1)) atTop
      (𝓝 ((K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i))) := by
  let V : Fin (m + 1) → ℚ := Fin.cases v0 (fun i => rationalLogWeights q i / θ)
  have hV : ∀ i, 0 < V i := by
    intro i
    exact Fin.cases hv0 (fun j => div_pos (rationalLogWeights_pos q hq j) hθ) i
  have hcast : (fun i => (V i : ℝ)) =
      InterpolationMatrix.rowWeights (v0 : ℝ) (θ : ℝ) (MatrixArithmetic.logWeights q) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [V, InterpolationMatrix.rowWeights]
    · simp [V, InterpolationMatrix.rowWeights]
  have hp : ∏ i, (V i : ℝ) =
      (v0 : ℝ) * (∏ i, MatrixArithmetic.logWeights q i) / (θ : ℝ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp [V, Finset.prod_div_distrib, mul_div_assoc]
  have ht := (tendsto_card_strictWeightedSimplex_rational V hV).const_mul (K : ℝ)
  have hθ0 : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have he : (K : ℝ) * (1 / (((m + 1).factorial : ℝ) * ∏ i, (V i : ℝ))) =
      (K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) := by
    rw [hp]
    field_simp
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    simp only [rowCount, InterpolationMatrix.row_card, Nat.cast_mul]
    rw [← hcast]
    ring)

theorem tendsto_lowIndexCount_normalized {m : ℕ} (A : ℚ)
    (q : Fin m → ℕ) (hA : 0 < A) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => lowIndexCount A q H / H ^ m) atTop
      (𝓝 ((A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i))) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have ht : Tendsto (fun H : ℝ => (A : ℝ) * H) atTop atTop :=
    Tendsto.const_mul_atTop hAR tendsto_id
  have h := ((tendsto_card_realWeightedSimplex_rational (rationalLogWeights q)
    (rationalLogWeights_pos q hq)).comp ht).mul_const ((A : ℝ) ^ m)
  simp only [rationalLogWeights_cast] at h
  have he : 1 / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) * (A : ℝ) ^ m =
      (A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) := by ring
  rw [he] at h
  have hweights : (fun i => (rationalLogWeights q i : ℝ)) = MatrixArithmetic.logWeights q := by
    funext i
    exact rationalLogWeights_cast q i
  apply h.congr'
  exact Eventually.of_forall (fun H => by
    simp only [Function.comp_apply, lowIndexCount, mul_pow]
    field_simp)

theorem tendsto_row_lowIndex_ratio {m : ℕ} (K : ℕ) (v0 θ A : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => rowCount K v0 θ q H / (H * lowIndexCount A q H)) atTop
      (𝓝 ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m))) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hvR : (0 : ℝ) < v0 := by exact_mod_cast hv0
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hP : 0 < ∏ i, MatrixArithmetic.logWeights q i :=
    Finset.prod_pos (fun i _ => MatrixArithmetic.ceil_log_weight_pos (hq i))
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hd : (A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) ≠ 0 :=
    (div_pos (pow_pos hAR m) (mul_pos hfac hP)).ne'
  have h := (tendsto_rowCount_normalized K v0 θ q hv0 hθ hq).div
    (tendsto_lowIndexCount_normalized A q hA hq) hd
  have he :
      ((K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i)) /
        ((A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i)) =
      (K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (rowCount K v0 θ q H / H ^ (m + 1)) / (lowIndexCount A q H / H ^ m) =
    rowCount K v0 θ q H / (H * lowIndexCount A q H)
  by_cases hn : lowIndexCount A q H = 0
  · simp [hn]
  · simp only [pow_succ]
    field_simp [hH.ne', hn]

theorem tendsto_collisionRatio {m : ℕ} (K : ℕ) (v0 θ A : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) (c η : ℝ) :
    Tendsto (fun H : ℝ => c * η ^ 2 * rowCount K v0 θ q H /
      (H * lowIndexCount A q H)) atTop
      (𝓝 (c * η ^ 2 * (K : ℝ) * (θ : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m))) := by
  have ht := (tendsto_row_lowIndex_ratio K v0 θ A q hv0 hθ hA hq).const_mul (c * η ^ 2)
  have he : (c * η ^ 2) *
      ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m)) =
      c * η ^ 2 * (K : ℝ) * (θ : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m) := by ring
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    change (c * η ^ 2) * (rowCount K v0 θ q H / (H * lowIndexCount A q H)) = _
    ring)

end PiExponent.MatrixCounting

end OAI

namespace OAI.PiExponent.DeterminantContradiction
theorem finiteDenominators_two_le {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

end OAI.PiExponent.DeterminantContradiction

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.tendsto_actualRowCount_normalized
    {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => (actualRowCount d H : ℝ) / H ^ (d.m + 1)) atTop
      (𝓝 ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
        (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
          ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hh := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.base.theta
    (finiteDenominators d) hv ht (finiteDenominators_two_le d)
  apply hh.congr'
  filter_upwards with H
  simp [MatrixCounting.rowCount, actualRowCount, Row]
end

section
-- OAI.PiExponent.DeterminantContradiction.analytic_aggregate (67192408-1d0d-4b30-ab99-7919c1c13b59)

open Filter Topology
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

private theorem log_div_of_normalized_pow {f : ℝ → ℝ} {n : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ n) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H : ℝ => Real.log (f H) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log (f H / H ^ n)) atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hslow : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (hlog.div_atTop tendsto_id).add (hslow.const_mul (n : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_ne_nhds hL.ne')] with H hH hn
  have hfne : f H ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  rw [Real.log_div hfne (pow_ne_zero _ hH.ne'), Real.log_pow]
  simp only [id_eq]
  ring

private theorem envelope_normalized (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => translationEnvelope m v H / H ^ (2 * m + 1))
      atTop (𝓝 (1 / v)) := by
  have hsmall : Tendsto (fun H : ℝ => 1 / H) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have h1 : Tendsto (fun H : ℝ => (H + 1) / H) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
  have h2 : Tendsto (fun H : ℝ => (H / v + 1) / H) atTop (𝓝 (1 / v)) := by
    have ht := (tendsto_const_nhds (x := (1 / v : ℝ))).add hsmall
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
  have h := (h1.pow (2 * m)).mul h2
  simp only [one_pow, one_mul] at h
  convert h using 1
  funext H
  simp only [translationEnvelope, div_pow, div_mul_div_comm, pow_succ]

private theorem remainder_tendsto {nu : ℝ} (d : FixedData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have hw : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log i.val]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hlead : 0 < (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
        (pow_pos d.base.theta_pos _)
    · exact mul_pos (mul_pos (by positivity) d.v0_pos)
        (Finset.prod_pos fun i _ => hw i)
  have hr := log_div_of_normalized_pow (tendsto_actualRowCount_normalized d) hlead
  have hc := tendsto_id.const_div_atTop
    (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)))
  have hq := log_div_of_normalized_pow (envelope_normalized d.m d.v0_pos)
    (div_pos zero_lt_one d.v0_pos)
  convert (hr.add hc).add hq using 1
  · funext H
    unfold analyticRemainder
    simp only [id_eq]
    ring
  · norm_num

private theorem rowCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H := by
  classical
  let r : Row d H := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩,
    ⟨fun _ => 0, by simp [strictWeightedSimplex, realWeightedSimplex, hH, hH.le]⟩⟩
  have : Nonempty (Row d H) := ⟨r⟩
  exact Fintype.card_pos

theorem OAI.PiExponent.DeterminantContradiction.analytic_aggregate : AnalyticAggregateStatement := by
  intro nu hnu d
  refine ⟨analyticRemainder d, remainder_tendsto d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hdet
  have hb := actual_minor_uniform_exp_bound d (le_trans (by norm_num) hnu.le) hH selection
  have hlog := Real.log_le_log (norm_pos_iff.mpr hdet) hb
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast rowCount_pos d hH) hH)).mpr
  simpa only [mul_comm] using hlog
end

section
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution : AnalyticAggregateStatement :=
  OAI.PiExponent.DeterminantContradiction.analytic_aggregate
end
