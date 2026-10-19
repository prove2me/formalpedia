-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actualMatrix_entry_translation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:58:49.654012+00:00
-- url     : https://prove2.me/submissions/da8dec0a-cb8a-40cb-be92-9d7042213f94

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_affinePower_coeff_translate
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_prod_add_pow_fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

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

theorem solution
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
