-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.pencil_laurent_specialize
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:47.029159+00:00
-- url     : https://prove2.me/submissions/bf7a003d-12e9-4ab6-8902-4e922e7b59dd

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace FP5Specialize

open HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

section Calc
variable {ι k R : Type*} [Fintype ι] [CommRing k] [CommRing R] [Algebra k R]

@[simp] lemma fieldAction_apply (δ : ι → Derivation k R R) (v : ι → R) (f : R) :
    fieldAction δ v f = ∑ i, v i * δ i f := by
  have hh := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := R) (M := R))
    (fun i => v i • δ i) Finset.univ) f
  simpa only [fieldAction, Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using hh

lemma fieldAction_add (δ : ι → Derivation k R R) (v w : ι → R) (f : R) :
    fieldAction δ (fun i => v i + w i) f = fieldAction δ v f + fieldAction δ w f := by
  simp only [fieldAction_apply, add_mul, Finset.sum_add_distrib]

lemma fieldAction_scale (δ : ι → Derivation k R R) (a : R) (v : ι → R) (f : R) :
    fieldAction δ (fun i => a * v i) f = a * fieldAction δ v f := by
  simp only [fieldAction_apply, Finset.mul_sum, mul_assoc]

lemma fieldDivergence_add (δ : ι → Derivation k R R) (v w : ι → R) :
    fieldDivergence δ (fun i => v i + w i) = fieldDivergence δ v + fieldDivergence δ w := by
  simp only [fieldDivergence, map_add, Finset.sum_add_distrib]

lemma fieldDivergence_scale (δ : ι → Derivation k R R) (a : R) (v : ι → R) :
    fieldDivergence δ (fun i => a * v i) =
      fieldAction δ v a + a * fieldDivergence δ v := by
  simp only [fieldDivergence, fieldAction_apply, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring

end Calc

section Telescoping
variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]

lemma laurentD_succ (j : ℕ) : laurentD (j + 1) = laurentC (j + 1) - laurentD j := rfl

lemma laurentC_succ_mul (j : ℕ) : laurentC (j + 1) * ((j : ℚ) + 1) = -(2 / 3 : ℚ) * laurentD j := by
  have h : (j : ℚ) + 1 ≠ 0 := by positivity
  simp only [laurentC]
  field_simp [h]

lemma chartCurrent_add (δ : ι → Derivation ℚ K K) (P : K) (v w : ι → K) :
    chartCurrent δ P (v + w) = chartCurrent δ P v + chartCurrent δ P w := by
  change chartCurrent δ P (fun i => v i + w i) = _
  simp only [chartCurrent, fieldAction_add, fieldDivergence_add]
  ring

lemma term (δ : ι → Derivation ℚ K K) (P h : K) (v : ι → K) (j : ℕ) :
    chartCurrent δ P (fun i => algebraMap ℚ K (laurentC (j + 1)) * h ^ (j + 1) * v i) =
      algebraMap ℚ K (laurentD (j + 1)) * h ^ (j + 1) * chartCurrent δ P v +
        algebraMap ℚ K (laurentD j) * h ^ j * chartCurrent δ (P * h) v := by
  have hc : algebraMap ℚ K (laurentC (j + 1)) * ((j : K) + 1) =
      -(2 / 3 : K) * algebraMap ℚ K (laurentD j) := by
    simpa only [map_mul, map_add, map_one, map_neg, map_div₀, map_ofNat, map_natCast] using
      congrArg (algebraMap ℚ K) (laurentC_succ_mul j)
  have hdiff : fieldAction δ v (algebraMap ℚ K (laurentC (j + 1)) * h ^ (j + 1)) =
      algebraMap ℚ K (laurentC (j + 1)) * (((j : K) + 1) * h ^ j * fieldAction δ v h) := by
    rw [Derivation.leibniz, Derivation.map_algebraMap, Derivation.leibniz_pow]
    simp [smul_eq_mul, nsmul_eq_mul, mul_assoc]
  simp only [chartCurrent, fieldAction_scale, fieldDivergence_scale, hdiff, laurentD_succ,
    map_sub, Derivation.leibniz, smul_eq_mul]
  linear_combination -P * h ^ j * (fieldAction δ v h) * hc

lemma partial_sum (δ : ι → Derivation ℚ K K) (P h A : K) (q : ℕ → ι → K) (m : ℕ)
    (hzero : chartCurrent δ P (q 0) + chartCurrent δ (P * h) (q 1) = A)
    (hpolar : ∀ j, j < m → chartCurrent δ P (q (j + 1)) + chartCurrent δ (P * h) (q (j + 2)) = 0) :
    chartCurrent δ P (laurentCorrected h q m) =
      A - algebraMap ℚ K (laurentD m) * h ^ m * chartCurrent δ (P * h) (q (m + 1)) := by
  induction m with
  | zero =>
    have hz : laurentCorrected h q 0 = q 0 := by ext i; simp [laurentCorrected, laurentC]
    rw [hz]
    simpa [laurentD, eq_sub_iff_add_eq] using hzero
  | succ m ih =>
    have prev := ih (fun j hj => hpolar j (by omega))
    have next := hpolar m (by omega)
    rw [show laurentCorrected h q (m + 1) = laurentCorrected h q m +
         (fun i => algebraMap ℚ K (laurentC (m + 1)) * h ^ (m + 1) * q (m + 1) i) by
           unfold laurentCorrected
           rw [Finset.sum_range_succ _ (m + 1)], chartCurrent_add, prev, term]
    linear_combination (algebraMap ℚ K (laurentD (m + 1)) * h ^ (m + 1)) * next

end Telescoping
end FP5Specialize

theorem solution :
    ∀ {ι K : Type} [Fintype ι] [Field K] [CharZero K]
      (δ : ι → Derivation ℚ K K) (P S A : K),
      P ≠ 0 →
      ∀ (q : ℕ → ι → K) (m : ℕ),
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (q 0) +
            HodgeComputer.FourPlusTwoResidual.chartCurrent δ S (q 1) = A →
        (∀ j, j < m →
          HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (q (j + 1)) +
              HodgeComputer.FourPlusTwoResidual.chartCurrent δ S (q (j + 2)) = 0) →
        q (m + 1) = 0 →
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P
            (HodgeComputer.FourPlusTwoResidual.laurentCorrected (S / P) q m) = A := by
  intro ι K _ _ _ δ P S A hP q m hzero hpolar htop
  have hp : P * (S / P) = S := by field_simp
  have h := FP5Specialize.partial_sum δ P (S / P) A q m (by simpa only [hp] using hzero)
    (fun j hj => by simpa only [hp] using hpolar j hj)
  rw [h, htop]
  simp [HodgeComputer.FourPlusTwoResidual.chartCurrent,
    HodgeComputer.FourPlusTwoResidual.fieldDivergence]
