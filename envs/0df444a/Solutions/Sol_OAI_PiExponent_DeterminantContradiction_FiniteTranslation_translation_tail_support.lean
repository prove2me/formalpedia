-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_tail_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:27:55.239277+00:00
-- url     : https://prove2.me/submissions/f58eee4f-1c38-4dba-941b-96f375ec903f

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.BigOperators.Ring.Finset

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

theorem solution
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