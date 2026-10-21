-- Prove2me | solution 1 for OAI.PiExponent.WeightedDivision.reduce_selected_monic_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:49:00.36582+00:00
-- url     : https://prove2.me/submissions/03a4aec9-39b7-4910-96e6-0ddf0c7b7de0

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators Pointwise

private noncomputable def blockWeight {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (a : ι →₀ ℕ) : ℝ :=
  ∑ i, d i * (a i : ℝ)

private theorem blockWeight_add {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (a b : ι →₀ ℕ) :
    blockWeight d (a + b) = blockWeight d a + blockWeight d b := by
  simp only [blockWeight, Finsupp.add_apply, Nat.cast_add, mul_add,
    Finset.sum_add_distrib]

private theorem blockWeight_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (i : ι) (n : ℕ) :
    blockWeight d (Finsupp.single i n) = d i * (n : ℝ) := by
  classical
  unfold blockWeight
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

-- A polynomial with a lower-weight error has no terms above its reference monomial.
private theorem support_le_of_lower_error
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ) (a : ι →₀ ℕ) (P : MvPolynomial ι R)
    (hP : ∀ v ∈ (MvPolynomial.monomial a (1 : R) - P).support,
      blockWeight d v < blockWeight d a) :
    ∀ v ∈ P.support, blockWeight d v ≤ blockWeight d a := by
  classical
  intro v hv
  have hv' : v ∈ (MvPolynomial.monomial a (1 : R) -
      (MvPolynomial.monomial a (1 : R) - P)).support := by
    simpa only [sub_sub_cancel] using hv
  rcases Finset.mem_union.mp (MvPolynomial.support_sub ι _ _ hv') with h | h
  · have heq : v = a :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst v
    exact le_rfl
  · exact (hP v h).le

-- Multiplication preserves a monic term modulo strictly lower-weight support.
private theorem lower_error_mul
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ) (a b : ι →₀ ℕ) (P Q : MvPolynomial ι R)
    (hP : ∀ v ∈ (MvPolynomial.monomial a (1 : R) - P).support,
      blockWeight d v < blockWeight d a)
    (hQ : ∀ v ∈ (MvPolynomial.monomial b (1 : R) - Q).support,
      blockWeight d v < blockWeight d b) :
    ∀ v ∈ (MvPolynomial.monomial (a + b) (1 : R) - P * Q).support,
      blockWeight d v < blockWeight d (a + b) := by
  classical
  have hPle := support_le_of_lower_error d a P hP
  have heq : MvPolynomial.monomial (a + b) (1 : R) - P * Q =
      (MvPolynomial.monomial a (1 : R) - P) * MvPolynomial.monomial b (1 : R) +
      P * (MvPolynomial.monomial b (1 : R) - Q) := by
    have hm : MvPolynomial.monomial (a + b) (1 : R) =
        MvPolynomial.monomial a (1 : R) * MvPolynomial.monomial b (1 : R) := by
      simp only [MvPolynomial.monomial_mul, mul_one]
    rw [hm]
    ring
  intro v hv
  rw [heq] at hv
  rcases Finset.mem_union.mp (MvPolynomial.support_add hv) with h | h
  · rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ h) with
      ⟨x, hx, y, hy, rfl⟩
    have hy' : y = b :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hy)
    subst y
    simpa only [blockWeight_add] using
      add_lt_add_left (hP x hx) (blockWeight d b)
  · rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ h) with
      ⟨x, hx, y, hy, rfl⟩
    simpa only [blockWeight_add] using
      add_lt_add_of_le_of_lt (hPle x hx) (hQ y hy)

private theorem lower_error_pow
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ) (a : ι →₀ ℕ) (P : MvPolynomial ι R)
    (hP : ∀ v ∈ (MvPolynomial.monomial a (1 : R) - P).support,
      blockWeight d v < blockWeight d a) (n : ℕ) :
    ∀ v ∈ (MvPolynomial.monomial (n • a) (1 : R) - P ^ n).support,
      blockWeight d v < blockWeight d (n • a) := by
  induction n with
  | zero =>
      simp only [zero_smul, pow_zero, ← MvPolynomial.one_def, sub_self,
        MvPolynomial.support_zero, Finset.notMem_empty, false_implies, implies_true]
  | succ n ih =>
      simpa only [succ_nsmul, pow_succ] using
        lower_error_mul d (n • a) a (P ^ n) P ih hP

private theorem lower_error_prod
    {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ) (a : κ → ι →₀ ℕ) (P : κ → MvPolynomial ι R)
    (hP : ∀ i, ∀ v ∈ (MvPolynomial.monomial (a i) (1 : R) - P i).support,
      blockWeight d v < blockWeight d (a i)) (t : Finset κ) :
    ∀ v ∈ (MvPolynomial.monomial (∑ i ∈ t, a i) (1 : R) -
      ∏ i ∈ t, P i).support,
      blockWeight d v < blockWeight d (∑ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Finset.prod_empty, ← MvPolynomial.one_def,
        sub_self, MvPolynomial.support_zero, Finset.notMem_empty,
        false_implies, implies_true]
  | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi, Finset.prod_insert hi] using
        lower_error_mul d (a i) (∑ j ∈ t, a j) (P i) (∏ j ∈ t, P j) (hP i) ih

theorem solution
    {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (d : ι → ℝ)
    (b : ι → ℕ) (hb : ∀ i, 0 < b i)
    (F : ι → MvPolynomial ι R)
    (hbelow : ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, d j * (v j : ℝ)) < d i * (b i : ℝ))
    (s : ℕ) (u : ι →₀ ℕ) (k : ι → ℕ)
    (hkdiv : ∀ i, k i * b i ≤ u i)
    (hksum : ∑ i, k i = s) :
    ∃ G : MvPolynomial ι R,
      G ∈ (Ideal.span (Set.range F)) ^ s ∧
      ∀ v ∈ (MvPolynomial.monomial u (1 : R) - G).support,
        (∑ i, d i * (v i : ℝ)) < (∑ i, d i * (u i : ℝ)) := by
  classical
  let B : ι →₀ ℕ := ∑ i : ι, Finsupp.single i (k i * b i)
  let rem : ι →₀ ℕ := u - B
  let P : MvPolynomial ι R := ∏ i : ι, F i ^ k i
  let J : Ideal (MvPolynomial ι R) := Ideal.span (Set.range F)
  have hBval (i : ι) : B i = k i * b i := by
    simp [B, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hB : B ≤ u := by
    intro i
    rw [hBval]
    exact hkdiv i
  have hrem : rem + B = u := tsub_add_cancel_of_le hB
  have hbase (i : ι) :
      ∀ v ∈ (MvPolynomial.monomial (Finsupp.single i (b i)) (1 : R) - F i).support,
        blockWeight d v < blockWeight d (Finsupp.single i (b i)) := by
    intro v hv
    rw [blockWeight_single]
    exact hbelow i v (by simpa only [MvPolynomial.X_pow_eq_monomial] using hv)
  have hpowers (i : ι) :
      ∀ v ∈ (MvPolynomial.monomial (Finsupp.single i (k i * b i)) (1 : R) -
        F i ^ k i).support,
        blockWeight d v < blockWeight d (Finsupp.single i (k i * b i)) := by
    simpa only [Finsupp.smul_single, smul_eq_mul] using
      lower_error_pow d (Finsupp.single i (b i)) (F i) (hbase i) (k i)
  have hP : ∀ v ∈ (MvPolynomial.monomial B (1 : R) - P).support,
      blockWeight d v < blockWeight d B :=
    lower_error_prod d (fun i => Finsupp.single i (k i * b i))
      (fun i => F i ^ k i) hpowers Finset.univ
  have hprod : P ∈ J ^ s := by
    have hmem : ∀ i ∈ (Finset.univ : Finset ι), F i ^ k i ∈ J ^ k i := by
      intro i _
      exact Ideal.pow_mem_pow (show F i ∈ J from Ideal.subset_span ⟨i, rfl⟩) (k i)
    have hp := Ideal.prod_mem_prod hmem
    simpa only [Finset.prod_pow_eq_pow_sum, hksum] using hp
  refine ⟨MvPolynomial.monomial rem (1 : R) * P, ?_, ?_⟩
  · exact (J ^ s).mul_mem_left _ hprod
  · have hid : ∀ v ∈ (MvPolynomial.monomial rem (1 : R) -
        MvPolynomial.monomial rem (1 : R)).support,
        blockWeight d v < blockWeight d rem := by
      simp
    have hfinal := lower_error_mul d rem B (MvPolynomial.monomial rem (1 : R)) P hid hP
    rw [hrem] at hfinal
    exact hfinal
