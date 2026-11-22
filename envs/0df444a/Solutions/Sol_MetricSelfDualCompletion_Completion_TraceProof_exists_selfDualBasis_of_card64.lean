-- Prove2me | solution 1 for MetricSelfDualCompletion.Completion.TraceProof.exists_selfDualBasis_of_card64
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:42:18.135664+00:00
-- url     : https://prove2.me/submissions/305de60a-e97c-439e-b252-13ab873f6f6b

import Mathlib


/-! A concrete six-dimensional binary field. The quotient/trace-matrix route
follows the public Lean-QECert construction (commit
4a64933303628b4f94c4567347e86636853f64a4), specialized here to Phi_9.
No AG host family or algorithm is assumed by this finite-algebra component. -/

open Polynomial
open scoped BigOperators Matrix

namespace MetricSelfDualCompletion.Completion.TraceProof

noncomputable section

def modulus : Polynomial (ZMod 2) := X ^ 6 + X ^ 3 + 1

lemma modulus_natDegree_le : modulus.natDegree ≤ 6 := by
  have h6 : (X ^ 6 : Polynomial (ZMod 2)).natDegree ≤ 6 := by simp
  have h3 : (X ^ 3 : Polynomial (ZMod 2)).natDegree ≤ 6 := by simp
  have h1 : (1 : Polynomial (ZMod 2)).natDegree ≤ 6 := by simp
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h6 h3) h1

lemma modulus_monic : modulus.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 6 modulus_natDegree_le
  norm_num [modulus, coeff_add, coeff_X_pow, coeff_one]

lemma modulus_natDegree : modulus.natDegree = 6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero modulus_natDegree_le
  norm_num [modulus, coeff_add, coeff_X_pow, coeff_one]

lemma modulus_eq_cyclotomic : modulus = cyclotomic 9 (ZMod 2) := by
  change modulus = cyclotomic (3 ^ (1 + 1)) (ZMod 2)
  rw [cyclotomic_prime_pow_eq_geom_sum (by norm_num : Nat.Prime 3)]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reducePow,
    Nat.reduceAdd, pow_zero, pow_one]
  unfold modulus
  ring

lemma modulus_irreducible : Irreducible modulus := by
  apply ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 9)
    (by norm_num)
  · rw [modulus_eq_cyclotomic]
  · rw [modulus_natDegree]
    symm
    apply (orderOf_eq_iff (by norm_num : 0 < 6)).mpr
    constructor
    · apply Units.ext
      norm_num [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
      decide
    · intro m hm0 hm6 h
      have hv := congrArg Units.val h
      interval_cases m <;>
        norm_num [ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val] at hv <;>
          revert hv <;> decide

instance modulus_irreducible_fact : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩

abbrev F64 : Type := AdjoinRoot modulus

instance : Module.Finite (ZMod 2) F64 := modulus_monic.finite_adjoinRoot
instance : Finite F64 := Module.finite_of_finite (ZMod 2)
instance : Fintype F64 := Fintype.ofFinite F64
instance : CharP F64 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F64).injective 2

def polynomialBasis : Module.Basis (Fin 6) (ZMod 2) F64 :=
  (AdjoinRoot.powerBasis' modulus_monic).basis.reindex (finCongr modulus_natDegree)

def alpha : F64 := AdjoinRoot.root modulus

lemma polynomialBasis_apply (i : Fin 6) : polynomialBasis i = alpha ^ (i : ℕ) := by
  rw [polynomialBasis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' modulus_monic).basis_eq_pow]
  rfl

lemma field_finrank : Module.finrank (ZMod 2) F64 = 6 := by
  simpa [F64, modulus_natDegree] using (AdjoinRoot.powerBasis' modulus_monic).finrank

lemma field_card : Fintype.card F64 = 64 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F64), ZMod.card, field_finrank]
  norm_num

end
end MetricSelfDualCompletion.Completion.TraceProof


open Polynomial
open scoped BigOperators Matrix

namespace MetricSelfDualCompletion.Completion.TraceProof

noncomputable section

lemma alpha_pow_eq_mk (k : ℕ) : alpha ^ k = AdjoinRoot.mk modulus (X ^ k) := by
  simp [alpha, ← AdjoinRoot.mk_X]

lemma alpha_pow_nine : alpha ^ 9 = 1 := by
  rw [alpha_pow_eq_mk, ← (AdjoinRoot.mk modulus).map_one, AdjoinRoot.mk_eq_mk]
  refine ⟨X ^ 3 - 1, ?_⟩
  simp only [modulus]
  ring

lemma alpha_six_add_three : alpha ^ 6 + alpha ^ 3 = 1 := by
  have hp : alpha ^ 6 + alpha ^ 3 + 1 = 0 := by
    have h : AdjoinRoot.mk modulus modulus = 0 := AdjoinRoot.mk_self
    change AdjoinRoot.mk modulus (X ^ 6 + X ^ 3 + 1) = 0 at h
    simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, alpha] using h
  have htwo : (2 : F64) = 0 := CharP.ofNat_eq_zero' (R := F64) 2 2 (by norm_num)
  linear_combination hp - htwo

lemma trace_one : Algebra.trace (ZMod 2) F64 (1 : F64) = 0 := by
  apply (algebraMap (ZMod 2) F64).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [field_finrank, Nat.card_zmod]
  exact CharP.ofNat_eq_zero' (R := F64) 2 6 (by norm_num)

lemma trace_alpha : Algebra.trace (ZMod 2) F64 alpha = 0 := by
  change Algebra.trace (ZMod 2) F64 (AdjoinRoot.powerBasis' modulus_monic).gen = 0
  rw [(AdjoinRoot.powerBasis' modulus_monic).trace_gen_eq_nextCoeff_minpoly]
  change -(minpoly (ZMod 2) (AdjoinRoot.root modulus)).nextCoeff = 0
  rw [AdjoinRoot.minpoly_root modulus_monic.ne_zero]
  rw [modulus_monic.leadingCoeff, inv_one, C.map_one, mul_one]
  change -modulus.nextCoeff = 0
  rw [nextCoeff, modulus_natDegree]
  norm_num [modulus, coeff_add, coeff_X_pow, coeff_one]

lemma trace_square (x : F64) :
    Algebra.trace (ZMod 2) F64 (x ^ 2) = Algebra.trace (ZMod 2) F64 x := by
  apply (algebraMap (ZMod 2) F64).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, field_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  norm_num
  have hx : x ^ 64 = x := by
    rw [← field_card]
    exact FiniteField.pow_card x
  rw [hx]
  ring

lemma trace_alpha_three : Algebra.trace (ZMod 2) F64 (alpha ^ 3) = 1 := by
  apply (algebraMap (ZMod 2) F64).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  norm_num [Finset.sum_range_succ, field_finrank, Nat.card_zmod]
  simp only [← pow_mul]
  norm_num
  rw [pow_eq_pow_mod 96 alpha_pow_nine, pow_eq_pow_mod 48 alpha_pow_nine,
    pow_eq_pow_mod 24 alpha_pow_nine, pow_eq_pow_mod 12 alpha_pow_nine]
  norm_num only [Nat.reduceMod]
  have htwo : (2 : F64) = 0 := CharP.ofNat_eq_zero' (R := F64) 2 2 (by norm_num)
  linear_combination 3 * alpha_six_add_three + htwo

lemma trace_alpha_powers (k : Fin 11) :
    Algebra.trace (ZMod 2) F64 (alpha ^ (k : ℕ)) =
      ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0] k := by
  have h2 : Algebra.trace (ZMod 2) F64 (alpha ^ 2) = 0 := by
    simpa using (trace_square alpha).trans trace_alpha
  have h4 : Algebra.trace (ZMod 2) F64 (alpha ^ 4) = 0 := by
    simpa only [← pow_mul] using (trace_square (alpha ^ 2)).trans h2
  have h8 : Algebra.trace (ZMod 2) F64 (alpha ^ 8) = 0 := by
    simpa only [← pow_mul] using (trace_square (alpha ^ 4)).trans h4
  have h7 : Algebra.trace (ZMod 2) F64 (alpha ^ 7) = 0 := by
    have he : alpha ^ 16 = alpha ^ 7 := by rw [pow_eq_pow_mod 16 alpha_pow_nine]
    simpa only [← pow_mul, he] using (trace_square (alpha ^ 8)).trans h8
  have h5 : Algebra.trace (ZMod 2) F64 (alpha ^ 5) = 0 := by
    have he : alpha ^ 14 = alpha ^ 5 := by rw [pow_eq_pow_mod 14 alpha_pow_nine]
    simpa only [← pow_mul, he] using (trace_square (alpha ^ 7)).trans h7
  have h6 : Algebra.trace (ZMod 2) F64 (alpha ^ 6) = 1 := by
    simpa only [← pow_mul] using (trace_square (alpha ^ 3)).trans trace_alpha_three
  have h10 : Algebra.trace (ZMod 2) F64 (alpha ^ 10) = 0 := by
    have he : alpha ^ 10 = alpha := by rw [pow_eq_pow_mod 10 alpha_pow_nine]; simp
    simpa only [he] using trace_alpha
  fin_cases k <;>
    norm_num [trace_one, trace_alpha, trace_alpha_three, h2, h4, h5, h6, h7, h8, h10,
      alpha_pow_nine]

end
end MetricSelfDualCompletion.Completion.TraceProof


open Polynomial
open scoped BigOperators Matrix

namespace MetricSelfDualCompletion.Completion.TraceProof

noncomputable section

def polynomialTraceGram : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 1;
     0, 1, 0, 0, 1, 0;
     1, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 1, 0, 0, 0, 0]

def selfDualP : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1;
     0, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 0, 0;
     1, 1, 1, 1, 1, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

def selfDualPInv : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0;
     1, 0, 1, 0, 0, 1;
     1, 1, 0, 0, 1, 0;
     1, 1, 1, 0, 1, 0;
     1, 1, 1, 0, 0, 1;
     1, 1, 1, 0, 0, 0]

lemma polynomialTraceMatrix_eq :
    Algebra.traceMatrix (ZMod 2) polynomialBasis = polynomialTraceGram := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    polynomialBasis_apply, polynomialBasis_apply, ← pow_add]
  rw [trace_alpha_powers ⟨(i : ℕ) + (j : ℕ), by omega⟩]
  fin_cases i <;> fin_cases j <;> norm_num [polynomialTraceGram]

lemma selfDualP_mul_inv : selfDualP * selfDualPInv = 1 := by decide
lemma selfDualPInv_mul : selfDualPInv * selfDualP = 1 := by decide
lemma selfDualP_transpose_mul_gram_mul :
    selfDualP.transpose * polynomialTraceGram * selfDualP = 1 := by decide

def selfDualChange : F64 ≃ₗ[ZMod 2] F64 :=
  Matrix.toLinearEquiv polynomialBasis selfDualP
    (Matrix.isUnit_det_of_right_inverse selfDualP_mul_inv)

def selfDualBasis : Module.Basis (Fin 6) (ZMod 2) F64 :=
  polynomialBasis.map selfDualChange

lemma selfDualBasis_apply (i : Fin 6) : selfDualBasis i =
    (polynomialBasis ᵥ* selfDualP.map (algebraMap (ZMod 2) F64)) i := by
  rw [selfDualBasis, Module.Basis.map_apply, selfDualChange]
  change Matrix.toLin polynomialBasis polynomialBasis selfDualP (polynomialBasis i) = _
  rw [Matrix.toLin_self]
  simp only [Matrix.vecMul, dotProduct, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl

lemma selfDualBasis_traceMatrix : Algebra.traceMatrix (ZMod 2) selfDualBasis = 1 := by
  have hb : (selfDualBasis : Fin 6 → F64) =
      polynomialBasis ᵥ* selfDualP.map (algebraMap (ZMod 2) F64) := funext selfDualBasis_apply
  rw [hb, Algebra.traceMatrix_of_matrix_vecMul, polynomialTraceMatrix_eq]
  exact selfDualP_transpose_mul_gram_mul

theorem selfDualBasis_trace_mul (i j : Fin 6) :
    Algebra.trace (ZMod 2) F64 (selfDualBasis i * selfDualBasis j) =
      if i = j then 1 else 0 := by
  have h := congr_fun (congr_fun selfDualBasis_traceMatrix i) j
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply] using h

theorem selfDualBasis_traceDual : selfDualBasis.traceDual = selfDualBasis := by
  apply DFunLike.ext _ _
  have h : (selfDualBasis.traceDual : Fin 6 → F64) = (selfDualBasis : Fin 6 → F64) := by
    apply Module.Basis.traceDual_eq_iff.mpr
    intro i j
    simpa only [Algebra.traceForm_apply, eq_comm] using selfDualBasis_trace_mul i j
  intro i
  exact congr_fun h i

end
end MetricSelfDualCompletion.Completion.TraceProof


namespace MetricSelfDualCompletion.Completion.TraceProof

noncomputable section

/-- The concrete basis is available over any carrier with exactly 64 elements,
so an AG implementation need not use the quotient type chosen here. -/
def selectedSelfDualBasis (E : Type*) [Field E] [Fintype E] [Algebra (ZMod 2) E]
    (hcard : Fintype.card E = 64) : Module.Basis (Fin 6) (ZMod 2) E :=
  selfDualBasis.map
    (FiniteField.algEquivOfCardEq 2 (field_card.trans hcard.symm)).toLinearEquiv

theorem selectedSelfDualBasis_trace_mul (E : Type*) [Field E] [Fintype E]
    [Algebra (ZMod 2) E] (hcard : Fintype.card E = 64) :
    ∀ i j, Algebra.trace (ZMod 2) E
      (selectedSelfDualBasis E hcard i * selectedSelfDualBasis E hcard j) =
        if i = j then 1 else 0 := by
  intro i j
  let e : F64 ≃ₐ[ZMod 2] E :=
    FiniteField.algEquivOfCardEq 2 (field_card.trans hcard.symm)
  change Algebra.trace (ZMod 2) E (e (selfDualBasis i) * e (selfDualBasis j)) = _
  rw [← map_mul, Algebra.trace_eq_of_algEquiv]
  exact selfDualBasis_trace_mul i j

theorem exists_selfDualBasis_of_card64 (E : Type*) [Field E] [Fintype E]
    [Algebra (ZMod 2) E] (hcard : Fintype.card E = 64) :
    ∃ b : Module.Basis (Fin 6) (ZMod 2) E, ∀ i j,
      Algebra.trace (ZMod 2) E (b i * b j) = if i = j then 1 else 0 :=
  ⟨selectedSelfDualBasis E hcard, selectedSelfDualBasis_trace_mul E hcard⟩

end
end MetricSelfDualCompletion.Completion.TraceProof

open MetricSelfDualCompletion.Completion.TraceProof
open scoped BigOperators
open scoped Matrix

theorem solution
    (E : Type*) [Field E] [Fintype E] [Algebra (ZMod 2) E]
    (hcard : Fintype.card E = 64) :
    ∃ b : Module.Basis (Fin 6) (ZMod 2) E, ∀ i j,
      Algebra.trace (ZMod 2) E (b i * b j) = if i = j then 1 else 0  := by exact MetricSelfDualCompletion.Completion.TraceProof.exists_selfDualBasis_of_card64 E hcard
