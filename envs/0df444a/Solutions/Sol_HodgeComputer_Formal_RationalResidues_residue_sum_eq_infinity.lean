-- Prove2me | solution 1 for HodgeComputer.Formal.RationalResidues.residue_sum_eq_infinity
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:24:40.648102+00:00
-- url     : https://prove2.me/submissions/987bc711-f052-4aac-8a22-9ddd5b7e3ee0

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Tactic

set_option autoImplicit false

/- Source component: RationalPartialFractions. -/
section

noncomputable section
open scoped BigOperators
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma eq_constant_of_degree_lt_linear (a : K) (P : K[X])
    (hP : P.degree < (X-C a).degree) : P = C (P.coeff 0) := by
  by_cases hz : P=0
  · simp [hz]
  have hn : P.natDegree < 1 :=
    (natDegree_lt_iff_degree_lt hz).mpr (by simpa using hP)
  exact eq_C_of_natDegree_eq_zero (by omega)

/-- Finite partial fractions with constant principal coefficients.
The splitting hypothesis can be obtained in a finite splitting field. -/
lemma exists_global_principal_parts (f : RatFunc K)
    (hsplit : f.denom.Splits) :
    ∃ (s : Finset K) (n : K → ℕ) (c : (a : K) → Fin (n a) → K) (P : K[X]),
      f = algebraMap K[X] (RatFunc K) P + ∑ a ∈ s, ∑ j : Fin (n a),
        RatFunc.C (c a j) * ((uniformizer a)^(j.val+1))⁻¹ := by
  classical
  let Q := f.denom
  let lc := Q.leadingCoeff
  have hlc : lc ≠ 0 := leadingCoeff_ne_zero.mpr f.denom_ne_zero
  let s := Q.roots.toFinset
  let n : K → ℕ := fun a => Q.rootMultiplicity a
  have hq : Q = C lc * ∏ a ∈ s, (X-C a)^n a := by
    calc Q = C lc * (Q.roots.map (fun a => X-C a)).prod := hsplit.eq_prod_roots
         _ = _ := by rw [prod_multiset_root_eq_finset_root]
  have hpair : Set.Pairwise (↑s : Set K) (fun a b => IsCoprime (X-C a) (X-C b)) := by
    intro a ha b hb hab
    exact pairwise_coprime_X_sub_C (fun x y h => h) hab
  have hinv (a : K) (ha : a ∈ s) :
      ((uniformizer a)⁻¹) * algebraMap K[X] (RatFunc K) (X-C a) = 1 := by
    exact inv_mul_cancel₀ (uniformizer_ne_zero a)
  obtain ⟨P,r,hr,he⟩ :=
    mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      (K := RatFunc K) (C lc⁻¹*f.num)
      (fun a (_ : a ∈ s) => monic_X_sub_C a) hpair n hinv
  refine ⟨s,n,fun a j => (r a j).coeff 0,P,?_⟩
  have heleft : algebraMap K[X] (RatFunc K) (C lc⁻¹*f.num) *
      ∏ a ∈ s, ((uniformizer a)⁻¹)^n a = f := by
    conv_rhs => rw [← f.num_div_denom]
    conv_rhs => rw [show f.denom = Q from rfl,hq]
    simp only [map_mul,map_prod,map_pow,RatFunc.algebraMap_C]
    change _ = _ / (RatFunc.C lc * ∏ a ∈ s, (uniformizer a)^n a)
    simp only [inv_pow,← Finset.prod_inv_distrib,div_eq_mul_inv,mul_inv_rev,
      map_inv₀]
    ring
  rw [heleft] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j hj
  rw [eq_constant_of_degree_lt_linear a _ (hr a ha j)]
  simp only [RatFunc.algebraMap_C,inv_pow]

end CrossedRationalResidue
end
end

/- Source component: RationalResidueSum. -/
section

noncomputable section
open scoped BigOperators
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma residue_term_other (a b c : K) (n : ℕ) (hab : a ≠ b) :
    residue a (RatFunc.C c*((uniformizer b)^(n+1))⁻¹) = 0 := by
  apply RegularAt.residue_eq_zero
  refine ⟨C c,(X-C b)^(n+1),?_,?_⟩
  · simpa using pow_ne_zero (n+1) (sub_ne_zero.mpr hab)
  · simp [div_eq_mul_inv,uniformizer]

lemma sum_residue_term (s : Finset K) (b c : K) (n : ℕ) (hb : b ∈ s) :
    (∑ a ∈ s, residue a (RatFunc.C c*((uniformizer b)^(n+1))⁻¹)) =
      infinityCoefficient (RatFunc.C c*((uniformizer b)^(n+1))⁻¹) := by
  classical
  rw [Finset.sum_eq_single b,residue_term,infinityCoefficient_term]
  · intro a ha hab
    exact residue_term_other a b c n hab
  · exact fun h => (h hb).elim

/-- The sum of all finite residues is the coefficient of `X⁻¹` at infinity. -/
lemma exists_finite_residue_sum (f : RatFunc K) (hsplit : f.denom.Splits) :
    ∃ s : Finset K, (∀ a ∉ s, residue a f = 0) ∧
      ∑ a ∈ s, residue a f = infinityCoefficient f := by
  classical
  obtain ⟨s,n,c,P,hf⟩ := exists_global_principal_parts f hsplit
  refine ⟨s,?_,?_⟩
  · intro a ha
    rw [hf,map_add,residue_polynomial,zero_add]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro b hb
    apply Finset.sum_eq_zero
    intro j hj
    apply residue_term_other
    intro h
    exact ha (h ▸ hb)
  · rw [hf,map_add,infinityCoefficient_polynomial,zero_add]
    simp only [map_add,map_sum,residue_polynomial,zero_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact sum_residue_term s b (c b j) j.val hb

/-- A finite set containing every pole can be enlarged without changing the sum. -/
lemma residue_sum_eq_infinity (f : RatFunc K) (hsplit : f.denom.Splits)
    (s : Finset K) (houtside : ∀ a ∉ s, residue a f = 0) :
    ∑ a ∈ s, residue a f = infinityCoefficient f := by
  classical
  obtain ⟨t,ht,he⟩ := exists_finite_residue_sum f hsplit
  rw [← he]
  calc
    ∑ a ∈ s, residue a f = ∑ a ∈ s ∪ t, residue a f := by
      exact Finset.sum_subset Finset.subset_union_left
        (fun a ha has => houtside a has)
    _ = ∑ a ∈ t, residue a f := by
      exact (Finset.sum_subset Finset.subset_union_right
        (fun a ha hat => ht a hat)).symm

end CrossedRationalResidue
end
end

open scoped BigOperators in
theorem solution
    {K : Type*} [Field K] (f : RatFunc K) (hsplit : f.denom.Splits) (s : Finset K)
    (houtside : ∀ a, a ∉ s → CrossedRationalResidue.residue a f = 0) :
    ∑ a ∈ s, CrossedRationalResidue.residue a f =
      CrossedRationalResidue.infinityCoefficient f :=
  CrossedRationalResidue.residue_sum_eq_infinity f hsplit s houtside
