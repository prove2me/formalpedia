-- Prove2me | solution 1 for Grunbaum2003.g_theorem_sufficiency_pos_g2_from_upper_triangular
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T23:30:59.343622+00:00
-- url     : https://prove2.me/submissions/f7f81fb3-0a49-43b2-bd61-181d171abb4b

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max
import Definitions.Def_Grunbaum2003_IsMSequence
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ext
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Erase
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

-- BEGIN GSufficiencyNextKronecker.lean
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.BilleraLee

/-- The ordinary base-`B` integer encoded by a finite exponent vector. -/
def kroneckerWeight {n : ℕ} (B : ℕ) (a : Fin n → ℕ) : ℕ :=
  ∑ i, a i * B ^ i.val

theorem kroneckerWeight_succ {n : ℕ} (B : ℕ) (a : Fin (n + 1) → ℕ) :
    kroneckerWeight B a = kroneckerWeight B (fun i => a i.castSucc) +
      a (Fin.last n) * B ^ n := by
  simp only [kroneckerWeight, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem kroneckerWeight_lt_pow {n : ℕ} (B : ℕ) (hB : 0 < B)
    (a : Fin n → ℕ) (ha : ∀ i, a i < B) : kroneckerWeight B a < B ^ n := by
  induction n with
  | zero => simp only [kroneckerWeight, Fin.sum_univ_zero, pow_zero, Nat.zero_lt_one]
  | succ n ih =>
      rw [kroneckerWeight_succ]
      calc
        kroneckerWeight B (fun i => a i.castSucc) + a (Fin.last n) * B ^ n
            < B ^ n + a (Fin.last n) * B ^ n :=
          Nat.add_lt_add_right (ih _ (fun i => ha i.castSucc)) _
        _ = (a (Fin.last n) + 1) * B ^ n := by ring
        _ ≤ B * B ^ n := Nat.mul_le_mul_right _ (ha (Fin.last n))
        _ = B ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Base encoding respects comparison at the last unequal coordinate, provided
the smaller vector's digits are less than the base. -/
theorem kroneckerWeight_lt_of_colex {n : ℕ} (B : ℕ) (hB : 0 < B)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < B)
    (hab : ∃ i, a i < b i ∧ ∀ j, i < j → a j = b j) :
    kroneckerWeight B a < kroneckerWeight B b := by
  induction n with
  | zero => obtain ⟨i, _, _⟩ := hab; exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨r, hr, heq⟩ := hab
      rw [kroneckerWeight_succ, kroneckerWeight_succ]
      by_cases hlast : r = Fin.last n
      · subst r
        calc
          kroneckerWeight B (fun i => a i.castSucc) + a (Fin.last n) * B ^ n
              < B ^ n + a (Fin.last n) * B ^ n :=
            Nat.add_lt_add_right (kroneckerWeight_lt_pow B hB _
              (fun i => ha i.castSucc)) _
          _ = (a (Fin.last n) + 1) * B ^ n := by ring
          _ ≤ b (Fin.last n) * B ^ n := Nat.mul_le_mul_right _ hr
          _ ≤ kroneckerWeight B (fun i => b i.castSucc) + b (Fin.last n) * B ^ n :=
            Nat.le_add_left _ _
      · have hrn : r.val < n := by
          have hne : r.val ≠ n := fun h => hlast (Fin.ext h)
          omega
        let r' : Fin n := ⟨r.val, hrn⟩
        have hcast : r'.castSucc = r := Fin.ext rfl
        have heqlast : a (Fin.last n) = b (Fin.last n) :=
          heq _ (show r < Fin.last n from hrn)
        rw [heqlast]
        apply Nat.add_lt_add_right
        apply ih _ _ (fun i => ha i.castSucc)
        refine ⟨r', ?_, ?_⟩
        · simpa only [hcast] using hr
        · intro j hj
          apply heq
          change r.val < j.val
          exact hj

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextKronecker.lean

-- BEGIN GSufficiencyNextPositiveEvaluation.lean
set_option autoImplicit false
open scoped Classical BigOperators
open Filter

namespace Grunbaum2003.BilleraLee

/-- Kronecker substitution of an actual sparse polynomial. -/
noncomputable def kroneckerPolynomial {n : ℕ} (B : ℕ)
    (p : MvPolynomial (Fin n) ℚ) : Polynomial ℚ :=
  ∑ a ∈ p.support, Polynomial.monomial (kroneckerWeight B a) (p.coeff a)

theorem eval_kroneckerPolynomial {n : ℕ} (B : ℕ)
    (p : MvPolynomial (Fin n) ℚ) (T : ℚ) :
    (kroneckerPolynomial B p).eval T =
      MvPolynomial.eval (fun i => T ^ (B ^ i.val)) p := by
  simp only [kroneckerPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  simp only [kroneckerWeight, ← pow_mul, Nat.mul_comm]
  exact (Finset.prod_pow_eq_pow_sum _ _ _).symm

theorem kroneckerPolynomial_leadingCoeff {n : ℕ} (B : ℕ) (hB : 0 < B)
    (p : MvPolynomial (Fin n) ℚ) (a : Fin n →₀ ℕ)
    (ha : p.coeff a ≠ 0)
    (hbound : ∀ b ∈ p.support, ∀ i, b i < B)
    (hlead : ∀ b ∈ p.support, b ≠ a →
      ∃ i, b i < a i ∧ ∀ j, i < j → b j = a j) :
    (kroneckerPolynomial B p).leadingCoeff = p.coeff a := by
  have hamem : a ∈ p.support := MvPolynomial.mem_support_iff.mpr ha
  have hlt : ∀ b ∈ p.support, b ≠ a →
      kroneckerWeight B b < kroneckerWeight B a := by
    intro b hb hba
    exact kroneckerWeight_lt_of_colex B hB b a (hbound b hb) (hlead b hb hba)
  have hcoeff : (kroneckerPolynomial B p).coeff (kroneckerWeight B a) = p.coeff a := by
    simp only [kroneckerPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single a]
    · exact Polynomial.coeff_monomial_same _ _
    · intro b hb hba
      exact Polynomial.coeff_monomial_of_ne _ (ne_of_gt (hlt b hb hba))
    · exact fun h => (h hamem).elim
  have hdeg : (kroneckerPolynomial B p).natDegree ≤ kroneckerWeight B a := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro b hb
    apply (Polynomial.natDegree_monomial_le _).trans
    by_cases hba : b = a
    · exact hba ▸ le_rfl
    · exact (hlt b hb hba).le
  rw [Polynomial.leadingCoeff,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; exact ha), hcoeff]

theorem eventually_eval_pos_of_leadingCoeff_pos (p : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) : ∀ᶠ T : ℚ in atTop, 0 < p.eval T := by
  by_cases hdeg : p.natDegree = 0
  · have hc : p = Polynomial.C p.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff, hdeg] using
        (Polynomial.eq_C_of_natDegree_eq_zero hdeg)
    exact Filter.Eventually.of_forall fun T => by
      rw [hc, Polynomial.eval_C]
      exact hp
  · exact (p.tendsto_atTop_of_leadingCoeff_nonneg
      (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)) hp.le).eventually
        (eventually_gt_atTop 0)

/-- A finite family of polynomials whose actual last-variable-first leading
coefficients are positive has a simultaneous positive rational evaluation at
strictly increasing positive parameters. The leading exponent is given by its
coefficient and comparison with every other exponent in the actual support.

This is the positive-evaluation ingredient identified as Proposition 3 in the
official polymake V4.15 implementation of the Billera--Lee construction. The
proof uses an independent Kronecker substitution and polynomial asymptotics.
It supplies no assumption or conclusion about geometric visibility. -/
theorem exists_increasing_pos_eval_of_colex_leading_pos {n : ℕ}
    (P : Finset (MvPolynomial (Fin n) ℚ))
    (hP : ∀ p ∈ P, ∃ a : Fin n →₀ ℕ, 0 < p.coeff a ∧
      ∀ b ∈ p.support, b ≠ a → ∃ i, b i < a i ∧ ∀ j, i < j → b j = a j) :
    ∃ t : Fin n → ℚ, (∀ i, 0 < t i) ∧ StrictMono t ∧
      ∀ p ∈ P, 0 < MvPolynomial.eval t p := by
  classical
  let B := 2 + P.sup (fun p => p.support.sup (fun a => Finset.univ.sup (fun i => a i)))
  have hB : 1 < B := by dsimp [B]; omega
  have hbound : ∀ p ∈ P, ∀ a ∈ p.support, ∀ i, a i < B := by
    intro p hp a ha i
    have h₁ : a i ≤ Finset.univ.sup (fun j => a j) :=
      Finset.le_sup (f := fun j => a j) (Finset.mem_univ i)
    have h₂ := Finset.le_sup (f := fun a => Finset.univ.sup (fun i => a i)) ha
    have h₃ := Finset.le_sup
      (f := fun p => p.support.sup (fun a => Finset.univ.sup (fun i => a i))) hp
    dsimp only [B]
    omega
  have hevent : ∀ᶠ T : ℚ in atTop, ∀ p ∈ P, 0 < (kroneckerPolynomial B p).eval T := by
    apply (Filter.eventually_all_finset P).mpr
    intro p hp
    obtain ⟨a, ha, hlead⟩ := hP p hp
    apply eventually_eval_pos_of_leadingCoeff_pos
    rw [kroneckerPolynomial_leadingCoeff B (by omega) p a ha.ne' (hbound p hp) hlead]
    exact ha
  obtain ⟨T, hT, hpos⟩ := ((eventually_gt_atTop (1 : ℚ)).and hevent).exists
  refine ⟨fun i => T ^ (B ^ i.val), ?_, ?_, ?_⟩
  · intro i
    exact pow_pos (lt_trans zero_lt_one hT) _
  · intro i j hij
    exact pow_lt_pow_right₀ hT (pow_lt_pow_right₀ hB hij)
  · intro p hp
    rw [← eval_kroneckerPolynomial B p T]
    exact hpos p hp

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextPositiveEvaluation.lean

-- BEGIN GSufficiencyNextComparisonPolynomial.lean
set_option autoImplicit false
open scoped Classical BigOperators MonomialOrder

namespace Grunbaum2003.BilleraLee

/-- The source's order compares exponent vectors at the largest variable index. -/
noncomputable def colexMonomialOrder (n : ℕ) : MonomialOrder (Fin n) where
  syn := Colex (Fin n →₀ ℕ)
  toSyn := { toEquiv := toColex, map_add' := by intros; rfl }
  toSyn_monotone := Finsupp.toColex_monotone

theorem colexMonomialOrder_lt_iff {n : ℕ} (a b : Fin n →₀ ℕ) :
    a ≺[colexMonomialOrder n] b ↔
      ∃ i, a i < b i ∧ ∀ j, i < j → a j = b j := by
  change toColex a < toColex b ↔ _
  rw [Finsupp.Colex.lt_iff]
  constructor <;> rintro ⟨i, h₁, h₂⟩ <;> exact ⟨i, h₂, h₁⟩

theorem leadingCoeff_prod {σ α R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (o : MonomialOrder σ) (s : Finset α) (f : α → MvPolynomial σ R) :
    o.leadingCoeff (∏ j ∈ s, f j) = ∏ j ∈ s, o.leadingCoeff (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonomialOrder.leadingCoeff_one]
  | insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, MonomialOrder.leadingCoeff_mul, ih]

theorem degree_leadingCoeff_sum_of_dominant {σ α R : Type*} [CommRing R]
    (o : MonomialOrder σ) (B : Finset α) (f : α → MvPolynomial σ R)
    (c : α) (hcB : c ∈ B) (_hfc : f c ≠ 0)
    (hdom : ∀ b ∈ B, b ≠ c → f b = 0 ∨ o.degree (f b) ≺[o] o.degree (f c)) :
    o.degree (∑ b ∈ B, f b) = o.degree (f c) ∧
      o.leadingCoeff (∑ b ∈ B, f b) = o.leadingCoeff (f c) := by
  classical
  have hrest_le : o.degree (∑ b ∈ B.erase c, f b) ≼[o] o.degree (f c) := by
    apply (o.degree_sum_le (s := B.erase c) (f := f)).trans
    apply Finset.sup_le
    intro b hb
    obtain ⟨hbc, hbB⟩ := Finset.mem_erase.mp hb
    rcases hdom b hbB hbc with hzero | hlt
    · rw [hzero, MonomialOrder.degree_zero]
      exact o.toSyn_monotone (fun _ => Nat.zero_le _)
    · exact hlt.le
  have hrest_lt : (o.degree (∑ b ∈ B.erase c, f b) ≺[o] o.degree (f c)) ∨
      ∑ b ∈ B.erase c, f b = 0 := by
    by_cases hzero : ∑ b ∈ B.erase c, f b = 0
    · exact Or.inr hzero
    · left
      apply lt_of_le_of_ne hrest_le
      intro heq
      have hm : o.degree (∑ b ∈ B.erase c, f b) ∈ (∑ b ∈ B.erase c, f b).support :=
        o.degree_mem_support hzero
      obtain ⟨b, hb, hmb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
      obtain ⟨hbc, hbB⟩ := Finset.mem_erase.mp hb
      have hfb0 : f b ≠ 0 := by
        intro hfb0
        rw [hfb0, MvPolynomial.support_zero] at hmb
        exact Finset.notMem_empty _ hmb
      rcases hdom b hbB hbc with hfbz | hlt
      · exact hfb0 hfbz
      · have hle : o.toSyn (o.degree (∑ b ∈ B.erase c, f b)) ≤ o.toSyn (o.degree (f b)) :=
          o.le_degree hmb
        have hlt' : o.toSyn (o.degree (∑ b ∈ B.erase c, f b)) < o.toSyn (o.degree (f c)) :=
          lt_of_le_of_lt hle hlt
        rw [heq] at hlt'
        exact lt_irrefl _ hlt'
  rw [← Finset.add_sum_erase B f hcB]
  rcases hrest_lt with hlt | hzero
  · rw [o.degree_add_of_lt hlt, o.leadingCoeff_add_of_lt hlt]
    exact ⟨rfl, rfl⟩
  · rw [hzero, add_zero]
    exact ⟨rfl, rfl⟩

/-- Literal specialization of the first cyclic parameter to zero. -/
noncomputable def cyclicParameterVariable {N : ℕ} (j : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) ℚ := if j = 0 then 0 else MvPolynomial.X j

/-- The root product evaluated at a sampled parameter, still a multivariate
polynomial in the remaining cyclic parameters. -/
noncomputable def cyclicRootSample {N : ℕ} (F : Finset (Fin (N + 1)))
    (b : Fin (N + 1)) : MvPolynomial (Fin (N + 1)) ℚ :=
  ∏ j ∈ F, (cyclicParameterVariable b - cyclicParameterVariable j)

noncomputable def cyclicTailWeight {N : ℕ} (d : ℕ) (b : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) ℚ :=
  ∏ j ∈ Finset.univ.filter (fun j => b < j), MvPolynomial.X j ^ d

/-- The full root-product form of the comparison polynomial. With equally
sized facets its common top coefficient cancels, giving the coefficient sum
in Billera--Lee section 7, equation (4), as implemented by polymake V4.15. -/
noncomputable def cyclicComparisonPolynomial {N : ℕ} (d : ℕ)
    (B F G : Finset (Fin (N + 1))) : MvPolynomial (Fin (N + 1)) ℚ :=
  ∑ b ∈ B, cyclicTailWeight d b * (cyclicRootSample F b - cyclicRootSample G b)

theorem cyclicComparisonPolynomial_eq_sub {N : ℕ} (d : ℕ)
    (B F G : Finset (Fin (N + 1))) :
    cyclicComparisonPolynomial d B F G =
      (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample F b) -
      (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample G b) := by
  simp only [cyclicComparisonPolynomial, mul_sub, Finset.sum_sub_distrib]

theorem cyclicRootSample_eq_zero_of_mem {N : ℕ}
    (F : Finset (Fin (N + 1))) (b : Fin (N + 1)) (hb : b ∈ F) :
    cyclicRootSample F b = 0 := by
  apply Finset.prod_eq_zero hb
  exact sub_self _

theorem cyclicParameterDifference_degree_leading {N : ℕ}
    (b j : Fin (N + 1)) (hb : b ≠ 0) (hbj : b ≠ j) :
    (colexMonomialOrder (N + 1)).degree
      (cyclicParameterVariable b - cyclicParameterVariable j) =
        Finsupp.single (max b j) 1 ∧
    (colexMonomialOrder (N + 1)).leadingCoeff
      (cyclicParameterVariable b - cyclicParameterVariable j) =
        if b < j then (-1 : ℚ) else 1 := by
  let o := colexMonomialOrder (N + 1)
  by_cases hj : j = 0
  · subst j
    simp only [cyclicParameterVariable, if_neg hb, if_true, sub_zero]
    have hnot : ¬ b < (0 : Fin (N + 1)) := not_lt_of_ge (Fin.zero_le _)
    rw [if_neg hnot, max_eq_left (Fin.zero_le _),
      MonomialOrder.degree_X, MonomialOrder.leadingCoeff_X]
    exact ⟨rfl, rfl⟩
  · simp only [cyclicParameterVariable, if_neg hb, if_neg hj]
    by_cases hbjlt : b < j
    · have hdeg : o.degree (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) ℚ) ≺[o]
          o.degree (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℚ) := by
        rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
        change toColex (Finsupp.single b 1) < toColex (Finsupp.single j 1)
        exact Finsupp.Colex.single_lt_iff.mpr hbjlt
      have hswap : (MvPolynomial.X b - MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℚ) =
          -(MvPolynomial.X j - MvPolynomial.X b) := by ring
      rw [hswap, MonomialOrder.degree_neg, MonomialOrder.leadingCoeff_neg,
          o.degree_sub_of_lt hdeg, o.leadingCoeff_sub_of_lt hdeg,
          MonomialOrder.degree_X, MonomialOrder.leadingCoeff_X,
          if_pos hbjlt, max_eq_right hbjlt.le]
      exact ⟨rfl, rfl⟩
    · have hjblt : j < b := lt_of_le_of_ne (le_of_not_gt hbjlt) (Ne.symm hbj)
      have hdeg : o.degree (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℚ) ≺[o]
          o.degree (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) ℚ) := by
        rw [MonomialOrder.degree_X, MonomialOrder.degree_X]
        change toColex (Finsupp.single j 1) < toColex (Finsupp.single b 1)
        exact Finsupp.Colex.single_lt_iff.mpr hjblt
      rw [o.degree_sub_of_lt hdeg, o.leadingCoeff_sub_of_lt hdeg,
          MonomialOrder.degree_X, MonomialOrder.leadingCoeff_X,
          if_neg hbjlt, max_eq_left hjblt.le]
      exact ⟨rfl, rfl⟩

theorem cyclicRootSample_degree_leading {N : ℕ}
    (F : Finset (Fin (N + 1))) (b : Fin (N + 1)) (hb : b ≠ 0) (hbF : b ∉ F) :
    (colexMonomialOrder (N + 1)).degree (cyclicRootSample F b) =
        ∑ j ∈ F, Finsupp.single (max b j) 1 ∧
    (colexMonomialOrder (N + 1)).leadingCoeff (cyclicRootSample F b) =
        (-1 : ℚ) ^ (F.filter (fun j => b < j)).card := by
  let o := colexMonomialOrder (N + 1)
  have hfactor (j : Fin (N + 1)) (hj : j ∈ F) :=
    cyclicParameterDifference_degree_leading b j hb (fun h => hbF (h.symm ▸ hj))
  have hnz : ∀ j ∈ F, cyclicParameterVariable b - cyclicParameterVariable j ≠ 0 := by
    intro j hj
    apply o.leadingCoeff_ne_zero_iff.mp
    rw [(hfactor j hj).2]
    split_ifs <;> norm_num
  constructor
  · rw [cyclicRootSample, o.degree_prod hnz]
    exact Finset.sum_congr rfl (fun j hj => (hfactor j hj).1)
  · rw [cyclicRootSample, leadingCoeff_prod o F]
    calc
      (∏ j ∈ F, o.leadingCoeff (cyclicParameterVariable b - cyclicParameterVariable j)) =
          ∏ j ∈ F, if b < j then (-1 : ℚ) else 1 :=
        Finset.prod_congr rfl (fun j hj => (hfactor j hj).2)
      _ = (-1 : ℚ) ^ (F.filter (fun j => b < j)).card := by
        rw [← Finset.prod_filter]
        simp only [Finset.prod_const]

theorem cyclicTailWeight_degree_leading {N : ℕ} (d : ℕ) (b : Fin (N + 1)) :
    (colexMonomialOrder (N + 1)).degree (cyclicTailWeight d b) =
        ∑ j ∈ Finset.univ.filter (fun j => b < j), Finsupp.single j d ∧
    (colexMonomialOrder (N + 1)).leadingCoeff (cyclicTailWeight d b) = 1 := by
  let o := colexMonomialOrder (N + 1)
  have hnz : ∀ j ∈ Finset.univ.filter (fun j : Fin (N + 1) => b < j),
      (MvPolynomial.X j ^ d : MvPolynomial (Fin (N + 1)) ℚ) ≠ 0 := by
    intro j _
    exact pow_ne_zero d (MvPolynomial.X_ne_zero j)
  constructor
  · rw [cyclicTailWeight, o.degree_prod hnz]
    apply Finset.sum_congr rfl
    intro j _
    rw [MonomialOrder.degree_pow, MonomialOrder.degree_X, Finsupp.smul_single, smul_eq_mul, mul_one]
  · rw [cyclicTailWeight, leadingCoeff_prod o]
    apply Finset.prod_eq_one
    intro j _
    rw [MonomialOrder.leadingCoeff_pow, MonomialOrder.leadingCoeff_X, one_pow]

/-- The leading exponent vector of a nonzero summand `cyclicTailWeight d b * cyclicRootSample F b`. -/
noncomputable def cyclicTermExponent {N : ℕ} (d : ℕ)
    (F : Finset (Fin (N + 1))) (b : Fin (N + 1)) : Fin (N + 1) →₀ ℕ :=
  (∑ j ∈ Finset.univ.filter (fun j => b < j), Finsupp.single j d) +
    ∑ j ∈ F, Finsupp.single (max b j) 1

theorem cyclicTerm_degree_leading {N : ℕ} (d : ℕ)
    (F : Finset (Fin (N + 1))) (b : Fin (N + 1)) (hb : b ≠ 0) (hbF : b ∉ F) :
    (colexMonomialOrder (N + 1)).degree (cyclicTailWeight d b * cyclicRootSample F b) =
        cyclicTermExponent d F b ∧
    (colexMonomialOrder (N + 1)).leadingCoeff (cyclicTailWeight d b * cyclicRootSample F b) =
        (-1 : ℚ) ^ (F.filter (fun j => b < j)).card := by
  let o := colexMonomialOrder (N + 1)
  obtain ⟨hdegW, hlcW⟩ := cyclicTailWeight_degree_leading d b
  obtain ⟨hdegR, hlcR⟩ := cyclicRootSample_degree_leading F b hb hbF
  have hW0 : cyclicTailWeight d b ≠ 0 := by
    apply o.leadingCoeff_ne_zero_iff.mp
    rw [hlcW]
    exact one_ne_zero
  have hR0 : cyclicRootSample F b ≠ 0 := by
    apply o.leadingCoeff_ne_zero_iff.mp
    rw [hlcR]
    exact pow_ne_zero _ (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [o.degree_mul hW0 hR0, hdegW, hdegR, cyclicTermExponent]
  · rw [MonomialOrder.leadingCoeff_mul, hlcW, hlcR, one_mul]

theorem cyclicTermExponent_apply_of_lt {N : ℕ} (d : ℕ)
    (F : Finset (Fin (N + 1))) (b k : Fin (N + 1)) (hkb : k < b) :
    cyclicTermExponent d F b k = 0 := by
  simp only [cyclicTermExponent, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  have h1 : (∑ x ∈ Finset.univ.filter (fun j => b < j), if x = k then d else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exact if_neg (ne_of_gt (lt_trans hkb hx.2))
  have h2 : (∑ x ∈ F, if max b x = k then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact if_neg (ne_of_gt (lt_of_lt_of_le hkb (le_max_left b x)))
  rw [h1, h2]

theorem cyclicTermExponent_apply_self {N : ℕ} (d : ℕ)
    (F : Finset (Fin (N + 1))) (b : Fin (N + 1)) :
    cyclicTermExponent d F b b = (F.filter (fun j => j ≤ b)).card := by
  simp only [cyclicTermExponent, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  have h1 : (∑ x ∈ Finset.univ.filter (fun j => b < j), if x = b then d else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exact if_neg (ne_of_gt hx.2)
  have h2 : (∑ x ∈ F, if max b x = b then 1 else 0) = (F.filter (fun j => j ≤ b)).card := by
    have hcond : ∀ x : Fin (N + 1), (max b x = b) ↔ x ≤ b := fun x => max_eq_left_iff
    simp_rw [hcond, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  rw [h1, zero_add, h2]

theorem cyclicTermExponent_apply_of_gt {N : ℕ} (d : ℕ)
    (F : Finset (Fin (N + 1))) (b k : Fin (N + 1)) (hbk : b < k) :
    cyclicTermExponent d F b k = d + if k ∈ F then 1 else 0 := by
  simp only [cyclicTermExponent, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  have h1 : (∑ x ∈ Finset.univ.filter (fun j => b < j), if x = k then d else 0) = d := by
    rw [Finset.sum_eq_single k]
    · exact if_pos rfl
    · intro x _ hxk
      exact if_neg hxk
    · intro hk
      exact (hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hbk⟩)).elim
  have h2 : (∑ x ∈ F, if max b x = k then 1 else 0) = if k ∈ F then 1 else 0 := by
    have hmax (x : Fin (N + 1)) : (max b x = k) ↔ x = k := by
      constructor
      · intro h
        rcases max_choice b x with hbx | hbx <;> rw [hbx] at h
        · exact (ne_of_lt hbk h).elim
        · exact h
      · rintro rfl
        exact max_eq_right hbk.le
    simp_rw [hmax]
    by_cases hkF : k ∈ F
    · rw [if_pos hkF, Finset.sum_eq_single k]
      · exact if_pos rfl
      · intro x _ hxk
        exact if_neg hxk
      · intro h
        exact (h hkF).elim
    · rw [if_neg hkF]
      apply Finset.sum_eq_zero
      intro x hx
      exact if_neg (fun (h : x = k) => hkF (h ▸ hx))
  rw [h1, h2]

theorem cyclicTermExponent_lt_of_gt {N : ℕ} (d : ℕ)
    (F : Finset (Fin (N + 1))) (c b : Fin (N + 1))
    (hcb : c < b) (hbF : b ∉ F)
    (hcard : (F.filter (fun j => j ≤ b)).card < d) :
    cyclicTermExponent d F b ≺[colexMonomialOrder (N + 1)] cyclicTermExponent d F c := by
  rw [colexMonomialOrder_lt_iff]
  refine ⟨b, ?_, ?_⟩
  · rw [cyclicTermExponent_apply_self, cyclicTermExponent_apply_of_gt d F c b hcb,
      if_neg hbF, add_zero]
    exact hcard
  · intro k hbk
    rw [cyclicTermExponent_apply_of_gt d F b k hbk,
      cyclicTermExponent_apply_of_gt d F c k (lt_trans hcb hbk)]

theorem cyclicTermExponent_lt_of_facet_diff {N : ℕ} (d : ℕ)
    (F G : Finset (Fin (N + 1))) (cF cG ℓ : Fin (N + 1))
    (hℓF : ℓ ∈ F) (hℓG : ℓ ∉ G)
    (hagree : ∀ k, ℓ < k → (k ∈ F ↔ k ∈ G))
    (hcF : cF < ℓ) (hcG : cG ≤ ℓ)
    (hcardG : (G.filter (fun j => j ≤ cG)).card ≤ d) :
    cyclicTermExponent d G cG ≺[colexMonomialOrder (N + 1)] cyclicTermExponent d F cF := by
  rw [colexMonomialOrder_lt_iff]
  refine ⟨ℓ, ?_, ?_⟩
  · rw [cyclicTermExponent_apply_of_gt d F cF ℓ hcF, if_pos hℓF]
    rcases lt_or_eq_of_le hcG with hlt | rfl
    · rw [cyclicTermExponent_apply_of_gt d G cG ℓ hlt, if_neg hℓG]
      omega
    · rw [cyclicTermExponent_apply_self]
      omega
  · intro k hℓk
    rw [cyclicTermExponent_apply_of_gt d G cG k (lt_of_le_of_lt hcG hℓk),
      cyclicTermExponent_apply_of_gt d F cF k (lt_trans hcF hℓk)]
    by_cases hkF : k ∈ F
    · rw [if_pos hkF, if_pos ((hagree k hℓk).mp hkF)]
    · rw [if_neg hkF, if_neg (fun hkG => hkF ((hagree k hℓk).mpr hkG))]

/-- The weighted root-sample sum for a single facet has leading exponent `cyclicTermExponent d F c`
at its first omitted sample `c`, with leading coefficient `(-1)^(#{j ∈ F : c < j})`. -/
theorem cyclicFacetSum_degree_leading {N : ℕ} (d : ℕ)
    (B F : Finset (Fin (N + 1))) (c : Fin (N + 1))
    (hcB : c ∈ B) (hc0 : c ≠ 0) (hcF : c ∉ F)
    (hbefore : ∀ b ∈ B, b < c → b ∈ F)
    (hafter : ∀ b ∈ B, c < b → b ∉ F → (F.filter (fun j => j ≤ b)).card < d) :
    (colexMonomialOrder (N + 1)).degree
      (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample F b) = cyclicTermExponent d F c ∧
    (colexMonomialOrder (N + 1)).leadingCoeff
      (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample F b) =
        (-1 : ℚ) ^ (F.filter (fun j => c < j)).card := by
  let o := colexMonomialOrder (N + 1)
  obtain ⟨hdegC, hlcC⟩ := cyclicTerm_degree_leading d F c hc0 hcF
  have hfc0 : cyclicTailWeight d c * cyclicRootSample F c ≠ 0 := by
    apply o.leadingCoeff_ne_zero_iff.mp
    rw [hlcC]
    exact pow_ne_zero _ (by norm_num)
  have hdom : ∀ b ∈ B, b ≠ c →
      cyclicTailWeight d b * cyclicRootSample F b = 0 ∨
        o.degree (cyclicTailWeight d b * cyclicRootSample F b) ≺[o]
          o.degree (cyclicTailWeight d c * cyclicRootSample F c) := by
    intro b hbB hbc
    by_cases hbF : b ∈ F
    · left
      rw [cyclicRootSample_eq_zero_of_mem F b hbF, mul_zero]
    · right
      have hcb : c < b := by
        rcases lt_or_gt_of_ne hbc with hlt | hgt
        · exact (hbF (hbefore b hbB hlt)).elim
        · exact hgt
      have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le c) hcb)
      obtain ⟨hdegB, _⟩ := cyclicTerm_degree_leading d F b hb0 hbF
      rw [hdegB, hdegC]
      exact cyclicTermExponent_lt_of_gt d F c b hcb hbF (hafter b hbB hcb hbF)
  obtain ⟨hdegSum, hlcSum⟩ := degree_leadingCoeff_sum_of_dominant o B
    (fun b => cyclicTailWeight d b * cyclicRootSample F b) c hcB hfc0 hdom
  exact ⟨hdegSum.trans hdegC, hlcSum.trans hlcC⟩

/-- The full Billera–Lee comparison polynomial has degree `cyclicTermExponent d F cF` and
leading coefficient `1` whenever `cF` has an even number of roots of `F` above it and the
highest differing label `ℓ` lies in `F \ G` above `cF` and at least `cG`. -/
theorem cyclicComparisonPolynomial_degree_leading_eq_one {N : ℕ} (d : ℕ)
    (B F G : Finset (Fin (N + 1))) (cF cG ℓ : Fin (N + 1))
    (hcFB : cF ∈ B) (hcF0 : cF ≠ 0) (hcFF : cF ∉ F)
    (hbeforeF : ∀ b ∈ B, b < cF → b ∈ F)
    (hafterF : ∀ b ∈ B, cF < b → b ∉ F → (F.filter (fun j => j ≤ b)).card < d)
    (hevenF : Even (F.filter (fun j => cF < j)).card)
    (hcGB : cG ∈ B) (hcG0 : cG ≠ 0) (hcGG : cG ∉ G)
    (hbeforeG : ∀ b ∈ B, b < cG → b ∈ G)
    (hafterG : ∀ b ∈ B, cG < b → b ∉ G → (G.filter (fun j => j ≤ b)).card < d)
    (hℓF : ℓ ∈ F) (hℓG : ℓ ∉ G)
    (hagree : ∀ k, ℓ < k → (k ∈ F ↔ k ∈ G))
    (hcFℓ : cF < ℓ) (hcGℓ : cG ≤ ℓ)
    (hcardG : (G.filter (fun j => j ≤ cG)).card ≤ d) :
    (colexMonomialOrder (N + 1)).degree (cyclicComparisonPolynomial d B F G) =
        cyclicTermExponent d F cF ∧
    (colexMonomialOrder (N + 1)).leadingCoeff (cyclicComparisonPolynomial d B F G) = 1 := by
  let o := colexMonomialOrder (N + 1)
  obtain ⟨hdegF, hlcF⟩ := cyclicFacetSum_degree_leading d B F cF hcFB hcF0 hcFF hbeforeF hafterF
  obtain ⟨hdegG, _⟩ := cyclicFacetSum_degree_leading d B G cG hcGB hcG0 hcGG hbeforeG hafterG
  have hlt : o.degree (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample G b) ≺[o]
      o.degree (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample F b) := by
    rw [hdegG, hdegF]
    exact cyclicTermExponent_lt_of_facet_diff d F G cF cG ℓ hℓF hℓG hagree hcFℓ hcGℓ hcardG
  rw [cyclicComparisonPolynomial_eq_sub, sub_eq_add_neg]
  have hltNeg : o.degree (-(∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample G b)) ≺[o]
      o.degree (∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample F b) := by
    rwa [MonomialOrder.degree_neg]
  rw [o.degree_add_of_lt hltNeg, o.leadingCoeff_add_of_lt hltNeg, hdegF, hlcF,
    hevenF.neg_one_pow]
  exact ⟨rfl, rfl⟩

/-- Any polynomial whose `colexMonomialOrder` leading coefficient is positive satisfies the
exact hypothesis of `exists_increasing_pos_eval_of_colex_leading_pos`. -/
theorem exists_colex_leading_pos_of_leadingCoeff_pos {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ)
    (hp : 0 < (colexMonomialOrder n).leadingCoeff p) :
    ∃ a : Fin n →₀ ℕ, 0 < p.coeff a ∧
      ∀ b ∈ p.support, b ≠ a → ∃ i, b i < a i ∧ ∀ j, i < j → b j = a j := by
  let o := colexMonomialOrder n
  have hp0 : p ≠ 0 := o.leadingCoeff_ne_zero_iff.mp (ne_of_gt hp)
  refine ⟨o.degree p, hp, ?_⟩
  intro b hb hba
  rw [← colexMonomialOrder_lt_iff]
  exact lt_of_le_of_ne (o.le_degree hb) ( fun h => hba (o.toSyn.injective h) )

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextComparisonPolynomial.lean

-- BEGIN GSufficiencyNextMomentCurve.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- The standard real moment curve, with coordinates of degrees one through `d`. -/
def momentCurve (d : ℕ) (t : ℝ) : Fin d → ℝ := fun j => t ^ (j.val + 1)

/-- Any at most `d + 1` distinct parameters give affinely independent points
on the real moment curve. -/
theorem momentCurve_affineIndependent {d n : ℕ} (hn : n ≤ d + 1)
    (t : Fin n → ℝ) (ht : Function.Injective t) :
    AffineIndependent ℝ (fun i => momentCurve d (t i)) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hsum i
  have hlinear : ∑ j : Fin n, w j • momentCurve d (t j) = 0 := by
    rwa [Finset.univ.weightedVSub_eq_linear_combination hw] at hsum
  have hzero : w = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht (by
      intro j
      by_cases hj : j.val = 0
      · simpa only [hj, pow_zero, mul_one] using hw
      · let q : Fin d := ⟨j.val - 1, by omega⟩
        have hq : q.val + 1 = j.val := by dsimp [q]; omega
        have hh := congrFun hlinear q
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          momentCurve, hq] using hh)
  exact congrFun hzero i

/-- Every finite moment-curve configuration with at least `d + 1` distinct points
spans the whole ambient affine space. -/
theorem momentCurve_affineSpan_eq_top {d n : ℕ} (hn : d + 1 ≤ n)
    (t : Fin n → ℝ) (ht : Function.Injective t) :
    affineSpan ℝ (Set.range (fun i => momentCurve d (t i))) = ⊤ := by
  let e : Fin (d + 1) ↪ Fin n := Fin.castLEEmb hn
  have hu := momentCurve_affineIndependent (le_refl (d + 1)) (t ∘ e)
    (ht.comp e.injective)
  have hspan : affineSpan ℝ (Set.range (fun i => momentCurve d (t (e i)))) = ⊤ := by
    apply hu.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp
  apply top_unique
  rw [← hspan]
  apply affineSpan_mono ℝ
  rintro x ⟨i, rfl⟩
  exact Set.mem_range_self (e i)

/-- Finite convex hulls of sufficiently many distinct moment-curve points are
full-dimensional polytopes in the canonical carrier. -/
theorem momentCurve_isDPolytope {d n : ℕ} (hn : d + 1 ≤ n)
    (t : Fin n → ℝ) (ht : Function.Injective t) :
    IsDPolytope (convexHull ℝ (Set.range (fun i => momentCurve d (t i)))) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨⟨_, Set.finite_range _, Set.range_nonempty _, rfl⟩, ?_⟩
  rw [affineSpan_convexHull]
  exact momentCurve_affineSpan_eq_top hn t ht

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextMomentCurve.lean

-- BEGIN StellarFaceTools.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarFaceTools

/-- Any exposed face of a finite hull is the hull of its incident input points. -/
theorem finite_face_hull {d : ℕ} {ι : Type*} [Finite ι]
    (v : ι → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

/-- A linear support certificate realizes an exposed face and certifies its exact
input-label incidence set. -/
theorem finite_face_of_support {d : ℕ} {ι : Type*} [Finite ι]
    (v : ι → Fin d → ℝ) (s : Set (ι)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : ι, l (v i) ≤ b)
    (heq : ∀ i : ι, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : ι, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : ι, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          finite_face_hull v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

/-- A simplex with `d + 1` affinely independent vertices in `ℝ^d` has full affine span. -/
theorem simplex_affineSpan_eq_top (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) : affineSpan ℝ (Set.range v) = ⊤ := by
  apply hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp only [Fintype.card_fin, Module.finrank_fin_fun]

/-- The convex hull of `d + 1` affinely independent vertices in `ℝ^d` is a `d`-polytope. -/
theorem simplex_isDPolytope (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) : IsDPolytope (convexHull ℝ (Set.range v)) := by
  refine ⟨⟨Set.range v, Set.finite_range v, Set.range_nonempty v, rfl⟩, ?_⟩
  rw [affineSpan_convexHull]
  exact simplex_affineSpan_eq_top d v hv

/-- Every vertex-subset hull of a simplex is an exposed face and has
exactly the selected incident vertices. -/
theorem simplex_subset_hull_isExposed_and_labels (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (I : Finset (Fin (d + 1))) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (I : Set (Fin (d + 1))))) ∧
      ∀ j : Fin (d + 1), v j ∈ convexHull ℝ (v '' (I : Set (Fin (d + 1)))) ↔ j ∈ I := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp only [Finset.coe_empty, Set.image_empty, convexHull_empty, Set.mem_empty_iff_false,
      Finset.notMem_empty, implies_true, and_true]
    exact fun h => False.elim (Set.not_nonempty_empty h)
  let b : AffineBasis (Fin (d + 1)) ℝ (Fin d → ℝ) :=
    ⟨v, hv, simplex_affineSpan_eq_top d v hv⟩
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ I, (b.coord i).linear
  let c : ℝ := ∑ i ∈ I, b.coord i 0
  let l : StrongDual ℝ (Fin d → ℝ) := L.toContinuousLinearMap
  have hl : ∀ j : Fin (d + 1), l (v j) = (if j ∈ I then 1 else 0) - c := by
    intro j
    change L (v j) = _
    simp only [L, LinearMap.sum_apply]
    have hlin : ∀ i : Fin (d + 1), (b.coord i).linear (v j) =
        b.coord i (v j) - b.coord i 0 := by
      intro i
      exact congrFun (b.coord i).decomp' (v j)
    simp_rw [hlin]
    rw [Finset.sum_sub_distrib]
    change (∑ i ∈ I, b.coord i (b j)) - c = _
    simp only [AffineBasis.coord_apply, Finset.sum_ite_eq']
  apply finite_face_of_support v (I : Set (Fin (d + 1)))
    (Finset.coe_nonempty.mpr hI) l (1 - c)
  · intro j
    rw [hl j]
    by_cases hj : j ∈ I
    · simp only [hj, if_true, le_refl]
    · simp only [hj, if_false]
      exact sub_le_sub_right zero_le_one c
  · intro j
    rw [hl j]
    by_cases hj : j ∈ I
    · simp only [hj, if_true, SetLike.mem_coe]
    · simp only [hj, if_false, Finset.mem_coe, iff_false]
      exact fun h => zero_ne_one (sub_left_injective h)

theorem isExposed_trans_polytope (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (F G : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) (hG : IsExposed ℝ F G) :
    IsExposed ℝ P G := by
  classical
  by_cases hEmpty : G = ∅
  · rw [hEmpty]
    exact isExposed_empty
  obtain ⟨z, hzG⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hzF : z ∈ F := hG.subset hzG
  have hzP : z ∈ P := hF.subset hzF
  obtain ⟨l, hFl⟩ := hF ⟨z, hzF⟩
  obtain ⟨m, hGm⟩ := hG ⟨z, hzG⟩
  have hlMax : ∀ x ∈ P, l x ≤ l z := by
    have hz := hzF
    rw [hFl] at hz
    exact hz.2
  have hmMax : ∀ x ∈ F, m x ≤ m z := by
    have hz := hzG
    rw [hGm] at hz
    exact hz.2
  have hFlevel (x : Fin d → ℝ) (hxP : x ∈ P) : x ∈ F ↔ l x = l z := by
    constructor
    · intro hxF
      rw [hFl] at hxF
      exact le_antisymm (hlMax x hxP) (hxF.2 z hzP)
    · intro hxEq
      rw [hFl]
      exact ⟨hxP, fun y hy => by rw [hxEq]; exact hlMax y hy⟩
  have hGlevel (x : Fin d → ℝ) (hxF : x ∈ F) : x ∈ G ↔ m x = m z := by
    constructor
    · intro hxG
      rw [hGm] at hxG
      exact le_antisymm (hmMax x hxF) (hxG.2 z hzF)
    · intro hxEq
      rw [hGm]
      exact ⟨hxF, fun y hy => by rw [hxEq]; exact hmMax y hy⟩
  obtain ⟨V, hVfin, _, hPgen⟩ := hP.1
  have hVP : V ⊆ P := by
    rw [hPgen]
    exact subset_convexHull ℝ V
  have hFaces (K : Set (Fin d → ℝ)) (hK : IsExposed ℝ P K) :
      K = convexHull ℝ (K ∩ V) := by
    have : Finite V := hVfin.to_subtype
    have hr : Set.range (fun i : V => i.val) = V := Subtype.range_coe
    rw [hPgen, ← hr] at hK
    simpa only [hr] using finite_face_hull (fun i : V => i.val) hK
  have hPconv : Convex ℝ P := hPgen ▸ convex_convexHull ℝ V
  let r : (Fin d → ℝ) → ℝ := fun w => (m w - m z) / (l z - l w)
  obtain ⟨M, hM⟩ := ((hVfin.image r).insert 0).bddAbove
  let C : ℝ := M + 1
  let n : StrongDual ℝ (Fin d → ℝ) := C • l + m
  have hStrict (w : Fin d → ℝ) (hwV : w ∈ V) (hwF : w ∉ F) : n w < n z := by
    have hwP : w ∈ P := hVP hwV
    have hlw : l w < l z := lt_of_le_of_ne (hlMax w hwP) (fun h => hwF ((hFlevel w hwP).mpr h))
    have hDen : 0 < l z - l w := sub_pos.mpr hlw
    have hRatio : r w < C := lt_of_le_of_lt (hM (Set.mem_insert_of_mem 0 ⟨w, hwV, rfl⟩)) (by dsimp [C]; linarith)
    have hNum : m w - m z < C * (l z - l w) := (div_lt_iff₀ hDen).mp hRatio
    change C * l w + m w < C * l z + m z
    nlinarith [hNum]
  have hGen (w : Fin d → ℝ) (hwV : w ∈ V) : n w ≤ n z := by
    by_cases hwF : w ∈ F
    · change C * l w + m w ≤ C * l z + m z
      rw [(hFlevel w (hVP hwV)).mp hwF]
      exact add_le_add le_rfl (hmMax w hwF)
    · exact (hStrict w hwV hwF).le
  have hnMax : ∀ x ∈ P, n x ≤ n z := by
    rw [hPgen]
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n z
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n z + b * n z :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n z := by rw [← add_mul, hab, one_mul]
  let K := {x ∈ P | n x = n z}
  have hK : IsExposed ℝ P K := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      exact ⟨hxP, fun y hy => (hnMax y hy).trans_eq hxEq.symm⟩
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hnMax x hxP) (hxMax z hzP)⟩
  have hKsubG : K ⊆ G := by
    have hHullK := hFaces K hK
    change K = convexHull ℝ (K ∩ V) at hHullK
    rw [hHullK]
    apply convexHull_min ?_ (hG.convex (hF.convex hPconv))
    rintro w ⟨hwK, hwV⟩
    have hwF : w ∈ F := by
      by_contra hnF
      exact (hStrict w hwV hnF).ne hwK.2
    apply (hGlevel w hwF).mpr
    have hEq : C * l w + m w = C * l z + m z := hwK.2
    rw [(hFlevel w hwK.1).mp hwF] at hEq
    linarith
  have hGsubK : G ⊆ K := by
    intro x hxG
    have hxF : x ∈ F := hG.subset hxG
    have hxP : x ∈ P := hF.subset hxF
    refine ⟨hxP, ?_⟩
    change C * l x + m x = C * l z + m z
    rw [(hFlevel x hxP).mp hxF, (hGlevel x hxF).mp hxG]
  have hKG : K = G := Set.Subset.antisymm hKsubG hGsubK
  rwa [hKG] at hK


end Grunbaum2003.StellarFaceTools
-- END StellarFaceTools.lean

-- BEGIN GSufficiencyNextSupportPolynomial.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- Every polynomial of degree at most the ambient dimension is an affine
functional on the moment curve; this is its linear part with reversed sign. -/
theorem exists_momentCurve_polynomial_support {d : ℕ} (p : Polynomial ℝ)
    (hp : p.natDegree ≤ d) :
    ∃ l : (Fin d → ℝ) →L[ℝ] ℝ, ∀ x : ℝ,
      l (momentCurve d x) = p.coeff 0 - p.eval x := by
  let l : (Fin d → ℝ) →L[ℝ] ℝ :=
    -(∑ j : Fin d, p.coeff (j.val + 1) • ContinuousLinearMap.proj j)
  refine ⟨l, ?_⟩
  intro x
  have heval := Polynomial.eval_eq_sum_range' (p := p) (n := d + 1) (by omega) x
  rw [Finset.sum_range_succ'] at heval
  simp only [pow_zero, mul_one] at heval
  have hl : l (momentCurve d x) =
      -(∑ j ∈ Finset.range d, p.coeff (j + 1) * x ^ (j + 1)) := by
    simp only [l, neg_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
      momentCurve, smul_eq_mul, neg_inj]
    exact Fin.sum_univ_eq_sum_range (fun j => p.coeff (j + 1) * x ^ (j + 1)) d
  rw [hl]
  linarith

/-- Polynomial support certificates determine exposed faces of any finite
moment-curve configuration, including their exact input-label incidences. -/
theorem momentCurve_face_of_polynomial {d n : ℕ} (t : Fin n → ℝ)
    (s : Set (Fin n)) (hs : s.Nonempty) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ d) (hnonneg : ∀ i, 0 ≤ p.eval (t i))
    (hzero : ∀ i, p.eval (t i) = 0 ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve d (t i))))
      (convexHull ℝ ((fun i => momentCurve d (t i)) '' s)) ∧
      ∀ i, momentCurve d (t i) ∈
        convexHull ℝ ((fun i => momentCurve d (t i)) '' s) ↔ i ∈ s := by
  obtain ⟨l, hl⟩ := exists_momentCurve_polynomial_support p hp
  apply StellarFaceTools.finite_face_of_support _ s hs l (p.coeff 0)
  · intro i
    rw [hl]
    linarith [hnonneg i]
  · intro i
    rw [hl]
    constructor
    · intro h
      apply (hzero i).mp
      linarith
    · intro h
      rw [(hzero i).mpr h, sub_zero]


/-- The product of adjacent-root pairs has a constant sign on an ordered
sample of the moment curve. Its zeros give an exposed face. This is the
polynomial certificate underlying the paired facets in the cyclic-polytope
construction. Pair repetitions are harmless for this support assertion. -/
theorem momentCurve_adjacent_pairs_exposed {d n m : ℕ} (hm : 0 < m)
    (hd : 2 * m ≤ d) (t : Fin n → ℝ) (ht : StrictMono t)
    (a b : Fin m → Fin n) (hab : ∀ r, (b r).val = (a r).val + 1) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve d (t i))))
      (convexHull ℝ ((fun i => momentCurve d (t i)) ''
        (Set.range a ∪ Set.range b))) ∧
    ∀ i, momentCurve d (t i) ∈
      convexHull ℝ ((fun i => momentCurve d (t i)) ''
        (Set.range a ∪ Set.range b)) ↔ i ∈ Set.range a ∪ Set.range b := by
  classical
  let p : Polynomial ℝ := ∏ r : Fin m,
    (Polynomial.X - Polynomial.C (t (a r))) * (Polynomial.X - Polynomial.C (t (b r)))
  have hs : (Set.range a ∪ Set.range b).Nonempty := by
    let r : Fin m := ⟨0, hm⟩
    exact ⟨a r, Or.inl (Set.mem_range_self r)⟩
  have hdeg : p.natDegree ≤ d := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc (∑ r : Fin m,
        ((Polynomial.X - Polynomial.C (t (a r))) *
          (Polynomial.X - Polynomial.C (t (b r)))).natDegree) ≤
        ∑ _r : Fin m, 2 := by
          apply Finset.sum_le_sum
          intro r _
          exact (Polynomial.natDegree_mul_le).trans
            (by simp only [Polynomial.natDegree_X_sub_C]; omega)
      _ = 2 * m := by simp [Nat.mul_comm]
      _ ≤ d := hd
  apply momentCurve_face_of_polynomial t _ hs p hdeg
  · intro i
    simp only [p, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_nonneg
    intro r _
    by_cases hia : i.val ≤ (a r).val
    · have hia' : t i ≤ t (a r) := ht.monotone hia
      have hib : t i ≤ t (b r) := ht.monotone (by change i.val ≤ (b r).val; rw [hab r]; omega)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hia') (sub_nonpos.mpr hib)
    · have hai : t (a r) ≤ t i := ht.monotone (by change (a r).val ≤ i.val; omega)
      have hbi : t (b r) ≤ t i := ht.monotone (by change (b r).val ≤ i.val; rw [hab r]; omega)
      exact mul_nonneg (sub_nonneg.mpr hai) (sub_nonneg.mpr hbi)
  · intro i
    simp only [p, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, mul_eq_zero, sub_eq_zero,
      Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨r, hr | hr⟩
      · exact Or.inl ⟨r, (ht.injective hr).symm⟩
      · exact Or.inr ⟨r, (ht.injective hr).symm⟩
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
      · exact ⟨r, Or.inl rfl⟩
      · exact ⟨r, Or.inr rfl⟩

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextSupportPolynomial.lean

-- BEGIN GSufficiencyNextCyclic.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- No codimension-one affine set contains more than `d` points of a moment curve
whose parameters are distinct. -/
theorem momentCurve_facet_indices_card_le {d n : ℕ} (t : Fin n → ℝ)
    (ht : Function.Injective t) (F : Set (Fin d → ℝ))
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d) :
    (Finset.univ.filter (fun i => momentCurve d (t i) ∈ F)).card ≤ d := by
  classical
  let S := Finset.univ.filter (fun i => momentCurve d (t i) ∈ F)
  change S.card ≤ d
  by_contra hn
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ S.card by omega)
  let e : Fin (d + 1) ≃ ↥T := Fintype.equivOfCardEq (by simp [hTcard])
  have hi : Function.Injective (fun i : Fin (d + 1) => t (e i).val) :=
    ht.comp (Subtype.val_injective.comp e.injective)
  have hu := momentCurve_affineIndependent (le_refl (d + 1)) _ hi
  have hspan : affineSpan ℝ
      (Set.range (fun i : Fin (d + 1) => momentCurve d (t (e i).val))) = ⊤ := by
    apply hu.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simp
  have htop : (⊤ : AffineSubspace ℝ (Fin d → ℝ)) ≤ affineSpan ℝ F := by
    rw [← hspan]
    apply affineSpan_mono ℝ
    rintro x ⟨i, rfl⟩
    exact (Finset.mem_filter.mp (hTS (e i).property)).2
  have hFtop := top_unique htop
  rw [hFtop, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hFdim
  omega

/-- Finite convex hulls of distinct real moment-curve points are simplicial
full-dimensional polytopes as soon as at least `d + 1` points are supplied. -/
theorem momentCurve_isSimplicialDPolytope {d n : ℕ} (hn : d + 1 ≤ n)
    (t : Fin n → ℝ) (ht : Function.Injective t) :
    IsSimplicialDPolytope (convexHull ℝ (Set.range (fun i => momentCurve d (t i)))) := by
  classical
  refine ⟨momentCurve_isDPolytope hn t ht, ?_⟩
  intro F hFne hF hFdim
  let S := Finset.univ.filter (fun i => momentCurve d (t i) ∈ F)
  have hSdata (i : Fin n) : i ∈ S ↔ momentCurve d (t i) ∈ F := by simp [S]
  have hSle : S.card ≤ d := momentCurve_facet_indices_card_le t ht F hFdim
  have hset : F ∩ Set.range (fun i => momentCurve d (t i)) =
      (fun i => momentCurve d (t i)) '' (S : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hSdata i).mpr hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hSdata i).mp hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ ((fun i => momentCurve d (t i)) '' (S : Set (Fin n))) := by
    rw [← hset]
    exact StellarFaceTools.finite_face_hull (fun i => momentCurve d (t i)) hF
  have hSne : S.Nonempty := by
    by_contra hnone
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hFempty : F = ∅ := by simpa [he] using hFhull
    exact hFne.ne_empty hFempty
  have : Nonempty (Fin S.card) := ⟨⟨0, Finset.card_pos.mpr hSne⟩⟩
  let e : Fin S.card ≃ ↥S := Fintype.equivOfCardEq (by simp)
  let u : Fin S.card → Fin d → ℝ := fun i => momentCurve d (t (e i).val)
  have hu : AffineIndependent ℝ u :=
    momentCurve_affineIndependent (by omega) (fun i => t (e i).val)
      (ht.comp (Subtype.val_injective.comp e.injective))
  have hrange : Set.range u =
      (fun i => momentCurve d (t i)) '' (S : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).val, (e i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      exact ⟨j, by simp [u, hj]⟩
  have hcard : d = S.card := by
    have hrank : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = S.card := by
      rw [hFhull, ← hrange, affineSpan_convexHull, direction_affineSpan]
      simpa only [Fintype.card_fin] using hu.finrank_vectorSpan_add_one
    omega
  let e' : Fin d ≃ Fin S.card := finCongr hcard
  refine ⟨u ∘ e', hu.comp_embedding e'.toEmbedding, ?_⟩
  rw [e'.surjective.range_comp u, hrange]
  exact hFhull

/-- For dimensions at least two, each sampled moment-curve point is an exposed
vertex of its finite convex hull, witnessed by a quadratic support polynomial. -/
theorem momentCurve_vertex_isExposed {d n : ℕ} (hd : 2 ≤ d)
    (t : Fin n → ℝ) (ht : Function.Injective t) (i : Fin n) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun j => momentCurve d (t j))))
      {momentCurve d (t i)} := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  let l : (Fin d → ℝ) →L[ℝ] ℝ :=
    (2 * t i) • ContinuousLinearMap.proj z - ContinuousLinearMap.proj o
  have hl (j : Fin n) : l (momentCurve d (t j)) = 2 * t i * t j - (t j)^2 := by
    simp [l, momentCurve, z, o]
  have hbound (j : Fin n) : l (momentCurve d (t j)) ≤ (t i)^2 := by
    rw [hl]
    nlinarith [sq_nonneg (t j - t i)]
  have heq (j : Fin n) : l (momentCurve d (t j)) = (t i)^2 ↔ j ∈ ({i} : Set (Fin n)) := by
    rw [hl, Set.mem_singleton_iff]
    constructor
    · intro h
      apply ht
      have hs : (t j - t i)^2 = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · rintro rfl
      ring
  have hf := (StellarFaceTools.finite_face_of_support (fun j => momentCurve d (t j))
    {i} (Set.singleton_nonempty i) l ((t i)^2) hbound heq).1
  simpa using hf

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextCyclic.lean

-- BEGIN GSufficiencyNextEndpoint.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- Adding the first sample to adjacent pairs supplies the odd-degree support
polynomial needed for the lower facets of an odd-dimensional cyclic polytope. -/
theorem momentCurve_first_and_adjacent_pairs_exposed {d n m : ℕ}
    (hd : 1 + 2 * m ≤ d) (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (a b : Fin m → Fin (n + 1)) (hab : ∀ r, (b r).val = (a r).val + 1) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve d (t i))))
      (convexHull ℝ ((fun i => momentCurve d (t i)) ''
        ({0} ∪ (Set.range a ∪ Set.range b)))) ∧
    ∀ i, momentCurve d (t i) ∈
      convexHull ℝ ((fun i => momentCurve d (t i)) ''
        ({0} ∪ (Set.range a ∪ Set.range b))) ↔
      i ∈ ({0} ∪ (Set.range a ∪ Set.range b)) := by
  classical
  let q : Polynomial ℝ := ∏ r : Fin m,
    (Polynomial.X - Polynomial.C (t (a r))) *
      (Polynomial.X - Polynomial.C (t (b r)))
  let p : Polynomial ℝ := (Polynomial.X - Polynomial.C (t 0)) * q
  have hqdeg : q.natDegree ≤ 2 * m := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc (∑ r : Fin m,
        ((Polynomial.X - Polynomial.C (t (a r))) *
          (Polynomial.X - Polynomial.C (t (b r)))).natDegree) ≤
        ∑ _r : Fin m, 2 := by
          apply Finset.sum_le_sum
          intro r _
          exact (Polynomial.natDegree_mul_le).trans
            (by simp only [Polynomial.natDegree_X_sub_C]; omega)
      _ = 2 * m := by simp [Nat.mul_comm]
  have hpdeg : p.natDegree ≤ d := by
    apply (Polynomial.natDegree_mul_le).trans
    simp only [Polynomial.natDegree_X_sub_C]
    omega
  apply momentCurve_face_of_polynomial t _ ⟨0, Or.inl (Set.mem_singleton 0)⟩ p hpdeg
  · intro i
    simp only [p, q, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply mul_nonneg (sub_nonneg.mpr (ht.monotone (Fin.zero_le i)))
    apply Finset.prod_nonneg
    intro r _
    by_cases hia : i.val ≤ (a r).val
    · have hia' : t i ≤ t (a r) := ht.monotone hia
      have hib : t i ≤ t (b r) :=
        ht.monotone (by change i.val ≤ (b r).val; rw [hab r]; omega)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hia') (sub_nonpos.mpr hib)
    · have hai : t (a r) ≤ t i := ht.monotone (by change (a r).val ≤ i.val; omega)
      have hbi : t (b r) ≤ t i :=
        ht.monotone (by change (b r).val ≤ i.val; rw [hab r]; omega)
      exact mul_nonneg (sub_nonneg.mpr hai) (sub_nonneg.mpr hbi)
  · intro i
    simp only [p, q, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (hi | ⟨r, hr | hr⟩)
      · exact Or.inl (ht.injective hi)
      · exact Or.inr (Or.inl ⟨r, (ht.injective hr).symm⟩)
      · exact Or.inr (Or.inr ⟨r, (ht.injective hr).symm⟩)
    · rintro (rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨r, Or.inl rfl⟩
      · exact Or.inr ⟨r, Or.inr rfl⟩

/-- A nonempty subset of at most `d + 1` distinct samples has affine dimension
one less than its cardinality. Together with polynomial support certificates,
this turns a `d`-element supported label set into an actual exposed facet. -/
theorem momentCurve_subset_finrank {d n : ℕ} (t : Fin n → ℝ)
    (ht : Function.Injective t) (S : Finset (Fin n)) (hSne : S.Nonempty)
    (hSle : S.card ≤ d + 1) :
    Module.finrank ℝ
      (affineSpan ℝ (convexHull ℝ
        ((fun i => momentCurve d (t i)) '' (S : Set (Fin n))))).direction + 1 =
      S.card := by
  classical
  have : Nonempty (Fin S.card) := ⟨⟨0, Finset.card_pos.mpr hSne⟩⟩
  let e : Fin S.card ≃ ↥S := Fintype.equivOfCardEq (by simp)
  let u : Fin S.card → Fin d → ℝ := fun i => momentCurve d (t (e i).val)
  have hu : AffineIndependent ℝ u :=
    momentCurve_affineIndependent hSle (fun i => t (e i).val)
      (ht.comp (Subtype.val_injective.comp e.injective))
  have hrange : Set.range u =
      (fun i => momentCurve d (t i)) '' (S : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).val, (e i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      exact ⟨j, by simp [u, hj]⟩
  rw [← hrange, affineSpan_convexHull, direction_affineSpan]
  simpa only [Fintype.card_fin] using hu.finrank_vectorSpan_add_one

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextEndpoint.lean

-- BEGIN GSufficiencyNextPairs.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- Offsetting a weakly increasing word by twice its position produces
disjoint adjacent pairs. Zero letters represent the padding of a monomial
of degree less than the word length. -/
theorem paired_offset_injective {m s : ℕ} (u : Fin m → Fin (s + 1))
    (hu : Monotone u) :
    Function.Injective (fun p : Fin m × Fin 2 => (u p.1).val + 2 * p.1.val + p.2.val) := by
  rintro ⟨r, e⟩ ⟨r', e'⟩ h
  have hrr' : r = r' := by
    apply le_antisymm
    · by_contra hn
      have hr'r : r' < r := lt_of_not_ge hn
      have hum := hu hr'r.le
      have he := e.isLt
      have he' := e'.isLt
      change (u r').val ≤ (u r).val at hum
      change (u r).val + 2 * r.val + e.val = (u r').val + 2 * r'.val + e'.val at h
      omega
    · by_contra hn
      have hrr' : r < r' := lt_of_not_ge hn
      have hum := hu hrr'.le
      have he := e.isLt
      have he' := e'.isLt
      change (u r).val ≤ (u r').val at hum
      change (u r).val + 2 * r.val + e.val = (u r').val + 2 * r'.val + e'.val at h
      omega
  subst r'
  have hee' : e = e' := by
    apply Fin.ext
    change (u r).val + 2 * r.val + e.val = (u r).val + 2 * r.val + e'.val at h
    omega
  subst e'
  rfl

/-- A padded sorted monomial word determines exactly `m` disjoint adjacent
pairs in the ordered set of `s + 2*m` labels. -/
theorem exists_adjacent_pairs_of_monotone {m s : ℕ} (u : Fin m → Fin (s + 1))
    (hu : Monotone u) :
    ∃ a b : Fin m → Fin (s + 2 * m),
      (∀ r, (a r).val = (u r).val + 2 * r.val) ∧
      (∀ r, (b r).val = (a r).val + 1) ∧
      (∀ r r', r < r' → b r < a r') ∧
      (Finset.univ.image a ∪ Finset.univ.image b).card = 2 * m := by
  classical
  let a : Fin m → Fin (s + 2 * m) := fun r =>
    ⟨(u r).val + 2 * r.val, by have := (u r).isLt; have := r.isLt; omega⟩
  let b : Fin m → Fin (s + 2 * m) := fun r =>
    ⟨(u r).val + 2 * r.val + 1, by have := (u r).isLt; have := r.isLt; omega⟩
  have hsep (r r' : Fin m) (hrr' : r < r') : b r < a r' := by
    have hum := hu hrr'.le
    change (u r).val ≤ (u r').val at hum
    change (u r).val + 2 * r.val + 1 < (u r').val + 2 * r'.val
    omega
  let f : Fin m × Fin 2 → Fin (s + 2 * m) := fun p =>
    ⟨(u p.1).val + 2 * p.1.val + p.2.val,
      by have := (u p.1).isLt; have := p.1.isLt; have := p.2.isLt; omega⟩
  have hfi : Function.Injective f := by
    intro p q hpq
    apply paired_offset_injective u hu
    exact congrArg Fin.val hpq
  have himage : Finset.univ.image f = Finset.univ.image a ∪ Finset.univ.image b := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨⟨r, e⟩, rfl⟩
      have he := e.isLt
      by_cases he0 : e.val = 0
      · exact Or.inl ⟨r, Fin.ext (by simp [a, f, he0])⟩
      · have he1 : e.val = 1 := by omega
        exact Or.inr ⟨r, Fin.ext (by simp [b, f, he1])⟩
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
      · exact ⟨(r, 0), Fin.ext (by simp [f, a])⟩
      · exact ⟨(r, 1), Fin.ext (by simp [f, b])⟩
  refine ⟨a, b, fun _ => rfl, fun _ => rfl, hsep, ?_⟩
  rw [← himage, Finset.card_image_of_injective _ hfi]
  simp [Nat.mul_comm]

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextPairs.lean

-- BEGIN GSufficiencyNextMonomialWord.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- Every monomial of degree at most `m` has a sorted word of length `m`:
positive letters record its exponents, and zeros pad the remaining positions.
This is the input to the adjacent-pair encoding. -/
theorem exists_monotone_word_of_degree_le {m s : ℕ} (f : Fin s →₀ ℕ)
    (hf : f.sum (fun _ n => n) ≤ m) :
    ∃ u : Fin m → Fin (s + 1), Monotone u ∧
      (∀ i : Fin s, ((List.ofFn u : List (Fin (s + 1))) : Multiset (Fin (s + 1))).count
        i.succ = f i) ∧
      ((List.ofFn u : List (Fin (s + 1))) : Multiset (Fin (s + 1))).count 0 =
        m - f.sum (fun _ n => n) := by
  classical
  let M : Multiset (Fin (s + 1)) :=
    Multiset.replicate (m - f.sum (fun _ n => n)) 0 + f.toMultiset.map Fin.succ
  have hcard : M.card = m := by
    simp only [M, Multiset.card_add, Multiset.card_replicate, Multiset.card_map,
      Finsupp.card_toMultiset]
    change (m - f.sum (fun _ n => n)) + f.sum (fun _ n => n) = m
    exact Nat.sub_add_cancel hf
  let l : List (Fin (s + 1)) := M.sort (· ≤ ·)
  have hlen : l.length = m := by simpa only [l, Multiset.length_sort] using hcard
  let u : Fin m → Fin (s + 1) := fun i => l.get (Fin.cast hlen.symm i)
  have hmono : Monotone u := by
    intro i j hij
    exact (Multiset.pairwise_sort M (· ≤ ·)).sortedLE.monotone_get hij
  have hof : List.ofFn u = l := by
    exact (List.ofFn_congr hlen l.get).symm.trans (List.ofFn_get l)
  have hM : ((List.ofFn u : List (Fin (s + 1))) : Multiset (Fin (s + 1))) = M := by
    rw [hof]
    exact Multiset.sort_eq M (· ≤ ·)
  refine ⟨u, hmono, ?_, ?_⟩
  · intro i
    have hi0 : (0 : Fin (s + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    rw [hM]
    simp only [M, Multiset.count_add, Multiset.count_replicate,
      hi0, if_false, zero_add]
    rw [Multiset.count_map_eq_count' Fin.succ _ (Fin.succ_injective s),
      Finsupp.count_toMultiset]
  · rw [hM, Multiset.count_add]
    have hzero : (f.toMultiset.map Fin.succ).count 0 = 0 := by
      apply Multiset.count_eq_zero.mpr
      simp only [Multiset.mem_map]
      rintro ⟨i, _, hi⟩
      exact Fin.succ_ne_zero i hi
    simp only [hzero, add_zero, Multiset.count_replicate, if_true]

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextMonomialWord.lean

-- BEGIN GSufficiencyNextShelling.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- The paired labels of a padded monomial word, before adding the common prefix. -/
def pairedFacet {m : ℕ} (u : Fin m → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun r => {u r + 2 * r.val, u r + 2 * r.val + 1})

/-- The right endpoints belonging to positive letters of the padded word. -/
def pairedRestriction {m : ℕ} (u : Fin m → ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun r => 0 < u r)).image (fun r => u r + 2 * r.val + 1)

/-- Compare padded words at their largest differing position. -/
def wordColexLt {m : ℕ} (v u : Fin m → ℕ) : Prop :=
  ∃ r, v r < u r ∧ ∀ j, r < j → v j = u j

/-- Lower the constant positive-letter block ending at position `r`. -/
def lowerBlock {m : ℕ} (u : Fin m → ℕ) (r : Fin m) : Fin m → ℕ :=
  fun j => if j ≤ r ∧ u j = u r then u j - 1 else u j

theorem mem_pairedFacet {m : ℕ} (u : Fin m → ℕ) (x : ℕ) :
    x ∈ pairedFacet u ↔ ∃ r, x = u r + 2 * r.val ∨ x = u r + 2 * r.val + 1 := by
  simp only [pairedFacet, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]

theorem mem_pairedRestriction {m : ℕ} (u : Fin m → ℕ) (x : ℕ) :
    x ∈ pairedRestriction u ↔ ∃ r, 0 < u r ∧ u r + 2 * r.val + 1 = x := by
  simp only [pairedRestriction, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem pairedRestriction_subset {m : ℕ} (u : Fin m → ℕ) :
    pairedRestriction u ⊆ pairedFacet u := by
  intro x hx
  obtain ⟨r, _, rfl⟩ := (mem_pairedRestriction u x).mp hx
  exact (mem_pairedFacet u _).mpr ⟨r, Or.inr rfl⟩

theorem pairedRestriction_card {m : ℕ} (u : Fin m → ℕ) (hu : Monotone u) :
    (pairedRestriction u).card = (Finset.univ.filter (fun r => 0 < u r)).card := by
  have hmono : StrictMono (fun r : Fin m => u r + 2 * r.val + 1) := by
    intro i j hij
    have hum := hu hij.le
    have hij' : i.val < j.val := hij
    change u i + 2 * i.val + 1 < u j + 2 * j.val + 1
    omega
  exact Finset.card_image_of_injective _ hmono.injective

/-- The right endpoint at the last differing position is absent from every
earlier paired facet. -/
theorem rightEndpoint_not_mem_of_wordColexLt {m : ℕ} (u v : Fin m → ℕ)
    (hu : Monotone u) (hv : Monotone v) (r : Fin m)
    (hr : v r < u r) (heq : ∀ j, r < j → v j = u j) :
    u r + 2 * r.val + 1 ∉ pairedFacet v := by
  rw [mem_pairedFacet]
  rintro ⟨j, hj | hj⟩
  · by_cases hjr : j ≤ r
    · have hvj := hv hjr
      have hjr' : j.val ≤ r.val := hjr
      omega
    · have hrj : r < j := lt_of_not_ge hjr
      have huj := hu hrj.le
      have hrj' : r.val < j.val := hrj
      rw [heq j hrj] at hj
      omega
  · by_cases hjr : j ≤ r
    · have hvj := hv hjr
      have hjr' : j.val ≤ r.val := hjr
      omega
    · have hrj : r < j := lt_of_not_ge hjr
      have huj := hu hrj.le
      have hrj' : r.val < j.val := hrj
      rw [heq j hrj] at hj
      omega

theorem lowerBlock_wordColexLt {m : ℕ} (u : Fin m → ℕ) (r : Fin m)
    (hr : 0 < u r) : wordColexLt (lowerBlock u r) u := by
  refine ⟨r, ?_, ?_⟩
  · simp only [lowerBlock, le_refl, and_self, if_true]
    omega
  · intro j hj
    simp only [lowerBlock, not_le.mpr hj, false_and, if_false]

/-- Lowering the block shifts one consecutive run of pairs one label to the
left. It preserves every old label except the chosen right endpoint. -/
theorem pairedFacet_erase_subset_lowerBlock {m : ℕ} (u : Fin m → ℕ)
    (hu : Monotone u) (r : Fin m) (hr : 0 < u r) :
    (pairedFacet u).erase (u r + 2 * r.val + 1) ⊆ pairedFacet (lowerBlock u r) := by
  intro x hx
  obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
  obtain ⟨i, hi | hi⟩ := (mem_pairedFacet u x).mp hx
  · by_cases hblock : i ≤ r ∧ u i = u r
    · apply (mem_pairedFacet (lowerBlock u r) x).mpr
      refine ⟨i, Or.inr ?_⟩
      simp only [lowerBlock, if_pos hblock]
      omega
    · apply (mem_pairedFacet (lowerBlock u r) x).mpr
      exact ⟨i, Or.inl (by simpa only [lowerBlock, hblock, if_false] using hi)⟩
  · by_cases hblock : i ≤ r ∧ u i = u r
    · have hir : i < r := by
        have hir' : i ≠ r := by intro he; subst i; exact hne hi
        exact lt_of_le_of_ne hblock.1 hir'
      let j : Fin m := ⟨i.val + 1, by have := r.isLt; have : i.val < r.val := hir; omega⟩
      have hij : i ≤ j := by change i.val ≤ i.val + 1; omega
      have hjr : j ≤ r := by change i.val + 1 ≤ r.val; exact hir
      have hjval : u j = u r := by
        have h1 := hu hij
        have h2 := hu hjr
        omega
      apply (mem_pairedFacet (lowerBlock u r) x).mpr
      refine ⟨j, Or.inl ?_⟩
      simp only [lowerBlock, hjr, hjval, and_self, if_true]
      change x = u r - 1 + 2 * (i.val + 1)
      omega
    · apply (mem_pairedFacet (lowerBlock u r) x).mpr
      exact ⟨i, Or.inr (by simpa only [lowerBlock, hblock, if_false] using hi)⟩

/-- The interval description of the new faces in the paired-facet order.
The closure assumption is a concrete operation on words; it is discharged
from divisibility and degreewise compression of the monomial family. -/
theorem pairedFacet_new_face_iff {m : ℕ} (W : Finset (Fin m → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (u : Fin m → ℕ) (hu : u ∈ W) (S : Finset ℕ) (hS : S ⊆ pairedFacet u) :
    (¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ pairedFacet v) ↔ pairedRestriction u ⊆ S := by
  constructor
  · intro hnew x hx
    by_contra hxS
    obtain ⟨r, hr, rfl⟩ := (mem_pairedRestriction u x).mp hx
    apply hnew
    refine ⟨lowerBlock u r, hlower u hu r hr, lowerBlock_wordColexLt u r hr, ?_⟩
    apply (Finset.subset_erase.mpr ⟨hS, hxS⟩).trans
    exact pairedFacet_erase_subset_lowerBlock u (hmono u hu) r hr
  · intro hR
    rintro ⟨v, hv, ⟨r, hr, heq⟩, hSv⟩
    have hpos : 0 < u r := by omega
    have hmem : u r + 2 * r.val + 1 ∈ pairedRestriction u :=
      (mem_pairedRestriction u _).mpr ⟨r, hpos, rfl⟩
    exact rightEndpoint_not_mem_of_wordColexLt u v (hmono u hu) (hmono v hv) r hr heq
      (hSv (hR hmem))

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextShelling.lean

-- BEGIN GSufficiencyNextShellingCounts.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

theorem pairedFacet_card {m : ℕ} (u : Fin m → ℕ) (hu : Monotone u) :
    (pairedFacet u).card = 2 * m := by
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun r => ({u r + 2 * r.val, u r + 2 * r.val + 1} : Finset ℕ)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · have hum := hu h.le
      have hval : i.val < j.val := h
      rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj <;> omega
    · have hum := hu h.le
      have hval : j.val < i.val := h
      rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj <;> omega
  rw [pairedFacet, Finset.card_biUnion hd]
  simp [Nat.mul_comm]

/-- Count the faces of a given cardinality first contributed by a paired facet.
The restriction cardinality is exactly the corresponding monomial degree. -/
theorem pairedFacet_new_faces_card {m : ℕ} (W : Finset (Fin m → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (u : Fin m → ℕ) (hu : u ∈ W) (n : ℕ)
    (hn : (pairedRestriction u).card ≤ n) :
    (((pairedFacet u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ pairedFacet v)).card =
      Nat.choose (2 * m - (pairedRestriction u).card)
        (n - (pairedRestriction u).card) := by
  classical
  have hfilter : ((pairedFacet u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ pairedFacet v) =
      ((pairedFacet u).powersetCard n).filter (pairedRestriction u ⊆ ·) := by
    apply Finset.filter_congr
    intro S hS
    exact pairedFacet_new_face_iff W hmono hlower u hu S (Finset.mem_powersetCard.mp hS).1
  rw [hfilter, Finset.card_filter_powersetCard_subset _ _ _ (pairedRestriction_subset u) hn,
    pairedFacet_card u (hmono u hu)]

theorem pairedFacet_no_new_faces_of_lt_restriction {m : ℕ} (W : Finset (Fin m → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (u : Fin m → ℕ) (hu : u ∈ W) (n : ℕ)
    (hn : n < (pairedRestriction u).card) :
    ((pairedFacet u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ pairedFacet v) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro S hS hnew
  have hR := (pairedFacet_new_face_iff W hmono hlower u hu S
    (Finset.mem_powersetCard.mp hS).1).mp hnew
  have hcard := Finset.card_le_card hR
  have hScard := (Finset.mem_powersetCard.mp hS).2
  omega

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextShellingCounts.lean

-- BEGIN GSufficiencyNextShellingTotal.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

theorem wordColexLt_iff {m : ℕ} (u v : Fin m → ℕ) :
    wordColexLt u v ↔ toColex u < toColex v := by
  change (∃ r, u r < v r ∧ ∀ j, r < j → u j = v j) ↔
    ∃ r, (∀ j, r < j → u j = v j) ∧ u r < v r
  constructor <;> rintro ⟨r, h1, h2⟩ <;> exact ⟨r, h2, h1⟩

/-- The `n`-label faces whose earliest containing paired facet is `u`. -/
noncomputable def pairedNewFaces {m : ℕ} (W : Finset (Fin m → ℕ)) (n : ℕ) (u : Fin m → ℕ) :
    Finset (Finset ℕ) :=
  ((pairedFacet u).powersetCard n).filter
    (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ pairedFacet v)

theorem pairedNewFaces_pairwiseDisjoint {m : ℕ} (W : Finset (Fin m → ℕ)) (n : ℕ) :
    (W : Set (Fin m → ℕ)).PairwiseDisjoint (pairedNewFaces W n) := by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro S hSu hSv
  obtain ⟨hSu, hnu⟩ := Finset.mem_filter.mp hSu
  obtain ⟨hSv, hnv⟩ := Finset.mem_filter.mp hSv
  have hne' : toColex u ≠ toColex v := by
    intro h
    exact hne (congrArg ofColex h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact hnv ⟨u, hu, (wordColexLt_iff u v).mpr h, (Finset.mem_powersetCard.mp hSu).1⟩
  · exact hnu ⟨v, hv, (wordColexLt_iff v u).mpr h, (Finset.mem_powersetCard.mp hSv).1⟩

/-- Every face belongs to the interval of its earliest containing facet. -/
theorem biUnion_pairedNewFaces {m : ℕ} (W : Finset (Fin m → ℕ)) (n : ℕ) :
    W.biUnion (pairedNewFaces W n) = W.biUnion (fun u => (pairedFacet u).powersetCard n) := by
  classical
  apply Finset.Subset.antisymm
  · intro S hS
    obtain ⟨u, hu, hSu⟩ := Finset.mem_biUnion.mp hS
    exact Finset.mem_biUnion.mpr ⟨u, hu, (Finset.mem_filter.mp hSu).1⟩
  · intro S hS
    obtain ⟨v, hv, hSv⟩ := Finset.mem_biUnion.mp hS
    let A := W.filter (fun u => S ⊆ pairedFacet u)
    have hA : A.Nonempty := ⟨v, Finset.mem_filter.mpr
      ⟨hv, (Finset.mem_powersetCard.mp hSv).1⟩⟩
    obtain ⟨u, huA, hmin⟩ := A.exists_min_image (fun u => toColex u) hA
    obtain ⟨hu, hSu⟩ := Finset.mem_filter.mp huA
    apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨hSu, (Finset.mem_powersetCard.mp hSv).2⟩
    · rintro ⟨w, hw, hwu, hSw⟩
      have hle := hmin w (Finset.mem_filter.mpr ⟨hw, hSw⟩)
      exact (not_lt_of_ge hle) ((wordColexLt_iff w u).mp hwu)

/-- The total face count is the sum of the explicitly disjoint shelling
intervals. No topological or geometric realization premise is used. -/
theorem paired_faces_card_eq_sum {m : ℕ} (W : Finset (Fin m → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W) (n : ℕ) :
    (W.biUnion (fun u => (pairedFacet u).powersetCard n)).card =
      ∑ u ∈ W, if (pairedRestriction u).card ≤ n then
        Nat.choose (2 * m - (pairedRestriction u).card)
          (n - (pairedRestriction u).card) else 0 := by
  classical
  rw [← biUnion_pairedNewFaces W n,
    Finset.card_biUnion (pairedNewFaces_pairwiseDisjoint W n)]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hn : (pairedRestriction u).card ≤ n
  · rw [if_pos hn]
    exact pairedFacet_new_faces_card W hmono hlower u hu n hn
  · rw [if_neg hn]
    change (((pairedFacet u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ pairedFacet v)).card = 0
    rw [pairedFacet_no_new_faces_of_lt_restriction W hmono hlower u hu n (by omega)]
    rfl

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextShellingTotal.lean

-- BEGIN GSufficiencyNextPairedComparison.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- The full `(d + 1)`-element paired facet in `ℕ`, obtained by adjoining the common
initial prefix `0, ..., d + 1 - 2 * (d / 2) - 1` and shifting `pairedFacet u` by
`d + 1 - 2 * (d / 2)`. -/
def fullPairedFacetNat (d : ℕ) (u : Fin (d / 2) → ℕ) : Finset ℕ :=
  Finset.range (d + 1 - 2 * (d / 2)) ∪
    (pairedFacet u).image (fun x => (d + 1 - 2 * (d / 2)) + x)

theorem mem_fullPairedFacetNat (d : ℕ) (u : Fin (d / 2) → ℕ) (x : ℕ) :
    x ∈ fullPairedFacetNat d u ↔
      x < d + 1 - 2 * (d / 2) ∨
        ∃ r : Fin (d / 2),
          x = (d + 1 - 2 * (d / 2)) + u r + 2 * r.val ∨
          x = (d + 1 - 2 * (d / 2)) + u r + 2 * r.val + 1 := by
  simp only [fullPairedFacetNat, Finset.mem_union, Finset.mem_range, Finset.mem_image,
    mem_pairedFacet]
  constructor
  · rintro (hlt | ⟨y, ⟨r, rfl | rfl⟩, rfl⟩)
    · exact Or.inl hlt
    · exact Or.inr ⟨r, Or.inl (by omega)⟩
    · exact Or.inr ⟨r, Or.inr (by omega)⟩
  · rintro (hlt | ⟨r, rfl | rfl⟩)
    · exact Or.inl hlt
    · exact Or.inr ⟨u r + 2 * r.val, ⟨r, Or.inl rfl⟩, by omega⟩
    · exact Or.inr ⟨u r + 2 * r.val + 1, ⟨r, Or.inr rfl⟩, by omega⟩

theorem fullPairedFacetNat_card (d : ℕ) (u : Fin (d / 2) → ℕ) (hu : Monotone u) :
    (fullPairedFacetNat d u).card = d + 1 := by
  let p := d + 1 - 2 * (d / 2)
  have hdisj : Disjoint (Finset.range p) ((pairedFacet u).image (fun x => p + x)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_range] at hx1
    rcases Finset.mem_image.mp hx2 with ⟨y, _, rfl⟩
    omega
  rw [fullPairedFacetNat, Finset.card_union_of_disjoint hdisj, Finset.card_range,
    Finset.card_image_of_injective _ (add_right_injective p), pairedFacet_card u hu]
  omega

theorem fullPairedFacetNat_lt_of_bound (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hbu : ∀ r, u r ≤ s) {x : ℕ} (hx : x ∈ fullPairedFacetNat d u) :
    x < s + d + 1 := by
  rcases (mem_fullPairedFacetNat d u x).mp hx with hlt | ⟨r, rfl | rfl⟩
  · omega
  · have hr := r.isLt
    have hur := hbu r
    omega
  · have hr := r.isLt
    have hur := hbu r
    omega

/-- For any label `b ≥ d + 1 - 2 * (d / 2)` omitted from `fullPairedFacetNat d u`,
the elements of `fullPairedFacetNat d u` strictly above `b` are partitioned into pairs
`{p + u r + 2 * r, p + u r + 2 * r + 1}` with `b < p + u r + 2 * r`. -/
theorem fullPairedFacetNat_filter_gt_card (d : ℕ) (u : Fin (d / 2) → ℕ) (hu : Monotone u)
    (b : ℕ) (hbp : d + 1 - 2 * (d / 2) ≤ b) (hbF : b ∉ fullPairedFacetNat d u) :
    ((fullPairedFacetNat d u).filter (fun x => b < x)).card =
      2 * (Finset.univ.filter
        (fun r : Fin (d / 2) => b < (d + 1 - 2 * (d / 2)) + u r + 2 * r.val)).card := by
  let p := d + 1 - 2 * (d / 2)
  let S := Finset.univ.filter (fun r : Fin (d / 2) => b < p + u r + 2 * r.val)
  have hfilter : (fullPairedFacetNat d u).filter (fun x => b < x) =
      S.biUnion (fun r => {p + u r + 2 * r.val, p + u r + 2 * r.val + 1}) := by
    ext x
    simp only [Finset.mem_filter, mem_fullPairedFacetNat, S, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hlt | ⟨r, rfl | rfl⟩, hbx⟩
      · omega
      · exact ⟨r, hbx, Or.inl rfl⟩
      · have hne : b ≠ p + u r + 2 * r.val := by
          intro hEq
          apply hbF
          rw [mem_fullPairedFacetNat]
          exact Or.inr ⟨r, Or.inl hEq⟩
        exact ⟨r, by omega, Or.inr rfl⟩
    · rintro ⟨r, hbr, rfl | rfl⟩
      · exact ⟨Or.inr ⟨r, Or.inl rfl⟩, hbr⟩
      · exact ⟨Or.inr ⟨r, Or.inr rfl⟩, by omega⟩
  have hdisj : (S : Set (Fin (d / 2))).PairwiseDisjoint
      (fun r : Fin (d / 2) => ({p + u r + 2 * r.val, p + u r + 2 * r.val + 1} : Finset ℕ)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · have hum := hu h.le
      have hval : i.val < j.val := h
      rcases hxi with rfl | rfl <;> rcases hxj with hxj | hxj <;> omega
    · have hum := hu h.le
      have hval : j.val < i.val := h
      rcases hxi with rfl | rfl <;> rcases hxj with hxj | hxj <;> omega
  rw [hfilter, Finset.card_biUnion hdisj]
  have hpair (r : Fin (d / 2)) :
      ({p + u r + 2 * r.val, p + u r + 2 * r.val + 1} : Finset ℕ).card = 2 :=
    Finset.card_pair (by omega)
  simp_rw [hpair]
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem fullPairedFacetNat_filter_le_card_lt_of_not_mem (d : ℕ) (hd : 2 ≤ d)
    (u : Fin (d / 2) → ℕ) (hu : Monotone u) (hpos : ∃ r, 0 < u r)
    (b : ℕ) (hbp : d + 1 - 2 * (d / 2) ≤ b) (hbd : b ≤ d + 1)
    (hbF : b ∉ fullPairedFacetNat d u) :
    ((fullPairedFacetNat d u).filter (fun x => x ≤ b)).card < d := by
  let p := d + 1 - 2 * (d / 2)
  rcases hpos with ⟨r₀, hr₀⟩
  let rLast : Fin (d / 2) := ⟨d / 2 - 1, by omega⟩
  have hr₀Last : r₀ ≤ rLast := by
    change r₀.val ≤ d / 2 - 1
    have := r₀.isLt
    omega
  have huLast : 0 < u rLast := lt_of_lt_of_le hr₀ (hu hr₀Last)
  have hne0 : b ≠ p + u rLast + 2 * rLast.val := by
    intro hEq
    exact hbF ((mem_fullPairedFacetNat d u b).mpr (Or.inr ⟨rLast, Or.inl hEq⟩))
  have hne1 : b ≠ p + u rLast + 2 * rLast.val + 1 := by
    intro hEq
    exact hbF ((mem_fullPairedFacetNat d u b).mpr (Or.inr ⟨rLast, Or.inr hEq⟩))
  have hbLast : b < p + u rLast + 2 * rLast.val := by
    change b < (d + 1 - 2 * (d / 2)) + u rLast + 2 * (d / 2 - 1)
    change b ≠ (d + 1 - 2 * (d / 2)) + u rLast + 2 * (d / 2 - 1) at hne0
    change b ≠ (d + 1 - 2 * (d / 2)) + u rLast + 2 * (d / 2 - 1) + 1 at hne1
    omega
  have hSne : (Finset.univ.filter
      (fun r : Fin (d / 2) => b < p + u r + 2 * r.val)).Nonempty :=
    ⟨rLast, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbLast⟩⟩
  have hScard : 1 ≤ (Finset.univ.filter
      (fun r : Fin (d / 2) => b < p + u r + 2 * r.val)).card :=
    Finset.card_pos.mpr hSne
  have hgtCard := fullPairedFacetNat_filter_gt_card d u hu b hbp hbF
  have hsum := Finset.card_filter_add_card_filter_not
    (s := fullPairedFacetNat d u) (fun x => x ≤ b)
  have hnot : (fullPairedFacetNat d u).filter (fun x => ¬ x ≤ b) =
      (fullPairedFacetNat d u).filter (fun x => b < x) := by
    apply Finset.filter_congr
    intro x _
    exact not_le
  rw [hnot, fullPairedFacetNat_card d u hu, hgtCard] at hsum
  dsimp only [p] at hScard
  omega

/-- If `r₀` is the first index where `u r₀ > 0`, then `c = (d + 1 - 2 * (d / 2)) + 2 * r₀`
is the exact first omitted label of `fullPairedFacetNat d u`. -/
theorem fullPairedFacetNat_first_omitted (d : ℕ) (u : Fin (d / 2) → ℕ) (hu : Monotone u)
    (r₀ : Fin (d / 2)) (hr₀ : 0 < u r₀) (hzero : ∀ r < r₀, u r = 0) :
    let c := (d + 1 - 2 * (d / 2)) + 2 * r₀.val
    c ∉ fullPairedFacetNat d u ∧
    ∀ b < c, b ∈ fullPairedFacetNat d u := by
  intro c
  let p := d + 1 - 2 * (d / 2)
  refine ⟨?_, ?_⟩
  · rw [mem_fullPairedFacetNat]
    rintro (hlt | ⟨r, hEq | hEq⟩)
    · omega
    · by_cases hrr₀ : r < r₀
      · have huz := hzero r hrr₀
        have hlt : r.val < r₀.val := hrr₀
        omega
      · have hr₀r : r₀ ≤ r := le_of_not_gt hrr₀
        have hum := hu hr₀r
        have hle : r₀.val ≤ r.val := hr₀r
        omega
    · by_cases hrr₀ : r < r₀
      · have huz := hzero r hrr₀
        have hlt : r.val < r₀.val := hrr₀
        omega
      · have hr₀r : r₀ ≤ r := le_of_not_gt hrr₀
        have hum := hu hr₀r
        have hle : r₀.val ≤ r.val := hr₀r
        omega
  · intro b hbc
    rw [mem_fullPairedFacetNat]
    by_cases hbp : b < p
    · exact Or.inl hbp
    · right
      let k := (b - p) / 2
      have hk : k < r₀.val := by omega
      let r : Fin (d / 2) := ⟨k, lt_trans hk r₀.isLt⟩
      have hrr₀ : r < r₀ := hk
      have huz : u r = 0 := hzero r hrr₀
      refine ⟨r, ?_⟩
      change b = p + u r + 2 * k ∨ b = p + u r + 2 * k + 1
      rw [huz]
      omega

/-- When `wordColexLt v u` at last differing index `r`, the right endpoint
`ℓ = p + u r + 2 * r + 1` belongs to `fullPairedFacetNat d u`, is absent from
`fullPairedFacetNat d v`, and all labels strictly above `ℓ` agree between the two facets. -/
theorem fullPairedFacetNat_diff_of_wordColexLt (d : ℕ) (u v : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hv : Monotone v) (r : Fin (d / 2))
    (hr : v r < u r) (heq : ∀ j, r < j → v j = u j) :
    let ℓ := (d + 1 - 2 * (d / 2)) + u r + 2 * r.val + 1
    ℓ ∈ fullPairedFacetNat d u ∧
    ℓ ∉ fullPairedFacetNat d v ∧
    ∀ k, ℓ < k → (k ∈ fullPairedFacetNat d u ↔ k ∈ fullPairedFacetNat d v) := by
  intro ℓ
  let p := d + 1 - 2 * (d / 2)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_fullPairedFacetNat]
    exact Or.inr ⟨r, Or.inr rfl⟩
  · rw [mem_fullPairedFacetNat]
    rintro (hlt | ⟨j, hEq | hEq⟩)
    · omega
    · apply rightEndpoint_not_mem_of_wordColexLt u v hu hv r hr heq
      rw [mem_pairedFacet]
      exact ⟨j, Or.inl (by omega)⟩
    · apply rightEndpoint_not_mem_of_wordColexLt u v hu hv r hr heq
      rw [mem_pairedFacet]
      exact ⟨j, Or.inr (by omega)⟩
  · intro k hℓk
    rw [mem_fullPairedFacetNat, mem_fullPairedFacetNat]
    constructor
    · rintro (hlt | ⟨j, rfl | rfl⟩)
      · omega
      · have hrj : r < j := by
          by_contra hle
          have hjr : j ≤ r := le_of_not_gt hle
          have huj := hu hjr
          have hjr' : j.val ≤ r.val := hjr
          omega
        exact Or.inr ⟨j, Or.inl (by rw [heq j hrj])⟩
      · have hrj : r < j := by
          by_contra hle
          have hjr : j ≤ r := le_of_not_gt hle
          have huj := hu hjr
          have hjr' : j.val ≤ r.val := hjr
          omega
        exact Or.inr ⟨j, Or.inr (by rw [heq j hrj])⟩
    · rintro (hlt | ⟨j, rfl | rfl⟩)
      · omega
      · have hrj : r < j := by
          by_contra hle
          have hjr : j ≤ r := le_of_not_gt hle
          have hvj := hv hjr
          have hjr' : j.val ≤ r.val := hjr
          omega
        exact Or.inr ⟨j, Or.inl (by rw [← heq j hrj])⟩
      · have hrj : r < j := by
          by_contra hle
          have hjr : j ≤ r := le_of_not_gt hle
          have hvj := hv hjr
          have hjr' : j.val ≤ r.val := hjr
          omega
        exact Or.inr ⟨j, Or.inr (by rw [← heq j hrj])⟩

/-- The full `(d + 1)`-element paired facet embedded in `Fin (s + d + 1)`. -/
def fullPairedFacet (d s : ℕ) (u : Fin (d / 2) → ℕ) : Finset (Fin (s + d + 1)) :=
  Finset.univ.filter (fun j : Fin (s + d + 1) => j.val ∈ fullPairedFacetNat d u)

@[simp] theorem mem_fullPairedFacet (d s : ℕ) (u : Fin (d / 2) → ℕ) (j : Fin (s + d + 1)) :
    j ∈ fullPairedFacet d s u ↔ j.val ∈ fullPairedFacetNat d u := by
  simp [fullPairedFacet]

theorem fullPairedFacet_filter_card (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hbu : ∀ r, u r ≤ s) (P : ℕ → Prop) [DecidablePred P] :
    ((fullPairedFacet d s u).filter (fun j => P j.val)).card =
      ((fullPairedFacetNat d u).filter P).card := by
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    obtain ⟨hjF, hjP⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨(mem_fullPairedFacet d s u j).mp hjF, hjP⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro x hx
    obtain ⟨hxF, hxP⟩ := Finset.mem_filter.mp hx
    refine ⟨⟨x, fullPairedFacetNat_lt_of_bound d s u hbu hxF⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨(mem_fullPairedFacet d s u _).mpr hxF, hxP⟩

/-- For any two bounded monotone words `u, v : Fin (d / 2) → ℕ` with `wordColexLt v u`,
first positive-letter indices `r_u, r_v`, and any sample set `B ⊆ Fin (s + d + 1)` containing
both first omitted labels `c_u, c_v` and bounded above by `d + 1`, the Billera–Lee comparison
polynomial `cyclicComparisonPolynomial d B (fullPairedFacet d s u) (fullPairedFacet d s v)`
has colex leading coefficient equal to `1`. -/
theorem fullPairedFacet_comparisonPolynomial_leadingCoeff_eq_one
    (d s : ℕ) (hd : 2 ≤ d)
    (u v : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hv : Monotone v)
    (hbu : ∀ j, u j ≤ s) (hbv : ∀ j, v j ≤ s)
    (ru rv : Fin (d / 2))
    (hru : 0 < u ru) (hzerou : ∀ j < ru, u j = 0)
    (hrv : 0 < v rv) (hzerov : ∀ j < rv, v j = 0)
    (r : Fin (d / 2)) (hr : v r < u r) (heq : ∀ j, r < j → v j = u j)
    (B : Finset (Fin (s + d + 1))) (hB_le : ∀ b ∈ B, b.val ≤ d + 1)
    (hcuB : ⟨(d + 1 - 2 * (d / 2)) + 2 * ru.val,
      by have := ru.isLt; omega⟩ ∈ B)
    (hcvB : ⟨(d + 1 - 2 * (d / 2)) + 2 * rv.val,
      by have := rv.isLt; omega⟩ ∈ B) :
    (colexMonomialOrder (s + d + 1)).leadingCoeff
      (cyclicComparisonPolynomial d B (fullPairedFacet d s u) (fullPairedFacet d s v)) = 1 := by
  let p := d + 1 - 2 * (d / 2)
  let cF : Fin (s + d + 1) := ⟨p + 2 * ru.val, by have := ru.isLt; omega⟩
  let cG : Fin (s + d + 1) := ⟨p + 2 * rv.val, by have := rv.isLt; omega⟩
  have hℓlt : p + u r + 2 * r.val + 1 < s + d + 1 := by
    have := r.isLt
    have := hbu r
    omega
  let ℓ : Fin (s + d + 1) := ⟨p + u r + 2 * r.val + 1, hℓlt⟩
  obtain ⟨hcFF_nat, hbeforeF_nat⟩ := fullPairedFacetNat_first_omitted d u hu ru hru hzerou
  obtain ⟨hcGG_nat, hbeforeG_nat⟩ := fullPairedFacetNat_first_omitted d v hv rv hrv hzerov
  obtain ⟨hℓF_nat, hℓG_nat, hagree_nat⟩ := fullPairedFacetNat_diff_of_wordColexLt d u v hu hv r hr heq
  have hcF0 : cF ≠ 0 := by
    intro h0
    have hval : cF.val = 0 := congrArg Fin.val h0
    change p + 2 * ru.val = 0 at hval
    omega
  have hcG0 : cG ≠ 0 := by
    intro h0
    have hval : cG.val = 0 := congrArg Fin.val h0
    change p + 2 * rv.val = 0 at hval
    omega
  have hcFF : cF ∉ fullPairedFacet d s u := by
    rw [mem_fullPairedFacet]
    exact hcFF_nat
  have hcGG : cG ∉ fullPairedFacet d s v := by
    rw [mem_fullPairedFacet]
    exact hcGG_nat
  have hbeforeF : ∀ b ∈ B, b < cF → b ∈ fullPairedFacet d s u := by
    intro b _ hlt
    rw [mem_fullPairedFacet]
    exact hbeforeF_nat b.val hlt
  have hbeforeG : ∀ b ∈ B, b < cG → b ∈ fullPairedFacet d s v := by
    intro b _ hlt
    rw [mem_fullPairedFacet]
    exact hbeforeG_nat b.val hlt
  have hafterF : ∀ b ∈ B, cF < b → b ∉ fullPairedFacet d s u →
      ((fullPairedFacet d s u).filter (fun j => j ≤ b)).card < d := by
    intro b hbB hlt hbnot
    rw [mem_fullPairedFacet] at hbnot
    have hcard_eq : ((fullPairedFacet d s u).filter (fun j => j ≤ b)).card =
        ((fullPairedFacetNat d u).filter (fun x => x ≤ b.val)).card :=
      fullPairedFacet_filter_card d s u hbu (fun x => x ≤ b.val)
    rw [hcard_eq]
    have hbp : p ≤ b.val := by
      have : cF.val < b.val := hlt
      change p + 2 * ru.val < b.val at this
      omega
    exact fullPairedFacetNat_filter_le_card_lt_of_not_mem d hd u hu ⟨ru, hru⟩
      b.val hbp (hB_le b hbB) hbnot
  have hafterG : ∀ b ∈ B, cG < b → b ∉ fullPairedFacet d s v →
      ((fullPairedFacet d s v).filter (fun j => j ≤ b)).card < d := by
    intro b hbB hlt hbnot
    rw [mem_fullPairedFacet] at hbnot
    have hcard_eq : ((fullPairedFacet d s v).filter (fun j => j ≤ b)).card =
        ((fullPairedFacetNat d v).filter (fun x => x ≤ b.val)).card :=
      fullPairedFacet_filter_card d s v hbv (fun x => x ≤ b.val)
    rw [hcard_eq]
    have hbp : p ≤ b.val := by
      have : cG.val < b.val := hlt
      change p + 2 * rv.val < b.val at this
      omega
    exact fullPairedFacetNat_filter_le_card_lt_of_not_mem d hd v hv ⟨rv, hrv⟩
      b.val hbp (hB_le b hbB) hbnot
  have hevenF : Even ((fullPairedFacet d s u).filter (fun j => cF < j)).card := by
    have hcard_eq : ((fullPairedFacet d s u).filter (fun j => cF < j)).card =
        ((fullPairedFacetNat d u).filter (fun x => cF.val < x)).card :=
      fullPairedFacet_filter_card d s u hbu (fun x => cF.val < x)
    rw [hcard_eq, fullPairedFacetNat_filter_gt_card d u hu cF.val
      (by change p ≤ p + 2 * ru.val; omega) hcFF_nat]
    exact even_two_mul _
  have hℓF : ℓ ∈ fullPairedFacet d s u := (mem_fullPairedFacet d s u ℓ).mpr hℓF_nat
  have hℓG : ℓ ∉ fullPairedFacet d s v := by
    rw [mem_fullPairedFacet]
    exact hℓG_nat
  have hagree : ∀ k : Fin (s + d + 1), ℓ < k →
      (k ∈ fullPairedFacet d s u ↔ k ∈ fullPairedFacet d s v) := by
    intro k hlt
    rw [mem_fullPairedFacet, mem_fullPairedFacet]
    exact hagree_nat k.val hlt
  have hcFℓ : cF < ℓ := by
    have hur : 0 < u r := by omega
    have hrur : ru ≤ r := by
      by_contra hlt
      exact (ne_of_gt hur (hzerou r (lt_of_not_ge hlt))).elim
    have hrur' : ru.val ≤ r.val := hrur
    change p + 2 * ru.val < p + u r + 2 * r.val + 1
    omega
  have hcGℓ : cG ≤ ℓ := by
    by_contra hlt
    exact hℓG_nat (hbeforeG_nat ℓ.val (lt_of_not_ge hlt))
  have hcardG : ((fullPairedFacet d s v).filter (fun j => j ≤ cG)).card ≤ d := by
    have hcard_eq : ((fullPairedFacet d s v).filter (fun j => j ≤ cG)).card =
        ((fullPairedFacetNat d v).filter (fun x => x ≤ cG.val)).card :=
      fullPairedFacet_filter_card d s v hbv (fun x => x ≤ cG.val)
    rw [hcard_eq]
    have hlt := fullPairedFacetNat_filter_le_card_lt_of_not_mem d hd v hv ⟨rv, hrv⟩
      cG.val (by change p ≤ p + 2 * rv.val; omega) (hB_le cG hcvB) hcGG_nat
    omega
  exact (cyclicComparisonPolynomial_degree_leading_eq_one d B
    (fullPairedFacet d s u) (fullPairedFacet d s v) cF cG ℓ
    hcuB hcF0 hcFF hbeforeF hafterF hevenF
    hcvB hcG0 hcGG hbeforeG hafterG
    hℓF hℓG hagree hcFℓ hcGℓ hcardG).2

/-- Any finite family of Billera–Lee comparison polynomials whose members have colex leading
coefficient `1` admits a simultaneous strictly increasing positive rational evaluation. -/
theorem exists_increasing_pos_eval_of_leadingCoeff_eq_one {n : ℕ}
    (P : Finset (MvPolynomial (Fin n) ℚ))
    (hP : ∀ p ∈ P, (colexMonomialOrder n).leadingCoeff p = 1) :
    ∃ t : Fin n → ℚ, (∀ i, 0 < t i) ∧ StrictMono t ∧
      ∀ p ∈ P, 0 < MvPolynomial.eval t p := by
  apply exists_increasing_pos_eval_of_colex_leading_pos P
  intro p hp
  apply exists_colex_leading_pos_of_leadingCoeff_pos p
  rw [hP p hp]
  exact zero_lt_one

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextPairedComparison.lean

-- BEGIN MacaulayGrowth.lean
/- Arithmetic proof source: accepted Prove2Me submission
fc1f53e1-19ed-5c67-9d5e-d9e6dac57f14 (Finsupp Macaulay cardinal bound).
Only its elementary top/remainder/growth lemmas are reused here.
Nat.macaulayPow has exactly the published definition body
0d6c2441-82b9-5cba-aa9d-bc350be56bb6; imports are narrowed locally.
No final g-theorem target or placeholder theorem is imported. -/

set_option autoImplicit false
open scoped BigOperators

namespace Nat

def macaulayPow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a =>
      (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1) + 1).choose (d + 2) +
        macaulayPow d (a - (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)).choose (d + 1))

end Nat

namespace Grunbaum2003.MacaulayGrowth

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

theorem macaulayPow_one (a : ℕ) : Nat.macaulayPow 1 a = (a + 1).choose 2 := by
  rw [macaulayPow_succ, top_zero_left, rem_zero_left, macaulayPow_zero]; rfl

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

theorem top_succ_of_le (d a : ℕ) (ha : 1 ≤ a) (h : a ≤ d + 2) : top (d + 1) a = d + 2 :=
  top_eq_of (d + 1) a (d + 2) (by rw [Nat.choose_self]; exact ha)
    (by have : (d + 2 + 1).choose (d + 1 + 1) = d + 2 + 1 := Nat.choose_succ_self_right (d + 2); omega)

theorem macaulayPow_eq_self : ∀ (d a : ℕ), a ≤ d + 1 → Nat.macaulayPow (d + 1) a = a
  | d, 0, _ => macaulayPow_zero_right (d + 1)
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [macaulayPow_one]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [macaulayPow_succ, ht, hr, macaulayPow_eq_self d a (by omega)]
      have : (d + 2 + 1).choose (d + 1 + 2) = 1 := by
        rw [show d + 1 + 2 = d + 2 + 1 by omega, Nat.choose_self]
      omega

def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a => (top d a - 1).choose (d + 1) + low d (rem d a)

theorem low_zero (a : ℕ) : low 0 a = 0 := rfl

theorem low_succ (d a : ℕ) : low (d + 1) a = (top d a - 1).choose (d + 1) + low d (rem d a) := rfl

theorem low_zero_right : ∀ d : ℕ, low d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [low_succ, top_zero_right, rem_zero_right, low_zero_right d, Nat.choose_eq_zero_of_lt (by omega)]

theorem low_eq_zero : ∀ (d a : ℕ), a ≤ d + 1 → low (d + 1) a = 0
  | d, 0, _ => low_zero_right _
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [low_succ, top_zero_left, low_zero]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [low_succ, ht, hr, low_eq_zero d a (by omega), Nat.choose_eq_zero_of_lt (by omega)]

theorem low_lt_choose : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → d + 1 ≤ m →
    low (d + 1) r < m.choose (d + 1)
  | 0, m, r, h, hm => by
      rw [low_succ, top_zero_left, low_zero]
      simp only [zero_add, Nat.choose_one_right, add_zero] at h ⊢
      omega
  | d + 1, m, r, h, hm => by
      rw [low_succ]
      show (top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r) < m.choose (d + 2)
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [top_zero_right, rem_zero_right, low_zero_right, Nat.choose_eq_zero_of_lt (by omega),
          zero_add]
        exact Nat.choose_pos (by omega)
      · have hT' : d + 1 < top (d + 1) r := d_lt_top_of_pos _ _ hr
        have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (by omega)]; exact rem_lt (d + 1) r
        have ih := low_lt_choose d (top (d + 1) r - 1) (rem (d + 1) r) hRlt (by omega)
        have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
            (top (d + 1) r).choose (d + 2) := by
          have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
          rw [Nat.sub_add_cancel (show 1 ≤ top (d + 1) r by omega)] at this
          rw [add_comm]; exact this.symm
        have h2 : (top (d + 1) r).choose (d + 2) ≤ m.choose (d + 2) := Nat.choose_le_choose _ hT
        omega

theorem macaulayPow_low_add : ∀ (d a : ℕ),
    Nat.macaulayPow (d + 1) (low (d + 1) a) + a = Nat.macaulayPow (d + 1) a
  | 0, a => by
      rw [low_succ, top_zero_left, low_zero, add_zero, macaulayPow_one, macaulayPow_one,
        Nat.choose_one_right]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rfl
      · have h2 : (a + 1).choose 2 = a + a.choose 2 := by
          have := Nat.choose_succ_succ' a 1; rw [Nat.choose_one_right] at this; exact this
        rw [Nat.sub_add_cancel ha]; omega
  | d + 1, a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [low_zero_right, add_zero]
      · set T := top (d + 1) a with hT
        set R := rem (d + 1) a with hR
        have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
        have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
        have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
        have ih := macaulayPow_low_add d R
        rw [low_succ, macaulayPow_succ (d + 1) a]
        show Nat.macaulayPow (d + 2) ((T - 1).choose (d + 2) + low (d + 1) R) + a =
          (T + 1).choose (d + 3) + Nat.macaulayPow (d + 1) R
        rcases (show T = d + 2 ∨ d + 3 ≤ T by omega) with hT2 | hT3
        ·
          have hC : (d + 2).choose (d + 1) = d + 2 := Nat.choose_succ_self_right (d + 1)
          have hR1 : R ≤ d + 1 := by rw [hT2] at hRlt; omega
          rw [hT2, show d + 2 - 1 = d + 1 from rfl, Nat.choose_succ_self, zero_add, low_eq_zero d R hR1,
            macaulayPow_zero_right, macaulayPow_eq_self d R hR1, Nat.choose_self]
          rw [hT2, Nat.choose_self] at hRa
          omega
        ·
          have hlow : low (d + 1) R < (T - 1).choose (d + 1) :=
            low_lt_choose d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt) (by omega)
          have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
            have := Nat.choose_succ_succ' (T - 1) (d + 1)
            rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
            rw [add_comm]; exact this.symm
          have hpasc' : T.choose (d + 3) + T.choose (d + 2) = (T + 1).choose (d + 3) := by
            rw [Nat.choose_succ_succ' T (d + 2), add_comm]
          have htop : top (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = T - 1 :=
            top_eq_of (d + 1) _ (T - 1) (Nat.le_add_right _ _)
              (by rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; show _ < T.choose (d + 2); omega)
          have hrem : rem (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = low (d + 1) R := by
            simp [rem, htop]
          rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]
          show T.choose (d + 3) + Nat.macaulayPow (d + 1) (low (d + 1) R) + a = _
          omega

theorem le_choose_add_low : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → r ≤ m.choose d + low (d + 1) r
  | 0, m, r, _ => by
      rw [low_succ, top_zero_left, low_zero, Nat.choose_zero_right, Nat.choose_one_right]; omega
  | d + 1, m, r, h => by
      rw [low_succ]
      show r ≤ m.choose (d + 1) + ((top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r))
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      have hT1 : 1 ≤ top (d + 1) r := by have := d_le_top (d + 1) r; omega
      have hRa : rem (d + 1) r + (top (d + 1) r).choose (d + 2) = r := rem_add_choose (d + 1) r
      have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
        rw [Nat.sub_add_cancel hT1]; exact rem_lt (d + 1) r
      have ih := le_choose_add_low d (top (d + 1) r - 1) (rem (d + 1) r) hRlt
      have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
          (top (d + 1) r).choose (d + 2) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h2 : (top (d + 1) r - 1).choose (d + 1) + (top (d + 1) r - 1).choose d =
          (top (d + 1) r).choose (d + 1) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) d
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h3 : (top (d + 1) r).choose (d + 1) ≤ m.choose (d + 1) := Nat.choose_le_choose _ hT
      omega

theorem le_add_low : ∀ (d a s : ℕ), a ≤ Nat.macaulayPow d s → a ≤ s + low (d + 1) a
  | 0, a, s, h => by rw [macaulayPow_zero] at h; omega
  | d + 1, a, s, h => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact Nat.zero_le _
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      set T' := top d s with hT'
      have hs : rem d s + T'.choose (d + 1) = s := rem_add_choose d s

      have hlt : Nat.macaulayPow (d + 1) s < (T' + 1 + 1).choose (d + 1 + 1) :=
        macaulayPow_lt_choose (d + 1) (T' + 1) s (lt_choose_top_succ d s)
      have hTT' : T ≤ T' + 1 := by
        have := top_lt_of_lt_choose (d + 1) a (T' + 1 + 1) (h.trans_lt hlt); omega
      rw [low_succ]
      show a ≤ s + ((T - 1).choose (d + 2) + low (d + 1) R)
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
        have := Nat.choose_succ_succ' (T - 1) (d + 1)
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      rcases (show T ≤ T' ∨ T = T' + 1 by omega) with hle | heq
      ·
        have h1 : T.choose (d + 1) ≤ T'.choose (d + 1) := Nat.choose_le_choose _ hle
        have h2 : R ≤ (T - 1).choose d + low (d + 1) R :=
          le_choose_add_low d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt)
        have h3 : (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
          have := Nat.choose_succ_succ' (T - 1) d
          rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
          rw [add_comm]; exact this.symm
        omega
      ·
        have hμ : Nat.macaulayPow (d + 1) s = (T' + 1).choose (d + 2) + Nat.macaulayPow d (rem d s) :=
          macaulayPow_succ d s
        rw [← heq] at hμ
        rw [show T' = T - 1 by omega] at hs
        have hR' : R ≤ Nat.macaulayPow d (rem d s) := by omega
        have ih := le_add_low d R (rem d s) hR'
        omega


end Grunbaum2003.MacaulayGrowth
-- END MacaulayGrowth.lean

-- BEGIN MacaulayCompressedBW.lean
/- Ordinary-source replay of the recursive compressed monomial construction.
The arithmetic prefix is shared with work.MacaulayGrowth. The source range
ends at card_Bplus_BW; no polynomial-ideal existence result is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Grunbaum2003.MacaulayCompressed
open MacaulayGrowth

variable (n : ℕ)

noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

@[scoped simp] theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

noncomputable def MonW (w e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  (Mon n e).filter (fun m => ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0)

theorem mem_MonW (w e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ MonW n w e ↔ m.degree = e ∧ ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0 := by
  simp [MonW]

theorem MonW_mono {w w' : ℕ} (h : w ≤ w') (e : ℕ) : MonW n w e ⊆ MonW n w' e := by
  intro m hm
  rw [mem_MonW] at hm ⊢
  exact ⟨hm.1, fun i hi => hm.2 i (h.trans hi)⟩

theorem MonW_of_le {w : ℕ} (h : n + 1 ≤ w) (e : ℕ) : MonW n w e = Mon n e := by
  ext m
  simp only [mem_MonW, mem_Mon, and_iff_left_iff_imp]
  intro _ i hi
  exact absurd (lt_of_lt_of_le i.2 (h.trans hi)) (lt_irrefl _)

noncomputable def var (j : ℕ) (h : j < n + 1) : Fin (n + 1) →₀ ℕ := Finsupp.single ⟨j, h⟩ 1

@[scoped simp] theorem var_apply (j : ℕ) (h : j < n + 1) (i : Fin (n + 1)) :
    var n j h i = if (i : ℕ) = j then 1 else 0 := by
  simp only [var, Finsupp.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

@[scoped simp] theorem degree_var (j : ℕ) (h : j < n + 1) : (var n j h).degree = 1 := by
  simp [var]

noncomputable def shift (j : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  if h : j < n + 1 then B.map (addRightEmbedding (var n j h)) else ∅

theorem shift_of_le {j : ℕ} (h : n + 1 ≤ j) (B : Finset (Fin (n + 1) →₀ ℕ)) : shift n j B = ∅ := by
  simp [shift, not_lt.mpr h]

theorem mem_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ ∃ b ∈ B, b + var n j h = u := by
  simp [shift, h]

theorem card_shift {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    (shift n j B).card = B.card := by
  simp [shift, h]

@[scoped simp] theorem shift_empty (j : ℕ) : shift n j (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  unfold shift; split_ifs <;> simp

theorem shift_mono (j : ℕ) {B B' : Finset (Fin (n + 1) →₀ ℕ)} (hB : B ⊆ B') :
    shift n j B ⊆ shift n j B' := by
  unfold shift; split_ifs
  · exact Finset.map_subset_map.mpr hB
  · exact Finset.Subset.refl _

theorem sub_var_add_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    u - var n j h + var n j h = u := by
  unfold var
  exact Finsupp.sub_add_single_one_cancel (by omega)

theorem add_var_sub_var {j : ℕ} (h : j < n + 1) (b : Fin (n + 1) →₀ ℕ) :
    b + var n j h - var n j h = b := by
  simp

theorem mem_shift_iff {j : ℕ} (h : j < n + 1) (B : Finset (Fin (n + 1) →₀ ℕ))
    (u : Fin (n + 1) →₀ ℕ) :
    u ∈ shift n j B ↔ 1 ≤ u ⟨j, h⟩ ∧ u - var n j h ∈ B := by
  rw [mem_shift n h]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, by simpa using hb⟩
    simp [var]
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, sub_var_add_var n h u h1⟩

theorem degree_sub_var {j : ℕ} (h : j < n + 1) (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u ⟨j, h⟩) :
    (u - var n j h).degree + 1 = u.degree := by
  conv_rhs => rw [← sub_var_add_var n h u hu]
  rw [map_add, degree_var]

theorem MonW_succ {j : ℕ} (h : j < n + 1) (e : ℕ) :
    MonW n (j + 1) (e + 1) = MonW n j (e + 1) ∪ shift n j (MonW n (j + 1) e) := by
  ext u
  rw [Finset.mem_union, mem_shift_iff n h, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨hdeg, hsupp⟩
    by_cases huj : u ⟨j, h⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, h⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp i hij
    · refine Or.inr ⟨by omega, ?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u (by omega)
        omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
        rw [hsupp i hi]; simp
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, hdeg, hsupp⟩)
    · exact ⟨hdeg, fun i hi => hsupp i (by omega)⟩
    · refine ⟨?_, fun i hi => ?_⟩
      · have := degree_sub_var n h u h1
        omega
      · have := hsupp i hi
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at this
        have hij : (i : ℕ) ≠ j := by omega
        simpa [hij] using this

theorem disjoint_MonW_shift (j e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    Disjoint (MonW n j e) (shift n j B) := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  by_cases h : j < n + 1
  · rw [mem_shift_iff n h] at hu'
    rw [mem_MonW] at hu
    have := hu.2 ⟨j, h⟩ le_rfl
    omega
  · rw [shift_of_le n (not_lt.mp h)] at hu'
    simp at hu'

theorem MonW_zero_succ (e : ℕ) : MonW n 0 (e + 1) = ∅ := by
  ext u
  simp only [mem_MonW, Finset.notMem_empty, iff_false, not_and]
  intro hdeg hsupp
  have : u = 0 := by
    ext i; exact hsupp i (Nat.zero_le _)
  rw [this, map_zero] at hdeg
  omega

theorem MonW_zero_right (w : ℕ) : MonW n w 0 = {0} := by
  ext u
  simp only [mem_MonW, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; simp

theorem card_MonW : ∀ (w e : ℕ), w ≤ n + 1 → (MonW n w e).card = (w + e - 1).choose e
  | w, 0, _ => by simp [MonW_zero_right]
  | 0, e + 1, _ => by
      rw [MonW_zero_succ, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]
  | w + 1, e + 1, hw => by
      rw [MonW_succ n (by omega), Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _),
        card_shift n (by omega), card_MonW w (e + 1) (by omega), card_MonW (w + 1) e hw,
        show w + 1 + (e + 1) - 1 = (w + e) + 1 by omega, Nat.choose_succ_succ',
        show w + (e + 1) - 1 = w + e by omega, show w + 1 + e - 1 = w + e by omega, add_comm]

theorem card_Mon (e : ℕ) : (Mon n e).card = (n + e).choose n := by
  rw [← MonW_of_le n le_rfl, card_MonW n (n + 1) e le_rfl, show n + 1 + e - 1 = n + e by omega,
    Nat.choose_symm_add]

theorem degree_sub_single (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hu : 1 ≤ u i) :
    (u - Finsupp.single i 1).degree + 1 = u.degree := by
  conv_rhs => rw [← Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)]
  rw [map_add, Finsupp.degree_single]

theorem exists_one_le_of_degree_ne_zero (u : Fin (n + 1) →₀ ℕ) (hu : u.degree ≠ 0) :
    ∃ i, 1 ≤ u i := by
  rw [Finsupp.degree_eq_sum] at hu
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  exact ⟨i, by omega⟩

theorem exists_sub_single_pos (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hi : 1 ≤ u i)
    (hdeg : 2 ≤ u.degree) : ∃ i', 1 ≤ u i' ∧ 1 ≤ (u - Finsupp.single i' 1 : Fin (n + 1) →₀ ℕ) i := by
  by_cases h2 : 2 ≤ u i
  · refine ⟨i, hi, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
  · have hui : u i = 1 := by omega
    have hsum : u i + ∑ k ∈ Finset.univ.erase i, u k = u.degree := by
      rw [Finsupp.degree_eq_sum]; exact Finset.add_sum_erase _ _ (Finset.mem_univ i)
    have hne : ∑ k ∈ Finset.univ.erase i, u k ≠ 0 := by omega
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    refine ⟨k, by omega, ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hki]; omega

noncomputable def BW : ℕ → ℕ → Finset (Fin (n + 1) →₀ ℕ)
  | 0, a => if a = 0 then ∅ else {0}
  | δ + 1, a => MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW δ (rem δ a))

theorem BW_succ (δ a : ℕ) :
    BW n (δ + 1) a = MonW n (top δ a - δ) (δ + 1) ∪ shift n (top δ a - δ) (BW n δ (rem δ a)) := rfl

theorem BW_zero_right : ∀ d : ℕ, BW n d 0 = ∅
  | 0 => by simp [BW]
  | δ + 1 => by
      rw [BW_succ, top_zero_right, rem_zero_right, BW_zero_right δ, Nat.sub_self, MonW_zero_succ,
        shift_empty, Finset.empty_union]

theorem card_MonW_succ_eq (w δ : ℕ) (hw : w ≤ n + 1) :
    (MonW n w (δ + 1)).card = (w + δ).choose (δ + 1) := by
  rw [card_MonW n w (δ + 1) hw, show w + (δ + 1) - 1 = w + δ by omega]

theorem top_sub_add (δ a : ℕ) : top δ a - δ + δ = top δ a := Nat.sub_add_cancel (d_le_top δ a)

theorem top_le_of_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a ≤ w + δ := by
  by_contra h
  push Not at h
  have h1 : (w + δ + 1).choose (δ + 1) ≤ (top δ a).choose (δ + 1) := Nat.choose_le_choose _ h
  have h2 := choose_top_le δ a
  rw [Nat.choose_succ_succ'] at h1
  have h3 : 1 ≤ (w + δ).choose δ := Nat.choose_pos (by omega)
  omega

theorem j_le (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) : top δ a - δ ≤ w := by
  have := top_le_of_le w δ a ha; omega

theorem j_lt_of_rem_ne_zero (w δ a : ℕ) (ha : a ≤ (w + δ).choose (δ + 1)) (hr : rem δ a ≠ 0) :
    top δ a - δ < w := by
  have hj := j_le w δ a ha
  rcases hj.lt_or_eq with h | h
  · exact h
  · exfalso
    have htop : top δ a = w + δ := by have := d_le_top δ a; omega
    have := rem_add_choose δ a
    rw [htop] at this
    omega

theorem rem_le_card (δ a : ℕ) (hj : top δ a - δ + 1 ≤ n + 1) :
    rem δ a ≤ (MonW n (top δ a - δ + 1) δ).card := by
  rw [card_MonW n _ _ hj, show top δ a - δ + 1 + δ - 1 = top δ a by have := d_le_top δ a; omega]
  exact (rem_lt δ a).le

theorem BW_subset : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → BW n d a ⊆ MonW n w d
  | 0, w, a, hw, ha => by
      simp only [BW]
      split_ifs
      · exact Finset.empty_subset _
      · rw [MonW_zero_right]
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ]
      have hj := j_le w δ a ha
      refine Finset.union_subset (MonW_mono n hj _) ?_
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty]; exact Finset.empty_subset _
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have ih := BW_subset δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        refine (shift_mono n _ ih).trans ?_
        refine subset_trans ?_ (MonW_mono n (show top δ a - δ + 1 ≤ w by omega) (δ + 1))
        rw [MonW_succ n (show top δ a - δ < n + 1 by omega) δ]
        exact Finset.subset_union_right

theorem card_BW : ∀ (d w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w d).card → (BW n d a).card = a
  | 0, w, a, hw, ha => by
      rw [MonW_zero_right, Finset.card_singleton] at ha
      simp only [BW]
      split_ifs with h
      · simp [h]
      · simp; omega
  | δ + 1, w, a, hw, ha => by
      rw [card_MonW_succ_eq n w δ hw] at ha
      rw [BW_succ, Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _)]
      have hj := j_le w δ a ha
      rw [card_MonW_succ_eq n _ δ (hj.trans hw), top_sub_add]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.card_empty]
        have := rem_add_choose δ a; omega
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        rw [card_shift n (by omega), card_BW δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]
        have := rem_add_choose δ a; omega

noncomputable def Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e + 1)).filter (fun u => ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B)

theorem mem_Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ Bplus n w e B ↔
      u ∈ MonW n w (e + 1) ∧ ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B := by
  simp [Bplus]

theorem Bplus_empty (w e : ℕ) : Bplus n w e (∅ : Finset (Fin (n + 1) →₀ ℕ)) = ∅ := by
  ext u
  simp only [mem_Bplus, Finset.notMem_empty, imp_false, not_le, Nat.lt_one_iff, iff_false, not_and,
    not_forall]
  intro hu
  rw [mem_MonW] at hu
  obtain ⟨i, hi⟩ := exists_one_le_of_degree_ne_zero n u (by omega)
  exact ⟨i, by omega⟩

theorem Bplus_MonW (w j δ : ℕ) (hjw : j ≤ w) :
    Bplus n w (δ + 1) (MonW n j (δ + 1)) = MonW n j (δ + 2) := by
  ext u
  rw [mem_Bplus, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩
    refine ⟨hdeg, fun i hi => ?_⟩
    by_contra hui
    obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
    have := ((mem_MonW n _ _ _).1 (hdiv i' hi')).2 i hi
    omega
  · rintro ⟨hdeg, hsupp⟩
    refine ⟨⟨hdeg, fun i hi => hsupp i (hjw.trans hi)⟩, fun i hi => ?_⟩
    rw [mem_MonW]
    refine ⟨by have := degree_sub_single n u i hi; omega, fun k hk => ?_⟩
    simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]

theorem Bplus_union_shift (w j δ : ℕ) (hj : j < n + 1) (hjw : j + 1 ≤ w)
    (B' : Finset (Fin (n + 1) →₀ ℕ)) (hB' : B' ⊆ MonW n (j + 1) δ) :
    Bplus n w (δ + 1) (MonW n j (δ + 1) ∪ shift n j B') =
      MonW n j (δ + 2) ∪ shift n j (Bplus n (j + 1) δ B') := by

  have hB : MonW n j (δ + 1) ∪ shift n j B' ⊆ MonW n (j + 1) (δ + 1) := by
    refine Finset.union_subset (MonW_mono n (Nat.le_succ j) _) ?_
    rw [MonW_succ n hj δ]
    exact (shift_mono n j hB').trans Finset.subset_union_right
  have hvar : var n j hj = Finsupp.single ⟨j, hj⟩ 1 := rfl
  ext u
  rw [mem_Bplus, Finset.mem_union, mem_shift_iff n hj, mem_Bplus, mem_MonW, mem_MonW, mem_MonW]
  constructor
  · rintro ⟨⟨hdeg, hsupp⟩, hdiv⟩

    have hsupp' : ∀ i : Fin (n + 1), j < (i : ℕ) → u i = 0 := by
      intro i hi
      by_contra hui
      obtain ⟨i', hi', h1⟩ := exists_sub_single_pos n u i (by omega) (by omega)
      have := ((mem_MonW n _ _ _).1 (hB (hdiv i' hi'))).2 i (by omega)
      omega
    by_cases huj : u ⟨j, hj⟩ = 0
    · refine Or.inl ⟨hdeg, fun i hi => ?_⟩
      rcases hi.eq_or_lt with hij | hij
      · have : i = ⟨j, hj⟩ := Fin.ext hij.symm
        rw [this]; exact huj
      · exact hsupp' i hij
    · refine Or.inr ⟨by omega, ⟨?_, fun i hi => ?_⟩, fun l hl => ?_⟩
      · have := degree_sub_var n hj u (by omega); omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp' i (by omega), Nat.zero_sub]
      ·
        have hul : 1 ≤ u l := by
          have : (u - var n j hj) l ≤ u l := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
          omega
        have hv := hdiv l hul
        rw [Finset.mem_union, mem_shift_iff n hj] at hv
        rcases hv with hv | ⟨-, hv⟩
        · exfalso
          have h0 := ((mem_MonW n _ _ _).1 hv).2 ⟨j, hj⟩ le_rfl
          by_cases hlj : l = ⟨j, hj⟩
          · subst hlj
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same, var] at h0 hl
            omega
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hlj] at h0
            omega
        · have : u - var n j hj - Finsupp.single l 1 = u - Finsupp.single l 1 - var n j hj := by
            ext k
            simp only [Finsupp.coe_tsub, Pi.sub_apply]
            omega
          rw [this]; exact hv
  · rintro (⟨hdeg, hsupp⟩ | ⟨h1, ⟨hdeg, hsupp⟩, hdiv⟩)
    ·
      refine ⟨⟨hdeg, fun i hi => hsupp i (by omega)⟩, fun i hi => ?_⟩
      refine Finset.mem_union_left _ ((mem_MonW n _ _ _).2 ⟨?_, fun k hk => ?_⟩)
      · have := degree_sub_single n u i hi; omega
      · simp only [Finsupp.coe_tsub, Pi.sub_apply, hsupp k hk, Nat.zero_sub]
    ·
      have hu : u - var n j hj + var n j hj = u := sub_var_add_var n hj u h1
      refine ⟨⟨?_, fun i hi => ?_⟩, fun i hi => ?_⟩
      · have := degree_sub_var n hj u h1; omega
      · have h0 := hsupp i (by omega)
        simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply] at h0
        have hij : (i : ℕ) ≠ j := by omega
        simp only [hij, if_false] at h0
        omega
      · rw [Finset.mem_union, mem_shift_iff n hj]
        by_cases hij : i = ⟨j, hj⟩
        ·
          subst hij
          rw [← hvar]
          by_cases hujj : (u - var n j hj) ⟨j, hj⟩ = 0
          · left
            rw [mem_MonW]
            refine ⟨hdeg, fun k hk => ?_⟩
            rcases hk.eq_or_lt with hkj | hkj
            · have : k = ⟨j, hj⟩ := Fin.ext hkj.symm
              rw [this]; exact hujj
            · exact hsupp k hkj
          · right
            have := hdiv ⟨j, hj⟩ (by omega)
            rw [← hvar] at this
            refine ⟨?_, this⟩
            simp only [Finsupp.coe_tsub, Pi.sub_apply] at hujj ⊢
            omega
        · right
          have hii : 1 ≤ (u - var n j hj) i := by
            simp only [Finsupp.coe_tsub, Pi.sub_apply, var_apply]
            have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
            simp only [this, if_false]; omega
          have hv := hdiv i hii
          refine ⟨?_, ?_⟩
          · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_neg hij]; omega
          · have : u - Finsupp.single i 1 - var n j hj = u - var n j hj - Finsupp.single i 1 := by
              ext k
              simp only [Finsupp.coe_tsub, Pi.sub_apply]
              omega
            rw [this]; exact hv

theorem card_Bplus_BW : ∀ (δ w a : ℕ), w ≤ n + 1 → a ≤ (MonW n w (δ + 1)).card →
    (Bplus n w (δ + 1) (BW n (δ + 1) a)).card = Nat.macaulayPow (δ + 1) a := by
  intro δ
  induction δ with
  | zero =>
      intro w a hw ha
      rw [card_MonW_succ_eq n w 0 hw] at ha
      have hj := j_le w 0 a ha
      rw [BW_succ, rem_zero_left, BW_zero_right, shift_empty, Finset.union_empty,
        Bplus_MonW n w _ 0 hj, card_MonW n _ _ (hj.trans hw), macaulayPow_succ, macaulayPow_zero,
        Nat.sub_zero, show top 0 a + (0 + 2) - 1 = top 0 a + 1 by omega]
      simp
  | succ δ' ih =>
      intro w a hw ha
      set δ := δ' + 1 with hδ
      rw [card_MonW_succ_eq n w δ hw] at ha
      have hj := j_le w δ a ha
      rw [BW_succ, macaulayPow_succ]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.union_empty, Bplus_MonW n w _ δ hj,
          card_MonW n _ _ (hj.trans hw), macaulayPow_zero_right,
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega]
        simp
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hjn : top δ a - δ < n + 1 := by omega
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have hB' := BW_subset n δ (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)
        rw [Bplus_union_shift n w _ δ hjn (by omega) _ hB',
          Finset.card_union_of_disjoint (disjoint_MonW_shift n _ _ _), card_shift n hjn,
          card_MonW n _ _ (hj.trans hw),
          show top δ a - δ + (δ + 2) - 1 = top δ a + 1 by have := d_le_top δ a; omega,
          ih (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]

end Grunbaum2003.MacaulayCompressed
-- END MacaulayCompressedBW.lean

-- BEGIN MacaulayCompressedShadow.lean
set_option autoImplicit false

namespace Grunbaum2003.MacaulayCompressed
open MacaulayGrowth

/-- Raising a Macaulay expansion raises its greedy top index by one. -/
theorem top_macaulayPow (d a : ℕ) :
    top (d + 1) (Nat.macaulayPow (d + 1) a) = top d a + 1 := by
  apply top_eq_of
  · change (top d a + 1).choose (d + 2) ≤ Nat.macaulayPow (d + 1) a
    rw [macaulayPow_succ]
    omega
  · have htail := macaulayPow_lt_choose d (top d a) (rem d a) (rem_lt d a)
    change Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 2)
    rw [macaulayPow_succ, Nat.choose_succ_succ' (top d a + 1) (d + 1)]
    exact (Nat.add_lt_add_left htail ((top d a + 1).choose (d + 2))).trans_eq
      (Nat.add_comm _ _)

/-- The raised expansion has the raised old remainder as its remainder. -/
theorem rem_macaulayPow (d a : ℕ) :
    rem (d + 1) (Nat.macaulayPow (d + 1) a) = Nat.macaulayPow d (rem d a) := by
  change Nat.macaulayPow (d + 1) a -
    (top (d + 1) (Nat.macaulayPow (d + 1) a)).choose (d + 2) =
      Nat.macaulayPow d (rem d a)
  rw [top_macaulayPow, macaulayPow_succ]
  omega

theorem BW_macaulayPow_succ (n d a : ℕ) :
    BW n (d + 2) (Nat.macaulayPow (d + 1) a) =
      MonW n (top d a - d) (d + 2) ∪
        shift n (top d a - d) (BW n (d + 1) (Nat.macaulayPow d (rem d a))) := by
  rw [BW_succ, top_macaulayPow, rem_macaulayPow,
    show top d a + 1 - (d + 1) = top d a - d by omega]

/-- The admissible next-degree monomials are the next compressed segment,
as a literal equality of finite sets, not merely an equality of cardinalities. -/
theorem Bplus_BW (n : ℕ) : ∀ (δ w a : ℕ), w ≤ n + 1 →
    a ≤ (MonW n w (δ + 1)).card →
    Bplus n w (δ + 1) (BW n (δ + 1) a) =
      BW n (δ + 2) (Nat.macaulayPow (δ + 1) a) := by
  intro δ
  induction δ with
  | zero =>
      intro w a hw ha
      rw [card_MonW_succ_eq n w 0 hw] at ha
      have hj := j_le w 0 a ha
      rw [BW_macaulayPow_succ, BW_succ, rem_zero_left, BW_zero_right,
        shift_empty, Finset.union_empty, Bplus_MonW n w _ 0 hj,
        macaulayPow_zero, BW_zero_right, shift_empty, Finset.union_empty]
  | succ δ' ih =>
      intro w a hw ha
      set δ := δ' + 1 with hδ
      rw [card_MonW_succ_eq n w δ hw] at ha
      have hj := j_le w δ a ha
      rw [BW_macaulayPow_succ, BW_succ]
      by_cases hr : rem δ a = 0
      · rw [hr, BW_zero_right, shift_empty, Finset.union_empty,
          Bplus_MonW n w _ δ hj, macaulayPow_zero_right,
          BW_zero_right, shift_empty, Finset.union_empty]
      · have hjw := j_lt_of_rem_ne_zero w δ a ha hr
        have hjn : top δ a - δ < n + 1 := by omega
        have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
        have hB' := BW_subset n δ (top δ a - δ + 1) (rem δ a)
          hj1 (rem_le_card n δ a hj1)
        rw [Bplus_union_shift n w _ δ hjn (by omega) _ hB',
          ih (top δ a - δ + 1) (rem δ a) hj1 (rem_le_card n δ a hj1)]

end Grunbaum2003.MacaulayCompressed
-- END MacaulayCompressedShadow.lean

-- BEGIN MacaulayCompressedColex.lean
set_option autoImplicit false

namespace Grunbaum2003.MacaulayCompressed
open MacaulayGrowth

/-- Compare exponent vectors at the largest variable where they differ. -/
def colexLT {s : ℕ} (u v : Fin s →₀ ℕ) : Prop :=
  ∃ i, u i < v i ∧ ∀ j, i < j → u j = v j

theorem colexLT_irrefl {s : ℕ} (u : Fin s →₀ ℕ) : ¬ colexLT u u := by
  rintro ⟨i, hi, _⟩
  exact (lt_irrefl (u i)) hi

theorem colexLT_trichotomy {s : ℕ} (u v : Fin s →₀ ℕ) :
    u = v ∨ colexLT u v ∨ colexLT v u := by
  classical
  by_cases huv : u = v
  · exact Or.inl huv
  · right
    let D : Finset (Fin s) := Finset.univ.filter (fun i => u i ≠ v i)
    have hD : D.Nonempty := by
      by_contra h
      apply huv
      ext i
      by_contra hi
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let r := D.max' hD
    have hr : u r ≠ v r := (Finset.mem_filter.mp (D.max'_mem hD)).2
    have heq : ∀ j, r < j → u j = v j := by
      intro j hj
      by_contra hne
      have hjD : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩
      have hle : j ≤ r := D.le_max' j hjD
      exact (not_lt_of_ge hle) hj
    rcases lt_or_gt_of_ne hr with hlt | hlt
    · exact Or.inl ⟨r, hlt, heq⟩
    · exact Or.inr ⟨r, hlt, fun j hj => (heq j hj).symm⟩

theorem colexLT_support_bound {s w : ℕ} {u v : Fin s →₀ ℕ}
    (h : colexLT u v) (hv : ∀ i : Fin s, w ≤ i.val → v i = 0) :
    ∀ i : Fin s, w ≤ i.val → u i = 0 := by
  obtain ⟨r, hr, heq⟩ := h
  have hrw : r.val < w := by
    by_contra hge
    have hz := hv r (by omega)
    omega
  intro i hi
  have hri : r < i := by change r.val < i.val; omega
  rw [heq i hri, hv i hi]

theorem colexLT_sub_single {s : ℕ} {u v : Fin s →₀ ℕ} (h : colexLT u v)
    (j : Fin s) (hu : 1 ≤ u j) (hv : 1 ≤ v j) :
    colexLT (u - Finsupp.single j 1) (v - Finsupp.single j 1) := by
  obtain ⟨r, hr, heq⟩ := h
  refine ⟨r, ?_, ?_⟩
  · by_cases hjr : j = r
    · subst j
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      omega
    · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
        if_neg hjr, Nat.sub_zero]
      exact hr
  · intro i hi
    simp only [Finsupp.coe_tsub, Pi.sub_apply, heq i hi]

/-- Every `BW` set is an initial segment among monomials of its degree. -/
theorem BW_initial (n : ℕ) : ∀ (d w a : ℕ), w ≤ n + 1 →
    a ≤ (MonW n w d).card →
    ∀ v ∈ BW n d a, ∀ u : Fin (n + 1) →₀ ℕ,
      u.degree = d → colexLT u v → u ∈ BW n d a
  | 0, w, a, hw, ha, v, hv, u, hu, huv => by
      have hvdeg := ((mem_MonW n w 0 v).mp ((BW_subset n 0 w a hw ha) hv)).1
      have hu0 : u = 0 := by simpa only [Finsupp.degree_eq_zero_iff] using hu
      have hv0 : v = 0 := by simpa only [Finsupp.degree_eq_zero_iff] using hvdeg
      rw [hu0, hv0] at huv
      exact (colexLT_irrefl 0 huv).elim
  | δ + 1, w, a, hw, ha, v, hv, u, hu, huv => by
      have hac := ha
      rw [card_MonW_succ_eq n w δ hw] at hac
      have hj := j_le w δ a hac
      rw [BW_succ, Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · left
        exact (mem_MonW n _ _ _).mpr
          ⟨hu, colexLT_support_bound huv ((mem_MonW n _ _ _).mp hv).2⟩
      · by_cases hr : rem δ a = 0
        · rw [hr, BW_zero_right, shift_empty] at hv
          exact (Finset.notMem_empty _ hv).elim
        · have hjw := j_lt_of_rem_ne_zero w δ a hac hr
          have hjn : top δ a - δ < n + 1 := by omega
          have hj1 : top δ a - δ + 1 ≤ n + 1 := by omega
          have hB' := BW_subset n δ (top δ a - δ + 1) (rem δ a)
            hj1 (rem_le_card n δ a hj1)
          have hvMon : v ∈ MonW n (top δ a - δ + 1) (δ + 1) := by
            rw [MonW_succ n hjn δ]
            exact Finset.mem_union_right _ ((shift_mono n _ hB') hv)
          have huSupp := colexLT_support_bound huv ((mem_MonW n _ _ _).mp hvMon).2
          by_cases huj : u ⟨top δ a - δ, hjn⟩ = 0
          · left
            refine (mem_MonW n _ _ _).mpr ⟨hu, ?_⟩
            intro i hi
            rcases hi.eq_or_lt with heq | hlt
            · have hieq : i = ⟨top δ a - δ, hjn⟩ := Fin.ext heq.symm
              rw [hieq]
              exact huj
            · exact huSupp i hlt
          · right
            rw [mem_shift_iff n hjn] at hv ⊢
            have hujpos : 1 ≤ u ⟨top δ a - δ, hjn⟩ := by omega
            refine ⟨hujpos, ?_⟩
            apply BW_initial n δ (top δ a - δ + 1) (rem δ a) hj1
              (rem_le_card n δ a hj1) _ hv.2
            · have hdeg := degree_sub_var n hjn u hujpos
              omega
            · exact colexLT_sub_single huv _ hujpos hv.1

/-- Compressed sets in one degree are nested as their prescribed sizes grow. -/
theorem BW_mono (n d w a b : ℕ) (hw : w ≤ n + 1)
    (hb : b ≤ (MonW n w d).card) (hab : a ≤ b) : BW n d a ⊆ BW n d b := by
  classical
  have ha := hab.trans hb
  intro u hu
  by_contra hub
  have huDeg := ((mem_MonW n w d u).mp ((BW_subset n d w a hw ha) hu)).1
  have hba : BW n d b ⊆ BW n d a := by
    intro v hv
    have hvDeg := ((mem_MonW n w d v).mp ((BW_subset n d w b hw hb) hv)).1
    rcases colexLT_trichotomy v u with hEq | hvu | huv
    · exact hEq.symm ▸ hu
    · exact BW_initial n d w a hw ha u hu v hvDeg hvu
    · exact (hub (BW_initial n d w b hw hb v hv u huDeg huv)).elim
  have hEq : BW n d b = BW n d a := Finset.eq_of_subset_of_card_le hba (by
    rw [card_BW n d w a hw ha, card_BW n d w b hw hb]
    exact hab)
  exact hub (hEq.symm ▸ hu)

end Grunbaum2003.MacaulayCompressed
-- END MacaulayCompressedColex.lean

-- BEGIN MacaulayExpansionBridge.lean
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.MacaulayGrowth

/-- The greedy binomial expansion simultaneously computes the original value
and the sum obtained by lowering only the upper entries. -/
theorem exists_expansion : ∀ (k n : ℕ), 0 < k → 0 < n →
    ∃ (i : ℕ) (a : ℕ → ℕ),
      0 < i ∧ i ≤ k ∧ i ≤ a i ∧
      (∀ r s : ℕ, i ≤ r → r < s → s ≤ k → a r < a s) ∧
      a k = top (k - 1) n ∧
      n = ∑ r ∈ Finset.Icc i k, Nat.choose (a r) r ∧
      low k n = ∑ r ∈ Finset.Icc i k, Nat.choose (a r - 1) r
  | 0, _, hk, _ => by omega
  | k + 1, n, _, hn => by
      let T := top k n
      let R := rem k n
      have hT : k + 1 ≤ T := by
        have := d_lt_top_of_pos k n hn
        omega
      have hrepr : R + T.choose (k + 1) = n := rem_add_choose k n
      by_cases hR : R = 0
      · refine ⟨k + 1, fun _ => T, by omega, le_rfl, hT, ?_, ?_, ?_, ?_⟩
        · intro r s hr hrs hs
          omega
        · simp [T]
        · simpa [hR] using hrepr.symm
        · have hR' : rem k n = 0 := hR
          simp only [low_succ, hR', low_zero_right, add_zero,
            Finset.Icc_self, Finset.sum_singleton]
          rfl
      · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
        have hkpos : 0 < k := by
          by_contra! hk
          have hk0 : k = 0 := by omega
          subst hk0
          exact hR (rem_zero_left n)
        obtain ⟨i, a, hi, hik, hai, hmono, hak, hsum, hlow⟩ :=
          exists_expansion k R hkpos hRpos
        let b : ℕ → ℕ := fun r => if r = k + 1 then T else a r
        have hb (r : ℕ) (hr : r ≤ k) : b r = a r := by simp [b, show r ≠ k + 1 by omega]
        have hbtop : b (k + 1) = T := by simp [b]
        have hatop : a k < T := by
          rw [hak]
          apply top_lt_of_lt_choose (k - 1) R T
          simpa only [Nat.sub_add_cancel hkpos] using rem_lt k n
        have halast (r : ℕ) (hir : i ≤ r) (hrk : r ≤ k) : a r ≤ a k := by
          rcases hrk.eq_or_lt with rfl | hlt
          · exact le_rfl
          · exact (hmono r k hir hlt le_rfl).le
        refine ⟨i, b, hi, by omega, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [hb i hik] using hai
        · intro r s hir hrs hsk
          have hrk : r ≤ k := by omega
          rw [hb r hrk]
          by_cases hs : s = k + 1
          · rw [hs, hbtop]
            exact (halast r hir hrk).trans_lt hatop
          · rw [hb s (by omega)]
            exact hmono r s hir hrs (by omega)
        · simpa [T] using hbtop
        · rw [Finset.sum_Icc_succ_top (by omega : i ≤ k + 1)]
          have hloweq : (∑ r ∈ Finset.Icc i k, (b r).choose r) =
              ∑ r ∈ Finset.Icc i k, (a r).choose r := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hb r (Finset.mem_Icc.mp hr).2]
          rw [hloweq, hbtop, ← hsum]
          exact hrepr.symm
        · rw [Finset.sum_Icc_succ_top (by omega : i ≤ k + 1)]
          have hloweq : (∑ r ∈ Finset.Icc i k, (b r - 1).choose r) =
              ∑ r ∈ Finset.Icc i k, (a r - 1).choose r := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hb r (Finset.mem_Icc.mp hr).2]
          rw [hloweq, hbtop, ← hlow, low_succ]
          exact Nat.add_comm _ _

/-- Lowering both entries in a binomial expansion gives the complementary part
of Pascal's identity. -/
theorem expansion_boundary_add_low {k n i : ℕ} {a : ℕ → ℕ}
    (hi : 0 < i) (hik : i ≤ k) (hai : i ≤ a i)
    (hmono : ∀ r s : ℕ, i ≤ r → r < s → s ≤ k → a r < a s)
    (hsum : n = ∑ r ∈ Finset.Icc i k, Nat.choose (a r) r)
    (hlow : low k n = ∑ r ∈ Finset.Icc i k, Nat.choose (a r - 1) r) :
    (∑ r ∈ Finset.Icc i k, Nat.choose (a r - 1) (r - 1)) + low k n = n := by
  rw [hlow, ← Finset.sum_add_distrib, hsum]
  apply Finset.sum_congr rfl
  intro r hr
  have hir := (Finset.mem_Icc.mp hr).1
  have hrk := (Finset.mem_Icc.mp hr).2
  have hrpos : 0 < r := by omega
  have harpos : 0 < a r := by
    rcases hir.eq_or_lt with heq | hlt
    · rw [← heq]
      omega
    · have := hmono i r le_rfl hlt hrk
      omega
  have hp := Nat.choose_succ_succ' (a r - 1) (r - 1)
  rw [Nat.sub_add_cancel harpos, Nat.sub_add_cancel hrpos] at hp
  exact hp.symm

/-- Standard forward Macaulay growth supplies the exact backward-boundary
witnesses used by the canonical Grünbaum M-sequence definition. -/
theorem isMSequence_of_macaulay_growth (m : ℕ) (g : ℕ → ℕ)
    (hg0 : g 0 = 1)
    (hg : ∀ k : ℕ, 0 < k → k < m → g (k + 1) ≤ Nat.macaulayPow k (g k)) :
    IsMSequence m g := by
  refine ⟨hg0, ?_⟩
  intro k hk hkm
  by_cases hz : g k = 0
  · exact Or.inl hz
  · right
    obtain ⟨i, a, hi, hik, hai, hmono, _, hsum, hlow⟩ :=
      exists_expansion k (g k) hk (Nat.pos_of_ne_zero hz)
    refine ⟨i, a, hi, hik, hai, hmono, hsum, ?_⟩
    have hboundary := expansion_boundary_add_low hi hik hai hmono hsum hlow
    by_cases hk1 : k = 1
    · subst k
      have hi1 : i = 1 := by omega
      subst i
      simp [hg0]
    · have hprev : 0 < k - 1 := by omega
      have hstep := hg (k - 1) hprev (by omega)
      rw [Nat.sub_add_cancel hk] at hstep
      have hineq := le_add_low (k - 1) (g k) (g (k - 1)) hstep
      rw [Nat.sub_add_cancel hk] at hineq
      omega

end Grunbaum2003.MacaulayGrowth
-- END MacaulayExpansionBridge.lean

-- BEGIN MacaulayConverse.lean
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.MacaulayGrowth

/-- Strict upper entries starting at `a i ≥ i` dominate their lower entries. -/
theorem expansion_entry_ge {i k : ℕ} {a : ℕ → ℕ} (hai : i ≤ a i)
    (hmono : ∀ r s : ℕ, i ≤ r → r < s → s ≤ k → a r < a s) :
    ∀ r : ℕ, i ≤ r → r ≤ k → r ≤ a r := by
  intro r hir
  induction r, hir using Nat.le_induction with
  | base => exact fun _ => hai
  | succ r hir ih =>
    intro hrk
    have hprev := ih (by omega)
    have hnext := hmono r (r + 1) hir (by omega) hrk
    omega

/-- Any admissible strict binomial expansion lies below the next possible top
term. This proves that its top entry is the greedy one. -/
theorem expansion_sum_lt_choose : ∀ (k i : ℕ) (a : ℕ → ℕ),
    0 < i → i ≤ k → i ≤ a i →
    (∀ r s : ℕ, i ≤ r → r < s → s ≤ k → a r < a s) →
    (∑ r ∈ Finset.Icc i k, Nat.choose (a r) r) < Nat.choose (a k + 1) k
  | 0, i, _, hi, hik, _, _ => by omega
  | k + 1, i, a, hi, hik, hai, hmono => by
      have htopge : k + 1 ≤ a (k + 1) := expansion_entry_ge hai hmono (k + 1) hik le_rfl
      have hpos : 0 < (a (k + 1)).choose k := Nat.choose_pos (by omega)
      by_cases heq : i = k + 1
      · subst i
        simp only [Finset.Icc_self, Finset.sum_singleton]
        rw [Nat.choose_succ_succ']
        omega
      · have hik' : i ≤ k := by omega
        have hrest := expansion_sum_lt_choose k i a hi hik' hai
          (fun r s hir hrs hsk => hmono r s hir hrs (by omega))
        have hlast := hmono k (k + 1) hik' (by omega) le_rfl
        have hchoose : (a k + 1).choose k ≤ (a (k + 1)).choose k :=
          Nat.choose_le_choose k (by omega)
        rw [Finset.sum_Icc_succ_top (by omega : i ≤ k + 1), Nat.choose_succ_succ']
        omega

/-- An arbitrary admissible strict expansion has the canonical greedy top. -/
theorem expansion_top_eq {k i n : ℕ} {a : ℕ → ℕ}
    (hi : 0 < i) (hik : i ≤ k) (hai : i ≤ a i)
    (hmono : ∀ r s : ℕ, i ≤ r → r < s → s ≤ k → a r < a s)
    (hsum : n = ∑ r ∈ Finset.Icc i k, Nat.choose (a r) r) :
    top (k - 1) n = a k := by
  have hk : 0 < k := by omega
  apply top_eq_of
  · rw [Nat.sub_add_cancel hk, hsum]
    exact Finset.single_le_sum (fun r hr => Nat.zero_le ((a r).choose r))
      (by simp [hik])
  · rw [Nat.sub_add_cancel hk, hsum]
    exact expansion_sum_lt_choose k i a hi hik hai hmono

/-- A single admissible binomial term grows by raising both entries. -/
theorem macaulayPow_choose {k T : ℕ} (hk : 0 < k) (hT : k ≤ T) :
    Nat.macaulayPow k (T.choose k) = (T + 1).choose (k + 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have htop : top r (T.choose (r + 1)) = T := by
    apply top_eq_of
    · exact le_rfl
    · rw [Nat.choose_succ_succ']
      have hpos : 0 < T.choose r := Nat.choose_pos (by omega)
      omega
  have hrem : rem r (T.choose (r + 1)) = 0 := by simp [rem, htop]
  rw [macaulayPow_succ, htop, hrem, macaulayPow_zero_right, add_zero]

/-- The backward boundary of any admissible degree-`k+1` expansion has enough
forward Macaulay growth to recover the original number. A possible degree-zero
boundary term is handled by the Pascal carry case. -/
theorem expansion_le_macaulayPow_boundary : ∀ (k i : ℕ) (a : ℕ → ℕ),
    0 < k → 0 < i → i ≤ k + 1 → i ≤ a i →
    (∀ r s : ℕ, i ≤ r → r < s → s ≤ k + 1 → a r < a s) →
    (∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r) ≤
      Nat.macaulayPow k (∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r - 1) (r - 1))
  | 0, _, _, hk, _, _, _, _ => by omega
  | k + 1, i, a, _, hi, hik, hai, hmono => by
      let T := a (k + 2)
      have hT : k + 2 ≤ T := expansion_entry_ge hai hmono (k + 2) hik le_rfl
      by_cases heq : i = k + 2
      · subst i
        simp only [Finset.Icc_self, Finset.sum_singleton]
        change T.choose (k + 2) ≤ Nat.macaulayPow (k + 1) ((T - 1).choose (k + 1))
        rw [macaulayPow_choose (by omega) (by omega), Nat.sub_add_cancel (by omega : 1 ≤ T)]
      · have hik' : i ≤ k + 1 := by omega
        let R := ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r) r
        let B := ∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r - 1) (r - 1)
        have hNsplit : (∑ r ∈ Finset.Icc i (k + 2), Nat.choose (a r) r) =
            R + T.choose (k + 2) := by
          rw [Finset.sum_Icc_succ_top (by omega : i ≤ k + 2)]
        have hBsplit : (∑ r ∈ Finset.Icc i (k + 2), Nat.choose (a r - 1) (r - 1)) =
            B + (T - 1).choose (k + 1) := by
          rw [Finset.sum_Icc_succ_top (by omega : i ≤ k + 2)]
          simp only [Nat.add_sub_cancel]
          rfl
        rw [hNsplit, hBsplit]
        by_cases hsmall : B < (T - 1).choose k
        · have hkpos : 0 < k := by
            by_contra! hzero
            have hkzero : k = 0 := by omega
            subst k
            have hi1 : i = 1 := by omega
            subst i
            simp [B] at hsmall
          have htop : top k (B + (T - 1).choose (k + 1)) = T - 1 := by
            apply top_eq_of
            · omega
            · rw [Nat.choose_succ_succ']
              omega
          have hrem : rem k (B + (T - 1).choose (k + 1)) = B := by simp [rem, htop]
          rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (by omega : 1 ≤ T)]
          have hrest : R ≤ Nat.macaulayPow k B :=
            expansion_le_macaulayPow_boundary k i a hkpos hi hik' hai
              (fun r s hir hrs hsk => hmono r s hir hrs (by omega))
          omega
        · have hcarry : T.choose (k + 1) ≤ B + (T - 1).choose (k + 1) := by
            have hp := Nat.choose_succ_succ' (T - 1) k
            rw [Nat.sub_add_cancel (by omega : 1 ≤ T)] at hp
            omega
          have hgrowth := macaulayPow_mono (k + 1) hcarry
          rw [macaulayPow_choose (by omega) (by omega : k + 1 ≤ T)] at hgrowth
          have hbound := expansion_sum_lt_choose (k + 2) i a hi hik hai hmono
          rw [hNsplit] at hbound
          exact hbound.le.trans hgrowth

/-- The canonical backward-boundary M-sequence condition implies standard
forward Macaulay growth, without a choice of binomial expansion. -/
theorem macaulay_growth_of_isMSequence (m : ℕ) (g : ℕ → ℕ) (hg : IsMSequence m g) :
    ∀ k : ℕ, 0 < k → k < m → g (k + 1) ≤ Nat.macaulayPow k (g k) := by
  intro k hk hkm
  rcases hg.2 (k + 1) (by omega) (by omega) with hz | ⟨i, a, hi, hik, hai, hmono, hsum, hboundary⟩
  · rw [hz]
    exact Nat.zero_le _
  · have hexp := expansion_le_macaulayPow_boundary k i a hk hi hik hai hmono
    rw [← hsum] at hexp
    have hbound : (∑ r ∈ Finset.Icc i (k + 1), Nat.choose (a r - 1) (r - 1)) ≤ g k := by
      simpa using hboundary
    exact hexp.trans (macaulayPow_mono k hbound)

/-- The canonical relational M-sequence definition and standard forward growth
are equivalent on their entire finite range. -/
theorem isMSequence_iff_macaulay_growth (m : ℕ) (g : ℕ → ℕ) :
    IsMSequence m g ↔ g 0 = 1 ∧
      ∀ k : ℕ, 0 < k → k < m → g (k + 1) ≤ Nat.macaulayPow k (g k) := by
  constructor
  · intro hg
    exact ⟨hg.1, macaulay_growth_of_isMSequence m g hg⟩
  · rintro ⟨hg0, hg⟩
    exact isMSequence_of_macaulay_growth m g hg0 hg

end Grunbaum2003.MacaulayGrowth
-- END MacaulayConverse.lean

-- BEGIN MacaulaySequenceBounds.lean
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003.MacaulayGrowth

/-- With a positive first entry, every entry fits in the corresponding degree
of the polynomial ring on `g 1` variables. -/
theorem isMSequence_entry_le_choose (m : ℕ) (g : ℕ → ℕ)
    (hg : IsMSequence m g) (hg1 : 0 < g 1) :
    ∀ k : ℕ, 0 < k → k ≤ m → g k ≤ (g 1 + k - 1).choose k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk hkm
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hprev := ih hkpos (by omega)
      have hstep := macaulay_growth_of_isMSequence m g hg k hkpos (by omega)
      calc
        g (k + 1) ≤ Nat.macaulayPow k (g k) := hstep
        _ ≤ Nat.macaulayPow k ((g 1 + k - 1).choose k) := macaulayPow_mono k hprev
        _ = (g 1 + (k + 1) - 1).choose (k + 1) := by
          rw [macaulayPow_choose hkpos (by omega)]
          congr 1
          omega

/-- A zero positive-degree entry forces all subsequent entries in the
specified range to vanish. -/
theorem isMSequence_zero_tail (m : ℕ) (g : ℕ → ℕ) (hg : IsMSequence m g)
    {k : ℕ} (hk : 0 < k) (hgk : g k = 0) :
    ∀ r : ℕ, k ≤ r → r ≤ m → g r = 0 := by
  intro r hkr
  induction r, hkr using Nat.le_induction with
  | base => exact fun _ => hgk
  | succ r hkr ih =>
    intro hrm
    have hz := ih (by omega)
    have hstep := macaulay_growth_of_isMSequence m g hg r (by omega) (by omega)
    rw [hz, macaulayPow_zero_right] at hstep
    exact Nat.eq_zero_of_le_zero hstep

end Grunbaum2003.MacaulayGrowth
-- END MacaulaySequenceBounds.lean

-- BEGIN MacaulayCompressedIdeal.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.MacaulayCompressed
open MacaulayGrowth

theorem isMSequence_capacity (n m : ℕ) (g : ℕ → ℕ)
    (hg : IsMSequence m g) (hn : g 1 ≤ n + 1) :
    ∀ k ≤ m, g k ≤ (MonW n (n + 1) k).card := by
  intro k hkm
  by_cases hk : k = 0
  · subst k
    rw [hg.1, MonW_zero_right, Finset.card_singleton]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    by_cases hg1 : g 1 = 0
    · have hz := isMSequence_zero_tail m g hg (k := 1) (by omega) hg1 k
        (by omega) hkm
      rw [hz]
      exact Nat.zero_le _
    · have hbound := isMSequence_entry_le_choose m g hg (by omega) k hkpos hkm
      rw [card_MonW n (n + 1) k le_rfl]
      exact hbound.trans (Nat.choose_le_choose k (by omega))

/-- The finite union of the prescribed compressed degree slices. -/
noncomputable def degreeUnion (n m : ℕ) (g : ℕ → ℕ) :
    Finset (Fin (n + 1) →₀ ℕ) :=
  (Finset.range (m + 1)).biUnion (fun k => BW n k (g k))

theorem mem_degreeUnion (n m : ℕ) (g : ℕ → ℕ)
    (hcap : ∀ k ≤ m, g k ≤ (MonW n (n + 1) k).card)
    (u : Fin (n + 1) →₀ ℕ) :
    u ∈ degreeUnion n m g ↔ u.degree ≤ m ∧ u ∈ BW n u.degree (g u.degree) := by
  constructor
  · intro hu
    obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hu
    have hkm : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hdeg := ((mem_MonW n (n + 1) k u).mp
      ((BW_subset n k (n + 1) (g k) le_rfl (hcap k hkm)) huk)).1
    exact ⟨by omega, hdeg.symm ▸ huk⟩
  · rintro ⟨hdeg, hu⟩
    exact Finset.mem_biUnion.mpr ⟨u.degree, Finset.mem_range.mpr (by omega), hu⟩

theorem degreeUnion_zero (n m : ℕ) (g : ℕ → ℕ) (hg0 : g 0 = 1) :
    (0 : Fin (n + 1) →₀ ℕ) ∈ degreeUnion n m g := by
  apply Finset.mem_biUnion.mpr
  refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  simp only [hg0, BW, Nat.one_ne_zero, if_false, Finset.mem_singleton]

theorem degreeUnion_slice (n m : ℕ) (g : ℕ → ℕ)
    (hcap : ∀ k ≤ m, g k ≤ (MonW n (n + 1) k).card)
    (k : ℕ) (hk : k ≤ m) :
    (degreeUnion n m g).filter (fun u => u.degree = k) = BW n k (g k) := by
  ext u
  rw [Finset.mem_filter, mem_degreeUnion n m g hcap u]
  constructor
  · rintro ⟨⟨_, hu⟩, hdeg⟩
    rwa [hdeg] at hu
  · intro hu
    have hdeg := ((mem_MonW n (n + 1) k u).mp
      ((BW_subset n k (n + 1) (g k) le_rfl (hcap k hk)) hu)).1
    exact ⟨⟨by omega, hdeg.symm ▸ hu⟩, hdeg⟩

theorem degreeUnion_sub_single (n m : ℕ) (g : ℕ → ℕ)
    (hg : IsMSequence m g) (hn : g 1 ≤ n + 1)
    (u : Fin (n + 1) →₀ ℕ) (hu : u ∈ degreeUnion n m g)
    (i : Fin (n + 1)) (hi : 1 ≤ u i) :
    u - Finsupp.single i 1 ∈ degreeUnion n m g := by
  have hcap := isMSequence_capacity n m g hg hn
  obtain ⟨hum, huBW⟩ := (mem_degreeUnion n m g hcap u).mp hu
  generalize hk : (u - Finsupp.single i 1).degree = k
  have hdeg : u.degree = k + 1 := by
    have h := degree_sub_single n u i hi
    omega
  cases k with
  | zero =>
      have hz : u - Finsupp.single i 1 = 0 := by
        simpa only [Finsupp.degree_eq_zero_iff] using hk
      rw [hz]
      exact degreeUnion_zero n m g hg.1
  | succ δ =>
      have hkM : δ + 1 ≤ m := by omega
      have hklt : δ + 1 < m := by omega
      have hgrowth := macaulay_growth_of_isMSequence m g hg (δ + 1) (by omega) hklt
      have hpowcap : Nat.macaulayPow (δ + 1) (g (δ + 1)) ≤
          (MonW n (n + 1) (δ + 2)).card := by
        rw [← card_Bplus_BW n δ (n + 1) (g (δ + 1)) le_rfl (hcap _ hkM)]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have huLarge := BW_mono n (δ + 2) (n + 1) (g (δ + 2))
        (Nat.macaulayPow (δ + 1) (g (δ + 1))) le_rfl hpowcap hgrowth
        (by simpa only [hdeg] using huBW)
      rw [← Bplus_BW n δ (n + 1) (g (δ + 1)) le_rfl (hcap _ hkM)] at huLarge
      have hdiv := ((mem_Bplus n (n + 1) (δ + 1) (BW n (δ + 1) (g (δ + 1))) u).mp huLarge).2 i hi
      apply (mem_degreeUnion n m g hcap _).mpr
      exact ⟨by omega, hk.symm ▸ hdiv⟩

theorem divisor_closed_of_sub_single (n : ℕ) (M : Finset (Fin (n + 1) →₀ ℕ))
    (hstep : ∀ u ∈ M, ∀ i, 1 ≤ u i → u - Finsupp.single i 1 ∈ M) :
    ∀ u ∈ M, ∀ v : Fin (n + 1) →₀ ℕ, v ≤ u → v ∈ M := by
  have main : ∀ d, ∀ u : Fin (n + 1) →₀ ℕ, u.degree = d →
      u ∈ M → ∀ v : Fin (n + 1) →₀ ℕ, v ≤ u → v ∈ M := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro u hud hu v hv
        by_cases hvu : v = u
        · exact hvu.symm ▸ hu
        · have hdiff : ∃ i, v i < u i := by
            by_contra h
            apply hvu
            ext i
            have hnlt : ¬ v i < u i := fun hi => h ⟨i, hi⟩
            exact le_antisymm (hv i) (Nat.le_of_not_gt hnlt)
          obtain ⟨i, hi⟩ := hdiff
          have hiu : 1 ≤ u i := by omega
          have hdeg := degree_sub_single n u i hiu
          have hvsub : v ≤ u - Finsupp.single i 1 := by
            intro j
            by_cases hij : i = j
            · subst j
              simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
              omega
            · simpa only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
                if_neg hij, Nat.sub_zero] using hv j
          exact ih _ (by omega) _ rfl (hstep u hu i hiu) v hvsub
  intro u hu v hv
  exact main u.degree u rfl hu v hv

/-- A finite M-sequence is realized by a finite compressed order ideal of
monomials. The arity bound only specifies that the ambient polynomial ring
has at least `g 1` variables. Only degrees `0` through `m` are used. -/
theorem exists_compressed_multicomplex (n m : ℕ) (g : ℕ → ℕ)
    (hg : IsMSequence m g) (hn : g 1 ≤ n + 1) :
    ∃ M : Finset (Fin (n + 1) →₀ ℕ),
      0 ∈ M ∧
      (∀ u ∈ M, u.degree ≤ m) ∧
      (∀ u ∈ M, ∀ v : Fin (n + 1) →₀ ℕ, v ≤ u → v ∈ M) ∧
      (∀ u ∈ M, ∀ v : Fin (n + 1) →₀ ℕ,
        v.degree = u.degree → colexLT v u → v ∈ M) ∧
      ∀ k ≤ m, (M.filter (fun u => u.degree = k)).card = g k := by
  let M := degreeUnion n m g
  have hcap := isMSequence_capacity n m g hg hn
  refine ⟨M, degreeUnion_zero n m g hg.1, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact ((mem_degreeUnion n m g hcap u).mp hu).1
  · exact divisor_closed_of_sub_single n M (degreeUnion_sub_single n m g hg hn)
  · intro u hu v hdeg hvu
    obtain ⟨hum, huBW⟩ := (mem_degreeUnion n m g hcap u).mp hu
    have hvBW := BW_initial n u.degree (n + 1) (g u.degree)
      le_rfl (hcap _ hum) u huBW v hdeg hvu
    exact (mem_degreeUnion n m g hcap v).mpr ⟨by omega, hdeg.symm ▸ hvBW⟩
  · intro k hk
    rw [degreeUnion_slice n m g hcap k hk, card_BW n k (n + 1) (g k) le_rfl (hcap k hk)]

end Grunbaum2003.MacaulayCompressed
-- END MacaulayCompressedIdeal.lean

-- BEGIN MacaulayCompressedWords.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- The exponent of variable `i` is the number of occurrences of positive
letter `i+1`; zero letters are padding. This literal count is defined on all
words, while the arity bound is imposed in the realization lemmas. -/
noncomputable def wordExponent {m : ℕ} (s : ℕ) (u : Fin m → ℕ) : Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i => (Finset.univ.filter (fun j => u j = i.val + 1)).card)

@[simp] theorem wordExponent_apply {m s : ℕ} (u : Fin m → ℕ) (i : Fin s) :
    wordExponent s u i = (Finset.univ.filter (fun j => u j = i.val + 1)).card := rfl

theorem lowerBlock_le {m : ℕ} (u : Fin m → ℕ) (r j : Fin m) :
    lowerBlock u r j ≤ u j := by
  simp only [lowerBlock]
  split_ifs <;> omega

theorem lowerBlock_monotone {m : ℕ} (u : Fin m → ℕ) (hu : Monotone u)
    (r : Fin m) : Monotone (lowerBlock u r) := by
  intro i j hij
  have hval := hu hij
  by_cases hi : i ≤ r ∧ u i = u r
  · by_cases hj : j ≤ r ∧ u j = u r
    · simp only [lowerBlock, if_pos hi, if_pos hj]
      omega
    · simp only [lowerBlock, if_pos hi, if_neg hj]
      omega
  · by_cases hj : j ≤ r ∧ u j = u r
    · have hir : i ≤ r := hij.trans hj.1
      have hne : u i ≠ u r := fun heq => hi ⟨hir, heq⟩
      simp only [lowerBlock, if_neg hi, if_pos hj]
      omega
    · simp only [lowerBlock, if_neg hi, if_neg hj]
      exact hval

theorem wordExponent_degree {m s : ℕ} (u : Fin m → ℕ) (hb : ∀ j, u j ≤ s) :
    (wordExponent s u).degree = (Finset.univ.filter (fun j => 0 < u j)).card := by
  rw [Finsupp.degree_eq_sum]
  simp only [wordExponent_apply]
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : u j = 0
  · simp only [hj, Nat.not_lt_zero, if_false]
    have hzero : ∀ i : Fin s, ¬ (0 : ℕ) = i.val + 1 := by intro i; omega
    simp only [hzero, if_false, Finset.sum_const_zero]
  · let i : Fin s := ⟨u j - 1, by have := hb j; omega⟩
    have hiff : ∀ k : Fin s, u j = k.val + 1 ↔ k = i := by
      intro k
      constructor
      · intro hk
        apply Fin.ext
        change k.val = u j - 1
        omega
      · intro hk
        subst k
        change u j = (u j - 1) + 1
        omega
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Nat.pos_of_ne_zero hj]

theorem wordExponent_lowerBlock_le_of_one {m s : ℕ} (u : Fin m → ℕ) (r : Fin m)
    (hr : u r = 1) : wordExponent s (lowerBlock u r) ≤ wordExponent s u := by
  intro i
  rw [wordExponent_apply, wordExponent_apply]
  apply Finset.card_le_card
  intro j hj
  have hval := (Finset.mem_filter.mp hj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ j, ?_⟩
  by_cases hchange : j ≤ r ∧ u j = u r
  · rw [lowerBlock, if_pos hchange, hchange.2, hr] at hval
    omega
  · simpa only [lowerBlock, if_neg hchange] using hval

theorem lowerBlock_fiber_lt {m : ℕ} (u : Fin m → ℕ) (r : Fin m) (hr : 0 < u r) :
    (Finset.univ.filter (fun j => lowerBlock u r j = u r)).card <
      (Finset.univ.filter (fun j => u j = u r)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    have hval := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j, ?_⟩
    by_cases hchange : j ≤ r ∧ u j = u r
    · rw [lowerBlock, if_pos hchange, hchange.2] at hval
      omega
    · simpa only [lowerBlock, if_neg hchange] using hval
  · intro heq
    have hrOld : r ∈ Finset.univ.filter (fun j => u j = u r) := by simp
    have hrNew := heq.symm ▸ hrOld
    have hval := (Finset.mem_filter.mp hrNew).2
    rw [lowerBlock, if_pos (show r ≤ r ∧ u r = u r from ⟨le_rfl, rfl⟩)] at hval
    omega

theorem lowerBlock_fiber_eq_of_gt {m : ℕ} (u : Fin m → ℕ) (r : Fin m)
    (k : ℕ) (hk : u r < k) :
    Finset.univ.filter (fun j => lowerBlock u r j = k) =
      Finset.univ.filter (fun j => u j = k) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hchange : j ≤ r ∧ u j = u r
  · rw [lowerBlock, if_pos hchange, hchange.2]
    omega
  · simp only [lowerBlock, if_neg hchange]

theorem wordExponent_lowerBlock_colex {m s : ℕ} (u : Fin m → ℕ) (r : Fin m)
    (hb : u r ≤ s) (hr : 1 < u r) :
    MacaulayCompressed.colexLT (wordExponent s (lowerBlock u r)) (wordExponent s u) := by
  let i : Fin s := ⟨u r - 1, by omega⟩
  have hi : i.val + 1 = u r := by change u r - 1 + 1 = u r; omega
  refine ⟨i, ?_, ?_⟩
  · simpa only [wordExponent_apply, hi] using lowerBlock_fiber_lt u r (by omega)
  · intro j hj
    simp only [wordExponent_apply]
    apply congrArg Finset.card
    apply lowerBlock_fiber_eq_of_gt
    have hij : i.val < j.val := hj
    omega

theorem wordExponent_lowerBlock_degree {m s : ℕ} (u : Fin m → ℕ) (r : Fin m)
    (hb : ∀ j, u j ≤ s) (hr : 1 < u r) :
    (wordExponent s (lowerBlock u r)).degree = (wordExponent s u).degree := by
  rw [wordExponent_degree _ (fun j => (lowerBlock_le u r j).trans (hb j)),
    wordExponent_degree u hb]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hchange : j ≤ r ∧ u j = u r
  · rw [lowerBlock, if_pos hchange, hchange.2]
    omega
  · simp only [lowerBlock, if_neg hchange]

/-- The exact lowering operation used by the paired-facet shelling stays
inside any divisor-closed, degreewise compressed monomial family. -/
theorem wordExponent_lowerBlock_mem {m s : ℕ} (M : Finset (Fin s →₀ ℕ))
    (hdiv : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ, g ≤ f → g ∈ M)
    (hinit : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ,
      g.degree = f.degree → MacaulayCompressed.colexLT g f → g ∈ M)
    (u : Fin m → ℕ) (hb : ∀ j, u j ≤ s) (hu : wordExponent s u ∈ M)
    (r : Fin m) (hr : 0 < u r) : wordExponent s (lowerBlock u r) ∈ M := by
  by_cases hr1 : u r = 1
  · exact hdiv _ hu _ (wordExponent_lowerBlock_le_of_one u r hr1)
  · exact hinit _ hu _ (wordExponent_lowerBlock_degree u r hb (by omega))
      (wordExponent_lowerBlock_colex u r (hb r) (by omega))

end Grunbaum2003.BilleraLee
-- END MacaulayCompressedWords.lean

-- BEGIN MacaulayCompressedWordFamily.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

theorem count_ofFn_eq_card_filter {m : ℕ} {α : Type*} [DecidableEq α]
    (u : Fin m → α) (a : α) :
    ((List.ofFn u : List α) : Multiset α).count a =
      (Finset.univ.filter (fun j => u j = a)).card := by
  rw [List.ofFn_eq_map, ← Multiset.map_coe, Multiset.count_map,
    ← Finset.val_univ_fin, ← Finset.filter_val]
  congr 1
  ext j
  simp only [eq_comm]

theorem monotone_word_eq_of_exponent_eq {m s : ℕ} (u v : Fin m → ℕ)
    (hu : Monotone u) (hv : Monotone v)
    (hbu : ∀ j, u j ≤ s) (hbv : ∀ j, v j ≤ s)
    (he : wordExponent s u = wordExponent s v) : u = v := by
  have hpos : (Finset.univ.filter (fun j => 0 < u j)).card =
      (Finset.univ.filter (fun j => 0 < v j)).card := by
    rw [← wordExponent_degree u hbu, ← wordExponent_degree v hbv, he]
  have hmultiset : ((List.ofFn u : List ℕ) : Multiset ℕ) = List.ofFn v := by
    apply Multiset.ext.mpr
    intro a
    rw [count_ofFn_eq_card_filter, count_ofFn_eq_card_filter]
    by_cases ha0 : a = 0
    · subst a
      have hcu := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (fun j => 0 < u j)
      have hcv := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (fun j => 0 < v j)
      simp only [Nat.not_lt, Nat.le_zero] at hcu hcv
      omega
    · by_cases has : a ≤ s
      · let i : Fin s := ⟨a - 1, by omega⟩
        have hi : i.val + 1 = a := by change a - 1 + 1 = a; omega
        have hc := congrArg (fun f : Fin s →₀ ℕ => f i) he
        simpa only [wordExponent_apply, hi] using hc
      · have huf : Finset.univ.filter (fun j => u j = a) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro j _ heq
          have := hbu j
          omega
        have hvf : Finset.univ.filter (fun j => v j = a) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro j _ heq
          have := hbv j
          omega
        rw [huf, hvf]
  apply List.ofFn_injective
  exact List.Perm.eq_of_sortedLE hu.sortedLE_ofFn hv.sortedLE_ofFn
    (Multiset.coe_eq_coe.mp hmultiset)

theorem exists_word_of_degree_le {m s : ℕ} (f : Fin s →₀ ℕ) (hf : f.degree ≤ m) :
    ∃ u : Fin m → ℕ, Monotone u ∧ (∀ j, u j ≤ s) ∧ wordExponent s u = f := by
  obtain ⟨u, hu, hcount, _⟩ := exists_monotone_word_of_degree_le f hf
  refine ⟨fun j => (u j).val, fun i j hij => hu hij,
    fun j => Nat.le_of_lt_succ (u j).isLt, ?_⟩
  ext i
  have hc := hcount i
  rw [count_ofFn_eq_card_filter] at hc
  simpa only [wordExponent_apply, Fin.ext_iff, Fin.val_succ] using hc

/-- All bounded monotone padded words whose literal exponent vector is selected. -/
noncomputable def compressedWords (m s : ℕ) (M : Finset (Fin s →₀ ℕ)) :
    Finset (Fin m → ℕ) :=
  ((Finset.univ : Finset (Fin m → Fin (s + 1))).image
    (fun u j => (u j).val)).filter
      (fun u => Monotone u ∧ wordExponent s u ∈ M)

theorem mem_compressedWords {m s : ℕ} (M : Finset (Fin s →₀ ℕ)) (u : Fin m → ℕ) :
    u ∈ compressedWords m s M ↔
      (∀ j, u j ≤ s) ∧ Monotone u ∧ wordExponent s u ∈ M := by
  rw [compressedWords, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hmono, hM⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨fun j => Nat.le_of_lt_succ (v j).isLt, hmono, hM⟩
  · rintro ⟨hb, hmono, hM⟩
    refine ⟨Finset.mem_image.mpr ⟨fun j => ⟨u j, Nat.lt_succ_of_le (hb j)⟩,
      Finset.mem_univ _, rfl⟩, hmono, hM⟩

theorem compressedWords_lowerBlock {m s : ℕ} (M : Finset (Fin s →₀ ℕ))
    (hdiv : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ, g ≤ f → g ∈ M)
    (hinit : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ,
      g.degree = f.degree → MacaulayCompressed.colexLT g f → g ∈ M)
    (u : Fin m → ℕ) (hu : u ∈ compressedWords m s M)
    (r : Fin m) (hr : 0 < u r) : lowerBlock u r ∈ compressedWords m s M := by
  obtain ⟨hb, hm, he⟩ := (mem_compressedWords M u).mp hu
  exact (mem_compressedWords M _).mpr
    ⟨fun j => (lowerBlock_le u r j).trans (hb j), lowerBlock_monotone u hm r,
      wordExponent_lowerBlock_mem M hdiv hinit u hb he r hr⟩

theorem compressedWords_card_slice {m s : ℕ} (M : Finset (Fin s →₀ ℕ))
    (hdeg : ∀ f ∈ M, f.degree ≤ m) (k : ℕ) :
    ((compressedWords m s M).filter
      (fun u => (Finset.univ.filter (fun j => 0 < u j)).card = k)).card =
      (M.filter (fun f => f.degree = k)).card := by
  apply Finset.card_bij (fun u _ => wordExponent s u)
  · intro u hu
    obtain ⟨hu, hk⟩ := Finset.mem_filter.mp hu
    obtain ⟨hb, _, he⟩ := (mem_compressedWords M u).mp hu
    exact Finset.mem_filter.mpr ⟨he, (wordExponent_degree u hb).trans hk⟩
  · intro u hu v hv he
    obtain ⟨hbu, hmu, _⟩ := (mem_compressedWords M u).mp (Finset.mem_filter.mp hu).1
    obtain ⟨hbv, hmv, _⟩ := (mem_compressedWords M v).mp (Finset.mem_filter.mp hv).1
    exact monotone_word_eq_of_exponent_eq u v hmu hmv hbu hbv he
  · intro f hf
    obtain ⟨hfM, hfk⟩ := Finset.mem_filter.mp hf
    obtain ⟨u, hu, hb, he⟩ := exists_word_of_degree_le f (hdeg f hfM)
    refine ⟨u, Finset.mem_filter.mpr ⟨?_, ?_⟩, he⟩
    · exact (mem_compressedWords M u).mpr ⟨hb, hu, he.symm ▸ hfM⟩
    · rw [← wordExponent_degree u hb, he, hfk]

theorem exists_shelling_word_family (n m : ℕ) (g : ℕ → ℕ)
    (hg : IsMSequence m g) (hn : g 1 ≤ n + 1) :
    ∃ W : Finset (Fin m → ℕ), W.Nonempty ∧
      (∀ u ∈ W, Monotone u) ∧
      (∀ u ∈ W, ∀ j, u j ≤ n + 1) ∧
      (∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W) ∧
      ∀ k ≤ m, (W.filter
        (fun u => (Finset.univ.filter (fun j => 0 < u j)).card = k)).card = g k := by
  obtain ⟨M, hzero, hdeg, hdiv, hinit, hcard⟩ :=
    MacaulayCompressed.exists_compressed_multicomplex n m g hg hn
  let W := compressedWords m (n + 1) M
  have hcount (k : ℕ) (hk : k ≤ m) : (W.filter
      (fun u => (Finset.univ.filter (fun j => 0 < u j)).card = k)).card = g k :=
    (compressedWords_card_slice M hdeg k).trans (hcard k hk)
  refine ⟨W, ?_, ?_, ?_, ?_, hcount⟩
  · have hc := hcount 0 (Nat.zero_le m)
    rw [hg.1] at hc
    have hnon := Finset.card_pos.mp (show 0 < (W.filter
      (fun u => (Finset.univ.filter (fun j => 0 < u j)).card = 0)).card by omega)
    exact hnon.mono (Finset.filter_subset _ _)
  · intro u hu
    exact ((mem_compressedWords M u).mp hu).2.1
  · intro u hu
    exact ((mem_compressedWords M u).mp hu).1
  · exact compressedWords_lowerBlock M hdiv hinit

end Grunbaum2003.BilleraLee
-- END MacaulayCompressedWordFamily.lean

-- BEGIN GSufficiencyNextWordOrderIdeal.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- On bounded monotone words, `wordColexLt` implies `MacaulayCompressed.colexLT` on exponent
vectors. -/
theorem wordExponent_colexLT_of_wordColexLt {m s : ℕ} (u v : Fin m → ℕ)
    (hu : Monotone u) (hv : Monotone v)
    (hbu : ∀ j, u j ≤ s)
    (hvu : wordColexLt v u) :
    MacaulayCompressed.colexLT (wordExponent s v) (wordExponent s u) := by
  rcases hvu with ⟨r, hvr, heq⟩
  have hur_pos : 0 < u r := by omega
  have hur_le : u r ≤ s := hbu r
  let i : Fin s := ⟨u r - 1, by omega⟩
  have hi_eq : i.val + 1 = u r := by dsimp [i]; omega
  refine ⟨i, ?_, ?_⟩
  · simp only [wordExponent_apply, hi_eq]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro j hj
      have hjv : v j = u r := (Finset.mem_filter.mp hj).2
      have hrj : r < j := by
        by_contra hle
        have := hv (not_lt.mp hle)
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (heq j hrj).symm.trans hjv⟩
    · intro hEq
      have hr_mem : r ∈ Finset.univ.filter (fun j => u j = u r) := by simp
      rw [← hEq, Finset.mem_filter] at hr_mem
      omega
  · intro k hik
    simp only [wordExponent_apply]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hur_lt : u r < k.val + 1 := by
      change u r - 1 < k.val at hik
      omega
    by_cases hrj : r < j
    · rw [heq j hrj]
    · have hjr : j ≤ r := not_lt.mp hrj
      have huv_lt : v j < k.val + 1 ∧ u j < k.val + 1 := by
        have := hv hjr
        have := hu hjr
        omega
      omega

/-- A monotone word has degree `≥ k` if and only if `k ≤ m` and its entry at `m - k` (when `0 < k`)
is positive; equivalently, for every `j` with `j.val < m - deg u`, `u j = 0`, and for every `j` with
`m - deg u ≤ j.val`, `0 < u j`. -/
theorem monotone_word_pos_iff {m : ℕ} (u : Fin m → ℕ) (hu : Monotone u) (j : Fin m) :
    0 < u j ↔ m - (Finset.univ.filter (fun i : Fin m => 0 < u i)).card ≤ j.val := by
  classical
  let d_u := (Finset.univ.filter (fun i : Fin m => 0 < u i)).card
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i : Fin m => 0 < u i)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have hzero_card : (Finset.univ.filter (fun i : Fin m => ¬ 0 < u i)).card = m - d_u := by omega
  constructor
  · intro hj_pos
    have hsub : Finset.univ.filter (fun i : Fin m => ¬ 0 < u i) ⊆
        Finset.univ.filter (fun i : Fin m => i.val < j.val) := by
      intro i hi
      have hi0 : ¬ 0 < u i := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      by_contra hij
      have hji : j ≤ i := not_lt.mp hij
      have := hu hji
      omega
    have hcard_le := (Finset.card_le_card hsub).trans_eq (by
      trans (Finset.range j.val).card
      · apply Finset.card_bij (fun (i : Fin m) _ => i.val)
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        · intro i1 _ i2 _ h; exact Fin.ext h
        · intro x hx
          rw [Finset.mem_range] at hx
          exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
      · exact Finset.card_range _)
    omega
  · intro hj_ge
    by_contra hj0
    have hsub : Finset.univ.filter (fun i : Fin m => i.val < j.val + 1) ⊆
        Finset.univ.filter (fun i : Fin m => ¬ 0 < u i) := by
      intro i hi
      have hij : i ≤ j := by
        have := (Finset.mem_filter.mp hi).2
        change i.val ≤ j.val
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      have := hu hij
      omega
    have hcard_low : (Finset.univ.filter (fun i : Fin m => i.val < j.val + 1)).card = j.val + 1 := by
      trans (Finset.range (j.val + 1)).card
      · apply Finset.card_bij (fun (i : Fin m) _ => i.val)
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        · intro i1 _ i2 _ h; exact Fin.ext h
        · intro x hx
          rw [Finset.mem_range] at hx
          exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
      · exact Finset.card_range _
    have hle := Finset.card_le_card hsub
    rw [hcard_low, hzero_card] at hle
    omega

/-- Truncating a word `u : Fin m → ℕ` to its last `k` entries (replacing indices `< m - k` by `0`). -/
def truncateWord {m : ℕ} (k : ℕ) (u : Fin m → ℕ) : Fin m → ℕ :=
  fun j => if j.val < m - k then 0 else u j

theorem truncateWord_monotone {m : ℕ} (k : ℕ) (u : Fin m → ℕ) (hu : Monotone u) :
    Monotone (truncateWord k u) := by
  intro i j hij
  dsimp [truncateWord]
  split_ifs with hi hj hj
  · exact le_rfl
  · exact Nat.zero_le _
  · have : i.val ≤ j.val := hij
    omega
  · exact hu hij

theorem truncateWord_le {m : ℕ} (k : ℕ) (u : Fin m → ℕ) (j : Fin m) :
    truncateWord k u j ≤ u j := by
  dsimp [truncateWord]
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

theorem wordExponent_truncateWord_le {m s : ℕ} (k : ℕ) (u : Fin m → ℕ) :
    wordExponent s (truncateWord k u) ≤ wordExponent s u := by
  intro i
  simp only [wordExponent_apply]
  apply Finset.card_le_card
  intro j hj
  have hval := (Finset.mem_filter.mp hj).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, ?_⟩
  dsimp [truncateWord] at hval
  by_cases hlt : j.val < m - k
  · rw [if_pos hlt] at hval
    omega
  · rw [if_neg hlt] at hval
    exact hval

theorem truncateWord_degree {m : ℕ} (k : ℕ) (u : Fin m → ℕ) (hu : Monotone u)
    (hk : k ≤ (Finset.univ.filter (fun j : Fin m => 0 < u j)).card) :
    (Finset.univ.filter (fun j : Fin m => 0 < truncateWord k u j)).card = k := by
  classical
  have hkm : k ≤ m := hk.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin m))
  have hfeq : Finset.univ.filter (fun j : Fin m => 0 < truncateWord k u j) =
      Finset.univ.filter (fun j : Fin m => m - k ≤ j.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [truncateWord]
    split_ifs with hlt
    · omega
    · have hge : m - k ≤ j.val := not_lt.mp hlt
      have hpos : 0 < u j := (monotone_word_pos_iff u hu j).mpr (by omega)
      exact ⟨fun _ => hge, fun _ => hpos⟩
  rw [hfeq]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun j : Fin m => m - k ≤ j.val)
  have hlow : (Finset.univ.filter (fun j : Fin m => ¬ m - k ≤ j.val)).card = m - k := by
    trans (Finset.range (m - k)).card
    · apply Finset.card_bij (fun (j : Fin m) _ => j.val)
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
        exact Finset.mem_range.mpr hj
      · intro j1 _ j2 _ h; exact Fin.ext h
      · intro x hx
        rw [Finset.mem_range] at hx
        exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mpr hx⟩, rfl⟩
    · exact Finset.card_range _
  rw [hlow, Finset.card_univ, Fintype.card_fin] at hpart
  omega

/-- Key separation property of a compressed word order ideal: for every degree `k`, every word
`u ∈ compressedWords m s M` of degree `≥ k` is strictly colex-smaller (`wordColexLt u v`) than
every bounded monotone word `v ∉ compressedWords m s M` of degree `k`. -/
theorem compressedWords_wordColexLt_of_notMem {m s : ℕ} (M : Finset (Fin s →₀ ℕ))
    (hdiv : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ, g ≤ f → g ∈ M)
    (hinit : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ,
      g.degree = f.degree → MacaulayCompressed.colexLT g f → g ∈ M)
    (k : ℕ) (u v : Fin m → ℕ)
    (hu : u ∈ compressedWords m s M)
    (huk : k ≤ (Finset.univ.filter (fun j : Fin m => 0 < u j)).card)
    (hv_mono : Monotone v) (hv_bound : ∀ j, v j ≤ s)
    (hv_deg : (Finset.univ.filter (fun j : Fin m => 0 < v j)).card = k)
    (hv_notMem : v ∉ compressedWords m s M) :
    wordColexLt u v := by
  obtain ⟨hu_bound, hu_mono, hu_M⟩ := (mem_compressedWords M u).mp hu
  let uk := truncateWord k u
  have huk_mono : Monotone uk := truncateWord_monotone k u hu_mono
  have huk_bound : ∀ j, uk j ≤ s := fun j => (truncateWord_le k u j).trans (hu_bound j)
  have huk_M : wordExponent s uk ∈ M := hdiv _ hu_M _ (wordExponent_truncateWord_le k u)
  have huk_mem : uk ∈ compressedWords m s M :=
    (mem_compressedWords M uk).mpr ⟨huk_bound, huk_mono, huk_M⟩
  have huk_deg : (Finset.univ.filter (fun j : Fin m => 0 < uk j)).card = k :=
    truncateWord_degree k u hu_mono huk
  have h_uk_lt_v : wordColexLt uk v := by
    rw [wordColexLt_iff]
    rcases lt_trichotomy (toColex uk) (toColex v) with hlt | heq | hgt
    · exact hlt
    · have huv_eq : uk = v := toColex.injective heq
      exact False.elim (hv_notMem (huv_eq ▸ huk_mem))
    · have hv_lt_uk : wordColexLt v uk := (wordColexLt_iff v uk).mpr hgt
      have hcolex := wordExponent_colexLT_of_wordColexLt uk v huk_mono hv_mono huk_bound hv_lt_uk
      have hdeg_eq : (wordExponent s v).degree = (wordExponent s uk).degree := by
        rw [wordExponent_degree v hv_bound, wordExponent_degree uk huk_bound, hv_deg, huk_deg]
      have hv_M : wordExponent s v ∈ M := hinit _ huk_M _ hdeg_eq hcolex
      exact False.elim (hv_notMem ((mem_compressedWords M v).mpr ⟨hv_bound, hv_mono, hv_M⟩))
  rcases h_uk_lt_v with ⟨r, hr_lt, hr_eq⟩
  have hvr_pos : 0 < v r := by omega
  have hr_ge : m - k ≤ r.val := by
    have := (monotone_word_pos_iff v hv_mono r).mp hvr_pos
    omega
  refine ⟨r, ?_, ?_⟩
  · dsimp [uk, truncateWord] at hr_lt
    rw [if_neg (not_lt.mpr hr_ge)] at hr_lt
    exact hr_lt
  · intro j hrj
    have hj_ge : ¬ j.val < m - k := by
      have : r.val < j.val := hrj
      omega
    have h := hr_eq j hrj
    dsimp [uk, truncateWord] at h
    rw [if_neg hj_ge] at h
    exact h

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextWordOrderIdeal.lean

-- BEGIN GSufficiencyNextCoefficientInduction.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- All bounded monotone words `u : Fin m → ℕ` with entries `≤ s`. -/
noncomputable def boundedMonotoneWords (m s : ℕ) : Finset (Fin m → ℕ) :=
  ((Finset.univ : Finset (Fin m → Fin (s + 1))).image
    (fun u j => (u j).val)).filter (fun u => Monotone u)

theorem mem_boundedMonotoneWords {m s : ℕ} (u : Fin m → ℕ) :
    u ∈ boundedMonotoneWords m s ↔ (∀ j, u j ≤ s) ∧ Monotone u := by
  rw [boundedMonotoneWords, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hmono⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨fun j => Nat.le_of_lt_succ (v j).isLt, hmono⟩
  · rintro ⟨hb, hmono⟩
    refine ⟨Finset.mem_image.mpr ⟨fun j => ⟨u j, Nat.lt_succ_of_le (hb j)⟩,
      Finset.mem_univ _, rfl⟩, hmono⟩

/-- Number of positive entries (degree) of a word `u : Fin m → ℕ`. -/
abbrev wordDegree {m : ℕ} (u : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => 0 < u j)).card

theorem wordDegree_le {m : ℕ} (u : Fin m → ℕ) : wordDegree u ≤ m :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)

/-- The Billera–Lee sample set for degree `k`, consisting of `p + 2 * r` for `0 ≤ r ≤ d / 2 - k`. -/
def degreeSampleSet (d s k : ℕ) : Finset (Fin (s + d + 1)) :=
  Finset.univ.filter (fun b : Fin (s + d + 1) =>
    ∃ r : Fin (d / 2), r.val ≤ d / 2 - k ∧ b.val = (d + 1 - 2 * (d / 2)) + 2 * r.val)

theorem degreeSampleSet_val_le (d s k : ℕ) (b : Fin (s + d + 1))
    (hb : b ∈ degreeSampleSet d s k) : b.val ≤ d + 1 := by
  rcases (Finset.mem_filter.mp hb).2 with ⟨r, _, hval⟩
  have := r.isLt
  omega

/-- Single-facet weighted root-sample sum polynomial. -/
noncomputable def cyclicFacetSumPoly {N : ℕ} (d : ℕ)
    (B F : Finset (Fin (N + 1))) : MvPolynomial (Fin (N + 1)) ℚ :=
  ∑ b ∈ B, cyclicTailWeight d b * cyclicRootSample F b

/-- When `wordDegree u < k ≤ d / 2`, every sample in `degreeSampleSet d s k` belongs to
`fullPairedFacet d s u`, so `cyclicFacetSumPoly` vanishes identically. -/
theorem cyclicFacetSumPoly_eq_zero_of_lt (d s k : ℕ) (hk : k ≤ d / 2) (u : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hlt : wordDegree u < k) :
    cyclicFacetSumPoly d (degreeSampleSet d s k) (fullPairedFacet d s u) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  rcases (Finset.mem_filter.mp hb).2 with ⟨r, hrk, hbval⟩
  have hr_lt : r.val < d / 2 - wordDegree u := by
    omega
  have hur0 : u r = 0 := by
    have hnot : ¬ 0 < u r := by
      rw [monotone_word_pos_iff u hu r]
      exact not_le.mpr hr_lt
    omega
  have hbF : b ∈ fullPairedFacet d s u := by
    rw [mem_fullPairedFacet, mem_fullPairedFacetNat]
    refine Or.inr ⟨r, Or.inl ?_⟩
    rw [hur0]
    omega
  rw [cyclicRootSample_eq_zero_of_mem _ _ hbF, mul_zero]

/-- For a monotone word `u : Fin (d / 2) → ℕ` with `1 ≤ k` and `k ≤ wordDegree u`, the index
`ru = d / 2 - wordDegree u` is the first positive-letter index of `u`, and its omitted sample
`p + 2 * ru` lies in `degreeSampleSet d s k`. -/
theorem firstPositiveIndex_spec (d s k : ℕ) (u : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hk1 : 1 ≤ k) (hku : k ≤ wordDegree u) :
    let ru : Fin (d / 2) := ⟨d / 2 - wordDegree u, by
      have := wordDegree_le u; omega⟩
    0 < u ru ∧
    (∀ j < ru, u j = 0) ∧
    (⟨(d + 1 - 2 * (d / 2)) + 2 * ru.val, by have := ru.isLt; omega⟩ : Fin (s + d + 1)) ∈
      degreeSampleSet d s k := by
  have hdeg_le := wordDegree_le u
  let ru : Fin (d / 2) := ⟨d / 2 - wordDegree u, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (monotone_word_pos_iff u hu ru).mpr le_rfl
  · intro j hj
    have hnot : ¬ 0 < u j := by
      rw [monotone_word_pos_iff u hu j]
      exact not_le.mpr hj
    omega
  · simp only [degreeSampleSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ru, by dsimp [ru]; omega, rfl⟩

/-- When `1 ≤ k ≤ wordDegree u`, the single-facet sum polynomial for `u` on `degreeSampleSet d s k`
has colex leading coefficient `1`. -/
theorem cyclicFacetSumPoly_leadingCoeff_eq_one_of_le (d s k : ℕ) (hd : 2 ≤ d)
    (u : Fin (d / 2) → ℕ) (hu : Monotone u) (hbu : ∀ j, u j ≤ s)
    (hk1 : 1 ≤ k) (hku : k ≤ wordDegree u) :
    (colexMonomialOrder (s + d + 1)).leadingCoeff
      (cyclicFacetSumPoly d (degreeSampleSet d s k) (fullPairedFacet d s u)) = 1 := by
  have hdeg_le := wordDegree_le u
  let ru : Fin (d / 2) := ⟨d / 2 - wordDegree u, by omega⟩
  obtain ⟨hru, hzerou, hcuB⟩ := firstPositiveIndex_spec d s k u hu hk1 hku
  let p := d + 1 - 2 * (d / 2)
  let cF : Fin (s + d + 1) := ⟨p + 2 * ru.val, by have := ru.isLt; omega⟩
  obtain ⟨hcFF_nat, hbeforeF_nat⟩ := fullPairedFacetNat_first_omitted d u hu ru hru hzerou
  have hcF0 : cF ≠ 0 := by
    intro h0
    have hval : cF.val = 0 := congrArg Fin.val h0
    change p + 2 * ru.val = 0 at hval
    omega
  have hcFF : cF ∉ fullPairedFacet d s u := by
    rw [mem_fullPairedFacet]
    exact hcFF_nat
  have hbeforeF : ∀ b ∈ degreeSampleSet d s k, b < cF → b ∈ fullPairedFacet d s u := by
    intro b _ hlt
    rw [mem_fullPairedFacet]
    exact hbeforeF_nat b.val hlt
  have hafterF : ∀ b ∈ degreeSampleSet d s k, cF < b → b ∉ fullPairedFacet d s u →
      ((fullPairedFacet d s u).filter (fun j => j ≤ b)).card < d := by
    intro b hbB hlt hbnot
    rw [mem_fullPairedFacet] at hbnot
    have hcard_eq : ((fullPairedFacet d s u).filter (fun j => j ≤ b)).card =
        ((fullPairedFacetNat d u).filter (fun x => x ≤ b.val)).card :=
      fullPairedFacet_filter_card d s u hbu (fun x => x ≤ b.val)
    rw [hcard_eq]
    have hbp : p ≤ b.val := by
      change p + 2 * ru.val < b.val at hlt
      omega
    exact fullPairedFacetNat_filter_le_card_lt_of_not_mem d hd u hu ⟨ru, hru⟩
      b.val hbp (degreeSampleSet_val_le d s k b hbB) hbnot
  have hevenF : Even ((fullPairedFacet d s u).filter (fun j => cF < j)).card := by
    have hcard_eq : ((fullPairedFacet d s u).filter (fun j => cF < j)).card =
        ((fullPairedFacetNat d u).filter (fun x => cF.val < x)).card :=
      fullPairedFacet_filter_card d s u hbu (fun x => cF.val < x)
    rw [hcard_eq, fullPairedFacetNat_filter_gt_card d u hu cF.val
        (by change p ≤ p + 2 * ru.val; omega) hcFF_nat]
    exact even_two_mul _
  obtain ⟨_, hlc⟩ := cyclicFacetSum_degree_leading d (degreeSampleSet d s k)
    (fullPairedFacet d s u) cF hcuB hcF0 hcFF hbeforeF hafterF
  change (colexMonomialOrder (s + d + 1)).leadingCoeff
    (∑ b ∈ degreeSampleSet d s k, cyclicTailWeight d b * cyclicRootSample (fullPairedFacet d s u) b) = 1
  rw [hlc, hevenF.neg_one_pow]

/-- Replacing `t_pos 0` with `0` preserves `MvPolynomial.eval` on `cyclicFacetSumPoly`. -/
theorem eval_zero_first_cyclicFacetSumPoly {N : ℕ} (d : ℕ)
    (B F : Finset (Fin (N + 1))) (t_pos : Fin (N + 1) → ℚ) :
    let t_rat : Fin (N + 1) → ℚ := fun i => if i = 0 then 0 else t_pos i
    MvPolynomial.eval t_rat (cyclicFacetSumPoly d B F) =
      MvPolynomial.eval t_pos (cyclicFacetSumPoly d B F) := by
  intro t_rat
  have hvar (j : Fin (N + 1)) :
      MvPolynomial.eval t_rat (cyclicParameterVariable j) =
        MvPolynomial.eval t_pos (cyclicParameterVariable j) := by
    dsimp [cyclicParameterVariable]
    split_ifs with hj
    · simp
    · simp [t_rat, hj]
  simp only [cyclicFacetSumPoly, map_sum, map_mul, cyclicTailWeight, cyclicRootSample,
    map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := by
      have hbj := (Finset.mem_filter.mp hj).2
      intro h0
      rw [h0] at hbj
      exact not_lt_of_ge (Fin.zero_le b) hbj
    simp [t_rat, hj0]
  · apply Finset.prod_congr rfl
    intro j _
    rw [hvar b, hvar j]

/-- Evaluating `cyclicFacetSumPoly` at a parameter vector `t_rat` with `t_rat 0 = 0` and casting to `ℝ`
matches the explicit real product formula. -/
theorem cast_eval_cyclicFacetSumPoly_eq {N : ℕ} (d : ℕ)
    (B F : Finset (Fin (N + 1))) (t_rat : Fin (N + 1) → ℚ) (ht0 : t_rat 0 = 0) :
    let t : Fin (N + 1) → ℝ := fun i => (t_rat i : ℝ)
    ((MvPolynomial.eval t_rat (cyclicFacetSumPoly d B F) : ℚ) : ℝ) =
      ∑ b ∈ B, (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
        (∏ j ∈ F, (t b - t j)) := by
  intro t
  have hvar (j : Fin (N + 1)) :
      MvPolynomial.eval t_rat (cyclicParameterVariable j) = t_rat j := by
    dsimp [cyclicParameterVariable]
    split_ifs with hj
    · subst hj; simp [ht0]
    · simp
  simp only [cyclicFacetSumPoly, map_sum, map_mul, cyclicTailWeight, cyclicRootSample,
    map_prod, map_sub, map_pow, MvPolynomial.eval_X, hvar,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, Rat.cast_pow, Rat.cast_sub]
  rfl

/-- Simultaneous strictly increasing evaluation `t : Fin (s + d + 1) → ℝ` with `t 0 = 0` making all
degree-`k` single-facet sums positive and strictly monotone along `wordColexLt`. -/
theorem exists_billera_lee_parameters (d s : ℕ) (hd : 2 ≤ d) :
    ∃ t : Fin (s + d + 1) → ℝ, t 0 = 0 ∧ StrictMono t ∧
      let Ψ : ℕ → (Fin (d / 2) → ℕ) → ℝ := fun k u =>
        ∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (∏ j ∈ fullPairedFacet d s u, (t b - t j))
      (∀ k ≤ d / 2, ∀ u ∈ boundedMonotoneWords (d / 2) s, wordDegree u < k → Ψ k u = 0) ∧
      (∀ k ∈ Finset.Icc 1 (d / 2), ∀ u ∈ boundedMonotoneWords (d / 2) s,
        k ≤ wordDegree u → 0 < Ψ k u) ∧
      (∀ k ∈ Finset.Icc 1 (d / 2),
        ∀ u ∈ boundedMonotoneWords (d / 2) s, ∀ v ∈ boundedMonotoneWords (d / 2) s,
          k ≤ wordDegree u → k ≤ wordDegree v → wordColexLt v u → Ψ k v < Ψ k u) := by
  classical
  let U := boundedMonotoneWords (d / 2) s
  let P1 : Finset (MvPolynomial (Fin (s + d + 1)) ℚ) :=
    (Finset.Icc 1 (d / 2)).biUnion (fun k =>
      (U.filter (fun u => k ≤ wordDegree u)).image (fun u =>
        cyclicFacetSumPoly d (degreeSampleSet d s k) (fullPairedFacet d s u)))
  let P2 : Finset (MvPolynomial (Fin (s + d + 1)) ℚ) :=
    (Finset.Icc 1 (d / 2)).biUnion (fun k =>
      (U.filter (fun u => k ≤ wordDegree u)).biUnion (fun u =>
        (U.filter (fun v => k ≤ wordDegree v ∧ wordColexLt v u)).image (fun v =>
          cyclicComparisonPolynomial d (degreeSampleSet d s k)
            (fullPairedFacet d s u) (fullPairedFacet d s v))))
  have hP : ∀ p ∈ P1 ∪ P2, (colexMonomialOrder (s + d + 1)).leadingCoeff p = 1 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · rcases Finset.mem_biUnion.mp hp1 with ⟨k, hk, hpu⟩
      rcases Finset.mem_image.mp hpu with ⟨u, hu, rfl⟩
      obtain ⟨huU, hku⟩ := Finset.mem_filter.mp hu
      obtain ⟨hbu, hmu⟩ := (mem_boundedMonotoneWords u).mp huU
      exact cyclicFacetSumPoly_leadingCoeff_eq_one_of_le d s k hd u hmu hbu
        (Finset.mem_Icc.mp hk).1 hku
    · rcases Finset.mem_biUnion.mp hp2 with ⟨k, hk, hpuv⟩
      rcases Finset.mem_biUnion.mp hpuv with ⟨u, hu, hpv⟩
      rcases Finset.mem_image.mp hpv with ⟨v, hv, rfl⟩
      obtain ⟨huU, hku⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvU, hkv, hvu⟩ := Finset.mem_filter.mp hv
      obtain ⟨hbu, hmu⟩ := (mem_boundedMonotoneWords u).mp huU
      obtain ⟨hbv, hmv⟩ := (mem_boundedMonotoneWords v).mp hvU
      obtain ⟨hru, hzerou, hcuB⟩ := firstPositiveIndex_spec d s k u hmu (Finset.mem_Icc.mp hk).1 hku
      obtain ⟨hrv, hzerov, hcvB⟩ := firstPositiveIndex_spec d s k v hmv (Finset.mem_Icc.mp hk).1 hkv
      rcases hvu with ⟨r, hr, heq⟩
      exact fullPairedFacet_comparisonPolynomial_leadingCoeff_eq_one d s hd u v hmu hmv hbu hbv
        ⟨d / 2 - wordDegree u, by have := wordDegree_le u; have := (Finset.mem_Icc.mp hk).1; omega⟩
        ⟨d / 2 - wordDegree v, by have := wordDegree_le v; have := (Finset.mem_Icc.mp hk).1; omega⟩
        hru hzerou hrv hzerov r hr heq
        (degreeSampleSet d s k) (degreeSampleSet_val_le d s k) hcuB hcvB
  obtain ⟨t_pos, ht_pos, ht_mono, ht_eval⟩ :=
    exists_increasing_pos_eval_of_leadingCoeff_eq_one (P1 ∪ P2) hP
  let t_rat : Fin (s + d + 1) → ℚ := fun i => if i = 0 then 0 else t_pos i
  have ht_rat0 : t_rat 0 = 0 := if_pos rfl
  let t : Fin (s + d + 1) → ℝ := fun i => (t_rat i : ℝ)
  have ht0 : t 0 = 0 := by simp [t, ht_rat0]
  have ht_strict : StrictMono t := by
    intro i j hij
    apply Rat.cast_lt.mpr
    dsimp [t_rat]
    split_ifs with hi hj hj
    · subst hi hj; exact False.elim (lt_irrefl (0 : Fin (s + d + 1)) hij)
    · exact ht_pos j
    · subst hj; exact False.elim (not_lt_of_ge (Fin.zero_le i) hij)
    · exact ht_mono hij
  refine ⟨t, ht0, ht_strict, ?_⟩
  intro Ψ
  have hΨ_eq (k : ℕ) (u : Fin (d / 2) → ℕ) :
      Ψ k u = ((MvPolynomial.eval t_pos
        (cyclicFacetSumPoly d (degreeSampleSet d s k) (fullPairedFacet d s u)) : ℚ) : ℝ) := by
    rw [← eval_zero_first_cyclicFacetSumPoly d (degreeSampleSet d s k) (fullPairedFacet d s u) t_pos,
      cast_eval_cyclicFacetSumPoly_eq d (degreeSampleSet d s k) (fullPairedFacet d s u) t_rat ht_rat0]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk u hu hlt
    obtain ⟨_, hmu⟩ := (mem_boundedMonotoneWords u).mp hu
    rw [hΨ_eq k u, cyclicFacetSumPoly_eq_zero_of_lt d s k hk u hmu hlt, map_zero, Rat.cast_zero]
  · intro k hk u hu hku
    rw [hΨ_eq k u]
    apply Rat.cast_pos.mpr
    apply ht_eval
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨k, hk,
      Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hku⟩, rfl⟩⟩
  · intro k hk u hu v hv hku hkv hvu
    have hsub : Ψ k u - Ψ k v = ((MvPolynomial.eval t_pos
        (cyclicComparisonPolynomial d (degreeSampleSet d s k)
          (fullPairedFacet d s u) (fullPairedFacet d s v)) : ℚ) : ℝ) := by
      rw [hΨ_eq k u, hΨ_eq k v, cyclicComparisonPolynomial_eq_sub, map_sub, Rat.cast_sub]
      rfl
    have hpos : 0 < Ψ k u - Ψ k v := by
      rw [hsub]
      apply Rat.cast_pos.mpr
      apply ht_eval
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨k, hk,
        Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hku⟩,
          Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hkv, hvu⟩, rfl⟩⟩⟩
    linarith

/-- Helper: between any nonempty finite lower-bound set `L ⊆ ℝ` and finite upper-bound set `R ⊆ ℝ`
with `∀ a ∈ L, ∀ b ∈ R, a < b`, there exists `c ∈ ℝ` strictly between `L` and `R`. -/
theorem exists_between_finsets (L R : Finset ℝ) (hL : L.Nonempty)
    (hLR : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    ∃ c : ℝ, (∀ a ∈ L, a < c) ∧ (∀ b ∈ R, c < b) := by
  by_cases hR : R.Nonempty
  · let a0 := L.max' hL
    let b0 := R.min' hR
    have ha0L : a0 ∈ L := Finset.max'_mem L hL
    have hb0R : b0 ∈ R := Finset.min'_mem R hR
    have hlt : a0 < b0 := hLR a0 ha0L b0 hb0R
    refine ⟨(a0 + b0) / 2, ?_, ?_⟩
    · intro a ha
      have : a ≤ a0 := Finset.le_max' L a ha
      linarith
    · intro b hb
      have : b0 ≤ b := Finset.min'_le R b hb
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hR
    let a0 := L.max' hL
    refine ⟨a0 + 1, ?_, ?_⟩
    · intro a ha
      have : a ≤ a0 := Finset.le_max' L a ha
      linarith
    · intro b hb
      rw [hR] at hb
      exact False.elim (Finset.notMem_empty b hb)

/-- Upward induction over degrees `K ≤ d / 2` constructing nonnegative weights `c k ≥ 0` that
separate `compressedWords (d / 2) s M` (`S u < 1`) from its complement in
`boundedMonotoneWords (d / 2) s` (`1 < S w`). -/
theorem exists_separating_coefficients_upto (d s : ℕ)
    (M : Finset (Fin s →₀ ℕ)) (h0M : (0 : Fin s →₀ ℕ) ∈ M)
    (hdiv : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ, g ≤ f → g ∈ M)
    (hinit : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ,
      g.degree = f.degree → MacaulayCompressed.colexLT g f → g ∈ M)
    (Ψ : ℕ → (Fin (d / 2) → ℕ) → ℝ)
    (hΨ_zero : ∀ k ≤ d / 2, ∀ u ∈ boundedMonotoneWords (d / 2) s, wordDegree u < k → Ψ k u = 0)
    (hΨ_pos : ∀ k ∈ Finset.Icc 1 (d / 2), ∀ u ∈ boundedMonotoneWords (d / 2) s,
      k ≤ wordDegree u → 0 < Ψ k u)
    (hΨ_mono : ∀ k ∈ Finset.Icc 1 (d / 2),
      ∀ u ∈ boundedMonotoneWords (d / 2) s, ∀ v ∈ boundedMonotoneWords (d / 2) s,
        k ≤ wordDegree u → k ≤ wordDegree v → wordColexLt v u → Ψ k v < Ψ k u)
    (K : ℕ) (hK : K ≤ d / 2) :
    let U := boundedMonotoneWords (d / 2) s
    let W := compressedWords (d / 2) s M
    ∃ c : ℕ → ℝ, (∀ k, 0 ≤ c k) ∧
      let S : (Fin (d / 2) → ℕ) → ℝ := fun u => ∑ k ∈ Finset.Icc 1 K, c k * Ψ k u
      (∀ u ∈ W, S u < 1) ∧
      (∀ w ∈ U, w ∉ W → wordDegree w ≤ K → 1 < S w) ∧
      (∀ u ∈ U, ∀ v ∈ U, K + 1 ≤ wordDegree u → K + 1 ≤ wordDegree v →
        wordColexLt u v → S u ≤ S v) := by
  classical
  let U := boundedMonotoneWords (d / 2) s
  let W := compressedWords (d / 2) s M
  induction K with
  | zero =>
    refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_, ?_⟩
    · intro u _
      simp
    · intro w hwU hwW hw0
      have hw_zero : ∀ j : Fin (d / 2), w j = 0 := by
        intro j
        by_contra hj0
        have hpos : 0 < w j := Nat.pos_of_ne_zero hj0
        have hmem : j ∈ Finset.univ.filter (fun i : Fin (d / 2) => 0 < w i) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpos⟩
        have hcard : 0 < wordDegree w := Finset.card_pos.mpr ⟨j, hmem⟩
        omega
      have hw_exp : wordExponent s w = 0 := by
        ext i
        simp only [wordExponent_apply, Finsupp.coe_zero, Pi.zero_apply, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff, Finset.mem_univ, forall_true_left]
        intro j
        rw [hw_zero j]
        omega
      obtain ⟨hbw, hmw⟩ := (mem_boundedMonotoneWords w).mp hwU
      have hw_mem : w ∈ W := (mem_compressedWords M w).mpr ⟨hbw, hmw, hw_exp.symm ▸ h0M⟩
      exact False.elim (hwW hw_mem)
    · intro u _ v _ _ _ _
      simp
  | succ K ih =>
    obtain ⟨c, hc_nonneg, hSW, hSU, hSmono⟩ := ih (by omega)
    let SK : (Fin (d / 2) → ℕ) → ℝ := fun u => ∑ k ∈ Finset.Icc 1 K, c k * Ψ k u
    have hK1_mem : K + 1 ∈ Finset.Icc 1 (d / 2) := Finset.mem_Icc.mpr ⟨by omega, hK⟩
    let L : Finset ℝ := insert 0
      ((U.filter (fun w => w ∉ W ∧ wordDegree w = K + 1)).image
        (fun w => (1 - SK w) / Ψ (K + 1) w))
    let R : Finset ℝ :=
      (W.filter (fun u => K + 1 ≤ wordDegree u)).image
        (fun u => (1 - SK u) / Ψ (K + 1) u)
    have hL_ne : L.Nonempty := ⟨0, Finset.mem_insert_self 0 _⟩
    have hWU_sub : ∀ u ∈ W, u ∈ U := by
      intro u hu
      obtain ⟨hb, hm, _⟩ := (mem_compressedWords M u).mp hu
      exact (mem_boundedMonotoneWords u).mpr ⟨hb, hm⟩
    have hLR : ∀ a ∈ L, ∀ b ∈ R, a < b := by
      intro a ha b hb
      rcases Finset.mem_image.mp hb with ⟨u, hu, rfl⟩
      obtain ⟨huW, hKu⟩ := Finset.mem_filter.mp hu
      have huU : u ∈ U := hWU_sub u huW
      have hΨu_pos : 0 < Ψ (K + 1) u := hΨ_pos (K + 1) hK1_mem u huU hKu
      have hSKu : 0 < 1 - SK u := sub_pos.mpr (hSW u huW)
      rcases Finset.mem_insert.mp ha with rfl | ha_img
      · exact div_pos hSKu hΨu_pos
      · rcases Finset.mem_image.mp ha_img with ⟨w, hw, rfl⟩
        obtain ⟨hwU, hwW, hKw⟩ := Finset.mem_filter.mp hw
        obtain ⟨hbw, hmw⟩ := (mem_boundedMonotoneWords w).mp hwU
        have hcolex : wordColexLt u w :=
          compressedWords_wordColexLt_of_notMem M hdiv hinit (K + 1) u w
            huW hKu hmw hbw hKw hwW
        have hSK_le : SK u ≤ SK w :=
          hSmono u huU w hwU hKu (by omega) hcolex
        have hΨw_pos : 0 < Ψ (K + 1) w := hΨ_pos (K + 1) hK1_mem w hwU (by omega)
        have hΨ_lt : Ψ (K + 1) u < Ψ (K + 1) w :=
          hΨ_mono (K + 1) hK1_mem w hwU u huU (by omega) hKu hcolex
        have h1 : (1 - SK w) / Ψ (K + 1) w ≤ (1 - SK u) / Ψ (K + 1) w := by
          apply div_le_div_of_nonneg_right _ hΨw_pos.le
          linarith
        have h2 : (1 - SK u) / Ψ (K + 1) w < (1 - SK u) / Ψ (K + 1) u :=
          div_lt_div_of_pos_left hSKu hΨu_pos hΨ_lt
        exact lt_of_le_of_lt h1 h2
    obtain ⟨cNew, hcL, hcR⟩ := exists_between_finsets L R hL_ne hLR
    have hcNew_pos : 0 < cNew := hcL 0 (Finset.mem_insert_self 0 _)
    let c' : ℕ → ℝ := fun k => if k = K + 1 then cNew else c k
    have hc'_nonneg (k : ℕ) : 0 ≤ c' k := by
      dsimp [c']
      split_ifs
      · exact hcNew_pos.le
      · exact hc_nonneg k
    have hsum_eq (u : Fin (d / 2) → ℕ) :
        (∑ k ∈ Finset.Icc 1 (K + 1), c' k * Ψ k u) = SK u + cNew * Ψ (K + 1) u := by
      have hIcc : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotMem : K + 1 ∉ Finset.Icc 1 K := by simp
      rw [hIcc, Finset.sum_insert hnotMem]
      have hrest : (∑ k ∈ Finset.Icc 1 K, c' k * Ψ k u) = SK u := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk_ne : k ≠ K + 1 := by
          have := (Finset.mem_Icc.mp hk).2
          omega
        simp [c', hk_ne]
      have htop : c' (K + 1) = cNew := if_pos rfl
      rw [htop, hrest, add_comm]
    refine ⟨c', hc'_nonneg, ?_, ?_, ?_⟩
    · intro u huW
      dsimp only
      rw [hsum_eq u]
      have huU : u ∈ U := hWU_sub u huW
      by_cases hKu : K + 1 ≤ wordDegree u
      · have hΨu_pos : 0 < Ψ (K + 1) u := hΨ_pos (K + 1) hK1_mem u huU hKu
        have hlt : cNew < (1 - SK u) / Ψ (K + 1) u :=
          hcR _ (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huW, hKu⟩, rfl⟩)
        have hmul := (lt_div_iff₀ hΨu_pos).mp hlt
        linarith
      · have hzero : Ψ (K + 1) u = 0 := hΨ_zero (K + 1) hK u huU (not_le.mp hKu)
        rw [hzero, mul_zero, add_zero]
        exact hSW u huW
    · intro w hwU hwW hdeg
      dsimp only
      rw [hsum_eq w]
      rcases lt_or_eq_of_le hdeg with hlt | heq
      · have hzero : Ψ (K + 1) w = 0 := hΨ_zero (K + 1) hK w hwU hlt
        rw [hzero, mul_zero, add_zero]
        exact hSU w hwU hwW (Nat.le_of_lt_succ hlt)
      · have hΨw_pos : 0 < Ψ (K + 1) w := hΨ_pos (K + 1) hK1_mem w hwU (by omega)
        have hlt : (1 - SK w) / Ψ (K + 1) w < cNew :=
          hcL _ (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hwU, hwW, heq⟩, rfl⟩))
        have hmul := (div_lt_iff₀ hΨw_pos).mp hlt
        linarith
    · intro u huU v hvU hKu hKv huv
      dsimp only
      rw [hsum_eq u, hsum_eq v]
      have h1 : SK u ≤ SK v := hSmono u huU v hvU (by omega) (by omega) huv
      have h2 : Ψ (K + 1) u < Ψ (K + 1) v :=
        hΨ_mono (K + 1) hK1_mem v hvU u huU (by omega) (by omega) huv
      nlinarith

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextCoefficientInduction.lean

-- BEGIN GSufficiencyNextFullShelling.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- The restriction set of `fullPairedFacetNat d u`, obtained by shifting
`pairedRestriction u` by the fixed prefix length `d + 1 - 2 * (d / 2)`. -/
def fullPairedRestrictionNat (d : ℕ) (u : Fin (d / 2) → ℕ) : Finset ℕ :=
  (pairedRestriction u).image (fun x => (d + 1 - 2 * (d / 2)) + x)

theorem mem_fullPairedRestrictionNat (d : ℕ) (u : Fin (d / 2) → ℕ) (x : ℕ) :
    x ∈ fullPairedRestrictionNat d u ↔
      ∃ r : Fin (d / 2), 0 < u r ∧ (d + 1 - 2 * (d / 2)) + u r + 2 * r.val + 1 = x := by
  simp only [fullPairedRestrictionNat, Finset.mem_image, mem_pairedRestriction]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, by omega⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨u r + 2 * r.val + 1, ⟨r, hr, rfl⟩, by omega⟩

theorem fullPairedRestrictionNat_subset (d : ℕ) (u : Fin (d / 2) → ℕ) :
    fullPairedRestrictionNat d u ⊆ fullPairedFacetNat d u := by
  intro x hx
  rw [fullPairedRestrictionNat, Finset.mem_image] at hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [fullPairedFacetNat, Finset.mem_union]
  exact Or.inr (Finset.mem_image_of_mem _ (pairedRestriction_subset u hy))

theorem fullPairedRestrictionNat_card (d : ℕ) (u : Fin (d / 2) → ℕ) (hu : Monotone u) :
    (fullPairedRestrictionNat d u).card =
      (Finset.univ.filter (fun r : Fin (d / 2) => 0 < u r)).card := by
  rw [fullPairedRestrictionNat,
    Finset.card_image_of_injective _ (add_right_injective (d + 1 - 2 * (d / 2))),
    pairedRestriction_card u hu]

theorem zero_mem_fullPairedFacetNat (d : ℕ) (u : Fin (d / 2) → ℕ) :
    0 ∈ fullPairedFacetNat d u := by
  rw [mem_fullPairedFacetNat]
  exact Or.inl (by omega)

theorem zero_not_mem_fullPairedRestrictionNat (d : ℕ) (u : Fin (d / 2) → ℕ) :
    0 ∉ fullPairedRestrictionNat d u := by
  rw [mem_fullPairedRestrictionNat]
  rintro ⟨r, _, h⟩
  omega

/-- Because every `fullPairedFacetNat d v` contains the fixed initial prefix
`Finset.range (d + 1 - 2 * (d / 2))`, a subset `S ⊆ fullPairedFacetNat d u` is omitted by all
earlier facets if and only if it contains `fullPairedRestrictionNat d u`. -/
theorem fullPairedFacetNat_new_face_iff (d : ℕ) (W : Finset (Fin (d / 2) → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (u : Fin (d / 2) → ℕ) (hu : u ∈ W)
    (S : Finset ℕ) (hS : S ⊆ fullPairedFacetNat d u) :
    (¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ fullPairedFacetNat d v) ↔
      fullPairedRestrictionNat d u ⊆ S := by
  let p := d + 1 - 2 * (d / 2)
  let S' : Finset ℕ := (S.filter (fun x => p ≤ x)).image (fun x => x - p)
  have hsub_iff (v : Fin (d / 2) → ℕ) :
      S ⊆ fullPairedFacetNat d v ↔ S' ⊆ pairedFacet v := by
    constructor
    · intro hSv y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      obtain ⟨hxS, hpx⟩ := Finset.mem_filter.mp hx
      have hxv := hSv hxS
      rw [fullPairedFacetNat, Finset.mem_union, Finset.mem_range] at hxv
      rcases hxv with hlt | hmem
      · omega
      · rcases Finset.mem_image.mp hmem with ⟨z, hz, rfl⟩
        simpa only [p, Nat.add_sub_cancel_left] using hz
    · intro hS'v x hxS
      rw [fullPairedFacetNat, Finset.mem_union, Finset.mem_range]
      by_cases hxp : x < p
      · exact Or.inl hxp
      · right
        have hpx : p ≤ x := le_of_not_gt hxp
        have hx' : x - p ∈ S' :=
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hxS, hpx⟩)
        refine Finset.mem_image.mpr ⟨x - p, hS'v hx', by omega⟩
  have hR_iff : fullPairedRestrictionNat d u ⊆ S ↔ pairedRestriction u ⊆ S' := by
    constructor
    · intro hR y hy
      have hpy : p + y ∈ S := hR (Finset.mem_image_of_mem _ hy)
      have hmem : p + y ∈ S.filter (fun x => p ≤ x) :=
        Finset.mem_filter.mpr ⟨hpy, by omega⟩
      simpa only [Nat.add_sub_cancel_left] using
        Finset.mem_image_of_mem (fun x => x - p) hmem
    · intro hR' x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp (hR' hy) with ⟨z, hz, hzy⟩
      obtain ⟨hzS, hpz⟩ := Finset.mem_filter.mp hz
      have hzx : z = p + y := by omega
      exact hzx ▸ hzS
  simp_rw [hsub_iff, hR_iff]
  exact pairedFacet_new_face_iff W hmono hlower u hu S' ((hsub_iff u).mp hS)

theorem fullPairedFacetNat_new_faces_card (d : ℕ) (W : Finset (Fin (d / 2) → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (u : Fin (d / 2) → ℕ) (hu : u ∈ W) (n : ℕ)
    (hn : (fullPairedRestrictionNat d u).card ≤ n) :
    (((fullPairedFacetNat d u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ fullPairedFacetNat d v)).card =
      Nat.choose (d + 1 - (fullPairedRestrictionNat d u).card)
        (n - (fullPairedRestrictionNat d u).card) := by
  classical
  have hfilter : ((fullPairedFacetNat d u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ fullPairedFacetNat d v) =
      ((fullPairedFacetNat d u).powersetCard n).filter (fullPairedRestrictionNat d u ⊆ ·) := by
    apply Finset.filter_congr
    intro S hS
    exact fullPairedFacetNat_new_face_iff d W hmono hlower u hu S
      (Finset.mem_powersetCard.mp hS).1
  rw [hfilter,
    Finset.card_filter_powersetCard_subset _ _ _ (fullPairedRestrictionNat_subset d u) hn,
    fullPairedFacetNat_card d u (hmono u hu)]

theorem fullPairedFacetNat_no_new_faces_of_lt_restriction (d : ℕ)
    (W : Finset (Fin (d / 2) → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (u : Fin (d / 2) → ℕ) (hu : u ∈ W) (n : ℕ)
    (hn : n < (fullPairedRestrictionNat d u).card) :
    ((fullPairedFacetNat d u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ fullPairedFacetNat d v) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro S hS hnew
  have hR := (fullPairedFacetNat_new_face_iff d W hmono hlower u hu S
    (Finset.mem_powersetCard.mp hS).1).mp hnew
  have hcard := Finset.card_le_card hR
  have hScard := (Finset.mem_powersetCard.mp hS).2
  omega

/-- The `n`-label faces of the full paired-facet complex whose earliest containing facet is `u`. -/
noncomputable def fullPairedNewFaces (d : ℕ) (W : Finset (Fin (d / 2) → ℕ))
    (n : ℕ) (u : Fin (d / 2) → ℕ) : Finset (Finset ℕ) :=
  ((fullPairedFacetNat d u).powersetCard n).filter
    (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ fullPairedFacetNat d v)

theorem fullPairedNewFaces_pairwiseDisjoint (d : ℕ) (W : Finset (Fin (d / 2) → ℕ)) (n : ℕ) :
    (W : Set (Fin (d / 2) → ℕ)).PairwiseDisjoint (fullPairedNewFaces d W n) := by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro S hSu hSv
  obtain ⟨hSu, hnu⟩ := Finset.mem_filter.mp hSu
  obtain ⟨hSv, hnv⟩ := Finset.mem_filter.mp hSv
  have hne' : toColex u ≠ toColex v := fun h => hne (congrArg ofColex h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact hnv ⟨u, hu, (wordColexLt_iff u v).mpr h, (Finset.mem_powersetCard.mp hSu).1⟩
  · exact hnu ⟨v, hv, (wordColexLt_iff v u).mpr h, (Finset.mem_powersetCard.mp hSv).1⟩

theorem biUnion_fullPairedNewFaces (d : ℕ) (W : Finset (Fin (d / 2) → ℕ)) (n : ℕ) :
    W.biUnion (fullPairedNewFaces d W n) =
      W.biUnion (fun u => (fullPairedFacetNat d u).powersetCard n) := by
  classical
  apply Finset.Subset.antisymm
  · intro S hS
    obtain ⟨u, hu, hSu⟩ := Finset.mem_biUnion.mp hS
    exact Finset.mem_biUnion.mpr ⟨u, hu, (Finset.mem_filter.mp hSu).1⟩
  · intro S hS
    obtain ⟨v, hv, hSv⟩ := Finset.mem_biUnion.mp hS
    let A := W.filter (fun u => S ⊆ fullPairedFacetNat d u)
    have hA : A.Nonempty := ⟨v, Finset.mem_filter.mpr
      ⟨hv, (Finset.mem_powersetCard.mp hSv).1⟩⟩
    obtain ⟨u, huA, hmin⟩ := A.exists_min_image (fun u => toColex u) hA
    obtain ⟨hu, hSu⟩ := Finset.mem_filter.mp huA
    apply Finset.mem_biUnion.mpr
    refine ⟨u, hu, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨hSu, (Finset.mem_powersetCard.mp hSv).2⟩
    · rintro ⟨w, hw, hwu, hSw⟩
      have hle := hmin w (Finset.mem_filter.mpr ⟨hw, hSw⟩)
      exact (not_lt_of_ge hle) ((wordColexLt_iff w u).mp hwu)

/-- Total `n`-element face count of the full `(d + 1)`-uniform paired-facet complex. -/
theorem fullPaired_faces_card_eq_sum (d : ℕ) (W : Finset (Fin (d / 2) → ℕ))
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W) (n : ℕ) :
    (W.biUnion (fun u => (fullPairedFacetNat d u).powersetCard n)).card =
      ∑ u ∈ W, if (fullPairedRestrictionNat d u).card ≤ n then
        Nat.choose (d + 1 - (fullPairedRestrictionNat d u).card)
          (n - (fullPairedRestrictionNat d u).card) else 0 := by
  classical
  rw [← biUnion_fullPairedNewFaces d W n,
    Finset.card_biUnion (fullPairedNewFaces_pairwiseDisjoint d W n)]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hn : (fullPairedRestrictionNat d u).card ≤ n
  · rw [if_pos hn]
    exact fullPairedFacetNat_new_faces_card d W hmono hlower u hu n hn
  · rw [if_neg hn]
    change (((fullPairedFacetNat d u).powersetCard n).filter
      (fun S => ¬ ∃ v ∈ W, wordColexLt v u ∧ S ⊆ fullPairedFacetNat d v)).card = 0
    rw [fullPairedFacetNat_no_new_faces_of_lt_restriction d W hmono hlower u hu n (by omega)]
    rfl

/-- Grouping the shelling sum by restriction degree gives the exact binomial formula
in terms of the degree-slice counts `g k`. -/
theorem fullPaired_faces_card_eq_degree_sum (d : ℕ) (W : Finset (Fin (d / 2) → ℕ))
    (g : ℕ → ℕ)
    (hmono : ∀ u ∈ W, Monotone u)
    (hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W)
    (hslice : ∀ k ≤ d / 2,
      (W.filter (fun u => (Finset.univ.filter (fun j => 0 < u j)).card = k)).card = g k)
    (n : ℕ) :
    (W.biUnion (fun u => (fullPairedFacetNat d u).powersetCard n)).card =
      ∑ k ∈ Finset.range (d / 2 + 1),
        if k ≤ n then g k * Nat.choose (d + 1 - k) (n - k) else 0 := by
  classical
  rw [fullPaired_faces_card_eq_sum d W hmono hlower n]
  let deg : (Fin (d / 2) → ℕ) → ℕ :=
    fun u => (Finset.univ.filter (fun j : Fin (d / 2) => 0 < u j)).card
  have hmaps : ∀ u ∈ W, deg u ∈ Finset.range (d / 2 + 1) := by
    intro u _
    rw [Finset.mem_range]
    have hle : deg u ≤ Fintype.card (Fin (d / 2)) := Finset.card_le_univ _
    rw [Fintype.card_fin] at hle
    omega
  have hcongr :
      (∑ u ∈ W, if (fullPairedRestrictionNat d u).card ≤ n then
        Nat.choose (d + 1 - (fullPairedRestrictionNat d u).card)
          (n - (fullPairedRestrictionNat d u).card) else 0) =
      ∑ u ∈ W, if deg u ≤ n then
        Nat.choose (d + 1 - deg u) (n - deg u) else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [fullPairedRestrictionNat_card d u (hmono u hu)]
  rw [hcongr, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hfiber :
      (∑ u ∈ W.filter (fun u => deg u = k),
        if deg u ≤ n then Nat.choose (d + 1 - deg u) (n - deg u) else 0) =
      ∑ _u ∈ W.filter (fun u => deg u = k),
        if k ≤ n then Nat.choose (d + 1 - k) (n - k) else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  rw [hfiber, Finset.sum_const, smul_eq_mul, hslice k (by omega)]
  split_ifs
  · rfl
  · rw [mul_zero]

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextFullShelling.lean

-- BEGIN GSufficiencyNextPairedFacetsExposed.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

theorem zero_mem_fullPairedFacet (d s : ℕ) (u : Fin (d / 2) → ℕ) :
    (0 : Fin (s + d + 1)) ∈ fullPairedFacet d s u := by
  rw [mem_fullPairedFacet]
  exact zero_mem_fullPairedFacetNat d u

theorem fullPairedFacet_nonempty (d s : ℕ) (u : Fin (d / 2) → ℕ) :
    (fullPairedFacet d s u).Nonempty :=
  ⟨0, zero_mem_fullPairedFacet d s u⟩

theorem fullPairedFacet_image_val (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hbu : ∀ r, u r ≤ s) :
    (fullPairedFacet d s u).image Fin.val = fullPairedFacetNat d u := by
  ext x
  simp only [Finset.mem_image, mem_fullPairedFacet]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hx
    exact ⟨⟨x, fullPairedFacetNat_lt_of_bound d s u hbu hx⟩, hx, rfl⟩

theorem fullPairedFacet_card (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hbu : ∀ r, u r ≤ s) :
    (fullPairedFacet d s u).card = d + 1 := by
  rw [← fullPairedFacetNat_card d u hu, ← fullPairedFacet_image_val d s u hbu,
    Finset.card_image_of_injective _ Fin.val_injective]

/-- Every `fullPairedFacet d s u` of a bounded word `u` realizes an exposed face of the
`(d + 1)`-dimensional cyclic polytope with exact vertex-incidence set `fullPairedFacet d s u`. -/
theorem fullPairedFacet_exposed (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hbu : ∀ r, u r ≤ s) (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))))
      (convexHull ℝ
        ((fun i => momentCurve (d + 1) (t i)) ''
          (fullPairedFacet d s u : Set (Fin (s + d + 1))))) ∧
    ∀ i, momentCurve (d + 1) (t i) ∈
      convexHull ℝ
        ((fun i => momentCurve (d + 1) (t i)) ''
          (fullPairedFacet d s u : Set (Fin (s + d + 1)))) ↔
      i ∈ fullPairedFacet d s u := by
  let p := d + 1 - 2 * (d / 2)
  rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
  · have hp : p = 1 := by dsimp [p]; omega
    let a : Fin (d / 2) → Fin ((s + d) + 1) := fun r =>
      ⟨p + u r + 2 * r.val, by have := r.isLt; have := hbu r; omega⟩
    let b : Fin (d / 2) → Fin ((s + d) + 1) := fun r =>
      ⟨p + u r + 2 * r.val + 1, by have := r.isLt; have := hbu r; omega⟩
    have hab : ∀ r, (b r).val = (a r).val + 1 := fun _ => rfl
    have hset : (fullPairedFacet d s u : Set (Fin ((s + d) + 1))) =
        {0} ∪ (Set.range a ∪ Set.range b) := by
      ext j
      simp only [Finset.mem_coe, mem_fullPairedFacet, mem_fullPairedFacetNat,
        Set.mem_union, Set.mem_singleton_iff, Set.mem_range, Fin.ext_iff, Fin.val_zero, a, b]
      constructor
      · rintro (hlt | ⟨r, h1 | h2⟩)
        · left; omega
        · right; left; exact ⟨r, h1.symm⟩
        · right; right; exact ⟨r, h2.symm⟩
      · rintro (hj0 | ⟨r, h1⟩ | ⟨r, h2⟩)
        · left; omega
        · right; exact ⟨r, Or.inl h1.symm⟩
        · right; exact ⟨r, Or.inr h2.symm⟩
    have h := momentCurve_first_and_adjacent_pairs_exposed
      (d := d + 1) (n := s + d) (m := d / 2) (by omega) t ht a b hab
    simpa only [← hset, Finset.mem_coe] using h
  · have hp : p = 2 := by dsimp [p]; omega
    let a : Fin (d / 2 + 1) → Fin (s + d + 1) := fun k =>
      if hk : k.val < d / 2 then
        ⟨p + u ⟨k.val, hk⟩ + 2 * k.val, by have := hbu ⟨k.val, hk⟩; omega⟩
      else
        ⟨0, by omega⟩
    let b : Fin (d / 2 + 1) → Fin (s + d + 1) := fun k =>
      if hk : k.val < d / 2 then
        ⟨p + u ⟨k.val, hk⟩ + 2 * k.val + 1, by have := hbu ⟨k.val, hk⟩; omega⟩
      else
        ⟨1, by omega⟩
    have hab : ∀ k, (b k).val = (a k).val + 1 := by
      intro k
      dsimp [a, b]
      split_ifs <;> rfl
    have hset : (fullPairedFacet d s u : Set (Fin (s + d + 1))) =
        Set.range a ∪ Set.range b := by
      ext j
      simp only [Finset.mem_coe, mem_fullPairedFacet, mem_fullPairedFacetNat,
        Set.mem_union, Set.mem_range]
      constructor
      · rintro (hlt | ⟨r, h1 | h2⟩)
        · have hj01 : j.val = 0 ∨ j.val = 1 := by omega
          rcases hj01 with hj0 | hj1
          · left
            refine ⟨⟨d / 2, Nat.lt_succ_self _⟩, ?_⟩
            apply Fin.ext
            simp [a, hj0]
          · right
            refine ⟨⟨d / 2, Nat.lt_succ_self _⟩, ?_⟩
            apply Fin.ext
            simp [b, hj1]
        · left
          refine ⟨⟨r.val, Nat.lt_succ_of_lt r.isLt⟩, ?_⟩
          apply Fin.ext
          simp [a, r.isLt, h1, p]
        · right
          refine ⟨⟨r.val, Nat.lt_succ_of_lt r.isLt⟩, ?_⟩
          apply Fin.ext
          simp [b, r.isLt, h2, p]
      · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
        · by_cases hk : k.val < d / 2
          · right
            exact ⟨⟨k.val, hk⟩, Or.inl (by simp [a, hk, p])⟩
          · left
            simp [a, hk]
            omega
        · by_cases hk : k.val < d / 2
          · right
            exact ⟨⟨k.val, hk⟩, Or.inr (by simp [b, hk, p])⟩
          · left
            simp [b, hk]
            omega
    have h := momentCurve_adjacent_pairs_exposed
      (d := d + 1) (n := s + d + 1) (m := d / 2 + 1)
      (Nat.succ_pos _) (by omega) t ht a b hab
    simpa only [← hset, Finset.mem_coe] using h

/-- Every `fullPairedFacet d s u` of a bounded monotone word `u` has affine dimension `d`
in `ℝ^(d + 1)`. -/
theorem fullPairedFacet_finrank (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hbu : ∀ r, u r ≤ s)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t) :
    Module.finrank ℝ
      (affineSpan ℝ (convexHull ℝ
        ((fun i => momentCurve (d + 1) (t i)) ''
          (fullPairedFacet d s u : Set (Fin (s + d + 1)))))).direction = d := by
  have hcard := fullPairedFacet_card d s u hu hbu
  have h := momentCurve_subset_finrank (d := d + 1) t ht.injective
    (fullPairedFacet d s u) (fullPairedFacet_nonempty d s u) (by omega)
  omega

/-- Every subset of at most `d + 1` distinct samples on the `(d + 1)`-dimensional moment curve
is an exposed face of that sample simplex with exact vertex-incidence set `I`. -/
theorem momentCurve_simplex_subset_exposed {d m : ℕ} (hm : m ≤ d + 1)
    (t : Fin m → ℝ) (ht : Function.Injective t) (I : Finset (Fin m)) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun j => momentCurve (d + 1) (t j))))
      (convexHull ℝ ((fun j => momentCurve (d + 1) (t j)) '' (I : Set (Fin m)))) ∧
    ∀ j : Fin m, momentCurve (d + 1) (t j) ∈
      convexHull ℝ ((fun j => momentCurve (d + 1) (t j)) '' (I : Set (Fin m))) ↔ j ∈ I := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hIne
  · simp only [Finset.coe_empty, Set.image_empty, convexHull_empty, Set.mem_empty_iff_false,
      Finset.notMem_empty, implies_true, and_true]
    exact isExposed_empty
  let c : Fin m → ℝ := fun r => ∏ j ∈ Finset.univ.erase r, (t r - t j)
  let pr : Fin m → Polynomial ℝ := fun r =>
    Polynomial.C (c r) * ∏ j ∈ Finset.univ.erase r, (Polynomial.X - Polynomial.C (t j))
  let p : Polynomial ℝ := ∑ r ∈ Finset.univ \ I, pr r
  have hcr_ne (r : Fin m) : c r ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.mpr (ht.ne (Finset.ne_of_mem_erase hj).symm)
  have hpr_eval_self (r : Fin m) : 0 < (pr r).eval (t r) := by
    simp only [pr, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X]
    exact mul_self_pos.mpr (hcr_ne r)
  have hpr_eval_ne (r k : Fin m) (hkr : k ≠ r) : (pr r).eval (t k) = 0 := by
    simp only [pr, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, mul_eq_zero, Finset.prod_eq_zero_iff]
    right
    exact ⟨k, Finset.mem_erase.mpr ⟨hkr, Finset.mem_univ k⟩, sub_self _⟩
  have hp_eval_mem (k : Fin m) (hk : k ∈ I) : p.eval (t k) = 0 := by
    simp only [p, Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro r hr
    have hkr : k ≠ r := by
      rintro rfl
      exact (Finset.mem_sdiff.mp hr).2 hk
    exact hpr_eval_ne r k hkr
  have hp_eval_notMem (k : Fin m) (hk : k ∉ I) : 0 < p.eval (t k) := by
    simp only [p, Polynomial.eval_finsetSum]
    have hk_mem : k ∈ Finset.univ \ I := Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hk⟩
    rw [Finset.sum_eq_single k]
    · exact hpr_eval_self k
    · intro r _ hrk
      exact hpr_eval_ne r k hrk.symm
    · intro hk_not
      exact False.elim (hk_not hk_mem)
  have hpr_deg (r : Fin m) : (pr r).natDegree ≤ d + 1 := by
    apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc (∑ j ∈ Finset.univ.erase r, (Polynomial.X - Polynomial.C (t j)).natDegree)
        ≤ ∑ _j ∈ Finset.univ.erase r, 1 := by
          apply Finset.sum_le_sum
          intro j _
          rw [Polynomial.natDegree_X_sub_C]
      _ = (Finset.univ.erase r).card := by simp
      _ ≤ m := (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
      _ ≤ d + 1 := hm
  have hp_deg : p.natDegree ≤ d + 1 := by
    apply (Polynomial.natDegree_sum_le _ _).trans
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun r _ => hpr_deg r⟩
  apply momentCurve_face_of_polynomial t (I : Set (Fin m)) (Finset.coe_nonempty.mpr hIne) p hp_deg
  · intro k
    by_cases hk : k ∈ I
    · rw [hp_eval_mem k hk]
    · exact (hp_eval_notMem k hk).le
  · intro k
    simp only [Finset.mem_coe]
    constructor
    · intro h0
      by_contra hk
      exact (hp_eval_notMem k hk).ne' h0
    · exact hp_eval_mem k

/-- Every subset `S ⊆ fullPairedFacet d s u` realizes an exposed face of the `(d + 1)`-dimensional
cyclic polytope with exact vertex-incidence set `S`. -/
theorem fullPairedFacet_subset_exposed (d s : ℕ) (u : Fin (d / 2) → ℕ)
    (hu : Monotone u) (hbu : ∀ r, u r ≤ s)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t)
    {S : Finset (Fin (s + d + 1))} (hS : S ⊆ fullPairedFacet d s u) :
    IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))))
      (convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (S : Set (Fin (s + d + 1))))) ∧
    ∀ i, momentCurve (d + 1) (t i) ∈
      convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (S : Set (Fin (s + d + 1)))) ↔
      i ∈ S := by
  classical
  let F := fullPairedFacet d s u
  have hFcard : F.card = d + 1 := fullPairedFacet_card d s u hu hbu
  let e : Fin (d + 1) ≃ ↥F := Fintype.equivOfCardEq (by simp [hFcard])
  let t' : Fin (d + 1) → ℝ := fun j => t (e j).val
  have ht' : Function.Injective t' :=
    ht.injective.comp (Subtype.val_injective.comp e.injective)
  let I : Finset (Fin (d + 1)) := Finset.univ.filter (fun j => (e j).val ∈ S)
  have hrange : Set.range (fun j => momentCurve (d + 1) (t' j)) =
      (fun i => momentCurve (d + 1) (t i)) '' (F : Set (Fin (s + d + 1))) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨(e j).val, (e j).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      exact ⟨j, by simp [t', hj]⟩
  have himage : (fun j => momentCurve (d + 1) (t' j)) '' (I : Set (Fin (d + 1))) =
      (fun i => momentCurve (d + 1) (t i)) '' (S : Set (Fin (s + d + 1))) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, I, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hjS, rfl⟩
      exact ⟨(e j).val, hjS, rfl⟩
    · rintro ⟨i, hiS, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hS hiS⟩
      have hjeq : (e j).val = i := congrArg Subtype.val hj
      exact ⟨j, hjeq.symm ▸ hiS, by simp [t', hjeq]⟩
  obtain ⟨hExpF, hIncF⟩ := fullPairedFacet_exposed d s u hbu t ht
  obtain ⟨hExpI, hIncI⟩ := momentCurve_simplex_subset_exposed (le_refl (d + 1)) t' ht' I
  rw [hrange, himage] at hExpI
  have hExpS : IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))))
      (convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (S : Set (Fin (s + d + 1))))) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have hFuniv : F = Finset.univ :=
        Finset.eq_univ_of_card F (by simp [hFcard])
      have hFtop : (fun i => momentCurve (d + 1) (t i)) '' (F : Set (Fin (0 + d + 1))) =
          Set.range (fun i => momentCurve (d + 1) (t i)) := by
        rw [hFuniv, Finset.coe_univ, Set.image_univ]
      rwa [hFtop] at hExpI
    · have hP : IsDPolytope (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))) :=
        momentCurve_isDPolytope (by omega) t ht.injective
      exact StellarFaceTools.isExposed_trans_polytope (d + 1) _ hP _ _ hExpF hExpI
  refine ⟨hExpS, ?_⟩
  intro i
  constructor
  · intro hi
    have hiF : i ∈ F :=
      (hIncF i).mp (convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hS)) hi)
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hiF⟩
    have hjeq : (e j).val = i := congrArg Subtype.val hj
    have hjv : momentCurve (d + 1) (t' j) ∈
        convexHull ℝ ((fun k => momentCurve (d + 1) (t' k)) '' (I : Set (Fin (d + 1)))) := by
      rw [himage]
      simpa only [t', hjeq] using hi
    have hjI : j ∈ I := (hIncI j).mp hjv
    simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and, hjeq] using hjI
  · intro hiS
    exact subset_convexHull ℝ _ ⟨i, hiS, rfl⟩

/-- Two subsets `S₁ ⊆ fullPairedFacet d s u₁` and `S₂ ⊆ fullPairedFacet d s u₂` have the same
convex hull on the moment curve if and only if `S₁ = S₂`. -/
theorem fullPairedFacet_subset_convexHull_eq_iff (d s : ℕ)
    (u₁ u₂ : Fin (d / 2) → ℕ)
    (hu₁ : Monotone u₁) (hu₂ : Monotone u₂)
    (hbu₁ : ∀ r, u₁ r ≤ s) (hbu₂ : ∀ r, u₂ r ≤ s)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t)
    {S₁ S₂ : Finset (Fin (s + d + 1))}
    (hS₁ : S₁ ⊆ fullPairedFacet d s u₁) (hS₂ : S₂ ⊆ fullPairedFacet d s u₂) :
    convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (S₁ : Set (Fin (s + d + 1)))) =
      convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (S₂ : Set (Fin (s + d + 1)))) ↔
      S₁ = S₂ := by
  obtain ⟨_, hInc₁⟩ := fullPairedFacet_subset_exposed d s u₁ hu₁ hbu₁ t ht hS₁
  obtain ⟨_, hInc₂⟩ := fullPairedFacet_subset_exposed d s u₂ hu₂ hbu₂ t ht hS₂
  constructor
  · intro hEq
    ext i
    rw [← hInc₁ i, hEq, hInc₂ i]
  · rintro rfl
    rfl

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextPairedFacetsExposed.lean

-- BEGIN GSufficiencyNextGaleEvenness.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- On strictly increasing parameters `t`, the sign of the root product `∏ j ∈ F, (t i - t j)`
at an omitted index `i ∉ F` is positive if and only if the number of elements of `F` strictly
above `i` is even. -/
theorem prod_sub_pos_iff_even_gt {n : ℕ} (t : Fin n → ℝ) (ht : StrictMono t)
    (F : Finset (Fin n)) (i : Fin n) (hi : i ∉ F) :
    (∏ j ∈ F, (t i - t j) ≠ 0) ∧
      (0 < ∏ j ∈ F, (t i - t j) ↔ Even ((F.filter (fun j => i < j)).card)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp
  | insert a S haS ih =>
    have hai : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a S)
    have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨hneS, hiffS⟩ := ih hiS
    rw [Finset.prod_insert haS, Finset.filter_insert]
    rcases lt_or_gt_of_ne hai with hia | hai'
    · have hneg : t i - t a < 0 := sub_neg.mpr (ht hia)
      have hne : (t i - t a) * ∏ j ∈ S, (t i - t j) ≠ 0 :=
        mul_ne_zero hneg.ne hneS
      refine ⟨hne, ?_⟩
      rw [if_pos hia, Finset.card_insert_of_notMem (by simp [haS]), Nat.even_add_one, ← hiffS]
      constructor
      · intro hpos hposS
        have : (t i - t a) * ∏ j ∈ S, (t i - t j) < 0 :=
          mul_neg_of_neg_of_pos hneg hposS
        linarith
      · intro hnPosS
        have hnegS : ∏ j ∈ S, (t i - t j) < 0 :=
          lt_of_le_of_ne (le_of_not_gt hnPosS) hneS
        exact mul_pos_of_neg_of_neg hneg hnegS
    · have hpos_a : 0 < t i - t a := sub_pos.mpr (ht hai')
      have hne : (t i - t a) * ∏ j ∈ S, (t i - t j) ≠ 0 :=
        mul_ne_zero hpos_a.ne' hneS
      refine ⟨hne, ?_⟩
      have hnot : ¬ i < a := not_lt.mpr hai'.le
      rw [if_neg hnot, mul_pos_iff_of_pos_left hpos_a, hiffS]

/-- If `F ⊆ Finset.range (2 * m + s)` has cardinality `2 * m` and every omitted label `b < 2 * m + s`
has an even number of elements of `F` strictly above `b`, then `F` is a `pairedFacet u` for a
monotone word `u : Fin m → ℕ` bounded by `s`. -/
theorem exists_word_of_even_above_nat (m s : ℕ) (F : Finset ℕ)
    (hsub : ∀ x ∈ F, x < s + 2 * m) (hcard : F.card = 2 * m)
    (heven : ∀ b < s + 2 * m, b ∉ F → Even ((F.filter (fun x => b < x)).card)) :
    ∃ u : Fin m → ℕ, Monotone u ∧ (∀ r, u r ≤ s) ∧ F = pairedFacet u := by
  classical
  let emb := F.orderEmbOfFin hcard
  have hmap : Finset.univ.map emb.toEmbedding = F := Finset.map_orderEmbOfFin_univ F hcard
  have hmem_iff (x : ℕ) : x ∈ F ↔ ∃ k : Fin (2 * m), emb k = x := by
    rw [← hmap, Finset.mem_map]
    simp only [Finset.mem_univ, RelEmbedding.coe_toEmbedding, true_and]
  have hpair (r : Fin m) :
      emb ⟨2 * r.val + 1, by omega⟩ = emb ⟨2 * r.val, by omega⟩ + 1 := by
    let i0 : Fin (2 * m) := ⟨2 * r.val, by omega⟩
    let i1 : Fin (2 * m) := ⟨2 * r.val + 1, by omega⟩
    have hlt : emb i0 < emb i1 := emb.strictMono (by change 2 * r.val < 2 * r.val + 1; omega)
    by_contra hne
    have hgt : emb i0 + 1 < emb i1 :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hlt) (Ne.symm hne)
    let b := emb i0 + 1
    have hb_lt : b < s + 2 * m := by
      have hi1 : emb i1 ∈ F := (hmem_iff _).mpr ⟨i1, rfl⟩
      have := hsub _ hi1
      omega
    have hbF : b ∉ F := by
      rw [hmem_iff]
      rintro ⟨k, hk⟩
      by_cases hk0 : k ≤ i0
      · have := emb.monotone hk0
        omega
      · have hi1k : i1 ≤ k := by
          change 2 * r.val + 1 ≤ k.val
          change ¬ k.val ≤ 2 * r.val at hk0
          omega
        have := emb.monotone hi1k
        omega
    have hfilter_card : (F.filter (fun x => b < x)).card = 2 * m - (2 * r.val + 1) := by
      rw [← hmap, Finset.filter_map, Finset.card_map]
      simp only [RelEmbedding.coe_toEmbedding]
      have hfeq : Finset.univ.filter ((fun x => b < x) ∘ emb) =
          Finset.univ.filter (fun k : Fin (2 * m) => 2 * r.val + 1 ≤ k.val) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
        constructor
        · intro hbk
          by_contra hlt_k
          have hk0 : k ≤ i0 := by change k.val ≤ 2 * r.val; omega
          have := emb.monotone hk0
          omega
        · intro hge
          have hi1k : i1 ≤ k := hge
          have := emb.monotone hi1k
          omega
      rw [hfeq]
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (2 * m))))
        (fun k : Fin (2 * m) => 2 * r.val + 1 ≤ k.val)
      have hlow : (Finset.univ.filter (fun k : Fin (2 * m) => ¬ 2 * r.val + 1 ≤ k.val)).card =
          2 * r.val + 1 := by
        trans (Finset.range (2 * r.val + 1)).card
        · apply Finset.card_bij (fun (k : Fin (2 * m)) _ => k.val)
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hk
            exact Finset.mem_range.mpr hk
          · intro k1 _ k2 _ h; exact Fin.ext h
          · intro x hx
            rw [Finset.mem_range] at hx
            exact ⟨⟨x, by omega⟩, by simp; omega, rfl⟩
        · exact Finset.card_range _
      rw [hlow, Finset.card_univ, Fintype.card_fin] at hpart
      omega
    rcases heven b hb_lt hbF with ⟨q, hq⟩
    rw [hfilter_card] at hq
    omega
  have hstep (r1 r2 : Fin m) (h12 : r1 ≤ r2) :
      emb ⟨2 * r1.val, by omega⟩ + 2 * (r2.val - r1.val) ≤ emb ⟨2 * r2.val, by omega⟩ := by
    obtain ⟨d_step, hd_step⟩ := Nat.exists_eq_add_of_le (show r1.val ≤ r2.val from h12)
    have h_ind : ∀ k (hk : r1.val + k < m),
        emb ⟨2 * r1.val, by omega⟩ + 2 * k ≤ emb ⟨2 * (r1.val + k), by omega⟩ := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        have hp_k := hpair ⟨r1.val + k, by omega⟩
        dsimp at hp_k
        have hlt_next : emb ⟨2 * (r1.val + k) + 1, by omega⟩ <
            emb ⟨2 * (r1.val + (k + 1)), by omega⟩ :=
          emb.strictMono (by change 2 * (r1.val + k) + 1 < 2 * (r1.val + (k + 1)); omega)
        omega
    have h := h_ind d_step (by omega)
    have hr2_eq : ⟨2 * (r1.val + d_step), by omega⟩ = (⟨2 * r2.val, by omega⟩ : Fin (2 * m)) := by
      apply Fin.ext
      dsimp
      omega
    rw [hr2_eq] at h
    omega
  have hge_2r (r : Fin m) : 2 * r.val ≤ emb ⟨2 * r.val, by omega⟩ := by
    let r0 : Fin m := ⟨0, r.pos⟩
    have h0r : r0 ≤ r := Nat.zero_le r.val
    have h0 := hstep r0 r h0r
    dsimp [r0] at h0
    omega
  let u : Fin m → ℕ := fun r => emb ⟨2 * r.val, by omega⟩ - 2 * r.val
  have hu_eq (r : Fin m) : emb ⟨2 * r.val, by omega⟩ = u r + 2 * r.val := by
    dsimp [u]
    have := hge_2r r
    omega
  have hu_mono : Monotone u := by
    intro r1 r2 h12
    have h := hstep r1 r2 h12
    have h1 := hge_2r r1
    have h2 := hge_2r r2
    have h12' : r1.val ≤ r2.val := h12
    dsimp [u]
    omega
  have hu_bound (r : Fin m) : u r ≤ s := by
    have hm : 0 < m := r.pos
    let rmax : Fin m := ⟨m - 1, by omega⟩
    have hrmax : r ≤ rmax := show r.val ≤ m - 1 by omega
    have hle := hu_mono hrmax
    have hmem : emb ⟨2 * rmax.val + 1, by omega⟩ ∈ F :=
      (hmem_iff _).mpr ⟨⟨2 * rmax.val + 1, by omega⟩, rfl⟩
    have hlt_top := hsub _ hmem
    have hp_top := hpair rmax
    have heq_top := hu_eq rmax
    dsimp [rmax] at hp_top heq_top hlt_top hle
    omega
  refine ⟨u, hu_mono, hu_bound, ?_⟩
  ext x
  rw [hmem_iff, mem_pairedFacet]
  constructor
  · rintro ⟨k, rfl⟩
    let r : Fin m := ⟨k.val / 2, by omega⟩
    rcases Nat.mod_two_eq_zero_or_one k.val with hk0 | hk1
    · have hk_eq : k = ⟨2 * r.val, by omega⟩ := by apply Fin.ext; dsimp [r]; omega
      rw [hk_eq, hu_eq r]
      exact ⟨r, Or.inl rfl⟩
    · have hk_eq : k = ⟨2 * r.val + 1, by omega⟩ := by apply Fin.ext; dsimp [r]; omega
      rw [hk_eq, hpair r, hu_eq r]
      exact ⟨r, Or.inr rfl⟩
  · rintro ⟨r, rfl | rfl⟩
    · exact ⟨⟨2 * r.val, by omega⟩, hu_eq r⟩
    · exact ⟨⟨2 * r.val + 1, by omega⟩, by rw [hpair r, hu_eq r]⟩

/-- Every `(d + 1)`-element subset `F ⊆ Fin (s + d + 1)` containing `0` whose root count strictly
above every omitted label is even is a `fullPairedFacet d s u` for a bounded monotone word `u`. -/
theorem exists_word_of_even_above (d s : ℕ) (F : Finset (Fin (s + d + 1)))
    (hcard : F.card = d + 1) (h0 : (0 : Fin (s + d + 1)) ∈ F)
    (heven : ∀ i : Fin (s + d + 1), i ∉ F → Even ((F.filter (fun j => i < j)).card)) :
    ∃ u : Fin (d / 2) → ℕ, Monotone u ∧ (∀ r, u r ≤ s) ∧ F = fullPairedFacet d s u := by
  classical
  let p := d + 1 - 2 * (d / 2)
  have hprefix (i : Fin (s + d + 1)) (hi : i.val < p) : i ∈ F := by
    by_contra hiF
    have hij0 : i.val = 1 ∧ p = 2 := by
      have hi0 : i ≠ 0 := fun h => hiF (h ▸ h0)
      have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      omega
    have hfilter_eq : F.filter (fun j => i < j) = F.erase 0 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      have h0val : (0 : Fin (s + d + 1)).val = 0 := rfl
      constructor
      · intro ⟨hjF, hij⟩
        refine ⟨?_, hjF⟩
        intro hj0
        rw [hj0] at hij
        change i.val < 0 at hij
        omega
      · intro ⟨hj0, hjF⟩
        refine ⟨hjF, ?_⟩
        have hji : j ≠ i := fun h => hiF (h ▸ hjF)
        have hne_i : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hne_0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        change i.val < j.val
        omega
    rcases heven i hiF with ⟨k, hk⟩
    rw [hfilter_eq, Finset.card_erase_of_mem h0, hcard] at hk
    omega
  let F' : Finset ℕ :=
    ((F.filter (fun j => p ≤ j.val)).image Fin.val).image (fun x => x - p)
  have hF'_sub : ∀ y ∈ F', y < s + 2 * (d / 2) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    have hjlt := j.isLt
    have hjp := (Finset.mem_filter.mp hj).2
    omega
  have hF'_mem_iff (y : ℕ) (hy : y < s + 2 * (d / 2)) :
      y ∈ F' ↔ (⟨p + y, by omega⟩ : Fin (s + d + 1)) ∈ F := by
    simp only [F', Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨j, ⟨hjF, hjp⟩, rfl⟩, rfl⟩
      convert hjF
      omega
    · intro hjF
      exact ⟨p + y, ⟨⟨p + y, by omega⟩, ⟨hjF, by dsimp; omega⟩, rfl⟩, by omega⟩
  have hF'_card : F'.card = 2 * (d / 2) := by
    have hinj1 : Set.InjOn (fun x : ℕ => x - p)
        (((F.filter (fun j => p ≤ j.val)).image Fin.val : Finset ℕ) : Set ℕ) := by
      intro x1 hx1 x2 hx2 h12
      rcases Finset.mem_image.mp hx1 with ⟨j1, hj1, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨j2, hj2, rfl⟩
      have h1 := (Finset.mem_filter.mp hj1).2
      have h2 := (Finset.mem_filter.mp hj2).2
      dsimp at h12
      omega
    rw [Finset.card_image_of_injOn hinj1, Finset.card_image_of_injective _ Fin.val_injective]
    have hpart := Finset.card_filter_add_card_filter_not (s := F) (fun j => p ≤ j.val)
    have hlow : (F.filter (fun j => ¬ p ≤ j.val)).card = p := by
      have heq_low : F.filter (fun j => ¬ p ≤ j.val) =
          Finset.univ.filter (fun j : Fin (s + d + 1) => j.val < p) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        exact ⟨fun h => h.2, fun h => ⟨hprefix j h, h⟩⟩
      rw [heq_low]
      trans (Finset.range p).card
      · apply Finset.card_bij (fun (j : Fin (s + d + 1)) _ => j.val)
        · intro j hj
          rw [Finset.mem_filter] at hj
          exact Finset.mem_range.mpr hj.2
        · intro j1 _ j2 _ h; exact Fin.ext h
        · intro x hx
          rw [Finset.mem_range] at hx
          exact ⟨⟨x, by omega⟩, by simp [hx], rfl⟩
      · exact Finset.card_range _
    rw [hlow, hcard] at hpart
    omega
  have hF'_even : ∀ b < s + 2 * (d / 2), b ∉ F' → Even ((F'.filter (fun y => b < y)).card) := by
    intro b hb hbF'
    let ib : Fin (s + d + 1) := ⟨p + b, by omega⟩
    have hibF : ib ∉ F := fun h => hbF' ((hF'_mem_iff b hb).mpr h)
    have hcard_eq : (F'.filter (fun y => b < y)).card = (F.filter (fun j => ib < j)).card := by
      apply Finset.card_bij (fun y hy => (⟨p + y, by
        have := hF'_sub y (Finset.mem_filter.mp hy).1; omega⟩ : Fin (s + d + 1)))
      · intro y hy
        obtain ⟨hyF', hby⟩ := Finset.mem_filter.mp hy
        have hy_lt := hF'_sub y hyF'
        exact Finset.mem_filter.mpr ⟨(hF'_mem_iff y hy_lt).mp hyF', by
          change p + b < p + y; omega⟩
      · intro y1 _ y2 _ h
        have hval := congrArg Fin.val h
        dsimp at hval
        omega
      · intro j hj
        obtain ⟨hjF, hij⟩ := Finset.mem_filter.mp hj
        change p + b < j.val at hij
        have hlt : j.val - p < s + 2 * (d / 2) := by have := j.isLt; omega
        have hjeq : (⟨p + (j.val - p), by omega⟩ : Fin (s + d + 1)) = j := by
          apply Fin.ext; dsimp; omega
        have hjF' : j.val - p ∈ F' := (hF'_mem_iff (j.val - p) hlt).mpr (hjeq.symm ▸ hjF)
        exact ⟨j.val - p, Finset.mem_filter.mpr ⟨hjF', by omega⟩, hjeq⟩
    rw [hcard_eq]
    exact heven ib hibF
  obtain ⟨u, hu_mono, hu_bound, hF'_eq⟩ :=
    exists_word_of_even_above_nat (d / 2) s F' hF'_sub hF'_card hF'_even
  refine ⟨u, hu_mono, hu_bound, ?_⟩
  ext j
  rw [mem_fullPairedFacet, fullPairedFacetNat, Finset.mem_union, Finset.mem_range]
  by_cases hjp : j.val < p
  · exact ⟨fun _ => Or.inl hjp, fun _ => hprefix j hjp⟩
  · have hge : p ≤ j.val := le_of_not_gt hjp
    have hlt : j.val - p < s + 2 * (d / 2) := by have := j.isLt; omega
    have hjeq : (⟨p + (j.val - p), by omega⟩ : Fin (s + d + 1)) = j := by
      apply Fin.ext; dsimp; omega
    have hiff := hF'_mem_iff (j.val - p) hlt
    rw [hjeq, hF'_eq] at hiff
    constructor
    · intro hjF
      right
      exact Finset.mem_image.mpr ⟨j.val - p, hiff.mpr hjF, by omega⟩
    · rintro (hlt' | hmem)
      · omega
      · rcases Finset.mem_image.mp hmem with ⟨z, hz, hzj⟩
        have hzeq : z = j.val - p := by omega
        exact hiff.mp (hzeq ▸ hz)

/-- Every exposed facet of a `(d + 1)`-dimensional cyclic polytope with `1 ≤ s` is supported by
either `+l_F` (a lower facet, where `0 ≤ q_F(t i)` for all `i`) or `-l_F` (an upper facet, where
`q_F(t i) ≤ 0` for all `i`), where `F` is its `(d + 1)`-element vertex-incidence set and
`q_F(X) = ∏ j ∈ F, (X - t j)`. -/
theorem cyclic_facet_support_characterization (d s : ℕ) (hs : 1 ≤ s)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t)
    (𝒢 : Set (Fin (d + 1) → ℝ)) (h𝒢ne : 𝒢.Nonempty)
    (h𝒢 : IsExposed ℝ (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))) 𝒢)
    (h𝒢dim : Module.finrank ℝ (affineSpan ℝ 𝒢).direction = d) :
    let F : Finset (Fin (s + d + 1)) :=
      Finset.univ.filter (fun i => momentCurve (d + 1) (t i) ∈ 𝒢)
    let q : Polynomial ℝ := ∏ j ∈ F, (Polynomial.X - Polynomial.C (t j))
    let l : StrongDual ℝ (Fin (d + 1) → ℝ) :=
      -(∑ j : Fin (d + 1), q.coeff (j.val + 1) • ContinuousLinearMap.proj j)
    F.card = d + 1 ∧
    𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (F : Set (Fin (s + d + 1)))) ∧
    (∀ x : ℝ, l (momentCurve (d + 1) x) = q.coeff 0 - q.eval x) ∧
    ((∀ i : Fin (s + d + 1), i ∉ F → 0 < q.eval (t i)) ∧
      (∀ y ∈ convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))), l y ≤ q.coeff 0) ∧
      (∀ y ∈ convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))),
        y ∈ 𝒢 ↔ l y = q.coeff 0) ∨
     (∀ i : Fin (s + d + 1), i ∉ F → q.eval (t i) < 0) ∧
      (∀ y ∈ convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))), -l y ≤ -q.coeff 0) ∧
      (∀ y ∈ convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))),
        y ∈ 𝒢 ↔ -l y = -q.coeff 0)) := by
  classical
  intro F q l
  let P := convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))
  have hFle : F.card ≤ d + 1 :=
    momentCurve_facet_indices_card_le t ht.injective 𝒢 (by omega)
  have hset : 𝒢 ∩ Set.range (fun i => momentCurve (d + 1) (t i)) =
      (fun i => momentCurve (d + 1) (t i)) '' (F : Set (Fin (s + d + 1))) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, Finset.mem_coe, F,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, i, rfl⟩
  have h𝒢hull : 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) '' (F : Set (Fin (s + d + 1)))) := by
    rw [← hset]
    exact StellarFaceTools.finite_face_hull (fun i => momentCurve (d + 1) (t i)) h𝒢
  have hFne : F.Nonempty := by
    by_contra hnone
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have h𝒢empty : 𝒢 = ∅ := by simpa [he] using h𝒢hull
    exact h𝒢ne.ne_empty h𝒢empty
  have hrank := momentCurve_subset_finrank (d := d + 1) t ht.injective F hFne (by omega)
  rw [← h𝒢hull, h𝒢dim] at hrank
  have hFcard : F.card = d + 1 := hrank.symm
  have hqdeg : q.natDegree ≤ d + 1 := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc (∑ j ∈ F, (Polynomial.X - Polynomial.C (t j)).natDegree)
        ≤ ∑ _j ∈ F, 1 := by
          apply Finset.sum_le_sum
          intro j _
          rw [Polynomial.natDegree_X_sub_C]
      _ = F.card := by simp
      _ = d + 1 := hFcard
  have hl_eval (x : ℝ) : l (momentCurve (d + 1) x) = q.coeff 0 - q.eval x := by
    have heval := Polynomial.eval_eq_sum_range' (p := q) (n := (d + 1) + 1) (by omega) x
    rw [Finset.sum_range_succ'] at heval
    simp only [pow_zero, mul_one] at heval
    have hl : l (momentCurve (d + 1) x) =
        -(∑ j ∈ Finset.range (d + 1), q.coeff (j + 1) * x ^ (j + 1)) := by
      simp only [l, neg_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
        momentCurve, smul_eq_mul, neg_inj]
      exact Fin.sum_univ_eq_sum_range (fun j => q.coeff (j + 1) * x ^ (j + 1)) (d + 1)
    rw [hl]
    linarith
  have hq_zero (i : Fin (s + d + 1)) : q.eval (t i) = 0 ↔ i ∈ F := by
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Finset.prod_eq_zero_iff, sub_eq_zero]
    exact ⟨fun ⟨j, hjF, hij⟩ => ht.injective hij ▸ hjF, fun hiF => ⟨i, hiF, rfl⟩⟩
  obtain ⟨x0, hx0⟩ := h𝒢ne
  obtain ⟨φ, hφ⟩ := h𝒢 ⟨x0, hx0⟩
  have hx0_max : x0 ∈ P ∧ ∀ y ∈ P, φ y ≤ φ x0 := by
    have h := hx0; rwa [hφ] at h
  have hφ_mem (y : Fin (d + 1) → ℝ) (hyP : y ∈ P) : y ∈ 𝒢 ↔ φ y = φ x0 := by
    constructor
    · intro hy𝒢
      rw [hφ] at hy𝒢
      exact le_antisymm (hx0_max.2 y hyP) (hy𝒢.2 x0 hx0_max.1)
    · intro hEq
      rw [hφ]
      exact ⟨hyP, fun z hz => hEq.symm ▸ hx0_max.2 z hz⟩
  have hφ_vert (i : Fin (s + d + 1)) :
      (i ∈ F → φ (momentCurve (d + 1) (t i)) = φ x0) ∧
      (i ∉ F → φ (momentCurve (d + 1) (t i)) < φ x0) := by
    have hiP : momentCurve (d + 1) (t i) ∈ P := subset_convexHull ℝ _ ⟨i, rfl⟩
    have hiF_iff : i ∈ F ↔ momentCurve (d + 1) (t i) ∈ 𝒢 := by simp [F]
    rw [hiF_iff, hφ_mem _ hiP]
    exact ⟨id, fun hne => lt_of_le_of_ne (hx0_max.2 _ hiP) hne⟩
  have hcompl_ne : (Finset.univ \ F).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hFcard]
    omega
  obtain ⟨iStar, hiStar⟩ := hcompl_ne
  have hiStarF : iStar ∉ F := (Finset.mem_sdiff.mp hiStar).2
  have hq_iStar_ne : q.eval (t iStar) ≠ 0 := fun h0 => hiStarF ((hq_zero iStar).mp h0)
  have hφ_iStar_pos : 0 < φ x0 - φ (momentCurve (d + 1) (t iStar)) :=
    sub_pos.mpr ((hφ_vert iStar).2 hiStarF)
  let lam : ℝ := (φ x0 - φ (momentCurve (d + 1) (t iStar))) / q.eval (t iStar)
  have hlam_ne : lam ≠ 0 := div_ne_zero hφ_iStar_pos.ne' hq_iStar_ne
  let Fplus : Finset (Fin (s + d + 1)) := insert iStar F
  have hFplus_card : Fplus.card = d + 2 := by
    rw [Finset.card_insert_of_notMem hiStarF, hFcard]
  let ePlus : Fin (d + 2) ≃ ↥Fplus := Fintype.equivOfCardEq (by simp [hFplus_card])
  have hspan_top : affineSpan ℝ
      (Set.range (fun k : Fin (d + 2) => momentCurve (d + 1) (t (ePlus k).val))) = ⊤ :=
    momentCurve_affineSpan_eq_top (le_refl (d + 2))
      (fun k => t (ePlus k).val) (ht.injective.comp (Subtype.val_injective.comp ePlus.injective))
  let ψ : (Fin (d + 1) → ℝ) →ᵃ[ℝ] ℝ :=
    φ.toLinearMap.toAffineMap - AffineMap.const ℝ (Fin (d + 1) → ℝ) (φ x0) -
      lam • (l.toLinearMap.toAffineMap - AffineMap.const ℝ (Fin (d + 1) → ℝ) (q.coeff 0))
  have hψ_Fplus (j : Fin (s + d + 1)) (hj : j ∈ Fplus) :
      ψ (momentCurve (d + 1) (t j)) = 0 := by
    change (φ (momentCurve (d + 1) (t j)) - φ x0) -
      lam * (l (momentCurve (d + 1) (t j)) - q.coeff 0) = 0
    rw [hl_eval (t j)]
    rcases Finset.mem_insert.mp hj with hj_eq | hjF
    · rw [hj_eq]
      have hmul : lam * (-q.eval (t iStar)) = -(φ x0 - φ (momentCurve (d + 1) (t iStar))) := by
        dsimp [lam]
        rw [mul_neg, div_mul_cancel₀ _ hq_iStar_ne]
      linarith
    · rw [(hφ_vert j).1 hjF, (hq_zero j).mpr hjF]
      ring
  have hψ_zero (y : Fin (d + 1) → ℝ) : ψ y = 0 := by
    have hy_top : y ∈ (⊤ : AffineSubspace ℝ (Fin (d + 1) → ℝ)) := AffineSubspace.mem_top ℝ _ y
    rw [← hspan_top] at hy_top
    have hsub_ker : Set.range (fun k : Fin (d + 2) => momentCurve (d + 1) (t (ePlus k).val)) ⊆
        (AffineSubspace.comap ψ (affineSpan ℝ {(0 : ℝ)}) : Set (Fin (d + 1) → ℝ)) := by
      rintro _ ⟨k, rfl⟩
      change ψ (momentCurve (d + 1) (t (ePlus k).val)) ∈ affineSpan ℝ {(0 : ℝ)}
      rw [hψ_Fplus (ePlus k).val (ePlus k).property]
      exact subset_affineSpan ℝ _ (Set.mem_singleton 0)
    have hmem := affineSpan_le.mpr hsub_ker hy_top
    change ψ y ∈ affineSpan ℝ {(0 : ℝ)} at hmem
    exact (AffineSubspace.mem_affineSpan_singleton ℝ ℝ).mp hmem
  have hφ_eq (y : Fin (d + 1) → ℝ) : φ y - φ x0 = lam * (l y - q.coeff 0) := by
    have h := hψ_zero y
    change (φ y - φ x0) - lam * (l y - q.coeff 0) = 0 at h
    linarith
  refine ⟨hFcard, h𝒢hull, hl_eval, ?_⟩
  rcases lt_or_gt_of_ne hlam_ne with hlam_neg | hlam_pos
  · right
    refine ⟨?_, ?_, ?_⟩
    · intro i hiF
      have h1 := (hφ_vert i).2 hiF
      have h2 := hφ_eq (momentCurve (d + 1) (t i))
      rw [hl_eval (t i)] at h2
      have h3 : lam * (-q.eval (t i)) < 0 := by linarith
      nlinarith
    · intro y hyP
      have h1 := hx0_max.2 y hyP
      have h2 := hφ_eq y
      have h3 : lam * (l y - q.coeff 0) ≤ 0 := by linarith
      nlinarith
    · intro y hyP
      rw [hφ_mem y hyP]
      have h2 := hφ_eq y
      constructor
      · intro hEq
        have h3 : lam * (l y - q.coeff 0) = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h0 | h0
        · exact False.elim (hlam_ne h0)
        · linarith
      · intro hEq
        have h3 : l y - q.coeff 0 = 0 := by linarith
        rw [h3, mul_zero] at h2
        linarith
  · left
    refine ⟨?_, ?_, ?_⟩
    · intro i hiF
      have h1 := (hφ_vert i).2 hiF
      have h2 := hφ_eq (momentCurve (d + 1) (t i))
      rw [hl_eval (t i)] at h2
      have h3 : lam * (-q.eval (t i)) < 0 := by linarith
      nlinarith
    · intro y hyP
      have h1 := hx0_max.2 y hyP
      have h2 := hφ_eq y
      have h3 : lam * (l y - q.coeff 0) ≤ 0 := by linarith
      nlinarith
    · intro y hyP
      rw [hφ_mem y hyP]
      have h2 := hφ_eq y
      constructor
      · intro hEq
        have h3 : lam * (l y - q.coeff 0) = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h0 | h0
        · exact False.elim (hlam_ne h0)
        · linarith
      · intro hEq
        have h3 : l y - q.coeff 0 = 0 := by linarith
        rw [h3, mul_zero] at h2
        linarith

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextGaleEvenness.lean

-- BEGIN GSufficiencyNextVisibilityConstruct.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- Monic univariate root polynomial `∏ j ∈ F, (X - t j)` for a vertex subset `F`. -/
noncomputable def cyclicRootPoly {N : ℕ} (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) : Polynomial ℝ :=
  ∏ j ∈ F, (Polynomial.X - Polynomial.C (t j))

/-- Canonical linear functional associated with `cyclicRootPoly t F` on `Fin (d + 1) → ℝ`. -/
noncomputable def cyclicFacetFunctional {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) : StrongDual ℝ (Fin (d + 1) → ℝ) :=
  -(∑ j : Fin (d + 1), (cyclicRootPoly t F).coeff (j.val + 1) • ContinuousLinearMap.proj j)

theorem cyclicRootPoly_eval {N : ℕ} (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) (x : ℝ) :
    (cyclicRootPoly t F).eval x = ∏ j ∈ F, (x - t j) := by
  simp only [cyclicRootPoly, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

theorem cyclicRootPoly_eval_eq_zero_iff {N : ℕ} (t : Fin (N + 1) → ℝ) (ht : StrictMono t)
    (F : Finset (Fin (N + 1))) (i : Fin (N + 1)) :
    (cyclicRootPoly t F).eval (t i) = 0 ↔ i ∈ F := by
  rw [cyclicRootPoly_eval, Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero]
  exact ⟨fun ⟨j, hjF, hij⟩ => ht.injective hij ▸ hjF, fun hiF => ⟨i, hiF, rfl⟩⟩

theorem cyclicRootPoly_coeff_zero {N : ℕ} (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) :
    (cyclicRootPoly t F).coeff 0 = ∏ j ∈ F, (-t j) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, cyclicRootPoly_eval]
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem cyclicRootPoly_coeff_zero_of_zero_mem {N : ℕ} (t : Fin (N + 1) → ℝ) (ht0 : t 0 = 0)
    (F : Finset (Fin (N + 1))) (h0 : (0 : Fin (N + 1)) ∈ F) :
    (cyclicRootPoly t F).coeff 0 = 0 := by
  rw [cyclicRootPoly_coeff_zero]
  apply Finset.prod_eq_zero h0
  rw [ht0, neg_zero]

theorem cyclicRootPoly_monic_and_natDegree {N : ℕ} (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) :
    (cyclicRootPoly t F).Monic ∧ (cyclicRootPoly t F).natDegree = F.card := by
  have hmonic : (cyclicRootPoly t F).Monic :=
    Polynomial.monic_prod_of_monic F (fun j => Polynomial.X - Polynomial.C (t j))
      (fun j _ => Polynomial.monic_X_sub_C (t j))
  refine ⟨hmonic, ?_⟩
  rw [cyclicRootPoly, Polynomial.natDegree_prod_of_monic F _
    (fun j _ => Polynomial.monic_X_sub_C (t j))]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem cyclicRootPoly_coeff_top {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) (hcard : F.card = d + 1) :
    (cyclicRootPoly t F).coeff (d + 1) = 1 := by
  obtain ⟨hmonic, hdeg⟩ := cyclicRootPoly_monic_and_natDegree t F
  rw [← hcard, ← hdeg]
  exact hmonic.leadingCoeff

theorem cyclicFacetFunctional_eval_momentCurve {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) (hcard : F.card = d + 1) (x : ℝ) :
    cyclicFacetFunctional d t F (momentCurve (d + 1) x) =
      (cyclicRootPoly t F).coeff 0 - (cyclicRootPoly t F).eval x := by
  obtain ⟨_, hdeg⟩ := cyclicRootPoly_monic_and_natDegree t F
  have heval := Polynomial.eval_eq_sum_range' (p := cyclicRootPoly t F)
    (n := (d + 1) + 1) (by omega) x
  rw [Finset.sum_range_succ'] at heval
  simp only [pow_zero, mul_one] at heval
  have hl : cyclicFacetFunctional d t F (momentCurve (d + 1) x) =
      -(∑ j ∈ Finset.range (d + 1), (cyclicRootPoly t F).coeff (j + 1) * x ^ (j + 1)) := by
    simp only [cyclicFacetFunctional, neg_apply, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, momentCurve, smul_eq_mul, neg_inj]
    exact Fin.sum_univ_eq_sum_range
      (fun j => (cyclicRootPoly t F).coeff (j + 1) * x ^ (j + 1)) (d + 1)
  rw [hl]
  linarith

theorem cyclicFacetFunctional_neg_topBasis {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (F : Finset (Fin (N + 1))) (hcard : F.card = d + 1) :
    cyclicFacetFunctional d t F (-Pi.single (Fin.last d) (1 : ℝ)) = 1 := by
  rw [map_neg, cyclicFacetFunctional, neg_apply, neg_neg, sum_apply]
  rw [Finset.sum_eq_single (Fin.last d)]
  · simp only [smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one, Fin.val_last]
    exact cyclicRootPoly_coeff_top d t F hcard
  · intro j _ hj
    simp only [smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem fullPairedFacet_rootPoly_pos_of_notMem (d s : ℕ)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t)
    (u : Fin (d / 2) → ℕ) (hu : Monotone u) (hbu : ∀ r, u r ≤ s)
    (i : Fin (s + d + 1)) (hi : i ∉ fullPairedFacet d s u) :
    0 < (cyclicRootPoly t (fullPairedFacet d s u)).eval (t i) := by
  rw [cyclicRootPoly_eval, (prod_sub_pos_iff_even_gt t ht (fullPairedFacet d s u) i hi).2]
  have hcard_eq : ((fullPairedFacet d s u).filter (fun j => i < j)).card =
      ((fullPairedFacetNat d u).filter (fun x => i.val < x)).card :=
    fullPairedFacet_filter_card d s u hbu (fun x => i.val < x)
  rw [hcard_eq]
  have hi_nat : i.val ∉ fullPairedFacetNat d u := by
    rwa [mem_fullPairedFacet] at hi
  have hip : d + 1 - 2 * (d / 2) ≤ i.val := by
    by_contra hlt
    exact hi_nat ((mem_fullPairedFacetNat d u i.val).mpr (Or.inl (not_le.mp hlt)))
  rw [fullPairedFacetNat_filter_gt_card d u hu i.val hip hi_nat]
  exact even_two_mul _

theorem momentCurve_mem_fullPairedFacet_hull_iff (d s : ℕ)
    (t : Fin (s + d + 1) → ℝ) (ht0 : t 0 = 0) (ht : StrictMono t)
    (u : Fin (d / 2) → ℕ) (hu : Monotone u) (hbu : ∀ r, u r ≤ s)
    (i : Fin (s + d + 1)) :
    momentCurve (d + 1) (t i) ∈
      convexHull ℝ ((fun j => momentCurve (d + 1) (t j)) ''
        (fullPairedFacet d s u : Set (Fin (s + d + 1)))) ↔
      i ∈ fullPairedFacet d s u := by
  let Fu := fullPairedFacet d s u
  let l := cyclicFacetFunctional d t Fu
  have hcard : Fu.card = d + 1 := fullPairedFacet_card d s u hu hbu
  have h0_coeff : (cyclicRootPoly t Fu).coeff 0 = 0 :=
    cyclicRootPoly_coeff_zero_of_zero_mem t ht0 Fu (zero_mem_fullPairedFacet d s u)
  constructor
  · intro hmem
    by_contra hiFu
    have hpos : 0 < (cyclicRootPoly t Fu).eval (t i) :=
      fullPairedFacet_rootPoly_pos_of_notMem d s t ht u hu hbu i hiFu
    have hl_neg : l (momentCurve (d + 1) (t i)) < 0 := by
      rw [cyclicFacetFunctional_eval_momentCurve d t Fu hcard (t i), h0_coeff]
      linarith
    have hsub : (fun j => momentCurve (d + 1) (t j)) '' (Fu : Set (Fin (s + d + 1))) ⊆
        {x : Fin (d + 1) → ℝ | 0 ≤ l x} := by
      rintro _ ⟨j, hj, rfl⟩
      change 0 ≤ l (momentCurve (d + 1) (t j))
      rw [cyclicFacetFunctional_eval_momentCurve d t Fu hcard (t j), h0_coeff,
        (cyclicRootPoly_eval_eq_zero_iff t ht Fu j).mpr hj, sub_zero]
    have hconv : Convex ℝ {x : Fin (d + 1) → ℝ | 0 ≤ l x} := by
      intro x hx y hy a b ha hb _
      change 0 ≤ l x at hx
      change 0 ≤ l y at hy
      change 0 ≤ l (a • x + b • y)
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      nlinarith
    have hge : 0 ≤ l (momentCurve (d + 1) (t i)) :=
      convexHull_min hsub hconv hmem
    linarith
  · intro hiFu
    exact subset_convexHull ℝ _ ⟨i, hiFu, rfl⟩

/-- The Section 7 visibility direction `v = -e_d + ∑_{k=1}^{d/2} c_k Z_k`. -/
noncomputable def visibilityDirection (d s : ℕ) (t : Fin (s + d + 1) → ℝ) (c : ℕ → ℝ) :
    Fin (d + 1) → ℝ :=
  -Pi.single (Fin.last d) (1 : ℝ) +
    ∑ k ∈ Finset.Icc 1 (d / 2), c k •
      ∑ b ∈ degreeSampleSet d s k,
        (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) •
          momentCurve (d + 1) (t b)

theorem cyclicFacetFunctional_visibilityDirection (d s : ℕ)
    (t : Fin (s + d + 1) → ℝ) (ht0 : t 0 = 0) (c : ℕ → ℝ)
    (F : Finset (Fin (s + d + 1))) (hcard : F.card = d + 1)
    (h0 : (0 : Fin (s + d + 1)) ∈ F) :
    cyclicFacetFunctional d t F (visibilityDirection d s t c) =
      1 - ∑ k ∈ Finset.Icc 1 (d / 2), c k *
        ∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (cyclicRootPoly t F).eval (t b) := by
  have hcoeff0 : (cyclicRootPoly t F).coeff 0 = 0 :=
    cyclicRootPoly_coeff_zero_of_zero_mem t ht0 F h0
  rw [visibilityDirection, map_add, cyclicFacetFunctional_neg_topBasis d t F hcard,
    map_sum]
  have hsum : (∑ k ∈ Finset.Icc 1 (d / 2),
      cyclicFacetFunctional d t F (c k • ∑ b ∈ degreeSampleSet d s k,
        (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) • momentCurve (d + 1) (t b))) =
      -(∑ k ∈ Finset.Icc 1 (d / 2), c k *
        ∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (cyclicRootPoly t F).eval (t b)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, map_sum, smul_eq_mul]
    have hinner : (∑ b ∈ degreeSampleSet d s k,
        cyclicFacetFunctional d t F
          ((∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) • momentCurve (d + 1) (t b))) =
        -(∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (cyclicRootPoly t F).eval (t b)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [map_smul, smul_eq_mul, cyclicFacetFunctional_eval_momentCurve d t F hcard (t b),
        hcoeff0, zero_sub, mul_neg]
    rw [hinner, mul_neg]
  rw [hsum, sub_eq_add_neg]

/-- Polynomial `(X - t_last) * (X - t_0)^(d - 2|S|) * ∏ j ∈ S, (X - t_j)^2` used to certify
that every subset `S` of size `≤ d / 2` lies on a supporting hyperplane of `P` strictly above `zStar`. -/
noncomputable def upperSubsetPoly {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (t (Fin.last N))) *
    (Polynomial.X - Polynomial.C (t 0)) ^ (d - 2 * S.card) *
    ∏ j ∈ S, ((Polynomial.X - Polynomial.C (t j)) * (Polynomial.X - Polynomial.C (t j)))

/-- Linear functional associated with `upperSubsetPoly d t S` on `Fin (d + 1) → ℝ`. -/
noncomputable def upperSubsetFunctional {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) : StrongDual ℝ (Fin (d + 1) → ℝ) :=
  -(∑ j : Fin (d + 1), (upperSubsetPoly d t S).coeff (j.val + 1) • ContinuousLinearMap.proj j)

theorem upperSubsetPoly_eval {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) (x : ℝ) :
    (upperSubsetPoly d t S).eval x =
      (x - t (Fin.last N)) * (x - t 0) ^ (d - 2 * S.card) *
        ∏ j ∈ S, ((x - t j) * (x - t j)) := by
  simp only [upperSubsetPoly, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem upperSubsetPoly_eval_nonpos {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ) (ht : StrictMono t)
    (S : Finset (Fin (N + 1))) (i : Fin (N + 1)) :
    (upperSubsetPoly d t S).eval (t i) ≤ 0 := by
  rw [upperSubsetPoly_eval]
  have h1 : t i - t (Fin.last N) ≤ 0 :=
    sub_nonpos.mpr (ht.monotone (Fin.le_last i))
  have h2 : 0 ≤ (t i - t 0) ^ (d - 2 * S.card) :=
    pow_nonneg (sub_nonneg.mpr (ht.monotone (Fin.zero_le i))) _
  have h3 : 0 ≤ ∏ j ∈ S, ((t i - t j) * (t i - t j)) :=
    Finset.prod_nonneg (fun j _ => mul_self_nonneg (t i - t j))
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h1 h2) h3

theorem upperSubsetPoly_eval_eq_zero_of_mem {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) {i : Fin (N + 1)} (hi : i ∈ S) :
    (upperSubsetPoly d t S).eval (t i) = 0 := by
  rw [upperSubsetPoly_eval]
  have hprod : (∏ j ∈ S, ((t i - t j) * (t i - t j))) = 0 := by
    apply Finset.prod_eq_zero hi
    ring
  rw [hprod, mul_zero]

theorem upperSubsetPoly_monic_and_natDegree {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) (hS : S.card ≤ d / 2) :
    (upperSubsetPoly d t S).Monic ∧ (upperSubsetPoly d t S).natDegree = d + 1 := by
  have hm1 : (Polynomial.X - Polynomial.C (t (Fin.last N))).Monic :=
    Polynomial.monic_X_sub_C _
  have hm2 : ((Polynomial.X - Polynomial.C (t 0)) ^ (d - 2 * S.card)).Monic :=
    (Polynomial.monic_X_sub_C _).pow _
  have hm3 : (∏ j ∈ S, ((Polynomial.X - Polynomial.C (t j)) *
      (Polynomial.X - Polynomial.C (t j)))).Monic :=
    Polynomial.monic_prod_of_monic S _ (fun j _ =>
      (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _))
  have hmonic : (upperSubsetPoly d t S).Monic := (hm1.mul hm2).mul hm3
  refine ⟨hmonic, ?_⟩
  rw [upperSubsetPoly, Polynomial.natDegree_mul (hm1.mul hm2).ne_zero hm3.ne_zero,
    Polynomial.natDegree_mul hm1.ne_zero hm2.ne_zero,
    Polynomial.natDegree_X_sub_C, (Polynomial.monic_X_sub_C (t 0)).natDegree_pow (d - 2 * S.card),
    Polynomial.natDegree_X_sub_C, mul_one,
    Polynomial.natDegree_prod_of_monic S _ (fun j _ =>
      (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _))]
  have hdeg_pair (j : Fin (N + 1)) :
      ((Polynomial.X - Polynomial.C (t j)) * (Polynomial.X - Polynomial.C (t j))).natDegree = 2 := by
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C _).ne_zero
      (Polynomial.monic_X_sub_C _).ne_zero, Polynomial.natDegree_X_sub_C]
  simp only [hdeg_pair, Finset.sum_const, smul_eq_mul]
  omega

theorem upperSubsetFunctional_eval_momentCurve {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) (hS : S.card ≤ d / 2) (x : ℝ) :
    upperSubsetFunctional d t S (momentCurve (d + 1) x) =
      (upperSubsetPoly d t S).coeff 0 - (upperSubsetPoly d t S).eval x := by
  obtain ⟨_, hdeg⟩ := upperSubsetPoly_monic_and_natDegree d t S hS
  have heval := Polynomial.eval_eq_sum_range' (p := upperSubsetPoly d t S)
    (n := (d + 1) + 1) (by omega) x
  rw [Finset.sum_range_succ'] at heval
  simp only [pow_zero, mul_one] at heval
  have hl : upperSubsetFunctional d t S (momentCurve (d + 1) x) =
      -(∑ j ∈ Finset.range (d + 1), (upperSubsetPoly d t S).coeff (j + 1) * x ^ (j + 1)) := by
    simp only [upperSubsetFunctional, neg_apply, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, momentCurve, smul_eq_mul, neg_inj]
    exact Fin.sum_univ_eq_sum_range
      (fun j => (upperSubsetPoly d t S).coeff (j + 1) * x ^ (j + 1)) (d + 1)
  rw [hl]
  linarith

theorem upperSubsetFunctional_neg_topBasis {N : ℕ} (d : ℕ) (t : Fin (N + 1) → ℝ)
    (S : Finset (Fin (N + 1))) (hS : S.card ≤ d / 2) :
    upperSubsetFunctional d t S (-Pi.single (Fin.last d) (1 : ℝ)) = 1 := by
  obtain ⟨hmonic, hdeg⟩ := upperSubsetPoly_monic_and_natDegree d t S hS
  rw [map_neg, upperSubsetFunctional, neg_apply, neg_neg, sum_apply]
  rw [Finset.sum_eq_single (Fin.last d)]
  · simp only [smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one, Fin.val_last]
    rw [← hdeg]
    exact hmonic.leadingCoeff
  · intro j _ hj
    simp only [smul_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem upperSubsetFunctional_visibilityDirection (d s : ℕ)
    (t : Fin (s + d + 1) → ℝ) (c : ℕ → ℝ)
    (S : Finset (Fin (s + d + 1))) (hS : S.card ≤ d / 2)
    (h0 : (upperSubsetPoly d t S).coeff 0 = 0) :
    upperSubsetFunctional d t S (visibilityDirection d s t c) =
      1 - ∑ k ∈ Finset.Icc 1 (d / 2), c k *
        ∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (upperSubsetPoly d t S).eval (t b) := by
  rw [visibilityDirection, map_add, upperSubsetFunctional_neg_topBasis d t S hS, map_sum]
  have hsum : (∑ k ∈ Finset.Icc 1 (d / 2),
      upperSubsetFunctional d t S (c k • ∑ b ∈ degreeSampleSet d s k,
        (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) • momentCurve (d + 1) (t b))) =
      -(∑ k ∈ Finset.Icc 1 (d / 2), c k *
        ∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (upperSubsetPoly d t S).eval (t b)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, map_sum, smul_eq_mul]
    have hinner : (∑ b ∈ degreeSampleSet d s k,
        upperSubsetFunctional d t S
          ((∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) • momentCurve (d + 1) (t b))) =
        -(∑ b ∈ degreeSampleSet d s k,
          (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
            (upperSubsetPoly d t S).eval (t b)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [map_smul, smul_eq_mul, upperSubsetFunctional_eval_momentCurve d t S hS (t b),
        h0, zero_sub, mul_neg]
    rw [hinner, mul_neg]
  rw [hsum, sub_eq_add_neg]

/-- Billera–Lee Section 7 Constructive Visibility Theorem:
For any compressed multicomplex `M` on `s` variables of degree `≤ d / 2` with `0 ∈ M`, there exist
strictly increasing cyclic parameters `t : Fin (s + d + 1) → ℝ` with `t 0 = 0` and an exterior point
`zStar : Fin (d + 1) → ℝ` such that every exposed facet `𝒢` of the `(d + 1)`-dimensional cyclic
polytope `P = conv {momentCurve (d + 1) (t i)}` is supported by a linear functional `(φ, α)` on `P`
for which `zStar` is strictly beyond `𝒢` (`α < φ zStar`) if and only if `𝒢` is one of the shelled
paired facets `fullPairedFacet d s u` with `u ∈ compressedWords (d / 2) s M`, and strictly beneath
`𝒢` (`φ zStar < α`) otherwise; moreover, every subset `S` of size `≤ d / 2` is supported on `P`
by a linear functional `(ψ, β)` with `ψ zStar < β`. -/
theorem exists_section7_visibility_point (d s : ℕ) (hd : 2 ≤ d) (hs : 1 ≤ s)
    (M : Finset (Fin s →₀ ℕ)) (h0M : (0 : Fin s →₀ ℕ) ∈ M)
    (hdiv : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ, g ≤ f → g ∈ M)
    (hinit : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ,
      g.degree = f.degree → MacaulayCompressed.colexLT g f → g ∈ M) :
    ∃ (t : Fin (s + d + 1) → ℝ) (zStar : Fin (d + 1) → ℝ),
      t 0 = 0 ∧ StrictMono t ∧
      let P := convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))
      let W := compressedWords (d / 2) s M
      (∀ 𝒢 : Set (Fin (d + 1) → ℝ), 𝒢.Nonempty → IsExposed ℝ P 𝒢 →
        Module.finrank ℝ (affineSpan ℝ 𝒢).direction = d →
        ∃ (φ : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ),
          (∀ y ∈ P, φ y ≤ α) ∧
          (∀ y ∈ P, y ∈ 𝒢 ↔ φ y = α) ∧
          ((∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → α < φ zStar) ∧
          ((¬ ∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → φ zStar < α)) ∧
      (∀ S : Finset (Fin (s + d + 1)), S.card ≤ d / 2 →
        ∃ (ψ : StrongDual ℝ (Fin (d + 1) → ℝ)) (β : ℝ),
          (∀ y ∈ P, ψ y ≤ β) ∧
          (∀ i ∈ S, ψ (momentCurve (d + 1) (t i)) = β) ∧
          ψ zStar < β) := by
  classical
  obtain ⟨t, ht0, ht, hΨ_zero, hΨ_pos, hΨ_mono⟩ := exists_billera_lee_parameters d s hd
  let Ψ : ℕ → (Fin (d / 2) → ℕ) → ℝ := fun k u =>
    ∑ b ∈ degreeSampleSet d s k,
      (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
        (∏ j ∈ fullPairedFacet d s u, (t b - t j))
  obtain ⟨c, hc_nonneg, hSW, hSU, _⟩ :=
    exists_separating_coefficients_upto d s M h0M hdiv hinit Ψ
      hΨ_zero hΨ_pos hΨ_mono (d / 2) le_rfl
  let v := visibilityDirection d s t c
  let nonZeroFacets : Finset (Finset (Fin (s + d + 1))) :=
    (Finset.univ : Finset (Finset (Fin (s + d + 1)))).filter
      (fun F => (0 : Fin (s + d + 1)) ∉ F)
  let nonZeroSubsets : Finset (Finset (Fin (s + d + 1))) :=
    (Finset.univ : Finset (Finset (Fin (s + d + 1)))).filter
      (fun S => (upperSubsetPoly d t S).coeff 0 ≠ 0)
  let E : Finset ℝ := insert 1
    ((nonZeroFacets.image (fun F =>
      |(cyclicRootPoly t F).coeff 0| / (|cyclicFacetFunctional d t F v| + 1))) ∪
     (nonZeroSubsets.image (fun S =>
      |(upperSubsetPoly d t S).coeff 0| / (|upperSubsetFunctional d t S v| + 1))))
  have hE_ne : E.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  have hE_pos : ∀ x ∈ E, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx_union
    · exact zero_lt_one
    · rcases Finset.mem_union.mp hx_union with hx_img | hx_img
      · rcases Finset.mem_image.mp hx_img with ⟨F, hF, rfl⟩
        have h0F : (0 : Fin (s + d + 1)) ∉ F := (Finset.mem_filter.mp hF).2
        have hcoeff_ne : (cyclicRootPoly t F).coeff 0 ≠ 0 := by
          rw [cyclicRootPoly_coeff_zero]
          apply Finset.prod_ne_zero_iff.mpr
          intro j hjF
          have hj0 : (0 : Fin (s + d + 1)) < j :=
            lt_of_le_of_ne (Fin.zero_le j) (fun h => h0F (h ▸ hjF))
          have htj : 0 < t j := ht0 ▸ ht hj0
          linarith
        have hnum : 0 < |(cyclicRootPoly t F).coeff 0| := abs_pos.mpr hcoeff_ne
        have hden : 0 < |cyclicFacetFunctional d t F v| + 1 := by
          have := abs_nonneg (cyclicFacetFunctional d t F v)
          linarith
        exact div_pos hnum hden
      · rcases Finset.mem_image.mp hx_img with ⟨S, hS, rfl⟩
        have hcoeff_ne : (upperSubsetPoly d t S).coeff 0 ≠ 0 := (Finset.mem_filter.mp hS).2
        have hnum : 0 < |(upperSubsetPoly d t S).coeff 0| := abs_pos.mpr hcoeff_ne
        have hden : 0 < |upperSubsetFunctional d t S v| + 1 := by
          have := abs_nonneg (upperSubsetFunctional d t S v)
          linarith
        exact div_pos hnum hden
  let ε : ℝ := E.min' hE_ne / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have hmin_pos : 0 < E.min' hE_ne := hE_pos _ (Finset.min'_mem E hE_ne)
    linarith
  have hε_small (F : Finset (Fin (s + d + 1))) (h0F : (0 : Fin (s + d + 1)) ∉ F) :
      ε * |cyclicFacetFunctional d t F v| < |(cyclicRootPoly t F).coeff 0| := by
    have hmem : |(cyclicRootPoly t F).coeff 0| / (|cyclicFacetFunctional d t F v| + 1) ∈ E :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ F, h0F⟩, rfl⟩))
    have hmin_le := Finset.min'_le E _ hmem
    have hmin_pos : 0 < E.min' hE_ne := hE_pos _ (Finset.min'_mem E hE_ne)
    have hε_lt : ε < |(cyclicRootPoly t F).coeff 0| / (|cyclicFacetFunctional d t F v| + 1) := by
      dsimp [ε]
      linarith
    have hden_pos : 0 < |cyclicFacetFunctional d t F v| + 1 := by
      have := abs_nonneg (cyclicFacetFunctional d t F v)
      linarith
    have hmul := (lt_div_iff₀ hden_pos).mp hε_lt
    nlinarith [abs_nonneg (cyclicFacetFunctional d t F v)]
  have hε_small_subset (S : Finset (Fin (s + d + 1)))
      (h0S : (upperSubsetPoly d t S).coeff 0 ≠ 0) :
      ε * |upperSubsetFunctional d t S v| < |(upperSubsetPoly d t S).coeff 0| := by
    have hmem : |(upperSubsetPoly d t S).coeff 0| / (|upperSubsetFunctional d t S v| + 1) ∈ E :=
      Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, h0S⟩, rfl⟩))
    have hmin_le := Finset.min'_le E _ hmem
    have hmin_pos : 0 < E.min' hE_ne := hE_pos _ (Finset.min'_mem E hE_ne)
    have hε_lt : ε < |(upperSubsetPoly d t S).coeff 0| / (|upperSubsetFunctional d t S v| + 1) := by
      dsimp [ε]
      linarith
    have hden_pos : 0 < |upperSubsetFunctional d t S v| + 1 := by
      have := abs_nonneg (upperSubsetFunctional d t S v)
      linarith
    have hmul := (lt_div_iff₀ hden_pos).mp hε_lt
    nlinarith [abs_nonneg (upperSubsetFunctional d t S v)]
  let zStar : Fin (d + 1) → ℝ := ε • v
  refine ⟨t, zStar, ht0, ht, ?_⟩
  intro P W
  refine ⟨?_, ?_⟩
  swap
  · intro S hS
    let qS : Polynomial ℝ := upperSubsetPoly d t S
    let lS : StrongDual ℝ (Fin (d + 1) → ℝ) := upperSubsetFunctional d t S
    refine ⟨-lS, -qS.coeff 0, ?_, ?_, ?_⟩
    · have hsub : Set.range (fun i => momentCurve (d + 1) (t i)) ⊆
          {y : Fin (d + 1) → ℝ | (-lS) y ≤ -qS.coeff 0} := by
        rintro _ ⟨i, rfl⟩
        change -lS (momentCurve (d + 1) (t i)) ≤ -qS.coeff 0
        rw [upperSubsetFunctional_eval_momentCurve d t S hS (t i)]
        have hle := upperSubsetPoly_eval_nonpos d t ht S i
        linarith
      have hconv : Convex ℝ {y : Fin (d + 1) → ℝ | (-lS) y ≤ -qS.coeff 0} := by
        intro x hx y hy a b ha hb hab
        change (-lS) x ≤ -qS.coeff 0 at hx
        change (-lS) y ≤ -qS.coeff 0 at hy
        change (-lS) (a • x + b • y) ≤ -qS.coeff 0
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        calc
          a * (-lS) x + b * (-lS) y ≤ a * (-qS.coeff 0) + b * (-qS.coeff 0) :=
            add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
          _ = -qS.coeff 0 := by rw [← add_mul, hab, one_mul]
      exact convexHull_min hsub hconv
    · intro i hiS
      change -lS (momentCurve (d + 1) (t i)) = -qS.coeff 0
      rw [upperSubsetFunctional_eval_momentCurve d t S hS (t i),
        upperSubsetPoly_eval_eq_zero_of_mem d t S hiS, sub_zero]
    · by_cases hqS0 : qS.coeff 0 = 0
      · rw [hqS0, neg_zero]
        change -lS (ε • v) < 0
        rw [map_smul, smul_eq_mul, neg_lt_zero]
        apply mul_pos hε_pos
        change 0 < upperSubsetFunctional d t S v
        rw [upperSubsetFunctional_visibilityDirection d s t c S hS hqS0]
        have hsum_nonpos : (∑ k ∈ Finset.Icc 1 (d / 2), c k *
            ∑ b ∈ degreeSampleSet d s k,
              (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
                (upperSubsetPoly d t S).eval (t b)) ≤ 0 := by
          apply Finset.sum_nonpos
          intro k _
          apply mul_nonpos_of_nonneg_of_nonpos (hc_nonneg k)
          apply Finset.sum_nonpos
          intro b _
          apply mul_nonpos_of_nonneg_of_nonpos
          · apply Finset.prod_nonneg
            intro j hj
            have hbj : b < j := (Finset.mem_filter.mp hj).2
            have hj0 : (0 : Fin (s + d + 1)) < j := lt_of_le_of_lt (Fin.zero_le b) hbj
            have htj : 0 < t j := ht0 ▸ ht hj0
            exact pow_nonneg htj.le d
          · exact upperSubsetPoly_eval_nonpos d t ht S b
        linarith
      · have hqS0_le : qS.coeff 0 ≤ 0 := by
          have h := upperSubsetPoly_eval_nonpos d t ht S 0
          rwa [ht0, ← Polynomial.coeff_zero_eq_eval_zero] at h
        have hqS0_neg : qS.coeff 0 < 0 := lt_of_le_of_ne hqS0_le hqS0
        have hsmall := hε_small_subset S hqS0
        rw [abs_of_neg hqS0_neg] at hsmall
        change -lS (ε • v) < -qS.coeff 0
        rw [map_smul, smul_eq_mul]
        have hle : -lS v ≤ |lS v| := neg_le_abs (lS v)
        nlinarith
  intro 𝒢 h𝒢ne h𝒢exp h𝒢dim
  obtain ⟨hFcard, h𝒢hull, hl_eval, hbranches⟩ :=
    cyclic_facet_support_characterization d s hs t ht 𝒢 h𝒢ne h𝒢exp h𝒢dim
  let F : Finset (Fin (s + d + 1)) :=
    Finset.univ.filter (fun i => momentCurve (d + 1) (t i) ∈ 𝒢)
  let q : Polynomial ℝ := cyclicRootPoly t F
  let l : StrongDual ℝ (Fin (d + 1) → ℝ) := cyclicFacetFunctional d t F
  have hF_of_hull (u : Fin (d / 2) → ℕ) (huW : u ∈ W)
      (hEq : 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
        (fullPairedFacet d s u : Set (Fin (s + d + 1)))) ) :
      F = fullPairedFacet d s u := by
    obtain ⟨hbu, hmu, _⟩ := (mem_compressedWords M u).mp huW
    ext i
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hEq]
    exact momentCurve_mem_fullPairedFacet_hull_iff d s t ht0 ht u hmu hbu i
  rcases hbranches with ⟨hq_pos, hl_le, hl_iff⟩ | ⟨hq_neg, hl_le, hl_iff⟩
  · -- Lower facet branch: supported by `(l, q.coeff 0)`
    refine ⟨l, q.coeff 0, hl_le, hl_iff, ?_, ?_⟩
    · rintro ⟨u, huW, hEq⟩
      have hFu : F = fullPairedFacet d s u := hF_of_hull u huW hEq
      have h0F : (0 : Fin (s + d + 1)) ∈ F := hFu ▸ zero_mem_fullPairedFacet d s u
      have hq0 : q.coeff 0 = 0 := cyclicRootPoly_coeff_zero_of_zero_mem t ht0 F h0F
      rw [hq0]
      change 0 < l (ε • v)
      rw [map_smul, smul_eq_mul]
      apply mul_pos hε_pos
      change 0 < cyclicFacetFunctional d t F v
      rw [cyclicFacetFunctional_visibilityDirection d s t ht0 c F hFcard h0F]
      have hΨ_rewrite : (∑ k ∈ Finset.Icc 1 (d / 2), c k *
          ∑ b ∈ degreeSampleSet d s k,
            (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
              (cyclicRootPoly t F).eval (t b)) =
          ∑ k ∈ Finset.Icc 1 (d / 2), c k * Ψ k u := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        apply Finset.sum_congr rfl
        intro b _
        rw [hFu, cyclicRootPoly_eval]
      rw [hΨ_rewrite]
      have hSW_u : ∑ k ∈ Finset.Icc 1 (d / 2), c k * Ψ k u < 1 := hSW u huW
      linarith
    · intro hnotW
      by_cases h0F : (0 : Fin (s + d + 1)) ∈ F
      · have heven : ∀ i : Fin (s + d + 1), i ∉ F → Even ((F.filter (fun j => i < j)).card) := by
          intro i hiF
          rw [← (prod_sub_pos_iff_even_gt t ht F i hiF).2, ← cyclicRootPoly_eval]
          exact hq_pos i hiF
        obtain ⟨w, hmw, hbw, hFw⟩ := exists_word_of_even_above d s F hFcard h0F heven
        have hwU : w ∈ boundedMonotoneWords (d / 2) s :=
          (mem_boundedMonotoneWords w).mpr ⟨hbw, hmw⟩
        have hw_notW : w ∉ W := by
          intro hwW
          apply hnotW
          refine ⟨w, hwW, ?_⟩
          rw [← hFw]
          exact h𝒢hull
        have hq0 : q.coeff 0 = 0 := cyclicRootPoly_coeff_zero_of_zero_mem t ht0 F h0F
        rw [hq0]
        change l (ε • v) < 0
        rw [map_smul, smul_eq_mul]
        apply mul_neg_of_pos_of_neg hε_pos
        change cyclicFacetFunctional d t F v < 0
        rw [cyclicFacetFunctional_visibilityDirection d s t ht0 c F hFcard h0F]
        have hΨ_rewrite : (∑ k ∈ Finset.Icc 1 (d / 2), c k *
            ∑ b ∈ degreeSampleSet d s k,
              (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
                (cyclicRootPoly t F).eval (t b)) =
            ∑ k ∈ Finset.Icc 1 (d / 2), c k * Ψ k w := by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          apply Finset.sum_congr rfl
          intro b _
          rw [hFw, cyclicRootPoly_eval]
        rw [hΨ_rewrite]
        have hSU_w : 1 < ∑ k ∈ Finset.Icc 1 (d / 2), c k * Ψ k w :=
          hSU w hwU hw_notW (wordDegree_le w)
        linarith
      · have hq0_pos : 0 < q.coeff 0 := by
          have h := hq_pos 0 h0F
          rwa [ht0, ← Polynomial.coeff_zero_eq_eval_zero] at h
        have hsmall := hε_small F h0F
        rw [abs_of_pos hq0_pos] at hsmall
        change l (ε • v) < q.coeff 0
        rw [map_smul, smul_eq_mul]
        have hle : l v ≤ |l v| := le_abs_self (l v)
        nlinarith
  · -- Upper facet branch: supported by `(-l, -q.coeff 0)`
    refine ⟨-l, -q.coeff 0, hl_le, hl_iff, ?_, ?_⟩
    · rintro ⟨u, huW, hEq⟩
      have hFu : F = fullPairedFacet d s u := hF_of_hull u huW hEq
      obtain ⟨hbu, hmu, _⟩ := (mem_compressedWords M u).mp huW
      have hcompl_ne : (Finset.univ \ F).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hFcard]
        omega
      obtain ⟨iStar, hiStar⟩ := hcompl_ne
      have hiStarF : iStar ∉ F := (Finset.mem_sdiff.mp hiStar).2
      have h1 : q.eval (t iStar) < 0 := hq_neg iStar hiStarF
      have h2 : 0 < q.eval (t iStar) := by
        change 0 < (cyclicRootPoly t F).eval (t iStar)
        rw [hFu]
        exact fullPairedFacet_rootPoly_pos_of_notMem d s t ht u hmu hbu iStar (hFu ▸ hiStarF)
      linarith
    · intro _
      by_cases h0F : (0 : Fin (s + d + 1)) ∈ F
      · have hq0 : q.coeff 0 = 0 := cyclicRootPoly_coeff_zero_of_zero_mem t ht0 F h0F
        rw [hq0, neg_zero]
        change -l (ε • v) < 0
        rw [map_smul, smul_eq_mul, neg_lt_zero]
        apply mul_pos hε_pos
        change 0 < cyclicFacetFunctional d t F v
        rw [cyclicFacetFunctional_visibilityDirection d s t ht0 c F hFcard h0F]
        have hsum_nonpos : (∑ k ∈ Finset.Icc 1 (d / 2), c k *
            ∑ b ∈ degreeSampleSet d s k,
              (∏ j ∈ Finset.univ.filter (fun j => b < j), t j ^ d) *
                (cyclicRootPoly t F).eval (t b)) ≤ 0 := by
          apply Finset.sum_nonpos
          intro k _
          apply mul_nonpos_of_nonneg_of_nonpos (hc_nonneg k)
          apply Finset.sum_nonpos
          intro b _
          apply mul_nonpos_of_nonneg_of_nonpos
          · apply Finset.prod_nonneg
            intro j hj
            have hbj : b < j := (Finset.mem_filter.mp hj).2
            have hj0 : (0 : Fin (s + d + 1)) < j := lt_of_le_of_lt (Fin.zero_le b) hbj
            have htj : 0 < t j := ht0 ▸ ht hj0
            exact pow_nonneg htj.le d
          · by_cases hbF : b ∈ F
            · rw [(cyclicRootPoly_eval_eq_zero_iff t ht F b).mpr hbF]
            · exact (hq_neg b hbF).le
        linarith
      · have hq0_neg : q.coeff 0 < 0 := by
          have h := hq_neg 0 h0F
          rwa [ht0, ← Polynomial.coeff_zero_eq_eval_zero] at h
        have hsmall := hε_small F h0F
        rw [abs_of_neg hq0_neg] at hsmall
        change -l (ε • v) < -q.coeff 0
        rw [map_smul, smul_eq_mul]
        have hle : -l v ≤ |l v| := neg_le_abs (l v)
        nlinarith

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextVisibilityConstruct.lean

-- BEGIN StellarCone.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarCone

/-- Adding a point outside the common support plane of an independent family
preserves affine independence. -/
theorem affineIndependent_cons {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (y : Fin d → ℝ) (hy : a < φ y) :
    AffineIndependent ℝ (Fin.cons (α := fun _ => Fin d → ℝ) y v) := by
  let e : {i : Fin (n + 1) // i ≠ 0} ↪ Fin n :=
    ⟨fun i => i.val.pred i.property, fun i j h => Subtype.ext (Fin.pred_inj.mp h)⟩
  have hbase : AffineIndependent ℝ
      (fun i : {i : Fin (n + 1) // i ≠ 0} =>
        (Fin.cons (α := fun _ => Fin d → ℝ) y v : Fin (n + 1) → Fin d → ℝ) i.val) := by
    have heq : (fun i : {i : Fin (n + 1) // i ≠ 0} =>
        (Fin.cons (α := fun _ => Fin d → ℝ) y v : Fin (n + 1) → Fin d → ℝ) i.val) = v ∘ e := by
      funext i
      change Fin.cons (α := fun _ => Fin d → ℝ) y v i.val = v (i.val.pred i.property)
      conv_lhs => rw [← Fin.succ_pred i.val i.property]
      rfl
    rw [heq]
    exact hv.comp_embedding e
  apply hbase.affineIndependent_of_notMem_span
  let H : AffineSubspace ℝ (Fin d → ℝ) :=
    (affineSpan ℝ ({a} : Set ℝ)).comap φ.toLinearMap.toAffineMap
  have hH : (Fin.cons (α := fun _ => Fin d → ℝ) y v) '' {i : Fin (n + 1) | i ≠ 0} ⊆ H := by
    rintro x ⟨i, hi, rfl⟩
    have hval : φ (Fin.cons (α := fun _ => Fin d → ℝ) y v i) = a := by
      rw [← Fin.succ_pred i hi]
      exact hlevel _
    simpa [H, AffineSubspace.mem_comap] using hval
  intro hmem
  have hspan := (affineSpan_le_of_subset_coe hH) hmem
  have heq : φ y = a := by simpa [H, AffineSubspace.mem_comap] using hspan
  exact hy.ne heq.symm

/-- Every cone over a subset of the base vertices is a simplex of the expected size. -/
theorem cone_simplex {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (y : Fin d → ℝ) (hy : a < φ y)
    (s : Finset (Fin n)) :
    ∃ w : Fin (s.card + 1) → Fin d → ℝ,
      AffineIndependent ℝ w ∧
        convexHull ℝ (insert y (v '' (s : Set (Fin n)))) = convexHull ℝ (Set.range w) := by
  let e : Fin s.card ≃ ↥s := Fintype.equivOfCardEq (by simp)
  let q : Fin s.card → Fin d → ℝ := fun i => v (e i).val
  have hq : AffineIndependent ℝ q :=
    (hv.comp_embedding ⟨Subtype.val, Subtype.val_injective⟩).comp_embedding e.toEmbedding
  have hqr : Set.range q = v '' (s : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).val, (e i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      exact ⟨j, by simp [q, hj]⟩
  refine ⟨Fin.cons y q, affineIndependent_cons q hq φ a (fun i => hlevel _) y hy, ?_⟩
  rw [Fin.range_cons, hqr]

/-- The cone over `s` has affine dimension exactly `s.card`, including the empty base. -/
theorem cone_finrank {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (y : Fin d → ℝ) (hy : a < φ y)
    (s : Finset (Fin n)) :
    Module.finrank ℝ (affineSpan ℝ
      (convexHull ℝ (insert y (v '' (s : Set (Fin n)))))).direction = s.card := by
  obtain ⟨w, hw, heq⟩ := cone_simplex v hv φ a hlevel y hy s
  rw [heq, affineSpan_convexHull, direction_affineSpan]
  exact hw.finrank_vectorSpan (Fintype.card_fin _)

/-- Nonempty subsets of an independent family have one fewer affine dimension than points. -/
theorem subset_finrank {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (s : Finset (Fin n)) (hs : s.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (v '' (s : Set (Fin n))))).direction + 1 =
      s.card := by
  have : Nonempty ↥s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hi : AffineIndependent ℝ (fun i : ↥s => v i.val) :=
    hv.comp_embedding (⟨Subtype.val, Subtype.val_injective⟩ : ↥s ↪ Fin n)
  have hrange : Set.range (fun i : ↥s => v i.val) = v '' (s : Set (Fin n)) := by
    ext x
    simp
  rw [affineSpan_convexHull, direction_affineSpan, ← hrange]
  simpa only [Fintype.card_coe] using hi.finrank_vectorSpan_add_one


/-- An apex strictly beyond a supporting hyperplane adds no points of the old
convex set to a cone over a subset of that hyperplane. -/
theorem convexHull_insert_inter_eq_of_supporting {d : ℕ}
    {P A : Set (Fin d → ℝ)} (hP : Convex ℝ P) (hAP : A ⊆ P)
    (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ c) (hlevel : ∀ x ∈ A, φ x = c)
    (y : Fin d → ℝ) (hy : c < φ y) :
    convexHull ℝ (insert y A) ∩ P = convexHull ℝ A := by
  have hyP : y ∉ P := fun h => (not_le_of_gt hy) (hbound y h)
  have hsub : convexHull ℝ A ⊆ P := convexHull_min hAP hP
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hA : A.Nonempty
    · have hconst : ∀ z ∈ convexHull ℝ A, φ z = c := by
        exact convexHull_min hlevel ((convex_singleton c).linear_preimage φ)
      rcases hx with ⟨hx, hxP⟩
      rw [convexHull_insert hA, mem_convexJoin] at hx
      rcases hx with ⟨y', hy', z, hz, a, b, ha, hb, hab, hx⟩
      obtain rfl : y' = y := hy'
      subst x
      have hφ := hbound _ hxP
      simp only [map_add, map_smul, smul_eq_mul, hconst z hz] at hφ
      have ha0 : a = 0 := by
        apply le_antisymm _ ha
        by_contra! hapos
        nlinarith [mul_pos hapos (sub_pos.mpr hy), congrArg (fun t : ℝ => t * c) hab]
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hz
    · have hA0 : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      have hxy : x = y := by simpa [hA0] using hx.1
      exact False.elim (hyP (hxy ▸ hx.2))
  · intro x hx
    exact ⟨convexHull_mono (Set.subset_insert y A) hx, hsub hx⟩

/-- The cone over selected old exposed vertices has exactly those old exposed
vertices when the apex lies strictly beyond their supporting hyperplane. -/
theorem stellarCone_old_exposed_vertices_of_supporting {d : ℕ}
    {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (v : Fin d → Fin d → ℝ)
    (hv : ∀ i, IsExposed ℝ P {v i})
    (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ c) (hlevel : ∀ i, φ (v i) = c)
    (y : Fin d → ℝ) (hy : c < φ y) (s : Finset (Fin d)) :
    convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
      {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d)) := by
  have hAP : v '' (s : Set (Fin d)) ⊆ P := by
    rintro _ ⟨i, _, rfl⟩
    exact (hv i).subset (Set.mem_singleton _)
  have hconv := convexHull_insert_inter_eq_of_supporting hP hAP φ c hbound
    (by rintro _ ⟨i, _, rfl⟩; exact hlevel i) y hy
  apply Set.Subset.antisymm
  · intro x hx
    have hxP := hx.2.subset (Set.mem_singleton _)
    have hxHull : x ∈ convexHull ℝ (v '' (s : Set (Fin d))) := by
      rw [← hconv]
      exact ⟨hx.1, hxP⟩
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_min hAP hP) ⟨hxHull, hx.2.isExtreme.mem_extremePoints⟩)
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩), hv i⟩


end Grunbaum2003.StellarCone
-- END StellarCone.lean

-- BEGIN StellarPyramidGeometry.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

/-- An apex beyond one supporting plane and beneath every other plane adds
exactly the pyramid over the chosen face. The family of other planes may be infinite. -/
theorem convexHull_insert_eq_union_pyramid
    {d : ℕ} {ι : Type*} (P : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (hPne : P.Nonempty) (y : Fin d → ℝ)
    (hyφ : a < φ y) (hyψ : ∀ j, ψ j y ≤ c j) :
    convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a}) := by
  have hmem (x : Fin d → ℝ) : x ∈ P ↔ φ x ≤ a ∧ ∀ j, ψ j x ≤ c j := by
    rw [hP]
    rfl
  have hconv : Convex ℝ P := by
    intro x hx z hz u v hu hv huv
    rw [hmem] at hx hz ⊢
    constructor
    · simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * φ x + v * φ z ≤ u * a + v * a :=
          add_le_add (mul_le_mul_of_nonneg_left hx.1 hu)
            (mul_le_mul_of_nonneg_left hz.1 hv)
        _ = a := by rw [← add_mul, huv, one_mul]
    · intro j
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * ψ j x + v * ψ j z ≤ u * c j + v * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 j) hu)
            (mul_le_mul_of_nonneg_left (hz.2 j) hv)
        _ = c j := by rw [← add_mul, huv, one_mul]
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    right
    rw [convexHull_insert hPne, hconv.convexHull_eq, mem_convexJoin] at hx
    obtain ⟨y', hy', z, hz, u, v, hu, hv, huv, hrep⟩ := hx
    have heqy : y' = y := hy'
    subst y'
    have hzφ := ((hmem z).mp hz).1
    have hzψ := ((hmem z).mp hz).2
    have hxψ (j : ι) : ψ j x ≤ c j := by
      rw [← hrep]
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * ψ j y + v * ψ j z ≤ u * c j + v * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hyψ j) hu)
            (mul_le_mul_of_nonneg_left (hzψ j) hv)
        _ = c j := by rw [← add_mul, huv, one_mul]
    have hxφ : a < φ x := by
      by_contra! h
      exact hxP ((hmem x).mpr ⟨h, hxψ⟩)
    have hD : 0 < φ y - φ z := by linarith
    have hD0 : φ y - φ z ≠ 0 := ne_of_gt hD
    let r : ℝ := (a - φ z) / (φ y - φ z)
    let s : ℝ := (φ y - a) / (φ y - φ z)
    have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hzφ) hD.le
    have hs : 0 < s := div_pos (sub_pos.mpr hyφ) hD
    have hrs : r + s = 1 := by
      dsimp [r, s]
      field_simp
      ring
    let w : Fin d → ℝ := r • y + s • z
    have hwφ : φ w = a := by
      dsimp [w]
      simp only [map_add, map_smul, smul_eq_mul]
      dsimp [r, s]
      field_simp
      ring
    have hwψ (j : ι) : ψ j w ≤ c j := by
      dsimp [w]
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        r * ψ j y + s * ψ j z ≤ r * c j + s * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hyψ j) hr)
            (mul_le_mul_of_nonneg_left (hzψ j) hs.le)
        _ = c j := by rw [← add_mul, hrs, one_mul]
    have hw : w ∈ {x ∈ P | φ x = a} :=
      ⟨(hmem w).mpr ⟨hwφ.le, hwψ⟩, hwφ⟩
    have hvle : v ≤ s := by
      apply (le_div_iff₀ hD).mpr
      have hval := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at hval
      nlinarith [congrArg (fun q : ℝ => q * φ y) huv]
    have hvs : 0 ≤ v / s := div_nonneg hv hs.le
    have hvs1 : v / s ≤ 1 := (div_le_one hs).mpr hvle
    have hwHull : w ∈ convexHull ℝ (insert y {x ∈ P | φ x = a}) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw)
    have hyHull : y ∈ convexHull ℝ (insert y {x ∈ P | φ x = a}) :=
      subset_convexHull ℝ _ (Set.mem_insert _ _)
    have heq : (1 - v / s) • y + (v / s) • w = x := by
      rw [← hrep]
      dsimp [w]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hs0 : s ≠ 0 := ne_of_gt hs
      field_simp
      nlinarith [congrArg (fun q : ℝ => q * (v * y i)) hrs,
        congrArg (fun q : ℝ => q * (s * y i)) huv]
    rw [← heq]
    exact (convex_convexHull ℝ _) hyHull hwHull
      (sub_nonneg.mpr hvs1) hvs (by ring)
  · rintro x (hx | hx)
    · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx)
    · exact convexHull_mono (by
        intro z hz
        rcases hz with rfl | hz
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hz.1) hx

end Grunbaum2003



set_option autoImplicit false
open scoped Classical Topology

namespace Grunbaum2003

/-- A proper supporting plane through an apex that violates only one of finitely
many defining inequalities meets the old polytope only in that chosen facet. -/
theorem support_through_apex_meets_chosen_face
    {d : ℕ} {ι : Type*} [Finite ι] (P : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j)
    (θ : (Fin d → ℝ) →L[ℝ] ℝ) (hθ : θ ≠ 0)
    (hmax : ∀ x ∈ P, θ x ≤ θ y) :
    ∀ x ∈ P, θ x = θ y → φ x = a := by
  intro x hx hθx
  have hxmem : φ x ≤ a ∧ ∀ j, ψ j x ≤ c j := by simpa [hP] using hx
  by_contra hxa
  have hxφ : φ x < a := lt_of_le_of_ne hxmem.1 hxa
  have hD : 0 < φ y - φ x := by linarith
  have hD0 : φ y - φ x ≠ 0 := ne_of_gt hD
  let s : ℝ := (a - φ x) / (2 * (φ y - φ x))
  have hs : 0 < s := div_pos (sub_pos.mpr hxφ) (by positivity)
  have hs1 : s < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * (φ y - φ x))).mpr
    linarith
  have hsD : s * (φ y - φ x) = (a - φ x) / 2 := by
    dsimp [s]
    field_simp
  let q : Fin d → ℝ := s • y + (1 - s) • x
  have hqφ : φ q < a := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [hsD]
  have hqψ (j : ι) : ψ j q < c j := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      s * ψ j y + (1 - s) * ψ j x < s * c j + (1 - s) * c j :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hyψ j) hs)
          (mul_le_mul_of_nonneg_left (hxmem.2 j) (by linarith))
      _ = c j := by ring
  have hqθ : θ q = θ y := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul, hθx]
    ring
  let U : Set (Fin d → ℝ) := {z | φ z < a ∧ ∀ j, ψ j z < c j}
  have hU : IsOpen U := by
    have hUeq : U = {z | φ z < a} ∩ ⋂ j, {z | ψ j z < c j} := by
      ext z
      simp [U]
    rw [hUeq]
    exact (isOpen_lt φ.continuous continuous_const).inter
      (isOpen_iInter_of_finite (fun j => isOpen_lt (ψ j).continuous continuous_const))
  have hqU : q ∈ U := ⟨hqφ, hqψ⟩
  have hmaxq : IsLocalMax (fun z => θ z) q := by
    filter_upwards [hU.mem_nhds hqU] with z hz
    have hzP : z ∈ P := by
      rw [hP]
      exact ⟨hz.1.le, fun j => (hz.2 j).le⟩
    simpa only [hqθ] using hmax z hzP
  exact hθ (hmaxq.hasFDerivAt_eq_zero θ.hasFDerivAt)

end Grunbaum2003


namespace Grunbaum2003

private lemma exposed_eq_level {d : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) {w : Fin d → ℝ} (hw : w ∈ P)
    (hmax : ∀ x ∈ P, φ x ≤ φ w) :
    φ.toExposed P = {x ∈ P | φ x = φ w} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hmax x hx.1) (hx.2 w hw)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun z hz => by rw [heq]; exact hmax z hz⟩

private lemma hull_bound {d : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hmax : ∀ x ∈ P, φ x ≤ c) {y : Fin d → ℝ} (hy : φ y ≤ c) :
    ∀ x ∈ convexHull ℝ (insert y P), φ x ≤ c := by
  apply convexHull_min
  · intro x hx
    rcases hx with rfl | hx
    · exact hy
    · exact hmax x hx
  · exact (convex_Iic c).linear_preimage φ.toLinearMap

/-- Adding an apex changes each support maximizer set according to its height
relative to the old support value. -/
theorem exposed_insert_trichotomy {d : ℕ} {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ) (hw : w ∈ P)
    (hmax : ∀ x ∈ P, φ x ≤ φ w) (y : Fin d → ℝ) :
    (φ y < φ w → φ.toExposed (convexHull ℝ (insert y P)) = φ.toExposed P) ∧
    (φ y = φ w → φ.toExposed (convexHull ℝ (insert y P)) =
      convexHull ℝ (insert y (φ.toExposed P))) ∧
    (φ w < φ y → φ.toExposed (convexHull ℝ (insert y P)) = {y}) := by
  have hrepr (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ (insert y P)) :
      ∃ z ∈ P, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
        a • y + b • z = x := by
    rw [convexHull_insert ⟨w, hw⟩, hP.convexHull_eq, mem_convexJoin] at hx
    rcases hx with ⟨y', hy', z, hz, a, b, ha, hb, hab, hx⟩
    obtain rfl : y' = y := hy'
    exact ⟨z, hz, a, b, ha, hb, hab, hx⟩
  have hwHull : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw)
  have hyHull : y ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro hy
    rw [exposed_eq_level φ hwHull (hull_bound φ (φ w) hmax hy.le),
      exposed_eq_level φ hw hmax]
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at heq'
      have hs : a * φ w + b * φ w = φ w := by rw [← add_mul, hab, one_mul]
      have ha0 : a = 0 := by
        apply le_antisymm _ ha
        by_contra! hapos
        have hgap := mul_pos hapos (sub_pos.mpr hy)
        have hgap' := mul_nonneg hb (sub_nonneg.mpr (hmax z hz))
        nlinarith
      have hb1 : b = 1 := by linarith
      have hxz : x = z := by simpa [ha0, hb1] using hrep.symm
      exact ⟨hxz ▸ hz, heq⟩
    · rintro ⟨hx, heq⟩
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx), heq⟩
  · intro hy
    rw [exposed_eq_level φ hwHull (hull_bound φ (φ w) hmax hy.le)]
    apply Set.Subset.antisymm
    · rintro x ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul, hy] at heq'
      have hs : a * φ w + b * φ w = φ w := by rw [← add_mul, hab, one_mul]
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        have hxy : x = y := by simpa [hb0, ha1] using hrep.symm
        rw [hxy]
        exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · have hzmax : φ z = φ w := by
          apply le_antisymm (hmax z hz)
          by_contra! hzlt
          have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hgap := mul_pos hbpos (sub_pos.mpr hzlt)
          nlinarith
        have hzF : z ∈ φ.toExposed P := by
          rw [exposed_eq_level φ hw hmax]
          exact ⟨hz, hzmax⟩
        rw [← hrep]
        exact (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hzF)) ha hb hab
    · have hsub : insert y (φ.toExposed P) ⊆
          {x ∈ convexHull ℝ (insert y P) | φ x = φ w} := by
        intro x hx
        rcases hx with rfl | hx
        · exact ⟨hyHull, hy⟩
        · exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
            le_antisymm (hmax x hx.1) (hx.2 w hw)⟩
      apply convexHull_min hsub
      exact (convex_convexHull ℝ _).inter
        ((convex_singleton (φ w)).linear_preimage φ.toLinearMap)
  · intro hy
    have hmaxY : ∀ x ∈ P, φ x ≤ φ y := fun x hx => (hmax x hx).trans hy.le
    rw [exposed_eq_level φ hyHull (hull_bound φ (φ y) hmaxY le_rfl)]
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at heq'
      have hs : a * φ y + b * φ y = φ y := by rw [← add_mul, hab, one_mul]
      have hb0 : b = 0 := by
        apply le_antisymm _ hb
        by_contra! hbpos
        have hgap := mul_pos hbpos (sub_pos.mpr (lt_of_le_of_lt (hmax z hz) hy))
        nlinarith
      have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hrep.symm
    · intro hx
      obtain rfl : x = y := hx
      exact ⟨hyHull, rfl⟩

end Grunbaum2003

namespace Grunbaum2003

/-- Every new nonempty proper exposed face is an old face, the apex, or a cone
whose base is an old exposed face contained in the chosen supporting plane. -/
theorem exposed_faces_of_pyramid_extension
    {d : ℕ} {ι : Type*} [Finite ι] (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j)
    (H : Set (Fin d → ℝ)) (hHne : H.Nonempty)
    (hH : IsExposed ℝ (convexHull ℝ (insert y P)) H)
    (hproper : H ≠ convexHull ℝ (insert y P)) :
    H = {y} ∨ IsExposed ℝ P H ∨
      ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
        G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G) := by
  obtain ⟨θ, hθH⟩ := hH hHne
  change H = θ.toExposed (convexHull ℝ (insert y P)) at hθH
  have hθ : θ ≠ 0 := by
    intro hz
    apply hproper
    simpa [hz, ContinuousLinearMap.toExposed] using hθH
  obtain ⟨w, hw, hmaxOn⟩ := hcompact.exists_isMaxOn hPne θ.continuous.continuousOn
  have hmax : ∀ x ∈ P, θ x ≤ θ w := fun _ hx => hmaxOn hx
  have hsplit := exposed_insert_trichotomy hconv θ w hw hmax y
  rcases lt_trichotomy (θ y) (θ w) with hlt | heq | hgt
  · right; left
    rw [hθH, hsplit.1 hlt]
    exact ContinuousLinearMap.toExposed.isExposed (l := θ)
  · right; right
    refine ⟨θ.toExposed P, ⟨w, hw, hmax⟩,
      ContinuousLinearMap.toExposed.isExposed (l := θ), ?_, hθH.trans (hsplit.2.1 heq)⟩
    intro x hx
    have hmax' : ∀ z ∈ P, θ z ≤ θ y := by simpa only [heq] using hmax
    have hxθ : θ x = θ y := (le_antisymm (hmax x hx.1) (hx.2 w hw)).trans heq.symm
    exact ⟨hx.1, support_through_apex_meets_chosen_face P φ a ψ c hP y hyφ hyψ θ hθ
      hmax' x hx.1 hxθ⟩
  · exact Or.inl (hθH.trans (hsplit.2.2 hgt))

/-- Tilting an old support functional by the chosen facet normal exposes the
cone over every base face whose old support plane strictly separates the apex. -/
theorem cone_exposed_of_support_below_apex
    {d : ℕ} {P : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hφ : ∀ x ∈ P, φ x ≤ a)
    (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ) (hw : w ∈ P)
    (hmax : ∀ x ∈ P, ℓ x ≤ ℓ w)
    (hface : ℓ.toExposed P ⊆ {x | φ x = a})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyℓ : ℓ y < ℓ w) :
    IsExposed ℝ (convexHull ℝ (insert y P))
      (convexHull ℝ (insert y (ℓ.toExposed P))) := by
  let t : ℝ := (ℓ w - ℓ y) / (φ y - a)
  have ht : 0 < t := div_pos (sub_pos.mpr hyℓ) (sub_pos.mpr hyφ)
  have htD : t * (φ y - a) = ℓ w - ℓ y :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hyφ))
  let θ : (Fin d → ℝ) →L[ℝ] ℝ := ℓ + t • φ
  have hwφ : φ w = a := hface ⟨hw, hmax⟩
  have hθw : θ w = ℓ w + t * a := by simp [θ, hwφ]
  have hθmax : ∀ x ∈ P, θ x ≤ θ w := by
    intro x hx
    simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hwφ]
    exact add_le_add (hmax x hx) (mul_le_mul_of_nonneg_left (hφ x hx) ht.le)
  have hθy : θ y = θ w := by
    simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hwφ]
    nlinarith [htD]
  have hfaces : θ.toExposed P = ℓ.toExposed P := by
    rw [exposed_eq_level θ hw hθmax, exposed_eq_level ℓ hw hmax]
    ext x
    constructor
    · rintro ⟨hx, hxθ⟩
      refine ⟨hx, ?_⟩
      have hnonneg := mul_nonneg ht.le (sub_nonneg.mpr (hφ x hx))
      simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hxθ
      rw [hwφ] at hxθ
      linarith [hmax x hx]
    · rintro ⟨hx, hxℓ⟩
      have hxφ : φ x = a := hface ⟨hx, fun z hz => by rw [hxℓ]; exact hmax z hz⟩
      exact ⟨hx, by simp [θ, hxℓ, hwφ, hxφ]⟩
  have heq := (exposed_insert_trichotomy hconv θ w hw hθmax y).2.1 hθy
  rw [hfaces] at heq
  rw [← heq]
  exact ContinuousLinearMap.toExposed.isExposed (l := θ)

end Grunbaum2003


namespace Grunbaum2003

/-- Set and exposed-face geometry for adjoining a point beyond one facet. -/
theorem pyramid_extension_set_and_face_classification
    {d m : ℕ} (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j) :
    (convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a})) ∧
    (∀ H : Set (Fin d → ℝ), H.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) H →
      H ≠ convexHull ℝ (insert y P) →
      H = {y} ∨ IsExposed ℝ P H ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G)) ∧
    (∀ (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, ℓ x ≤ ℓ w) → ℓ y < ℓ w →
      IsExposed ℝ (convexHull ℝ (insert y P)) (ℓ.toExposed P) ∧
      (ℓ.toExposed P ⊆ {x | φ x = a} →
        IsExposed ℝ (convexHull ℝ (insert y P))
          (convexHull ℝ (insert y (ℓ.toExposed P))))) := by
  refine ⟨convexHull_insert_eq_union_pyramid P φ a ψ c hP hPne y hyφ
    (fun j => (hyψ j).le), ?_, ?_⟩
  · exact fun H hne hH hp => exposed_faces_of_pyramid_extension P hconv hcompact hPne
      φ a ψ c hP y hyφ hyψ H hne hH hp
  · intro ℓ w hw hmax hyℓ
    constructor
    · rw [← (exposed_insert_trichotomy hconv ℓ w hw hmax y).1 hyℓ]
      exact ContinuousLinearMap.toExposed.isExposed (l := ℓ)
    · intro hface
      apply cone_exposed_of_support_below_apex hconv φ a _ ℓ w hw hmax hface y hyφ hyℓ
      intro x hx
      rw [hP] at hx
      exact hx.1

end Grunbaum2003
-- END StellarPyramidGeometry.lean

-- BEGIN StellarFacetPresentation.lean
set_option autoImplicit false

noncomputable section

namespace Grunbaum2003


theorem aux_pp_int_step {d : ℕ} {P : Set (Fin d → ℝ)} {c : Fin d → ℝ} (hc : c ∈ interior P)
    (u : Fin d → ℝ) : ∃ ε : ℝ, 0 < ε ∧ c + ε • u ∈ P := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  refine ⟨r / (2 * (‖u‖ + 1)), by positivity, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h1 : ‖u‖ < ‖u‖ + 1 := by linarith
  calc r / (2 * (‖u‖ + 1)) * ‖u‖ ≤ r / (2 * (‖u‖ + 1)) * (‖u‖ + 1) := by
        gcongr
    _ = r / 2 := by field_simp
    _ < r := by linarith

theorem aux_pp_hull_le {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (l : Module.Dual ℝ (Fin d → ℝ)) (β : ℝ) (hl : ∀ v ∈ V, l (v - c) ≤ β) :
    ∀ y ∈ convexHull ℝ (V : Set (Fin d → ℝ)), l (y - c) ≤ β := by
  intro y hy
  have hsub : convexHull ℝ (V : Set (Fin d → ℝ)) ⊆ {w | l w ≤ β + l c} :=
    convexHull_min (fun v hv => by
      have := hl v hv; rw [map_sub] at this; show l v ≤ β + l c; linarith)
      (convex_halfSpace_le l.isLinear _)
  have := hsub hy
  simp only [Set.mem_setOf_eq] at this
  rw [map_sub]; linarith

/-- Polar-vertex step: a separating normalized functional can be moved until its tight
vertices span the space. -/
theorem aux_pp_polar {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hc : c ∈ interior (convexHull ℝ (V : Set (Fin d → ℝ)))) (x : Fin d → ℝ) :
    ∀ n : ℕ, ∀ l : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l (v - c) ≤ 1) → 1 < l (x - c) →
      (V.filter (fun v => l (v - c) < 1)).card = n →
      ∃ l' : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l' (v - c) ≤ 1) ∧ 1 < l' (x - c) ∧
        Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l' (v - c) = 1))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hx hn
  by_cases hW : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤
  · exact ⟨l, hl, hx, hW⟩
  obtain ⟨h0, h0ne, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
  have hk : ∀ v ∈ V, l (v - c) = 1 → h0 (v - c) = 0 := fun v hv hv1 =>
    hle (Submodule.subset_span ⟨v, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hv, hv1⟩), rfl⟩)
  obtain ⟨h, hne, hker, hhx⟩ : ∃ h : Module.Dual ℝ (Fin d → ℝ), h ≠ 0 ∧
      (∀ v ∈ V, l (v - c) = 1 → h (v - c) = 0) ∧ 0 ≤ h (x - c) := by
    by_cases hs : 0 ≤ h0 (x - c)
    · exact ⟨h0, h0ne, hk, hs⟩
    · refine ⟨-h0, neg_ne_zero.mpr h0ne, fun v hv hv1 => by simp [hk v hv hv1], ?_⟩
      simp only [LinearMap.neg_apply]; linarith [not_le.mp hs]
  have hexists : ∃ v ∈ V, 0 < h (v - c) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hP := aux_pp_hull_le V c h 0 hcon
    refine LinearMap.ext (fun u => ?_)
    obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
    obtain ⟨ε', hε', hεu'⟩ := aux_pp_int_step hc (-u)
    have h1 := hP _ hεu
    have h2 := hP _ hεu'
    simp only [add_sub_cancel_left, map_smul, map_neg, smul_eq_mul] at h1 h2
    have h3 : h u ≤ 0 := by nlinarith
    have h4 : 0 ≤ h u := by nlinarith
    rw [LinearMap.zero_apply]
    linarith
  set S := V.filter (fun v => 0 < h (v - c)) with hS
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hpos⟩ := hexists
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hpos⟩⟩
  obtain ⟨vs, hvsS, hvsmin⟩ := S.exists_min_image (fun v => (1 - l (v - c)) / h (v - c)) hSne
  have hvs : vs ∈ V ∧ 0 < h (vs - c) := Finset.mem_filter.mp hvsS
  set t := (1 - l (vs - c)) / h (vs - c) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hl vs hvs.1]) hvs.2.le
  set l' := l + t • h with hl'def
  have hl'app : ∀ z, l' z = l z + t * h z := fun z => by
    simp [hl'def, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hl' : ∀ v ∈ V, l' (v - c) ≤ 1 := by
    intro v hv
    rw [hl'app]
    by_cases hpos : 0 < h (v - c)
    · have := hvsmin v (Finset.mem_filter.mpr ⟨hv, hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push Not at hpos
      nlinarith [hl v hv]
  have hx' : 1 < l' (x - c) := by rw [hl'app]; nlinarith
  have hvs1 : l' (vs - c) = 1 := by
    rw [hl'app, ht, div_mul_cancel₀ _ hvs.2.ne']; ring
  have hvslt : l (vs - c) < 1 := by
    rcases lt_or_eq_of_le (hl vs hvs.1) with h' | h'
    · exact h'
    · exfalso; have := hker vs hvs.1 h'; linarith [hvs.2]
  have hsub : V.filter (fun v => l' (v - c) < 1) ⊂ V.filter (fun v => l (v - c) < 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨vs, Finset.mem_filter.mpr ⟨hvs.1, hvslt⟩, ?_⟩
      intro hmem
      have := (Finset.mem_filter.mp hmem).2
      linarith
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      by_contra hcon
      have heq : l (v - c) = 1 := le_antisymm (hl v hv.1) (not_lt.mp hcon)
      have h5 := hker v hv.1 heq
      have : l' (v - c) = 1 := by rw [hl'app, h5, heq]; ring
      linarith [hv.2]
  exact ih _ (hn ▸ Finset.card_lt_card hsub) l' hl' hx' rfl

/-- The face cut out by a polar vertex is a facet, and every exposing functional of it
separates `x`. -/
theorem aux_pp_facet {d : ℕ} (hd : 0 < d) (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hcP : c ∈ convexHull ℝ (V : Set (Fin d → ℝ))) (l : Module.Dual ℝ (Fin d → ℝ))
    (hl : ∀ v ∈ V, l (v - c) ≤ 1)
    (hspan : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤)
    (x : Fin d → ℝ) (hx : 1 < l (x - c)) :
    ∃ G ∈ {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = d - 1},
      ∀ g : StrongDual ℝ (Fin d → ℝ),
        G = {y ∈ convexHull ℝ (V : Set (Fin d → ℝ)) |
          ∀ y' ∈ convexHull ℝ (V : Set (Fin d → ℝ)), g y' ≤ g y} →
        ∀ f ∈ G, g f < g x := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  set T := V.filter (fun v => l (v - c) = 1) with hT
  have hPle : ∀ y ∈ P, l (y - c) ≤ 1 := aux_pp_hull_le V c l 1 hl
  have hTne : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty] at hTe
    rw [hTe, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hspan
    have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) = 0 := by rw [← hspan, finrank_bot]
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨t0, ht0⟩ := hTne
  have ht0' := Finset.mem_filter.mp ht0
  set lc : StrongDual ℝ (Fin d → ℝ) := LinearMap.toContinuousLinearMap l with hlcdef
  have hlc : ∀ z, lc z = l z := fun z => by simp [hlcdef]
  set G := {y ∈ P | ∀ y' ∈ P, lc y' ≤ lc y} with hG
  have hTG : ∀ t ∈ T, t ∈ G := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr ht'.1), fun y' hy' => ?_⟩
    rw [hlc, hlc]
    have h1 := hPle y' hy'
    have h2 := ht'.2
    rw [map_sub] at h1 h2
    linarith
  have hG1 : ∀ y ∈ G, l (y - c) = 1 := by
    intro y hy
    have h1 := hy.2 t0 (hTG t0 ht0).1
    rw [hlc, hlc] at h1
    have h2 := hPle y hy.1
    have h3 := ht0'.2
    rw [map_sub] at h2 h3 ⊢
    linarith
  refine ⟨G, ⟨⟨t0, hTG t0 ht0⟩, fun _ => ⟨lc, rfl⟩, ?_⟩, ?_⟩
  · have hl0 : l ≠ 0 := by
      intro h0; have := ht0'.2; rw [h0, LinearMap.zero_apply] at this; norm_num at this
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
    rw [Module.finrank_fin_fun] at hker
    set D := (affineSpan ℝ G).direction with hD
    have hDle : D ≤ LinearMap.ker l := by
      rw [hD, direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro z ⟨y, hy, y', hy', rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
      have h1 := hG1 y hy
      have h2 := hG1 y' hy'
      rw [map_sub] at h1 h2 ⊢
      linarith
    have hup : Module.finrank ℝ D ≤ d - 1 := by
      have := Submodule.finrank_mono hDle
      omega
    have hdown : d ≤ Module.finrank ℝ D + 1 := by
      have htop : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ D ⊔ Submodule.span ℝ {t0 - c} := by
        rw [← hspan, Submodule.span_le]
        rintro z ⟨t, ht, rfl⟩
        have hsplit : t - c = (t - t0) + (t0 - c) := by abel
        simp only [SetLike.mem_coe]
        rw [hsplit]
        refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton_self _)
        rw [hD, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ (hTG t ht) (hTG t0 ht0)
      have h1 := Submodule.finrank_mono htop
      rw [finrank_top, Module.finrank_fin_fun] at h1
      have h2 := Submodule.finrank_add_le_finrank_add_finrank D (Submodule.span ℝ {t0 - c})
      have h3 : Module.finrank ℝ (Submodule.span ℝ ({t0 - c} : Set (Fin d → ℝ))) ≤ 1 := by
        have := finrank_span_le_card (R := ℝ) ({t0 - c} : Set (Fin d → ℝ))
        simpa using this
      omega
    omega
  · intro g hg f hf
    have hGg : ∀ y ∈ G, ∀ y' ∈ P, g y' ≤ g y := by
      intro y hy; rw [hg] at hy; exact hy.2
    have hGP : ∀ y ∈ G, y ∈ P := fun y hy => hy.1
    have hTeq : ∀ t ∈ T, g t = g f := fun t ht =>
      le_antisymm (hGg f hf t (hGP t (hTG t ht))) (hGg t (hTG t ht) f (hGP f hf))
    set β := g f - g c with hβ
    have hlin : (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) = β • l := by
      refine LinearMap.ext_on hspan ?_
      rintro z ⟨t, ht, rfl⟩
      have ht' := Finset.mem_filter.mp ht
      simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, smul_eq_mul]
      rw [ht'.2, mul_one, map_sub, hTeq t ht]
    have happ : ∀ z, g z = β * l z := fun z => by
      have := congrArg (fun φ : (Fin d → ℝ) →ₗ[ℝ] ℝ => φ z) hlin
      simpa using this
    have hβ0 : 0 ≤ β := by
      have := hGg f hf c hcP
      rw [hβ]; linarith
    have hβpos : 0 < β := by
      rcases lt_or_eq_of_le hβ0 with h | h
      · exact h
      · exfalso
        have hcG : c ∈ G := by
          rw [hg]
          exact ⟨hcP, fun y' _ => by rw [happ, happ, ← h]; simp⟩
        have := hG1 c hcG
        simp at this
    have hgx := happ (x - c)
    rw [map_sub] at hgx
    nlinarith

/-- A full-dimensional polytope is exactly the intersection of one prescribed
supporting halfspace per actual facet; an interior point is strictly feasible. -/
theorem stellarFacetPresentation_exists {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (ℱ : Finset (Set (Fin d → ℝ)))
    (hℱ : (ℱ : Set (Set (Fin d → ℝ))) =
      {F | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = d - 1}) :
    ∃ (φ : {F // F ∈ ℱ} → StrongDual ℝ (Fin d → ℝ)) (a : {F // F ∈ ℱ} → ℝ),
      P = {x | ∀ F, φ F x ≤ a F} ∧
      (∀ F, F.val = {x ∈ P | φ F x = a F}) ∧
      ∃ c ∈ interior P, ∀ F, φ F c < a F := by
  classical
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  have hcompact : IsCompact P := by
    obtain ⟨V, hfin, _, rfl⟩ := hP.1
    exact hfin.isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨c, hc⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hP.2
  have hcP : c ∈ P := interior_subset hc
  have hfacets (F : {F // F ∈ ℱ}) : F.val.Nonempty ∧ IsExposed ℝ P F.val ∧
      Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1 := by
    have hmem : F.val ∈ (ℱ : Set (Set (Fin d → ℝ))) := F.property
    rw [hℱ] at hmem
    exact hmem
  have hex (F : {F // F ∈ ℱ}) :
      ∃ (φ : StrongDual ℝ (Fin d → ℝ)) (w : Fin d → ℝ),
        w ∈ F.val ∧ F.val = {x ∈ P | ∀ z ∈ P, φ z ≤ φ x} := by
    obtain ⟨φ, hφ⟩ := (hfacets F).2.1 (hfacets F).1
    exact ⟨φ, (hfacets F).1.some, (hfacets F).1.some_mem, hφ⟩
  choose φ w hw hdesc using hex
  have hwP (F : {F // F ∈ ℱ}) : w F ∈ P := (hfacets F).2.1.subset (hw F)
  have hmax (F : {F // F ∈ ℱ}) : ∀ z ∈ P, φ F z ≤ φ F (w F) := by
    have h := hw F
    rw [hdesc F] at h
    exact h.2
  have hlevel (F : {F // F ∈ ℱ}) : F.val = {x ∈ P | φ F x = φ F (w F)} := by
    rw [hdesc F]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm (hmax F x hx.1) (hx.2 (w F) (hwP F))⟩
    · rintro ⟨hx, hval⟩
      exact ⟨hx, fun z hz => hval ▸ hmax F z hz⟩
  refine ⟨φ, fun F => φ F (w F), ?_, hlevel, c, hc, ?_⟩
  · ext x
    constructor
    · exact fun hx F => hmax F x hx
    · intro hx
      by_contra hxP
      obtain ⟨V0, hVfin, _, hPV0⟩ := hP.1
      let V := hVfin.toFinset
      have hPV : P = convexHull ℝ (V : Set (Fin d → ℝ)) := by
        simpa only [V, hVfin.coe_toFinset] using hPV0
      have hc' : c ∈ interior (convexHull ℝ (V : Set (Fin d → ℝ))) := by
        rw [← hPV]
        exact hc
      obtain ⟨θ, u, hθP, hθx⟩ := geometric_hahn_banach_closed_point hconv hcompact.isClosed hxP
      have hθc := hθP c hcP
      let l0 : Module.Dual ℝ (Fin d → ℝ) :=
        (u - θ c)⁻¹ • (θ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
      have hl0app : ∀ z, l0 z = θ z / (u - θ c) := by
        intro z
        simp [l0, div_eq_inv_mul]
      have hl0V : ∀ v ∈ V, l0 (v - c) ≤ 1 := by
        intro v hv
        rw [hl0app, div_le_one (by linarith), map_sub]
        have hvP : v ∈ P := by
          rw [hPV]
          exact subset_convexHull ℝ _ hv
        linarith [hθP v hvP]
      have hl0x : 1 < l0 (x - c) := by
        rw [hl0app, one_lt_div (by linarith), map_sub]
        linarith
      obtain ⟨l, hl, hlx, hlspan⟩ := aux_pp_polar V c hc' x _ l0 hl0V hl0x rfl
      have hcP' : c ∈ convexHull ℝ (V : Set (Fin d → ℝ)) := by
        rw [← hPV]
        exact hcP
      obtain ⟨G, hG, hGsep⟩ := aux_pp_facet hd V c hcP' l hl hlspan x hlx
      rw [← hPV] at hG hGsep
      have hGF : G ∈ ℱ := by
        change G ∈ (ℱ : Set (Set (Fin d → ℝ)))
        rw [hℱ]
        exact hG
      let I : {F // F ∈ ℱ} := ⟨G, hGF⟩
      have hsep := hGsep (φ I) (hdesc I) (w I) (hw I)
      exact (not_lt_of_ge (hx I)) hsep
  · intro F
    have hφne : φ F ≠ 0 := by
      intro hzero
      have hFP : F.val = P := by
        rw [hdesc F, hzero]
        ext x
        simp
      have hdim := (hfacets F).2.2
      rw [hFP, hP.2, AffineSubspace.direction_top, finrank_top,
        Module.finrank_fin_fun] at hdim
      omega
    obtain ⟨v, hv⟩ : ∃ v, 0 < φ F v := by
      by_contra! hn
      apply hφne
      ext v
      have hnneg := hn (-v)
      rw [map_neg] at hnneg
      simp only [ContinuousLinearMap.zero_apply]
      linarith [hn v]
    obtain ⟨ε, hε, hεv⟩ := aux_pp_int_step hc v
    have hbound := hmax F _ hεv
    rw [map_add, map_smul, smul_eq_mul] at hbound
    nlinarith

end Grunbaum2003
end
-- END StellarFacetPresentation.lean

-- BEGIN GSufficiencyNextApexCones.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.BilleraLee

/-- Polar-vertex step with non-strict separation `1 ≤ l (x - c)` and monotone preservation
of the tight vertex set `{v ∈ V | l (v - c) = 1}`. -/
theorem aux_pp_polar_le {D : ℕ} (V : Finset (Fin D → ℝ)) (c : Fin D → ℝ)
    (hc : c ∈ interior (convexHull ℝ (V : Set (Fin D → ℝ)))) (x : Fin D → ℝ) :
    ∀ n : ℕ, ∀ l : Module.Dual ℝ (Fin D → ℝ), (∀ v ∈ V, l (v - c) ≤ 1) → 1 ≤ l (x - c) →
      (V.filter (fun v => l (v - c) < 1)).card = n →
      ∃ l' : Module.Dual ℝ (Fin D → ℝ), (∀ v ∈ V, l' (v - c) ≤ 1) ∧ 1 ≤ l' (x - c) ∧
        (∀ v ∈ V, l (v - c) = 1 → l' (v - c) = 1) ∧
        Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l' (v - c) = 1))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hx hn
  by_cases hW : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤
  · exact ⟨l, hl, hx, fun _ _ h => h, hW⟩
  obtain ⟨h0, h0ne, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
  have hk : ∀ v ∈ V, l (v - c) = 1 → h0 (v - c) = 0 := fun v hv hv1 =>
    hle (Submodule.subset_span ⟨v, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hv, hv1⟩), rfl⟩)
  obtain ⟨h, hne, hker, hhx⟩ : ∃ h : Module.Dual ℝ (Fin D → ℝ), h ≠ 0 ∧
      (∀ v ∈ V, l (v - c) = 1 → h (v - c) = 0) ∧ 0 ≤ h (x - c) := by
    by_cases hs : 0 ≤ h0 (x - c)
    · exact ⟨h0, h0ne, hk, hs⟩
    · refine ⟨-h0, neg_ne_zero.mpr h0ne, fun v hv hv1 => by simp [hk v hv hv1], ?_⟩
      simp only [LinearMap.neg_apply]; linarith [not_le.mp hs]
  have hexists : ∃ v ∈ V, 0 < h (v - c) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hP := aux_pp_hull_le V c h 0 hcon
    refine LinearMap.ext (fun u => ?_)
    obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
    obtain ⟨ε', hε', hεu'⟩ := aux_pp_int_step hc (-u)
    have h1 := hP _ hεu
    have h2 := hP _ hεu'
    simp only [add_sub_cancel_left, map_smul, map_neg, smul_eq_mul] at h1 h2
    have h3 : h u ≤ 0 := by nlinarith
    have h4 : 0 ≤ h u := by nlinarith
    rw [LinearMap.zero_apply]
    linarith
  set S := V.filter (fun v => 0 < h (v - c))
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hpos⟩ := hexists
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hpos⟩⟩
  obtain ⟨vs, hvsS, hvsmin⟩ := S.exists_min_image (fun v => (1 - l (v - c)) / h (v - c)) hSne
  have hvs : vs ∈ V ∧ 0 < h (vs - c) := Finset.mem_filter.mp hvsS
  set t := (1 - l (vs - c)) / h (vs - c) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hl vs hvs.1]) hvs.2.le
  set l' := l + t • h with hl'def
  have hl'app : ∀ z, l' z = l z + t * h z := fun z => by
    simp [hl'def, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hl' : ∀ v ∈ V, l' (v - c) ≤ 1 := by
    intro v hv
    rw [hl'app]
    by_cases hpos : 0 < h (v - c)
    · have := hvsmin v (Finset.mem_filter.mpr ⟨hv, hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push Not at hpos
      nlinarith [hl v hv]
  have hx' : 1 ≤ l' (x - c) := by rw [hl'app]; nlinarith
  have hpres : ∀ v ∈ V, l (v - c) = 1 → l' (v - c) = 1 := by
    intro v hv hv1
    rw [hl'app, hv1, hker v hv hv1]
    ring
  have hvslt : l (vs - c) < 1 := by
    rcases lt_or_eq_of_le (hl vs hvs.1) with h' | h'
    · exact h'
    · exfalso; have := hker vs hvs.1 h'; linarith [hvs.2]
  have hvs1 : l' (vs - c) = 1 := by
    rw [hl'app, ht, div_mul_cancel₀ _ hvs.2.ne']; ring
  have hsub : V.filter (fun v => l' (v - c) < 1) ⊂ V.filter (fun v => l (v - c) < 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨vs, Finset.mem_filter.mpr ⟨hvs.1, hvslt⟩, ?_⟩
      intro hmem
      have := (Finset.mem_filter.mp hmem).2
      linarith
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      by_contra hcon
      have heq : l (v - c) = 1 := le_antisymm (hl v hv.1) (not_lt.mp hcon)
      have := hpres v hv.1 heq
      linarith [hv.2]
  obtain ⟨l'', hl'', hx'', hpres'', hspan''⟩ :=
    ih _ (hn ▸ Finset.card_lt_card hsub) l' hl' hx' rfl
  exact ⟨l'', hl'', hx'', fun v hv hv1 => hpres'' v hv (hpres v hv hv1), hspan''⟩

/-- A polar vertex `l` with `1 ≤ l (x - c)` cuts out an exposed facet `𝒢` containing all tight
vertices `{v ∈ V | l (v - c) = 1}` such that every supporting functional `(φ, α)` of `𝒢`
satisfies `α ≤ φ x`. -/
theorem aux_pp_facet_le {D : ℕ} (hD : 0 < D) (V : Finset (Fin D → ℝ)) (c : Fin D → ℝ)
    (hcP : c ∈ convexHull ℝ (V : Set (Fin D → ℝ))) (l : Module.Dual ℝ (Fin D → ℝ))
    (hl : ∀ v ∈ V, l (v - c) ≤ 1)
    (hspan : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤)
    (x : Fin D → ℝ) (hx : 1 ≤ l (x - c)) :
    ∃ 𝒢 : Set (Fin D → ℝ),
      𝒢.Nonempty ∧
      IsExposed ℝ (convexHull ℝ (V : Set (Fin D → ℝ))) 𝒢 ∧
      Module.finrank ℝ (affineSpan ℝ 𝒢).direction = D - 1 ∧
      (∀ v ∈ V, l (v - c) = 1 → v ∈ 𝒢) ∧
      (∀ (φ : StrongDual ℝ (Fin D → ℝ)) (α : ℝ),
        (∀ y ∈ convexHull ℝ (V : Set (Fin D → ℝ)), φ y ≤ α) →
        (∀ y ∈ convexHull ℝ (V : Set (Fin D → ℝ)), y ∈ 𝒢 ↔ φ y = α) →
        α ≤ φ x) := by
  set P := convexHull ℝ (V : Set (Fin D → ℝ))
  set T := V.filter (fun v => l (v - c) = 1)
  have hPle : ∀ y ∈ P, l (y - c) ≤ 1 := aux_pp_hull_le V c l 1 hl
  have hTne : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty] at hTe
    rw [hTe, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hspan
    have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin D → ℝ)) = 0 := by rw [← hspan, finrank_bot]
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨t0, ht0⟩ := hTne
  have ht0' := Finset.mem_filter.mp ht0
  set lc : StrongDual ℝ (Fin D → ℝ) := LinearMap.toContinuousLinearMap l with hlcdef
  have hlc : ∀ z, lc z = l z := fun z => by simp [hlcdef]
  set G := {y ∈ P | ∀ y' ∈ P, lc y' ≤ lc y}
  have hTG : ∀ t ∈ T, t ∈ G := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr ht'.1), fun y' hy' => ?_⟩
    rw [hlc, hlc]
    have h1 := hPle y' hy'
    have h2 := ht'.2
    rw [map_sub] at h1 h2
    linarith
  have hG1 : ∀ y ∈ G, l (y - c) = 1 := by
    intro y hy
    have h1 := hy.2 t0 (hTG t0 ht0).1
    rw [hlc, hlc] at h1
    have h2 := hPle y hy.1
    have h3 := ht0'.2
    rw [map_sub] at h2 h3 ⊢
    linarith
  refine ⟨G, ⟨t0, hTG t0 ht0⟩, fun _ => ⟨lc, rfl⟩, ?_, ?_, ?_⟩
  · have hl0 : l ≠ 0 := by
      intro h0; have := ht0'.2; rw [h0, LinearMap.zero_apply] at this; norm_num at this
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
    rw [Module.finrank_fin_fun] at hker
    set E := (affineSpan ℝ G).direction with hE
    have hEle : E ≤ LinearMap.ker l := by
      rw [hE, direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro z ⟨y, hy, y', hy', rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
      have h1 := hG1 y hy
      have h2 := hG1 y' hy'
      rw [map_sub] at h1 h2 ⊢
      linarith
    have hup : Module.finrank ℝ E ≤ D - 1 := by
      have := Submodule.finrank_mono hEle
      omega
    have hdown : D ≤ Module.finrank ℝ E + 1 := by
      have htop : (⊤ : Submodule ℝ (Fin D → ℝ)) ≤ E ⊔ Submodule.span ℝ {t0 - c} := by
        rw [← hspan, Submodule.span_le]
        rintro z ⟨t, ht, rfl⟩
        have hsplit : t - c = (t - t0) + (t0 - c) := by abel
        simp only [SetLike.mem_coe]
        rw [hsplit]
        refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton_self _)
        rw [hE, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ (hTG t ht) (hTG t0 ht0)
      have h1 := Submodule.finrank_mono htop
      rw [finrank_top, Module.finrank_fin_fun] at h1
      have h2 := Submodule.finrank_add_le_finrank_add_finrank E (Submodule.span ℝ {t0 - c})
      have h3 : Module.finrank ℝ (Submodule.span ℝ ({t0 - c} : Set (Fin D → ℝ))) ≤ 1 := by
        have := finrank_span_le_card (R := ℝ) ({t0 - c} : Set (Fin D → ℝ))
        simpa using this
      omega
    omega
  · intro v hv hv1
    exact hTG v (Finset.mem_filter.mpr ⟨hv, hv1⟩)
  · intro φ α hφle hφiff
    have hTeq : ∀ t ∈ T, φ t = α := fun t ht =>
      (hφiff t (hTG t ht).1).mp (hTG t ht)
    set β := α - φ c with hβ
    have hlin : (φ : (Fin D → ℝ) →ₗ[ℝ] ℝ) = β • l := by
      refine LinearMap.ext_on hspan ?_
      rintro z ⟨t, ht, rfl⟩
      have ht' := Finset.mem_filter.mp ht
      simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, smul_eq_mul]
      rw [ht'.2, mul_one, map_sub, hTeq t ht]
    have happ : ∀ z, φ z = β * l z := fun z => by
      have := congrArg (fun ψ : (Fin D → ℝ) →ₗ[ℝ] ℝ => ψ z) hlin
      simpa using this
    have hβ0 : 0 ≤ β := by
      have := hφle c hcP
      rw [hβ]; linarith
    have hφx := happ (x - c)
    rw [map_sub] at hφx
    nlinarith

theorem convexHull_insert_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    (y : E) (A : Set E) :
    convexHull ℝ (insert y (convexHull ℝ A)) = convexHull ℝ (insert y A) := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ (insert y A))
    intro x hx
    rcases hx with rfl | hx
    · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · exact convexHull_mono (Set.subset_insert _ _) hx
  · exact convexHull_mono (Set.insert_subset_insert (subset_convexHull ℝ A))

theorem zero_mem_compressedWords (d s : ℕ) (M : Finset (Fin s →₀ ℕ))
    (h0M : (0 : Fin s →₀ ℕ) ∈ M) :
    (0 : Fin (d / 2) → ℕ) ∈ compressedWords (d / 2) s M := by
  rw [mem_compressedWords]
  refine ⟨fun _ => Nat.zero_le s, fun _ _ _ => le_rfl, ?_⟩
  have hzero : wordExponent s (0 : Fin (d / 2) → ℕ) = 0 := by
    ext j
    simp [wordExponent_apply]
  rw [hzero]
  exact h0M

/-- In the Section 7 construction, `P_ext = convexHull ℝ (insert zStar P)` is a `(d + 1)`-polytope
and `{zStar}` is an exposed vertex of `P_ext` with `zStar ∉ P`. -/
theorem apex_isDPolytope_and_singleton_exposed (d s : ℕ) (_hd : 2 ≤ d) (hs : 1 ≤ s)
    (M : Finset (Fin s →₀ ℕ)) (h0M : (0 : Fin s →₀ ℕ) ∈ M)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t) (zStar : Fin (d + 1) → ℝ)
    (hvis :
      let P := convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))
      let W := compressedWords (d / 2) s M
      ∀ 𝒢 : Set (Fin (d + 1) → ℝ), 𝒢.Nonempty → IsExposed ℝ P 𝒢 →
        Module.finrank ℝ (affineSpan ℝ 𝒢).direction = d →
        ∃ (φ : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ),
          (∀ y ∈ P, φ y ≤ α) ∧
          (∀ y ∈ P, y ∈ 𝒢 ↔ φ y = α) ∧
          ((∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → α < φ zStar) ∧
          ((¬ ∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → φ zStar < α)) :
    let v := fun i => momentCurve (d + 1) (t i)
    let P := convexHull ℝ (Set.range v)
    let P_ext := convexHull ℝ (insert zStar P)
    IsDPolytope P_ext ∧ zStar ∉ P ∧ IsExposed ℝ P_ext {zStar} := by
  intro v P P_ext
  have hPd : IsDPolytope P := momentCurve_isDPolytope (by omega) t ht.injective
  have hP_ext_hull : P_ext = convexHull ℝ (insert zStar (Set.range v)) :=
    convexHull_insert_convexHull zStar (Set.range v)
  have hP_ext_d : IsDPolytope P_ext := by
    refine ⟨⟨insert zStar (Set.range v), (Set.finite_range v).insert zStar,
      Set.insert_nonempty _ _, hP_ext_hull⟩, ?_⟩
    apply top_unique
    rw [← hPd.2]
    exact affineSpan_mono ℝ
      ((Set.subset_insert zStar P).trans (subset_convexHull ℝ (insert zStar P)))
  let u0 : Fin (d / 2) → ℕ := 0
  have hu0W : u0 ∈ compressedWords (d / 2) s M := zero_mem_compressedWords d s M h0M
  have hmu0 : Monotone u0 := fun _ _ _ => le_rfl
  have hbu0 : ∀ r, u0 r ≤ s := fun _ => Nat.zero_le s
  let 𝒢0 := convexHull ℝ (v '' (fullPairedFacet d s u0 : Set (Fin (s + d + 1))))
  have h𝒢0_ne : 𝒢0.Nonempty :=
    ⟨v 0, subset_convexHull ℝ _ ⟨0, zero_mem_fullPairedFacet d s u0, rfl⟩⟩
  have h𝒢0_exp : IsExposed ℝ P 𝒢0 := (fullPairedFacet_exposed d s u0 hbu0 t ht).1
  have h𝒢0_dim : Module.finrank ℝ (affineSpan ℝ 𝒢0).direction = d :=
    fullPairedFacet_finrank d s u0 hmu0 hbu0 t ht
  obtain ⟨φ, α, hφle, hφiff, hφgt, _⟩ := hvis 𝒢0 h𝒢0_ne h𝒢0_exp h𝒢0_dim
  have hα_lt : α < φ zStar := hφgt ⟨u0, hu0W, rfl⟩
  have hzStar_notP : zStar ∉ P := fun hz => (hφle zStar hz).not_gt hα_lt
  have hwP : v 0 ∈ P := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hw𝒢0 : v 0 ∈ 𝒢0 := subset_convexHull ℝ _ ⟨0, zero_mem_fullPairedFacet d s u0, rfl⟩
  have hφw : φ (v 0) = α := (hφiff (v 0) hwP).mp hw𝒢0
  have hmax : ∀ y ∈ P, φ y ≤ φ (v 0) := fun y hy => hφw ▸ hφle y hy
  have hlt : φ (v 0) < φ zStar := hφw ▸ hα_lt
  have hPconv : Convex ℝ P := convex_convexHull ℝ (Set.range v)
  have hexp_eq := (exposed_insert_trichotomy hPconv φ (v 0) hwP hmax zStar).2.2 hlt
  have hexp : IsExposed ℝ P_ext {zStar} := by
    rw [← hexp_eq]
    exact ContinuousLinearMap.toExposed.isExposed (l := φ)
  exact ⟨hP_ext_d, hzStar_notP, hexp⟩

/-- Forward cone exposure: for every word `u ∈ W` and every nonempty subset
`S ⊆ fullPairedFacet d s u` with `S.card ≤ d / 2`, the cone
`convexHull ℝ (insert zStar (v '' S))` is an exposed face of `P_ext` of affine dimension `S.card`. -/
theorem apex_cone_exposed_of_subset_paired (d s : ℕ) (_hd : 2 ≤ d) (_hs : 1 ≤ s)
    (M : Finset (Fin s →₀ ℕ))
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t) (zStar : Fin (d + 1) → ℝ)
    (hvis :
      let P := convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))
      let W := compressedWords (d / 2) s M
      (∀ 𝒢 : Set (Fin (d + 1) → ℝ), 𝒢.Nonempty → IsExposed ℝ P 𝒢 →
        Module.finrank ℝ (affineSpan ℝ 𝒢).direction = d →
        ∃ (φ : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ),
          (∀ y ∈ P, φ y ≤ α) ∧
          (∀ y ∈ P, y ∈ 𝒢 ↔ φ y = α) ∧
          ((∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → α < φ zStar) ∧
          ((¬ ∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → φ zStar < α)) ∧
      (∀ S : Finset (Fin (s + d + 1)), S.card ≤ d / 2 →
        ∃ (ψ : StrongDual ℝ (Fin (d + 1) → ℝ)) (β : ℝ),
          (∀ y ∈ P, ψ y ≤ β) ∧
          (∀ i ∈ S, ψ (momentCurve (d + 1) (t i)) = β) ∧
          ψ zStar < β))
    {u : Fin (d / 2) → ℕ} (huW : u ∈ compressedWords (d / 2) s M)
    {S : Finset (Fin (s + d + 1))} (hS : S ⊆ fullPairedFacet d s u)
    (hSne : S.Nonempty) (hScard : S.card ≤ d / 2) :
    let v := fun i => momentCurve (d + 1) (t i)
    let P := convexHull ℝ (Set.range v)
    let P_ext := convexHull ℝ (insert zStar P)
    let H := convexHull ℝ (insert zStar (v '' (S : Set (Fin (s + d + 1)))))
    IsExposed ℝ P_ext H ∧
      Module.finrank ℝ (affineSpan ℝ H).direction = S.card ∧
      H ∩ P = convexHull ℝ (v '' (S : Set (Fin (s + d + 1)))) := by
  intro v P P_ext H
  obtain ⟨hbu, hmu, _⟩ := (mem_compressedWords M u).mp huW
  have hPconv : Convex ℝ P := convex_convexHull ℝ (Set.range v)
  let 𝒢 := convexHull ℝ (v '' (fullPairedFacet d s u : Set (Fin (s + d + 1))))
  have h𝒢_ne : 𝒢.Nonempty :=
    ⟨v 0, subset_convexHull ℝ _ ⟨0, zero_mem_fullPairedFacet d s u, rfl⟩⟩
  have h𝒢_exp : IsExposed ℝ P 𝒢 := (fullPairedFacet_exposed d s u hbu t ht).1
  have h𝒢_dim : Module.finrank ℝ (affineSpan ℝ 𝒢).direction = d :=
    fullPairedFacet_finrank d s u hmu hbu t ht
  obtain ⟨φ, α, hφle, hφiff, hφgt, _⟩ := hvis.1 𝒢 h𝒢_ne h𝒢_exp h𝒢_dim
  have hα_lt : α < φ zStar := hφgt ⟨u, huW, rfl⟩
  let G0 := convexHull ℝ (v '' (S : Set (Fin (s + d + 1))))
  have hG0_exp : IsExposed ℝ P G0 := (fullPairedFacet_subset_exposed d s u hmu hbu t ht hS).1
  obtain ⟨i0, hi0S⟩ := hSne
  let w := v i0
  have hwG0 : w ∈ G0 := subset_convexHull ℝ _ ⟨i0, hi0S, rfl⟩
  have hwP : w ∈ P := subset_convexHull ℝ _ (Set.mem_range_self i0)
  obtain ⟨m0, hm0G0⟩ := hG0_exp ⟨w, hwG0⟩
  have hm0max : ∀ y ∈ P, m0 y ≤ m0 w := by
    have hw' := hwG0
    rw [hm0G0] at hw'
    exact hw'.2
  obtain ⟨ψ, β, hψle, hψS, hψz⟩ := hvis.2 S hScard
  have hψw : ψ w = β := hψS i0 hi0S
  have hψG0 : ∀ y ∈ G0, ψ y = β := by
    apply convexHull_min
    · rintro _ ⟨i, hi, rfl⟩
      exact hψS i hi
    · exact (convex_singleton β).linear_preimage ψ.toLinearMap
  let C : ℝ := max 0 ((m0 zStar - m0 w) / (β - ψ zStar)) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    have := le_max_left 0 ((m0 zStar - m0 w) / (β - ψ zStar))
    linarith
  have hC_gt : (m0 zStar - m0 w) / (β - ψ zStar) < C := by
    dsimp [C]
    have := le_max_right 0 ((m0 zStar - m0 w) / (β - ψ zStar))
    linarith
  have hden_pos : 0 < β - ψ zStar := sub_pos.mpr hψz
  have hC_mul : m0 zStar - m0 w < C * (β - ψ zStar) := (div_lt_iff₀ hden_pos).mp hC_gt
  let m : StrongDual ℝ (Fin (d + 1) → ℝ) := m0 + C • ψ
  have hmmax : ∀ y ∈ P, m y ≤ m w := by
    intro y hy
    simp only [m, add_apply, smul_apply, smul_eq_mul, hψw]
    exact add_le_add (hm0max y hy) (mul_le_mul_of_nonneg_left (hψle y hy) hC_pos.le)
  have hmz : m zStar < m w := by
    simp only [m, add_apply, smul_apply, smul_eq_mul, hψw]
    linarith
  have hm_eq_G0 : m.toExposed P = G0 := by
    ext y
    constructor
    · intro hy
      have hyP : y ∈ P := hy.1
      have hge : m w ≤ m y := hy.2 w hwP
      simp only [m, add_apply, smul_apply, smul_eq_mul, hψw] at hge
      have h1 := hm0max y hyP
      have h2 : C * ψ y ≤ C * β := mul_le_mul_of_nonneg_left (hψle y hyP) hC_pos.le
      have hm0_eq : m0 y = m0 w := by linarith
      rw [hm0G0]
      exact ⟨hyP, fun z hz => hm0_eq ▸ hm0max z hz⟩
    · intro hyG0
      have hyP : y ∈ P := hG0_exp.subset hyG0
      have hy' := hyG0
      rw [hm0G0] at hy'
      have hm0_eq : m0 y = m0 w := le_antisymm (hm0max y hyP) (hy'.2 w hwP)
      have hψ_eq : ψ y = β := hψG0 y hyG0
      refine ⟨hyP, fun z hz => ?_⟩
      have hmax_z := hmmax z hz
      simp only [m, add_apply, smul_apply, smul_eq_mul, hm0_eq, hψ_eq, hψw] at hmax_z ⊢
      exact hmax_z
  have hface_φ : m.toExposed P ⊆ {y | φ y = α} := by
    rw [hm_eq_G0]
    intro y hyG0
    have hy𝒢 : y ∈ 𝒢 :=
      convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hS)) hyG0
    exact (hφiff y (h𝒢_exp.subset hy𝒢)).mp hy𝒢
  have hcone_exp := cone_exposed_of_support_below_apex hPconv φ α hφle m w hwP hmmax hface_φ
    zStar hα_lt hmz
  have hcone_eq : convexHull ℝ (insert zStar (m.toExposed P)) = H := by
    rw [hm_eq_G0]
    exact convexHull_insert_convexHull zStar (v '' (S : Set (Fin (s + d + 1))))
  rw [hcone_eq] at hcone_exp
  -- Now prove finrank and intersection with P
  let F := fullPairedFacet d s u
  have hFcard : F.card = d + 1 := fullPairedFacet_card d s u hmu hbu
  let e : Fin (d + 1) ≃ ↥F := Fintype.equivOfCardEq (by simp [hFcard])
  let vF : Fin (d + 1) → Fin (d + 1) → ℝ := fun j => v (e j).val
  have hvF_ind : AffineIndependent ℝ vF :=
    momentCurve_affineIndependent (d := d + 1) (by omega) (fun j => t (e j).val)
      (ht.injective.comp (Subtype.val_injective.comp e.injective))
  have hφ_vF (j : Fin (d + 1)) : φ (vF j) = α := by
    have hj𝒢 : vF j ∈ 𝒢 := subset_convexHull ℝ _ ⟨(e j).val, (e j).property, rfl⟩
    exact (hφiff (vF j) (h𝒢_exp.subset hj𝒢)).mp hj𝒢
  let I : Finset (Fin (d + 1)) := Finset.univ.filter (fun j => (e j).val ∈ S)
  have hI_image : vF '' (I : Set (Fin (d + 1))) = v '' (S : Set (Fin (s + d + 1))) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, I, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hjS, rfl⟩
      exact ⟨(e j).val, hjS, rfl⟩
    · rintro ⟨i, hiS, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hS hiS⟩
      have hjeq : (e j).val = i := congrArg Subtype.val hj
      exact ⟨j, hjeq.symm ▸ hiS, by simp [vF, hjeq]⟩
  have hI_card : I.card = S.card := by
    have hbij : I.image (fun j => (e j).val) = S := by
      ext i
      simp only [Finset.mem_image, I, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hjS, rfl⟩
        exact hjS
      · intro hiS
        obtain ⟨j, hj⟩ := e.surjective ⟨i, hS hiS⟩
        have hjeq : (e j).val = i := congrArg Subtype.val hj
        exact ⟨j, hjeq.symm ▸ hiS, hjeq⟩
    rw [← hbij]
    exact (Finset.card_image_of_injective I (Subtype.val_injective.comp e.injective)).symm
  have hH_I : H = convexHull ℝ (insert zStar (vF '' (I : Set (Fin (d + 1))))) := by
    dsimp [H]
    rw [hI_image]
  have hfinrank : Module.finrank ℝ (affineSpan ℝ H).direction = S.card := by
    rw [hH_I, StellarCone.cone_finrank vF hvF_ind φ α hφ_vF zStar hα_lt I, hI_card]
  have hinter : H ∩ P = G0 := by
    apply StellarCone.convexHull_insert_inter_eq_of_supporting hPconv
    · rintro _ ⟨i, _, rfl⟩
      exact subset_convexHull ℝ _ (Set.mem_range_self i)
    · exact hφle
    · rintro _ ⟨i, hiS, rfl⟩
      have hi𝒢 : v i ∈ 𝒢 := subset_convexHull ℝ _ ⟨i, hS hiS, rfl⟩
      exact (hφiff (v i) (h𝒢_exp.subset hi𝒢)).mp hi𝒢
    · exact hα_lt
  exact ⟨hcone_exp, hfinrank, hinter⟩

/-- Reverse characterization of proper exposed faces of `P_ext` containing `zStar`:
every proper exposed face `H` of `P_ext` with `zStar ∈ H` and `H ≠ {zStar}` is of the form
`H = convexHull ℝ (insert zStar (v '' S))` for a nonempty subset `S ⊆ fullPairedFacet d s u`
with `u ∈ W`, has `S.card ≤ d`, `finrank = S.card`, and is a simplex. -/
theorem apex_proper_face_characterization (d s : ℕ) (hd : 2 ≤ d) (hs : 1 ≤ s)
    (M : Finset (Fin s →₀ ℕ)) (h0M : (0 : Fin s →₀ ℕ) ∈ M)
    (t : Fin (s + d + 1) → ℝ) (ht : StrictMono t) (zStar : Fin (d + 1) → ℝ)
    (hvis :
      let P := convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))
      let W := compressedWords (d / 2) s M
      ∀ 𝒢 : Set (Fin (d + 1) → ℝ), 𝒢.Nonempty → IsExposed ℝ P 𝒢 →
        Module.finrank ℝ (affineSpan ℝ 𝒢).direction = d →
        ∃ (φ : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ),
          (∀ y ∈ P, φ y ≤ α) ∧
          (∀ y ∈ P, y ∈ 𝒢 ↔ φ y = α) ∧
          ((∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → α < φ zStar) ∧
          ((¬ ∃ u ∈ W, 𝒢 = convexHull ℝ ((fun i => momentCurve (d + 1) (t i)) ''
              (fullPairedFacet d s u : Set (Fin (s + d + 1))))) → φ zStar < α))
    (H : Set (Fin (d + 1) → ℝ))
    (hHexp : IsExposed ℝ
      (convexHull ℝ (insert zStar (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i)))))) H)
    (hHproper : H ≠
      convexHull ℝ (insert zStar (convexHull ℝ (Set.range (fun i => momentCurve (d + 1) (t i))))))
    (hzStarH : zStar ∈ H) (hHne_apex : H ≠ {zStar}) :
    let v := fun i => momentCurve (d + 1) (t i)
    let W := compressedWords (d / 2) s M
    ∃ u ∈ W, ∃ S : Finset (Fin (s + d + 1)),
      S.Nonempty ∧ S ⊆ fullPairedFacet d s u ∧ S.card ≤ d ∧
      H = convexHull ℝ (insert zStar (v '' (S : Set (Fin (s + d + 1))))) ∧
      Module.finrank ℝ (affineSpan ℝ H).direction = S.card ∧
      (∃ w : Fin (S.card + 1) → Fin (d + 1) → ℝ,
        AffineIndependent ℝ w ∧ H = convexHull ℝ (Set.range w)) := by
  intro v W
  let P := convexHull ℝ (Set.range v)
  let P_ext := convexHull ℝ (insert zStar P)
  have hPd : IsDPolytope P := momentCurve_isDPolytope (by omega) t ht.injective
  have hPconv : Convex ℝ P := convex_convexHull ℝ (Set.range v)
  have hPcomp : IsCompact P := (Set.finite_range v).isCompact_convexHull ℝ
  have hPne : P.Nonempty := ⟨v 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩
  obtain ⟨_, hzStar_notP, _⟩ :=
    apex_isDPolytope_and_singleton_exposed d s hd hs M h0M t ht zStar hvis
  obtain ⟨θ, hθH⟩ := hHexp ⟨zStar, hzStarH⟩
  have hθ_ne : θ ≠ 0 := by
    intro h0
    apply hHproper
    simpa [h0, ContinuousLinearMap.toExposed] using hθH
  obtain ⟨w, hwP, hmaxOn⟩ := hPcomp.exists_isMaxOn hPne θ.continuous.continuousOn
  have hmax : ∀ x ∈ P, θ x ≤ θ w := fun _ hx => hmaxOn hx
  have hsplit := exposed_insert_trichotomy hPconv θ w hwP hmax zStar
  have hθH' : H = θ.toExposed P_ext := hθH
  have hθ_eq : θ zStar = θ w := by
    rcases lt_trichotomy (θ zStar) (θ w) with hlt | heq | hgt
    · exfalso
      have hH_sub : H ⊆ P := by
        rw [hθH', hsplit.1 hlt]
        exact fun x hx => hx.1
      exact hzStar_notP (hH_sub hzStarH)
    · exact heq
    · exfalso
      exact hHne_apex (hθH'.trans (hsplit.2.2 hgt))
  let G0 := θ.toExposed P
  have hH_cone : H = convexHull ℝ (insert zStar G0) :=
    hθH'.trans (hsplit.2.1 hθ_eq)
  have hG0_exp : IsExposed ℝ P G0 := ContinuousLinearMap.toExposed.isExposed (l := θ)
  have hG0_hull : G0 = convexHull ℝ (G0 ∩ Set.range v) :=
    StellarFaceTools.finite_face_hull v hG0_exp
  let S : Finset (Fin (s + d + 1)) := Finset.univ.filter (fun i => v i ∈ G0)
  have hG0_S : G0 ∩ Set.range v = v '' (S : Set (Fin (s + d + 1))) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, Finset.mem_coe,
      S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxG0, i, rfl⟩
      exact ⟨i, hxG0, rfl⟩
    · rintro ⟨i, hiG0, rfl⟩
      exact ⟨hiG0, i, rfl⟩
  have hG0_eq : G0 = convexHull ℝ (v '' (S : Set (Fin (s + d + 1)))) := by
    rw [hG0_hull, hG0_S]
  have hSne : S.Nonempty := by
    by_contra hSempty
    rw [Finset.not_nonempty_iff_eq_empty] at hSempty
    have hG0_empty : G0 = ∅ := by simp [hG0_eq, hSempty]
    have hwG0 : w ∈ G0 := ⟨hwP, hmax⟩
    rw [hG0_empty] at hwG0
    exact hwG0
  have hH_eq : H = convexHull ℝ (insert zStar (v '' (S : Set (Fin (s + d + 1))))) := by
    rw [hH_cone, hG0_eq, convexHull_insert_convexHull]
  -- Now use aux_pp_polar_le and aux_pp_facet_le to find u ∈ W with S ⊆ fullPairedFacet d s u
  let V : Finset (Fin (d + 1) → ℝ) := Finset.univ.image v
  have hV_coe : (V : Set (Fin (d + 1) → ℝ)) = Set.range v := by
    ext x
    simp [V]
  have hPV : P = convexHull ℝ (V : Set (Fin (d + 1) → ℝ)) := by rw [hV_coe]
  obtain ⟨c, hc⟩ := hPconv.interior_nonempty_iff_affineSpan_eq_top.mpr hPd.2
  have hcP : c ∈ P := interior_subset hc
  have hcV : c ∈ interior (convexHull ℝ (V : Set (Fin (d + 1) → ℝ))) := hPV ▸ hc
  have hcPV : c ∈ convexHull ℝ (V : Set (Fin (d + 1) → ℝ)) := hPV ▸ hcP
  have hθc_lt : θ c < θ w := by
    obtain ⟨u_dir, hu_dir⟩ : ∃ u_dir, 0 < θ u_dir := by
      by_contra! hn
      apply hθ_ne
      ext u_dir
      have hnneg := hn (-u_dir)
      rw [map_neg] at hnneg
      simp only [zero_apply]
      linarith [hn u_dir]
    obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u_dir
    have hbound := hmax _ hεu
    change θ (c + ε • u_dir) ≤ θ w at hbound
    rw [map_add, map_smul, smul_eq_mul] at hbound
    nlinarith
  let l0 : Module.Dual ℝ (Fin (d + 1) → ℝ) :=
    (θ w - θ c)⁻¹ • (θ : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ)
  have hl0_app : ∀ z, l0 z = θ z / (θ w - θ c) := by
    intro z
    simp [l0, div_eq_inv_mul]
  have hl0V : ∀ x ∈ V, l0 (x - c) ≤ 1 := by
    intro x hx
    rw [hl0_app, div_le_one (by linarith), map_sub]
    have hxP : x ∈ P := hPV ▸ subset_convexHull ℝ _ hx
    linarith [hmax x hxP]
  have hl0z : 1 ≤ l0 (zStar - c) := by
    rw [hl0_app, le_div_iff₀ (by linarith), map_sub, hθ_eq]
    linarith
  have hl0S : ∀ i ∈ S, l0 (v i - c) = 1 := by
    intro i hiS
    have hviG0 : v i ∈ G0 := (Finset.mem_filter.mp hiS).2
    have hθvi : θ (v i) = θ w := le_antisymm (hmax (v i) hviG0.1) (hviG0.2 w hwP)
    rw [hl0_app, map_sub, hθvi, div_self (by linarith)]
  obtain ⟨l', hl'V, hl'z, hl'pres, hspan⟩ :=
    aux_pp_polar_le V c hcV zStar _ l0 hl0V hl0z rfl
  obtain ⟨𝒢, h𝒢ne, h𝒢exp, h𝒢dim, h𝒢tight, h𝒢sep⟩ :=
    aux_pp_facet_le (by omega) V c hcPV l' hl'V hspan zStar hl'z
  rw [← hPV] at h𝒢exp h𝒢sep
  obtain ⟨φ, α, hφle, hφiff, _, hφlt_notW⟩ := hvis 𝒢 h𝒢ne h𝒢exp h𝒢dim
  have hα_le : α ≤ φ zStar := h𝒢sep φ α hφle hφiff
  have hexU : ∃ u ∈ W, 𝒢 = convexHull ℝ (v '' (fullPairedFacet d s u : Set (Fin (s + d + 1)))) := by
    by_contra hnotW
    exact (hφlt_notW hnotW).not_ge hα_le
  obtain ⟨u, huW, h𝒢u⟩ := hexU
  obtain ⟨hbu, hmu, _⟩ := (mem_compressedWords M u).mp huW
  have hS_sub : S ⊆ fullPairedFacet d s u := by
    intro i hiS
    have hviV : v i ∈ V := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hvi𝒢 : v i ∈ 𝒢 := h𝒢tight (v i) hviV (hl'pres (v i) hviV (hl0S i hiS))
    rw [h𝒢u] at hvi𝒢
    exact ((fullPairedFacet_exposed d s u hbu t ht).2 i).mp hvi𝒢
  -- Now prove simplex and finrank using (φ_u, α_u) from hvis on 𝒢
  obtain ⟨φ_u, α_u, hφ_u_le, hφ_u_iff, hφ_u_gt, _⟩ := hvis 𝒢 h𝒢ne h𝒢exp h𝒢dim
  have hα_u_lt : α_u < φ_u zStar := hφ_u_gt ⟨u, huW, h𝒢u⟩
  let F := fullPairedFacet d s u
  have hFcard : F.card = d + 1 := fullPairedFacet_card d s u hmu hbu
  let e : Fin (d + 1) ≃ ↥F := Fintype.equivOfCardEq (by simp [hFcard])
  let vF : Fin (d + 1) → Fin (d + 1) → ℝ := fun j => v (e j).val
  have hvF_ind : AffineIndependent ℝ vF :=
    momentCurve_affineIndependent (d := d + 1) (by omega) (fun j => t (e j).val)
      (ht.injective.comp (Subtype.val_injective.comp e.injective))
  have hφ_u_vF (j : Fin (d + 1)) : φ_u (vF j) = α_u := by
    have hj𝒢 : vF j ∈ 𝒢 := by
      rw [h𝒢u]
      exact subset_convexHull ℝ _ ⟨(e j).val, (e j).property, rfl⟩
    exact (hφ_u_iff (vF j) (h𝒢exp.subset hj𝒢)).mp hj𝒢
  let I : Finset (Fin (d + 1)) := Finset.univ.filter (fun j => (e j).val ∈ S)
  have hI_image : vF '' (I : Set (Fin (d + 1))) = v '' (S : Set (Fin (s + d + 1))) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, I, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hjS, rfl⟩
      exact ⟨(e j).val, hjS, rfl⟩
    · rintro ⟨i, hiS, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hS_sub hiS⟩
      have hjeq : (e j).val = i := congrArg Subtype.val hj
      exact ⟨j, hjeq.symm ▸ hiS, by simp [vF, hjeq]⟩
  have hI_card : I.card = S.card := by
    have hbij : I.image (fun j => (e j).val) = S := by
      ext i
      simp only [Finset.mem_image, I, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hjS, rfl⟩
        exact hjS
      · intro hiS
        obtain ⟨j, hj⟩ := e.surjective ⟨i, hS_sub hiS⟩
        have hjeq : (e j).val = i := congrArg Subtype.val hj
        exact ⟨j, hjeq.symm ▸ hiS, hjeq⟩
    rw [← hbij]
    exact (Finset.card_image_of_injective I (Subtype.val_injective.comp e.injective)).symm
  have hH_I : H = convexHull ℝ (insert zStar (vF '' (I : Set (Fin (d + 1))))) := by
    rw [hH_eq, hI_image]
  have hfinrank : Module.finrank ℝ (affineSpan ℝ H).direction = S.card := by
    rw [hH_I, StellarCone.cone_finrank vF hvF_ind φ_u α_u hφ_u_vF zStar hα_u_lt I, hI_card]
  have hsimplex : ∃ w : Fin (S.card + 1) → Fin (d + 1) → ℝ,
      AffineIndependent ℝ w ∧ H = convexHull ℝ (Set.range w) := by
    obtain ⟨wI, hwI_ind, hwI_hull⟩ :=
      StellarCone.cone_simplex vF hvF_ind φ_u α_u hφ_u_vF zStar hα_u_lt I
    rw [← hH_I] at hwI_hull
    let eqv : Fin (S.card + 1) ≃ Fin (I.card + 1) := finCongr (by rw [hI_card])
    refine ⟨wI ∘ eqv, hwI_ind.comp_embedding eqv.toEmbedding, ?_⟩
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, hwI_hull]
  -- Finally, prove S.card ≤ d because H lies in the hyperplane θ x = θ zStar
  have hScard_le_d : S.card ≤ d := by
    have hθ_lin_ne : (θ : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ) ≠ 0 := by
      intro h0
      exact hθ_ne (ContinuousLinearMap.coe_inj.mp h0)
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hθ_lin_ne
    rw [Module.finrank_fin_fun] at hker
    have hdir_le : (affineSpan ℝ H).direction ≤ LinearMap.ker (θ : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ) := by
      rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro z ⟨x, hxH, y, hyH, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, ContinuousLinearMap.coe_coe,
        map_sub, sub_eq_zero]
      have hx' := hxH
      have hy' := hyH
      rw [hθH] at hx' hy'
      exact le_antisymm (hy'.2 x hx'.1) (hx'.2 y hy'.1)
    have hmono := Submodule.finrank_mono hdir_le
    omega
  exact ⟨u, huW, S, hSne, hS_sub, hScard_le_d, hH_eq, hfinrank, hsimplex⟩

end Grunbaum2003.BilleraLee
-- END GSufficiencyNextApexCones.lean

-- BEGIN StellarFaceFamilies.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.StellarAssembly

/-- Adjoining one point to a full-dimensional polytope preserves the polytope conditions. -/
theorem isDPolytope_insert {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (y : Fin d → ℝ) : IsDPolytope (convexHull ℝ (insert y P)) := by
  obtain ⟨V, hfin, hne, hPV⟩ := hP.1
  have heq : convexHull ℝ (insert y P) = convexHull ℝ (insert y V) := by
    rw [hPV, Set.insert_eq, convexHull_convexHull_union_right, ← Set.insert_eq]
  refine ⟨⟨insert y V, hfin.insert y, Set.insert_nonempty _ _, heq⟩, ?_⟩
  apply top_unique
  rw [← hP.2]
  apply affineSpan_mono ℝ
  exact fun x hx => subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx)

/-- A finite polytope has only finitely many exposed faces, including the improper ones. -/
theorem finite_exposed_faces {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    {F : Set (Fin d → ℝ) | IsExposed ℝ P F}.Finite := by
  obtain ⟨V, hVfin, _, hPgen⟩ := hP.1
  have : Finite V := hVfin.to_subtype
  have hr : Set.range (fun i : V => i.val) = V := Subtype.range_coe
  have hFaces (F : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) :
      F = convexHull ℝ (F ∩ V) := by
    rw [hPgen, ← hr] at hF
    simpa only [hr] using StellarFaceTools.finite_face_hull (fun i : V => i.val) hF
  apply Set.Finite.of_finite_image (f := fun F => F ∩ V)
  · apply hVfin.finite_subsets.subset
    rintro _ ⟨F, _, rfl⟩
    exact Set.inter_subset_right
  · intro F hF G hG heq
    change F ∩ V = G ∩ V at heq
    rw [hFaces F hF, hFaces G hG, heq]

/-- Exact finite face families exist in every dimension, with the canonical `faceCount`. -/
theorem exists_face_families {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    ∃ ℱ : ℕ → Finset (Set (Fin d → ℝ)), ∀ k,
      (ℱ k : Set (Set (Fin d → ℝ))) =
        {F | F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k := by
  let S := fun k : ℕ => {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}
  have hfin (k : ℕ) : (S k).Finite :=
    (finite_exposed_faces hP).subset (fun _ h => h.2.1)
  refine ⟨fun k => (hfin k).toFinset, fun k => ⟨(hfin k).coe_toFinset, ?_⟩⟩
  exact (Set.ncard_eq_toFinset_card (S k) (hfin k)).symm

end Grunbaum2003.StellarAssembly
-- END StellarFaceFamilies.lean

-- BEGIN GSufficiencyNextVertexFigureLink.lean
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

noncomputable section

namespace Grunbaum2003.BilleraLee

open Grunbaum2003

private theorem face_vertex_cut_crossing {D : ℕ}
    (G : Set (Fin D → ℝ)) (hG : Convex ℝ G)
    (v w : Fin D → ℝ) (hv : v ∈ G) (hw : w ∈ G)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hwBelow : l w < α) :
    ∃ t : ℝ, t ≠ 0 ∧
      AffineMap.lineMap v w t ∈ G ∩ l ⁻¹' {α} ∧
      AffineMap.lineMap v (AffineMap.lineMap v w t) t⁻¹ = w := by
  let t : ℝ := (l v - α) / (l v - l w)
  have hDen : 0 < l v - l w := sub_pos.mpr (hwBelow.trans hα)
  have ht₀ : 0 < t := div_pos (sub_pos.mpr hα) hDen
  have ht₁ : t < 1 := (div_lt_one hDen).mpr (by linarith only [hwBelow])
  have htMul : t * (l v - l w) = l v - α := div_mul_cancel₀ _ hDen.ne'
  have hLevel : l (AffineMap.lineMap v w t) = α := by
    rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith only [htMul]
  refine ⟨t, ht₀.ne', ⟨hG.lineMap_mem hv hw ⟨ht₀.le, ht₁.le⟩, hLevel⟩, ?_⟩
  rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht₀.ne',
    AffineMap.lineMap_apply_one]

theorem exposed_face_eq_convexHull_inter_insert {D : ℕ} (v : Fin D → ℝ)
    (W : Set (Fin D → ℝ)) (hWfin : W.Finite)
    {G : Set (Fin D → ℝ)} (hG : IsExposed ℝ (convexHull ℝ (insert v W)) G) :
    G = convexHull ℝ (G ∩ insert v W) := by
  have hfin : (insert v W).Finite := hWfin.insert v
  have : Finite ↥(insert v W) := hfin.to_subtype
  have hr : Set.range (fun x : ↥(insert v W) => x.val) = insert v W := Subtype.range_coe
  rw [← hr] at hG
  simpa only [hr] using StellarFaceTools.finite_face_hull (fun x : ↥(insert v W) => x.val) hG

theorem affineSpan_vertex_figure_face_insert_gen {D : ℕ}
    (v : Fin D → ℝ) (W : Set (Fin D → ℝ)) (hWfin : W.Finite)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (G : Set (Fin D → ℝ)) (hG : IsExposed ℝ (convexHull ℝ (insert v W)) G) (hv : v ∈ G) :
    affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G := by
  let R := G ∩ l ⁻¹' {α}
  let S := affineSpan ℝ (insert v R)
  have hvS : v ∈ S := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hGconv : Convex ℝ G := hG.convex (convex_convexHull ℝ (insert v W))
  have hHull := exposed_face_eq_convexHull_inter_insert v W hWfin hG
  apply le_antisymm
  · exact affineSpan_mono ℝ (Set.insert_subset_iff.mpr ⟨hv, Set.inter_subset_left⟩)
  · apply affineSpan_le_of_subset_coe
    change G ⊆ S
    rw [hHull]
    apply convexHull_min ?_ S.convex
    rintro w ⟨hwG, hwGen⟩
    change w ∈ S
    rcases hwGen with rfl | hwW
    · exact hvS
    · obtain ⟨t, _, hq, hRecover⟩ := face_vertex_cut_crossing G hGconv v w hv hwG
        l α hα (hBelow w hwW)
      have hqS : AffineMap.lineMap v w t ∈ S :=
        subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ hq)
      have hwS := AffineMap.lineMap_mem t⁻¹ hvS hqS
      rw [hRecover] at hwS
      exact hwS

theorem vertex_figure_face_section_nonempty_iff_gen {D : ℕ}
    (v : Fin D → ℝ) (W : Set (Fin D → ℝ)) (hWfin : W.Finite)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (G : Set (Fin D → ℝ)) (hG : IsExposed ℝ (convexHull ℝ (insert v W)) G) (hv : v ∈ G) :
    (G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v} := by
  constructor
  · rintro ⟨x, hxG, hxLevel⟩ hEq
    have hxv : x = v := by simpa only [hEq, Set.mem_singleton_iff] using hxG
    subst x
    exact hα.ne hxLevel.symm
  · intro hNot
    by_contra hEmpty
    have hR : G ∩ l ⁻¹' {α} = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
    have hSpan := affineSpan_vertex_figure_face_insert_gen v W hWfin l α hα hBelow G hG hv
    have hSub : G ⊆ {v} := by
      intro x hx
      have hxSpan := subset_affineSpan ℝ G hx
      rw [← hSpan, hR, insert_empty_eq] at hxSpan
      exact (AffineSubspace.mem_affineSpan_singleton ℝ (Fin D → ℝ)).mp hxSpan
    exact hNot (Set.Subset.antisymm hSub (Set.singleton_subset_iff.mpr hv))

theorem vertex_figure_face_finrank_add_one_gen {D : ℕ}
    (v : Fin D → ℝ) (W : Set (Fin D → ℝ)) (hWfin : W.Finite)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (G : Set (Fin D → ℝ)) (hG : IsExposed ℝ (convexHull ℝ (insert v W)) G) (hv : v ∈ G)
    (hNonapex : G ≠ {v}) :
    (G ∩ l ⁻¹' {α}).Nonempty ∧
      Module.finrank ℝ (affineSpan ℝ G).direction =
        Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1 := by
  have hR :=
    (vertex_figure_face_section_nonempty_iff_gen v W hWfin l α hα hBelow G hG hv).mpr hNonapex
  refine ⟨hR, ?_⟩
  let R := G ∩ l ⁻¹' {α}
  let A := affineSpan ℝ R
  obtain ⟨r₀, hr₀⟩ := hR
  have hr₀A : r₀ ∈ A := subset_affineSpan ℝ R hr₀
  have hDir : A.direction ≤ LinearMap.ker l.toLinearMap := by
    change (affineSpan ℝ R).direction ≤ LinearMap.ker l.toLinearMap
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    change l (x - y) = 0
    rw [map_sub, hx.2, hy.2, sub_self]
  have hTransverse : v -ᵥ r₀ ∉ A.direction := by
    intro hMem
    have hz := hDir hMem
    change l (v - r₀) = 0 at hz
    rw [map_sub, hr₀.2] at hz
    exact (sub_pos.mpr hα).ne' hz
  have hSpan := affineSpan_vertex_figure_face_insert_gen v W hWfin l α hα hBelow G hG hv
  calc
    Module.finrank ℝ (affineSpan ℝ G).direction =
        Module.finrank ℝ (affineSpan ℝ (insert v R)).direction := by rw [hSpan]
    _ = Module.finrank ℝ
        (Submodule.span ℝ {v -ᵥ r₀} ⊔ A.direction : Submodule ℝ (Fin D → ℝ)) := by
      rw [← affineSpan_insert_affineSpan, AffineSubspace.direction_affineSpan_insert hr₀A]
    _ = Module.finrank ℝ A.direction + 1 := by
      rw [sup_comm]
      exact Submodule.finrank_sup_span_singleton hTransverse

theorem convexHull_insert_inter_level_eq (D : ℕ) (v : Fin D → ℝ)
    (W : Set (Fin D → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    convexHull ℝ (insert v W) ∩ l ⁻¹' {α} =
      convexHull ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) := by
  let q : (Fin D → ℝ) → (Fin D → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hq (w : Fin D → ℝ) (hw : w ∈ W) :
      q w ∈ convexHull ℝ (insert v W) ∧ l (q w) = α := by
    have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
    have ht0 : 0 ≤ (l v - α) / (l v - l w) := (div_pos hD hDen).le
    have ht1 : (l v - α) / (l v - l w) ≤ 1 :=
      (div_le_one hDen).mpr (by linarith [hBelow w hw])
    constructor
    · exact (convex_convexHull ℝ _).lineMap_mem
        (subset_convexHull ℝ _ (Set.mem_insert v W))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem v hw)) ⟨ht0, ht1⟩
    · have hMul : ((l v - α) / (l v - l w)) * (l v - l w) = l v - α :=
        div_mul_cancel₀ _ hDen.ne'
      dsimp [q]
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
      nlinarith [hMul]
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxLevel⟩
    change l x = α at hxLevel
    obtain ⟨ι, hι, a, z, ha, haSum, hz, haz⟩ := mem_convexHull_iff_exists_fintype.mp hx
    letI := hι
    obtain ⟨w₀, hw₀⟩ := hW
    let b : ι → ℝ := fun i => a i * (l v - l (z i)) / (l v - α)
    let u : ι → (Fin D → ℝ) := fun i => if z i = v then q w₀ else q (z i)
    have hzLe (i : ι) : l (z i) ≤ l v := by
      rcases hz i with h | h
      · simpa only [h] using le_refl (l v)
      · exact ((hBelow (z i) h).trans hα).le
    have hb (i : ι) : 0 ≤ b i := div_nonneg (mul_nonneg (ha i) (sub_nonneg.mpr (hzLe i))) hD.le
    have hlSum : ∑ i, a i * l (z i) = α := by
      have h := congrArg l haz
      simpa only [map_sum, map_smul, smul_eq_mul, hxLevel] using h
    have hbSum : ∑ i, b i = 1 := by
      calc
        ∑ i, b i = (∑ i, a i * (l v - l (z i))) / (l v - α) := by
          simp only [b, div_eq_mul_inv, Finset.sum_mul]
        _ = ((∑ i, a i) * l v - ∑ i, a i * l (z i)) / (l v - α) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = 1 := by rw [haSum, hlSum, one_mul, div_self hD.ne']
    have hu (i : ι) : u i ∈ q '' W := by
      dsimp [u]
      split_ifs with hi
      · exact ⟨w₀, hw₀, rfl⟩
      · exact ⟨z i, (Set.mem_insert_iff.mp (hz i)).resolve_left hi, rfl⟩
    have hTerm (i : ι) : b i • u i = b i • v + a i • (z i - v) := by
      by_cases hi : z i = v
      · simp [u, b, hi]
      · have hzi : z i ∈ W := (Set.mem_insert_iff.mp (hz i)).resolve_left hi
        have hDen : l v - l (z i) ≠ 0 := (sub_pos.mpr ((hBelow (z i) hzi).trans hα)).ne'
        have hCoef : b i * ((l v - α) / (l v - l (z i))) = a i := by
          dsimp [b]
          field_simp [hD.ne', hDen]
        dsimp [u]
        rw [if_neg hi]
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', smul_add, smul_smul, hCoef, add_comm]
    apply mem_convexHull_of_exists_fintype b u hb hbSum hu
    calc
      ∑ i, b i • u i = ∑ i, (b i • v + a i • (z i - v)) := Finset.sum_congr rfl (fun i _ => hTerm i)
      _ = (∑ i, b i) • v + (∑ i, a i • z i - (∑ i, a i) • v) := by
        simp only [Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      _ = x := by rw [hbSum, haSum, haz, one_smul]; abel
  · apply convexHull_min
    · rintro _ ⟨w, hw, rfl⟩
      exact hq w hw
    · apply (convex_convexHull ℝ _).inter
      intro x hx y hy a b _ _ hab
      change l x = α at hx
      change l y = α at hy
      change l (a • x + b • y) = α
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx, hy]
      rw [← add_mul, hab, one_mul]

theorem exposed_vertex_figure_face_lift (D : ℕ) (v : Fin D → ℝ)
    (W : Set (Fin D → ℝ)) (hW : W.Nonempty)
    (l m : StrongDual ℝ (Fin D → ℝ)) (α β : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hMax : ∀ x ∈ convexHull ℝ (insert v W) ∩ l ⁻¹' {α}, m x ≤ β) :
    let P := convexHull ℝ (insert v W)
    let n := m + ((β - m v) / (l v - α)) • l
    let G := {x ∈ P | n x = n v}
    (∀ x ∈ P, n x ≤ n v) ∧ IsExposed ℝ P G ∧ v ∈ G ∧
      {x ∈ P ∩ l ⁻¹' {α} | m x = β} = G ∩ l ⁻¹' {α} := by
  let P := convexHull ℝ (insert v W)
  let c : ℝ := (β - m v) / (l v - α)
  let n : StrongDual ℝ (Fin D → ℝ) := m + c • l
  let G := {x ∈ P | n x = n v}
  change (∀ x ∈ P, n x ≤ n v) ∧ IsExposed ℝ P G ∧ v ∈ G ∧
    {x ∈ P ∩ l ⁻¹' {α} | m x = β} = G ∩ l ⁻¹' {α}
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hcMul : c * (l v - α) = β - m v := div_mul_cancel₀ _ hD.ne'
  have hvP : v ∈ P := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hGen (w : Fin D → ℝ) (hw : w ∈ insert v W) : n w ≤ n v := by
    rcases hw with rfl | hw
    · exact le_rfl
    · have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
      let q := AffineMap.lineMap v w ((l v - α) / (l v - l w))
      have hq : q ∈ P ∩ l ⁻¹' {α} := by
        have hmem : q ∈ convexHull ℝ
            ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :=
          subset_convexHull ℝ _ ⟨w, hw, rfl⟩
        rwa [← convexHull_insert_inter_level_eq D v W hW l α hα hBelow] at hmem
      have hM := hMax q hq
      have hmq : m q = ((l v - α) * (m w - m v)) / (l v - l w) + m v := by
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
        ring
      rw [hmq] at hM
      have hFrac : ((l v - α) * (m w - m v)) / (l v - l w) ≤ β - m v := by linarith
      have hWeighted : (l v - α) * (m w - m v) ≤ (l v - α) * (c * (l v - l w)) := by
        calc
          (l v - α) * (m w - m v) ≤ (β - m v) * (l v - l w) := (div_le_iff₀ hDen).mp hFrac
          _ = (c * (l v - α)) * (l v - l w) := by rw [hcMul]
          _ = (l v - α) * (c * (l v - l w)) := by ring
      have hBound : m w - m v ≤ c * (l v - l w) := (mul_le_mul_iff_right₀ hD).mp hWeighted
      change m w + c * l w ≤ m v + c * l v
      nlinarith [hBound]
  have hN : ∀ x ∈ P, n x ≤ n v := by
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n v
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n v + b * n v :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n v := by rw [← add_mul, hab, one_mul]
  have hG : IsExposed ℝ P G := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      refine ⟨hxP, fun y hy => ?_⟩
      calc n y ≤ n v := hN y hy
           _ = n x := hxEq.symm
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hN x hxP) (hxMax v hvP)⟩
  have hEq (x : Fin D → ℝ) (hx : l x = α) : n x = n v ↔ m x = β := by
    change m x + c * l x = m v + c * l v ↔ m x = β
    rw [hx]
    constructor <;> intro h <;> nlinarith [hcMul]
  refine ⟨hN, hG, ⟨hvP, rfl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxP, hxLevel⟩, hxM⟩
    exact ⟨⟨hxP, (hEq x hxLevel).mpr hxM⟩, hxLevel⟩
  · rintro ⟨⟨hxP, hxN⟩, hxLevel⟩
    exact ⟨⟨hxP, hxLevel⟩, (hEq x hxLevel).mp hxN⟩

theorem isExposed_inter_restrict {D : ℕ} {P G B : Set (Fin D → ℝ)}
    (hG : IsExposed ℝ P G) (hBP : B ⊆ P) : IsExposed ℝ B (G ∩ B) := by
  intro hNonempty
  obtain ⟨z, hzG, hzB⟩ := hNonempty
  obtain ⟨m, hm⟩ := hG ⟨z, hzG⟩
  have hzMax : ∀ y ∈ P, m y ≤ m z := by
    have hz := hzG
    rw [hm] at hz
    exact hz.2
  refine ⟨m, ?_⟩
  ext x
  constructor
  · rintro ⟨hxG, hxB⟩
    rw [hm] at hxG
    exact ⟨hxB, fun y hy => hxG.2 y (hBP hy)⟩
  · rintro ⟨hxB, hxMax⟩
    refine ⟨?_, hxB⟩
    rw [hm]
    refine ⟨hBP hxB, fun y hy => ?_⟩
    exact (hzMax y hy).trans (hxMax z hzB)

theorem lineMap_mem_face_iff {D : ℕ} {P G : Set (Fin D → ℝ)}
    (hP : Convex ℝ P) (hG : IsExposed ℝ P G)
    {v w : Fin D → ℝ} (hvG : v ∈ G) (hwP : w ∈ P)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap v w t ∈ G ↔ w ∈ G := by
  constructor
  · intro hx
    exact hG.isExtreme.right_mem_of_mem_openSegment (hG.subset hvG) hwP hx
      (lineMap_mem_openSegment ℝ v w ht)
  · intro hwG
    exact (hG.convex hP).lineMap_mem hvG hwG ⟨ht.1.le, ht.2.le⟩

theorem vertex_figure_section_order_reflects_gen (D : ℕ)
    (v : Fin D → ℝ) (W : Set (Fin D → ℝ)) (hWfin : W.Finite)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (G₁ G₂ : Set (Fin D → ℝ))
    (hG₁ : IsExposed ℝ (convexHull ℝ (insert v W)) G₁)
    (hG₂ : IsExposed ℝ (convexHull ℝ (insert v W)) G₂)
    (hv₁ : v ∈ G₁) (hv₂ : v ∈ G₂)
    (hSections : G₁ ∩ l ⁻¹' {α} ⊆ G₂ ∩ l ⁻¹' {α}) : G₁ ⊆ G₂ := by
  let P := convexHull ℝ (insert v W)
  have hPconv : Convex ℝ P := convex_convexHull ℝ (insert v W)
  calc
    G₁ = convexHull ℝ (G₁ ∩ insert v W) := exposed_face_eq_convexHull_inter_insert v W hWfin hG₁
    _ ⊆ G₂ := by
      apply convexHull_min ?_ (hG₂.convex hPconv)
      rintro w ⟨hw₁, rfl | hwW⟩
      · exact hv₂
      · have hLow : l w < α := hBelow w hwW
        have hDen : 0 < l v - l w := sub_pos.mpr (hLow.trans hα)
        let t : ℝ := (l v - α) / (l v - l w)
        have ht₀ : 0 < t := div_pos (sub_pos.mpr hα) hDen
        have ht₁ : t < 1 := (div_lt_one hDen).mpr (by linarith)
        have hwP : w ∈ P := hG₁.subset hw₁
        have hq₁ : AffineMap.lineMap v w t ∈ G₁ :=
          (lineMap_mem_face_iff hPconv hG₁ hv₁ hwP ⟨ht₀, ht₁⟩).mpr hw₁
        have htMul : t * (l v - l w) = l v - α := div_mul_cancel₀ _ hDen.ne'
        have hqLevel : l (AffineMap.lineMap v w t) = α := by
          rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
          nlinarith [htMul]
        have hq₂ : AffineMap.lineMap v w t ∈ G₂ := (hSections ⟨hq₁, hqLevel⟩).1
        exact (lineMap_mem_face_iff hPconv hG₂ hv₂ hwP ⟨ht₀, ht₁⟩).mp hq₂

theorem vertex_figure_face_orderIso_gen (D : ℕ)
    (v : Fin D → ℝ) (W : Set (Fin D → ℝ)) (hWfin : W.Finite) (hW : W.Nonempty)
    (hv : IsExposed ℝ (convexHull ℝ (insert v W)) {v})
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    let P := convexHull ℝ (insert v W)
    ∃ Φ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace (P ∩ l ⁻¹' {α}),
      ∀ G, (Φ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) := by
  intro P
  let Q := P ∩ l ⁻¹' {α}
  let A := {G : PolytopeFace P // v ∈ G.val}
  let f : A → PolytopeFace Q := fun G =>
    ⟨G.val.val ∩ Q, isExposed_inter_restrict G.val.property Set.inter_subset_left⟩
  have hMap (G₁ G₂ : A) : f G₁ ≤ f G₂ ↔ G₁ ≤ G₂ := by
    change G₁.val.val ∩ Q ⊆ G₂.val.val ∩ Q ↔ G₁.val.val ⊆ G₂.val.val
    constructor
    · intro h
      apply vertex_figure_section_order_reflects_gen D v W hWfin l α hα hBelow
        G₁.val.val G₂.val.val G₁.val.property G₂.val.property G₁.property G₂.property
      rintro x ⟨hxG, hxLevel⟩
      have hxQ : x ∈ Q := ⟨G₁.val.property.subset hxG, hxLevel⟩
      have hx := h ⟨hxG, hxQ⟩
      exact ⟨hx.1, hx.2.2⟩
    · intro h x hx
      exact ⟨h hx.1, hx.2⟩
  let emb : A ↪o PolytopeFace Q := OrderEmbedding.ofMapLEIff f hMap
  have hSurj : Function.Surjective f := by
    intro R
    by_cases hEmpty : R.val = ∅
    · let G : A := ⟨⟨{v}, hv⟩, Set.mem_singleton v⟩
      refine ⟨G, ?_⟩
      apply Subtype.ext
      change {v} ∩ Q = R.val
      rw [hEmpty]
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      rintro x ⟨hxv, hxQ⟩
      have hx : x = v := hxv
      subst x
      exact (hα.ne hxQ.2.symm).elim
    · have hRne : R.val.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨z, hz⟩ := hRne
      obtain ⟨m, hm⟩ := R.property ⟨z, hz⟩
      have hzQ : z ∈ Q := R.property.subset hz
      have hzMax : ∀ y ∈ Q, m y ≤ m z := by
        have hz' := hz
        rw [hm] at hz'
        exact hz'.2
      let β := m z
      have hRmax : R.val = {x ∈ Q | m x = β} := by
        ext x
        constructor
        · intro hx
          have hx' := hx
          rw [hm] at hx'
          exact ⟨hx'.1, le_antisymm (hzMax x hx'.1) (hx'.2 z hzQ)⟩
        · rintro ⟨hxQ, hxEq⟩
          rw [hm]
          refine ⟨hxQ, fun y hy => ?_⟩
          calc m y ≤ m z := hzMax y hy
               _ = m x := hxEq.symm
      obtain ⟨_, hExpose, hVertex, hSlice⟩ :=
        exposed_vertex_figure_face_lift D v W hW l m α β hα hBelow hzMax
      let n := m + ((β - m v) / (l v - α)) • l
      let G : Set (Fin D → ℝ) := {x ∈ P | n x = n v}
      refine ⟨⟨⟨G, hExpose⟩, hVertex⟩, ?_⟩
      apply Subtype.ext
      change G ∩ Q = R.val
      rw [hRmax, hSlice]
      ext x
      constructor
      · rintro ⟨hxG, hxQ⟩
        exact ⟨hxG, hxQ.2⟩
      · rintro ⟨hxG, hxLevel⟩
        exact ⟨hxG, ⟨hExpose.subset hxG, hxLevel⟩⟩
  refine ⟨OrderIso.ofSurjective emb hSurj, fun _ => rfl⟩

theorem affineSpan_crossing_image_eq_level (D : ℕ) (v : Fin D → ℝ)
    (W : Set (Fin D → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin D → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hSpan : affineSpan ℝ (insert v W) = ⊤) :
    (affineSpan ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :
      Set (Fin D → ℝ)) = l ⁻¹' {α} := by
  let q : (Fin D → ℝ) → (Fin D → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  let A : AffineSubspace ℝ (Fin D → ℝ) := affineSpan ℝ (q '' W)
  let H : AffineSubspace ℝ (Fin D → ℝ) :=
    (affineSpan ℝ ({α} : Set ℝ)).comap l.toLinearMap.toAffineMap
  have hH (x : Fin D → ℝ) : x ∈ H ↔ l x = α := by
    change l x ∈ affineSpan ℝ ({α} : Set ℝ) ↔ _
    exact AffineSubspace.mem_affineSpan_singleton ℝ ℝ
  have hqLevel (w : Fin D → ℝ) (hw : w ∈ W) : l (q w) = α := by
    have hq : q w ∈ convexHull ℝ (q '' W) := subset_convexHull ℝ _ ⟨w, hw, rfl⟩
    rw [← convexHull_insert_inter_level_eq D v W hW l α hα hBelow] at hq
    exact hq.2
  have hAH : A ≤ H := by
    apply affineSpan_le_of_subset_coe
    rintro x ⟨w, hw, rfl⟩
    exact (hH _).mpr (hqLevel w hw)
  have hALevel (x : Fin D → ℝ) (hx : x ∈ A) : l x = α := (hH x).mp (hAH hx)
  obtain ⟨w₀, hw₀⟩ := hW
  have hq₀ : q w₀ ∈ A := subset_affineSpan ℝ _ ⟨w₀, hw₀, rfl⟩
  let S : AffineSubspace ℝ (Fin D → ℝ) := affineSpan ℝ (insert v (A : Set (Fin D → ℝ)))
  have hvS : v ∈ S := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hCover : insert v W ⊆ S := by
    rintro w (rfl | hw)
    · exact hvS
    · have hqwS : q w ∈ S := subset_affineSpan ℝ _
        (Set.mem_insert_of_mem v (subset_affineSpan ℝ _ ⟨w, hw, rfl⟩))
      let t : ℝ := (l v - α) / (l v - l w)
      have ht : t ≠ 0 := div_ne_zero (sub_pos.mpr hα).ne'
        (sub_pos.mpr ((hBelow w hw).trans hα)).ne'
      have hLine : AffineMap.lineMap v (q w) t⁻¹ = w := by
        change AffineMap.lineMap v (AffineMap.lineMap v w t) t⁻¹ = w
        rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht, AffineMap.lineMap_apply_one]
      have hm := AffineMap.lineMap_mem t⁻¹ hvS hqwS
      rwa [hLine] at hm
  have hSTop : S = ⊤ := by
    apply eq_top_iff.mpr
    have h := affineSpan_le_of_subset_coe hCover
    rwa [hSpan] at h
  ext x
  change x ∈ A ↔ l x = α
  constructor
  · exact hALevel x
  · intro hx
    have hxS : x ∈ S := by rw [hSTop]; trivial
    obtain ⟨r, p₀, hp₀, hxp₀⟩ := (AffineSubspace.mem_affineSpan_insert_iff hq₀ v x).mp hxS
    have hEq := congrArg l hxp₀
    simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul] at hEq
    rw [hx, hALevel p₀ hp₀, hALevel (q w₀) hq₀] at hEq
    have hMul : r * (l v - α) = 0 := by linarith
    have hr : r = 0 := (mul_eq_zero.mp hMul).resolve_right (sub_pos.mpr hα).ne'
    simp only [hr, zero_smul, zero_vadd] at hxp₀
    rwa [hxp₀]

theorem exists_vertex_figure_coordinates (d : ℕ) (v : Fin (d + 1) → ℝ)
    (W : Set (Fin (d + 1) → ℝ)) (hWfin : W.Finite) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hSpan : affineSpan ℝ (insert v W) = ⊤) :
    let Q := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
    letI : Nonempty (affineSpan ℝ Q) := by
      obtain ⟨w, hw⟩ := hW
      exact ⟨⟨_, subset_affineSpan ℝ Q ⟨w, hw, rfl⟩⟩⟩
    ∃ e : (affineSpan ℝ Q) ≃ᵃ[ℝ] (Fin d → ℝ),
      IsDPolytope (convexHull ℝ (e '' (((↑) : affineSpan ℝ Q → (Fin (d + 1) → ℝ)) ⁻¹' Q))) := by
  let q : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  let A : AffineSubspace ℝ (Fin (d + 1) → ℝ) := affineSpan ℝ (q '' W)
  obtain ⟨w₀, hw₀⟩ := hW
  have hq₀ : q w₀ ∈ A := subset_affineSpan ℝ _ ⟨w₀, hw₀, rfl⟩
  have : Nonempty A := ⟨⟨q w₀, hq₀⟩⟩
  change ∃ e : A ≃ᵃ[ℝ] (Fin d → ℝ),
    IsDPolytope (convexHull ℝ (e '' (((↑) : A → (Fin (d + 1) → ℝ)) ⁻¹' (q '' W))))
  have hASet : (A : Set (Fin (d + 1) → ℝ)) = l ⁻¹' {α} :=
    affineSpan_crossing_image_eq_level (d + 1) v W ⟨w₀, hw₀⟩ l α hα hBelow hSpan
  have hALevel (x : Fin (d + 1) → ℝ) (hx : x ∈ A) : l x = α := by
    have hx' : x ∈ (A : Set (Fin (d + 1) → ℝ)) := hx
    rw [hASet] at hx'
    exact hx'
  have hDir : A.direction = LinearMap.ker l.toLinearMap := by
    ext z
    change z ∈ A.direction ↔ l z = 0
    rw [← AffineSubspace.vadd_mem_iff_mem_direction z hq₀]
    change z + q w₀ ∈ (A : Set (Fin (d + 1) → ℝ)) ↔ l z = 0
    rw [hASet]
    change l (z + q w₀) = α ↔ l z = 0
    rw [map_add, hALevel (q w₀) hq₀]
    constructor <;> intro h <;> linarith
  have hlne : l.toLinearMap ≠ 0 := by
    intro hz
    have hzv := LinearMap.congr_fun hz v
    have hzw := LinearMap.congr_fun hz w₀
    change l v = 0 at hzv
    change l w₀ = 0 at hzw
    linarith [hBelow w₀ hw₀]
  have hRank : Module.finrank ℝ (LinearMap.ker l.toLinearMap) + 1 = d + 1 := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero hlne
  have hDim : Module.finrank ℝ A.direction = d := by
    rw [hDir]
    omega
  let eL : A.direction ≃ₗ[ℝ] (Fin d → ℝ) :=
    LinearEquiv.ofFinrankEq A.direction (Fin d → ℝ) (by simpa using hDim)
  let e : A ≃ᵃ[ℝ] (Fin d → ℝ) :=
    (AffineEquiv.vaddConst ℝ (⟨q w₀, hq₀⟩ : A)).symm.trans eL.toAffineEquiv
  let V : Set A := ((↑) : A → (Fin (d + 1) → ℝ)) ⁻¹' (q '' W)
  have hVfin : V.Finite := Set.Finite.preimage Subtype.val_injective.injOn (hWfin.image q)
  have hVne : V.Nonempty := ⟨⟨q w₀, hq₀⟩, ⟨w₀, hw₀, rfl⟩⟩
  have : Nonempty (q '' W) := ⟨⟨q w₀, ⟨w₀, hw₀, rfl⟩⟩⟩
  have hVSpan : affineSpan ℝ V = ⊤ := affineSpan_coe_preimage_eq_top (q '' W)
  refine ⟨e, ⟨⟨e '' V, hVfin.image e, hVne.image e, rfl⟩, ?_⟩⟩
  rw [affineSpan_convexHull]
  exact e.span_eq_top_iff.mp hVSpan

theorem isExposed_image_affineMap_of_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  intro hne
  have hSne : S.Nonempty := by
    obtain ⟨y, x, hx, rfl⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hS hSne
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  obtain ⟨u, hu⟩ := f.linear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hlin)
  have hu_apply : ∀ x : E, u (f.linear x) = x := by
    intro x
    exact congrArg (fun L : E →ₗ[ℝ] E => L x) hu
  let m : F →L[ℝ] ℝ := l.comp u.toContinuousLinearMap
  have hm : ∀ x : E, m (f x) = l x + l (u (f 0)) := by
    intro x
    have hfx : f x = f.linear x + f 0 := by
      simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E) x
    change l (u (f x)) = _
    rw [hfx, map_add, hu_apply, map_add]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P ∧ ∀ z ∈ P, l z ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm, hm]
    exact add_le_add (hx'.2 z hz) le_rfl
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have ht := hmax (f z) ⟨z, hz, rfl⟩
    rw [hm, hm] at ht
    exact (add_le_add_iff_right _).mp ht

theorem isExposed_preimage_affineMap_of_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P : Set E} {T : Set F} (hT : IsExposed ℝ (f '' P) T) :
    IsExposed ℝ P (f ⁻¹' T) := by
  intro hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hT ⟨f x, hx⟩
  let m : E →L[ℝ] ℝ := l.comp f.linear.toContinuousLinearMap
  have hm : ∀ x : E, m x = l (f x) - l (f 0) := by
    intro x
    have hv := f.linearMap_vsub x (0 : E)
    change f.linear (x - 0) = f x - f 0 at hv
    have hv' : f.linear x = f x - f 0 := by simpa only [sub_zero] using hv
    change l (f.linear x) = _
    rw [hv', map_sub]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · intro hy
    change f y ∈ T at hy
    have hy' : f y ∈ f '' P ∧ ∀ z ∈ f '' P, l z ≤ l (f y) := by
      simpa only [hl, Set.mem_ofPred_eq] using hy
    refine ⟨hf.mem_set_image.mp hy'.1, ?_⟩
    intro z hz
    rw [hm, hm]
    exact sub_le_sub_right (hy'.2 (f z) ⟨z, hz, rfl⟩) _
  · rintro ⟨hy, hmax⟩
    change f y ∈ T
    rw [hl]
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have ht := hmax z hz
    rw [hm, hm] at ht
    exact (sub_le_sub_iff_right _).mp ht

theorem finrank_direction_affineSpan_image_injective {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (S : Set E) :
    Module.finrank ℝ (affineSpan ℝ (f '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact ((affineSpan ℝ S).direction.equivMapOfInjective f.linear hlin).symm.finrank_eq

theorem polytopeFace_image_affineMap_orderIso {D e : ℕ}
    (f : (Fin e → ℝ) →ᵃ[ℝ] (Fin D → ℝ)) (hf : Function.Injective f)
    (Q₀ : Set (Fin e → ℝ)) (Q : Set (Fin D → ℝ)) (hQ : f '' Q₀ = Q) :
    ∃ Θ : PolytopeFace Q₀ ≃o PolytopeFace Q,
      ∀ R : PolytopeFace Q₀, (Θ R).val = f '' R.val := by
  let toFace : PolytopeFace Q₀ → PolytopeFace Q := fun R =>
    ⟨f '' R.val, hQ ▸ isExposed_image_affineMap_of_injective f hf R.property⟩
  have hMap (R₁ R₂ : PolytopeFace Q₀) : toFace R₁ ≤ toFace R₂ ↔ R₁ ≤ R₂ := by
    change f '' R₁.val ⊆ f '' R₂.val ↔ R₁.val ⊆ R₂.val
    exact Set.image_subset_image_iff hf
  let emb : PolytopeFace Q₀ ↪o PolytopeFace Q := OrderEmbedding.ofMapLEIff toFace hMap
  have hSurj : Function.Surjective toFace := by
    intro T
    have hTexp : IsExposed ℝ Q₀ (f ⁻¹' T.val) :=
      isExposed_preimage_affineMap_of_injective f hf (hQ.symm ▸ T.property)
    refine ⟨⟨f ⁻¹' T.val, hTexp⟩, ?_⟩
    apply Subtype.ext
    change f '' (f ⁻¹' T.val) = T.val
    apply Set.image_preimage_eq_iff.mpr
    calc T.val ⊆ Q := T.property.subset
      _ = f '' Q₀ := hQ.symm
      _ ⊆ Set.range f := Set.image_subset_range f Q₀
  refine ⟨OrderIso.ofSurjective emb hSurj, fun _ => rfl⟩

/-- Vertex-figure `d`-polytope and face-lattice isomorphism for `P_ext = convexHull ℝ (insert v W)`
in `ℝ^(d + 1)`. -/
theorem exists_vertex_figure_polytope_iso_gen (d : ℕ) (v : Fin (d + 1) → ℝ)
    (W : Set (Fin (d + 1) → ℝ)) (hWfin : W.Finite) (hW : W.Nonempty)
    (hv : IsExposed ℝ (convexHull ℝ (insert v W)) {v})
    (hSpan : affineSpan ℝ (insert v W) = ⊤)
    (l : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    let P_ext := convexHull ℝ (insert v W)
    ∃ (Q₀ : Set (Fin d → ℝ))
      (f : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d + 1) → ℝ))
      (Ψ : {G : PolytopeFace P_ext // v ∈ G.val} ≃o PolytopeFace Q₀),
      IsDPolytope Q₀ ∧
      Function.Injective f ∧
      f '' Q₀ = P_ext ∩ l ⁻¹' {α} ∧
      ∀ G : {G : PolytopeFace P_ext // v ∈ G.val},
        f '' (Ψ G).val = G.val.val ∩ l ⁻¹' {α} ∧
        ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
        (G.val.val ≠ {v} →
          (Ψ G).val.Nonempty ∧
            Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
              Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1) := by
  intro P_ext
  let R := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
  let A := affineSpan ℝ R
  have : Nonempty A := by
    obtain ⟨w, hw⟩ := hW
    exact ⟨⟨_, subset_affineSpan ℝ R ⟨w, hw, rfl⟩⟩⟩
  obtain ⟨e, hPoly⟩ := exists_vertex_figure_coordinates d v W hWfin hW l α hα hBelow hSpan
  have hQHull : P_ext ∩ l ⁻¹' {α} = convexHull ℝ R :=
    convexHull_insert_inter_level_eq (d + 1) v W hW l α hα hBelow
  let T : Set A := ((↑) : A → (Fin (d + 1) → ℝ)) ⁻¹' R
  let f : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d + 1) → ℝ) := A.subtype.comp e.symm.toAffineMap
  have hfInj : Function.Injective f := A.subtype_injective.comp e.symm.injective
  have hImageT : f '' (e '' T) = R := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change (e.symm (e z)).val ∈ R
      rw [e.symm_apply_apply]
      exact hz
    · intro x hx
      let z : A := ⟨x, subset_affineSpan ℝ R hx⟩
      refine ⟨e z, ⟨z, hx, rfl⟩, ?_⟩
      change (e.symm (e z)).val = x
      rw [e.symm_apply_apply]
  let Q₀ : Set (Fin d → ℝ) := convexHull ℝ (e '' T)
  have hQ₀Poly : IsDPolytope Q₀ := hPoly
  have hfQ₀ : f '' Q₀ = P_ext ∩ l ⁻¹' {α} := by
    dsimp only [Q₀]
    rw [f.image_convexHull, hImageT, hQHull]
  obtain ⟨Φ, hΦ⟩ := vertex_figure_face_orderIso_gen (d + 1) v W hWfin hW hv l α hα hBelow
  obtain ⟨Θ, hΘ⟩ := polytopeFace_image_affineMap_orderIso f hfInj Q₀ (P_ext ∩ l ⁻¹' {α}) hfQ₀
  let Ψ : {G : PolytopeFace P_ext // v ∈ G.val} ≃o PolytopeFace Q₀ := Φ.trans Θ.symm
  have hΨimg : ∀ G : {G : PolytopeFace P_ext // v ∈ G.val},
      f '' (Ψ G).val = G.val.val ∩ (P_ext ∩ l ⁻¹' {α}) := by
    intro G
    have h1 := hΘ (Θ.symm (Φ G))
    rw [OrderIso.apply_symm_apply] at h1
    exact h1.symm.trans (hΦ G)
  have hGInterEq : ∀ G : {G : PolytopeFace P_ext // v ∈ G.val},
      G.val.val ∩ (P_ext ∩ l ⁻¹' {α}) = G.val.val ∩ l ⁻¹' {α} := by
    intro G
    ext x
    constructor
    · rintro ⟨hxG, _, hxL⟩
      exact ⟨hxG, hxL⟩
    · rintro ⟨hxG, hxL⟩
      exact ⟨hxG, G.val.property.subset hxG, hxL⟩
  refine ⟨Q₀, f, Ψ, hQ₀Poly, hfInj, hfQ₀, ?_⟩
  intro G
  have hImgEq : f '' (Ψ G).val = G.val.val ∩ l ⁻¹' {α} :=
    (hΨimg G).trans (hGInterEq G)
  have hSecIff := vertex_figure_face_section_nonempty_iff_gen v W hWfin l α hα hBelow
    G.val.val G.val.property G.property
  have hEmptyIff : (Ψ G).val = ∅ ↔ G.val.val = {v} := by
    rw [← Set.not_nonempty_iff_eq_empty, ← Set.image_nonempty (f := f), hImgEq, hSecIff, not_not]
  refine ⟨hImgEq, hEmptyIff, ?_⟩
  intro hNeV
  obtain ⟨hSecNe, hRankEq⟩ := vertex_figure_face_finrank_add_one_gen v W hWfin l α hα hBelow
    G.val.val G.val.property G.property hNeV
  have hΨNe : (Ψ G).val.Nonempty := by
    rw [← Set.image_nonempty (f := f), hImgEq]
    exact hSecNe
  have hRankImg :
      Module.finrank ℝ (affineSpan ℝ (G.val.val ∩ l ⁻¹' {α})).direction =
        Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction := by
    rw [← hImgEq]
    exact finrank_direction_affineSpan_image_injective f hfInj (Ψ G).val
  exact ⟨hΨNe, hRankEq.trans (by rw [hRankImg])⟩

/-- Scaling each vector of a linearly independent family by a nonzero scalar preserves
linear independence. -/
theorem linearIndependent_smul_of_ne_zero {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {u : ι → E} (hu : LinearIndependent ℝ u) {t : ι → ℝ} (ht : ∀ i, t i ≠ 0) :
    LinearIndependent ℝ (fun i => t i • u i) := by
  rw [linearIndependent_iff'] at hu ⊢
  intro s g hsum i hi
  have hsum' : ∑ j ∈ s, (g j * t j) • u j = 0 := by
    simpa only [mul_smul] using hsum
  exact (mul_eq_zero.mp (hu s (fun j => g j * t j) hsum' i hi)).resolve_right (ht i)

/-- Equivalence between `AffineIndependent ℝ (Fin.cons z w)` and linear independence of
`j ↦ w j -ᵥ z`. -/
theorem affineIndependent_cons_iff_linearIndependent_vsub {d : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (z : E) (w : Fin d → E) :
    AffineIndependent ℝ (Fin.cons z w : Fin (d + 1) → E) ↔
      LinearIndependent ℝ (fun j : Fin d => w j -ᵥ z) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (Fin.cons z w : Fin (d + 1) → E) 0]
  let eSucc : Fin d ≃ {i : Fin (d + 1) // i ≠ 0} :=
    { toFun := fun j => ⟨j.succ, Fin.succ_ne_zero j⟩
      invFun := fun i => i.val.pred i.property
      left_inv := fun j => Fin.pred_succ j
      right_inv := fun i => Subtype.ext (Fin.succ_pred i.val i.property) }
  exact (linearIndependent_equiv eSucc).symm

/-- Cutting a simplex cone `convexHull ℝ (insert zStar (Set.range vS))` by `l ⁻¹' {α}` and
pulling back along an injective affine map `f` produces a simplex in `ℝ^d`. -/
theorem cone_section_simplex {d : ℕ} (hd : 0 < d) (zStar : Fin (d + 1) → ℝ)
    (vS : Fin d → Fin (d + 1) → ℝ)
    (hcons_ind : AffineIndependent ℝ (Fin.cons zStar vS : Fin (d + 1) → Fin (d + 1) → ℝ))
    (l : StrongDual ℝ (Fin (d + 1) → ℝ)) (α : ℝ)
    (hα : α < l zStar) (hBelow : ∀ j : Fin d, l (vS j) < α)
    (f : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d + 1) → ℝ)) (hfInj : Function.Injective f)
    (R₀ : Set (Fin d → ℝ))
    (hfR₀ : f '' R₀ = convexHull ℝ (insert zStar (Set.range vS)) ∩ l ⁻¹' {α}) :
    ∃ q : Fin d → Fin d → ℝ,
      AffineIndependent ℝ q ∧ R₀ = convexHull ℝ (Set.range q) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hBelowRange : ∀ w ∈ Set.range vS, l w < α := by
    rintro _ ⟨j, rfl⟩
    exact hBelow j
  have hInter := convexHull_insert_inter_level_eq (d + 1) zStar (Set.range vS)
    (Set.range_nonempty vS) l α hα hBelowRange
  let tau : Fin d → ℝ := fun j => (l zStar - α) / (l zStar - l (vS j))
  let q_ext : Fin d → Fin (d + 1) → ℝ := fun j => AffineMap.lineMap zStar (vS j) (tau j)
  have hRange_q_ext :
      ((fun w => AffineMap.lineMap zStar w ((l zStar - α) / (l zStar - l w))) '' Set.range vS) =
        Set.range q_ext := by
    rw [← Set.range_comp]
    rfl
  rw [hRange_q_ext] at hInter
  have hfR₀_hull : f '' R₀ = convexHull ℝ (Set.range q_ext) := hfR₀.trans hInter
  have hq_ext_mem (j : Fin d) : ∃ x ∈ R₀, f x = q_ext j := by
    have hmem : q_ext j ∈ f '' R₀ := by
      rw [hfR₀_hull]
      exact subset_convexHull ℝ _ (Set.mem_range_self j)
    rcases hmem with ⟨x, hxR₀, hfx⟩
    exact ⟨x, hxR₀, hfx⟩
  choose q hq using hq_ext_mem
  have hfq_range : f '' Set.range q = Set.range q_ext := by
    rw [← Set.range_comp]
    congr 1
    funext j
    exact (hq j).2
  have hR₀_eq : R₀ = convexHull ℝ (Set.range q) := by
    apply hfInj.image_injective
    rw [hfR₀_hull, f.image_convexHull, hfq_range]
  have hlin_vS : LinearIndependent ℝ (fun j : Fin d => vS j -ᵥ zStar) :=
    (affineIndependent_cons_iff_linearIndependent_vsub zStar vS).mp hcons_ind
  have htau_ne (j : Fin d) : tau j ≠ 0 := by
    have h1 : 0 < l zStar - α := sub_pos.mpr hα
    have h2 : 0 < l zStar - l (vS j) := sub_pos.mpr ((hBelow j).trans hα)
    exact (div_pos h1 h2).ne'
  have hq_ext_vsub : (fun j : Fin d => q_ext j -ᵥ zStar) =
      (fun j : Fin d => tau j • (vS j -ᵥ zStar)) := by
    funext j
    simp [q_ext, AffineMap.lineMap_apply]
  have hlin_q_ext : LinearIndependent ℝ (fun j : Fin d => q_ext j -ᵥ zStar) := by
    rw [hq_ext_vsub]
    exact linearIndependent_smul_of_ne_zero hlin_vS htau_ne
  have hcons_q_ext : AffineIndependent ℝ (Fin.cons zStar q_ext : Fin (d + 1) → Fin (d + 1) → ℝ) :=
    (affineIndependent_cons_iff_linearIndependent_vsub zStar q_ext).mpr hlin_q_ext
  let embSucc : Fin d ↪ Fin (d + 1) := ⟨Fin.succ, Fin.succ_injective d⟩
  have hq_ext_ind : AffineIndependent ℝ q_ext := by
    have hcomp := hcons_q_ext.comp_embedding embSucc
    have hfn : (Fin.cons zStar q_ext ∘ embSucc) = q_ext := by
      funext x
      simp [embSucc]
    rwa [hfn] at hcomp
  have hfq_comp : f ∘ q = q_ext := funext (fun j => (hq j).2)
  have hq_ind : AffineIndependent ℝ q := by
    rw [← hfq_comp] at hq_ext_ind
    exact AffineIndependent.of_comp f hq_ext_ind
  exact ⟨q, hq_ind, hR₀_eq⟩

/-- Billera–Lee Section 7 Simplicial Polytope Construction and Low-Dimensional Face Counts:
for any compressed multicomplex `M` on `s` variables of degree `≤ d / 2` with `0 ∈ M` and
degree-slice counts `g k`, the vertex figure `Q₀ ⊆ ℝ^d` of `P_ext = conv(P ∪ {zStar})` at `zStar`
is a simplicial `d`-polytope whose `(k - 1)`-face count for every `1 ≤ k ≤ d / 2` equals
`∑ i ∈ range (d / 2 + 1), if i ≤ k then g i * (d + 1 - i).choose (k - i) else 0`. -/
theorem exists_section7_simplicial_polytope_low_faceCounts
    (d s : ℕ) (hd : 2 ≤ d) (hs : 1 ≤ s)
    (M : Finset (Fin s →₀ ℕ)) (h0M : (0 : Fin s →₀ ℕ) ∈ M)
    (hdeg : ∀ f ∈ M, f.degree ≤ d / 2)
    (hdiv : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ, g ≤ f → g ∈ M)
    (hinit : ∀ f ∈ M, ∀ g : Fin s →₀ ℕ,
      g.degree = f.degree → MacaulayCompressed.colexLT g f → g ∈ M)
    (g : ℕ → ℕ)
    (hcard : ∀ k ≤ d / 2, (M.filter (fun f => f.degree = k)).card = g k) :
    ∃ Q₀ : Set (Fin d → ℝ),
      IsSimplicialDPolytope Q₀ ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ d / 2 →
        faceCount Q₀ (k - 1) =
          ∑ i ∈ Finset.range (d / 2 + 1),
            if i ≤ k then g i * Nat.choose (d + 1 - i) (k - i) else 0 := by
  obtain ⟨t, zStar, ht0, ht, hvis⟩ :=
    exists_section7_visibility_point d s hd hs M h0M hdiv hinit
  let v : Fin (s + d + 1) → Fin (d + 1) → ℝ := fun i => momentCurve (d + 1) (t i)
  let P := convexHull ℝ (Set.range v)
  let P_ext := convexHull ℝ (insert zStar P)
  let W := compressedWords (d / 2) s M
  obtain ⟨hP_ext_d, hzStar_notP, hzStar_exp⟩ :=
    apex_isDPolytope_and_singleton_exposed d s hd hs M h0M t ht zStar hvis.1
  have hP_ext_gen : P_ext = convexHull ℝ (insert zStar (Set.range v)) :=
    convexHull_insert_convexHull zStar (Set.range v)
  -- Construct the cutting hyperplane (l, α) separating zStar from Set.range v
  let u0 : Fin (d / 2) → ℕ := 0
  have hu0W : u0 ∈ W := zero_mem_compressedWords d s M h0M
  have hmu0 : Monotone u0 := fun _ _ _ => le_rfl
  have hbu0 : ∀ r, u0 r ≤ s := fun _ => Nat.zero_le s
  let 𝒢0 := convexHull ℝ (v '' (fullPairedFacet d s u0 : Set (Fin (s + d + 1))))
  have h𝒢0_ne : 𝒢0.Nonempty :=
    ⟨v 0, subset_convexHull ℝ _ ⟨0, zero_mem_fullPairedFacet d s u0, rfl⟩⟩
  have h𝒢0_exp : IsExposed ℝ P 𝒢0 := (fullPairedFacet_exposed d s u0 hbu0 t ht).1
  have h𝒢0_dim : Module.finrank ℝ (affineSpan ℝ 𝒢0).direction = d :=
    fullPairedFacet_finrank d s u0 hmu0 hbu0 t ht
  obtain ⟨l, α0, hlle, _, hlgt, _⟩ := hvis.1 𝒢0 h𝒢0_ne h𝒢0_exp h𝒢0_dim
  have hα0_lt : α0 < l zStar := hlgt ⟨u0, hu0W, rfl⟩
  let α : ℝ := (α0 + l zStar) / 2
  have hα_lt : α < l zStar := by dsimp [α]; linarith
  have hBelowP : ∀ y ∈ P, l y < α := by
    intro y hy
    have := hlle y hy
    dsimp [α]
    linarith
  have hBelowRange : ∀ w ∈ Set.range v, l w < α :=
    fun w hw => hBelowP w (subset_convexHull ℝ _ hw)
  have hSpan : affineSpan ℝ (insert zStar (Set.range v)) = ⊤ := by
    rw [← affineSpan_convexHull, ← hP_ext_gen]
    exact hP_ext_d.2
  have hzStar_exp_gen : IsExposed ℝ (convexHull ℝ (insert zStar (Set.range v))) {zStar} := by
    rwa [← hP_ext_gen]
  obtain ⟨Q₀, f, Ψ_gen, hQ₀_d, hfInj, hfQ₀, hΨ_gen⟩ :=
    exists_vertex_figure_polytope_iso_gen d zStar (Set.range v)
      (Set.finite_range v) (Set.range_nonempty v) hzStar_exp_gen hSpan l α hα_lt hBelowRange
  -- Cast Ψ_gen along hP_ext_gen.symm : convexHull ℝ (insert zStar (Set.range v)) = P_ext
  let eFace : {G : PolytopeFace P_ext // zStar ∈ G.val} ≃o
      {G : PolytopeFace (convexHull ℝ (insert zStar (Set.range v))) // zStar ∈ G.val} :=
    { toFun := fun G => ⟨⟨G.val.val, hP_ext_gen ▸ G.val.property⟩, G.property⟩
      invFun := fun G => ⟨⟨G.val.val, hP_ext_gen.symm ▸ G.val.property⟩, G.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  let Ψ : {G : PolytopeFace P_ext // zStar ∈ G.val} ≃o PolytopeFace Q₀ := eFace.trans Ψ_gen
  have hΨ (G : {G : PolytopeFace P_ext // zStar ∈ G.val}) :
      f '' (Ψ G).val = G.val.val ∩ l ⁻¹' {α} ∧
      ((Ψ G).val = ∅ ↔ G.val.val = {zStar}) ∧
      (G.val.val ≠ {zStar} →
        (Ψ G).val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
            Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1) :=
    hΨ_gen (eFace G)
  refine ⟨Q₀, ⟨hQ₀_d, ?_⟩, ?_⟩
  · -- Prove that every facet R₀ of Q₀ is a simplex
    intro R₀ hR₀_ne hR₀_exp hR₀_dim
    let G : {G : PolytopeFace P_ext // zStar ∈ G.val} := Ψ.symm ⟨R₀, hR₀_exp⟩
    have hΨG_val : (Ψ G).val = R₀ := congrArg Subtype.val (Ψ.apply_symm_apply ⟨R₀, hR₀_exp⟩)
    have hG_ne_apex : G.val.val ≠ {zStar} := by
      intro hEq
      have hEmp : R₀ = ∅ := hΨG_val ▸ (hΨ G).2.1.mpr hEq
      exact Set.not_nonempty_empty (hEmp ▸ hR₀_ne)
    have hG_rank : Module.finrank ℝ (affineSpan ℝ G.val.val).direction = d := by
      have hshift := ((hΨ G).2.2 hG_ne_apex).2
      rw [hΨG_val] at hshift
      omega
    have hG_proper : G.val.val ≠ P_ext := by
      intro hEq
      have htop : Module.finrank ℝ (affineSpan ℝ G.val.val).direction = d + 1 := by
        rw [hEq, hP_ext_d.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
      omega
    obtain ⟨u, huW, S, hSne, hS_sub, _, hG_eq, hG_S_card, _⟩ :=
      apex_proper_face_characterization d s hd hs M h0M t ht zStar hvis.1
        G.val.val G.val.property hG_proper G.property hG_ne_apex
    have hScard : S.card = d := hG_S_card.symm.trans hG_rank
    obtain ⟨hbu, hmu, _⟩ := (mem_compressedWords M u).mp huW
    let 𝒢_u := convexHull ℝ (v '' (fullPairedFacet d s u : Set (Fin (s + d + 1))))
    have h𝒢_u_ne : 𝒢_u.Nonempty :=
      ⟨v 0, subset_convexHull ℝ _ ⟨0, zero_mem_fullPairedFacet d s u, rfl⟩⟩
    have h𝒢_u_exp : IsExposed ℝ P 𝒢_u := (fullPairedFacet_exposed d s u hbu t ht).1
    have h𝒢_u_dim : Module.finrank ℝ (affineSpan ℝ 𝒢_u).direction = d :=
      fullPairedFacet_finrank d s u hmu hbu t ht
    obtain ⟨φ_u, α_u, _, hφ_u_iff, hφ_u_gt, _⟩ := hvis.1 𝒢_u h𝒢_u_ne h𝒢_u_exp h𝒢_u_dim
    have hα_u_lt : α_u < φ_u zStar := hφ_u_gt ⟨u, huW, rfl⟩
    let eS : Fin d ≃ ↥S := Fintype.equivOfCardEq (by simp [hScard])
    let vS : Fin d → Fin (d + 1) → ℝ := fun j => v (eS j).val
    have hvS_ind : AffineIndependent ℝ vS :=
      momentCurve_affineIndependent (d := d + 1) (by omega) (fun j => t (eS j).val)
        (ht.injective.comp (Subtype.val_injective.comp eS.injective))
    have hφ_u_vS (j : Fin d) : φ_u (vS j) = α_u := by
      have hj𝒢 : vS j ∈ 𝒢_u := subset_convexHull ℝ _ ⟨(eS j).val, hS_sub (eS j).property, rfl⟩
      exact (hφ_u_iff (vS j) (h𝒢_u_exp.subset hj𝒢)).mp hj𝒢
    have hcons_ind : AffineIndependent ℝ (Fin.cons zStar vS : Fin (d + 1) → Fin (d + 1) → ℝ) :=
      StellarCone.affineIndependent_cons vS hvS_ind φ_u α_u hφ_u_vS zStar hα_u_lt
    have hvS_range : Set.range vS = v '' (S : Set (Fin (s + d + 1))) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨(eS j).val, (eS j).property, rfl⟩
      · rintro ⟨i, hiS, rfl⟩
        obtain ⟨j, hj⟩ := eS.surjective ⟨i, hiS⟩
        exact ⟨j, by simp [vS, hj]⟩
    have hfR₀ : f '' R₀ = convexHull ℝ (insert zStar (Set.range vS)) ∩ l ⁻¹' {α} := by
      rw [← hΨG_val, (hΨ G).1, hG_eq, hvS_range]
    exact cone_section_simplex (by omega) zStar vS hcons_ind l α hα_lt
      (fun j => hBelowRange (vS j) (Set.mem_range_self _)) f hfInj R₀ hfR₀
  · -- Prove low-dimensional face counts for 1 ≤ k ≤ d / 2
    intro k hk1 hk_half
    obtain ⟨ℱ_Q, hℱ_Q⟩ := StellarAssembly.exists_face_families hQ₀_d
    have hℱ_Q_mem (R₀ : Set (Fin d → ℝ)) :
        R₀ ∈ ℱ_Q (k - 1) ↔ R₀.Nonempty ∧ IsExposed ℝ Q₀ R₀ ∧
          Module.finrank ℝ (affineSpan ℝ R₀).direction = k - 1 := by
      change R₀ ∈ (ℱ_Q (k - 1) : Set (Set (Fin d → ℝ))) ↔ _
      rw [(hℱ_Q (k - 1)).1]
      rfl
    let ℬ : Finset (Finset (Fin (s + d + 1))) :=
      W.biUnion (fun u => (fullPairedFacet d s u).powersetCard k)
    have hℬ_prop {S : Finset (Fin (s + d + 1))} (hS : S ∈ ℬ) :
        S.Nonempty ∧ S.card = k ∧ S.card ≤ d / 2 ∧
          ∃ u ∈ W, S ⊆ fullPairedFacet d s u := by
      obtain ⟨u, huW, hSu⟩ := Finset.mem_biUnion.mp hS
      obtain ⟨hsub, hcardS⟩ := Finset.mem_powersetCard.mp hSu
      exact ⟨Finset.card_pos.mp (by omega), hcardS, by omega, u, huW, hsub⟩
    let H_of (S : Finset (Fin (s + d + 1))) : Set (Fin (d + 1) → ℝ) :=
      convexHull ℝ (insert zStar (v '' (S : Set (Fin (s + d + 1)))))
    have hH_of_prop {S : Finset (Fin (s + d + 1))} (hS : S ∈ ℬ) :
        IsExposed ℝ P_ext (H_of S) ∧
        Module.finrank ℝ (affineSpan ℝ (H_of S)).direction = k ∧
        H_of S ∩ P = convexHull ℝ (v '' (S : Set (Fin (s + d + 1)))) := by
      obtain ⟨hSne, hScard, hSle, u, huW, hsub⟩ := hℬ_prop hS
      obtain ⟨hexp, hrank, hinter⟩ :=
        apex_cone_exposed_of_subset_paired d s hd hs M t ht zStar hvis huW hsub hSne hSle
      exact ⟨hexp, hrank.trans hScard, hinter⟩
    have hcard_eq_ℬ : faceCount Q₀ (k - 1) = ℬ.card := by
      rw [← (hℱ_Q (k - 1)).2]
      symm
      apply Finset.card_bij (fun S (hS : S ∈ ℬ) =>
        (Ψ ⟨⟨H_of S, (hH_of_prop hS).1⟩, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩).val)
      · intro S hS
        rw [hℱ_Q_mem]
        let G : {G : PolytopeFace P_ext // zStar ∈ G.val} :=
          ⟨⟨H_of S, (hH_of_prop hS).1⟩, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
        have hG_rank : Module.finrank ℝ (affineSpan ℝ G.val.val).direction = k :=
          (hH_of_prop hS).2.1
        have hG_ne_apex : G.val.val ≠ {zStar} := by
          intro hEq
          have h0 : Module.finrank ℝ (affineSpan ℝ G.val.val).direction = 0 := by
            rw [hEq, direction_affineSpan, vectorSpan_singleton, finrank_bot]
          omega
        obtain ⟨hΨ_ne, hΨ_rank⟩ := (hΨ G).2.2 hG_ne_apex
        have hΨ_rank' : Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction = k - 1 := by
          omega
        exact ⟨hΨ_ne, (Ψ G).property, hΨ_rank'⟩
      · intro S₁ hS₁ S₂ hS₂ hEq
        let G₁ : {G : PolytopeFace P_ext // zStar ∈ G.val} :=
          ⟨⟨H_of S₁, (hH_of_prop hS₁).1⟩, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
        let G₂ : {G : PolytopeFace P_ext // zStar ∈ G.val} :=
          ⟨⟨H_of S₂, (hH_of_prop hS₂).1⟩, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
        have hG_eq : G₁ = G₂ := Ψ.injective (Subtype.ext hEq)
        have hH_eq : H_of S₁ = H_of S₂ := congrArg (fun G => G.val.val) hG_eq
        have hHull_eq : convexHull ℝ (v '' (S₁ : Set (Fin (s + d + 1)))) =
            convexHull ℝ (v '' (S₂ : Set (Fin (s + d + 1)))) := by
          rw [← (hH_of_prop hS₁).2.2, ← (hH_of_prop hS₂).2.2, hH_eq]
        obtain ⟨_, _, _, u₁, hu₁W, hsub₁⟩ := hℬ_prop hS₁
        obtain ⟨_, _, _, u₂, hu₂W, hsub₂⟩ := hℬ_prop hS₂
        obtain ⟨hbu₁, hmu₁, _⟩ := (mem_compressedWords M u₁).mp hu₁W
        obtain ⟨hbu₂, hmu₂, _⟩ := (mem_compressedWords M u₂).mp hu₂W
        exact (fullPairedFacet_subset_convexHull_eq_iff d s u₁ u₂ hmu₁ hmu₂ hbu₁ hbu₂
          t ht hsub₁ hsub₂).mp hHull_eq
      · intro R₀ hR₀
        obtain ⟨hR₀_ne, hR₀_exp, hR₀_rank⟩ := (hℱ_Q_mem R₀).mp hR₀
        let G : {G : PolytopeFace P_ext // zStar ∈ G.val} := Ψ.symm ⟨R₀, hR₀_exp⟩
        have hΨG_val : (Ψ G).val = R₀ := congrArg Subtype.val (Ψ.apply_symm_apply ⟨R₀, hR₀_exp⟩)
        have hG_ne_apex : G.val.val ≠ {zStar} := by
          intro hEq
          have hEmp : R₀ = ∅ := hΨG_val ▸ (hΨ G).2.1.mpr hEq
          exact Set.not_nonempty_empty (hEmp ▸ hR₀_ne)
        have hG_rank : Module.finrank ℝ (affineSpan ℝ G.val.val).direction = k := by
          have hshift := ((hΨ G).2.2 hG_ne_apex).2
          rw [hΨG_val] at hshift
          omega
        have hG_proper : G.val.val ≠ P_ext := by
          intro hEq
          have htop : Module.finrank ℝ (affineSpan ℝ G.val.val).direction = d + 1 := by
            rw [hEq, hP_ext_d.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
          omega
        obtain ⟨u, huW, S, _, hS_sub, _, hG_eq, hG_S_card, _⟩ :=
          apex_proper_face_characterization d s hd hs M h0M t ht zStar hvis.1
            G.val.val G.val.property hG_proper G.property hG_ne_apex
        have hScard : S.card = k := hG_S_card.symm.trans hG_rank
        have hS_ℬ : S ∈ ℬ := Finset.mem_biUnion.mpr
          ⟨u, huW, Finset.mem_powersetCard.mpr ⟨hS_sub, hScard⟩⟩
        refine ⟨S, hS_ℬ, ?_⟩
        have hG_ext : (⟨⟨H_of S, (hH_of_prop hS_ℬ).1⟩,
            subset_convexHull ℝ _ (Set.mem_insert _ _)⟩ :
            {G : PolytopeFace P_ext // zStar ∈ G.val}) = G := by
          apply Subtype.ext
          apply Subtype.ext
          exact hG_eq.symm
        rw [hG_ext, hΨG_val]
    rw [hcard_eq_ℬ]
    -- Show ℬ.card equals the Nat powersetCard biUnion cardinality
    let ℬ_nat : Finset (Finset ℕ) :=
      W.biUnion (fun u => (fullPairedFacetNat d u).powersetCard k)
    have hℬ_eq_nat : ℬ.card = ℬ_nat.card := by
      apply Finset.card_bij (fun S _ => S.image Fin.val)
      · intro S hS
        obtain ⟨u, huW, hSu⟩ := Finset.mem_biUnion.mp hS
        obtain ⟨hbu, _, _⟩ := (mem_compressedWords M u).mp huW
        obtain ⟨hsub, hcardS⟩ := Finset.mem_powersetCard.mp hSu
        refine Finset.mem_biUnion.mpr ⟨u, huW, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
        · rw [← fullPairedFacet_image_val d s u hbu]
          exact Finset.image_subset_image hsub
        · rw [Finset.card_image_of_injective _ Fin.val_injective, hcardS]
      · intro S₁ _ S₂ _ hEq
        ext i
        have h : i.val ∈ S₁.image Fin.val ↔ i.val ∈ S₂.image Fin.val := by rw [hEq]
        simpa only [Finset.mem_image, Fin.val_inj, exists_eq_right] using h
      · intro T hT
        obtain ⟨u, huW, hTu⟩ := Finset.mem_biUnion.mp hT
        obtain ⟨hbu, _, _⟩ := (mem_compressedWords M u).mp huW
        obtain ⟨hsub, hcardT⟩ := Finset.mem_powersetCard.mp hTu
        let S : Finset (Fin (s + d + 1)) := Finset.univ.filter (fun i => i.val ∈ T)
        have hS_img : S.image Fin.val = T := by
          ext x
          simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hiT, rfl⟩
            exact hiT
          · intro hxT
            exact ⟨⟨x, fullPairedFacetNat_lt_of_bound d s u hbu (hsub hxT)⟩, hxT, rfl⟩
        have hS_sub : S ⊆ fullPairedFacet d s u := by
          intro i hiS
          rw [mem_fullPairedFacet]
          exact hsub (Finset.mem_filter.mp hiS).2
        have hS_card : S.card = k := by
          rw [← hcardT, ← hS_img, Finset.card_image_of_injective _ Fin.val_injective]
        exact ⟨S, Finset.mem_biUnion.mpr ⟨u, huW, Finset.mem_powersetCard.mpr ⟨hS_sub, hS_card⟩⟩,
          hS_img⟩
    rw [hℬ_eq_nat]
    have hmono : ∀ u ∈ W, Monotone u := fun u hu => ((mem_compressedWords M u).mp hu).2.1
    have hlower : ∀ u ∈ W, ∀ r, 0 < u r → lowerBlock u r ∈ W :=
      compressedWords_lowerBlock M hdiv hinit
    have hslice : ∀ j ≤ d / 2,
        (W.filter (fun u => (Finset.univ.filter (fun r => 0 < u r)).card = j)).card = g j :=
      fun j hj => (compressedWords_card_slice M hdeg j).trans (hcard j hj)
    exact fullPaired_faces_card_eq_degree_sum d W g hmono hlower hslice k

end Grunbaum2003.BilleraLee

end
-- END GSufficiencyNextVertexFigureLink.lean

-- BEGIN GNecessityNextBoundaryGeometry.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

/-- An exposed face containing an interior point is the whole ambient polytope. -/
theorem exposed_eq_of_mem_interior {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) {x : Fin d → ℝ} (hxF : x ∈ F)
    (hx : x ∈ interior P) : F = P := by
  obtain ⟨l, hl⟩ := hF ⟨x, hxF⟩
  have hxmax := hxF
  rw [hl] at hxmax
  apply Set.Subset.antisymm hF.subset
  intro z hz
  obtain ⟨ε, hε, hy⟩ := aux_pp_int_step hx (x - z)
  have hstep := hxmax.2 _ hy
  rw [map_add, map_smul, map_sub] at hstep
  have hzx := hxmax.2 z hz
  have heq : l z = l x := by
    change l x + ε * (l x - l z) ≤ l x at hstep
    nlinarith
  rw [hl]
  refine ⟨hz, ?_⟩
  intro w hw
  rw [heq]
  exact hxmax.2 w hw

/-- Strict satisfaction of a finite continuous halfspace presentation gives an interior point. -/
theorem mem_interior_of_strict_halfspaces {d : ℕ} {ι : Type*} [Finite ι]
    {P : Set (Fin d → ℝ)} (l : ι → StrongDual ℝ (Fin d → ℝ)) (a : ι → ℝ)
    (hP : P = {x | ∀ i, l i x ≤ a i}) {x : Fin d → ℝ}
    (hx : ∀ i, l i x < a i) : x ∈ interior P := by
  let U : Set (Fin d → ℝ) := {y | ∀ i, l i y < a i}
  have hopen : IsOpen U := by
    have h : IsOpen (⋂ i, {y | l i y < a i}) :=
      isOpen_iInter_of_finite (fun i => isOpen_lt (l i).continuous continuous_const)
    convert h using 1
    ext y
    simp [U]
  have hsub : U ⊆ P := by
    intro y hy
    rw [hP]
    exact fun i => (hy i).le
  exact mem_interior.mpr ⟨U, hsub, hopen, hx⟩

/-- Every nonempty proper exposed face of a full-dimensional polytope lies in an actual facet.
The finite supporting-halfspace presentation is the already proved geometric presentation. -/
theorem exists_facet_containing {d : ℕ} (hd : 0 < d)
    {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F) (hproper : F ≠ P) :
    ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
      Module.finrank ℝ (affineSpan ℝ G).direction + 1 = d ∧ F ⊆ G := by
  classical
  obtain ⟨ℱ, hℱ⟩ := Grunbaum2003.StellarAssembly.exists_face_families hP
  obtain ⟨l, a, hrep, hcontact, _, _, _⟩ :=
    stellarFacetPresentation_exists hd P hP (ℱ (d - 1)) (hℱ (d - 1)).1
  let I := {G : Set (Fin d → ℝ) // G ∈ ℱ (d - 1)}
  let : Fintype I := (ℱ (d - 1)).fintypeCoeSort
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  have hbound (i : I) {z : Fin d → ℝ} (hz : z ∈ P) : l i z ≤ a i := by
    rw [hrep] at hz
    exact hz i
  have hfacne : (ℱ (d - 1)).Nonempty := by
    by_contra hn
    obtain ⟨x, hx⟩ := hFne
    apply hproper (exposed_eq_of_mem_interior hF hx ?_)
    apply mem_interior_of_strict_halfspaces l a hrep
    intro i
    exact False.elim (hn ⟨i.val, i.property⟩)
  let : Nonempty I := ⟨⟨hfacne.choose, hfacne.choose_spec⟩⟩
  have hex : ∃ i : I, F ⊆ i.val := by
    by_contra hnone
    have hw : ∀ i : I, ∃ z ∈ F, z ∉ i.val := by
      intro i
      exact Set.not_subset.mp (fun hi => hnone ⟨i, hi⟩)
    choose z hzF hzi using hw
    have hstrict (i : I) : l i (z i) < a i := by
      have hle := hbound i (hF.subset (hzF i))
      apply lt_of_le_of_ne hle
      intro heq
      apply hzi i
      rw [hcontact i]
      exact ⟨hF.subset (hzF i), heq⟩
    let q : Fin d → ℝ := Finset.univ.centerMass (fun _ : I => (1 : ℝ)) z
    have hcard : (0 : ℝ) < Fintype.card I := by
      exact_mod_cast Fintype.card_pos
    have hqF : q ∈ F := by
      apply (hF.convex hconv).centerMass_mem
      · intro i hi
        exact zero_le_one
      · simpa using hcard
      · intro i hi
        exact hzF i
    have hqstrict (i : I) : l i q < a i := by
      have hs : ∑ j : I, l i (z j) < ∑ _j : I, a i :=
        Finset.sum_lt_sum (fun j _ => hbound i (hF.subset (hzF j)))
          ⟨i, Finset.mem_univ i, hstrict i⟩
      have hs' : (∑ j : I, l i (z j)) < a i * Fintype.card I := by
        simpa [mul_comm] using hs
      have hdv := (div_lt_iff₀ hcard).mpr hs'
      simpa [q, Finset.centerMass, map_smul, map_sum, div_eq_inv_mul] using hdv
    exact hproper (exposed_eq_of_mem_interior hF hqF
      (mem_interior_of_strict_halfspaces l a hrep hqstrict))
  obtain ⟨i, hi⟩ := hex
  have hiData : i.val.Nonempty ∧ IsExposed ℝ P i.val ∧
      Module.finrank ℝ (affineSpan ℝ i.val).direction = d - 1 := by
    have hm : i.val ∈ (ℱ (d - 1) : Set (Set (Fin d → ℝ))) := i.property
    rw [(hℱ (d - 1)).1] at hm
    exact hm
  exact ⟨i.val, hiData.1, hiData.2.1, by omega, hi⟩

end Grunbaum2003.GNecessityNext
-- END GNecessityNextBoundaryGeometry.lean

-- BEGIN StellarBaseFaces.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarCone

/-- All vertex-subset hulls of the selected simplex facet are old exposed faces. -/
theorem base_subset_exposed {d : ℕ} {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hlevel : ∀ i, φ (v i) = a)
    (y : Fin d → ℝ) (hy : a < φ y) (s : Finset (Fin d)) :
    IsExposed ℝ P (convexHull ℝ (v '' (s : Set (Fin d)))) := by
  let u : Fin (d + 1) → Fin d → ℝ := Fin.cons y v
  have hu : AffineIndependent ℝ u := affineIndependent_cons v hv φ a hlevel y hy
  have hface := (StellarFaceTools.simplex_subset_hull_isExposed_and_labels d u hu
    (s.image Fin.succ)).1
  have himage : u '' ((s.image Fin.succ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) =
      v '' (s : Set (Fin d)) := by
    rw [Finset.coe_image, Set.image_image]
    congr 1
  rw [himage] at hface
  have hFU : F ⊆ convexHull ℝ (Set.range u) := by
    rw [hFv]
    apply convexHull_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, rfl⟩
  have hSF : convexHull ℝ (v '' (s : Set (Fin d))) ⊆ F := by
    rw [hFv]
    exact convexHull_mono (Set.image_subset_range _ _)
  exact StellarFaceTools.isExposed_trans_polytope d P hP F _ hF (hface.mono hFU hSF)

/-- In particular, the generating points of the selected facet are actual old vertices. -/
theorem base_vertices_exposed {d : ℕ} {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hlevel : ∀ i, φ (v i) = a)
    (y : Fin d → ℝ) (hy : a < φ y) (i : Fin d) : IsExposed ℝ P {v i} := by
  simpa using base_subset_exposed hP hF v hv hFv φ a hlevel y hy {i}

/-- Every old exposed face in the chosen simplex facet has a vertex-subset presentation. -/
theorem old_face_in_base {d : ℕ} {P F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ)
    (hFv : F = convexHull ℝ (Set.range v))
    (hG : IsExposed ℝ P G) (hGF : G ⊆ F) (hGne : G.Nonempty) :
    ∃ s : Finset (Fin d), s.Nonempty ∧ G = convexHull ℝ (v '' (s : Set (Fin d))) := by
  let s := Finset.univ.filter (fun i => v i ∈ G)
  have hGr : IsExposed ℝ (convexHull ℝ (Set.range v)) G := by
    rw [← hFv]
    exact hG.mono hF.subset hGF
  have hi : G ∩ Set.range v = v '' (s : Set (Fin d)) := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Finset.mem_filter.mp hi).2, Set.mem_range_self i⟩
  have heq : G = convexHull ℝ (v '' (s : Set (Fin d))) := by
    rw [← hi]
    exact StellarFaceTools.finite_face_hull v hGr
  refine ⟨s, ?_, heq⟩
  have hne := heq ▸ hGne
  obtain ⟨_, i, hi, rfl⟩ := convexHull_nonempty_iff.mp hne
  exact ⟨i, hi⟩

/-- An old face which survives after adding the apex exposes its cone whenever
it lies in the selected support plane. -/
theorem cone_exposed_of_survival {d : ℕ} {P G : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hbound : ∀ x ∈ P, φ x ≤ a)
    (y : Fin d → ℝ) (hy : a < φ y)
    (hGne : G.Nonempty) (hGP : G ⊆ P) (hlevel : ∀ x ∈ G, φ x = a)
    (hG : IsExposed ℝ (convexHull ℝ (insert y P)) G) :
    IsExposed ℝ (convexHull ℝ (insert y P)) (convexHull ℝ (insert y G)) := by
  obtain ⟨w, hw⟩ := hGne
  obtain ⟨ℓ, hdesc⟩ := hG ⟨w, hw⟩
  have hwP := hGP hw
  have hwQ : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hwP)
  have hyQ : y ∈ convexHull ℝ (insert y P) := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hmaxQ : ∀ z ∈ convexHull ℝ (insert y P), ℓ z ≤ ℓ w := by
    have hw' := hw
    rw [hdesc] at hw'
    exact hw'.2
  have hmaxP : ∀ z ∈ P, ℓ z ≤ ℓ w := fun z hz =>
    hmaxQ z (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hz))
  have hlow : ℓ y < ℓ w := by
    apply lt_of_le_of_ne (hmaxQ y hyQ)
    intro heq
    have hyG : y ∈ G := by
      rw [hdesc]
      exact ⟨hyQ, fun z hz => heq ▸ hmaxQ z hz⟩
    exact (not_le_of_gt hy) (hbound y (hGP hyG))
  have hface : ℓ.toExposed P = G := by
    ext x
    constructor
    · intro hx
      have heq : ℓ x = ℓ w := le_antisymm (hmaxP x hx.1) (hx.2 w hwP)
      rw [hdesc]
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
        fun z hz => heq ▸ hmaxQ z hz⟩
    · intro hx
      have hx' := hx
      rw [hdesc] at hx'
      exact ⟨hGP hx, fun z hz => hx'.2 z (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hz))⟩
  rw [← hface]
  apply cone_exposed_of_support_below_apex hconv φ a hbound ℓ w hwP hmaxP _ y hy hlow
  rw [hface]
  exact hlevel

end Grunbaum2003.StellarCone
-- END StellarBaseFaces.lean

-- BEGIN GNecessityNextBoundaryComplex.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

/-- Actual exposed vertices of the canonical polytope. -/
abbrev PolytopeVertex {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {x : Fin d → ℝ // IsExposed ℝ P {x}}

theorem finite_polytopeVertex {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    Finite (PolytopeVertex P) := by
  have hv : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    apply Set.Finite.of_finite_image (f := fun x => ({x} : Set (Fin d → ℝ)))
    · apply (Grunbaum2003.StellarAssembly.finite_exposed_faces hP).subset
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx y hy hxy
      exact Set.singleton_injective hxy
  exact hv.to_subtype

/-- The geometric hull of a finite set of actual vertices. -/
def vertexHull {d : ℕ} {P : Set (Fin d → ℝ)} (s : Finset (PolytopeVertex P)) :
    Set (Fin d → ℝ) := convexHull ℝ (Subtype.val '' (s : Set (PolytopeVertex P)))

theorem vertexHull_subset {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (s : Finset (PolytopeVertex P)) : vertexHull s ⊆ P := by
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  apply convexHull_min _ hconv
  rintro _ ⟨v, hv, rfl⟩
  exact v.property.subset (Set.mem_singleton v.val)

/-- No actual polytope vertex can be generated by a finite collection omitting that vertex. -/
theorem vertex_mem_vertexHull_iff {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (s : Finset (PolytopeVertex P)) (v : PolytopeVertex P) :
    v.val ∈ vertexHull s ↔ v ∈ s := by
  constructor
  · intro hv
    have he : IsExposed ℝ (vertexHull s) {v.val} :=
      v.property.mono (vertexHull_subset hP s) (Set.singleton_subset_iff.mpr hv)
    obtain ⟨w, hw, hwv⟩ := extremePoints_convexHull_subset he.isExtreme.mem_extremePoints
    have hwv' : w = v := Subtype.ext hwv
    exact hwv' ▸ hw
  · intro hv
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩

theorem vertexHull_injective {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    Function.Injective (@vertexHull d P) := by
  intro s t hst
  ext v
  rw [← vertex_mem_vertexHull_iff hP s v, ← vertex_mem_vertexHull_iff hP t v, hst]

/-- The boundary complex consists of nonempty vertex sets contained in actual facets.
The empty face is excluded exactly as in Mathlib's PreAbstractSimplicialComplex convention. -/
def polytopeBoundary {d : ℕ} (P : Set (Fin d → ℝ)) :
    PreAbstractSimplicialComplex (PolytopeVertex P) where
  faces := {s | s.Nonempty ∧ ∃ F : Set (Fin d → ℝ),
    F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d ∧
      ∀ v ∈ s, v.val ∈ F}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    obtain ⟨F, hne, hex, hdim, hvertices⟩ := hs.2
    exact ⟨ht, F, hne, hex, hdim, fun v hv => hvertices v (hts hv)⟩

theorem facet_ne_polytope {d : ℕ} {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d) : F ≠ P := by
  intro h
  rw [h, hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hdim
  omega

/-- Every vertex subset of an actual simplex facet is an exposed face of the original polytope. -/
theorem simplex_facet_subset_exposed {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v)) (s : Finset (Fin d)) :
    IsExposed ℝ P (convexHull ℝ (v '' (s : Set (Fin d)))) := by
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  obtain ⟨c, hc⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hP.2
  obtain ⟨x, hx⟩ := hFne
  obtain ⟨φ, hφ⟩ := hF ⟨x, hx⟩
  have hxmax := hx
  rw [hφ] at hxmax
  have hlevel (i : Fin d) : φ (v i) = φ x := by
    have hi : v i ∈ F := by
      rw [hFv]
      exact subset_convexHull ℝ _ (Set.mem_range_self i)
    rw [hφ] at hi
    exact le_antisymm (hxmax.2 _ hi.1) (hi.2 _ hxmax.1)
  have hcstrict : φ c < φ x := by
    apply lt_of_le_of_ne (hxmax.2 c (interior_subset hc))
    intro heq
    have hcF : c ∈ F := by
      rw [hφ]
      refine ⟨interior_subset hc, ?_⟩
      intro z hz
      rw [heq]
      exact hxmax.2 z hz
    exact facet_ne_polytope hP hdim (exposed_eq_of_mem_interior hF hcF hc)
  let y := x + (x - c)
  have hy : φ x < φ y := by
    dsimp [y]
    rw [map_add, map_sub]
    linarith
  exact Grunbaum2003.StellarCone.base_subset_exposed hP hF v hv hFv φ (φ x)
    hlevel y hy s

/-- The vertices of an actual simplex facet are actual polytope vertices. -/
theorem simplex_facet_vertices_exposed {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v)) (i : Fin d) :
    IsExposed ℝ P {v i} := by
  simpa using simplex_facet_subset_exposed hP hFne hF hdim v hv hFv {i}

theorem vertex_in_facet_range {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ)
    (hFv : F = convexHull ℝ (Set.range v)) (x : PolytopeVertex P) (hx : x.val ∈ F) :
    x.val ∈ Set.range v := by
  have he : IsExposed ℝ F {x.val} :=
    x.property.mono hF.subset (Set.singleton_subset_iff.mpr hx)
  rw [hFv] at he
  exact extremePoints_convexHull_subset he.isExtreme.mem_extremePoints

/-- Every abstract boundary face spans a nonempty proper actual exposed face. -/
theorem vertexHull_boundary_face {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) :
    (vertexHull s).Nonempty ∧ IsExposed ℝ P (vertexHull s) ∧ vertexHull s ≠ P := by
  classical
  obtain ⟨hsne, F, hFne, hF, hdim, hsF⟩ := hs
  obtain ⟨v, hv, hFv⟩ := hP.2 F hFne hF hdim
  let t : Finset (Fin d) := Finset.univ.filter
    (fun i => ∃ x ∈ s, x.val = v i)
  have him : Subtype.val '' (s : Set (PolytopeVertex P)) = v '' (t : Set (Fin d)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := vertex_in_facet_range hF v hFv x (hsF x hx)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hi.symm⟩, hi⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨x, hx, hxi⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨x, hx, hxi⟩
  have hH : vertexHull s = convexHull ℝ (v '' (t : Set (Fin d))) := by
    rw [vertexHull, him]
  have hHF : vertexHull s ⊆ F := by
    rw [hH, hFv]
    exact convexHull_mono (Set.image_subset_range _ _)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hsne
    exact ⟨x.val, (vertex_mem_vertexHull_iff hP.1 s x).mpr hx⟩
  · rw [hH]
    exact simplex_facet_subset_exposed hP.1 hFne hF hdim v hv hFv t
  · intro h
    exact facet_ne_polytope hP.1 hdim (Set.Subset.antisymm hF.subset (h ▸ hHF))

/-- Every nonempty proper actual exposed face is spanned by one abstract boundary face. -/
theorem exists_boundary_face_vertexHull {d : ℕ} (hd : 0 < d)
    {P F : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F) (hproper : F ≠ P) :
    ∃ s : Finset (PolytopeVertex P), s ∈ polytopeBoundary P ∧ vertexHull s = F := by
  classical
  obtain ⟨G, hGne, hG, hdim, hFG⟩ := exists_facet_containing hd hP.1 hFne hF hproper
  obtain ⟨v, hv, hGv⟩ := hP.2 G hGne hG hdim
  obtain ⟨t, htne, hFt⟩ := Grunbaum2003.StellarCone.old_face_in_base hG v hGv hF hFG hFne
  let w : Fin d → PolytopeVertex P := fun i =>
    ⟨v i, simplex_facet_vertices_exposed hP.1 hGne hG hdim v hv hGv i⟩
  let s := t.image w
  have hsn : s.Nonempty := htne.image w
  have hs : s ∈ polytopeBoundary P := by
    refine ⟨hsn, G, hGne, hG, hdim, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    change v i ∈ G
    rw [hGv]
    exact subset_convexHull ℝ _ (Set.mem_range_self i)
  refine ⟨s, hs, ?_⟩
  rw [hFt]
  change convexHull ℝ (Subtype.val '' (↑(t.image w) : Set (PolytopeVertex P))) = _
  rw [Finset.coe_image, Set.image_image]

/-- Boundary face size is exactly one more than its affine dimension. -/
theorem vertexHull_boundary_finrank {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) :
    Module.finrank ℝ (affineSpan ℝ (vertexHull s)).direction + 1 = s.card := by
  classical
  obtain ⟨hsne, F, hFne, hF, hdim, hsF⟩ := hs
  obtain ⟨v, hv, hFv⟩ := hP.2 F hFne hF hdim
  have hindex : ∀ x : ↥s, ∃ i : Fin d, v i = x.val.val := by
    intro x
    exact vertex_in_facet_range hF v hFv x.val (hsF x.val x.property)
  choose f hf using hindex
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    calc x.val.val = v (f x) := (hf x).symm
      _ = v (f y) := congrArg v hxy
      _ = y.val.val := hf y
  have hAI : AffineIndependent ℝ (fun x : ↥s => x.val.val) := by
    convert hv.comp_embedding (⟨f, hfi⟩ : ↥s ↪ Fin d) using 1
    funext x
    exact (hf x).symm
  have hrange : Set.range (fun x : ↥s => x.val.val) =
      Subtype.val '' (s : Set (PolytopeVertex P)) := by
    ext x
    simp
  let : Nonempty ↥s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  rw [vertexHull, affineSpan_convexHull, direction_affineSpan, ← hrange]
  simpa only [Fintype.card_coe] using hAI.finrank_vectorSpan_add_one

/-- The abstract boundary and the actual nonempty proper exposed faces are equivalent. -/
noncomputable def boundaryFaceEquiv {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P) :
    {s : Finset (PolytopeVertex P) // s ∈ polytopeBoundary P} ≃
      {F : Set (Fin d → ℝ) // F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P} :=
  Equiv.ofBijective
    (fun s => ⟨vertexHull s.val, vertexHull_boundary_face hP s.val s.property⟩)
    ⟨fun s t h => Subtype.ext (vertexHull_injective hP.1 (congrArg Subtype.val h)),
      fun F => by
        obtain ⟨s, hs, heq⟩ := exists_boundary_face_vertexHull hd hP
          F.property.1 F.property.2.1 F.property.2.2
        exact ⟨⟨s, hs⟩, Subtype.ext heq⟩⟩

/-- Cardinalities of abstract boundary faces agree with the canonical geometric faceCount. -/
theorem boundary_faceCount {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P) (j : ℕ) (hj : j < d) :
    {s : Finset (PolytopeVertex P) | s ∈ polytopeBoundary P ∧ s.card = j + 1}.ncard =
      faceCount P j := by
  change _ = {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = j}.ncard
  apply Set.BijOn.ncard_eq (f := @vertexHull d P)
  refine ⟨?_, (vertexHull_injective hP.1).injOn, ?_⟩
  · intro s hs
    obtain ⟨hne, hex, _⟩ := vertexHull_boundary_face hP s hs.1
    have hdim := vertexHull_boundary_finrank hP s hs.1
    exact ⟨hne, hex, Nat.add_right_cancel (hdim.trans hs.2)⟩
  · intro F hF
    have hproper : F ≠ P := by
      intro heq
      have hdim := hF.2.2
      rw [heq, hP.1.2, AffineSubspace.direction_top, finrank_top,
        Module.finrank_fin_fun] at hdim
      omega
    obtain ⟨s, hs, heq⟩ := exists_boundary_face_vertexHull hd hP hF.1 hF.2.1 hproper
    have hdim := vertexHull_boundary_finrank hP s hs
    rw [heq, hF.2.2] at hdim
    exact ⟨s, ⟨hs, hdim.symm⟩, heq⟩

end Grunbaum2003.GNecessityNext
-- END GNecessityNextBoundaryComplex.lean

-- BEGIN GNecessityNextLinearParameters.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

variable {ι κ R : Type*} [CommRing R]

/-- The actual linear polynomial with the specified coordinate coefficients. -/
noncomputable def parameterLinearForm [Fintype ι] (a : ι → R) : MvPolynomial ι R :=
  ∑ i, a i • MvPolynomial.X i

/-- An invertible coefficient basis gives an actual polynomial change of coordinates. -/
noncomputable def linearParameterEquiv [Fintype ι]
    (b : Module.Basis κ R (ι → R)) : MvPolynomial κ R ≃ₐ[R] MvPolynomial ι R :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.trans
    (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R ι))

@[simp] theorem linearParameterEquiv_X [Fintype ι]
    (b : Module.Basis κ R (ι → R)) (i : κ) :
    linearParameterEquiv b (MvPolynomial.X i) = parameterLinearForm (b i) := by
  change SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R ι)
    ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X i)) = _
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  change SymmetricAlgebra.lift ((Pi.basisFun R ι).constr R MvPolynomial.X)
    (SymmetricAlgebra.ι R (ι → R) (b i)) = _
  rw [SymmetricAlgebra.lift_ι_apply, Module.Basis.constr_apply_fintype]
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply, parameterLinearForm]

theorem linearParameterEquiv_toAlgHom [Fintype ι]
    (b : Module.Basis κ R (ι → R)) :
    (linearParameterEquiv b).toAlgHom = MvPolynomial.aeval (fun i => parameterLinearForm (b i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  change linearParameterEquiv b (MvPolynomial.X i) =
    MvPolynomial.aeval (fun j => parameterLinearForm (b j)) (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, linearParameterEquiv_X]

/-- The coordinate rows of a basis of column vectors themselves form a basis.
For a facet basis b, the entry i,j is literally the i-coordinate of vertex vector b j. -/
noncomputable def coordinateRowBasis [Fintype κ]
    (b : Module.Basis ι R (κ → R)) : Module.Basis κ R (ι → R) :=
  (Pi.basisFun R κ).dualBasis.map (b.constr R).symm

@[simp] theorem coordinateRowBasis_apply [Fintype κ]
    (b : Module.Basis ι R (κ → R)) (i : κ) (j : ι) :
    coordinateRowBasis b i j = b j i := by
  simp only [coordinateRowBasis, Module.Basis.map_apply, Module.Basis.constr_symm_apply,
    Module.Basis.dualBasis_apply, Pi.basisFun_repr]

/-- The polynomial parameter map associated with the actual ambient coordinate rows. -/
noncomputable def coordinateParameterMap [Fintype ι] (v : ι → κ → R) :
    MvPolynomial κ R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval (fun i => parameterLinearForm (fun j => v j i))

theorem killCompl_parameterLinearForm [Fintype ι] (F : Finset ι) (a : ι → R) :
    MvPolynomial.killCompl (f := (Subtype.val : ↥F → ι)) Subtype.val_injective
      (parameterLinearForm a) = parameterLinearForm (fun j : ↥F => a j.val) := by
  classical
  let q := MvPolynomial.killCompl (R := R) (f := (Subtype.val : ↥F → ι))
    Subtype.val_injective
  have hinside (j : ↥F) : q (MvPolynomial.X j.val) = MvPolynomial.X j := by
    simpa only [MvPolynomial.rename_X] using
      (MvPolynomial.killCompl_rename_app (R := R) (f := (Subtype.val : ↥F → ι))
        Subtype.val_injective (MvPolynomial.X j))
  have houtside (j : ι) (hj : j ∉ F) : q (MvPolynomial.X j) = 0 := by
    have hnot : j ∉ Set.range (Subtype.val : ↥F → ι) := by
      rintro ⟨x, rfl⟩
      exact hj x.property
    simp only [q, MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hnot]
  change q (parameterLinearForm a) = _
  simp only [parameterLinearForm, map_sum, map_smul]
  calc
    ∑ j : ι, a j • q (MvPolynomial.X j) = ∑ j ∈ F, a j • q (MvPolynomial.X j) := by
      apply (Finset.sum_subset (Finset.subset_univ F) ?_).symm
      intro j hj hjF
      rw [houtside j hjF, smul_zero]
    _ = ∑ j : ↥F, a j.val • q (MvPolynomial.X j.val) := (Finset.sum_coe_sort F _).symm
    _ = ∑ j : ↥F, a j.val • MvPolynomial.X j := by simp only [hinside]

/-- Restricting the actual coordinate parameter map to a facet gives the explicit algebra
equivalence induced by its coordinate-row basis. Shifted vertices v−c can be supplied as v. -/
theorem restricted_coordinateParameterMap [Fintype ι] [Fintype κ]
    (v : ι → κ → R) (F : Finset ι) (b : Module.Basis (↥F) R (κ → R))
    (hb : ∀ j : ↥F, b j = v j.val) :
    (MvPolynomial.killCompl (R := R) (f := (Subtype.val : ↥F → ι)) Subtype.val_injective).comp
      (coordinateParameterMap v) = (linearParameterEquiv (coordinateRowBasis b)).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  change MvPolynomial.killCompl Subtype.val_injective
      (MvPolynomial.aeval (fun k => parameterLinearForm (fun j => v j k)) (MvPolynomial.X i)) =
    linearParameterEquiv (coordinateRowBasis b) (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, killCompl_parameterLinearForm, linearParameterEquiv_X]
  apply congrArg parameterLinearForm
  funext j
  rw [coordinateRowBasis_apply, hb]

end Grunbaum2003.GNecessityNext
-- END GNecessityNextLinearParameters.lean

-- BEGIN GNecessityNextFacetParameters.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

/-- Translating an affinely independent family on a hyperplane away from the origin
gives a linearly independent family. The hyperplane separation is used explicitly. -/
theorem linearIndependent_sub_of_level {d : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (c : Fin d → ℝ) (φ : StrongDual ℝ (Fin d → ℝ)) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (hne : a ≠ φ c) :
    LinearIndependent ℝ (fun i => v i - c) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro w hw i
  have hscalar := congrArg φ hw
  simp only [map_sum, map_smul, map_sub, hlevel, map_zero, smul_eq_mul] at hscalar
  have hsum : ∑ i, w i = 0 := by
    rw [← Finset.sum_mul] at hscalar
    exact (mul_eq_zero.mp hscalar).resolve_right (sub_ne_zero.mpr hne)
  have hvec : ∑ i, w i • v i = 0 := by
    simp_rw [smul_sub] at hw
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, zero_smul, sub_zero] at hw
    exact hw
  exact hv.eq_zero_of_sum_eq_zero hsum hvec i (Finset.mem_univ i)

/-- Every actual boundary face has affinely independent vertices. -/
theorem boundary_affineIndependent {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) :
    AffineIndependent ℝ (fun x : ↥s => x.val.val) := by
  classical
  obtain ⟨_, F, hFne, hF, hdim, hsF⟩ := hs
  obtain ⟨v, hv, hFv⟩ := hP.2 F hFne hF hdim
  have hindex : ∀ x : ↥s, ∃ i : Fin d, v i = x.val.val := by
    intro x
    exact vertex_in_facet_range hF v hFv x.val (hsF x.val x.property)
  choose f hf using hindex
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    calc x.val.val = v (f x) := (hf x).symm
      _ = v (f y) := congrArg v hxy
      _ = y.val.val := hf y
  convert hv.comp_embedding (⟨f, hfi⟩ : ↥s ↪ Fin d) using 1
  funext x
  exact (hf x).symm

/-- Actual boundary vertices, shifted by any interior point, are linearly independent.
The original polytope and its vertex labels are retained. -/
theorem boundary_shifted_linearIndependent {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) (c : Fin d → ℝ) (hc : c ∈ interior P) :
    LinearIndependent ℝ (fun x : ↥s => x.val.val - c) := by
  have hAI := boundary_affineIndependent hP s hs
  obtain ⟨_, F, hFne, hF, hdim, hsF⟩ := hs
  obtain ⟨x, hx⟩ := hFne
  obtain ⟨φ, hφ⟩ := hF ⟨x, hx⟩
  have hxmax := hx
  rw [hφ] at hxmax
  have hlevel (v : ↥s) : φ v.val.val = φ x := by
    have hv := hsF v.val v.property
    rw [hφ] at hv
    exact le_antisymm (hxmax.2 _ hv.1) (hv.2 _ hxmax.1)
  have hne : φ x ≠ φ c := by
    intro heq
    have hcF : c ∈ F := by
      rw [hφ]
      refine ⟨interior_subset hc, ?_⟩
      intro z hz
      rw [← heq]
      exact hxmax.2 z hz
    exact facet_ne_polytope hP.1 hdim (exposed_eq_of_mem_interior hF hcF hc)
  exact linearIndependent_sub_of_level _ hAI c φ (φ x) hlevel hne

/-- The shifted vertices of an actual boundary facet form an ambient vector basis. -/
noncomputable def boundaryFacetBasis {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) (hcard : s.card = d)
    (c : Fin d → ℝ) (hc : c ∈ interior P) : Module.Basis (↥s) ℝ (Fin d → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun x : ↥s => x.val.val - c)
    (boundary_shifted_linearIndependent hP s hs c hc)
    (by simpa only [Fintype.card_coe, Module.finrank_fin_fun] using hcard)

@[simp] theorem boundaryFacetBasis_apply {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) (hcard : s.card = d)
    (c : Fin d → ℝ) (hc : c ∈ interior P) (j : ↥s) :
    boundaryFacetBasis hP s hs hcard c hc j = j.val.val - c := by
  simp only [boundaryFacetBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- The literal coordinate parameters of the original boundary, with an interior-point
shift in their coefficients, restrict to an algebra equivalence on every actual facet. -/
theorem boundary_coordinateParameter_equiv {d : ℕ} {P : Set (Fin d → ℝ)}
    [Fintype (PolytopeVertex P)]
    (hP : IsSimplicialDPolytope P) (s : Finset (PolytopeVertex P))
    (hs : s ∈ polytopeBoundary P) (hcard : s.card = d)
    (c : Fin d → ℝ) (hc : c ∈ interior P) :
    ∃ e : MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (↥s) ℝ,
      (MvPolynomial.killCompl (R := ℝ)
        (f := (Subtype.val : ↥s → PolytopeVertex P)) Subtype.val_injective).comp
          (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c)) = e.toAlgHom := by
  refine ⟨linearParameterEquiv (coordinateRowBasis (boundaryFacetBasis hP s hs hcard c hc)), ?_⟩
  exact restricted_coordinateParameterMap _ s (boundaryFacetBasis hP s hs hcard c hc)
    (fun j => boundaryFacetBasis_apply hP s hs hcard c hc j)

end Grunbaum2003.GNecessityNext
-- END GNecessityNextFacetParameters.lean

-- BEGIN BoundaryFacetSupports.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

/-- Actual facets represented by their full vertex sets in the already identified boundary. -/
abbrev BoundaryFacet {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {s : Finset (PolytopeVertex P) // s ∈ polytopeBoundary P ∧ s.card = d}

/-- A common interior point normalizes the actual facet supporting forms to one.
Their vertex contact sets are exactly the facet labels, so these forms are
nonzero and pairwise distinct. No abstract normal-fan data are assumed. -/
theorem exists_boundary_facet_supports {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P) :
    ∃ c ∈ interior P, ∃ l : BoundaryFacet P → StrongDual ℝ (Fin d → ℝ),
      (∀ F, ∀ x ∈ P, l F (x - c) ≤ 1) ∧
      (∀ F, ∀ v : PolytopeVertex P, l F (v.val - c) = 1 ↔ v ∈ F.val) ∧
      (∀ F, l F ≠ 0) ∧ Function.Injective l := by
  classical
  obtain ⟨ℱ, hℱ⟩ := Grunbaum2003.StellarAssembly.exists_face_families hP.1
  obtain ⟨φ, a, hrep, hcontact, c, hc, hstrict⟩ :=
    stellarFacetPresentation_exists hd P hP.1 (ℱ (d - 1)) (hℱ (d - 1)).1
  let I := {G : Set (Fin d → ℝ) // G ∈ ℱ (d - 1)}
  have hfacet (F : BoundaryFacet P) : vertexHull F.val ∈ ℱ (d - 1) := by
    have hface := vertexHull_boundary_face hP F.val F.property.1
    have hrank := vertexHull_boundary_finrank hP F.val F.property.1
    change vertexHull F.val ∈ (ℱ (d - 1) : Set (Set (Fin d → ℝ)))
    rw [(hℱ (d - 1)).1]
    refine ⟨hface.1, hface.2.1, ?_⟩
    rw [F.property.2] at hrank
    omega
  let index : BoundaryFacet P → I := fun F => ⟨vertexHull F.val, hfacet F⟩
  let δ : BoundaryFacet P → ℝ := fun F => a (index F) - φ (index F) c
  have hδ (F : BoundaryFacet P) : 0 < δ F := sub_pos.mpr (hstrict (index F))
  let l : BoundaryFacet P → StrongDual ℝ (Fin d → ℝ) :=
    fun F => (δ F)⁻¹ • φ (index F)
  have hformula (F : BoundaryFacet P) (x : Fin d → ℝ) :
      l F (x - c) = (φ (index F) x - φ (index F) c) / δ F := by
    simp only [l, smul_apply, map_sub, smul_eq_mul, div_eq_inv_mul, mul_sub]
  have hle (F : BoundaryFacet P) (x : Fin d → ℝ) (hx : x ∈ P) :
      l F (x - c) ≤ 1 := by
    rw [hformula, div_le_one (hδ F)]
    have hx' : φ (index F) x ≤ a (index F) := by
      rw [hrep] at hx
      exact hx (index F)
    change φ (index F) x - φ (index F) c ≤ a (index F) - φ (index F) c
    exact sub_le_sub_right hx' _
  have heq (F : BoundaryFacet P) (v : PolytopeVertex P) :
      l F (v.val - c) = 1 ↔ v ∈ F.val := by
    have hvP : v.val ∈ P := v.property.subset (Set.mem_singleton _)
    have hcontact' : v.val ∈ vertexHull F.val ↔ φ (index F) v.val = a (index F) := by
      change v.val ∈ (index F).val ↔ _
      rw [hcontact (index F)]
      exact and_iff_right hvP
    rw [hformula, div_eq_one_iff_eq (ne_of_gt (hδ F))]
    have hdifference : φ (index F) v.val - φ (index F) c = δ F ↔
        φ (index F) v.val = a (index F) := by
      dsimp only [δ]
      exact sub_left_inj
    rw [hdifference, ← hcontact', vertex_mem_vertexHull_iff hP.1]
  refine ⟨c, hc, l, hle, heq, ?_, ?_⟩
  · intro F hzero
    obtain ⟨v, hv⟩ := (polytopeBoundary P).isRelLowerSet_faces F.property.1 |>.1
    have h := (heq F v).mpr hv
    rw [hzero] at h
    norm_num at h
  · intro F G hFG
    apply Subtype.ext
    ext v
    rw [← heq F v, ← heq G v, hFG]

end Grunbaum2003.GNecessityNext
-- END BoundaryFacetSupports.lean

-- BEGIN BoundaryFacetFamily.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

/-- The actual vertex-set facet family is finite. -/
theorem finite_boundaryFacet {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    Finite (BoundaryFacet P) := by
  classical
  let : Finite (PolytopeVertex P) := finite_polytopeVertex hP
  let : Fintype (PolytopeVertex P) := Fintype.ofFinite _
  infer_instance

/-- Every actual boundary face is contained in an actual full-size facet. -/
theorem boundary_face_subset_facet {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (s : Finset (PolytopeVertex P)) (hs : s ∈ polytopeBoundary P) :
    ∃ F : BoundaryFacet P, s ⊆ F.val := by
  obtain ⟨_, G, hGne, hG, hGdim, hsG⟩ := hs
  obtain ⟨t, ht, htG⟩ := exists_boundary_face_vertexHull hd hP hGne hG
    (facet_ne_polytope hP.1 hGdim)
  have htcard : t.card = d := by
    have h := vertexHull_boundary_finrank hP t ht
    rw [htG] at h
    exact h.symm.trans hGdim
  refine ⟨⟨t, ht, htcard⟩, ?_⟩
  intro v hv
  apply (vertex_mem_vertexHull_iff hP.1 t v).mp
  rw [htG]
  exact hsG v hv

/-- A positive-dimensional full-dimensional simplicial polytope has an actual
facet. An empty facet presentation would make the compact polytope all of space. -/
theorem nonempty_boundaryFacet {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P) :
    Nonempty (BoundaryFacet P) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hcompact : IsCompact P := by
    obtain ⟨V, hfin, _, rfl⟩ := hP.1.1
    exact hfin.isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨ℱ, hℱ⟩ := Grunbaum2003.StellarAssembly.exists_face_families hP.1
  obtain ⟨φ, a, hrep, _⟩ :=
    stellarFacetPresentation_exists hd P hP.1 (ℱ (d - 1)) (hℱ (d - 1)).1
  have hfacne : (ℱ (d - 1)).Nonempty := by
    by_contra hn
    have hPu : P = Set.univ := by
      rw [hrep]
      apply Set.eq_univ_of_forall
      intro x i
      exact (hn ⟨i.val, i.property⟩).elim
    rw [hPu] at hcompact
    exact noncompact_univ (Fin d → ℝ) hcompact
  obtain ⟨G, hGmem⟩ := hfacne
  have hGdata : G.Nonempty ∧ IsExposed ℝ P G ∧
      Module.finrank ℝ (affineSpan ℝ G).direction = d - 1 := by
    have h : G ∈ (ℱ (d - 1) : Set (Set (Fin d → ℝ))) := hGmem
    rwa [(hℱ (d - 1)).1] at h
  have hGdim : Module.finrank ℝ (affineSpan ℝ G).direction + 1 = d := by
    rw [hGdata.2.2]
    omega
  obtain ⟨s, hs, hsG⟩ := exists_boundary_face_vertexHull hd hP hGdata.1 hGdata.2.1
    (facet_ne_polytope hP.1 hGdim)
  have hcard : s.card = d := by
    have h := vertexHull_boundary_finrank hP s hs
    rw [hsG] at h
    exact h.symm.trans hGdim
  exact ⟨⟨s, hs, hcard⟩⟩

end Grunbaum2003.GNecessityNext
-- END BoundaryFacetFamily.lean

-- BEGIN FaceRingFacetSeparation.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

/-- Actual facets separate a nonempty exposed face from any polytope point
outside that face. This is the face-as-intersection-of-facets property needed
for the adjacent-facet step in a geometric line shelling. -/
theorem exists_facet_containing_face_omitting_point {d : ℕ} (hd : 0 < d)
    {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    {z : Fin d → ℝ} (hzP : z ∈ P) (hzF : z ∉ F) :
    ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
      Module.finrank ℝ (affineSpan ℝ G).direction + 1 = d ∧ F ⊆ G ∧ z ∉ G := by
  classical
  obtain ⟨ℱ, hℱ⟩ := Grunbaum2003.StellarAssembly.exists_face_families hP
  obtain ⟨l, a, hrep, hcontact, _, _, _⟩ :=
    stellarFacetPresentation_exists hd P hP (ℱ (d - 1)) (hℱ (d - 1)).1
  let I := {G : Set (Fin d → ℝ) // G ∈ ℱ (d - 1)}
  let : Fintype I := (ℱ (d - 1)).fintypeCoeSort
  have hproper : F ≠ P := by
    intro h
    exact hzF (h.symm ▸ hzP)
  obtain ⟨G, hGne, hG, hGdim, _⟩ := exists_facet_containing hd hP hFne hF hproper
  have hGmem : G ∈ ℱ (d - 1) := by
    change G ∈ (ℱ (d - 1) : Set (Set (Fin d → ℝ)))
    rw [(hℱ (d - 1)).1]
    exact ⟨hGne, hG, by omega⟩
  let : Nonempty I := ⟨⟨G, hGmem⟩⟩
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  have hbound (i : I) {x : Fin d → ℝ} (hx : x ∈ P) : l i x ≤ a i := by
    rw [hrep] at hx
    exact hx i
  have hex : ∃ i : I, F ⊆ i.val ∧ z ∉ i.val := by
    by_contra hnone
    have hz (i : I) (hi : F ⊆ i.val) : z ∈ i.val := by
      by_contra hzi
      exact hnone ⟨i, hi, hzi⟩
    obtain ⟨x₀, hx₀⟩ := hFne
    have hw : ∀ i : I, ∃ x ∈ F, (¬ F ⊆ i.val → x ∉ i.val) := by
      intro i
      by_cases hi : F ⊆ i.val
      · exact ⟨x₀, hx₀, fun hn => (hn hi).elim⟩
      · obtain ⟨x, hxF, hxi⟩ := Set.not_subset.mp hi
        exact ⟨x, hxF, fun _ => hxi⟩
    choose x hxF hxi using hw
    let q : Fin d → ℝ := Finset.univ.centerMass (fun _ : I => (1 : ℝ)) x
    have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hqF : q ∈ F := by
      apply (hF.convex hconv).centerMass_mem
      · intro i hi
        exact zero_le_one
      · simpa using hcard
      · intro i hi
        exact hxF i
    have hstrict (i : I) (hi : ¬ F ⊆ i.val) : l i q < a i := by
      have hxi' : l i (x i) < a i := by
        apply lt_of_le_of_ne (hbound i (hF.subset (hxF i)))
        intro heq
        apply hxi i hi
        rw [hcontact i]
        exact ⟨hF.subset (hxF i), heq⟩
      have hs : ∑ j : I, l i (x j) < ∑ _j : I, a i :=
        Finset.sum_lt_sum (fun j _ => hbound i (hF.subset (hxF j)))
          ⟨i, Finset.mem_univ i, hxi'⟩
      have hs' : (∑ j : I, l i (x j)) < a i * Fintype.card I := by
        simpa [mul_comm] using hs
      have hdv := (div_lt_iff₀ hcard).mpr hs'
      simpa [q, Finset.centerMass, map_smul, map_sum, div_eq_inv_mul] using hdv
    let U : Set (Fin d → ℝ) := {y | ∀ i : I, F ⊆ i.val ∨ l i y < a i}
    have hopen : IsOpen U := by
      have h : IsOpen (⋂ i : I, {y | F ⊆ i.val ∨ l i y < a i}) := by
        apply isOpen_iInter_of_finite
        intro i
        by_cases hi : F ⊆ i.val
        · simpa only [hi, true_or, Set.ofPred_true] using isOpen_univ
        · simpa only [hi, false_or] using isOpen_lt (l i).continuous continuous_const
      convert h using 1
      ext y
      simp [U]
    have hqU : q ∈ U := by
      intro i
      by_cases hi : F ⊆ i.val
      · exact Or.inl hi
      · exact Or.inr (hstrict i hi)
    have hqInt : q ∈ interior U := by simpa only [hopen.interior_eq] using hqU
    obtain ⟨ε, hε, hyU⟩ := aux_pp_int_step hqInt (q - z)
    have hyP : q + ε • (q - z) ∈ P := by
      rw [hrep]
      intro i
      by_cases hi : F ⊆ i.val
      · have hqi : l i q = a i := by
          have h := hi hqF
          rw [hcontact i] at h
          exact h.2
        have hzi : l i z = a i := by
          have h := hz i hi
          rw [hcontact i] at h
          exact h.2
        simp only [map_add, map_smul, map_sub, hqi, hzi, sub_self, smul_zero, add_zero]
        exact le_rfl
      · exact ((hyU i).resolve_left hi).le
    obtain ⟨ψ, hψ⟩ := hF ⟨q, hqF⟩
    have hqmax := hqF
    rw [hψ] at hqmax
    have hzlt : ψ z < ψ q := by
      apply lt_of_le_of_ne (hqmax.2 z hzP)
      intro heq
      apply hzF
      rw [hψ]
      exact ⟨hzP, fun w hw => (hqmax.2 w hw).trans_eq heq.symm⟩
    have hbad := hqmax.2 _ hyP
    rw [map_add, map_smul, map_sub] at hbad
    change ψ q + ε * (ψ q - ψ z) ≤ ψ q at hbad
    nlinarith
  obtain ⟨i, hi, hzi⟩ := hex
  have hiData : i.val.Nonempty ∧ IsExposed ℝ P i.val ∧
      Module.finrank ℝ (affineSpan ℝ i.val).direction = d - 1 := by
    have hm : i.val ∈ (ℱ (d - 1) : Set (Set (Fin d → ℝ))) := i.property
    rw [(hℱ (d - 1)).1] at hm
    exact hm
  exact ⟨i.val, hiData.1, hiData.2.1, by omega, hi, hzi⟩

end Grunbaum2003.GNecessityNext
-- END FaceRingFacetSeparation.lean

-- BEGIN BoundaryFacetNeighbors.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

/-- Removing one vertex from an actual simplicial facet gives a ridge contained
in another actual facet that omits the removed vertex. The proof uses the
geometric face-separation theorem; no abstract pseudomanifold postulate is assumed. -/
theorem boundary_facet_neighbour {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (s : Finset (PolytopeVertex P)) (hs : s ∈ polytopeBoundary P)
    (hcard : s.card = d) (v : PolytopeVertex P) (hv : v ∈ s) :
    ∃ t : Finset (PolytopeVertex P), t ∈ polytopeBoundary P ∧
      t.card = d ∧ s.erase v ⊆ t ∧ v ∉ t := by
  classical
  have hrne : (s.erase v).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hv, hcard]
    omega
  have hr : s.erase v ∈ polytopeBoundary P :=
    ((polytopeBoundary P).isRelLowerSet_faces hs).2 (Finset.erase_subset v s) hrne
  obtain ⟨hRne, hR, _⟩ := vertexHull_boundary_face hP (s.erase v) hr
  have hvP : v.val ∈ P := v.property.subset (Set.mem_singleton _)
  have hvR : v.val ∉ vertexHull (s.erase v) := by
    rw [vertex_mem_vertexHull_iff hP.1]
    exact Finset.notMem_erase v s
  obtain ⟨G, hGne, hG, hGdim, hRG, hvG⟩ :=
    exists_facet_containing_face_omitting_point (by omega) hP.1 hRne hR hvP hvR
  obtain ⟨t, ht, htG⟩ := exists_boundary_face_vertexHull (by omega) hP hGne hG
    (facet_ne_polytope hP.1 hGdim)
  have htcard : t.card = d := by
    have h := vertexHull_boundary_finrank hP t ht
    rw [htG] at h
    exact h.symm.trans hGdim
  refine ⟨t, ht, htcard, ?_, ?_⟩
  · intro x hx
    apply (vertex_mem_vertexHull_iff hP.1 t x).mp
    rw [htG]
    exact hRG ((vertex_mem_vertexHull_iff hP.1 (s.erase v) x).mpr hx)
  · intro hvt
    apply hvG
    rw [← htG]
    exact (vertex_mem_vertexHull_iff hP.1 t v).mpr hvt

end Grunbaum2003.GNecessityNext
-- END BoundaryFacetNeighbors.lean

-- BEGIN FaceRingGenericVector.lean
set_option autoImplicit false

namespace Grunbaum2003.GNecessityNext

/-- Finitely many distinct nonzero real linear forms possess one vector on
which their values are all nonzero and pairwise distinct. The finite family
of forms and pairwise differences has a common point outside its kernels. -/
theorem exists_vector_distinguishing_linear_forms {ι V : Type*} [Finite ι]
    [AddCommGroup V] [Module ℝ V]
    (L : ι → V →ₗ[ℝ] ℝ) (hinj : Function.Injective L) (hne : ∀ i, L i ≠ 0) :
    ∃ w : V, (∀ i, L i w ≠ 0) ∧ Function.Injective (fun i => L i w) := by
  classical
  let f : ι ⊕ {ij : ι × ι // ij.1 ≠ ij.2} → Module.Dual ℝ V :=
    Sum.elim L (fun ij => L ij.val.1 - L ij.val.2)
  have hf : ∀ i, f i ≠ 0 := by
    rintro (i | ⟨⟨i, j⟩, hij⟩)
    · exact hne i
    · change L i - L j ≠ 0
      exact sub_ne_zero.mpr (fun heq => hij (hinj heq))
  obtain ⟨w, hw⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f (by
    intro i
    by_contra h
    apply hf i
    ext x
    by_contra hx
    exact h ⟨x, hx⟩)
  refine ⟨w, fun i => hw (Sum.inl i), ?_⟩
  intro i j heq
  by_contra hij
  have hd := hw (Sum.inr ⟨⟨i, j⟩, hij⟩)
  change L i w - L j w ≠ 0 at hd
  exact hd (sub_eq_zero.mpr heq)

/-- The coordinate-space specialization used to order actual normalized
facet supports in the line-shelling construction. -/
theorem exists_generic_facet_direction {ι : Type*} [Finite ι] (d : ℕ)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hinj : Function.Injective L) (hne : ∀ i, L i ≠ 0) :
    ∃ w : Fin d → ℝ,
      (∀ i, L i w ≠ 0) ∧ ∀ i j, i ≠ j → L i w ≠ L j w := by
  obtain ⟨w, hw0, hw⟩ := exists_vector_distinguishing_linear_forms L hinj hne
  exact ⟨w, hw0, fun i j hij heq => hij (hw heq)⟩

end Grunbaum2003.GNecessityNext
-- END FaceRingGenericVector.lean

-- BEGIN LineShellingCriterion.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

variable {ι κ : Type*}

/-- A finite support calculation underlying geometric line shellings. Scores
are normalized facet supports evaluated at a common direction. The coefficients
are that direction's coordinates in the chosen facet basis. Each ridge has a
second facet, encoded explicitly by `hneighbour`; no shelling is assumed. -/
theorem earlier_facet_iff_negative_coordinate
    (F S : Finset ι) (hSF : S ⊆ F) (facets : κ → Finset ι)
    (α : ι → ℝ) (supportValue : κ → ι → ℝ) (score : κ → ℝ) (baseScore : ℝ)
    (hbound : ∀ j, ∀ i ∈ F, supportValue j i ≤ 1)
    (hcontact : ∀ j, ∀ i ∈ F, supportValue j i = 1 ↔ i ∈ facets j)
    (hscore : ∀ j, score j - baseScore =
      ∑ i ∈ F, α i * (supportValue j i - 1))
    (hneighbour : ∀ i ∈ F, ∃ j, F.erase i ⊆ facets j ∧ i ∉ facets j) :
    (∃ j, baseScore < score j ∧ S ⊆ facets j) ↔
      ∃ i ∈ F, i ∉ S ∧ α i < 0 := by
  classical
  constructor
  · rintro ⟨j, hj, hSj⟩
    by_contra hnone
    have hterm : ∀ i ∈ F, α i * (supportValue j i - 1) ≤ 0 := by
      intro i hi
      by_cases hiS : i ∈ S
      · rw [(hcontact j i hi).mpr (hSj hiS), sub_self, mul_zero]
      · have hα : 0 ≤ α i := by
          by_contra hn
          exact hnone ⟨i, hi, hiS, lt_of_not_ge hn⟩
        exact mul_nonpos_of_nonneg_of_nonpos hα (sub_nonpos.mpr (hbound j i hi))
    have hs : (∑ i ∈ F, α i * (supportValue j i - 1)) ≤ 0 :=
      Finset.sum_nonpos hterm
    rw [← hscore j] at hs
    linarith
  · rintro ⟨i, hiF, hiS, hα⟩
    obtain ⟨j, hFj, hij⟩ := hneighbour i hiF
    have hvalue : supportValue j i < 1 := by
      apply lt_of_le_of_ne (hbound j i hiF)
      intro heq
      exact hij ((hcontact j i hiF).mp heq)
    have hsum : (∑ k ∈ F, α k * (supportValue j k - 1)) =
        α i * (supportValue j i - 1) := by
      apply Finset.sum_eq_single i
      · intro k hk hki
        have hkG := hFj (Finset.mem_erase.mpr ⟨hki, hk⟩)
        rw [(hcontact j k hk).mpr hkG, sub_self, mul_zero]
      · intro hnot
        exact (hnot hiF).elim
    refine ⟨j, ?_, ?_⟩
    · have hp := mul_pos_of_neg_of_neg hα (sub_neg.mpr hvalue)
      rw [← hsum, ← hscore j] at hp
      linarith
    · intro k hk
      apply hFj
      refine Finset.mem_erase.mpr ⟨?_, hSF hk⟩
      intro hki
      exact hiS (hki ▸ hk)

/-- The faces appearing for the first time are exactly the interval above the
negative-coordinate vertices. This supplies the combinatorial shelling clause
once the displayed support data come from actual facets. -/
theorem new_face_iff_negative_coordinate_subset
    (F S : Finset ι) (hSF : S ⊆ F) (facets : κ → Finset ι)
    (α : ι → ℝ) (supportValue : κ → ι → ℝ) (score : κ → ℝ) (baseScore : ℝ)
    (hbound : ∀ j, ∀ i ∈ F, supportValue j i ≤ 1)
    (hcontact : ∀ j, ∀ i ∈ F, supportValue j i = 1 ↔ i ∈ facets j)
    (hscore : ∀ j, score j - baseScore =
      ∑ i ∈ F, α i * (supportValue j i - 1))
    (hneighbour : ∀ i ∈ F, ∃ j, F.erase i ⊆ facets j ∧ i ∉ facets j) :
    (¬ ∃ j, baseScore < score j ∧ S ⊆ facets j) ↔
      F.filter (fun i => α i < 0) ⊆ S := by
  classical
  rw [earlier_facet_iff_negative_coordinate F S hSF facets α supportValue
    score baseScore hbound hcontact hscore hneighbour]
  constructor
  · intro h i hi
    obtain ⟨hiF, hα⟩ := Finset.mem_filter.mp hi
    by_contra hiS
    exact h ⟨i, hiF, hiS, hα⟩
  · intro h ⟨i, hiF, hiS, hα⟩
    exact hiS (h (Finset.mem_filter.mpr ⟨hiF, hα⟩))

end Grunbaum2003.GNecessityNext
-- END LineShellingCriterion.lean

-- BEGIN BoundaryLineShelling.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

/-- The actual facets of every simplicial polytope of dimension at least two
possess distinct ordering scores and exact restriction-face intervals. This
geometric statement supplies the combinatorial input of the shelling induction.
It is proved from normalized supports, genuine neighboring facets, and a generic
direction expressed in the actual shifted vertex basis of each facet. -/
theorem boundary_line_shelling_criterion {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P) :
    ∃ score : BoundaryFacet P → ℝ, Function.Injective score ∧
      ∃ r : BoundaryFacet P → Finset (PolytopeVertex P),
        (∀ F, r F ⊆ F.val) ∧
        ∀ (F : BoundaryFacet P) (S : Finset (PolytopeVertex P)) (_hSF : S ⊆ F.val),
          (¬ ∃ G : BoundaryFacet P, score F < score G ∧ S ⊆ G.val) ↔ r F ⊆ S := by
  classical
  let : Finite (BoundaryFacet P) := finite_boundaryFacet hP.1
  obtain ⟨c, hc, l, hbound, hcontact, hne, hinj⟩ :=
    exists_boundary_facet_supports (by omega) hP
  let L : BoundaryFacet P → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun F => (l F).toLinearMap
  have hLi : Function.Injective L := by
    intro F G hFG
    apply hinj
    ext x
    exact congrArg (fun f : (Fin d → ℝ) →ₗ[ℝ] ℝ => f x) hFG
  have hLn (F : BoundaryFacet P) : L F ≠ 0 := by
    intro hzero
    apply hne F
    ext x
    exact congrArg (fun f : (Fin d → ℝ) →ₗ[ℝ] ℝ => f x) hzero
  obtain ⟨w, _, hw⟩ := exists_vector_distinguishing_linear_forms L hLi hLn
  let b (F : BoundaryFacet P) : Module.Basis (↥F.val) ℝ (Fin d → ℝ) :=
    boundaryFacetBasis hP F.val F.property.1 F.property.2 c hc
  let α (F : BoundaryFacet P) (v : PolytopeVertex P) : ℝ :=
    if hv : v ∈ F.val then (b F).repr w ⟨v, hv⟩ else 0
  have hα (F : BoundaryFacet P) (v : ↥F.val) :
      α F v.val = (b F).repr w v := by
    simp only [α, dif_pos v.property]
  have hrepr (F : BoundaryFacet P) :
      ∑ v ∈ F.val, α F v • (v.val - c) = w := by
    calc
      ∑ v ∈ F.val, α F v • (v.val - c) =
          ∑ v : ↥F.val, α F v.val • (v.val.val - c) :=
        (Finset.sum_coe_sort F.val _).symm
      _ = ∑ v : ↥F.val, (b F).repr w v • b F v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hα]
        simp only [b, boundaryFacetBasis_apply]
      _ = w := (b F).sum_repr w
  let score (F : BoundaryFacet P) : ℝ := l F w
  let r (F : BoundaryFacet P) : Finset (PolytopeVertex P) :=
    F.val.filter (fun v => α F v < 0)
  refine ⟨score, hw, r, fun F => Finset.filter_subset _ _, ?_⟩
  intro F S hSF
  apply new_face_iff_negative_coordinate_subset F.val S hSF
    (fun G : BoundaryFacet P => G.val) (α F)
    (fun G v => l G (v.val - c)) score (score F)
  · intro G v hv
    exact hbound G v.val (v.property.subset (Set.mem_singleton _))
  · intro G v hv
    exact hcontact G v
  · intro G
    change l G w - l F w = _
    rw [← hrepr F, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(hcontact F v).mpr hv]
    ring
  · intro v hv
    obtain ⟨t, ht, htc, hsub, hnot⟩ :=
      boundary_facet_neighbour hd hP F.val F.property.1 F.property.2 v hv
    refine ⟨⟨t, ht, htc⟩, ?_, hnot⟩
    intro x hx
    exact hsub (by simpa only [Finset.mem_erase] using hx)

end Grunbaum2003.GNecessityNext
-- END BoundaryLineShelling.lean

-- BEGIN FiniteShellingPrefixes.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

/-- The nonempty faces lying in a facet among the first `k+1` entries. -/
def finiteFacetPrefix {V : Type*} {N : ℕ}
    (f : Fin (N + 1) → Finset V) (k : Fin (N + 1)) :
    PreAbstractSimplicialComplex V where
  faces := {S | S.Nonempty ∧ ∃ j, j ≤ k ∧ S ⊆ f j}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨hS.1, ?_⟩
    intro T hTS hT
    obtain ⟨j, hj, hSj⟩ := hS.2
    exact ⟨hT, j, hj, hTS.trans hSj⟩

@[simp] theorem mem_finiteFacetPrefix {V : Type*} {N : ℕ}
    (f : Fin (N + 1) → Finset V) (k : Fin (N + 1)) (S : Finset V) :
    S ∈ finiteFacetPrefix f k ↔ S.Nonempty ∧ ∃ j, j ≤ k ∧ S ⊆ f j := Iff.rfl

theorem finiteFacetPrefix_first {V : Type*} {N : ℕ}
    (f : Fin (N + 1) → Finset V) (S : Finset V) :
    S ∈ finiteFacetPrefix f 0 ↔ S.Nonempty ∧ S ⊆ f 0 := by
  rw [mem_finiteFacetPrefix]
  constructor
  · rintro ⟨hS, j, hj, hSj⟩
    have hj0 : j = 0 := le_antisymm hj (Fin.zero_le j)
    exact ⟨hS, hj0 ▸ hSj⟩
  · rintro ⟨hS, hSf⟩
    exact ⟨hS, 0, le_rfl, hSf⟩

theorem finiteFacetPrefix_last {V : Type*} {N : ℕ}
    (f : Fin (N + 1) → Finset V) (S : Finset V) :
    S ∈ finiteFacetPrefix f (Fin.last N) ↔ S.Nonempty ∧ ∃ j, S ⊆ f j := by
  rw [mem_finiteFacetPrefix]
  constructor
  · rintro ⟨hS, j, _, hSj⟩
    exact ⟨hS, j, hSj⟩
  · rintro ⟨hS, j, hSj⟩
    exact ⟨hS, j, Fin.le_last j, hSj⟩

theorem finiteFacetPrefix_nonempty {V : Type*} {N : ℕ}
    (f : Fin (N + 1) → Finset V) (hf : ∀ j, (f j).Nonempty)
    (k : Fin (N + 1)) : (finiteFacetPrefix f k).faces.Nonempty :=
  ⟨f k, hf k, k, le_rfl, Finset.Subset.refl _⟩

/-- Distinct real scores give a descending enumeration of any prescribed
finite cardinality. The order is pulled back from the reversed score order. -/
theorem exists_descending_score_enumeration {J : Type*} [Fintype J]
    (score : J → ℝ) (hinj : Function.Injective score)
    (N : ℕ) (hcard : Fintype.card J = N + 1) :
    ∃ e : Fin (N + 1) ≃ J, StrictAnti (fun j => score (e j)) := by
  let : LinearOrder J := LinearOrder.lift'
    (fun j => OrderDual.toDual (score j)) (fun _ _ h => hinj h)
  let e := Fintype.orderIsoFinOfCardEq J hcard
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  exact e.strictMono hij

theorem exists_finite_descending_score_enumeration {J : Type*} [Finite J] [Nonempty J]
    (score : J → ℝ) (hinj : Function.Injective score) :
    ∃ (N : ℕ) (e : Fin (N + 1) ≃ J), StrictAnti (fun j => score (e j)) := by
  let := Fintype.ofFinite J
  have hpos : 0 < Fintype.card J := Fintype.card_pos
  obtain ⟨e, he⟩ := exists_descending_score_enumeration score hinj
    (Fintype.card J - 1) (by omega)
  exact ⟨Fintype.card J - 1, e, he⟩

/-- The exact restriction criterion produces every combinatorial premise of
`unique_parameter_representation_shelling`. No shelling or algebraic
representation is assumed. The final prefix is the full facet-generated complex. -/
theorem exists_prefixes_of_descending_facet_criterion {V J : Type*}
    (N : ℕ) (F R : J → Finset V) (score : J → ℝ)
    (e : Fin (N + 1) ≃ J) (hscore : StrictAnti (fun j => score (e j)))
    (hRF : ∀ j, R j ⊆ F j)
    (hcriterion : ∀ j (S : Finset V) (_hSF : S ⊆ F j),
      (¬ ∃ k, score j < score k ∧ S ⊆ F k) ↔ R j ⊆ S) :
    ∃ C : Fin (N + 1) → PreAbstractSimplicialComplex V,
      R (e 0) = ∅ ∧
      (∀ S : Finset V, S ∈ C 0 ↔ S.Nonempty ∧ S ⊆ F (e 0)) ∧
      (∀ j : Fin N, (R (e j.succ)).Nonempty) ∧
      (∀ j : Fin N, R (e j.succ) ∉ C j.castSucc) ∧
      (∀ j : Fin N, R (e j.succ) ⊆ F (e j.succ)) ∧
      (∀ (j : Fin N) (S : Finset V),
        S ∈ C j.succ ↔ S ∈ C j.castSucc ∨
          R (e j.succ) ⊆ S ∧ S ⊆ F (e j.succ)) ∧
      ∀ S : Finset V,
        S ∈ C (Fin.last N) ↔ S.Nonempty ∧ ∃ k : J, S ⊆ F k := by
  classical
  let f : Fin (N + 1) → Finset V := fun j => F (e j)
  let C := finiteFacetPrefix f
  have hearlier (j : Fin N) (S : Finset V) :
      (∃ k : J, score (e j.succ) < score k ∧ S ⊆ F k) ↔
        ∃ i : Fin (N + 1), i ≤ j.castSucc ∧ S ⊆ f i := by
    constructor
    · rintro ⟨k, hk, hSk⟩
      have hlt : e.symm k < j.succ := hscore.lt_iff_gt.mp (by simpa using hk)
      refine ⟨e.symm k, ?_, ?_⟩
      · change (e.symm k).val ≤ j.val
        change (e.symm k).val < j.val + 1 at hlt
        omega
      · simpa only [f, e.apply_symm_apply] using hSk
    · rintro ⟨i, hi, hSi⟩
      refine ⟨e i, hscore ?_, hSi⟩
      change i.val < j.val + 1
      change i.val ≤ j.val at hi
      omega
  have hnew (j : Fin N) (S : Finset V) (hSF : S ⊆ F (e j.succ)) :
      (¬ ∃ i : Fin (N + 1), i ≤ j.castSucc ∧ S ⊆ f i) ↔ R (e j.succ) ⊆ S := by
    rw [← hearlier j S]
    exact hcriterion (e j.succ) S hSF
  have hr0 : R (e 0) = ∅ := by
    apply Finset.subset_empty.mp
    apply (hcriterion (e 0) ∅ (Finset.empty_subset _)).mp
    rintro ⟨k, hk, _⟩
    have hlt : e.symm k < (0 : Fin (N + 1)) :=
      hscore.lt_iff_gt.mp (by simpa using hk)
    exact (not_lt_of_ge (Fin.zero_le _)) hlt
  have hrne (j : Fin N) : (R (e j.succ)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hn := (hnew j ∅ (Finset.empty_subset _)).mpr (by rw [he])
    exact hn ⟨0, Fin.zero_le _, Finset.empty_subset _⟩
  have hrOld (j : Fin N) : R (e j.succ) ∉ C j.castSucc := by
    rintro ⟨_, i, hi, hRi⟩
    exact ((hnew j _ (hRF (e j.succ))).mpr (Finset.Subset.refl _)) ⟨i, hi, hRi⟩
  refine ⟨C, hr0, finiteFacetPrefix_first f, hrne, hrOld,
    fun j => hRF (e j.succ), ?_, ?_⟩
  · intro j S
    constructor
    · rintro ⟨hSne, i, hi, hSi⟩
      by_cases hOld : S ∈ C j.castSucc
      · exact Or.inl hOld
      · right
        have his : i = j.succ := by
          apply Fin.ext
          have hnot : ¬ i ≤ j.castSucc := fun h => hOld ⟨hSne, i, h, hSi⟩
          change i.val ≤ j.val + 1 at hi
          change ¬ i.val ≤ j.val at hnot
          change i.val = j.val + 1
          omega
        have hSF : S ⊆ F (e j.succ) := his ▸ hSi
        refine ⟨(hnew j S hSF).mp ?_, hSF⟩
        rintro ⟨k, hk, hSk⟩
        exact hOld ⟨hSne, k, hk, hSk⟩
    · rintro (⟨hSne, i, hi, hSi⟩ | ⟨hRS, hSF⟩)
      · refine ⟨hSne, i, ?_, hSi⟩
        change i.val ≤ j.val + 1
        change i.val ≤ j.val at hi
        omega
      · exact ⟨(hrne j).mono hRS, j.succ, le_rfl, hSF⟩
  · intro S
    rw [finiteFacetPrefix_last]
    constructor
    · rintro ⟨hS, j, hSj⟩
      exact ⟨hS, e j, hSj⟩
    · rintro ⟨hS, k, hSk⟩
      exact ⟨hS, e.symm k, by simpa only [f, e.apply_symm_apply] using hSk⟩

end Grunbaum2003.GNecessityNext
-- END FiniteShellingPrefixes.lean

-- BEGIN GNecessityNextFaceRing.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R : Type*}

/-- The squarefree exponent vector associated to a finite vertex set. -/
noncomputable def squarefreeExponent (s : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

@[simp] theorem squarefreeExponent_support (s : Finset ι) :
    (squarefreeExponent s).support = s := by
  classical
  ext i
  simp [squarefreeExponent, Finsupp.mem_support_iff, Finsupp.indicator_apply]

/-- Divisibility by a squarefree monomial is exactly containment of vertex supports. -/
theorem squarefreeExponent_le_iff (s : Finset ι) (m : ι →₀ ℕ) :
    squarefreeExponent s ≤ m ↔ s ⊆ m.support := by
  classical
  constructor
  · intro h i hi
    have hpos : 1 ≤ m i := by simpa [squarefreeExponent, hi] using h i
    exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hpos)
  · intro h i
    by_cases hi : i ∈ s
    · have hm : m i ≠ 0 := Finsupp.mem_support_iff.mp (h hi)
      simpa [squarefreeExponent, hi] using Nat.one_le_iff_ne_zero.mpr hm
    · simp [squarefreeExponent, hi]

/-- The Stanley–Reisner ideal is generated by squarefree monomials of nonfaces.
Mathlib's complex omits the empty face, so only nonempty nonfaces are generators. -/
noncomputable def nonfaceIdeal [CommSemiring R] (K : PreAbstractSimplicialComplex ι) :
    Ideal (MvPolynomial ι R) :=
  Ideal.span ((fun m : ι →₀ ℕ => MvPolynomial.monomial m (1 : R)) ''
    (squarefreeExponent '' {s : Finset ι | s.Nonempty ∧ s ∉ K}))

/-- Exact support characterization of membership in the Stanley–Reisner ideal. -/
theorem mem_nonfaceIdeal_iff [CommSemiring R] (K : PreAbstractSimplicialComplex ι)
    (p : MvPolynomial ι R) :
    p ∈ nonfaceIdeal K ↔
      ∀ m ∈ p.support, m.support.Nonempty ∧ m.support ∉ K := by
  classical
  rw [nonfaceIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h m hm
    obtain ⟨_, ⟨s, hs, rfl⟩, hle⟩ := h m hm
    have hsub := (squarefreeExponent_le_iff s m).mp hle
    refine ⟨hs.1.mono hsub, ?_⟩
    intro hface
    exact hs.2 ((K.isRelLowerSet_faces hface).2 hsub hs.1)
  · intro h m hm
    exact ⟨squarefreeExponent m.support, ⟨m.support, h m hm, rfl⟩,
      (squarefreeExponent_le_iff m.support m).mpr (Finset.Subset.refl _)⟩

/-- Coefficients supported on actual faces completely detect the nonface ideal. -/
theorem mem_nonfaceIdeal_iff_coeff_zero [CommSemiring R]
    (K : PreAbstractSimplicialComplex ι) (p : MvPolynomial ι R) :
    p ∈ nonfaceIdeal K ↔
      ∀ m : ι →₀ ℕ, m.support = ∅ ∨ m.support ∈ K → p.coeff m = 0 := by
  classical
  rw [mem_nonfaceIdeal_iff]
  constructor
  · intro h m hm
    by_contra hc
    have hbad := h m (MvPolynomial.mem_support_iff.mpr hc)
    rcases hm with he | hf
    · exact hbad.1.ne_empty he
    · exact hbad.2 hf
  · intro h m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    constructor
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      exact hc (h m (Or.inl he))
    · intro hf
      exact hc (h m (Or.inr hf))

/-- A nonzero monomial lies in the face ideal exactly when its support is a nonface. -/
theorem monomial_mem_nonfaceIdeal_iff [CommSemiring R]
    (K : PreAbstractSimplicialComplex ι) (m : ι →₀ ℕ) {r : R} (hr : r ≠ 0) :
    MvPolynomial.monomial m r ∈ nonfaceIdeal K ↔
      m.support.Nonempty ∧ m.support ∉ K := by
  classical
  simpa [MvPolynomial.support_monomial, hr] using
    mem_nonfaceIdeal_iff K (MvPolynomial.monomial m r)

/-- The standard face ring, with the empty support retained as the unit monomial. -/
abbrev FaceRing [CommRing R] (K : PreAbstractSimplicialComplex ι) :=
  MvPolynomial ι R ⧸ nonfaceIdeal (R := R) K

/-- Face-supported monomials survive in the face ring, and all other monomials vanish. -/
theorem monomial_image_ne_zero_iff [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (m : ι →₀ ℕ) {r : R} (hr : r ≠ 0) :
    Ideal.Quotient.mk (nonfaceIdeal K) (MvPolynomial.monomial m r) ≠ 0 ↔
      m.support = ∅ ∨ m.support ∈ K := by
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, monomial_mem_nonfaceIdeal_iff K m hr]
  simp only [not_and_or, Finset.not_nonempty_iff_eq_empty, not_not]

/-- Two representatives have equal face-ring classes precisely when their
coefficients agree at every face-supported monomial. -/
theorem quotient_eq_iff_face_coefficients [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (p q : MvPolynomial ι R) :
    Ideal.Quotient.mk (nonfaceIdeal K) p = Ideal.Quotient.mk (nonfaceIdeal K) q ↔
      ∀ m : ι →₀ ℕ, m.support = ∅ ∨ m.support ∈ K → p.coeff m = q.coeff m := by
  rw [Ideal.Quotient.eq, mem_nonfaceIdeal_iff_coeff_zero]
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

/-- Enlarging a complex removes nonface relations. -/
theorem nonfaceIdeal_antitone [CommSemiring R] :
    Antitone (nonfaceIdeal (R := R) : PreAbstractSimplicialComplex ι → Ideal (MvPolynomial ι R)) := by
  intro K L hKL p hp
  rw [mem_nonfaceIdeal_iff] at hp ⊢
  intro m hm
  exact ⟨(hp m hm).1, fun hface => (hp m hm).2 (hKL hface)⟩

/-- The face ideal retains the complete combinatorial complex. -/
theorem nonfaceIdeal_injective [CommRing R] [Nontrivial R] :
    Function.Injective (nonfaceIdeal (R := R) :
      PreAbstractSimplicialComplex ι → Ideal (MvPolynomial ι R)) := by
  intro K L hKL
  apply SetLike.coe_injective
  ext s
  by_cases hs : s.Nonempty
  · have hK := monomial_mem_nonfaceIdeal_iff (R := R) K (squarefreeExponent s) one_ne_zero
    have hL := monomial_mem_nonfaceIdeal_iff (R := R) L (squarefreeExponent s) one_ne_zero
    simp only [squarefreeExponent_support, hs, true_and] at hK hL
    rw [hKL] at hK
    exact not_iff_not.mp (hK.symm.trans hL)
  · constructor
    · intro h
      exact False.elim (hs (K.isRelLowerSet_faces h).1)
    · intro h
      exact False.elim (hs (L.isRelLowerSet_faces h).1)

end Grunbaum2003.GNecessityNext
-- END GNecessityNextFaceRing.lean

-- BEGIN FaceRingShellingStep.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R : Type*}

/-- The monomial of a smaller support divides the monomial of a larger support,
as an explicit membership in the corresponding principal ideal. -/
theorem squarefree_monomial_mem_span_of_subset [CommSemiring R]
    {s t : Finset ι} (hst : s ⊆ t) :
    MvPolynomial.monomial (squarefreeExponent t) (1 : R) ∈
      Ideal.span {MvPolynomial.monomial (squarefreeExponent s) (1 : R)} := by
  have hle : squarefreeExponent s ≤ squarefreeExponent t := by
    rw [squarefreeExponent_le_iff, squarefreeExponent_support]
    exact hst
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨MvPolynomial.monomial (squarefreeExponent t - squarefreeExponent s) (1 : R), ?_⟩
  rw [MvPolynomial.monomial_mul, tsub_add_cancel_of_le hle, one_mul]

/-- Attaching the new-face interval `[r,f]` changes the old nonface ideal by
exactly the principal monomial for its restriction face. This is the literal
ideal step in the shelling proof of the Stanley–Reisner free-basis theorem
(Carl Lee, 2013 notes, Theorem 12.3, pp. 92–93). -/
theorem nonfaceIdeal_eq_sup_of_attach_interval [CommSemiring R]
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f) :
    nonfaceIdeal (R := R) K = nonfaceIdeal L ⊔
      Ideal.span {MvPolynomial.monomial (squarefreeExponent r) (1 : R)} := by
  classical
  have hKL : K ≤ L := fun s hs => (hattach s).mpr (Or.inl hs)
  apply le_antisymm
  · change Ideal.span _ ≤ _
    apply Ideal.span_le.mpr
    rintro p ⟨m, ⟨s, hs, rfl⟩, rfl⟩
    by_cases hsL : s ∈ L
    · have hrs : r ⊆ s := ((hattach s).mp hsL).resolve_left hs.2 |>.1
      exact (show Ideal.span {MvPolynomial.monomial (squarefreeExponent r) (1 : R)} ≤
        nonfaceIdeal L ⊔ Ideal.span {MvPolynomial.monomial (squarefreeExponent r) (1 : R)}
        from le_sup_right) (squarefree_monomial_mem_span_of_subset hrs)
    · apply (show nonfaceIdeal (R := R) L ≤ nonfaceIdeal L ⊔
          Ideal.span {MvPolynomial.monomial (squarefreeExponent r) (1 : R)} from le_sup_left)
      apply Ideal.subset_span
      exact ⟨squarefreeExponent s, ⟨s, ⟨hs.1, hsL⟩, rfl⟩, rfl⟩
  · apply sup_le (nonfaceIdeal_antitone hKL)
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    apply Ideal.subset_span
    exact ⟨squarefreeExponent r, ⟨r, ⟨hr, hrK⟩, rfl⟩, rfl⟩

/-- The same exact ideal identity persists after imposing additional relations,
such as the global linear parameters. -/
theorem nonfaceIdeal_sup_eq_of_attach_interval [CommSemiring R]
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f)
    (T : Ideal (MvPolynomial ι R)) :
    nonfaceIdeal K ⊔ T = (nonfaceIdeal L ⊔ T) ⊔
      Ideal.span {MvPolynomial.monomial (squarefreeExponent r) (1 : R)} := by
  rw [nonfaceIdeal_eq_sup_of_attach_interval K L r f hr hrK hattach]
  ac_rfl

end Grunbaum2003.GNecessityNext
-- END FaceRingShellingStep.lean

-- BEGIN GNecessityNextFaceRestriction.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R : Type*}

/-- A face support, with the empty support restored to Mathlib's nonempty convention. -/
abbrev FaceSupport (K : PreAbstractSimplicialComplex ι) :=
  {s : Finset ι // s = ∅ ∨ s ∈ K}

/-- Restrict a polynomial to the coordinate subspace belonging to a face. -/
noncomputable def faceRestriction [CommSemiring R] (K : PreAbstractSimplicialComplex ι)
    (s : FaceSupport K) : MvPolynomial ι R →ₐ[R] MvPolynomial (↥s.val) R :=
  MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective

/-- Every sub-support of an admissible support is admissible. -/
theorem faceSupport_mono (K : PreAbstractSimplicialComplex ι)
    {s t : Finset ι} (hs : s = ∅ ∨ s ∈ K) (ht : t ⊆ s) :
    t = ∅ ∨ t ∈ K := by
  rcases t.eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · right
    rcases hs with rfl | hs
    · exact False.elim (h.ne_empty (Finset.subset_empty.mp ht))
    · exact (K.isRelLowerSet_faces hs).2 ht h

/-- A polynomial vanishes in the face ring exactly when all coordinate-face restrictions vanish.
This identifies the face ideal with the intersection of the coordinate-face kernels. -/
theorem mem_nonfaceIdeal_iff_restrictions [CommSemiring R]
    (K : PreAbstractSimplicialComplex ι) (p : MvPolynomial ι R) :
    p ∈ nonfaceIdeal K ↔ ∀ s : FaceSupport K, faceRestriction K s p = 0 := by
  classical
  rw [mem_nonfaceIdeal_iff_coeff_zero]
  constructor
  · intro h s
    ext m
    rw [MvPolynomial.coeff_zero]
    change (p.killCompl (f := (Subtype.val : ↥s.val → ι))
      Subtype.val_injective).coeff m = 0
    rw [MvPolynomial.coeff_killCompl]
    apply h
    apply faceSupport_mono K s.property
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hx)
    exact y.property
  · intro h m hm
    let s : FaceSupport K := ⟨m.support, hm⟩
    let e : ↥s.val → ι := Subtype.val
    have he : Function.Injective e := Subtype.val_injective
    have hs : (↑m.support : Set ι) ⊆ Set.range e := by
      intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩
    have hc := congrArg (MvPolynomial.coeff (m.comapDomain e he.injOn)) (h s)
    change (p.killCompl he).coeff (m.comapDomain e he.injOn) = 0 at hc
    rw [MvPolynomial.coeff_killCompl, m.mapDomain_comapDomain e he hs] at hc
    exact hc

end Grunbaum2003.GNecessityNext
-- END GNecessityNextFaceRestriction.lean

-- BEGIN FaceRingShellingKernel.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R : Type*}

/-- Coordinate restriction detects exactly the coefficients supported on the facet. -/
theorem killCompl_eq_zero_iff_coeff_support_subset [CommSemiring R]
    (f : Finset ι) (p : MvPolynomial ι R) :
    p.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective = 0 ↔
      ∀ m : ι →₀ ℕ, m.support ⊆ f → p.coeff m = 0 := by
  classical
  constructor
  · intro h m hm
    let e : ↥f → ι := Subtype.val
    have he : Function.Injective e := Subtype.val_injective
    have hs : (↑m.support : Set ι) ⊆ Set.range e := by
      intro x hx
      exact ⟨⟨x, hm hx⟩, rfl⟩
    have hc := congrArg (MvPolynomial.coeff (m.comapDomain e he.injOn)) h
    change (p.killCompl he).coeff (m.comapDomain e he.injOn) = 0 at hc
    rw [MvPolynomial.coeff_killCompl, m.mapDomain_comapDomain e he hs] at hc
    exact hc
  · intro h
    ext m
    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_killCompl]
    apply h
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hx)
    exact y.property

/-- For a genuine shelling attachment, multiplication by the new restriction
monomial has exactly the facet coordinate kernel. This is the cancellation
step in Lee's free-basis proof, expressed in the literal nonface ideal. -/
theorem restriction_monomial_mul_mem_iff [CommSemiring R]
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K) (hrf : r ⊆ f)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f)
    (p : MvPolynomial ι R) :
    MvPolynomial.monomial (squarefreeExponent r) (1 : R) * p ∈ nonfaceIdeal L ↔
      p.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective = 0 := by
  classical
  rw [mem_nonfaceIdeal_iff_coeff_zero, killCompl_eq_zero_iff_coeff_support_subset]
  constructor
  · intro h m hm
    have hsupport : (squarefreeExponent r + m).support = r ∪ m.support := by
      rw [Finsupp.support_add_eq_union, squarefreeExponent_support]
    have hface : (squarefreeExponent r + m).support ∈ L := by
      rw [hsupport]
      exact (hattach _).mpr (Or.inr ⟨Finset.subset_union_left,
        Finset.union_subset hrf hm⟩)
    simpa only [MvPolynomial.coeff_monomial_mul, one_mul] using h _ (Or.inr hface)
  · intro h m hm
    rw [MvPolynomial.coeff_monomial_mul']
    split_ifs with hle
    · rw [one_mul]
      have hrm : r ⊆ m.support := (squarefreeExponent_le_iff r m).mp hle
      have hmL : m.support ∈ L := by
        rcases hm with hm | hm
        · exact False.elim (hr.ne_empty (Finset.subset_empty.mp (hm ▸ hrm)))
        · exact hm
      have hmK : m.support ∉ K := by
        intro hmK
        exact hrK ((K.isRelLowerSet_faces hmK).2 hrm hr)
      have hmf : m.support ⊆ f := ((hattach _).mp hmL).resolve_left hmK |>.2
      exact h _ (Finsupp.support_tsub.trans hmf)
    · rfl

/-- Equal facet restrictions give equal multiples of the new restriction
monomial in the actual face ring. -/
theorem restriction_monomial_quotient_eq_iff [CommRing R]
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K) (hrf : r ⊆ f)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f)
    (p q : MvPolynomial ι R) :
    Ideal.Quotient.mk (nonfaceIdeal L)
        (MvPolynomial.monomial (squarefreeExponent r) (1 : R) * p) =
      Ideal.Quotient.mk (nonfaceIdeal L)
        (MvPolynomial.monomial (squarefreeExponent r) (1 : R) * q) ↔
      p.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective =
        q.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective := by
  rw [Ideal.Quotient.eq, ← mul_sub,
    restriction_monomial_mul_mem_iff K L r f hr hrK hrf hattach,
    map_sub, sub_eq_zero]

/-- No relation is lost when the new facet polynomial is inserted in the
shelling kernel via its restriction monomial. -/
theorem restriction_monomial_facet_injective [CommRing R]
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K) (hrf : r ⊆ f)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f) :
    Function.Injective (fun p : MvPolynomial (↥f) R =>
      Ideal.Quotient.mk (nonfaceIdeal L)
        (MvPolynomial.monomial (squarefreeExponent r) (1 : R) *
          MvPolynomial.rename Subtype.val p)) := by
  intro p q hpq
  have h := (restriction_monomial_quotient_eq_iff K L r f hr hrK hrf hattach _ _).mp hpq
  simpa only [MvPolynomial.killCompl_rename_app] using h

/-- Every polynomial that disappears in the preceding shelling stage is a
unique facet polynomial times the new restriction monomial in the new face ring. -/
theorem existsUnique_facet_polynomial_of_mem_old_ideal [CommRing R]
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K) (hrf : r ⊆ f)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f)
    (p : MvPolynomial ι R) (hp : p ∈ nonfaceIdeal K) :
    ∃! q : MvPolynomial (↥f) R,
      Ideal.Quotient.mk (nonfaceIdeal L) p =
        Ideal.Quotient.mk (nonfaceIdeal L)
          (MvPolynomial.monomial (squarefreeExponent r) (1 : R) *
            MvPolynomial.rename Subtype.val q) := by
  rw [nonfaceIdeal_eq_sup_of_attach_interval K L r f hr hrK hattach] at hp
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  let q := MvPolynomial.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective t
  have heq : Ideal.Quotient.mk (nonfaceIdeal L)
        (a + t * MvPolynomial.monomial (squarefreeExponent r) (1 : R)) =
      Ideal.Quotient.mk (nonfaceIdeal L)
        (MvPolynomial.monomial (squarefreeExponent r) (1 : R) *
          MvPolynomial.rename Subtype.val q) := by
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, mul_comm t]
    apply (restriction_monomial_quotient_eq_iff K L r f hr hrK hrf hattach _ _).mpr
    exact (MvPolynomial.killCompl_rename_app Subtype.val_injective q).symm
  refine ⟨q, heq, ?_⟩
  intro q' hq'
  exact restriction_monomial_facet_injective K L r f hr hrK hrf hattach
    (hq'.symm.trans heq)

end Grunbaum2003.GNecessityNext
-- END FaceRingShellingKernel.lean

-- BEGIN FaceRingShellingBase.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R A : Type*}

/-- On the first simplex, the face ideal is exactly the facet-coordinate kernel. -/
theorem simplex_mem_nonfaceIdeal_iff [CommSemiring R]
    (K : PreAbstractSimplicialComplex ι) (f : Finset ι)
    (hK : ∀ s : Finset ι, s ∈ K ↔ s.Nonempty ∧ s ⊆ f)
    (p : MvPolynomial ι R) :
    p ∈ nonfaceIdeal K ↔
      p.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective = 0 := by
  rw [mem_nonfaceIdeal_iff_coeff_zero, killCompl_eq_zero_iff_coeff_support_subset]
  have hsupport (m : ι →₀ ℕ) : m.support = ∅ ∨ m.support ∈ K ↔ m.support ⊆ f := by
    rw [hK]
    constructor
    · rintro (he | ⟨_, hf⟩)
      · rw [he]
        exact Finset.empty_subset _
      · exact hf
    · intro hf
      rcases m.support.eq_empty_or_nonempty with he | hn
      · exact Or.inl he
      · exact Or.inr ⟨hn, hf⟩
  simp only [hsupport]

/-- Unique parameter representation on the first facet, where the restriction
face is empty and its monomial is one. This is the base of the shelling induction. -/
theorem unique_parameter_representation_simplex [CommRing R] [CommRing A] [Algebra R A]
    (K : PreAbstractSimplicialComplex ι) (f : Finset ι)
    (hK : ∀ s : Finset ι, s ∈ K ↔ s.Nonempty ∧ s ⊆ f)
    (θ : A →ₐ[R] MvPolynomial ι R)
    (e : A ≃ₐ[R] MvPolynomial (↥f) R)
    (he : ∀ a : A,
      (θ a).killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective = e a)
    (p : MvPolynomial ι R) :
    ∃! a : A, Ideal.Quotient.mk (nonfaceIdeal K) p =
      Ideal.Quotient.mk (nonfaceIdeal K) (θ a) := by
  let q := p.killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective
  refine ⟨e.symm q, ?_, ?_⟩
  · change Ideal.Quotient.mk (nonfaceIdeal K) p =
      Ideal.Quotient.mk (nonfaceIdeal K) (θ (e.symm q))
    rw [Ideal.Quotient.eq, simplex_mem_nonfaceIdeal_iff K f hK,
      map_sub, sub_eq_zero, he]
    exact (e.apply_symm_apply q).symm
  · intro a ha
    rw [Ideal.Quotient.eq, simplex_mem_nonfaceIdeal_iff K f hK,
      map_sub, sub_eq_zero, he] at ha
    apply e.injective
    rw [e.apply_symm_apply]
    exact ha.symm

end Grunbaum2003.GNecessityNext
-- END FaceRingShellingBase.lean

-- BEGIN FaceRingShellingRepresentation.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

variable {ι κ R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype κ]

/-- The induction step in the Stanley–Reisner free-basis proof. The parameter
algebra is mapped by the actual global parameters, and their restriction to the
new facet is explicitly an algebra equivalence. A shelling attachment then adds
exactly one unique coefficient, multiplying its literal restriction monomial.
The first-facet case and existence of a geometric shelling are separate. -/
theorem unique_parameter_representation_attach
    (K L : PreAbstractSimplicialComplex ι) (r f : Finset ι)
    (hr : r.Nonempty) (hrK : r ∉ K) (hrf : r ⊆ f)
    (hattach : ∀ s : Finset ι, s ∈ L ↔ s ∈ K ∨ r ⊆ s ∧ s ⊆ f)
    (θ : A →ₐ[R] MvPolynomial ι R)
    (e : A ≃ₐ[R] MvPolynomial (↥f) R)
    (he : ∀ a : A,
      (θ a).killCompl (f := (Subtype.val : ↥f → ι)) Subtype.val_injective = e a)
    (η : κ → MvPolynomial ι R)
    (hold : ∀ p : MvPolynomial ι R, ∃! c : κ → A,
      Ideal.Quotient.mk (nonfaceIdeal K) p =
        Ideal.Quotient.mk (nonfaceIdeal K) (∑ j, θ (c j) * η j)) :
    ∀ p : MvPolynomial ι R, ∃! c : (κ → A) × A,
      Ideal.Quotient.mk (nonfaceIdeal L) p =
        Ideal.Quotient.mk (nonfaceIdeal L)
          ((∑ j, θ (c.1 j) * η j) +
            MvPolynomial.monomial (squarefreeExponent r) (1 : R) * θ c.2) := by
  classical
  intro p
  let S : (κ → A) → MvPolynomial ι R := fun c => ∑ j, θ (c j) * η j
  let M : MvPolynomial ι R := MvPolynomial.monomial (squarefreeExponent r) (1 : R)
  have hKL : K ≤ L := fun s hs => (hattach s).mpr (Or.inl hs)
  have hrestrict (a b : MvPolynomial ι R)
      (hab : Ideal.Quotient.mk (nonfaceIdeal L) a =
        Ideal.Quotient.mk (nonfaceIdeal L) b) :
      Ideal.Quotient.mk (nonfaceIdeal K) a =
        Ideal.Quotient.mk (nonfaceIdeal K) b :=
    Ideal.Quotient.eq.mpr (nonfaceIdeal_antitone hKL (Ideal.Quotient.eq.mp hab))
  have hM : M ∈ nonfaceIdeal K := by
    apply Ideal.subset_span
    exact ⟨squarefreeExponent r, ⟨r, ⟨hr, hrK⟩, rfl⟩, rfl⟩
  obtain ⟨c, hc, hcuniq⟩ := hold p
  have hp : p - S c ∈ nonfaceIdeal K := Ideal.Quotient.eq.mp hc
  obtain ⟨q, hq, _⟩ := existsUnique_facet_polynomial_of_mem_old_ideal
    K L r f hr hrK hrf hattach (p - S c) hp
  let a : A := e.symm q
  have hqa : Ideal.Quotient.mk (nonfaceIdeal L)
      (M * MvPolynomial.rename Subtype.val q) =
        Ideal.Quotient.mk (nonfaceIdeal L) (M * θ a) := by
    apply (restriction_monomial_quotient_eq_iff K L r f hr hrK hrf hattach _ _).mpr
    rw [MvPolynomial.killCompl_rename_app, he]
    exact (e.apply_symm_apply q).symm
  have hnew : Ideal.Quotient.mk (nonfaceIdeal L) p =
      Ideal.Quotient.mk (nonfaceIdeal L) (S c + M * θ a) := by
    have hdiff := hq.trans hqa
    rw [map_sub] at hdiff
    rw [map_add, add_comm]
    exact sub_eq_iff_eq_add.mp hdiff
  refine ⟨(c, a), hnew, ?_⟩
  intro c' hc'
  have hc'old := hrestrict _ _ hc'
  change Ideal.Quotient.mk (nonfaceIdeal K) p =
    Ideal.Quotient.mk (nonfaceIdeal K) (S c'.1 + M * θ c'.2) at hc'old
  rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hM,
    zero_mul, add_zero] at hc'old
  have hfirst : c'.1 = c := hcuniq c'.1 hc'old
  have hsecond : c'.2 = a := by
    have hsum := hc'.symm.trans hnew
    change Ideal.Quotient.mk (nonfaceIdeal L) (S c'.1 + M * θ c'.2) =
      Ideal.Quotient.mk (nonfaceIdeal L) (S c + M * θ a) at hsum
    rw [hfirst, map_add, map_add] at hsum
    have hmul := add_left_cancel hsum
    have heq := (restriction_monomial_quotient_eq_iff K L r f hr hrK hrf hattach _ _).mp hmul
    rw [he, he] at heq
    exact e.injective heq
  exact Prod.ext hfirst hsecond

end Grunbaum2003.GNecessityNext
-- END FaceRingShellingRepresentation.lean

-- BEGIN FaceRingShellingInduction.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Ungraded free parameter representation for a finite shelling, assembled from
its simplex base and actual interval attachments. Every coefficient is unique.
The geometric existence of these shelling data and grading compatibility are
not assumed conclusions of this algebraic induction. -/
theorem unique_parameter_representation_shelling (N : ℕ) :
    ∀ (C : Fin (N + 1) → PreAbstractSimplicialComplex ι)
      (r f : Fin (N + 1) → Finset ι)
      (θ : A →ₐ[R] MvPolynomial ι R)
      (e : ∀ j, A ≃ₐ[R] MvPolynomial (↥(f j)) R),
    r 0 = ∅ →
    (∀ s : Finset ι, s ∈ C 0 ↔ s.Nonempty ∧ s ⊆ f 0) →
    (∀ j : Fin N, (r j.succ).Nonempty) →
    (∀ j : Fin N, r j.succ ∉ C j.castSucc) →
    (∀ j : Fin N, r j.succ ⊆ f j.succ) →
    (∀ (j : Fin N) (s : Finset ι),
      s ∈ C j.succ ↔ s ∈ C j.castSucc ∨ r j.succ ⊆ s ∧ s ⊆ f j.succ) →
    (∀ (j : Fin (N + 1)) (a : A),
      (θ a).killCompl (f := (Subtype.val : ↥(f j) → ι)) Subtype.val_injective = e j a) →
    ∀ p : MvPolynomial ι R, ∃! c : Fin (N + 1) → A,
      Ideal.Quotient.mk (nonfaceIdeal (C (Fin.last N))) p =
        Ideal.Quotient.mk (nonfaceIdeal (C (Fin.last N)))
          (∑ j, θ (c j) * MvPolynomial.monomial (squarefreeExponent (r j)) (1 : R)) := by
  classical
  induction N with
  | zero =>
      intro C r f θ e hr0 hfirst _ _ _ _ he p
      have hmono : MvPolynomial.monomial (squarefreeExponent (r 0)) (1 : R) = 1 := by
        rw [hr0]
        have hz : squarefreeExponent (∅ : Finset ι) = 0 := by
          ext i
          simp [squarefreeExponent]
        simp [hz]
      obtain ⟨a, ha, huniq⟩ := unique_parameter_representation_simplex
        (C 0) (f 0) hfirst θ (e 0) (he 0) p
      refine ⟨fun _ => a, ?_, ?_⟩
      · change Ideal.Quotient.mk (nonfaceIdeal (C 0)) p =
          Ideal.Quotient.mk (nonfaceIdeal (C 0))
            (∑ j : Fin 1, θ a * MvPolynomial.monomial (squarefreeExponent (r j)) (1 : R))
        simpa only [Fin.sum_univ_one, hmono, mul_one] using ha
      · intro c hc
        change Ideal.Quotient.mk (nonfaceIdeal (C 0)) p =
          Ideal.Quotient.mk (nonfaceIdeal (C 0))
            (∑ j : Fin 1, θ (c j) * MvPolynomial.monomial (squarefreeExponent (r j)) (1 : R)) at hc
        have hc' : Ideal.Quotient.mk (nonfaceIdeal (C 0)) p =
            Ideal.Quotient.mk (nonfaceIdeal (C 0)) (θ (c 0)) := by
          simpa only [Fin.sum_univ_one, hmono, mul_one] using hc
        funext j
        have hj : j = 0 := Fin.ext (by omega)
        rw [hj]
        exact huniq (c 0) hc'
  | succ N ih =>
      intro C r f θ e hr0 hfirst hr hrK hrf hattach he p
      have hold := ih (fun j => C j.castSucc) (fun j => r j.castSucc)
        (fun j => f j.castSucc) θ (fun j => e j.castSucc) hr0 hfirst
        (fun j => hr j.castSucc) (fun j => hrK j.castSucc)
        (fun j => hrf j.castSucc) (fun j => hattach j.castSucc)
        (fun j => he j.castSucc)
      let t : Fin (N + 1) := Fin.last N
      let z : Fin (N + 2) := Fin.last (N + 1)
      let M : MvPolynomial ι R := MvPolynomial.monomial (squarefreeExponent (r z)) (1 : R)
      let η : Fin (N + 1) → MvPolynomial ι R :=
        fun j => MvPolynomial.monomial (squarefreeExponent (r j.castSucc)) (1 : R)
      obtain ⟨a, ha, huniq⟩ := unique_parameter_representation_attach
        (C t.castSucc) (C t.succ) (r t.succ) (f t.succ)
        (hr t) (hrK t) (hrf t) (hattach t) θ (e t.succ) (he t.succ) η hold p
      let c : Fin (N + 2) → A := Fin.lastCases a.2 a.1
      have hsum (b : Fin (N + 2) → A) :
          (∑ j, θ (b j) * MvPolynomial.monomial (squarefreeExponent (r j)) (1 : R)) =
            (∑ j : Fin (N + 1), θ (b j.castSucc) * η j) + M * θ (b z) := by
        rw [Fin.sum_univ_castSucc]
        change (∑ j : Fin (N + 1), θ (b j.castSucc) * η j) + θ (b z) * M = _
        rw [mul_comm (θ (b z))]
      have hc : Ideal.Quotient.mk (nonfaceIdeal (C z)) p =
          Ideal.Quotient.mk (nonfaceIdeal (C z))
            (∑ j, θ (c j) * MvPolynomial.monomial (squarefreeExponent (r j)) (1 : R)) := by
        rw [hsum]
        simpa only [c, z, M, t, Fin.succ_last, Fin.lastCases_castSucc,
          Fin.lastCases_last] using ha
      refine ⟨c, hc, ?_⟩
      intro b hb
      rw [hsum] at hb
      have hpair : ((fun j : Fin (N + 1) => b j.castSucc), b z) = a :=
        huniq _ hb
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [c, z, Fin.lastCases_last] using congrArg Prod.snd hpair
      · simpa only [c, Fin.lastCases_castSucc] using congrFun (congrArg Prod.fst hpair) k

end Grunbaum2003.GNecessityNext
-- END FaceRingShellingInduction.lean

-- BEGIN GNecessityNextArtinianParameters.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open MvPolynomial

variable {ι κ τ R : Type*} [CommRing R]

/-- The actual polynomial ideal obtained by adjoining all parameter polynomials. -/
noncomputable def parameterQuotientIdeal (I : Ideal (MvPolynomial ι R))
    (θ : MvPolynomial κ R →ₐ[R] MvPolynomial ι R) : Ideal (MvPolynomial ι R) :=
  I ⊔ Ideal.span (Set.range (fun i : κ => θ (MvPolynomial.X i)))

/-- In the actual parameter quotient, a parameter polynomial evaluates to its constant term. -/
theorem parameterQuotient_parameter_eq_constant (I : Ideal (MvPolynomial ι R))
    (θ : MvPolynomial κ R →ₐ[R] MvPolynomial ι R) (p : MvPolynomial κ R) :
    Ideal.Quotient.mk (parameterQuotientIdeal I θ) (θ p) =
      Ideal.Quotient.mk (parameterQuotientIdeal I θ) (C (constantCoeff p)) := by
  let J := parameterQuotientIdeal I θ
  have heq : (Ideal.Quotient.mkₐ R J).comp θ =
      MvPolynomial.aeval (fun _ : κ => (0 : MvPolynomial ι R ⧸ J)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change Ideal.Quotient.mk J (θ (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span (Set.range (fun i : κ => θ (MvPolynomial.X i))) ≤ J from
      le_sup_right) (Ideal.mem_span_range_self (x := i))
  have h := DFunLike.congr_fun heq p
  change Ideal.Quotient.mk J (θ p) = algebraMap R (MvPolynomial ι R ⧸ J) (constantCoeff p)
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.aeval_zero'] using h

/-- A free polynomial-parameter representation forces scalar independence after quotienting
by those same parameters. Ideal multipliers are expanded in the proved free representation. -/
theorem scalar_coefficients_zero_of_mem_parameterQuotient [Fintype κ] [Fintype τ]
    (I : Ideal (MvPolynomial ι R))
    (θ : MvPolynomial κ R →ₐ[R] MvPolynomial ι R) (η : τ → MvPolynomial ι R)
    (hfree : ∀ p : MvPolynomial ι R, ∃! c : τ → MvPolynomial κ R,
      Ideal.Quotient.mk I p = Ideal.Quotient.mk I (∑ j, θ (c j) * η j))
    (a : τ → R)
    (ha : (∑ j, C (a j) * η j) ∈ parameterQuotientIdeal I θ) : ∀ j, a j = 0 := by
  classical
  obtain ⟨p, hp, q, hq, heq⟩ := Submodule.mem_sup.mp ha
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq
  have hrep (i : κ) : ∃ c : τ → MvPolynomial κ R,
      Ideal.Quotient.mk I (u i) = Ideal.Quotient.mk I (∑ j, θ (c j) * η j) :=
    (hfree (u i)).exists
  choose d hd using hrep
  let b : τ → MvPolynomial κ R := fun j => ∑ i, d i j * MvPolynomial.X i
  have hb : Ideal.Quotient.mk I (∑ j, C (a j) * η j) =
      Ideal.Quotient.mk I (∑ j, θ (b j) * η j) := by
    calc
      Ideal.Quotient.mk I (∑ j, C (a j) * η j) =
          ∑ i, Ideal.Quotient.mk I (u i) * Ideal.Quotient.mk I (θ (MvPolynomial.X i)) := by
        rw [← heq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hp, zero_add, ← hu]
        simp only [map_sum, map_mul]
      _ = ∑ i, Ideal.Quotient.mk I (∑ j, θ (d i j) * η j) *
          Ideal.Quotient.mk I (θ (MvPolynomial.X i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hd i]
      _ = Ideal.Quotient.mk I (∑ j, θ (b j) * η j) := by
        simp only [b, map_sum, map_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have haRep : Ideal.Quotient.mk I (∑ j, C (a j) * η j) =
      Ideal.Quotient.mk I (∑ j, θ (C (a j)) * η j) := by
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [show θ (C (a j)) = C (a j) from θ.commutes (a j)]
  obtain ⟨c, hc, huniq⟩ := hfree (∑ j, C (a j) * η j)
  have hcoeff : (fun j => C (a j)) = b := (huniq _ haRep).trans (huniq _ hb).symm
  intro j
  have h := congrArg MvPolynomial.constantCoeff (congrFun hcoeff j)
  simpa only [b, map_sum, map_mul, constantCoeff_C, constantCoeff_X,
    mul_zero, Finset.sum_const_zero] using h

/-- The actual quotient by all parameters has unique scalar coefficients in the original
free generators. For finitely many generators over a field this gives the finite quotient basis. -/
theorem unique_scalar_representation_parameter_quotient [Fintype κ] [Fintype τ]
    (I : Ideal (MvPolynomial ι R))
    (θ : MvPolynomial κ R →ₐ[R] MvPolynomial ι R) (η : τ → MvPolynomial ι R)
    (hfree : ∀ p : MvPolynomial ι R, ∃! c : τ → MvPolynomial κ R,
      Ideal.Quotient.mk I p = Ideal.Quotient.mk I (∑ j, θ (c j) * η j)) :
    ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk (parameterQuotientIdeal I θ) p =
        Ideal.Quotient.mk (parameterQuotientIdeal I θ) (∑ j, C (a j) * η j) := by
  classical
  intro p
  let J := parameterQuotientIdeal I θ
  obtain ⟨c, hc, _⟩ := hfree p
  let a : τ → R := fun j => constantCoeff (c j)
  have ha : Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j) := by
    calc
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, θ (c j) * η j) :=
        Ideal.Quotient.eq.mpr ((show I ≤ J from le_sup_left) (Ideal.Quotient.eq.mp hc))
      _ = Ideal.Quotient.mk J (∑ j, C (a j) * η j) := by
        simp only [map_sum, map_mul, a]
        apply Finset.sum_congr rfl
        intro j hj
        rw [parameterQuotient_parameter_eq_constant I θ (c j)]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  have hdiff : (∑ j, C (a' j - a j) * η j) ∈ J := by
    have h := Ideal.Quotient.eq.mp (ha'.symm.trans ha)
    simpa only [map_sub, sub_mul, Finset.sum_sub_distrib] using h
  have hz := scalar_coefficients_zero_of_mem_parameterQuotient I θ η hfree
    (fun j => a' j - a j) hdiff
  funext j
  exact sub_eq_zero.mp (hz j)

end Grunbaum2003.GNecessityNext
-- END GNecessityNextArtinianParameters.lean

-- BEGIN GNecessityNextFaceBasis.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R : Type*}

/-- The exponent vectors whose monomials are permitted by the complex. -/
abbrev FaceExponent (K : PreAbstractSimplicialComplex ι) :=
  {m : ι →₀ ℕ // m.support = ∅ ∨ m.support ∈ K}

/-- Restrict a polynomial's coefficient vector to the face-supported exponents. -/
noncomputable def faceCoefficients [CommRing R] (K : PreAbstractSimplicialComplex ι) :
    MvPolynomial ι R →ₗ[R] FaceExponent K →₀ R :=
  (Finsupp.lsubtypeDomain {m : ι →₀ ℕ | m.support = ∅ ∨ m.support ∈ K}).comp
    (MvPolynomial.basisMonomials ι R).repr.toLinearMap

@[simp] theorem faceCoefficients_apply [CommRing R] (K : PreAbstractSimplicialComplex ι)
    (p : MvPolynomial ι R) (m : FaceExponent K) :
    faceCoefficients K p m = p.coeff m.val := rfl

/-- Every finite face-supported coefficient vector has a polynomial representative. -/
theorem faceCoefficients_surjective [CommRing R] (K : PreAbstractSimplicialComplex ι) :
    Function.Surjective (faceCoefficients (R := R) K) := by
  classical
  intro f
  let e : FaceExponent K ↪ (ι →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨(MvPolynomial.basisMonomials ι R).repr.symm (f.embDomain e), ?_⟩
  ext m
  change ((MvPolynomial.basisMonomials ι R).repr
    ((MvPolynomial.basisMonomials ι R).repr.symm (f.embDomain e))) m.val = f m
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.embDomain_apply_self e f m

/-- The nonface ideal is exactly the kernel of retaining the face coefficients. -/
theorem faceCoefficients_ker [CommRing R] (K : PreAbstractSimplicialComplex ι) :
    LinearMap.ker (faceCoefficients (R := R) K) = (nonfaceIdeal K).restrictScalars R := by
  ext p
  change faceCoefficients K p = 0 ↔ p ∈ nonfaceIdeal K
  rw [mem_nonfaceIdeal_iff_coeff_zero]
  constructor
  · intro h m hm
    exact DFunLike.congr_fun h ⟨m, hm⟩
  · intro h
    ext m
    exact h m.val m.property

/-- The face ring has precisely the finite coefficient vectors on face monomials. -/
noncomputable def faceMonomialEquiv [CommRing R] (K : PreAbstractSimplicialComplex ι) :
    FaceRing (R := R) K ≃ₗ[R] FaceExponent K →₀ R :=
  (Submodule.quotEquivOfEq ((nonfaceIdeal (R := R) K).restrictScalars R)
    (LinearMap.ker (faceCoefficients (R := R) K)) (faceCoefficients_ker K).symm).trans
    ((faceCoefficients (R := R) K).quotKerEquivOfSurjective
      (faceCoefficients_surjective K))

@[simp] theorem faceMonomialEquiv_apply_mk [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (p : MvPolynomial ι R) :
    faceMonomialEquiv (R := R) K (Ideal.Quotient.mk (nonfaceIdeal (R := R) K) p) =
      faceCoefficients K p := by
  change (faceCoefficients (R := R) K).quotKerEquivOfSurjective (faceCoefficients_surjective K)
    (Submodule.Quotient.mk p) = faceCoefficients K p
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ p

/-- Face-supported monomials form a basis of the Stanley–Reisner ring. -/
noncomputable def faceMonomialBasis [CommRing R] (K : PreAbstractSimplicialComplex ι) :
    Module.Basis (FaceExponent K) R (FaceRing (R := R) K) :=
  Module.Basis.ofRepr (faceMonomialEquiv K)

@[simp] theorem faceMonomialBasis_apply [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (m : FaceExponent K) :
    faceMonomialBasis (R := R) K m =
      Ideal.Quotient.mk (nonfaceIdeal (R := R) K) (MvPolynomial.monomial m.val (1 : R)) := by
  classical
  apply (faceMonomialEquiv (R := R) K).injective
  change (faceMonomialBasis (R := R) K).repr (faceMonomialBasis K m) = _
  rw [Module.Basis.repr_self, faceMonomialEquiv_apply_mk]
  ext n
  simp only [Finsupp.single_apply, faceCoefficients_apply, MvPolynomial.coeff_monomial]
  congr 1
  exact propext Subtype.ext_iff

end Grunbaum2003.GNecessityNext
-- END GNecessityNextFaceBasis.lean

-- BEGIN GNecessityNextFaceGrading.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.GNecessityNext

variable {ι R : Type*}

/-- Taking a homogeneous component preserves the literal squarefree nonface ideal. -/
theorem homogeneousComponent_mem_nonfaceIdeal [CommSemiring R]
    (K : PreAbstractSimplicialComplex ι) {p : MvPolynomial ι R}
    (hp : p ∈ nonfaceIdeal K) (n : ℕ) :
    MvPolynomial.homogeneousComponent n p ∈ nonfaceIdeal K := by
  classical
  rw [mem_nonfaceIdeal_iff] at hp ⊢
  intro m hm
  rw [MvPolynomial.support_homogeneousComponent] at hm
  exact hp m (Finset.mem_filter.mp hm).1

/-- Face-supported exponent vectors of one fixed total degree. -/
abbrev DegreeFaceExponent (K : PreAbstractSimplicialComplex ι) (n : ℕ) :=
  {m : ι →₀ ℕ // (m.support = ∅ ∨ m.support ∈ K) ∧ m.degree = n}

/-- The degree-n face-ring piece, expressed directly as a quotient of homogeneous polynomials.
For Fin (v+1) vertices this is definitionally the platform HilbertFunctor.piece. -/
abbrev FacePiece [CommRing R] (K : PreAbstractSimplicialComplex ι) (n : ℕ) :=
  ↥(MvPolynomial.homogeneousSubmodule ι R n) ⧸
    Submodule.comap (MvPolynomial.homogeneousSubmodule ι R n).subtype
      ((nonfaceIdeal (R := R) K).restrictScalars R)

/-- The coefficient vector on degree-n face monomials. -/
noncomputable def degreeFaceCoefficients [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule ι R n) →ₗ[R] DegreeFaceExponent K n →₀ R :=
  (Finsupp.lsubtypeDomain
    {m : ι →₀ ℕ | (m.support = ∅ ∨ m.support ∈ K) ∧ m.degree = n}).comp
    ((MvPolynomial.basisMonomials ι R).repr.toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule ι R n).subtype)

@[simp] theorem degreeFaceCoefficients_apply [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι R n) (m : DegreeFaceExponent K n) :
    degreeFaceCoefficients K n p m = p.val.coeff m.val := rfl

/-- Every finitely supported vector in a fixed degree has a homogeneous representative. -/
theorem degreeFaceCoefficients_surjective [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    Function.Surjective (degreeFaceCoefficients (R := R) K n) := by
  classical
  intro f
  let e : DegreeFaceExponent K n ↪ (ι →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
  let p := (MvPolynomial.basisMonomials ι R).repr.symm (f.embDomain e)
  refine ⟨⟨MvPolynomial.homogeneousComponent n p,
    MvPolynomial.homogeneousComponent_mem n p⟩, ?_⟩
  ext m
  rw [degreeFaceCoefficients_apply, MvPolynomial.coeff_homogeneousComponent, if_pos m.property.2]
  change ((MvPolynomial.basisMonomials ι R).repr
    ((MvPolynomial.basisMonomials ι R).repr.symm (f.embDomain e))) m.val = f m
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.embDomain_apply_self e f m

/-- The kernel consists precisely of homogeneous representatives belonging to the face ideal. -/
theorem degreeFaceCoefficients_ker [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    LinearMap.ker (degreeFaceCoefficients (R := R) K n) =
      Submodule.comap (MvPolynomial.homogeneousSubmodule ι R n).subtype
        ((nonfaceIdeal K).restrictScalars R) := by
  ext p
  change degreeFaceCoefficients K n p = 0 ↔ p.val ∈ nonfaceIdeal K
  rw [mem_nonfaceIdeal_iff_coeff_zero]
  constructor
  · intro h m hm
    by_cases hmn : m.degree = n
    · exact DFunLike.congr_fun h ⟨m, hm, hmn⟩
    · exact p.property.coeff_eq_zero hmn
  · intro h
    ext m
    exact h m.val m.property.1

/-- The homogeneous quotient has an explicit coordinate space indexed by its face monomials. -/
noncomputable def degreeFaceMonomialEquiv [CommRing R]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    FacePiece (R := R) K n ≃ₗ[R] DegreeFaceExponent K n →₀ R :=
  (Submodule.quotEquivOfEq
    (Submodule.comap (MvPolynomial.homogeneousSubmodule ι R n).subtype
      ((nonfaceIdeal (R := R) K).restrictScalars R))
    (LinearMap.ker (degreeFaceCoefficients (R := R) K n))
      (degreeFaceCoefficients_ker K n).symm).trans
    ((degreeFaceCoefficients (R := R) K n).quotKerEquivOfSurjective
      (degreeFaceCoefficients_surjective K n))

/-- Every fixed-degree face-monomial index set is finite for a finite vertex type. -/
theorem finite_degreeFaceExponent [Finite ι]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    Finite (DegreeFaceExponent K n) :=
  ((Finsupp.finite_of_degree_eq n).subset (fun _ h => h.2)).to_subtype

/-- The exact Hilbert function counts degree-n monomials with face support. -/
theorem finrank_facePiece [Field R] [Finite ι]
    (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    Module.finrank R (FacePiece (R := R) K n) = Nat.card (DegreeFaceExponent K n) := by
  let : Finite (DegreeFaceExponent K n) := finite_degreeFaceExponent K n
  let : Fintype (DegreeFaceExponent K n) := Fintype.ofFinite _
  rw [(degreeFaceMonomialEquiv (R := R) K n).finrank_eq]
  simpa only [Nat.card_eq_fintype_card] using
    (Module.finrank_finsupp_self (R := R) (ι := DegreeFaceExponent K n))

end Grunbaum2003.GNecessityNext
-- END GNecessityNextFaceGrading.lean

-- BEGIN GNecessityNextGradedParameters.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open MvPolynomial

variable {ι κ τ R : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

@[simp] theorem squarefreeExponent_degree (s : Finset ι) :
    (squarefreeExponent s).degree = s.card := by
  classical
  rw [Finsupp.degree_apply, squarefreeExponent_support]
  calc
    ∑ i ∈ s, squarefreeExponent s i = ∑ _i ∈ s, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finsupp.indicator_of_mem hi _
    _ = s.card := by simp

theorem restrictionMonomial_homogeneous (s : Finset ι) :
    (MvPolynomial.monomial (squarefreeExponent s) (1 : R)).IsHomogeneous s.card :=
  isHomogeneous_monomial 1 (squarefreeExponent_degree s)

theorem parameterLinearForm_homogeneous [Fintype ι] (a : ι → R) :
    (parameterLinearForm a).IsHomogeneous 1 := by
  apply (homogeneousSubmodule ι R 1).sum_mem
  intro i hi
  exact (homogeneousSubmodule ι R 1).smul_mem (a i) (isHomogeneous_X R i)

theorem coordinateParameterMap_homogeneous [Fintype ι] (v : ι → κ → R)
    {p : MvPolynomial κ R} {k : ℕ} (hp : p.IsHomogeneous k) :
    (coordinateParameterMap v p).IsHomogeneous k := by
  simpa only [coordinateParameterMap, one_mul] using
    hp.aeval (fun i => parameterLinearForm (fun j => v j i))
      (fun i => parameterLinearForm_homogeneous (fun j => v j i))

/-- The actual coordinate parameter map preserves every homogeneous component. -/
theorem coordinateParameterMap_homogeneousComponent [Fintype ι]
    (v : ι → κ → R) (p : MvPolynomial κ R) (k : ℕ) :
    coordinateParameterMap v (homogeneousComponent k p) =
      homogeneousComponent k (coordinateParameterMap v p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
      have hm : (MvPolynomial.monomial m a).IsHomogeneous m.degree :=
        isHomogeneous_monomial a rfl
      rw [homogeneousComponent_of_mem hm,
        homogeneousComponent_of_mem (coordinateParameterMap_homogeneous v hm)]
      split_ifs <;> simp only [map_zero]
  | add p q hp hq =>
      simp only [map_add, hp, hq]

/-- Multiplying by a homogeneous polynomial shifts the component projection by its degree. -/
theorem homogeneousComponent_mul_homogeneous (p η : MvPolynomial ι R)
    {r : ℕ} (hη : η.IsHomogeneous r) (k : ℕ) :
    homogeneousComponent k (p * η) =
      if r ≤ k then homogeneousComponent (k - r) p * η else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (homogeneousSubmodule ι R) k (a := p) hη
  have hdec (q : MvPolynomial ι R) (n : ℕ) :
      (DirectSum.decompose (homogeneousSubmodule ι R) q n : MvPolynomial ι R) =
        homogeneousComponent n q := MvPolynomial.decomposition.decompose'_apply q n
  simpa only [hdec] using h

/-- Unique polynomial coefficients in a homogeneous face-ring representation automatically
have the required shifted degrees. This derives grading from the actual parameter map and
literal nonface ideal, rather than assuming that the ungraded free representation is graded. -/
theorem unique_parameter_coefficients_component [Fintype ι] [Fintype τ]
    (K : PreAbstractSimplicialComplex ι) (v : ι → κ → R)
    (η : τ → MvPolynomial ι R) (r : τ → ℕ)
    (hη : ∀ j, (η j).IsHomogeneous (r j))
    (p : MvPolynomial ι R) (k : ℕ) (hp : p.IsHomogeneous k)
    (c : τ → MvPolynomial κ R)
    (hc : Ideal.Quotient.mk (nonfaceIdeal K) p =
      Ideal.Quotient.mk (nonfaceIdeal K) (∑ j, coordinateParameterMap v (c j) * η j))
    (huniq : ∀ c' : τ → MvPolynomial κ R,
      Ideal.Quotient.mk (nonfaceIdeal K) p =
        Ideal.Quotient.mk (nonfaceIdeal K) (∑ j, coordinateParameterMap v (c' j) * η j) →
          c' = c) :
    ∀ j, c j = if r j ≤ k then homogeneousComponent (k - r j) (c j) else 0 := by
  classical
  let c' : τ → MvPolynomial κ R := fun j =>
    if r j ≤ k then homogeneousComponent (k - r j) (c j) else 0
  have hterm (j : τ) :
      homogeneousComponent k (coordinateParameterMap v (c j) * η j) =
        coordinateParameterMap v (c' j) * η j := by
    rw [homogeneousComponent_mul_homogeneous _ _ (hη j)]
    dsimp only [c']
    split_ifs
    · rw [coordinateParameterMap_homogeneousComponent]
    · rw [map_zero, zero_mul]
  have hmem := homogeneousComponent_mem_nonfaceIdeal K (Ideal.Quotient.eq.mp hc) k
  rw [map_sub, map_sum, homogeneousComponent_eq_self hp] at hmem
  simp only [hterm] at hmem
  have hrep : Ideal.Quotient.mk (nonfaceIdeal K) p =
      Ideal.Quotient.mk (nonfaceIdeal K) (∑ j, coordinateParameterMap v (c' j) * η j) :=
    Ideal.Quotient.eq.mpr hmem
  intro j
  exact (congrFun (huniq c' hrep) j).symm

end Grunbaum2003.GNecessityNext
-- END GNecessityNextGradedParameters.lean

-- BEGIN GNecessityNextArtinianGrading.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open MvPolynomial

variable {ι κ τ R : Type*} [CommRing R] [Fintype τ]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal homogeneous ideal quotient used by the Hilbert-piece API. -/
abbrev HomogeneousIdealPiece (J : Ideal (MvPolynomial ι R)) (k : ℕ) :=
  ↥(homogeneousSubmodule ι R k) ⧸
    Submodule.comap (homogeneousSubmodule ι R k).subtype (J.restrictScalars R)

noncomputable def scalarRepresentationMap (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R) : (τ → R) →ₗ[R] MvPolynomial ι R ⧸ J where
  toFun a := ∑ j, a j • Ideal.Quotient.mk J (η j)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]

theorem scalarRepresentationMap_apply (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R) (a : τ → R) :
    scalarRepresentationMap J η a = Ideal.Quotient.mk J (∑ j, C (a j) * η j) := by
  change ∑ j, Ideal.Quotient.mk J (a j • η j) = Ideal.Quotient.mk J (∑ j, C (a j) * η j)
  simp only [MvPolynomial.smul_eq_C_mul, map_sum]

theorem scalarRepresentationMap_bijective (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R)
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) :
    Function.Bijective (scalarRepresentationMap J η) := by
  constructor
  · intro a b hab
    obtain ⟨c, hc, huniq⟩ := hscalar (∑ j, C (a j) * η j)
    rw [scalarRepresentationMap_apply, scalarRepresentationMap_apply] at hab
    exact (huniq a rfl).trans (huniq b hab).symm
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha, _⟩ := hscalar p
    exact ⟨a, (scalarRepresentationMap_apply J η a).trans ha.symm⟩

/-- The scalar coordinates of the actual quotient, obtained from proved unique representations. -/
noncomputable def scalarCoefficientEquiv (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R)
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) :
    (MvPolynomial ι R ⧸ J) ≃ₗ[R] (τ → R) :=
  (LinearEquiv.ofBijective (scalarRepresentationMap J η)
    (scalarRepresentationMap_bijective J η hscalar)).symm

theorem scalarCoefficientEquiv_representation (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R)
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j))
    (p : MvPolynomial ι R) :
    Ideal.Quotient.mk J p = Ideal.Quotient.mk J
      (∑ j, C (scalarCoefficientEquiv J η hscalar (Ideal.Quotient.mk J p) j) * η j) := by
  rw [← scalarRepresentationMap_apply]
  exact ((LinearEquiv.ofBijective (scalarRepresentationMap J η)
    (scalarRepresentationMap_bijective J η hscalar)).apply_symm_apply _).symm

theorem scalarCoefficientEquiv_sum (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R)
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) (a : τ → R) :
    scalarCoefficientEquiv J η hscalar (Ideal.Quotient.mk J (∑ j, C (a j) * η j)) = a := by
  rw [← scalarRepresentationMap_apply]
  exact (LinearEquiv.ofBijective (scalarRepresentationMap J η)
    (scalarRepresentationMap_bijective J η hscalar)).symm_apply_apply a

/-- Homogeneous representatives have no scalar coefficients in generators of other degrees. -/
theorem scalar_coefficients_zero_off_degree (J : Ideal (MvPolynomial ι R))
    (hJ : ∀ p ∈ J, ∀ k : ℕ, homogeneousComponent k p ∈ J)
    (η : τ → MvPolynomial ι R) (r : τ → ℕ)
    (hη : ∀ j, (η j).IsHomogeneous (r j))
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j))
    (p : MvPolynomial ι R) (k : ℕ) (hp : p.IsHomogeneous k)
    (a : τ → R) (ha : Ideal.Quotient.mk J p =
      Ideal.Quotient.mk J (∑ j, C (a j) * η j)) :
    ∀ j, r j ≠ k → a j = 0 := by
  classical
  let b : τ → R := fun j => if r j = k then a j else 0
  have hterm (j : τ) : homogeneousComponent k (C (a j) * η j) = C (b j) * η j := by
    rw [homogeneousComponent_C_mul, homogeneousComponent_of_mem (hη j)]
    by_cases hj : r j = k
    · simp only [b, hj, if_pos]
    · have hkj : k ≠ r j := Ne.symm hj
      simp only [b, hj, hkj, if_false, mul_zero, map_zero, zero_mul]
  have hmem := hJ _ (Ideal.Quotient.eq.mp ha) k
  rw [map_sub, map_sum, homogeneousComponent_eq_self hp] at hmem
  simp only [hterm] at hmem
  have hb := Ideal.Quotient.eq.mpr hmem
  obtain ⟨c, hc, huniq⟩ := hscalar p
  have hab : a = b := (huniq a ha).trans (huniq b hb).symm
  intro j hj
  simpa only [b, if_neg hj] using congrFun hab j

noncomputable def degreeScalarCoefficients (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R)
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j))
    (r : τ → ℕ) (k : ℕ) :
    ↥(homogeneousSubmodule ι R k) →ₗ[R] ({j : τ // r j = k} → R) where
  toFun p j := scalarCoefficientEquiv J η hscalar (Ideal.Quotient.mk J p.val) j.val
  map_add' p q := by ext j; simp
  map_smul' a p := by
    ext j
    change scalarCoefficientEquiv J η hscalar (a • Ideal.Quotient.mk J p.val) j.val = _
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem degreeScalarCoefficients_surjective (J : Ideal (MvPolynomial ι R))
    (η : τ → MvPolynomial ι R) (r : τ → ℕ)
    (hη : ∀ j, (η j).IsHomogeneous (r j))
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) (k : ℕ) :
    Function.Surjective (degreeScalarCoefficients J η hscalar r k) := by
  classical
  intro a
  let b : τ → R := fun j => if hj : r j = k then a ⟨j, hj⟩ else 0
  let p : MvPolynomial ι R := ∑ j, C (b j) * η j
  have hp : p.IsHomogeneous k := by
    apply IsHomogeneous.sum
    intro j hj
    by_cases hr : r j = k
    · simpa only [zero_add, hr] using (isHomogeneous_C ι (b j)).mul (hη j)
    · simp only [b, dif_neg hr, map_zero, zero_mul]
      exact isHomogeneous_zero ι R k
  refine ⟨⟨p, hp⟩, ?_⟩
  ext j
  change scalarCoefficientEquiv J η hscalar (Ideal.Quotient.mk J p) j.val = a j
  rw [scalarCoefficientEquiv_sum J η hscalar b]
  exact dif_pos j.property

theorem degreeScalarCoefficients_ker (J : Ideal (MvPolynomial ι R))
    (hJ : ∀ p ∈ J, ∀ k : ℕ, homogeneousComponent k p ∈ J)
    (η : τ → MvPolynomial ι R) (r : τ → ℕ)
    (hη : ∀ j, (η j).IsHomogeneous (r j))
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) (k : ℕ) :
    LinearMap.ker (degreeScalarCoefficients J η hscalar r k) =
      Submodule.comap (homogeneousSubmodule ι R k).subtype (J.restrictScalars R) := by
  classical
  ext p
  change degreeScalarCoefficients J η hscalar r k p = 0 ↔ p.val ∈ J
  constructor
  · intro hzero
    have hcoeff : scalarCoefficientEquiv J η hscalar (Ideal.Quotient.mk J p.val) = 0 := by
      ext j
      by_cases hj : r j = k
      · exact congrFun hzero ⟨j, hj⟩
      · exact scalar_coefficients_zero_off_degree J hJ η r hη hscalar p.val k p.property _
          (scalarCoefficientEquiv_representation J η hscalar p.val) j hj
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (scalarCoefficientEquiv J η hscalar).injective (hcoeff.trans (map_zero _).symm)
  · intro hp
    ext j
    change scalarCoefficientEquiv J η hscalar (Ideal.Quotient.mk J p.val) j.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, Pi.zero_apply]

/-- Each actual homogeneous quotient piece has precisely the scalar coordinates of generators
of that degree. This identifies the Hilbert pieces, not just the total quotient dimension. -/
noncomputable def homogeneousPieceScalarEquiv (J : Ideal (MvPolynomial ι R))
    (hJ : ∀ p ∈ J, ∀ k : ℕ, homogeneousComponent k p ∈ J)
    (η : τ → MvPolynomial ι R) (r : τ → ℕ)
    (hη : ∀ j, (η j).IsHomogeneous (r j))
    (hscalar : ∀ p : MvPolynomial ι R, ∃! a : τ → R,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) (k : ℕ) :
    HomogeneousIdealPiece J k ≃ₗ[R] ({j : τ // r j = k} → R) :=
  (Submodule.quotEquivOfEq
    (Submodule.comap (homogeneousSubmodule ι R k).subtype (J.restrictScalars R))
    (LinearMap.ker (degreeScalarCoefficients J η hscalar r k))
      (degreeScalarCoefficients_ker J hJ η r hη hscalar k).symm).trans
    ((degreeScalarCoefficients J η hscalar r k).quotKerEquivOfSurjective
      (degreeScalarCoefficients_surjective J η r hη hscalar k))

theorem finrank_homogeneousPiece_eq_card_generators {F : Type*} [Field F]
    (J : Ideal (MvPolynomial ι F))
    (hJ : ∀ p ∈ J, ∀ k : ℕ, homogeneousComponent k p ∈ J)
    (η : τ → MvPolynomial ι F) (r : τ → ℕ)
    (hη : ∀ j, (η j).IsHomogeneous (r j))
    (hscalar : ∀ p : MvPolynomial ι F, ∃! a : τ → F,
      Ideal.Quotient.mk J p = Ideal.Quotient.mk J (∑ j, C (a j) * η j)) (k : ℕ) :
    Module.finrank F (HomogeneousIdealPiece J k) = Nat.card {j : τ // r j = k} := by
  classical
  rw [(homogeneousPieceScalarEquiv J hJ η r hη hscalar k).finrank_eq]
  simpa only [Nat.card_eq_fintype_card] using
    (Module.finrank_fintype_fun_eq_card (R := F) (η := {j : τ // r j = k}))

/-- The actual face ideal together with the actual coordinate parameters is homogeneous. -/
theorem homogeneous_coordinateParameter_quotient [Fintype ι]
    (K : PreAbstractSimplicialComplex ι) (v : ι → κ → R) :
    ∀ p ∈ parameterQuotientIdeal (nonfaceIdeal K) (coordinateParameterMap v), ∀ k : ℕ,
      homogeneousComponent k p ∈
        parameterQuotientIdeal (nonfaceIdeal K) (coordinateParameterMap v) := by
  have hI : (nonfaceIdeal (R := R) K).IsHomogeneous (homogeneousSubmodule ι R) := by
    apply Ideal.homogeneous_span
    rintro p ⟨m, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s.card, restrictionMonomial_homogeneous s⟩
  have hparams : (Ideal.span (Set.range (fun i : κ =>
      coordinateParameterMap v (MvPolynomial.X i)))).IsHomogeneous
        (homogeneousSubmodule ι R) := by
    apply Ideal.homogeneous_span
    rintro p ⟨i, rfl⟩
    exact ⟨1, coordinateParameterMap_homogeneous v (isHomogeneous_X R i)⟩
  intro p hp k
  exact homogeneousComponent_mem_of_mem (hI.sup hparams) hp k

/-- The Hilbert function of the actual parameter quotient counts shelling restriction faces
by their cardinality, once their proved unique free representation is supplied. -/
theorem finrank_coordinateParameter_quotient {F : Type*} [Field F] [Fintype ι] [Fintype κ]
    (K : PreAbstractSimplicialComplex ι) (v : ι → κ → F) (r : τ → Finset ι)
    (hfree : ∀ p : MvPolynomial ι F, ∃! c : τ → MvPolynomial κ F,
      Ideal.Quotient.mk (nonfaceIdeal K) p = Ideal.Quotient.mk (nonfaceIdeal K)
        (∑ j, coordinateParameterMap v (c j) *
          MvPolynomial.monomial (squarefreeExponent (r j)) (1 : F))) (k : ℕ) :
    Module.finrank F (HomogeneousIdealPiece
      (parameterQuotientIdeal (nonfaceIdeal K) (coordinateParameterMap v)) k) =
        Nat.card {j : τ // (r j).card = k} := by
  exact finrank_homogeneousPiece_eq_card_generators _
    (homogeneous_coordinateParameter_quotient K v)
    (fun j => MvPolynomial.monomial (squarefreeExponent (r j)) (1 : F))
    (fun j => (r j).card) (fun j => restrictionMonomial_homogeneous (r j))
    (unique_scalar_representation_parameter_quotient (nonfaceIdeal K)
      (coordinateParameterMap v) _ hfree) k

end Grunbaum2003.GNecessityNext
-- END GNecessityNextArtinianGrading.lean

-- BEGIN GNecessityNextBoundaryShelling.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open MvPolynomial

/-- A nonempty subset of a boundary facet is a boundary face. -/
theorem mem_polytopeBoundary_iff_exists_boundaryFacet {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (S : Finset (PolytopeVertex P)) :
    S ∈ polytopeBoundary P ↔ S.Nonempty ∧ ∃ F : BoundaryFacet P, S ⊆ F.val := by
  constructor
  · intro hS
    exact ⟨((polytopeBoundary P).isRelLowerSet_faces hS).1,
      boundary_face_subset_facet hd hP S hS⟩
  · rintro ⟨hSne, F, hSF⟩
    exact ((polytopeBoundary P).isRelLowerSet_faces F.property.1).2 hSF hSne

/-- Every simplicial polytope of dimension at least two admits a finite facet shelling
whose final prefix is the literal boundary complex, together with unique polynomial
parameter representations and exact Artinian quotient piece dimensions. -/
theorem exists_boundary_shelling_and_parameter_quotient {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (c : Fin d → ℝ) (hc : c ∈ interior P) :
    let _ : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
    let _ : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
    ∃ (N : ℕ) (e : Fin (N + 1) ≃ BoundaryFacet P)
      (r : BoundaryFacet P → Finset (PolytopeVertex P))
      (C : Fin (N + 1) → PreAbstractSimplicialComplex (PolytopeVertex P)),
      r (e 0) = ∅ ∧
      (∀ S : Finset (PolytopeVertex P), S ∈ C 0 ↔ S.Nonempty ∧ S ⊆ (e 0).val) ∧
      (∀ j : Fin N, (r (e j.succ)).Nonempty) ∧
      (∀ j : Fin N, r (e j.succ) ∉ C j.castSucc) ∧
      (∀ j : Fin N, r (e j.succ) ⊆ (e j.succ).val) ∧
      (∀ (j : Fin N) (S : Finset (PolytopeVertex P)),
        S ∈ C j.succ ↔ S ∈ C j.castSucc ∨
          r (e j.succ) ⊆ S ∧ S ⊆ (e j.succ).val) ∧
      C (Fin.last N) = polytopeBoundary P ∧
      (∀ p : MvPolynomial (PolytopeVertex P) ℝ,
        ∃! coeff : Fin (N + 1) → MvPolynomial (Fin d) ℝ,
          Ideal.Quotient.mk (nonfaceIdeal (polytopeBoundary P)) p =
            Ideal.Quotient.mk (nonfaceIdeal (polytopeBoundary P))
              (∑ j, coordinateParameterMap (fun v : PolytopeVertex P => v.val - c) (coeff j) *
                MvPolynomial.monomial (squarefreeExponent (r (e j))) (1 : ℝ))) ∧
      ∀ k : ℕ,
        Module.finrank ℝ (HomogeneousIdealPiece
          (parameterQuotientIdeal (nonfaceIdeal (polytopeBoundary P))
            (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c))) k) =
          Nat.card {j : Fin (N + 1) // (r (e j)).card = k} := by
  classical
  let : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
  let : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
  let : Finite (BoundaryFacet P) := finite_boundaryFacet hP.1
  let : Nonempty (BoundaryFacet P) := nonempty_boundaryFacet (by omega) hP
  obtain ⟨score, hscoreInj, r, hrF, hcriterion⟩ := boundary_line_shelling_criterion hd hP
  obtain ⟨N, e, hscore⟩ := exists_finite_descending_score_enumeration score hscoreInj
  obtain ⟨C, hr0, hfirst, hrne, hrOld, hrSub, hattach, hfinal⟩ :=
    exists_prefixes_of_descending_facet_criterion N (fun F : BoundaryFacet P => F.val)
      r score e hscore hrF hcriterion
  have hlast : C (Fin.last N) = polytopeBoundary P := by
    ext S
    exact (hfinal S).trans (mem_polytopeBoundary_iff_exists_boundaryFacet (by omega) hP S).symm
  have hparamExist (j : Fin (N + 1)) :
      ∃ eParam : MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (↥(e j).val) ℝ,
        (MvPolynomial.killCompl (R := ℝ)
          (f := (Subtype.val : ↥(e j).val → PolytopeVertex P)) Subtype.val_injective).comp
            (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c)) = eParam.toAlgHom :=
    boundary_coordinateParameter_equiv hP (e j).val (e j).property.1 (e j).property.2 c hc
  choose eParam heParam using hparamExist
  have hkill (j : Fin (N + 1)) (a : MvPolynomial (Fin d) ℝ) :
      (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c) a).killCompl
        (f := (Subtype.val : ↥(e j).val → PolytopeVertex P)) Subtype.val_injective =
          eParam j a :=
    DFunLike.congr_fun (heParam j) a
  have hfree : ∀ p : MvPolynomial (PolytopeVertex P) ℝ,
      ∃! coeff : Fin (N + 1) → MvPolynomial (Fin d) ℝ,
        Ideal.Quotient.mk (nonfaceIdeal (polytopeBoundary P)) p =
          Ideal.Quotient.mk (nonfaceIdeal (polytopeBoundary P))
            (∑ j, coordinateParameterMap (fun v : PolytopeVertex P => v.val - c) (coeff j) *
              MvPolynomial.monomial (squarefreeExponent (r (e j))) (1 : ℝ)) := by
    rw [← hlast]
    exact unique_parameter_representation_shelling N C (fun j => r (e j))
      (fun j => (e j).val) (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c))
      eParam hr0 hfirst hrne hrOld hrSub hattach hkill
  refine ⟨N, e, r, C, hr0, hfirst, hrne, hrOld, hrSub, hattach, hlast, hfree, ?_⟩
  intro k
  exact finrank_coordinateParameter_quotient (polytopeBoundary P)
    (fun v : PolytopeVertex P => v.val - c) (fun j => r (e j)) hfree k

end Grunbaum2003.GNecessityNext
-- END GNecessityNextBoundaryShelling.lean

-- BEGIN GNecessityNextShellingCounts.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open MvPolynomial

/-- Faces of a fixed cardinality in a finite simplicial complex. -/
noncomputable def complexFacesOfCard {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun S => S ∈ K ∧ S.card = n)

theorem mem_complexFacesOfCard {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) (S : Finset V) :
    S ∈ complexFacesOfCard K n ↔ S ∈ K ∧ S.card = n := by
  simp only [complexFacesOfCard, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_complexFacesOfCard_eq_ncard {V : Type*} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    (complexFacesOfCard K n).card = {S : Finset V | S ∈ K ∧ S.card = n}.ncard := by
  have hcoe : (↑(complexFacesOfCard K n) : Set (Finset V)) =
      {S : Finset V | S ∈ K ∧ S.card = n} := by
    ext S
    simp only [Finset.mem_coe, mem_complexFacesOfCard]
    rfl
  rw [← hcoe, Set.ncard_coe_finset]

theorem card_filter_powersetCard_subset_ite {V : Type*}
    (R F : Finset V) (d n : ℕ) (hRF : R ⊆ F) (hF : F.card = d) :
    ((F.powersetCard n).filter (R ⊆ ·)).card =
      if R.card ≤ n then Nat.choose (d - R.card) (n - R.card) else 0 := by
  classical
  by_cases hle : R.card ≤ n
  · rw [if_pos hle, Finset.card_filter_powersetCard_subset _ _ _ hRF hle, hF]
  · rw [if_neg hle]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro S hS hRS
    have hcard := Finset.card_le_card hRS
    have hScard := (Finset.mem_powersetCard.mp hS).2
    omega

/-- In a finite shelling of `d`-element facets, the number of faces of cardinality `m + 1`
in the final complex is the sum of the interval binomial counts over all facets. -/
theorem card_complexFacesOfCard_shelling {V : Type*} [Fintype V] (d m N : ℕ) :
    ∀ (C : Fin (N + 1) → PreAbstractSimplicialComplex V)
      (r f : Fin (N + 1) → Finset V),
      (∀ j, (f j).card = d) →
      r 0 = ∅ →
      (∀ S : Finset V, S ∈ C 0 ↔ S.Nonempty ∧ S ⊆ f 0) →
      (∀ j : Fin N, (r j.succ).Nonempty) →
      (∀ j : Fin N, r j.succ ∉ C j.castSucc) →
      (∀ j : Fin N, r j.succ ⊆ f j.succ) →
      (∀ (j : Fin N) (S : Finset V),
        S ∈ C j.succ ↔ S ∈ C j.castSucc ∨ r j.succ ⊆ S ∧ S ⊆ f j.succ) →
      (complexFacesOfCard (C (Fin.last N)) (m + 1)).card =
        ∑ j : Fin (N + 1),
          if (r j).card ≤ m + 1 then
            Nat.choose (d - (r j).card) (m + 1 - (r j).card)
          else 0 := by
  classical
  induction N with
  | zero =>
      intro C r f hf hr0 hfirst _ _ _ _
      have heq : complexFacesOfCard (C (Fin.last 0)) (m + 1) =
          ((f 0).powersetCard (m + 1)).filter (r 0 ⊆ ·) := by
        ext S
        rw [Fin.last_zero, mem_complexFacesOfCard, hfirst, Finset.mem_filter,
          Finset.mem_powersetCard, hr0]
        constructor
        · rintro ⟨⟨_, hSf⟩, hScard⟩
          exact ⟨⟨hSf, hScard⟩, Finset.empty_subset S⟩
        · rintro ⟨⟨hSf, hScard⟩, _⟩
          have hne : S.Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨⟨hne, hSf⟩, hScard⟩
      rw [heq, Fin.sum_univ_one,
        card_filter_powersetCard_subset_ite (r 0) (f 0) d (m + 1)
          (by rw [hr0]; exact Finset.empty_subset _) (hf 0)]
  | succ N ih =>
      intro C r f hf hr0 hfirst hrne hrOld hrSub hattach
      have hold := ih (fun j => C j.castSucc) (fun j => r j.castSucc)
        (fun j => f j.castSucc) (fun j => hf j.castSucc) hr0 hfirst
        (fun j => hrne j.castSucc) (fun j => hrOld j.castSucc)
        (fun j => hrSub j.castSucc) (fun j => hattach j.castSucc)
      let t : Fin (N + 1) := Fin.last N
      let z : Fin (N + 2) := Fin.last (N + 1)
      have hunion : complexFacesOfCard (C z) (m + 1) =
          complexFacesOfCard (C t.castSucc) (m + 1) ∪
            ((f z).powersetCard (m + 1)).filter (r z ⊆ ·) := by
        ext S
        rw [Finset.mem_union, mem_complexFacesOfCard, mem_complexFacesOfCard,
          Finset.mem_filter, Finset.mem_powersetCard]
        change (S ∈ C t.succ ∧ S.card = m + 1) ↔
          (S ∈ C t.castSucc ∧ S.card = m + 1) ∨
            (S ⊆ f t.succ ∧ S.card = m + 1) ∧ r t.succ ⊆ S
        rw [hattach t S]
        tauto
      have hdisj : Disjoint (complexFacesOfCard (C t.castSucc) (m + 1))
          (((f z).powersetCard (m + 1)).filter (r z ⊆ ·)) := by
        rw [Finset.disjoint_left]
        intro S hSold hSnew
        rw [mem_complexFacesOfCard] at hSold
        rw [Finset.mem_filter] at hSnew
        exact hrOld t (((C t.castSucc).isRelLowerSet_faces hSold.1).2 hSnew.2 (hrne t))
      rw [hunion, Finset.card_union_of_disjoint hdisj, Fin.sum_univ_castSucc,
        hold, card_filter_powersetCard_subset_ite (r z) (f z) d (m + 1) (hrSub t) (hf z)]

theorem sum_shelling_binomial_eq_fiber_sum {α V : Type*} [Fintype α]
    (d m : ℕ) (r : α → Finset V) :
    (∑ j : α,
      if (r j).card ≤ m + 1 then
        Nat.choose (d - (r j).card) (m + 1 - (r j).card)
      else 0) =
      ∑ k ∈ Finset.range (m + 2),
        Nat.card {j : α // (r j).card = k} * Nat.choose (d - k) (m + 1 - k) := by
  classical
  have hpoint (j : α) :
      (if (r j).card ≤ m + 1 then
        Nat.choose (d - (r j).card) (m + 1 - (r j).card)
      else 0) =
        ∑ k ∈ Finset.range (m + 2),
          if (r j).card = k then Nat.choose (d - k) (m + 1 - k) else 0 := by
    by_cases hle : (r j).card ≤ m + 1
    · rw [if_pos hle, Finset.sum_eq_single (r j).card]
      · simp only [if_true]
      · intro k _ hk
        exact if_neg hk.symm
      · intro hmem
        exact (hmem (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg hle]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      exact if_neg (by omega)
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hcard : (Finset.univ.filter (fun j : α => (r j).card = k)).card =
      Nat.card {j : α // (r j).card = k} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]

/-- The canonical geometric face counts of a simplicial `d`-polytope are given by the
McMullen binomial transform of the Hilbert function of the Artinian coordinate-parameter
quotient of its boundary face ring. -/
theorem boundary_faceCount_eq_sum_parameterQuotient_finrank {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (c : Fin d → ℝ) (hc : c ∈ interior P) (m : ℕ) (hm : m < d) :
    let _ : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
    let _ : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
    faceCount P m =
      ∑ k ∈ Finset.range (m + 2),
        Module.finrank ℝ (HomogeneousIdealPiece
          (parameterQuotientIdeal (nonfaceIdeal (polytopeBoundary P))
            (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c))) k) *
          Nat.choose (d - k) (m + 1 - k) := by
  classical
  intro _ _
  let : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
  let : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
  obtain ⟨N, e, r, C, hr0, hfirst, hrne, hrOld, hrSub, hattach, hlast, _, hfinrank⟩ :=
    exists_boundary_shelling_and_parameter_quotient hd hP c hc
  have hcount : faceCount P m = (complexFacesOfCard (C (Fin.last N)) (m + 1)).card := by
    rw [hlast, card_complexFacesOfCard_eq_ncard, boundary_faceCount (by omega) hP m hm]
  rw [hcount,
    card_complexFacesOfCard_shelling d m N C (fun j => r (e j)) (fun j => (e j).val)
      (fun j => (e j).property.2) hr0 hfirst hrne hrOld hrSub hattach,
    sum_shelling_binomial_eq_fiber_sum d m (fun j => r (e j))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hfinrank k]

end Grunbaum2003.GNecessityNext
-- END GNecessityNextShellingCounts.lean

-- BEGIN GNecessityNextDehnSommerville.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open MvPolynomial

/-- Given normalized facet supports at an interior point `c` and a direction `w`
whose facet scores are injective, the negative-coordinate subsets in the shifted
facet bases satisfy the line-shelling criterion. -/
theorem line_shelling_criterion_of_vector {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (c : Fin d → ℝ) (hc : c ∈ interior P)
    (l : BoundaryFacet P → StrongDual ℝ (Fin d → ℝ))
    (hbound : ∀ F, ∀ x ∈ P, l F (x - c) ≤ 1)
    (hcontact : ∀ F, ∀ v : PolytopeVertex P, l F (v.val - c) = 1 ↔ v ∈ F.val)
    (w : Fin d → ℝ) (hw : Function.Injective (fun F : BoundaryFacet P => l F w)) :
    let b := fun F : BoundaryFacet P =>
      boundaryFacetBasis hP F.val F.property.1 F.property.2 c hc
    let α := fun (F : BoundaryFacet P) (v : PolytopeVertex P) =>
      if hv : v ∈ F.val then (b F).repr w ⟨v, hv⟩ else 0
    let r := fun F : BoundaryFacet P => F.val.filter (fun v => α F v < 0)
    (∀ F, r F ⊆ F.val) ∧
    (∀ (F : BoundaryFacet P) (S : Finset (PolytopeVertex P)) (_hSF : S ⊆ F.val),
      (¬ ∃ G : BoundaryFacet P, l F w < l G w ∧ S ⊆ G.val) ↔ r F ⊆ S) ∧
    ∀ (F : BoundaryFacet P), ∀ v ∈ F.val, α F v ≠ 0 := by
  classical
  intro b α r
  have hα (F : BoundaryFacet P) (v : ↥F.val) :
      α F v.val = (b F).repr w v := by
    simp only [α, dif_pos v.property]
  have hrepr (F : BoundaryFacet P) :
      ∑ v ∈ F.val, α F v • (v.val - c) = w := by
    calc
      ∑ v ∈ F.val, α F v • (v.val - c) =
          ∑ v : ↥F.val, α F v.val • (v.val.val - c) :=
        (Finset.sum_coe_sort F.val _).symm
      _ = ∑ v : ↥F.val, (b F).repr w v • b F v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hα]
        simp only [b, boundaryFacetBasis_apply]
      _ = w := (b F).sum_repr w
  have hdiff (F G : BoundaryFacet P) :
      l G w - l F w = ∑ v ∈ F.val, α F v * (l G (v.val - c) - 1) := by
    rw [← hrepr F, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(hcontact F v).mpr hv]
    ring
  refine ⟨fun F => Finset.filter_subset _ _, ?_, ?_⟩
  · intro F S hSF
    apply new_face_iff_negative_coordinate_subset F.val S hSF
      (fun G : BoundaryFacet P => G.val) (α F)
      (fun G v => l G (v.val - c)) (fun G => l G w) (l F w)
    · intro G v _
      exact hbound G v.val (v.property.subset (Set.mem_singleton _))
    · intro G v _
      exact hcontact G v
    · intro G
      exact hdiff F G
    · intro v hv
      obtain ⟨t, ht, htc, hsub, hnot⟩ :=
        boundary_facet_neighbour hd hP F.val F.property.1 F.property.2 v hv
      refine ⟨⟨t, ht, htc⟩, ?_, hnot⟩
      intro x hx
      exact hsub (by simpa only [Finset.mem_erase] using hx)
  · intro F v hv
    obtain ⟨t, ht, htc, hsub, hnot⟩ :=
      boundary_facet_neighbour hd hP F.val F.property.1 F.property.2 v hv
    let G : BoundaryFacet P := ⟨t, ht, htc⟩
    have hGF : G ≠ F := by
      intro hEq
      have hvG : v ∈ G.val := hEq ▸ hv
      exact hnot hvG
    have hneScore : l G w - l F w ≠ 0 :=
      sub_ne_zero.mpr (fun h => hGF (hw h))
    rw [hdiff F G, Finset.sum_eq_single v] at hneScore
    · exact left_ne_zero_of_mul hneScore
    · intro u hu huv
      have huG : u ∈ G.val := hsub (Finset.mem_erase.mpr ⟨huv, hu⟩)
      rw [(hcontact G u).mpr huG, sub_self, mul_zero]
    · intro habs
      exact (habs hv).elim

/-- Any restriction family satisfying the descending facet criterion computes the
Hilbert function of the Artinian coordinate-parameter quotient, and satisfies
`h 0 = 1` and `h k = 0` for `k > d`. -/
theorem finrank_parameterQuotient_of_descending_criterion {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (c : Fin d → ℝ) (hc : c ∈ interior P)
    (score : BoundaryFacet P → ℝ) (hscoreInj : Function.Injective score)
    (r : BoundaryFacet P → Finset (PolytopeVertex P))
    (hrF : ∀ F, r F ⊆ F.val)
    (hcriterion : ∀ (F : BoundaryFacet P) (S : Finset (PolytopeVertex P)) (_hSF : S ⊆ F.val),
      (¬ ∃ G : BoundaryFacet P, score F < score G ∧ S ⊆ G.val) ↔ r F ⊆ S) :
    let _ : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
    let _ : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
    let h := fun k : ℕ =>
      Module.finrank ℝ (HomogeneousIdealPiece
        (parameterQuotientIdeal (nonfaceIdeal (polytopeBoundary P))
          (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c))) k)
    (∀ k : ℕ, h k = Nat.card {F : BoundaryFacet P // (r F).card = k}) ∧
    h 0 = 1 ∧
    (∀ k : ℕ, d < k → h k = 0) ∧
    ∀ m < d, faceCount P m =
      ∑ k ∈ Finset.range (d + 1), h k * Nat.choose (d - k) (d - 1 - m) := by
  classical
  intro _ _ h
  let : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
  let : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
  let : Finite (BoundaryFacet P) := finite_boundaryFacet hP.1
  let : Nonempty (BoundaryFacet P) := nonempty_boundaryFacet (by omega) hP
  obtain ⟨N, e, hscore⟩ := exists_finite_descending_score_enumeration score hscoreInj
  obtain ⟨C, hr0, hfirst, hrne, hrOld, hrSub, hattach, hfinal⟩ :=
    exists_prefixes_of_descending_facet_criterion N (fun F : BoundaryFacet P => F.val)
      r score e hscore hrF hcriterion
  have hlast : C (Fin.last N) = polytopeBoundary P := by
    ext S
    exact (hfinal S).trans (mem_polytopeBoundary_iff_exists_boundaryFacet (by omega) hP S).symm
  have hparamExist (j : Fin (N + 1)) :
      ∃ eParam : MvPolynomial (Fin d) ℝ ≃ₐ[ℝ] MvPolynomial (↥(e j).val) ℝ,
        (MvPolynomial.killCompl (R := ℝ)
          (f := (Subtype.val : ↥(e j).val → PolytopeVertex P)) Subtype.val_injective).comp
            (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c)) = eParam.toAlgHom :=
    boundary_coordinateParameter_equiv hP (e j).val (e j).property.1 (e j).property.2 c hc
  choose eParam heParam using hparamExist
  have hkill (j : Fin (N + 1)) (a : MvPolynomial (Fin d) ℝ) :
      (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c) a).killCompl
        (f := (Subtype.val : ↥(e j).val → PolytopeVertex P)) Subtype.val_injective =
          eParam j a :=
    DFunLike.congr_fun (heParam j) a
  have hfree : ∀ p : MvPolynomial (PolytopeVertex P) ℝ,
      ∃! coeff : Fin (N + 1) → MvPolynomial (Fin d) ℝ,
        Ideal.Quotient.mk (nonfaceIdeal (polytopeBoundary P)) p =
          Ideal.Quotient.mk (nonfaceIdeal (polytopeBoundary P))
            (∑ j, coordinateParameterMap (fun v : PolytopeVertex P => v.val - c) (coeff j) *
              MvPolynomial.monomial (squarefreeExponent (r (e j))) (1 : ℝ)) := by
    rw [← hlast]
    exact unique_parameter_representation_shelling N C (fun j => r (e j))
      (fun j => (e j).val) (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c))
      eParam hr0 hfirst hrne hrOld hrSub hattach hkill
  have hfin (k : ℕ) : h k = Nat.card {j : Fin (N + 1) // (r (e j)).card = k} :=
    finrank_coordinateParameter_quotient (polytopeBoundary P)
      (fun v : PolytopeVertex P => v.val - c) (fun j => r (e j)) hfree k
  have hcard (k : ℕ) : h k = Nat.card {F : BoundaryFacet P // (r F).card = k} := by
    rw [hfin k]
    exact Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
  have hh0 : h 0 = 1 := by
    rw [hfin 0]
    have huniq : Unique {j : Fin (N + 1) // (r (e j)).card = 0} :=
      { default := ⟨0, by simp [hr0]⟩
        uniq := by
          rintro ⟨j, hj⟩
          apply Subtype.ext
          revert hj
          refine Fin.cases (fun _ => rfl) (fun i hi => ?_) j
          have hpos : 0 < (r (e i.succ)).card := Finset.card_pos.mpr (hrne i)
          omega }
    exact Nat.card_unique
  have hgt (k : ℕ) (hk : d < k) : h k = 0 := by
    rw [hcard k, Nat.card_eq_fintype_card]
    have hempty : IsEmpty {F : BoundaryFacet P // (r F).card = k} :=
      ⟨fun ⟨F, hF⟩ => by
        have hle : (r F).card ≤ d :=
          (Finset.card_le_card (hrF F)).trans (le_of_eq F.property.2)
        omega⟩
    exact Fintype.card_eq_zero
  refine ⟨hcard, hh0, hgt, ?_⟩
  intro m hm
  rw [boundary_faceCount_eq_sum_parameterQuotient_finrank hd hP c hc m hm]
  change ∑ k ∈ Finset.range (m + 2), h k * Nat.choose (d - k) (m + 1 - k) =
    ∑ k ∈ Finset.range (d + 1), h k * Nat.choose (d - k) (d - 1 - m)
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 2 ≤ d + 1)]
  have htail : ∑ k ∈ Finset.Ico (m + 2) (d + 1), h k * Nat.choose (d - k) (d - 1 - m) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hsub : d - k - (m + 1 - k) = d - 1 - m := by omega
  rw [← Nat.choose_symm (by omega : m + 1 - k ≤ d - k), hsub]

/-- Reversing the generic line-shelling direction complements every facet restriction set
and proves the Dehn–Sommerville symmetry `h (d - k) = h k` for the Artinian coordinate-parameter
quotient of the boundary face ring, together with `h 0 = 1`, `h k = 0` for `k > d`, and the
McMullen face-count formula. -/
theorem exists_dehn_sommerville_parameterQuotient {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P) :
    let _ : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
    let _ : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
    ∃ c ∈ interior P,
      let h := fun k : ℕ =>
        Module.finrank ℝ (HomogeneousIdealPiece
          (parameterQuotientIdeal (nonfaceIdeal (polytopeBoundary P))
            (coordinateParameterMap (fun v : PolytopeVertex P => v.val - c))) k)
      h 0 = 1 ∧
      (∀ k : ℕ, d < k → h k = 0) ∧
      (∀ k ≤ d, h (d - k) = h k) ∧
      ∀ m < d, faceCount P m =
        ∑ k ∈ Finset.range (d + 1), h k * Nat.choose (d - k) (d - 1 - m) := by
  classical
  intro _ _
  let : Finite (PolytopeVertex P) := finite_polytopeVertex hP.1
  let : Fintype (PolytopeVertex P) := Fintype.ofFinite (PolytopeVertex P)
  let : Finite (BoundaryFacet P) := finite_boundaryFacet hP.1
  obtain ⟨c, hc, l, hbound, hcontact, hne, hinj⟩ :=
    exists_boundary_facet_supports (by omega) hP
  let L : BoundaryFacet P → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun F => (l F).toLinearMap
  have hLi : Function.Injective L := by
    intro F G hFG
    apply hinj
    ext x
    exact congrArg (fun f : (Fin d → ℝ) →ₗ[ℝ] ℝ => f x) hFG
  have hLn (F : BoundaryFacet P) : L F ≠ 0 := by
    intro hzero
    apply hne F
    ext x
    exact congrArg (fun f : (Fin d → ℝ) →ₗ[ℝ] ℝ => f x) hzero
  obtain ⟨w, _, hw⟩ := exists_vector_distinguishing_linear_forms L hLi hLn
  have hwNeg : Function.Injective (fun F : BoundaryFacet P => l F (-w)) := by
    intro F G hFG
    simp only [map_neg, neg_inj] at hFG
    exact hw hFG
  let b (F : BoundaryFacet P) : Module.Basis (↥F.val) ℝ (Fin d → ℝ) :=
    boundaryFacetBasis hP F.val F.property.1 F.property.2 c hc
  let αPos (F : BoundaryFacet P) (v : PolytopeVertex P) : ℝ :=
    if hv : v ∈ F.val then (b F).repr w ⟨v, hv⟩ else 0
  let αNeg (F : BoundaryFacet P) (v : PolytopeVertex P) : ℝ :=
    if hv : v ∈ F.val then (b F).repr (-w) ⟨v, hv⟩ else 0
  let rPos (F : BoundaryFacet P) : Finset (PolytopeVertex P) :=
    F.val.filter (fun v => αPos F v < 0)
  let rNeg (F : BoundaryFacet P) : Finset (PolytopeVertex P) :=
    F.val.filter (fun v => αNeg F v < 0)
  obtain ⟨hrPosSub, hcritPos, hαPosNe⟩ :=
    line_shelling_criterion_of_vector hd hP c hc l hbound hcontact w hw
  obtain ⟨hrNegSub, hcritNeg, _⟩ :=
    line_shelling_criterion_of_vector hd hP c hc l hbound hcontact (-w) hwNeg
  obtain ⟨hcardPos, hh0, hgt, hface⟩ :=
    finrank_parameterQuotient_of_descending_criterion hd hP c hc
      (fun F => l F w) hw rPos hrPosSub hcritPos
  obtain ⟨hcardNeg, _, _, _⟩ :=
    finrank_parameterQuotient_of_descending_criterion hd hP c hc
      (fun F => l F (-w)) hwNeg rNeg hrNegSub hcritNeg
  have hcardSum (F : BoundaryFacet P) : (rPos F).card + (rNeg F).card = d := by
    have hfilter : rNeg F = F.val.filter (fun v => ¬ αPos F v < 0) := by
      apply Finset.filter_congr
      intro v hv
      have hneg : αNeg F v = - αPos F v := by
        simp only [αNeg, αPos, dif_pos hv, map_neg, Finsupp.coe_neg, Pi.neg_apply]
      have hne0 : αPos F v ≠ 0 := hαPosNe F v hv
      rw [hneg]
      constructor
      · intro h1 h2
        linarith
      · intro h1
        rcases lt_trichotomy (αPos F v) 0 with hlt | heq | hgt'
        · exact (h1 hlt).elim
        · exact (hne0 heq).elim
        · linarith
    rw [hfilter]
    exact (Finset.card_filter_add_card_filter_not (fun v => αPos F v < 0)).trans F.property.2
  refine ⟨c, hc, hh0, hgt, ?_, hface⟩
  intro k hk
  rw [hcardNeg (d - k), hcardPos k]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl (BoundaryFacet P)) ?_
  intro F
  dsimp only [Equiv.refl_apply]
  have hsum := hcardSum F
  omega

end Grunbaum2003.GNecessityNext
-- END GNecessityNextDehnSommerville.lean

-- BEGIN GNecessityNextMatrixRepresentation.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.GNecessityNext

open Grunbaum2003

theorem sum_range_choose_eq (N r : ℕ) :
    ∑ n ∈ Finset.range N, Nat.choose n r = Nat.choose N (r + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, add_comm]

theorem sum_symm_interval_choose_eq_gTheoremMatrix (d i m : ℕ)
    (hi : i ≤ d / 2) (hm : m < d) :
    (∑ k ∈ Finset.range (d + 1),
      if i ≤ k ∧ k ≤ d - i then
        (Nat.choose (d - k) (d - 1 - m) : ℤ)
      else 0) = gTheoremMatrix d i (m + 1) := by
  have hrev :
      (∑ k ∈ Finset.range (d + 1),
        if i ≤ k ∧ k ≤ d - i then
          (Nat.choose (d - k) (d - 1 - m) : ℤ)
        else 0) =
      ∑ n ∈ Finset.range (d + 1),
        if i ≤ n ∧ n ≤ d - i then
          (Nat.choose n (d - 1 - m) : ℤ)
        else 0 := by
    apply Finset.sum_bij (fun k _ => d - k)
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    · intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      omega
    · intro n hn
      rw [Finset.mem_range] at hn
      refine ⟨d - n, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      rw [Finset.mem_range] at hk
      have hcond : (i ≤ k ∧ k ≤ d - i) ↔ (i ≤ d - k ∧ d - k ≤ d - i) := by omega
      simp only [hcond]
  rw [hrev]
  have hsplit1 :
      (∑ n ∈ Finset.range (d + 1),
        if i ≤ n ∧ n ≤ d - i then
          (Nat.choose n (d - 1 - m) : ℤ)
        else 0) =
      ∑ n ∈ Finset.range (d + 1 - i),
        if i ≤ n then (Nat.choose n (d - 1 - m) : ℤ) else 0 := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : d + 1 - i ≤ d + 1)]
    have htail :
        (∑ n ∈ Finset.Ico (d + 1 - i) (d + 1),
          if i ≤ n ∧ n ≤ d - i then
            (Nat.choose n (d - 1 - m) : ℤ)
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_Ico] at hn
      exact if_neg (by omega)
    rw [htail, add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    have hcond : (i ≤ n ∧ n ≤ d - i) ↔ i ≤ n := by omega
    simp only [hcond]
  rw [hsplit1, ← Finset.sum_range_add_sum_Ico _ (by omega : i ≤ d + 1 - i)]
  have hhead :
      (∑ n ∈ Finset.range i,
        if i ≤ n then (Nat.choose n (d - 1 - m) : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_range] at hn
    exact if_neg (by omega)
  have hmid :
      (∑ n ∈ Finset.Ico i (d + 1 - i),
        if i ≤ n then (Nat.choose n (d - 1 - m) : ℤ) else 0) =
      ∑ n ∈ Finset.Ico i (d + 1 - i), (Nat.choose n (d - 1 - m) : ℤ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact if_pos hn.1
  rw [hhead, zero_add, hmid]
  have hadd := Finset.sum_range_add_sum_Ico
    (fun n => (Nat.choose n (d - 1 - m) : ℤ)) (by omega : i ≤ d + 1 - i)
  have hsum1 :
      (∑ n ∈ Finset.range (d + 1 - i), (Nat.choose n (d - 1 - m) : ℤ)) =
        (Nat.choose (d + 1 - i) (d + 1 - (m + 1)) : ℤ) := by
    rw [← Nat.cast_sum, sum_range_choose_eq]
    have hr : d - 1 - m + 1 = d + 1 - (m + 1) := by omega
    rw [hr]
  have hsum2 :
      (∑ n ∈ Finset.range i, (Nat.choose n (d - 1 - m) : ℤ)) =
        (Nat.choose i (d + 1 - (m + 1)) : ℤ) := by
    rw [← Nat.cast_sum, sum_range_choose_eq]
    have hr : d - 1 - m + 1 = d + 1 - (m + 1) := by omega
    rw [hr]
  unfold gTheoremMatrix
  linarith

theorem h_eq_sum_range_g_of_le_half (d : ℕ) (h g : ℕ → ℕ)
    (hh0 : h 0 = 1) (hg0 : g 0 = 1)
    (hdiff : ∀ k, k < d / 2 → h (k + 1) = h k + g (k + 1)) :
    ∀ k ≤ d / 2, h k = ∑ i ∈ Finset.range (k + 1), g i := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [Finset.sum_range_one, hh0, hg0]
  | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ _ (k + 1), ← ih (by omega), hdiff k (by omega)]

theorem h_eq_symm_interval_sum_g (d : ℕ) (h g : ℕ → ℕ)
    (hh0 : h 0 = 1) (hg0 : g 0 = 1)
    (hsymm : ∀ k ≤ d, h (d - k) = h k)
    (hdiff : ∀ k, k < d / 2 → h (k + 1) = h k + g (k + 1)) :
    ∀ k ≤ d, h k =
      ∑ i ∈ Finset.range (d / 2 + 1),
        if i ≤ k ∧ k ≤ d - i then g i else 0 := by
  have hlow := h_eq_sum_range_g_of_le_half d h g hh0 hg0 hdiff
  have hlow_ite : ∀ m ≤ d / 2, h m =
      ∑ i ∈ Finset.range (d / 2 + 1),
        if i ≤ m ∧ m ≤ d - i then g i else 0 := by
    intro m hm
    rw [hlow m hm, ← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ d / 2 + 1)]
    have htail :
        (∑ i ∈ Finset.Ico (m + 1) (d / 2 + 1),
          if i ≤ m ∧ m ≤ d - i then g i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact if_neg (by omega)
    rw [htail, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
  intro k hk
  by_cases hkhalf : k ≤ d / 2
  · exact hlow_ite k hkhalf
  · rw [← hsymm k hk, hlow_ite (d - k) (by omega)]
    apply Finset.sum_congr rfl
    intro i hi
    have hcond : (i ≤ d - k ∧ d - k ≤ d - i) ↔ (i ≤ k ∧ k ≤ d - i) := by omega
    simp only [hcond]

/-- If `h` satisfies `h 0 = 1`, Dehn–Sommerville symmetry `h (d - k) = h k`, and the
McMullen face-count identity, and `g` satisfies `g 0 = 1` and `h (k + 1) = h k + g (k + 1)`
for `k < d / 2`, then `g` represents all canonical face counts via `gTheoremMatrix`. -/
theorem faceCount_eq_sum_gTheoremMatrix_of_dehn_sommerville
    {d : ℕ} {P : Set (Fin d → ℝ)} (h g : ℕ → ℕ)
    (hh0 : h 0 = 1) (hg0 : g 0 = 1)
    (hsymm : ∀ k ≤ d, h (d - k) = h k)
    (hface : ∀ m < d, faceCount P m =
      ∑ k ∈ Finset.range (d + 1), h k * Nat.choose (d - k) (d - 1 - m))
    (hdiff : ∀ k, k < d / 2 → h (k + 1) = h k + g (k + 1)) :
    ∀ j : Fin d, (faceCount P j.val : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  intro j
  rw [hface j.val j.isLt, Nat.cast_sum]
  have hstep (k : ℕ) (hk : k ∈ Finset.range (d + 1)) :
      ((h k * Nat.choose (d - k) (d - 1 - j.val) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          (g i : ℤ) *
            (if i ≤ k ∧ k ≤ d - i then
              (Nat.choose (d - k) (d - 1 - j.val) : ℤ)
            else 0) := by
    rw [Finset.mem_range] at hk
    rw [h_eq_symm_interval_sum_g d h g hh0 hg0 hsymm hdiff k (by omega),
      Finset.sum_mul, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [← Finset.mul_sum,
    sum_symm_interval_choose_eq_gTheoremMatrix d i j.val (by omega) j.isLt]
  rfl

end Grunbaum2003.GNecessityNext
-- END GNecessityNextMatrixRepresentation.lean

-- BEGIN GSufficiencyNextSolution.lean
set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped Classical BigOperators

noncomputable section

namespace Grunbaum2003

open Grunbaum2003.BilleraLee
open Grunbaum2003.GNecessityNext

private lemma gTheoremMatrix_zero_of_lt (d i k : ℕ) (hki : k < i) (hi : i ≤ d / 2) :
    gTheoremMatrix d i k = 0 := by
  unfold gTheoremMatrix
  have h1 : Nat.choose (d + 1 - i) (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  have h2 : Nat.choose i (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h1, h2]

private lemma gTheoremMatrix_diag_eq_one (d k : ℕ) (hk : k ≤ d / 2) :
    gTheoremMatrix d k k = 1 := by
  unfold gTheoremMatrix
  have h2 : Nat.choose k (d + 1 - k) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [h2]

private lemma gTheoremMatrix_eq_ite_of_le_half (d i k : ℕ) (hi : i ≤ d / 2) (hk : k ≤ d / 2) :
    gTheoremMatrix d i k =
      if i ≤ k then (Nat.choose (d + 1 - i) (k - i) : ℤ) else 0 := by
  split_ifs with hik
  · unfold gTheoremMatrix
    have h2 : Nat.choose i (d + 1 - k) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have hsymm : Nat.choose (d + 1 - i) (d + 1 - k) = Nat.choose (d + 1 - i) (k - i) := by
      have hsub : (d + 1 - i) - (d + 1 - k) = k - i := by omega
      rw [← hsub, Nat.choose_symm (by omega : d + 1 - k ≤ d + 1 - i)]
    simp [h2, hsymm]
  · exact gTheoremMatrix_zero_of_lt d i k (by omega) hi

private lemma gTheoremMatrix_prefix_sum_eq_of_le_half (d : ℕ) (g : ℕ → ℤ) (k : ℕ) (hk : k ≤ d / 2) :
    ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k =
      (∑ i ∈ Finset.range k, g i * gTheoremMatrix d i k) + g k := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ d / 2 + 1)]
  have hTail : ∑ i ∈ Finset.Ico (k + 1) (d / 2 + 1), g i * gTheoremMatrix d i k = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [gTheoremMatrix_zero_of_lt d i k (by omega) (by omega), mul_zero]
  rw [hTail, add_zero, Finset.sum_range_succ, gTheoremMatrix_diag_eq_one d k hk, mul_one]

private lemma gTheoremMatrix_unique_of_le_half (d : ℕ) (g₁ g₂ : ℕ → ℤ)
    (hEq : ∀ k : ℕ, k ≤ d / 2 →
      ∑ i ∈ Finset.range (d / 2 + 1), g₁ i * gTheoremMatrix d i k =
      ∑ i ∈ Finset.range (d / 2 + 1), g₂ i * gTheoremMatrix d i k) :
    ∀ k : ℕ, k ≤ d / 2 → g₁ k = g₂ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hEqk := hEq k hk
    rw [gTheoremMatrix_prefix_sum_eq_of_le_half d g₁ k hk,
      gTheoremMatrix_prefix_sum_eq_of_le_half d g₂ k hk] at hEqk
    have hSum : ∑ i ∈ Finset.range k, g₁ i * gTheoremMatrix d i k =
        ∑ i ∈ Finset.range k, g₂ i * gTheoremMatrix d i k := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hik : i < k := Finset.mem_range.1 hi
      rw [ih i hik (by omega)]
    omega

private lemma h_int_eq_sum_range_g_of_le_half (d : ℕ) (h : ℕ → ℕ) (g : ℕ → ℤ)
    (hh0 : h 0 = 1) (hg0 : g 0 = 1)
    (hdiff : ∀ k, k < d / 2 → (h (k + 1) : ℤ) = (h k : ℤ) + g (k + 1)) :
    ∀ k ≤ d / 2, (h k : ℤ) = ∑ i ∈ Finset.range (k + 1), g i := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [Finset.sum_range_one, hh0, Nat.cast_one, hg0]
  | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ _ (k + 1), ← ih (by omega), hdiff k (by omega)]

private lemma h_int_eq_symm_interval_sum_g (d : ℕ) (h : ℕ → ℕ) (g : ℕ → ℤ)
    (hh0 : h 0 = 1) (hg0 : g 0 = 1)
    (hsymm : ∀ k ≤ d, h (d - k) = h k)
    (hdiff : ∀ k, k < d / 2 → (h (k + 1) : ℤ) = (h k : ℤ) + g (k + 1)) :
    ∀ k ≤ d, (h k : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1),
        if i ≤ k ∧ k ≤ d - i then g i else 0 := by
  have hlow := h_int_eq_sum_range_g_of_le_half d h g hh0 hg0 hdiff
  have hlow_ite : ∀ m ≤ d / 2, (h m : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1),
        if i ≤ m ∧ m ≤ d - i then g i else 0 := by
    intro m hm
    rw [hlow m hm, ← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ d / 2 + 1)]
    have htail :
        (∑ i ∈ Finset.Ico (m + 1) (d / 2 + 1),
          if i ≤ m ∧ m ≤ d - i then g i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact if_neg (by omega)
    rw [htail, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
  intro k hk
  by_cases hkhalf : k ≤ d / 2
  · exact hlow_ite k hkhalf
  · rw [← hsymm k hk, hlow_ite (d - k) (by omega)]
    apply Finset.sum_congr rfl
    intro i _
    have hcond : (i ≤ d - k ∧ d - k ≤ d - i) ↔ (i ≤ k ∧ k ≤ d - i) := by omega
    simp only [hcond]

private lemma faceCount_eq_sum_gTheoremMatrix_of_dehn_sommerville_int
    {d : ℕ} {P : Set (Fin d → ℝ)} (h : ℕ → ℕ) (g : ℕ → ℤ)
    (hh0 : h 0 = 1) (hg0 : g 0 = 1)
    (hsymm : ∀ k ≤ d, h (d - k) = h k)
    (hface : ∀ m < d, faceCount P m =
      ∑ k ∈ Finset.range (d + 1), h k * Nat.choose (d - k) (d - 1 - m))
    (hdiff : ∀ k, k < d / 2 → (h (k + 1) : ℤ) = (h k : ℤ) + g (k + 1)) :
    ∀ j : Fin d, (faceCount P j.val : ℤ) =
      ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i j.succ.val := by
  intro j
  rw [hface j.val j.isLt, Nat.cast_sum]
  have hstep (k : ℕ) (hk : k ∈ Finset.range (d + 1)) :
      ((h k * Nat.choose (d - k) (d - 1 - j.val) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1),
          g i *
            (if i ≤ k ∧ k ≤ d - i then
              (Nat.choose (d - k) (d - 1 - j.val) : ℤ)
            else 0) := by
    rw [Finset.mem_range] at hk
    rw [Nat.cast_mul, h_int_eq_symm_interval_sum_g d h g hh0 hg0 hsymm hdiff k (by omega),
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [← Finset.mul_sum,
    sum_symm_interval_choose_eq_gTheoremMatrix d i j.val (by omega) j.isLt]
  rfl

theorem g_theorem_sufficiency_pos_g2_from_upper_triangular (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) (hg2 : 0 < g 2)
    (hUpper :
      (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
      (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
      (∀ (k : ℕ), k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
          (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
      (∀ (k : ℕ), k ≤ d →
        gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ))) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      faceCount P 0 = d + 1 + g 1 ∧
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  have _ := hg1
  have _ := hg2
  have _ := hUpper
  obtain ⟨M, h0M, hdeg, hdiv, hinit, hcard⟩ :=
    MacaulayCompressed.exists_compressed_multicomplex (g 1) (d / 2) g hg (by omega)
  obtain ⟨Q₀, hQ₀_simp, hlow⟩ :=
    exists_section7_simplicial_polytope_low_faceCounts d (g 1 + 1) (by omega) (by omega)
      M h0M hdeg hdiv hinit g hcard
  have hhalf_ge_two : 2 ≤ d / 2 := by omega
  have hQ₀_f0 : faceCount Q₀ 0 = d + 1 + g 1 := by
    have h1 := hlow 1 le_rfl (by omega)
    simp only [Nat.sub_self] at h1
    rw [h1, ← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ d / 2 + 1)]
    have htail :
        (∑ i ∈ Finset.Ico 2 (d / 2 + 1),
          if i ≤ 1 then g i * Nat.choose (d + 1 - i) (1 - i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact if_neg (by omega)
    rw [htail, add_zero, Finset.sum_range_succ, Finset.sum_range_one]
    simp [hg.1, Nat.choose_one_right]
  have hQ₀_f1 : faceCount Q₀ 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 := by
    have h2 := hlow 2 (by omega) hhalf_ge_two
    change faceCount Q₀ 1 = _ at h2
    rw [h2, ← Finset.sum_range_add_sum_Ico _ (by omega : 3 ≤ d / 2 + 1)]
    have htail :
        (∑ i ∈ Finset.Ico 3 (d / 2 + 1),
          if i ≤ 2 then g i * Nat.choose (d + 1 - i) (2 - i) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact if_neg (by omega)
    rw [htail, add_zero, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.zero_le, ↓reduceIte, hg.1, one_mul, Nat.sub_zero,
      show (1 : ℕ) ≤ 2 by decide, show 2 - 1 = 1 by rfl,
      show d + 1 - 1 = d by omega, Nat.choose_one_right,
      le_rfl, Nat.sub_self, Nat.choose_zero_right, mul_one]
    ring
  have : Finite (PolytopeVertex Q₀) := finite_polytopeVertex hQ₀_simp.1
  letI : Fintype (PolytopeVertex Q₀) := Fintype.ofFinite (PolytopeVertex Q₀)
  obtain ⟨c, _, hh0, _, hsymm, hface⟩ :=
    exists_dehn_sommerville_parameterQuotient (by omega : 2 ≤ d) hQ₀_simp
  let h : ℕ → ℕ := fun k =>
    Module.finrank ℝ (HomogeneousIdealPiece
      (parameterQuotientIdeal (nonfaceIdeal (polytopeBoundary Q₀))
        (coordinateParameterMap (fun v : PolytopeVertex Q₀ => v.val - c))) k)
  let g_Q : ℕ → ℤ := fun i =>
    match i with
    | 0 => 1
    | k + 1 => (h (k + 1) : ℤ) - (h k : ℤ)
  have hg_Q0 : g_Q 0 = 1 := rfl
  have hdiff_Q (k : ℕ) (_ : k < d / 2) : (h (k + 1) : ℤ) = (h k : ℤ) + g_Q (k + 1) := by
    dsimp [g_Q]
    ring
  have hDS_mat := faceCount_eq_sum_gTheoremMatrix_of_dehn_sommerville_int h g_Q
    hh0 hg_Q0 hsymm hface hdiff_Q
  have hlow_mat (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ d / 2) :
      (faceCount Q₀ (k - 1) : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k := by
    rw [hlow k hk1 hk, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gTheoremMatrix_eq_ite_of_le_half d i k (by omega) hk]
    split_ifs <;> simp
  have hEq_half (k : ℕ) (hk : k ≤ d / 2) :
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
        ∑ i ∈ Finset.range (d / 2 + 1), g_Q i * gTheoremMatrix d i k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [gTheoremMatrix_prefix_sum_eq_of_le_half d (fun i => (g i : ℤ)) 0 hk,
        gTheoremMatrix_prefix_sum_eq_of_le_half d g_Q 0 hk]
      simp [hg.1, hg_Q0]
    · let j : Fin d := ⟨k - 1, by omega⟩
      have hj_val : j.val = k - 1 := rfl
      have hj_succ : j.succ.val = k := by
        change (k - 1) + 1 = k
        omega
      have h1 := hlow_mat k hkpos hk
      have h2 := hDS_mat j
      rw [hj_val, hj_succ] at h2
      exact h1.symm.trans h2
  have hg_eq_g_Q (i : ℕ) (hi : i ≤ d / 2) : (g i : ℤ) = g_Q i :=
    gTheoremMatrix_unique_of_le_half d (fun i => (g i : ℤ)) g_Q hEq_half i hi
  refine ⟨Q₀, hQ₀_simp, hQ₀_f0, hQ₀_f1, ?_⟩
  intro j
  rw [hDS_mat j]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [hg_eq_g_Q i (by omega)]

end Grunbaum2003
-- END GSufficiencyNextSolution.lean

open Grunbaum2003 in
theorem solution (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) (hg2 : 0 < g 2)
    (hUpper :
      (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
      (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
      (∀ (k : ℕ), k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
          (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
      (∀ (k : ℕ), k ≤ d →
        gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ))) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      faceCount P 0 = d + 1 + g 1 ∧
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val :=
  Grunbaum2003.g_theorem_sufficiency_pos_g2_from_upper_triangular d hd g hg hg1 hg2 hUpper
