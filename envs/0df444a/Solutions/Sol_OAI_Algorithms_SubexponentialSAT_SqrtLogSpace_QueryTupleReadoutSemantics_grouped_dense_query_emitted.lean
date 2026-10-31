-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:37:09.221329+00:00
-- url     : https://prove2.me/submissions/05f506a5-912e-445c-bf86-efca2b102522

import Mathlib
import Definitions.Def_OAIQ081S151

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_BooleanDifferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

private theorem subset_sign_sum (E T : Finset V) :
    (∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
      (if T ⊆ U then 1 else 0)) = if T = E then 1 else 0 := by
  induction E using Finset.induction_on generalizing T with
  | empty => simp only [Finset.powerset_empty, Finset.sum_singleton,
      Finset.card_empty, Nat.sub_self, pow_zero, one_mul, Finset.subset_empty]
  | @insert a E ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have hcard (U : Finset V) (hU : U ∈ E.powerset) : U.card ≤ E.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hU)
    have hnot (U : Finset V) (hU : U ∈ E.powerset) : a ∉ U :=
      fun h => ha (Finset.mem_powerset.mp hU h)
    by_cases hat : a ∈ T
    · have hzero : (∑ U ∈ E.powerset, (-1 : R) ^ ((insert a E).card - U.card) *
          (if T ⊆ U then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro U hU
        simp [show ¬T ⊆ U from fun h => hnot U hU (h hat)]
      rw [hzero, zero_add]
      calc
        _ = ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
            (if T.erase a ⊆ U then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro U hU
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem (hnot U hU)]
          have hsub : T ⊆ insert a U ↔ T.erase a ⊆ U := by
            constructor
            · intro h v hv
              exact (Finset.mem_insert.mp (h (Finset.mem_erase.mp hv).2)).resolve_left
                (Finset.mem_erase.mp hv).1
            · intro h v hv
              by_cases hav : v = a
              · simp [hav]
              · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.mpr ⟨hav, hv⟩))
          simp [hsub]
        _ = if T.erase a = E then 1 else 0 := ih _
        _ = _ := by
          have heq : T.erase a = E ↔ T = insert a E := by
            constructor
            · intro h; rw [← h, Finset.insert_erase hat]
            · intro h; subst T; simp [ha]
          simp only [heq]
    · have hsub (U : Finset V) : T ⊆ insert a U ↔ T ⊆ U := by
        constructor
        · intro h v hv
          exact (Finset.mem_insert.mp (h hv)).resolve_left (fun h => hat (h ▸ hv))
        · exact fun h => h.trans (Finset.subset_insert _ _)
      have hfirst : (∑ U ∈ E.powerset, (-1 : R) ^ ((insert a E).card - U.card) *
          (if T ⊆ U then 1 else 0)) =
          -(∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
            (if T ⊆ U then 1 else 0)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro U hU
        rw [Finset.card_insert_of_notMem ha,
          show E.card + 1 - U.card = E.card - U.card + 1 by
            have := hcard U hU
            omega, pow_succ]
        split_ifs <;> simp
      rw [hfirst]
      have hsecond : (∑ U ∈ E.powerset,
          (-1 : R) ^ ((insert a E).card - (insert a U).card) *
            (if T ⊆ insert a U then 1 else 0)) =
          ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
            (if T ⊆ U then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro U hU
        simp [Finset.card_insert_of_notMem ha,
          Finset.card_insert_of_notMem (hnot U hU), hsub]
      rw [hsecond, neg_add_cancel]
      simp [show T ≠ insert a E from fun h => hat (h.symm ▸ Finset.mem_insert_self a E)]

theorem difference_monomial (E : Finset V) (d : V →₀ ℕ) (c : R) :
    difference E (MvPolynomial.monomial d c) = if d.support = E then c else 0 := by
  classical
  simp only [difference, evalAt_monomial]
  calc
    _ = (∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) *
          (if d.support ⊆ U then 1 else 0)) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      split_ifs <;> simp
    _ = _ := by rw [subset_sign_sum]; split_ifs <;> simp

theorem difference_eq_sum_coeff (E : Finset V) (p : MvPolynomial V R) :
    difference E p = ∑ d ∈ p.support,
      if d.support = E then p.coeff d else 0 := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [difference, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  exact difference_monomial E d (p.coeff d)

omit [DecidableEq V] in
/-- Degree controls the number of distinct variables in every monomial. -/
theorem support_card_le_totalDegree (p : MvPolynomial V R) {d : V →₀ ℕ}
    (hd : d ∈ p.support) : d.support.card ≤ p.totalDegree := by
  calc
    d.support.card = ∑ v ∈ d.support, 1 := by simp
    _ ≤ ∑ v ∈ d.support, d v := Finset.sum_le_sum (fun v hv =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

/-- Recovery at one Boolean point; high-degree supports do not contribute. -/
theorem evalAt_eq_sum_differences [Fintype V] {J : ℕ} (X : Finset V)
    (p : MvPolynomial V R) (hp : p.totalDegree < J) :
    evalAt X p = ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J),
      if E ⊆ X then difference E p else 0 := by
  classical
  simp only [difference_eq_sum_coeff]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hcard : d.support.card < J := (support_card_le_totalDegree p hd).trans_lt hp
  rw [evalAt_monomial]
  by_cases hsub : d.support ⊆ X
  · rw [ite_eq_left hsub]
    symm
    rw [Finset.sum_eq_single d.support]
    · simp [hsub]
    · intro E _ hE
      simp [Ne.symm hE]
    · simp [hcard]
  · rw [ite_eq_right hsub]
    symm
    apply Finset.sum_eq_zero
    intro E _
    by_cases he : d.support = E
    · subst E; simp [hsub]
    · simp [he]

/-- ETH Boolean finite differences over an arbitrary commutative ring.
The polynomial is allowed to depend on the assignment being summed. -/
theorem sum_eval_eq_sum_differences [Fintype V] {J : ℕ}
    (p : (V → Bool) → MvPolynomial V R)
    (hp : ∀ x, (p x).totalDegree < J) :
    (∑ x, evalAt (trueSet x) (p x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        (-1 : R) ^ (E.card - U.card) *
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            evalAt U (p x) := by
  classical
  conv_lhs =>
    arg 2
    ext x
    rw [evalAt_eq_sum_differences _ _ (hp x)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  simp only [difference, Finset.sum_filter, subset_trueSet]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSeparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Arbitrarily many independent symbolic color groups

Section 4.3 of `source/subexponential-sat.txt`.  The color type is an arbitrary
finite type, so the results apply to `Fin r` with no fixed bound on `r`.
Every sum and product is a genuine finite operation in a commutative semiring.
The independence assumptions are pointwise statements about group values,
not assumptions about the desired sum identity.
-/

namespace SubexponentialSAT.SubexpSeparation

open scoped BigOperators

section IndependentProducts

variable {R G : Type*} {X : G → Type*} [CommSemiring R]
  [Fintype G] [DecidableEq G] [∀ g, Fintype (X g)]

/-- Finite distributivity over all independent color choices. -/
theorem sum_prod_eq_prod_sum (f : ∀ g, X g → R) :
    (∑ x : ∀ g, X g, ∏ g, f g (x g)) = ∏ g, ∑ y : X g, f g y :=
  (Fintype.prod_sum f).symm

/-- Equation (4.6) for fixed outer data.  The group of color `g` depends only
on the `g` input.  All other inputs may therefore be replaced by their fixed
representatives when evaluating that group, while the actual weight stays. -/
theorem weighted_separation (reps : ∀ g, X g)
    (A : G → (∀ g, X g) → R) (w : (∀ g, X g) → R)
    (c : R) (wg : ∀ g, X g → R)
    (hA : ∀ g x y, x g = y g → A g x = A g y)
    (hw : ∀ x, w x = c * ∏ g, wg g (x g)) :
    (∑ x : ∀ g, X g, w x * ∏ g, A g x) =
      c * ∏ g, ∑ y : X g, wg g y * A g (Function.update reps g y) := by
  calc
    _ = ∑ x : ∀ g, X g,
        c * ∏ g, wg g (x g) * A g (Function.update reps g (x g)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hw, mul_assoc, ← Finset.prod_mul_distrib]
      apply congrArg (c * ·)
      apply Finset.prod_congr rfl
      intro g hg
      rw [hA g x (Function.update reps g (x g)) (by simp)]
    _ = c * (∑ x : ∀ g, X g,
        ∏ g, wg g (x g) * A g (Function.update reps g (x g))) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (c * ·)
      (sum_prod_eq_prod_sum (fun g y => wg g y * A g (Function.update reps g y)))

end IndependentProducts

section OuterData

variable {R Ω O G : Type*} {X : O → G → Type*} [CommSemiring R]
  [Fintype Ω] [Fintype O] [Fintype G] [DecidableEq G]
  [∀ o g, Fintype (X o g)]

/-- An actual equivalence reindexes the full assignment space by its outer
data and one independent inner choice for each color. -/
theorem sum_reindex_fibers (e : Ω ≃ Σ o, ∀ g, X o g) (f : Ω → R) :
    (∑ z, f z) = ∑ o, ∑ x : ∀ g, X o g, f (e.symm ⟨o, x⟩) := by
  calc
    _ = ∑ z : Σ o, ∀ g, X o g, f (e.symm z) :=
      Fintype.sum_equiv e _ _ (fun z => by rw [e.symm_apply_apply])
    _ = _ := Fintype.sum_sigma _

end OuterData

end SubexponentialSAT.SubexpSeparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

noncomputable section

variable [DecidableEq V] [CommSemiring R]

theorem eval_eq_sum (x : V → R) (hx : ∀ v, x v * x v = x v) (f : Poly V R) :
    evalHom x hx f = f.coeff.sum (fun s c => c * weight x s.vars) := by
  calc
    evalHom x hx f = evalHom x hx (f.coeff.sum MonoidAlgebra.single) := by
      rw [MonoidAlgebra.sum_coeff_single]
    _ = f.coeff.sum (fun s c => c * weight x s.vars) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro a ha
      exact eval_monomial x hx a.vars (f.coeff a)

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsBuckets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual attained labels and their Boolean fibers. The label codomain need
not be finite: integer signature vectors are allowed. Enumeration is the
image of each finite head assignment set, followed by its actual fibers. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

section BooleanFibers

variable {V G : Type*} [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

/-- The actual bucket product has exactly the original Boolean mass. -/
theorem sum_boolean_actual_buckets {B : Type*} [CommSemiring B]
    (head : V → G) (label : ∀ g, (Head head g → Bool) → L g)
    (f : (V → Bool) → B) :
    (∑ x, f x) = ∑ y : ∀ g, LabelValue label g,
      ∑ a : ∀ g, LabelBucket label g (y g), f (assemble head (fun g => (a g).val)) := by
  classical
  exact SubexpSeparation.sum_reindex_fibers (booleanBucketEquiv head label) f

end BooleanFibers

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Restricted sums over the actual Boolean heads. All products are formed in
one coefficient ring before any additive coefficient readout. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

/-- An actual head rescan tests the entire key and the correction predicate.
The finite sum here specifies its result; it does not materialize a fiber. -/
theorem fiber_sum_eq_rescan {X K R : Type*} [Fintype X] [DecidableEq K]
    [AddCommMonoid R] (label : X → K) (key : K) (P : X → Prop)
    [DecidablePred P] (f : X → R) :
    (∑ a : {x // label x = key}, if P a.val then f a.val else 0) =
      ∑ a : X, if label a = key ∧ P a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x => label x = key))
    (by simp) (fun x => if P x then f x else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hk : label x = key <;> simp [hk]

section RestrictedSeparation

variable {R G : Type*} {X : G → Type*} [CommSemiring R]
  [Fintype G] [DecidableEq G] [∀ g, Fintype (X g)]

/-- Representatives belong to their signature fibers but need not satisfy
any of the additional local correction restrictions. -/
theorem restricted_separation (reps : ∀ g, X g)
    (A : G → (∀ g, X g) → R) (P : ∀ g, X g → Prop)
    [∀ g, DecidablePred (P g)]
    (hA : ∀ g x y, x g = y g → A g x = A g y) :
    (∑ x : ∀ g, X g, if ∀ g, P g (x g) then ∏ g, A g x else 0) =
      ∏ g, ∑ a : X g, if P g a then A g (Function.update reps g a) else 0 := by
  have h := OAI.Algorithms.SubexponentialSAT.SubexpSeparation.weighted_separation reps A
    (fun x => if ∀ g, P g (x g) then 1 else 0) 1
    (fun g a => if P g a then 1 else 0) hA
    (fun x => by simp only [one_mul, Fintype.prod_boole])
  simpa only [one_mul, ite_mul, zero_mul] using h

end RestrictedSeparation

section BooleanHeads

variable {V G R : Type*} [Fintype V] [Fintype G]
  [DecidableEq V] [DecidableEq G] [CommSemiring R]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

omit [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G] in
/-- The current finite-difference support restricts original variables.
There is one Boolean choice per variable, including variables with no incidences. -/
theorem restricted_assemble_iff (head : V → G) (E : Finset V)
    (a : ∀ g, Head head g → Bool) :
    (∀ v ∈ E, assemble head a v = true) ↔
      ∀ g (v : Head head g), v.val ∈ E → a g v = true := by
  constructor
  · intro h g v hv
    rcases v with ⟨v, hg⟩
    cases hg
    exact h v hv
  · intro h v hv
    exact h (head v) ⟨v, rfl⟩ hv

/-- Reindex by attained full labels and perform each restricted head sum.
`hA` is the locality proved from the actual layout's integer kernels. -/
theorem restricted_grouping (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (E : Finset V) (A : G → (V → Bool) → R)
    (hA : ∀ g x z, split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      A g x = A g z) :
    (∑ x : V → Bool, if ∀ v ∈ E, x v = true then ∏ g, A g x else 0) =
      ∑ y : ∀ g, LabelValue label g, ∏ g,
        ∑ a : LabelBucket label g (y g),
          if ∀ v : Head head g, v.val ∈ E → a.val v = true then
            A g (assemble head (fun h =>
              (Function.update (reps y) g a h).val)) else 0 := by
  classical
  rw [sum_boolean_actual_buckets head label]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [restricted_assemble_iff]
  apply restricted_separation (reps y)
    (fun g x => A g (assemble head (fun h => (x h).val)))
    (fun g a => ∀ v : Head head g, v.val ∈ E → a.val v = true)
  intro g x z hxz
  apply hA g
  · have hx := (headEquiv head).apply_symm_apply (fun h => (x h).val)
    have hz := (headEquiv head).apply_symm_apply (fun h => (z h).val)
    change split head (assemble head (fun h => (x h).val)) = _ at hx
    change split head (assemble head (fun h => (z h).val)) = _ at hz
    rw [hx, hz]
    exact congrArg Subtype.val hxz
  · intro h _
    have hx := (headEquiv head).apply_symm_apply (fun h => (x h).val)
    have hz := (headEquiv head).apply_symm_apply (fun h => (z h).val)
    change split head (assemble head (fun h => (x h).val)) = _ at hx
    change split head (assemble head (fun h => (z h).val)) = _ at hz
    rw [hx, hz, (x h).property, (z h).property]

end BooleanHeads

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

variable {V G R : Type*} [Fintype V] [Fintype G]
  [DecidableEq V] [DecidableEq G] [CommSemiring R]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

/-- Each attained tuple is followed by one bounded-width raw head rescan;
the complete key is checked before a contribution is admitted. -/
theorem restricted_grouping_rescan (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (E : Finset V) (A : G → (V → Bool) → R)
    (hA : ∀ g x z, split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      A g x = A g z) :
    (∑ x : V → Bool, if ∀ v ∈ E, x v = true then ∏ g, A g x else 0) =
      ∑ y : ∀ g, LabelValue label g, ∏ g,
        ∑ a : Head head g → Bool,
          if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v=true) then
            A g (assemble head (Function.update (fun h => (reps y h).val) g a)) else 0 := by
  classical
  rw [restricted_grouping head label reps E A hA]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro g _
  rw [←fiber_sum_eq_rescan (label g) (y g).val
    (fun a => ∀ v : Head head g, v.val ∈ E → a v=true)
    (fun a => A g (assemble head (Function.update (fun h => (reps y h).val) g a)))]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  apply congrArg (assemble head)
  funext h
  by_cases hh : h=g
  · subst h
    simp
  · simp [Function.update_of_ne hh]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact natural-valued query semantics. These identities preserve the ambient
assignment type, including coordinates absent from every clause. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation

open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

section SquarefreeBridge

variable {V R : Type*} [DecidableEq V] [CommRing R]

theorem eval_squarefreePolynomial (f : Squarefree.Poly V R)
    (x : V → R) (hx : ∀ v, x v * x v = x v) :
    MvPolynomial.eval x (squarefreePolynomial f) = Squarefree.evalHom x hx f := by
  classical
  rw [Squarefree.eval_eq_sum]
  simp [squarefreePolynomial, Finsupp.sum, Squarefree.weight]

omit [DecidableEq V] in
/-- Existing positive-Taylor-degree support control implies the hypothesis of
Boolean finite differences, without a new backend or formal-variable expansion. -/
theorem squarefreePolynomial_totalDegree (f : Squarefree.Poly V R) (q : ℕ)
    (hf : Squarefree.Bounded q f) : (squarefreePolynomial f).totalDegree ≤ q := by
  classical
  nontriviality R using Subsingleton.eq_zero (squarefreePolynomial f)
  unfold squarefreePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  calc
    (MvPolynomial.C (f.coeff s) * ∏ v ∈ s.vars, MvPolynomial.X v).totalDegree ≤
        0 + ∑ v ∈ s.vars, (MvPolynomial.X v : MvPolynomial V R).totalDegree := by
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add (by simp) (MvPolynomial.totalDegree_finsetProd _ _))
    _ = s.vars.card := by simp
    _ ≤ q := hf s hs

@[simp] theorem evalAt_squarefreePolynomial (U : Finset V) (f : Squarefree.Poly V R) :
    BooleanDifferences.evalAt U (squarefreePolynomial f) =
      Squarefree.evalBool (fun v => decide (v ∈ U)) f := by
  have he : (fun v => if v ∈ U then (1 : R) else 0) =
      Squarefree.boolValue (fun v => decide (v ∈ U)) := by
    funext v
    simp [Squarefree.boolValue]
  rw [BooleanDifferences.evalAt, he]
  exact eval_squarefreePolynomial f _ (Squarefree.boolValue_idempotent _)

/-- Boolean finite differences apply directly to the source's squarefree
coefficients; the original support bound supplies the degree premise. -/
theorem squarefree_sum_eval_differences [Fintype V] {q J : ℕ} (hq : q < J)
    (f : (V → Bool) → Squarefree.Poly V R) (hf : ∀ x, Squarefree.Bounded q (f x)) :
    (∑ x, Squarefree.evalBool x (f x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        (-1 : R) ^ (E.card - U.card) *
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            Squarefree.evalBool (fun v => decide (v ∈ U)) (f x) := by
  classical
  have htrue (x : V → Bool) :
      (fun v => decide (v ∈ BooleanDifferences.trueSet x)) = x := by
    funext v
    simp [BooleanDifferences.trueSet]
  simpa only [evalAt_squarefreePolynomial, htrue] using
    BooleanDifferences.sum_eval_eq_sum_differences (fun x => squarefreePolynomial (f x))
      (fun x => (squarefreePolynomial_totalDegree (f x) q (hf x)).trans_lt hq)

/-- All Taylor and lifting coefficients use the same streamed pair family.
The sign is an integer action, so no multiplicativity of readout is needed. -/
theorem dense_jet_finite_differences [Fintype V] (t J : ℕ)
    (f : (V → Bool) → Squarefree.Jet V R)
    (hf : ∀ x, Squarefree.Admissible (f x)) :
    (∑ x, specializeDense t J x (f x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            specializeDense t J (fun v => decide (v ∈ U)) (f x) := by
  classical
  ext u z
  simp only [Truncated.coeff_sum, Truncated.coeff_zsmul, coeff_specializeDense]
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    squarefree_sum_eval_differences z.isLt
      (fun x => ((f x).coeff u.val).coeff z.val) (fun x => hf x u.val z.val)

end SquarefreeBridge

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryJetSelected
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact dense semantics of the native selected-factor run after immediate
Boolean specialization. The common lifting marker remains through products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open scoped BigOperators
open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open LeafProgram LeafProgram.NodeSemantics


section RescanQuery

open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments QueryEvaluation

variable {V G R : Type*} [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [CommRing R]
  {L : G → Type*} [∀ g, DecidableEq (L g)]

/-- The exact dense query in the form tested by the native full-head rescan:
the complete attained key and correction condition guard each contribution.
The shared-marker readout is applied after every group multiplication. -/
theorem grouped_dense_query_rescan (t J : ℕ) (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (A : G → (V → Bool) → Squarefree.Jet V R)
    (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
    (hlocal : ∀ (U : Finset V) g x z,
      split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
        specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
    Dense.readout (∑ x, specializeDense t J x (∏ g, A g x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ y : ∀ g, LabelValue label g,
            Dense.readout (∏ g, ∑ a : Head head g → Bool,
              if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
                specializeDense t J (fun v => decide (v ∈ U))
                  (A g (assemble head (Function.update (fun h => (reps y h).val) g a)))
              else 0) := by
  classical
  rw [dense_jet_finite_differences t J (fun x => ∏ g, A g x) hadm]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  apply congrArg (fun a => ((-1 : ℤ) ^ (E.card - U.card)) • a)
  have hg := HeadEvaluation.restricted_grouping_rescan head label reps E
    (fun g x => specializeDense t J (fun v => decide (v ∈ U)) (A g x)) (hlocal U)
  have hgroup :
      (∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
        specializeDense t J (fun v => decide (v ∈ U)) (∏ g, A g x)) =
      ∑ y : ∀ g, LabelValue label g, ∏ g, ∑ a : Head head g → Bool,
        if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
          specializeDense t J (fun v => decide (v ∈ U))
            (A g (assemble head (Function.update (fun h => (reps y h).val) g a)))
        else 0 := by
    simpa only [Finset.sum_filter, map_prod] using hg
  simpa only [map_sum] using congrArg Dense.readout hgroup

end RescanQuery

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleReadoutSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact readout of the emitted first-occurrence tuples. The equivalences
below preserve the numeric representative at every head. They are proof-level
reindexings of the native traversal, not stored families or evaluator services. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog Moments SignatureTupleDFS SignatureTupleTraversal
open Classical

section Representatives

variable {r : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}
    {X L : Fin r → Type*} [∀ g, Fintype (X g)] [∀ g, DecidableEq (L g)]

/-- Multiplicity one is inherited from the proved first-occurrence
equivalence, with the actual representative assignment in every summand. -/
theorem sum_emitted (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    {M : Type*} [AddCommMonoid M] (value : (∀ g, X g) → M) :
    (∑ reps : Prefix (Representatives key) r,
      value (fun g => enumerate g (reps g).val)) =
    ∑ y : ∀ g, LabelValue label g,
      value (fun g => (labelRepresentatives key enumerate label hkernel y g).val) := by
  classical
  simpa only [labelRepresentatives_emitted] using
    (tupleLabelEquiv key enumerate label hkernel).sum_comp
      (fun y => value (fun g => (labelRepresentatives key enumerate label hkernel y g).val))

end Representatives

section Readout

variable {r : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    {L : Fin r → Type*} [∀ g, DecidableEq (L g)]

/-- The exact native tuple value: full-head key and correction tests remain
inside each head sum, and additive readout remains outside the full product. -/
theorem emitted_readout (t J : ℕ) (head : V → Fin r)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ (Head head g → Bool))
    (label : ∀ g, (Head head g → Bool) → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (E : Finset V) (A : Fin r → (V → Bool) → Dense R t J) :
    (∑ reps : Prefix (Representatives key) r,
      Dense.readout (∏ g, ∑ a : Head head g → Bool,
        if label g a = label g (enumerate g (reps g).val) ∧
            (∀ v : Head head g, v.val ∈ E → a v = true) then
          A g (assemble head (Function.update (fun h => enumerate h (reps h).val) g a))
        else 0)) =
    ∑ y : ∀ g, LabelValue label g,
      Dense.readout (∏ g, ∑ a : Head head g → Bool,
        if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
          A g (assemble head (Function.update
            (fun h => (labelRepresentatives key enumerate label hkernel y h).val) g a))
        else 0) := by
  classical
  have h := sum_emitted key enumerate label hkernel
    (fun reps => Dense.readout (∏ g, ∑ a : Head head g → Bool,
      if label g a = label g (reps g) ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
        A g (assemble head (Function.update reps g a)) else 0))
  simpa only [(labelRepresentatives key enumerate label hkernel _ _).property] using h

/-- Reindex the existing finite-difference/grouping theorem by exactly the
tuples emitted by the native traversal. No coefficient identity is reproved. -/
theorem grouped_dense_query_emitted_oai (t J : ℕ) (head : V → Fin r)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ (Head head g → Bool))
    (label : ∀ g, (Head head g → Bool) → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (A : Fin r → (V → Bool) → Squarefree.Jet V R)
    (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
    (hlocal : ∀ (U : Finset V) g x z,
      split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
    Dense.readout (∑ x, QueryEvaluation.specializeDense t J x (∏ g, A g x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ reps : Prefix (Representatives key) r,
            Dense.readout (∏ g, ∑ a : Head head g → Bool,
              if label g a = label g (enumerate g (reps g).val) ∧
                  (∀ v : Head head g, v.val ∈ E → a v = true) then
                QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U))
                  (A g (assemble head
                    (Function.update (fun h => enumerate h (reps h).val) g a)))
              else 0) := by
  rw [QueryJetSemantics.grouped_dense_query_rescan t J head label
    (labelRepresentatives key enumerate label hkernel) A hadm hlocal]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  apply congrArg (fun a => ((-1 : ℤ) ^ (E.card - U.card)) • a)
  exact (emitted_readout t J head key enumerate label hkernel E
    (fun g x => QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g x))).symm

end Readout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics
end
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted_oai.{u_1, u_2, u_3, u_4} := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted_oai.{u_1, u_2, u_3, u_4}
