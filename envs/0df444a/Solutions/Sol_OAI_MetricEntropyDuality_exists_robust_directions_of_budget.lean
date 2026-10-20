-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_robust_directions_of_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:58:14.056496+00:00
-- url     : https://prove2.me/submissions/f5a60e3a-8f4e-4465-b070-4171228f7ac5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/RobustDirections.lean:L23-L95
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_robust_directions_of_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Theorems.Thm_OAI_MetricEntropyDuality_DirectionDeletion_exists_good_subset
import Theorems.Thm_OAI_MetricEntropyDuality_DirectionSampling_prob_badSamples_le
import Theorems.Thm_OAI_MetricEntropyDuality_coeff_diagonalPolynomial
import Theorems.Thm_OAI_MetricEntropyDuality_polynomial_zero_card_mul_le
import Theorems.Thm_OAI_MetricEntropyDuality_symFiberCard_dvd_factorial
import Theorems.Thm_OAI_MetricEntropyDuality_totalDegree_tuplePolynomial_le

-- ---- from OAI.Analysis.MetricEntropy.FormDimension ----
namespace OAI

universe uK

/-!
# Dimension of symmetric-form coefficients

The coefficients of a symmetric `j`-linear form on an `r`-dimensional space
are indexed by multisets of `j` basis vectors. Their number gives the
dimension of the coefficient space and hence its cardinality over a finite field.
-/

namespace MetricEntropyDuality

/-- Positive ambient dimension gives a nonempty coefficient index set. -/
theorem formDimension_pos {r j : ℕ} (hr : 0 < r) : 0 < formDimension r j := by
  exact Nat.choose_pos (Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_left hr))

/-- Stars and bars counts the actual multiset coefficient indices. -/
theorem card_sym_fin (r j : ℕ) :
    Fintype.card (Sym (Fin r) j) = formDimension r j := by
  simpa only [Fintype.card_fin, formDimension] using
    (Sym.card_sym_eq_choose (α := Fin r) j)

/-- A coefficient function over `ZMod p` has exactly `p` choices at each index. -/
theorem card_form_coefficients (p r j : ℕ) [NeZero p] :
    Fintype.card (Sym (Fin r) j → ZMod p) = p ^ formDimension r j := by
  classical
  rw [Fintype.card_fun, ZMod.card, card_sym_fin]

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.DirectionSampling ----
namespace OAI

universe uU uE uJ uZ

/-!
# Counting and avoiding all disjoint zero-tuple witnesses

All ordered tuples are retained, including tuples with repeated indices.
The probability product estimate is applied only to lists whose distinct
tuple supports are pairwise disjoint. Their number is bounded by the exact
number of all ordered lists, `u ^ (h * w)`.
-/

noncomputable section

open scoped BigOperators

namespace MetricEntropyDuality.DirectionSampling

open FiniteProductCounting

section FiniteUnion

variable {U : Type uU} {E : Type uE} {J : Type uJ} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E]

/-- Strictly fewer than all samples in an event leaves an actual sample
outside it. Nonempty `E` also covers an empty coordinate index type. -/
theorem exists_not_mem_of_prob_lt_one (event : Finset (U → E))
    (hevent : prob event < 1) : ∃ t : U → E, t ∉ event := by
  classical
  by_contra hnone
  have hall : ∀ t : U → E, t ∈ event := by simpa only [not_exists, not_not] using hnone
  have heq : event = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [heq, prob_univ] at hevent
  exact (lt_irrefl (1 : ℝ)) hevent

end FiniteUnion

section Tuples

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E] {h w : ℕ}

end Tuples

section Sampling

variable {Z : Type uZ} {E : Type uE} [Fintype E] [DecidableEq E] [Nonempty E]
  {u h w : ℕ}

/-- The numerical bound used for degree-`h` forms over a field of `p`
elements. Form counts and each repeated-tuple zero bound are explicit
inputs, supplied by the actual form and polynomial constructions. -/
theorem prob_badSamples_le_field_budget (forms : Finset Z)
    (bad : Z → (Fin h → E) → Prop) (p D : ℕ) (hcard : forms.card ≤ p ^ D)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u,
      prob (tupleEvent (bad z) a) ≤ (h : ℝ) / p) :
    prob (badSamples (u := u) (w := w) forms bad) ≤
      (p : ℝ) ^ D * (u : ℝ) ^ (h * w) * ((h : ℝ) / p) ^ w := by
  have hb : 0 ≤ (h : ℝ) / p := div_nonneg (Nat.cast_nonneg h) (Nat.cast_nonneg p)
  have hc : (forms.card : ℝ) ≤ (p : ℝ) ^ D := by exact_mod_cast hcard
  exact (prob_badSamples_le forms bad ((h : ℝ) / p) hb hbound).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (pow_nonneg (Nat.cast_nonneg u) _))
      (pow_nonneg hb _))

theorem exists_sample_avoiding_of_field_budget (forms : Finset Z)
    (bad : Z → (Fin h → E) → Prop) (p D : ℕ) (hcard : forms.card ≤ p ^ D)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u,
      prob (tupleEvent (bad z) a) ≤ (h : ℝ) / p)
    (hbudget : (p : ℝ) ^ D * (u : ℝ) ^ (h * w) * ((h : ℝ) / p) ^ w < 1) :
    ∃ t : Fin u → E, ∀ z ∈ forms, ∀ L : Fin w → Fin h → Fin u,
      DisjointSupports L → ¬ ∀ j, bad z (fun i => t (L j i)) := by
  classical
  obtain ⟨t, ht⟩ := exists_not_mem_of_prob_lt_one (badSamples (u := u) (w := w) forms bad)
    ((prob_badSamples_le_field_budget forms bad p D hcard hbound).trans_lt hbudget)
  refine ⟨t, ?_⟩
  intro z hz L hL hall
  exact ht (mem_badSamples.mpr ⟨z, hz, L, hL, hall⟩)

end Sampling

end MetricEntropyDuality.DirectionSampling

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.SymmetricMultiplicity ----
namespace OAI

/-!
# Multiplicities of symmetric indices

The tuples representing a fixed multiset form a permutation orbit. Its size is
positive and divides the factorial of the number of slots. Consequently the
coefficient multiplicity cannot vanish modulo a prime larger than that number.
-/

namespace MetricEntropyDuality

/-- No prime larger than the tuple length divides its multiplicity. -/
theorem not_dvd_symFiberCard {r j p : ℕ} (s : Sym (Fin r) j)
    (hp : p.Prime) (hjp : j < p) : ¬ p ∣ symFiberCard s := by
  intro h
  exact (Nat.not_le_of_lt hjp) (hp.dvd_factorial.mp (h.trans (symFiberCard_dvd_factorial s)))

/-- The diagonal coefficient multiplicity is nonzero in the required field. -/
theorem symFiberCard_cast_ne_zero {r j p : ℕ} (s : Sym (Fin r) j)
    (hp : p.Prime) (hjp : j < p) : (symFiberCard s : ZMod p) ≠ 0 := by
  intro h
  exact not_dvd_symFiberCard s hp hjp ((ZMod.natCast_eq_zero_iff _ _).mp h)

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.FormPolynomials ----
namespace OAI

universe uK

/-!
# Actual polynomials of symmetric forms

The definitions sum over ordered basis tuples, exactly as the multilinear
form evaluation does. The diagonal coefficient of a basis multiset is its
ordered-tuple fiber cardinality times the value of the form. This coefficient
is nonzero in characteristic greater than the degree. Renaming every vector
block to the same coordinate proves nonvanishing for every index tuple,
including tuples with repeated indices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators
open MvPolynomial

theorem eval_tuplePolynomial {K : Type uK} [CommSemiring K] {r h u : ℕ}
    (F : SymmetricForm K r h) (a : Fin h → Fin u) (t : Fin u → Fin r → K) :
    MvPolynomial.eval (fun z => t z.1 z.2) (tuplePolynomial F a) =
      SymmetricForm.eval F (fun j => t (a j)) := by
  simp [tuplePolynomial, SymmetricForm.eval, eval_mul]

/-- Identifying all blocks with one vector gives the diagonal polynomial. -/
theorem rename_tuplePolynomial {K : Type uK} [CommSemiring K] {r h u : ℕ}
    (F : SymmetricForm K r h) (a : Fin h → Fin u) :
    MvPolynomial.rename Prod.snd (tuplePolynomial F a) = diagonalPolynomial F := by
  simp [tuplePolynomial, diagonalPolynomial, map_sum, map_prod]

/-- Characteristic greater than the degree prevents diagonal cancellation. -/
theorem diagonalPolynomial_ne_zero {p r h : ℕ} [Fact p.Prime]
    (hp : h < p) (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0) :
    diagonalPolynomial F ≠ 0 := by
  intro hz
  apply hF
  funext s
  have hc := congrArg (fun polynomial => polynomial.coeff (symExponent s)) hz
  simp only [coeff_diagonalPolynomial, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_left (symFiberCard_cast_ne_zero s (Fact.out : p.Prime) hp)

/-- Every symbolic tuple evaluation is nonzero, with no distinct-index
hypothesis. The proof includes all repeated-index patterns. -/
theorem tuplePolynomial_ne_zero {p r h u : ℕ} [Fact p.Prime]
    (hp : h < p) (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) : tuplePolynomial F a ≠ 0 := by
  intro hz
  apply diagonalPolynomial_ne_zero hp F hF
  rw [← rename_tuplePolynomial F a, hz, map_zero]

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.PolynomialZeroBound ----
namespace OAI

universe uV

/-!
# Polynomial zero counts over a finite prime field

The sample space contains every assignment of the finite variable set. In
particular, using a product variable type imposes no restriction on repeated
vector indices. The exact counting bound is obtained from the
Schwartz–Zippel theorem by renaming variables and clearing positive denominators.
-/

noncomputable section

namespace MetricEntropyDuality

variable {p : ℕ} [Fact p.Prime]

/-- A supplied upper bound for total degree gives the same exact zero count. -/
theorem polynomial_zero_card_mul_le_of_totalDegree_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) :
    p * (polynomialZeros P).card ≤ d * p ^ Fintype.card V :=
  (polynomial_zero_card_mul_le P hP).trans (Nat.mul_le_mul_right _ hdeg)

/-- The number of zeros is at most `d/p` times the number of assignments. -/
theorem polynomial_zero_card_real_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) :
    ((polynomialZeros P).card : ℝ) ≤
      (d : ℝ) / p * ((p ^ Fintype.card V : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcross : (p : ℝ) * (polynomialZeros P).card ≤
      (d : ℝ) * ((p ^ Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast polynomial_zero_card_mul_le_of_totalDegree_le P hP hdeg
  calc
    ((polynomialZeros P).card : ℝ) ≤
        ((d : ℝ) * ((p ^ Fintype.card V : ℕ) : ℝ)) / p :=
      (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hcross)
    _ = (d : ℝ) / p * ((p ^ Fintype.card V : ℕ) : ℝ) := by ring

/-- The exact fraction of assignments on which the polynomial vanishes is
at most `d/p`; this is the uniform-product probability formulation. -/
theorem polynomial_zero_proportion_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) {d : ℕ}
    (hdeg : P.totalDegree ≤ d) :
    ((polynomialZeros P).card : ℝ) / ((p ^ Fintype.card V : ℕ) : ℝ) ≤
      (d : ℝ) / p := by
  have htotal : (0 : ℝ) < ((p ^ Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos (Fintype.card V)
  exact (div_le_iff₀ htotal).2 (polynomial_zero_card_real_le P hP hdeg)

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.FormZeroCount ----
namespace OAI

/-!
# Actual repeated-tuple zero events

The finite sample is a family of vectors. Currying identifies it with the
scalar assignments of the literal tuple polynomial. No injectivity or
nonzero-coordinate assumption is made on the sampled vectors or tuple indices.
-/

noncomputable section

namespace MetricEntropyDuality

variable {p r h u : ℕ} [Fact p.Prime]

/-- The original vector-sample event has exactly the polynomial zero count. -/
theorem tupleEvent_form_zero_card (F : SymmetricForm (ZMod p) r h)
    (a : Fin h → Fin u) :
    (tupleEvent (fun v => SymmetricForm.eval F v = 0) a).card =
      (polynomialZeros (tuplePolynomial F a)).card := by
  classical
  apply Finset.card_equiv (Equiv.curry (Fin u) (Fin r) (ZMod p)).symm
  intro t
  simp only [mem_tupleEvent, mem_polynomialZeros]
  change SymmetricForm.eval F (fun j => t (a j)) = 0 ↔
    MvPolynomial.eval (fun z => t z.1 z.2) (tuplePolynomial F a) = 0
  rw [eval_tuplePolynomial]

/-- The literal number of samples is the number of scalar assignments. -/
theorem card_direction_samples :
    Fintype.card (Fin u → Fin r → ZMod p) =
      p ^ Fintype.card (Fin u × Fin r) := by
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Fintype.card_prod]
  rw [← pow_mul, Nat.mul_comm r u]

/-- Uniform probability of a zero evaluation is at most `h/p`, with repetitions
allowed in `a`. The denominator is the full finite vector-sample cardinality. -/
theorem tupleEvent_form_zero_proportion_le (hp : h < p)
    (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) :
    ((tupleEvent (fun v => SymmetricForm.eval F v = 0) a).card : ℝ) /
      (Fintype.card (Fin u → Fin r → ZMod p) : ℝ) ≤ (h : ℝ) / p := by
  rw [tupleEvent_form_zero_card, card_direction_samples]
  exact polynomial_zero_proportion_le (tuplePolynomial F a)
    (tuplePolynomial_ne_zero hp F hF a) (totalDegree_tuplePolynomial_le F a)

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.DirectionBudget ----
namespace OAI

/-!
# The numerical budget for robust directions

The scalar expression in the finite union bound is strictly below one
for a sufficiently large prime chosen after the other finite parameters.
-/

namespace MetricEntropyDuality

/-- The union-bound expression after substituting `w = 2 * D`. -/
theorem direction_bad_event_bound_eq (D h : ℕ) (u p : ℝ) (hp : p ≠ 0) :
    p ^ D * u ^ (h * (2 * D)) * ((h : ℝ) / p) ^ (2 * D) =
      (((h : ℝ) ^ 2 * u ^ (2 * h)) / p) ^ D := by
  have hexp : h * (2 * D) = (2 * h) * D := by ring
  have hbase : p * u ^ (2 * h) * ((h : ℝ) / p) ^ 2 =
      ((h : ℝ) ^ 2 * u ^ (2 * h)) / p := by
    field_simp [hp]
  calc
    p ^ D * u ^ (h * (2 * D)) * ((h : ℝ) / p) ^ (2 * D) =
        (p * u ^ (2 * h) * ((h : ℝ) / p) ^ 2) ^ D := by
      rw [hexp, pow_mul u (2 * h) D, pow_mul ((h : ℝ) / p) 2 D,
        mul_pow, mul_pow]
    _ = (((h : ℝ) ^ 2 * u ^ (2 * h)) / p) ^ D := by rw [hbase]

/-- The last-prime threshold makes the actual counting bound strictly less
than one. No positivity of `h` or `u` is needed for this scalar implication. -/
theorem direction_bad_event_bound_lt_one {D h u p : ℕ} (hD : 0 < D)
    (hp : h ^ 2 * u ^ (2 * h) < p) :
    (p : ℝ) ^ D * (u : ℝ) ^ (h * (2 * D)) *
        ((h : ℝ) / p) ^ (2 * D) < 1 := by
  have hp₀ : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le (h ^ 2 * u ^ (2 * h))) hp)
  rw [direction_bad_event_bound_eq D h (u : ℝ) (p : ℝ) (ne_of_gt hp₀)]
  apply pow_lt_one₀ (by positivity) _ (Nat.ne_of_gt hD)
  apply (div_lt_one hp₀).mpr
  exact_mod_cast hp

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.RobustDirections ----
namespace OAI

/-!
# Actual directions surviving deletion

The sample is the full finite product of indexed vectors over `ZMod p`.
The actual symmetric-form count and the zero bound for every repeated-index
tuple feed the disjoint-witness union bound. A finite maximum disjoint family
then produces the surviving set separately for each nonzero form.
-/

noncomputable section

namespace MetricEntropyDuality

/-- The actual finite-field direction construction with an explicit deletion
budget. One sample works for every nonzero form; its surviving subset may
depend on that form. All ordered tuples, including repetitions, are retained. -/
theorem exists_robust_directions_of_budget
    {p r h u : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hh : 0 < h) (hu : 0 < u)
    {θ : ℝ} (hθ : θ < 1)
    (hdel : (h : ℝ) * (2 * (formDimension r h : ℝ)) ≤ θ * (u : ℝ))
    (hp_h : h < p) (hp_size : h ^ 2 * u ^ (2 * h) < p) :
    ∃ t : Fin u → Fin r → ZMod p,
      ∀ F : SymmetricForm (ZMod p) r h, F ≠ 0 →
        ∃ T : Finset (Fin u),
          ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧ T.Nonempty ∧
          ∀ a : Fin h → Fin u, (∀ j, a j ∈ T) →
            SymmetricForm.eval F (fun j => t (a j)) ≠ 0 := by
  classical
  let forms : Finset (SymmetricForm (ZMod p) r h) :=
    Finset.univ.filter (fun F => F ≠ 0)
  have hcard : forms.card ≤ p ^ formDimension r h := by
    calc
      forms.card ≤ Fintype.card (SymmetricForm (ZMod p) r h) :=
        Finset.card_le_univ forms
      _ = p ^ formDimension r h := card_form_coefficients p r h
  have hbound : ∀ F ∈ forms, ∀ a : Fin h → Fin u,
      FiniteProductCounting.prob
        (tupleEvent (fun v => SymmetricForm.eval F v = 0) a) ≤ (h : ℝ) / p := by
    intro F hF a
    have hFne : F ≠ 0 := (Finset.mem_filter.mp hF).2
    exact tupleEvent_form_zero_proportion_le hp_h F hFne a
  have hbudget :
      (p : ℝ) ^ formDimension r h * (u : ℝ) ^ (h * (2 * formDimension r h)) *
        ((h : ℝ) / p) ^ (2 * formDimension r h) < 1 :=
    direction_bad_event_bound_lt_one (formDimension_pos hr) hp_size
  obtain ⟨t, ht⟩ := DirectionSampling.exists_sample_avoiding_of_field_budget
    (u := u) (h := h) (w := 2 * formDimension r h)
    forms (fun F v => SymmetricForm.eval F v = 0)
    p (formDimension r h) hcard hbound hbudget
  refine ⟨t, ?_⟩
  intro F hF
  have hFmem : F ∈ forms := Finset.mem_filter.mpr ⟨Finset.mem_univ F, hF⟩
  have hno : ¬ ∃ L : Fin (2 * formDimension r h) → Fin h → Fin u,
      (∀ i, SymmetricForm.eval F (fun j => t (L i j)) = 0) ∧
        DisjointSupports L := by
    rintro ⟨L, hzero, hdisj⟩
    exact ht F hFmem L hdisj hzero
  obtain ⟨T, hTcard, hTgood⟩ := DirectionDeletion.exists_good_subset
    (fun a : Fin h → Fin u => SymmetricForm.eval F (fun j => t (a j)) = 0)
    hh hno
  have hTcardNat : u - T.card ≤ h * (2 * formDimension r h - 1) := by
    simpa only [Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin] using hTcard
  have hTbound : ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
    calc
      ((Finset.univ \ T).card : ℝ) ≤
          ((h * (2 * formDimension r h - 1) : ℕ) : ℝ) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ T),
          Finset.card_univ, Fintype.card_fin]
        exact_mod_cast hTcardNat
      _ ≤ ((h * (2 * formDimension r h) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left h (Nat.sub_le (2 * formDimension r h) 1)
      _ = (h : ℝ) * (2 * (formDimension r h : ℝ)) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ θ * (u : ℝ) := hdel
  have hTnonempty : T.Nonempty := by
    apply Classical.byContradiction
    intro hTempty
    have hTzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTempty
    have hbad : (u : ℝ) ≤ θ * (u : ℝ) := by simpa [hTzero] using hTbound
    have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
    have hstrict : θ * (u : ℝ) < (u : ℝ) := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hθ huR
    exact (not_le_of_gt hstrict) hbad
  exact ⟨T, hTbound, hTnonempty, hTgood⟩

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.exists_robust_directions_of_budget := @_root_.OAI.MetricEntropyDuality.exists_robust_directions_of_budget
