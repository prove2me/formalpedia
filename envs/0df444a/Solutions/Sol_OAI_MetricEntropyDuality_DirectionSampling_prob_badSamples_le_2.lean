-- Prove2me | solution 2 for OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:51:26.58696+00:00
-- url     : https://prove2.me/submissions/9af9fe5f-129e-48dd-a625-fb1d19d33236

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/DirectionSampling.lean:L142-L171
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_FiniteProductCounting_prob_allEvents_eq_prod

-- ---- from OAI.Analysis.MetricEntropy.FiniteProductCounting ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

universe uU uE uJ

/-!
# Counting events on disjoint sets of coordinates

The sample space is the actual finite function space `U → E`, with uniform
probability given by cardinality divided by the cardinality of that space.
A coordinate-swap bijection proves independence of two events from their
literal disjoint supports. Finite intersections then follow by induction.
No independence hypothesis or distinctness within an individual tuple is used.
-/

namespace MetricEntropyDuality.FiniteProductCounting

open scoped BigOperators

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem prob_nonneg (A : Finset (U → E)) : 0 ≤ prob A :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

section NonemptyAlphabet

variable [Nonempty E]

end NonemptyAlphabet

section FiniteIntersection

variable [Nonempty E]

theorem prob_all_univ_eq_prod {w : ℕ} (S : Fin w → Finset U)
    (A : Fin w → Finset (U → E))
    (hdep : ∀ j, DependsOn (S j) (A j))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j)) :
    prob (allEvents Finset.univ A) = ∏ j, prob (A j) :=
  prob_allEvents_eq_prod Finset.univ S A (fun j _ => hdep j)
    (fun _ _ _ _ hij => hdisj hij)

/-- The repeated-event bound follows from the proved finite product identity. -/
theorem prob_all_univ_le_pow {w : ℕ} (S : Fin w → Finset U)
    (A : Fin w → Finset (U → E))
    (hdep : ∀ j, DependsOn (S j) (A j))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (b : ℝ) (hbound : ∀ j, prob (A j) ≤ b) :
    prob (allEvents Finset.univ A) ≤ b ^ w := by
  rw [prob_all_univ_eq_prod S A hdep hdisj]
  calc
    (∏ j, prob (A j)) ≤ ∏ _j : Fin w, b :=
      Finset.prod_le_prod₀ (fun index _ => prob_nonneg (A index))
        (fun index _ => hbound index)
    _ = b ^ w := by simp

end FiniteIntersection

end MetricEntropyDuality.FiniteProductCounting

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

omit [Nonempty E] in
/-- The union bound for the actual normalized finite sample counts. -/
theorem prob_biUnion_le (s : Finset J) (events : J → Finset (U → E)) :
    prob (s.biUnion events) ≤ ∑ j ∈ s, prob (events j) := by
  classical
  unfold prob
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hcard : (s.biUnion events).card ≤ ∑ j ∈ s, (events j).card :=
    Finset.card_biUnion_le
  exact_mod_cast hcard

end FiniteUnion

section Tuples

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E] {h w : ℕ}

omit [DecidableEq U] [DecidableEq E] [Nonempty E] in
/-- A repeated-index tuple event depends only on the distinct indices in
its literal support. -/
theorem tupleEvent_dependsOn (bad : (Fin h → E) → Prop) (a : Fin h → U) :
    DependsOn (tupleSupport a) (tupleEvent bad a) := by
  intro t s hts
  have heq : (fun j => t (a j)) = (fun j => s (a j)) := by
    funext j
    exact hts (a j) (mem_tupleSupport.mpr ⟨j, rfl⟩)
  simp only [mem_tupleEvent, heq]

/-- Product estimate proved from disjoint coordinate supports; no
independence hypothesis is assumed. -/
theorem prob_badListEvent_le (bad : (Fin h → E) → Prop)
    (L : Fin w → Fin h → U) (hL : DisjointSupports L) (b : ℝ)
    (hbound : ∀ a : Fin h → U, prob (tupleEvent bad a) ≤ b) :
    prob (badListEvent bad L) ≤ b ^ w :=
  prob_all_univ_le_pow (fun j => tupleSupport (L j))
    (fun j => tupleEvent bad (L j)) (fun j => tupleEvent_dependsOn bad (L j))
    hL b (fun j => hbound (L j))

end Tuples

/-- All ordered witness lists, before imposing disjointness, are counted
exactly. Repetition within any tuple remains allowed. -/
theorem card_witnessLists (u h w : ℕ) :
    Fintype.card (Fin w → Fin h → Fin u) = u ^ (h * w) := by
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul]

theorem card_disjointLists_le (u h w : ℕ) :
    (disjointLists u h w).card ≤ u ^ (h * w) := by
  classical
  calc
    (disjointLists u h w).card ≤ Fintype.card (Fin w → Fin h → Fin u) :=
      Finset.card_le_univ _
    _ = u ^ (h * w) := card_witnessLists u h w

section Sampling

variable {Z : Type uZ} {E : Type uE} [Fintype E] [DecidableEq E] [Nonempty E]
  {u h w : ℕ}

/-- The counted union bound over the literal form set and every possible
disjoint witness list. -/
theorem prob_badSamples_le (forms : Finset Z) (bad : Z → (Fin h → E) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u, prob (tupleEvent (bad z) a) ≤ b) :
    prob (badSamples (u := u) (w := w) forms bad) ≤
      (forms.card : ℝ) * (u : ℝ) ^ (h * w) * b ^ w := by
  classical
  have hlistcard : ((disjointLists u h w).card : ℝ) ≤ (u : ℝ) ^ (h * w) := by
    exact_mod_cast card_disjointLists_le u h w
  have hinner (z : Z) (hz : z ∈ forms) :
      prob ((disjointLists u h w).biUnion fun L => badListEvent (bad z) L) ≤
        (u : ℝ) ^ (h * w) * b ^ w := by
    calc
      _ ≤ ∑ L ∈ disjointLists u h w, prob (badListEvent (bad z) L) :=
        prob_biUnion_le _ _
      _ ≤ ∑ _L ∈ disjointLists u h w, b ^ w := by
        apply Finset.sum_le_sum
        intro L hL
        exact prob_badListEvent_le (bad z) L (mem_disjointLists.mp hL) b (hbound z hz)
      _ = ((disjointLists u h w).card : ℝ) * b ^ w := by simp
      _ ≤ (u : ℝ) ^ (h * w) * b ^ w :=
        mul_le_mul_of_nonneg_right hlistcard (pow_nonneg hb w)
  calc
    _ ≤ ∑ z ∈ forms,
        prob ((disjointLists u h w).biUnion fun L => badListEvent (bad z) L) :=
      prob_biUnion_le _ _
    _ ≤ ∑ _z ∈ forms, (u : ℝ) ^ (h * w) * b ^ w :=
      Finset.sum_le_sum hinner
    _ = _ := by simp [mul_assoc]

end Sampling

end MetricEntropyDuality.DirectionSampling

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.DirectionSampling
open scoped BigOperators
open FiniteProductCounting


theorem solution.{uE,uZ} : type_of% @_root_.OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le.{uE,uZ} := @_root_.OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le.{uE,uZ}
