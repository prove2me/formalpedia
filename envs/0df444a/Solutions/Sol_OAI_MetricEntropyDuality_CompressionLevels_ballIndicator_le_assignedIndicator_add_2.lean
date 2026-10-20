-- Prove2me | solution 2 for OAI.MetricEntropyDuality.CompressionLevels.ballIndicator_le_assignedIndicator_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:13:20.735456+00:00
-- url     : https://prove2.me/submissions/835414c9-2473-47b4-a5a9-d86369d1bf81

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CompressionLevels.lean:L59-L85
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.CompressionLevels.ballIndicator_le_assignedIndicator_add. The node keeps its source
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
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels

-- ---- from OAI.Analysis.MetricEntropy.PartitionGraph ----
namespace OAI

universe uX uι uLabel

/-!
# Partition graphs and their extended distances

An edge records equality of one selected label. Distances take values in `ℕ∞`,
so vertices in different connected components have infinite distance. The
pivot comparison and finite-walk characterization control the paths
between vertices with common labels.
-/

noncomputable section

namespace MetricEntropyDuality.PartitionGraph

variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}
variable (L : (i : ι) → X → Label i) (T : Finset ι)

theorem distance_comm (x y : X) : distance L T x y = distance L T y x :=
  SimpleGraph.edist_comm

theorem distance_triangle (x y z : X) :
    distance L T x z ≤ distance L T x y + distance L T y z :=
  SimpleGraph.edist_triangle

theorem near_symm {k : ℕ} {x y : X} (h : near L T k x y) :
    near L T k y x := by
  change distance L T y x ≤ (k : ℕ∞)
  rw [distance_comm L T y x]
  exact h

theorem near_triangle {j k : ℕ} {x y z : X}
    (hxy : near L T j x y) (hyz : near L T k y z) :
    near L T (j + k) x z := by
  change distance L T x z ≤ ((j + k : ℕ) : ℕ∞)
  simpa only [Nat.cast_add] using
    (distance_triangle L T x y z).trans (add_le_add hxy hyz)

/-- A label match gives distance at most one, including coincident vertices. -/
theorem distance_le_one_of_label_eq {i : ι} {x y : X}
    (hi : i ∈ T) (heq : L i x = L i y) : distance L T x y ≤ 1 := by
  by_cases hxy : x = y
  · subst y
    simp
  · have hadj : (graph L T).Adj x y := ⟨hxy, i, hi, heq⟩
    exact (SimpleGraph.edist_eq_one_iff_adj.mpr hadj).le

theorem near_one_of_label_eq {i : ι} {x y : X}
    (hi : i ∈ T) (heq : L i x = L i y) : near L T 1 x y :=
  distance_le_one_of_label_eq L T hi heq

/-- Replacing a pivot by a vertex with the same selected label costs one step. -/
theorem pivot_replacement {i : ι} {j : ℕ} {v z z' : X}
    (hi : i ∈ T) (heq : L i z' = L i z) (hvz : near L T j v z) :
    near L T (j + 1) v z' :=
  near_triangle L T hvz (near_one_of_label_eq L T hi heq.symm)

theorem pivot_forward {i : ι} {j : ℕ} {v z z' x : X}
    (hi : i ∈ T) (heq : L i z' = L i z) (hvz : near L T j v z)
    (hxv : near L T j x v) : near L T (2 * j + 1) x z' := by
  have h := near_triangle L T hxv (pivot_replacement L T hi heq hvz)
  simpa only [two_mul, add_assoc] using h

end MetricEntropyDuality.PartitionGraph

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.CompressionLevels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uX uY uK uι uLabel

/-!
# Graph-ball comparison at one compression level

Columns omitted by the common index and retained columns left uncovered
each contribute at most `θ`. Assigned columns are compared using the actual
partition graph and replacement pivots with the same selected label.
Graph distances remain extended distances throughout.
-/

noncomputable section

namespace MetricEntropyDuality.CompressionLevels

open scoped BigOperators Classical

variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}

theorem ballIndicator_nonneg (L : (i : ι) → X → Label i) (T : Finset ι)
    (j : ℕ) (x v : X) : 0 ≤ ballIndicator L T j x v := by
  unfold ballIndicator
  split_ifs <;> simp

theorem assignedIndicator_nonneg (L : (i : ι) → X → Label i) (T : Y → Finset ι)
    (rep : K → X) (assignment : Y → Option K) (j : ℕ) (x : X) (y : Y) :
    0 ≤ assignedIndicator L T rep assignment j x y := by
  unfold assignedIndicator
  cases assignment y with
  | none => exact le_rfl
  | some k => exact ballIndicator_nonneg _ _ _ _ _

/-- Pointwise accounting for assigned, omitted, and uncovered columns. -/
theorem ballIndicator_le_assignedIndicator_add
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (i : ι) (j : ℕ) (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) (y : Y) :
    ballIndicator L (T y) j x (v y) ≤
      assignedIndicator L T rep assignment j x y +
        (if i ∉ T y then 1 else 0) +
        (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by
  have ha := assignedIndicator_nonneg L T rep assignment j x y
  by_cases hx : PartitionGraph.near L (T y) j x (v y)
  · by_cases hi : i ∈ T y
    · cases hass : assignment y with
      | none => simp [ballIndicator, assignedIndicator, hx, hi, hass]
      | some k =>
          have hk := hassign y k hass
          have hf := PartitionGraph.pivot_forward L (T y) hk.1 (hrep k)
            (PartitionGraph.near_symm L (T y) hk.2) hx
          simp [ballIndicator, assignedIndicator, hx, hi, hass, hf]
    · simp only [ballIndicator, ite_eq_left hx, hi, not_false_eq_true, ite_true,
        false_and, ite_false]
      linarith
  · simp only [ballIndicator, hx, and_false, false_and, ite_false]
    split_ifs <;> linarith

section Weighted

variable [Fintype Y]

end Weighted

end MetricEntropyDuality.CompressionLevels

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.CompressionLevels
open scoped BigOperators Classical


theorem solution.{uX,uY,uK,uι,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.CompressionLevels.ballIndicator_le_assignedIndicator_add.{uX,uY,uK,uι,uLabel} := @_root_.OAI.MetricEntropyDuality.CompressionLevels.ballIndicator_le_assignedIndicator_add.{uX,uY,uK,uι,uLabel}
