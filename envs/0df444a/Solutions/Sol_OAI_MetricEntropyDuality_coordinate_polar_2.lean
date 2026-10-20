-- Prove2me | solution 2 for OAI.MetricEntropyDuality.coordinate_polar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:45:07.712728+00:00
-- url     : https://prove2.me/submissions/a7d3710e-e5ff-45e6-afa8-bc4dfb67a608

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CoordinateTransport.lean:L170-L187
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.coordinate_polar. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.CoordinateTransport ----
namespace OAI

universe uι uκ

/-!
# Relabelling finite real coordinates

The coordinate map is a linear homeomorphism of the full ambient spaces.
It transports all translation centers, rather than restricting them to the
body being covered. Consequently equality of covering numbers follows from
equality of the sets of admissible natural cover counts.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {κ : Type uκ}

section FiniteCoordinates

variable [Fintype ι] [Fintype κ]

theorem pairing_coordinateEquiv (e : ι ≃ κ) (x y : RealSpace ι) :
    pairing (coordinateEquiv e x) (coordinateEquiv e y) = pairing x y := by
  unfold pairing
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- Coordinate permutations preserve the literal pairing polar, with both
the body and its dual coordinates transported by the same map. -/
theorem coordinate_polar (e : ι ≃ κ) (K : Set (RealSpace ι)) :
    coordinateEquiv e '' polar K = polar (coordinateEquiv e '' K) := by
  ext y
  rw [mem_coordinate_image_iff]
  constructor
  · intro hy z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hp := pairing_coordinateEquiv e x ((coordinateEquiv e).symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hp
    rw [hp]
    exact hy x hx
  · intro hy x hx
    have hh := hy (coordinateEquiv e x) ⟨x, hx, rfl⟩
    have hp := pairing_coordinateEquiv e x ((coordinateEquiv e).symm y)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hp
    rwa [hp] at hh

end FiniteCoordinates

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators Pointwise


theorem solution.{uι,uκ} : type_of% @_root_.OAI.MetricEntropyDuality.coordinate_polar.{uι,uκ} := @_root_.OAI.MetricEntropyDuality.coordinate_polar.{uι,uκ}
