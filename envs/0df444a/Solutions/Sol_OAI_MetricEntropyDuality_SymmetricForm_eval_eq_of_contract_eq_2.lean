-- Prove2me | solution 2 for OAI.MetricEntropyDuality.SymmetricForm.eval_eq_of_contract_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:59:57.869478+00:00
-- url     : https://prove2.me/submissions/7f8a2f87-6bd8-464e-99d0-5230ad104f21

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FieldGraphSeparation.lean:L30-L48
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.SymmetricForm.eval_eq_of_contract_eq. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_SymmetricForm_eval_basis
import Theorems.Thm_OAI_MetricEntropyDuality_SymmetricForm_eval_contract

-- ---- from OAI.Analysis.MetricEntropy.SymmetricForms ----
namespace OAI

universe uK

/-!
# Literal coefficients and actual symmetric multilinear forms

A coefficient is assigned freely to every multiset of basis indices, including
repetitions. Summing over ordered tuples gives an actual multilinear map. Basis
evaluation recovers every coefficient, and every permutation-invariant
multilinear map arises this way. The degree-zero case is included.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

/-- Permuting the argument slots does not change the actual multilinear map. -/
theorem toMultilinearMap_domDomCongr (F : SymmetricForm K r j)
    (σ : Equiv.Perm (Fin j)) :
    (toMultilinearMap F).domDomCongr σ = toMultilinearMap F := by
  apply Module.Basis.ext_multilinear (fun _ : Fin j => Pi.basisFun K (Fin r))
  intro a
  simp only [MultilinearMap.domDomCongr_apply, Pi.basisFun_apply,
    toMultilinearMap_apply]
  change eval F (fun i => Pi.single ((a ∘ σ) i) (1 : K)) =
    eval F (fun i => Pi.single (a i) (1 : K))
  rw [eval_basis, eval_basis, tupleSym_comp_perm]

/-- The evaluation is invariant under every permutation, including repeated
vectors and the zero-degree tuple. -/
theorem eval_comp_perm (F : SymmetricForm K r j)
    (v : Fin j → (Fin r → K)) (σ : Equiv.Perm (Fin j)) :
    eval F (v ∘ σ) = eval F v := by
  have h := congrArg
    (fun f : MultilinearMap K (fun _ : Fin j => Fin r → K) K => f v)
    (toMultilinearMap_domDomCongr F σ)
  simpa only [MultilinearMap.domDomCongr_apply, toMultilinearMap_apply,
    Function.comp_def] using h

section Ring

variable {K : Type uK} [CommRing K] {r j : ℕ}

end Ring

end SymmetricForm

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.FieldGraphSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uι uα uV uA

/-!
# Actual contraction labels obstruct short walks

One label is chosen for each edge of a hypothetical short walk. These labels
are padded to the full degree using one fixed member of the same set of
directions. Symmetry moves each edge's direction to the contracted slot, so
evaluation on this single tuple is constant along the walk. This contradicts
robust nonvanishing of the difference of its endpoints.
-/

noncomputable section

namespace MetricEntropyDuality

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

/-- Equal contractions imply equal evaluations whenever the contracted vector
occurs in any slot. Repeated arguments are allowed. -/
theorem eval_eq_of_contract_eq (v : Fin r → K)
    (F G : SymmetricForm K r (j + 1))
    (hFG : contract v F = contract v G)
    (args : Fin (j + 1) → (Fin r → K)) (a : Fin (j + 1)) (ha : args a = v) :
    F.eval args = G.eval args := by
  classical
  let σ : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 a
  have hz : (args ∘ σ) 0 = v := by simp [σ, Function.comp_apply, ha]
  have hc : Fin.cons v (Fin.tail (args ∘ σ)) = args ∘ σ := by
    rw [← hz]
    exact Fin.cons_self_tail (args ∘ σ)
  calc
    F.eval args = F.eval (args ∘ σ) := (eval_comp_perm F args σ).symm
    _ = (contract v F).eval (Fin.tail (args ∘ σ)) := by rw [eval_contract, hc]
    _ = (contract v G).eval (Fin.tail (args ∘ σ)) := by rw [hFG]
    _ = G.eval (args ∘ σ) := by rw [eval_contract, hc]
    _ = G.eval args := eval_comp_perm G args σ

end SymmetricForm

namespace FieldGraphSeparation

variable {K : Type uK} {ι : Type uι} [CommRing K] {r j : ℕ}

end FieldGraphSeparation
end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.SymmetricForm


theorem solution.{uK} : type_of% @_root_.OAI.MetricEntropyDuality.SymmetricForm.eval_eq_of_contract_eq.{uK} := @_root_.OAI.MetricEntropyDuality.SymmetricForm.eval_eq_of_contract_eq.{uK}
