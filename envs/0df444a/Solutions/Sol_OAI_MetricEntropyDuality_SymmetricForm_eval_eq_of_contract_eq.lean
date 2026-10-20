-- Prove2me | solution 1 for OAI.MetricEntropyDuality.SymmetricForm.eval_eq_of_contract_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:53:15.161894+00:00
-- url     : https://prove2.me/submissions/620c3c59-7da2-4eb3-8334-ca78d8af6375

import Mathlib
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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.SymmetricForm
universe uK uι uα uV uA
variable {K : Type uK} [CommSemiring K] {r j : ℕ}
theorem h51b_eval_perm {K : Type*} [CommSemiring K] {r j : ℕ}
    (F : OAI.MetricEntropyDuality.SymmetricForm K r j) (args : Fin j → Fin r → K)
    (σ : Equiv.Perm (Fin j)) :
    OAI.MetricEntropyDuality.SymmetricForm.eval F (args ∘ σ) =
      OAI.MetricEntropyDuality.SymmetricForm.eval F args := by
  unfold OAI.MetricEntropyDuality.SymmetricForm.eval
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl _)) _ _ (fun c => ?_)
  show F (tupleSym c) * ∏ i, args (σ i) (c i) =
    F (tupleSym (c ∘ σ.symm)) * ∏ i, args i (c (σ.symm i))
  rw [tupleSym_comp_perm, ← Equiv.prod_comp σ (fun i => args i (c (σ.symm i)))]
  simp

theorem h51b_eval_cons {K : Type*} [CommSemiring K] {r j : ℕ}
    (F : OAI.MetricEntropyDuality.SymmetricForm K r (j + 1)) (v : Fin r → K)
    (w : Fin j → Fin r → K) :
    OAI.MetricEntropyDuality.SymmetricForm.eval F (Fin.cons v w) =
      OAI.MetricEntropyDuality.SymmetricForm.eval
        (OAI.MetricEntropyDuality.SymmetricForm.contract v F) w := by
  unfold OAI.MetricEntropyDuality.SymmetricForm.eval
  rw [← (Fin.consEquiv (fun _ => Fin r)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, tupleSym_cons, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, OAI.MetricEntropyDuality.SymmetricForm.contract_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show ((Fin.consEquiv fun _ => Fin r) (a, b)) = Fin.cons a b from rfl, tupleSym_cons]
  ring

theorem solution (v : Fin r → K)
    (F G : SymmetricForm K r (j + 1))
    (hFG : contract v F = contract v G)
    (args : Fin (j + 1) → (Fin r → K)) (a : Fin (j + 1)) (ha : args a = v) :
    F.eval args = G.eval args := by
  have key : ∀ H : SymmetricForm K r (j + 1),
      H.eval args = H.eval (Fin.cons v (Fin.tail (args ∘ Equiv.swap 0 a))) := by
    intro H
    rw [← h51b_eval_perm H args (Equiv.swap 0 a)]
    congr 1
    have h0 : (args ∘ Equiv.swap 0 a) 0 = v := by simp [ha]
    rw [← h0, Fin.cons_self_tail]
  rw [key F, key G, h51b_eval_cons, h51b_eval_cons, hFG]

