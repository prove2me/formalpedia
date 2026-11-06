-- Prove2me | solution 1 for Monodromy.Counter.Reversible.PrimeCompression.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:07:58.908208+00:00
-- url     : https://prove2.me/submissions/2113935d-ded0-467c-8008-aaf0c236132f

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.PrimeCompression
variable {n q e : ℕ}

theorem solution (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) :
    Function.Injective (encode basis source deterministic compatible) := by
  have decode_encode (registers : Fin n → ℕ) (index : Fin n) :
      (basis.encode registers).factorization (basis.prime index) = registers index := by
    unfold PrimeCode.Basis.encode
    rw [Nat.factorization_prod_apply
      (fun j _ => pow_ne_zero _ (basis.isPrime j).ne_zero)]
    simp only [(basis.isPrime _).factorization_pow, Finsupp.single_apply]
    rw [Finset.sum_eq_single index]
    · simp
    · intro j _ different
      have primes_different : basis.prime j ≠ basis.prime index :=
        fun same => different (basis.distinct same)
      simp [primes_different]
    · simp
  have encode_injective : Function.Injective basis.encode := by
    intro first second same
    funext index
    rw [← decode_encode first index, ← decode_encode second index, same]
  have boundary_link_none (position : Fin q) :
      (wiring basis source deterministic compatible).link
        (boundary basis source position) = none := by
    apply (PortNetwork.relationLink_none_iff (Connection basis source) _).mpr
    exact boundary_unconnected basis source deterministic position
  intro first second same
  have pc : first.pc = second.pc :=
    boundary_injective basis source
      (PortNetwork.control_unlinked_injective (wiring basis source deterministic compatible)
        (boundary_link_none first.pc) (boundary_link_none second.pc)
        (congrArg Prod.fst same))
  have counters : basis.encode first.counters = basis.encode second.counters := by
    have encoded : (basis.encode first.counters : ℤ) = basis.encode second.counters := by
      have values := congrFun (congrArg Prod.snd same) 0
      simpa [encode] using values
    exact_mod_cast encoded
  cases first
  cases second
  cases pc
  cases encode_injective counters
  rfl
