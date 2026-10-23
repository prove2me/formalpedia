-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_jet_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:01:41.319375+00:00
-- url     : https://prove2.me/submissions/9cd653f3-cf72-41bc-a102-ca30a6282f14

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (n K : Nat) (W V : Fin n → Rat) (N : Nat) (a : Real)
    (c : Fin K → Fin n → Complex)
    (hSfinite : Set.Finite {m : Fin n →₀ Nat |
      (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)})
    (hTfinite : Set.Finite {b : Fin n →₀ Nat |
      (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)})
    (hcard : Set.ncard {m : Fin n →₀ Nat |
      (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)} >
      K * Set.ncard {b : Fin n →₀ Nat |
      (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)}) :
    ∃ F : MvPolynomial (Fin n) Complex,
      F ≠ 0 ∧ fibreContactSupportBound W N F ∧
        fibreContactJetVanishing c V (a * (N : Real)) F := by
  set S := {m : Fin n →₀ Nat |
      (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)} with hS
  set T := {b : Fin n →₀ Nat |
      (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)} with hT
  haveI : Fintype S := hSfinite.fintype
  haveI : Fintype T := hTfinite.fintype
  let P := MvPolynomial.restrictSupport Complex S
  let g : Fin K → Fin n → MvPolynomial (Fin n) Complex :=
    fun j i => MvPolynomial.C (c j i) + MvPolynomial.X i
  let L : P →ₗ[Complex] (Fin K × T → Complex) :=
    LinearMap.pi (fun p : Fin K × T =>
      ((MvPolynomial.lcoeff Complex (p.2 : Fin n →₀ Nat)).comp
        (MvPolynomial.aeval (g p.1)).toLinearMap).comp P.subtype)
  have hdimP : Module.finrank Complex P = S.ncard := by
    rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport Complex S),
      Set.ncard_eq_toFinset_card' S, Set.toFinset_card]
  haveI : FiniteDimensional Complex P :=
    Module.Finite.of_basis (MvPolynomial.basisRestrictSupport Complex S)
  have hdimT : Module.finrank Complex (Fin K × T → Complex) = K * T.ncard := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Set.ncard_eq_toFinset_card' T, Set.toFinset_card]
  have hker : LinearMap.ker L ≠ ⊥ := L.ker_ne_bot_of_finrank_lt (by omega)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(x : MvPolynomial (Fin n) Complex), ?_, ?_, ?_⟩
  · intro h; exact hx0 (Subtype.ext h)
  · intro m hm
    exact x.2 hm
  · intro j b hb
    have := congrFun (LinearMap.mem_ker.mp hx) (j, ⟨b, hb⟩)
    simpa [L, g] using this
