-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.finiteQuadratic_detects_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:38.456447+00:00
-- url     : https://prove2.me/submissions/c9db3a1b-6695-4859-add1-987abab79199

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ActualEisensteinSieve
example (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
example (P : Ideal O) [P.IsMaximal] : Finite (O ⧸ P) := inferInstance
private theorem exists_localQuadratic_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ x : O, localQuadratic P x = -1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hodd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨x, ?_⟩
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = -1
  exact ha
end ActualEisensteinSieve
end
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinSieve
namespace OAI.ActualEisensteinSieve
theorem _root_.solution
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ∃ x : O,
      (∀ j : ι, j ≠ i₀ → Ideal.Quotient.mk (P j) x = 1) ∧
      (∏ j : ι, localQuadratic (P j) x) = -1 := by
  classical
  obtain ⟨a, ha⟩ := exists_localQuadratic_neg_one (P i₀) (hodd i₀)
  let target (j : ι) : O ⧸ P j :=
    Ideal.Quotient.mk (P j) (if j = i₀ then a else 1)
  obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective hpair target
  have hlocal (j : ι) :
      localQuadratic (P j) x = if j = i₀ then -1 else 1 := by
    by_cases hj : j = i₀
    · subst j
      have hres : Ideal.Quotient.mk (P i₀) x = Ideal.Quotient.mk (P i₀) a := by
        simpa [target] using hx i₀
      simpa using (localQuadratic_congr (P i₀) x a hres).trans ha
    · have hres : Ideal.Quotient.mk (P j) x = Ideal.Quotient.mk (P j) (1 : O) := by
        simpa [target, hj] using hx j
      simpa [hj] using (localQuadratic_congr (P j) x 1 hres).trans
        (localQuadratic_one (P j))
  refine ⟨x, ?_, ?_⟩
  · intro j hj
    simpa [target, hj] using hx j
  · simp_rw [hlocal]
    simp
end OAI.ActualEisensteinSieve
