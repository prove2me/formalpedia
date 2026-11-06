-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.squarefreeQuotientChar_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:30.767782+00:00
-- url     : https://prove2.me/submissions/c02f9d76-21c1-4a87-a37e-6531bc7650af

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadraticOnQuotient_mk
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_not_factor_subproduct
import Theorems.Thm_OAI_ActualEisensteinSieve_squarefreeQuotientChar_mk

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
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ s.prod P) → ℤ,
      ∀ x : O,
        squarefreeQuotientChar P hpair
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by
  intro hf
  apply finiteQuadratic_not_factor_subproduct P hpair hodd s i₀ hi₀
  obtain ⟨f, hf⟩ := hf
  refine ⟨f, ?_⟩
  intro x
  simpa only [finiteQuadraticOnQuotient_mk, squarefreeQuotientChar_mk] using hf x
end OAI.ActualEisensteinSieve
