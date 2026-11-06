-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.finiteQuadratic_not_factor_subproduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:14.961482+00:00
-- url     : https://prove2.me/submissions/921b4d73-8ee3-460d-aeda-2428e86ccd0c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_detects_prime
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadraticOnQuotient_mk

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
        finiteQuadraticOnQuotient P
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprod : s.prod P = ⨅ j ∈ s, P j :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hmem : x - 1 ∈ s.prod P := by
    rw [hprod]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := by
      intro he
      subst j
      exact hi₀ hj
    exact Ideal.Quotient.eq.mp (hres j hjne)
  have hsame : Ideal.Quotient.mk (s.prod P) x =
      Ideal.Quotient.mk (s.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr hmem
  have hx := hf x
  have h1 := hf (1 : O)
  rw [finiteQuadraticOnQuotient_mk, hneg] at hx
  rw [finiteQuadraticOnQuotient_mk] at h1
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (s.prod P) x) := hx
      _ = f (Ideal.Quotient.mk (s.prod P) (1 : O)) := by rw [hsame]
      _ = 1 := h1.symm
  norm_num at absurd
end OAI.ActualEisensteinSieve
