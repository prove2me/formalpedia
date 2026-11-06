-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.finiteQuadratic_not_factor_omit_prime_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:27.235366+00:00
-- url     : https://prove2.me/submissions/df82591d-1677-443c-9f3a-0f89ef0265fa

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_detects_prime

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
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ¬ ∃ f : (O ⧸ (Finset.univ.erase i₀).prod P) → ℤ,
      ∀ x : O,
        (∏ j : ι, localQuadratic (P j) x) =
          f (Ideal.Quotient.mk ((Finset.univ.erase i₀).prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  let s : Finset ι := Finset.univ.erase i₀
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprod : s.prod P = ⨅ j ∈ s, P j := by
    exact Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hmem : x - 1 ∈ s.prod P := by
    rw [hprod]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    exact Ideal.Quotient.eq.mp (hres j hjne)
  have hsame : Ideal.Quotient.mk (s.prod P) x =
      Ideal.Quotient.mk (s.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr hmem
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg] at hx
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (s.prod P) x) := by simpa [s] using hx
      _ = f (Ideal.Quotient.mk (s.prod P) (1 : O)) := by rw [hsame]
      _ = 1 := by simpa [s] using h1.symm
  norm_num at absurd
end OAI.ActualEisensteinSieve
