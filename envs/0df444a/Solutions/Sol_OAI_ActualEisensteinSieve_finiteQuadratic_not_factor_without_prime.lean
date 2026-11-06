-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.finiteQuadratic_not_factor_without_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:26.543199+00:00
-- url     : https://prove2.me/submissions/f3c09320-0f33-4e00-8bf1-377682ec762c

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
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ¬ ∃ f : ((j : {j : ι // j ≠ i₀}) → O ⧸ P j.1) → ℤ,
      ∀ x : O,
        (∏ j : ι, localQuadratic (P j) x) =
          f (fun j => Ideal.Quotient.mk (P j.1) x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  have hsame :
      (fun j : {j : ι // j ≠ i₀} => Ideal.Quotient.mk (P j.1) x) =
      (fun j : {j : ι // j ≠ i₀} => Ideal.Quotient.mk (P j.1) (1 : O)) := by
    funext j
    simpa using hres j.1 j.2
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg, hsame] at hx
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := hx.trans h1.symm
  norm_num at absurd
end OAI.ActualEisensteinSieve
