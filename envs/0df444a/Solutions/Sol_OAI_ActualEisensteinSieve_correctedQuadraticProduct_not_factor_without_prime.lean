-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.correctedQuadraticProduct_not_factor_without_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:42.183866+00:00
-- url     : https://prove2.me/submissions/7d892785-45f2-417c-b5b9-487df533fc92

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_detects_prime
import Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_congr_mod_product
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
private theorem crt_pair (I J : Ideal O) (h : IsCoprime I J)
    (a : O ⧸ I) (b : O ⧸ J) :
    ∃ x : O, Ideal.Quotient.mk I x = a ∧ Ideal.Quotient.mk J x = b := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (a, b))
  have he : e (Ideal.Quotient.mk (I * J) x) = (a, b) := by
    rw [hx, e.apply_symm_apply]
  refine ⟨x, ?_, ?_⟩
  · simpa [e] using congrArg Prod.fst he
  · simpa [e] using congrArg Prod.snd he
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
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ lambdaIdeal * s.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  obtain ⟨y, hlam, hfull⟩ := crt_pair lambdaIdeal (Finset.univ.prod P) hcop
    (Ideal.Quotient.mk lambdaIdeal (1 : O))
    (Ideal.Quotient.mk (Finset.univ.prod P) x)
  have hraw : quadraticProduct P y = -1 := by
    change (∏ j : ι, localQuadratic (P j) y) = -1
    rw [finiteQuadratic_congr_mod_product P y x hfull]
    exact hneg
  have hlocal : localQuadratic lambdaIdeal y = 1 := by
    rw [localQuadratic_congr lambdaIdeal y 1 hlam]
    exact localQuadratic_one lambdaIdeal
  have hy : correctedQuadraticProduct P y = -1 := by
    by_cases hsign : quadraticProduct P (-1) = 1
    · simp [correctedQuadraticProduct, hsign, hraw]
    · simp [correctedQuadraticProduct, hsign, hraw, hlocal]
  have hcopS : IsCoprime lambdaIdeal (s.prod P) := by
    apply IsCoprime.prod_right
    intro j hj
    exact (IsCoprime.prod_right_iff.mp hcop) j (Finset.mem_univ j)
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprodS : s.prod P = ⨅ j ∈ s, P j :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hs : y - 1 ∈ s.prod P := by
    rw [hprodS]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := by
      intro he
      subst j
      exact hi₀ hj
    have hPj : Ideal.Quotient.mk (P j) y =
        Ideal.Quotient.mk (P j) x := by
      apply Ideal.Quotient.eq.mpr
      exact (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_univ j))) (Ideal.Quotient.eq.mp hfull)
    exact Ideal.Quotient.eq.mp (hPj.trans (hres j hjne))
  have hmod : Ideal.Quotient.mk (lambdaIdeal * s.prod P) y =
      Ideal.Quotient.mk (lambdaIdeal * s.prod P) (1 : O) := by
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.mul_eq_inf_of_isCoprime hcopS]
    exact ⟨Ideal.Quotient.eq.mp hlam, hs⟩
  have : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) y) :=
        hy.symm.trans (hf y)
      _ = f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) (1 : O)) :=
        congrArg f hmod
      _ = 1 := (hf 1).symm.trans (correctedQuadraticProduct_one P)
  norm_num at this
end OAI.ActualEisensteinSieve
