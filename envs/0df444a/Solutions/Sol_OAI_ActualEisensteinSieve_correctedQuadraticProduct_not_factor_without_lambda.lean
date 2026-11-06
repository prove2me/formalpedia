-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.correctedQuadraticProduct_not_factor_without_lambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:32.267945+00:00
-- url     : https://prove2.me/submissions/4e08f1ab-3c8a-4c75-8f56-227a633c2cd7

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
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
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (hneed : quadraticProduct P (-1) ≠ 1) :
    ¬ ∃ f : (O ⧸ Finset.univ.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (Finset.univ.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hlambda, hP⟩ := crt_pair lambdaIdeal (Finset.univ.prod P) hcop
    (Ideal.Quotient.mk lambdaIdeal (-1 : O))
    (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O))
  have hraw : quadraticProduct P x = 1 := by
    change (∏ i : ι, localQuadratic (P i) x) = 1
    rw [finiteQuadratic_congr_mod_product P x 1 hP]
    simp [localQuadratic_one]
  have hlocal : localQuadratic lambdaIdeal x = -1 := by
    rw [localQuadratic_congr lambdaIdeal x (-1) hlambda]
    exact lambdaQuadratic_neg_one
  have hx : correctedQuadraticProduct P x = -1 := by
    simp [correctedQuadraticProduct, hneed, hraw, hlocal]
  have h1 : correctedQuadraticProduct P (1 : O) = 1 :=
    correctedQuadraticProduct_one P
  have hEq : f (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      f (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O)) :=
    congrArg f hP
  have : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (Finset.univ.prod P) x) :=
        hx.symm.trans (hf x)
      _ = f (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O)) := hEq
      _ = 1 := (hf 1).symm.trans h1
  norm_num at this
end OAI.ActualEisensteinSieve
