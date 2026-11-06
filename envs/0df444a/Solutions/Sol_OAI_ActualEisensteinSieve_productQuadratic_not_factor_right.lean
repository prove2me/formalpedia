-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.productQuadratic_not_factor_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:53.717189+00:00
-- url     : https://prove2.me/submissions/44a8e504-3058-4acd-b765-baf342382de8

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
private theorem productQuadratic_detects_left
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ x : O,
      Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q (1 : O) ∧
      localQuadratic P x * localQuadratic Q x = -1 := by
  obtain ⟨a, ha⟩ := exists_localQuadratic_neg_one P hodd
  obtain ⟨x, hP, hQ⟩ := crt_pair P Q hcop
    (Ideal.Quotient.mk P a) (Ideal.Quotient.mk Q (1 : O))
  refine ⟨x, hQ, ?_⟩
  rw [localQuadratic_congr P x a hP,
    localQuadratic_congr Q x 1 hQ, ha, localQuadratic_one]
  ring
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
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ¬ ∃ f : (O ⧸ Q) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk Q x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hQ, hneg⟩ := productQuadratic_detects_left P Q hcop hodd
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg, hQ] at hx
  rw [localQuadratic_one P, localQuadratic_one Q] at h1
  norm_num at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk Q (1 : O)) := hx
      _ = f 1 := by simp
      _ = 1 := h1.symm
  norm_num at absurd
end OAI.ActualEisensteinSieve
