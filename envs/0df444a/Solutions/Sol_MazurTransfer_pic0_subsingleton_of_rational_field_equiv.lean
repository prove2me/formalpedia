-- Prove2me | solution 1 for MazurTransfer.pic0_subsingleton_of_rational_field_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T15:21:40.138184+00:00
-- url     : https://prove2.me/submissions/cdef1c83-bd60-4cb9-9ce5-149c40a8c575

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses complete checked Anthropic FLT rational divisor and Picard transport
proofs at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0.
Design boundary: degree-zero arithmetic divisor classes of a field
isomorphic to K(t). Named downstream consumer: the actual order-thirteen
order-three and hyperelliptic quotient Picard groups in Galois trace.
-/
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import Definitions.Def_AlgebraicCurve_Pic0Congr

noncomputable section
universe u v
namespace MazurTransfer.PublicRationalArithmeticPicardProof
open AlgebraicCurve
variable {K : Type u} [Field K]
local instance : Algebra K (RatFunc K) := RatFunc.instAlgebraOfPolynomial K K

theorem ratFunc_pic0_eq_zero (c : Pic0 K (RatFunc K)) : c = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  apply (QuotientAddGroup.eq_zero_iff D).mpr
  change (D : Divisor K (RatFunc K)) ∈ Divisor.principal (K := K) (F := RatFunc K)
  exact RationalFunctionField.isPrincipal_of_degree_eq_zero (D : Divisor K (RatFunc K))
    (show Divisor.degree (D : Divisor K (RatFunc K)) = 0 from D.2)

theorem ratFunc_pic0_subsingleton : Subsingleton (Pic0 K (RatFunc K)) := by
  constructor
  intro a b
  exact (ratFunc_pic0_eq_zero a).trans (ratFunc_pic0_eq_zero b).symm

variable {F : Type v} [Field F] [Algebra K F]

theorem principal_of_rational_field_equiv (e : RatFunc K ≃ₐ[K] F)
    (D : Divisor K F) (hD : Divisor.degree D = 0) : D.IsPrincipal := by
  let E := Divisor.congr e.toRingEquiv e.commutes
  have h := RationalFunctionField.isPrincipal_of_degree_eq_zero (E.symm D)
    (by simpa [E] using hD)
  have ht := Divisor.congr_mem_principal e.toRingEquiv e.commutes h
  change D ∈ Divisor.principal (K := K) (F := F)
  simpa [E] using ht

theorem pic0_eq_zero_of_rational_field_equiv (e : RatFunc K ≃ₐ[K] F)
    (c : Pic0 K F) : c = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  apply (QuotientAddGroup.eq_zero_iff D).mpr
  exact principal_of_rational_field_equiv e D (Divisor.mem_degZero.mp D.2)

theorem pic0_subsingleton_of_rational_field_equiv (e : RatFunc K ≃ₐ[K] F) :
    Subsingleton (Pic0 K F) := by
  constructor
  intro a b
  exact (pic0_eq_zero_of_rational_field_equiv e a).trans
    (pic0_eq_zero_of_rational_field_equiv e b).symm

end MazurTransfer.PublicRationalArithmeticPicardProof
#print axioms MazurTransfer.PublicRationalArithmeticPicardProof.pic0_subsingleton_of_rational_field_equiv

theorem solution (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (e : RatFunc K ≃ₐ[K] F) :
    Subsingleton (AlgebraicCurve.Pic0 K F) := by
  exact MazurTransfer.PublicRationalArithmeticPicardProof.pic0_subsingleton_of_rational_field_equiv e

#print axioms solution
