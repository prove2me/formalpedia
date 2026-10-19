-- Prove2me | solution 1 for MazurTransfer.RationalArithmeticPicardTriviality.principal_of_rational_field_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:52:42.14816+00:00
-- url     : https://prove2.me/submissions/6d6b3614-ccb5-47d8-9d35-c290817111db

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete original rational-field divisor principality proof retained.
The native public theorem resolves to its retained checked interface.
Design boundary: every degree-zero divisor over a field isomorphic to K(t)
is principal, with the actual divisor and field equivalence explicit.
Named downstream consumer: rational quotient Picard Galois trace, then the
actual order-13 diamond cyclotomic and norm identities.
Official Anthropic FLT inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
import Definitions.Def_AlgebraicCurve_Pic0Congr
noncomputable section
universe u v
open AlgebraicCurve
local instance (K : Type u) [Field K] : Algebra K (RatFunc K) := RatFunc.instAlgebraOfPolynomial K K

theorem solution
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (e : RatFunc K ≃ₐ[K] F)
    (D : Divisor K F) (hD : Divisor.degree D = 0) : D.IsPrincipal := by
  let E := Divisor.congr e.toRingEquiv e.commutes
  have h := RationalFunctionField.isPrincipal_of_degree_eq_zero (E.symm D)
    (by simpa [E] using hD)
  have ht := Divisor.congr_mem_principal e.toRingEquiv e.commutes h
  change D ∈ Divisor.principal (K := K) (F := F)
  simpa [E] using ht


#print axioms solution
