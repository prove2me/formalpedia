-- Prove2me | solution 1 for MazurTransfer.RationalQuotientPicardGaloisTrace.degree_zero_galois_trace_principal
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T16:06:24.972352+00:00
-- url     : https://prove2.me/submissions/15238816-5ff5-4488-bc5f-fcb6f32089a0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete original finite-Galois rational-quotient trace proof retained.
Native imports resolve through the recorded retained checked interface closure.
Design boundary: the conjugate sum of a degree-zero divisor over a finite
Galois extension of a specified rational function field is principal.
Named downstream consumer: Pic0 Galois trace, then actual diamond cyclic trace.
Official Anthropic FLT trace and divisor inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_RationalArithmeticPicardTriviality_principal_of_rational_field_equiv
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward
noncomputable section
universe u v w
open AlgebraicCurve
namespace MazurTransfer.RationalQuotientGaloisTracePublicHelpers20261017
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
theorem place_ofAlgAut_smul (σ : F ≃ₐ[K] F) (p : Place K F) :
    SemilinearAut.ofAlgAut σ • p = σ • p := by
  apply Place.ext
  ext x
  rfl

theorem divisor_ofAlgAut_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    SemilinearAut.ofAlgAut σ • D = σ • D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | single_add p n D _ _ ih =>
    simp only [smul_add, SemilinearAut.smul_single, Divisor.smul_single,
      place_ofAlgAut_smul, ih]

end MazurTransfer.RationalQuotientGaloisTracePublicHelpers20261017

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {E : Type w} [Field E] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K E] (e : RatFunc K ≃ₐ[K] F)
    (D : Divisor K E) (hD : Divisor.degree D = 0) :
    (∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • D).IsPrincipal := by
  have hs : (∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • D) =
      Divisor.pullback E (Divisor.pushforward F D) := by
    simpa only [MazurTransfer.RationalQuotientGaloisTracePublicHelpers20261017.divisor_ofAlgAut_smul] using
      Divisor.sum_galois_smul_eq_pullback_pushforward D
  rw [hs]
  apply Divisor.isPrincipal_pullback
  apply MazurTransfer.RationalArithmeticPicardTriviality.principal_of_rational_field_equiv e
  simpa only [Divisor.degree_pushforward] using hD


#print axioms solution
