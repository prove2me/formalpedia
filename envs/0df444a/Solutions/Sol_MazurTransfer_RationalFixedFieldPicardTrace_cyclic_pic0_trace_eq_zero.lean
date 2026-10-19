-- Prove2me | solution 1 for MazurTransfer.RationalFixedFieldPicardTrace.cyclic_pic0_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T16:28:41.862599+00:00
-- url     : https://prove2.me/submissions/359f1176-c1e9-41a3-b79b-ff879f39f85c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete original fixed-field subgroup and cyclic Pic0 trace proofs retained.
Design boundary: a finite-order automorphism with a specified rational fixed
field has zero cyclic trace on arithmetic Pic0, with the actual order explicit.
Named downstream consumer: actual order-13 diamond square/cube trace and norm.
Official Anthropic FLT divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_RationalQuotientPicardGaloisTrace_pic0_galois_trace_eq_zero
import Mathlib.FieldTheory.Fixed
noncomputable section
universe u v
open AlgebraicCurve
namespace MazurTransfer.RationalFixedFieldPicardTracePublicHelpers20261017
variable {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
  [HasPrincipalDivisors K E]
theorem subgroup_pic0_trace_eq_zero (H : Subgroup (E ≃ₐ[K] E)) [Fintype H]
    (e : RatFunc K ≃ₐ[K] IntermediateField.fixedField H) (c : Pic0 K E) :
    ∑ σ : H, (σ : E ≃ₐ[K] E) • c = 0 := by
  classical
  haveI : FiniteDimensional (IntermediateField.fixedField H) E :=
    inferInstanceAs (FiniteDimensional (FixedPoints.subfield H E) E)
  haveI : IsGalois (IntermediateField.fixedField H) E := IsGalois.of_fixed_field E H
  have h := MazurTransfer.RationalQuotientPicardGaloisTrace.pic0_galois_trace_eq_zero e c
  let A : H ≃* (E ≃ₐ[IntermediateField.fixedField H] E) :=
    FixedPoints.toAlgAutMulEquiv H E
  have hr (σ : H) : (A σ).restrictScalars K = (σ : E ≃ₐ[K] E) := by
    ext x
    rfl
  have hs := A.toEquiv.sum_comp (fun σ => (σ.restrictScalars K) • c)
  have hs0 : (∑ σ : H, (A σ).restrictScalars K • c) = 0 := hs.trans h
  simpa only [hr] using hs0

end MazurTransfer.RationalFixedFieldPicardTracePublicHelpers20261017

theorem solution
    {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [HasPrincipalDivisors K E] (σ : E ≃ₐ[K] E) (hσ : IsOfFinOrder σ)
    (e : RatFunc K ≃ₐ[K] IntermediateField.fixedField (Subgroup.zpowers σ))
    (c : Pic0 K E) :
    ∑ i : Fin (orderOf σ), (σ ^ (i : ℕ)) • c = 0 := by
  classical
  letI : Fintype (Subgroup.zpowers σ) := Fintype.ofEquiv (Fin (orderOf σ))
    (finEquivZPowers hσ)
  have h := MazurTransfer.RationalFixedFieldPicardTracePublicHelpers20261017.subgroup_pic0_trace_eq_zero (Subgroup.zpowers σ) e c
  have hs := (finEquivZPowers hσ).sum_comp
    (fun τ : Subgroup.zpowers σ => (τ : E ≃ₐ[K] E) • c)
  exact hs.trans h

#print axioms solution
