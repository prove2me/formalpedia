-- Prove2me | solution 1 for MazurTransfer.RationalQuotientPicardGaloisTrace.pic0_galois_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T16:20:15.807246+00:00
-- url     : https://prove2.me/submissions/30c1ba89-eb63-4980-bb3a-46de053fa8a8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original Pic0 Galois-trace proof retained, using its public principal-divisor input.
Design boundary: the sum of Galois conjugates of any arithmetic degree-zero
Picard class vanishes over a specified rational quotient field.
Named downstream consumer: finite-subgroup and cyclic Pic0 trace.
Official Anthropic FLT divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_RationalQuotientPicardGaloisTrace_degree_zero_galois_trace_principal
noncomputable section
universe u v w
open AlgebraicCurve MazurTransfer.RationalQuotientPicardGaloisTrace

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {E : Type w} [Field E] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K E] (e : RatFunc K ≃ₐ[K] F) (c : Pic0 K E) :
    ∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • c = 0 := by
  classical
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  let T : Divisor.degZero (K := K) (F := E) :=
    ∑ σ : E ≃ₐ[F] E, Pic0.degZeroSMulHom (σ.restrictScalars K) D
  have hT : (T : Divisor K E) =
      ∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • (D : Divisor K E) := by
    change (Divisor.degZero (K := K) (F := E)).subtype
      (∑ σ : E ≃ₐ[F] E, Pic0.degZeroSMulHom (σ.restrictScalars K) D) = _
    rw [map_sum]
    rfl
  have hp : (T : Divisor K E).IsPrincipal := by
    rw [hT]
    exact degree_zero_galois_trace_principal e (D : Divisor K E)
      (show Divisor.degree (D : Divisor K E) = 0 from D.2)
  have hm : Pic0.mk T = 0 := (QuotientAddGroup.eq_zero_iff T).mpr hp
  let q : Divisor.degZero (K := K) (F := E) →+ Pic0 K E :=
    QuotientAddGroup.mk' _
  have hsum : Pic0.mk T =
      ∑ σ : E ≃ₐ[F] E, (σ.restrictScalars K) • Pic0.mk D := by
    change q T = _
    rw [map_sum]
    rfl
  exact hsum.symm.trans hm

#print axioms solution
