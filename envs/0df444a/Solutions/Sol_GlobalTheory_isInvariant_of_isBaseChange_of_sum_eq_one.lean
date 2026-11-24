-- Prove2me | solution 1 for GlobalTheory.isInvariant_of_isBaseChange_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:33.309717+00:00
-- url     : https://prove2.me/submissions/11342d03-61d6-49a9-94a9-9c3945e69b26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type*} [Group G] [Fintype G] {B B' A A' : Type*} [CommRing B] [CommRing B']
  [CommRing A] [CommRing A'] [Algebra B B'] [Algebra B A] [Algebra B A'] [Algebra B' A']
  [IsScalarTower B B' A'] [MulSemiringAction G A] [SMulCommClass G B A] [MulSemiringAction G A']
  [SMulCommClass G B' A'] [FaithfulSMul B A] [Algebra.IsInvariant B A G]
namespace GlobalTheory
theorem _root_.solution {c : A} (hc : ∑ g : G, g • c = 1)
    (f : A →ₐ[B] A') (hb : IsBaseChange B' f.toLinearMap)
    (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    FaithfulSMul B' A' ∧ Algebra.IsInvariant B' A' G := by
  let τ : A' →ₗ[B'] B' := hb.lift
    (Algebra.linearMap B B' ∘ₗ FreeQuotient.ringTrace G B A ∘ₗ LinearMap.mulLeft B c)
  have hτf (a : A) : τ (f a) = algebraMap B B' (FreeQuotient.ringTrace G B A (c * a)) :=
    hb.lift_eq _ a
  have hτ (x : A') : algebraMap B' A' (τ x) = ∑ g : G, g • (f c * x) := by
    induction x using hb.inductionOn with
    | zero => simp
    | tmul a =>
      change algebraMap B' A' (τ (f a)) = ∑ g : G, g • (f c * f a)
      rw [hτf, ← IsScalarTower.algebraMap_apply, ← f.commutes, FreeQuotient.algebraMap_ringTrace,
        map_sum]
      simp only [hf, map_mul]
    | smul b x hx =>
      rw [map_smul, smul_eq_mul, map_mul, hx, ← Algebra.smul_def, Finset.smul_sum]
      simp only [mul_smul_comm, smul_comm _ b]
    | add x y hx hy => simp only [map_add, hx, hy, mul_add, smul_add, Finset.sum_add_distrib]
  have h1 : τ 1 = 1 := by
    have : FreeQuotient.ringTrace G B A c = 1 := FaithfulSMul.algebraMap_injective B A (by
      rw [FreeQuotient.algebraMap_ringTrace, hc, map_one])
    rw [← map_one f, hτf, mul_one, this, map_one]
  refine ⟨(faithfulSMul_iff_algebraMap_injective _ _).mpr (Function.LeftInverse.injective
    (g := τ) fun b ↦ ?_), ⟨fun x hx ↦ ⟨τ x, ?_⟩⟩⟩
  · rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul, mul_one]
  · have hx' (g : G) : g • x = x := hx g
    rw [hτ]
    simp only [smul_mul', hx', ← hf]
    rw [← Finset.sum_mul, ← map_sum, hc, map_one, one_mul]
end GlobalTheory
