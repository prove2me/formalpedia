-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.existsUnique_equivariant_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:46:57.599038+00:00
-- url     : https://prove2.me/submissions/55933b9d-cbc8-43d8-a764-e7c9e5b0f355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {B : Type*} [CommRing B] [Algebra B A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
  [Module B N] [IsScalarTower B A N] [SMulCommClass G B N]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution
    (hb : IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype)
    (φ : (Representation.ofDistribMulAction B G M).invariants →ₗ[B]
      (Representation.ofDistribMulAction B G N).invariants) :
    ∃! f : M →ₗ[A] N, (∀ (g : G) m, f (g • m) = g • f m) ∧
      ∀ x : (Representation.ofDistribMulAction B G M).invariants, f x = φ x := by
  have hf := hb.lift_eq ((Representation.ofDistribMulAction B G N).invariants.subtype ∘ₗ φ)
  refine ⟨hb.lift (Submodule.subtype _ ∘ₗ φ), ⟨fun g m ↦ ?_, hf⟩, fun f' hf' ↦
    hb.algHom_ext _ _ fun x ↦ (hf'.2 x).trans (hf x).symm⟩
  induction m using hb.inductionOn with
  | zero => simp
  | tmul x =>
    have hx : g • (Submodule.subtype _ x : M) = Submodule.subtype _ x := x.2 g
    rw [hx, hf]
    exact ((φ x).2 g).symm
  | smul a m hm => simp only [smul_distrib_smul g a, LinearMap.map_smul, hm]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
end GlobalTheory.FreeQuotient
