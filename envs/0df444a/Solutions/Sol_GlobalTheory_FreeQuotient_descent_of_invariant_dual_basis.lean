-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.descent_of_invariant_dual_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:10.35384+00:00
-- url     : https://prove2.me/submissions/df8faa1c-0f11-4469-a246-efa717216b0c

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
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
omit [Fintype G] [SMulDistribClass G A M]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution {n : ℕ} (v : Fin n → M) (f : Fin n → M →ₗ[A] A)
    (hv : ∀ i (g : G), g • v i = v i) (hf : ∀ i (g : G) m, f i (g • m) = g • f i m)
    (hfv : ∀ m, ∑ i, f i m • v i = m) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by
  set I := (Representation.ofDistribMulAction B G M).invariants
  let v' : Fin n → I := fun i ↦ ⟨v i, hv i⟩
  let f' : Fin n → I →ₗ[B] B := fun i ↦ (invariantsRingEquiv G B A).symm.toLinearMap ∘ₗ
    invariantsMap _ _ ((f i).restrictScalars B) (hf i)
  have hf' : ∀ i x, algebraMap B A (f' i x) = f i x := fun i x ↦
    algebraMap_invariantsRingEquiv_symm G B A _
  have hfv' : ∀ x, ∑ i, f' i x • v' i = x := fun x ↦ Subtype.ext <| by
    conv_rhs => rw [← hfv x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, v', ← hf', algebraMap_smul]
  have hcomp : Fintype.linearCombination B v' ∘ₗ LinearMap.pi f' = LinearMap.id := by
    refine LinearMap.ext fun x ↦ ?_
    simpa [Fintype.linearCombination_apply] using hfv' x
  refine ⟨?_, ?_, .of_split _ _ hcomp⟩
  · let ψ : M →ₗ[A] A ⊗[B] I := ∑ i, (f i).smulRight (1 ⊗ₜ v' i)
    have hψ : ∀ m, ψ m = ∑ i, f i m • (1 : A) ⊗ₜ[B] v' i := fun m ↦ by
      simp [ψ, LinearMap.sum_apply]
    refine .of_equiv (LinearEquiv.ofLinear (I.subtype.liftBaseChange A) ψ ?_ ?_) fun x ↦
      (LinearMap.liftBaseChange_tmul A I.subtype 1 x).trans (one_smul _ _)
    · refine LinearMap.ext fun m ↦ ?_
      simpa [hψ, v'] using hfv m
    · ext x
      change ψ (I.subtype.liftBaseChange A (1 ⊗ₜ x)) = 1 ⊗ₜ x
      rw [LinearMap.liftBaseChange_tmul, one_smul, Submodule.subtype_apply, hψ]
      conv_rhs => rw [← hfv' x]
      simp [TensorProduct.tmul_sum, ← hf']
  · refine .of_surjective (Fintype.linearCombination B v') fun x ↦ ⟨_, LinearMap.congr_fun hcomp x⟩
end GlobalTheory.FreeQuotient
