-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_reduction_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:43.965581+00:00
-- url     : https://prove2.me/submissions/c7c6e2a8-5a5e-454e-9962-76ff5d106a71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_flat_of_flat_reduction
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]
namespace GlobalTheory
theorem _root_.solution {C D : Type*} [CommRing C] [CommRing D] (φ : A →ₐ[T] B)
    (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hp𝔪 : RingHom.ker p = (maximalIdeal T).map (algebraMap T A))
    (hq𝔪 : RingHom.ker q = (maximalIdeal T).map (algebraMap T B))
    (hsq : ψ.comp p = q.comp φ) (hψ : ψ.Flat) : (φ : A →+* B).Flat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have h𝔪 := hπ.maximalIdeal_eq
  have hφ : (φ : A →+* B) (algebraMap T A π) = algebraMap T B π := φ.commutes π
  refine ringHom_flat_of_flat_reduction (φ : A →+* B) (π := algebraMap T A π) ?_ ?_ p q ψ hp hq
    ?_ ?_ hsq hψ
  · rw [hφ]
    exact maximalIdeal_le_jacobson _ (map_nonunit _ _ hπ.not_isUnit)
  · rw [hφ]
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
    intro x y hxy
    apply this
    simpa [Algebra.smul_def] using hxy
  · rw [hp𝔪, h𝔪, Ideal.map_span, Set.image_singleton]
  · rw [hq𝔪, h𝔪, Ideal.map_span, Set.image_singleton, hφ]
end GlobalTheory
