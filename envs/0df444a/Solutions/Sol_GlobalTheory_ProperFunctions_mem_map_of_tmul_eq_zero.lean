-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.mem_map_of_tmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:19.149685+00:00
-- url     : https://prove2.me/submissions/ee2622fb-fbaf-4290-b407-da61a2294cec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [AddCommGroup M] [Module R M] (x : A) (m : M) (J : Ideal R)
    (hJ : ∀ r : R, r • m = 0 → r ∈ J) (h : x ⊗ₜ[R] m = 0) :
    x ∈ J.map (algebraMap R A) := by
  let φ : R →ₗ[R] M := LinearMap.toSpanSingleton R M m
  have hex := Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map φ)
  have h0 : φ.lTensor A (x ⊗ₜ[R] (1 : R)) = 0 := by simp [φ, h]
  obtain ⟨y, hy⟩ := (hex _).mp h0
  have key : ∀ y : A ⊗[R] LinearMap.ker φ,
      TensorProduct.rid R A ((LinearMap.ker φ).subtype.lTensor A y) ∈ J.map (algebraMap R A) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, TensorProduct.rid_tmul,
        Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hJ _ (LinearMap.mem_ker.mp r.2)))
    | add a b ha hb => simpa only [map_add] using Ideal.add_mem _ ha hb
  simpa [hy] using key y
end GlobalTheory.ProperFunctions
