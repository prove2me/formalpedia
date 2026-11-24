-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_baseChange_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:13.993799+00:00
-- url     : https://prove2.me/submissions/a4c9615d-d134-46e7-9a84-25245e41cce3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomology
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology
theorem _root_.solution (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A]
    [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) :
    Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by
  let e₁ := AlgebraTensorModule.cancelBaseChange R A K K Q
  let e₂ := AlgebraTensorModule.cancelBaseChange R A K K P
  have comm : ∀ x, e₂ (((d.baseChange A).baseChange K) x) = (d.baseChange K) (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul a q =>
        simp [e₁, e₂, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']
  refine ⟨LinearEquiv.ofSubmodules e₁ _ _ ?_⟩
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := comm x
    rw [hx, map_zero] at this
    exact this.symm
  · intro hy
    refine ⟨e₁.symm y, ?_, by simp⟩
    apply e₂.injective
    rw [comm, map_zero]
    simpa using hy
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
