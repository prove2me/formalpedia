-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:34.962864+00:00
-- url     : https://prove2.me/submissions/02399ef8-c922-48bc-b19a-f21a5e7b7604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have key : ∀ (z : R), z ≠ 0 → ∀ K : Ideal R, Nonempty (K ≃ₗ[R] ↥(Ideal.span {z} * K)) := by
    intro z hz K
    have hinj : Function.Injective (LinearMap.mulLeft R z) := fun a b hab => mul_left_cancel₀ hz hab
    refine ⟨(Submodule.equivMapOfInjective _ hinj K).trans (LinearEquiv.ofEq _ _ ?_)⟩
    ext w
    rw [Submodule.mem_map, Ideal.mem_span_singleton_mul]
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  exact ⟨(key x hx I).some.trans ((LinearEquiv.ofEq _ _ hxy).trans (key y hy J).some.symm)⟩
end GlobalTheory.ProjModFinIso
