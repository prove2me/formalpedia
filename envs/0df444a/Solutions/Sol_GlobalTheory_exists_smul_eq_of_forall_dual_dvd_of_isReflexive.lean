-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_of_forall_dual_dvd_of_isReflexive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:34.361153+00:00
-- url     : https://prove2.me/submissions/f0ea7773-052a-49f9-b345-26bfcffee1e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [IsDomain A] [Module.IsReflexive A M]
    {a : A} (ha : a ≠ 0) {m : M} (h : ∀ φ : Module.Dual A M, a ∣ φ m) : ∃ m', a • m' = m := by
  choose c hc using h
  let ψ : Module.Dual A (Module.Dual A M) :=
    { toFun := c
      map_add' := fun φ φ' => mul_left_cancel₀ ha (by rw [mul_add, ← hc, ← hc, ← hc]; rfl)
      map_smul' := fun r φ => mul_left_cancel₀ ha (by
        rw [RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hc, ← hc]; rfl) }
  obtain ⟨m', hm'⟩ := (Module.bijective_dual_eval A M).2 ψ
  refine ⟨m', (Module.bijective_dual_eval A M).1 (LinearMap.ext fun φ => ?_)⟩
  rw [map_smul, hm', LinearMap.smul_apply, Module.Dual.eval_apply, hc]
  rfl
end GlobalTheory
