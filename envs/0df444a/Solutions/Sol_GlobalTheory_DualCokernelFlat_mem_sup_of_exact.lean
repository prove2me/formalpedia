-- Prove2me | solution 1 for GlobalTheory.DualCokernelFlat.mem_sup_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:04.080005+00:00
-- url     : https://prove2.me/submissions/9fce087a-c230-4314-b7b2-71b6e82f74fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernelFlat_dual_baseChange_surjective
import Theorems.Thm_GlobalTheory_DualCokernelFlat_dual_baseChange_eq_zero_iff
import Theorems.Thm_GlobalTheory_DualCokernelFlat_dual_baseChange_dualMap
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernelFlat
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
namespace GlobalTheory.DualCokernelFlat
theorem _root_.solution (hs : Surjective (algebraMap A B)) {M₀ M₁ M₂ : Type}
    [AddCommGroup M₀] [Module A M₀] [Module.Free A M₀] [Module.Finite A M₀]
    [AddCommGroup M₁] [Module A M₁] [Module.Free A M₁] [Module.Finite A M₁]
    [AddCommGroup M₂] [Module A M₂] [Module.Free A M₂] (a : M₀ →ₗ[A] M₁) (b : M₁ →ₗ[A] M₂)
    (h : Exact (b.baseChange B).dualMap (a.baseChange B).dualMap) (x : Module.Dual A M₁)
    (hx : a.dualMap x ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₀))) :
    x ∈ LinearMap.range b.dualMap ⊔
      (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₁)) := by
  rw [← dual_baseChange_eq_zero_iff, dual_baseChange_dualMap] at hx
  obtain ⟨y, hy⟩ := (h _).1 hx
  obtain ⟨y, rfl⟩ := dual_baseChange_surjective hs M₂ y
  have : x = b.dualMap y + (x - b.dualMap y) := by abel
  rw [this]
  refine Submodule.add_mem_sup ⟨y, rfl⟩ ?_
  rw [← dual_baseChange_eq_zero_iff, map_sub, dual_baseChange_dualMap, hy, sub_self]
end GlobalTheory.DualCokernelFlat
