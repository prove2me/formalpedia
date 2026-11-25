-- Prove2me | solution 1 for GlobalTheory.DualCokernelFlat.dual_baseChange_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:30.631702+00:00
-- url     : https://prove2.me/submissions/a9bacc7a-4560-4896-9045-97f120b45ff0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
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
theorem _root_.solution (M : Type) [AddCommGroup M]
    [Module A M] [Module.Free A M] [Module.Finite A M] (f : Module.Dual A M) :
    Module.Dual.baseChange B f = 0 ↔
      f ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M)) := by
  constructor
  · intro h
    let b := Module.Free.chooseBasis A M
    rw [← b.sum_dual_apply_smul_coord f]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have := LinearMap.congr_fun h (1 ⊗ₜ b i)
    simpa [RingHom.mem_ker, Algebra.algebraMap_eq_smul_one] using this
  · intro h
    refine Submodule.smul_induction_on h (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, ← algebraMap_smul B r, RingHom.mem_ker.mp hr, zero_smul]
    · rw [map_add, hx, hy, add_zero]
end GlobalTheory.DualCokernelFlat
