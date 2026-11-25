-- Prove2me | solution 1 for GlobalTheory.DualCokernel.extZero_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:03.422505+00:00
-- url     : https://prove2.me/submissions/905e1150-7be8-4884-80ac-1c5261d77448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution {X F : Type} [AddCommGroup X] [Module R X] [AddCommGroup F] [Module R F]
    (f : X →ₗ[R] F) (q : F →ₗ[R] X) (h : q ∘ₗ f = LinearMap.id) (n : ℕ)
    (hF : ExtZero (R := R) F n) : ExtZero (R := R) X n := by
  have hid : 𝟙 (ModuleCat.of R X) = ModuleCat.ofHom f ≫ ModuleCat.ofHom q := by
    rw [← ModuleCat.ofHom_comp, h, ModuleCat.ofHom_id]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, hid, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    @Subsingleton.elim _ hF (x.comp _ _) 0, Ext.zero_comp]
end GlobalTheory.DualCokernel
