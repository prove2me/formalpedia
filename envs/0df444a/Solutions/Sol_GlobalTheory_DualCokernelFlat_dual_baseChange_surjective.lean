-- Prove2me | solution 1 for GlobalTheory.DualCokernelFlat.dual_baseChange_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:11.839134+00:00
-- url     : https://prove2.me/submissions/70c4b231-324a-413b-8a7f-b5356aef04a5

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
theorem _root_.solution (hs : Surjective (algebraMap A B)) (M : Type) [AddCommGroup M]
    [Module A M] [Module.Projective A M] :
    Surjective (Module.Dual.baseChange B : Module.Dual A M → Module.Dual B (B ⊗[A] M)) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap A B)
    (g.restrictScalars A ∘ₗ TensorProduct.mk A B M 1) hs
  refine ⟨f, ?_⟩
  ext x
  have := LinearMap.congr_fun hf x
  simpa [Algebra.algebraMap_eq_smul_one] using this
end GlobalTheory.DualCokernelFlat
