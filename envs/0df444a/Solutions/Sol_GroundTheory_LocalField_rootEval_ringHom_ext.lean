-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_ringHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:55.503893+00:00
-- url     : https://prove2.me/submissions/242fd68e-6fb4-436c-a832-03ae00833a0c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_powerSeries_ringHom_ext
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_mem_span_root_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
namespace GroundTheory.LocalField
theorem _root_.solution [IsHausdorff I B] (hP : P.IsDistinguishedAt I)
    {Φ₁ Φ₂ : B⟦X⟧ →+* AdjoinRoot P}
    (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ Ideal.span {AdjoinRoot.root P}) : Φ₁ = Φ₂ :=
  powerSeries_ringHom_ext (fun _ hz => eq_zero_of_forall_mem_span_root_pow hP hz) hC hX hXJ
end GroundTheory.LocalField
