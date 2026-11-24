-- Prove2me | solution 1 for GlobalTheory.ScaledRestr.inK_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:50.187069+00:00
-- url     : https://prove2.me/submissions/92f0c497-5250-4b4f-a8e0-a29e47af3233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.ScaledRestr
namespace GlobalTheory.ScaledRestr
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) := inferInstance
  unfold inK
  rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors O)]
  intro c
  intro x y hxy
  exact smul_right_injective H (nonZeroDivisors.coe_ne_zero c) hxy
end GlobalTheory.ScaledRestr
