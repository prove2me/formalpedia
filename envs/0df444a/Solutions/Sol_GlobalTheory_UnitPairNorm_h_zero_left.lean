-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.h_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:14.221954+00:00
-- url     : https://prove2.me/submissions/46bed51c-7aab-4bcc-8e67-170db17b5baf

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution (h : V → V → E) (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (z : V) : h 0 z = 0 := by
  have := hsmul 0 0 z
  rwa [zero_smul, zero_mul] at this
end GlobalTheory.UnitPairNorm
