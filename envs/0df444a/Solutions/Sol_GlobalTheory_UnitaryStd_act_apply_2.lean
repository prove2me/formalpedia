-- Prove2me | solution 2 for GlobalTheory.UnitaryStd.act_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:31.195281+00:00
-- url     : https://prove2.me/submissions/58da52d9-bf68-44f9-9750-d45483702ff4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open GlobalTheory GlobalTheory.UnitaryStd
variable {r g : ℕ}
variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
variable {ρ g}
variable (ρ g)
namespace GlobalTheory.UnitaryStd
theorem _root_.solution (a : 𝓞 E) (x : Lat ρ g) : act ρ g a x = a • x := rfl
end GlobalTheory.UnitaryStd
