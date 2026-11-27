-- Prove2me | solution 2 for GlobalTheory.UnitaryStd.zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:33.993839+00:00
-- url     : https://prove2.me/submissions/03a85763-a5c2-498c-b1ad-03d3c9045c7c

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
namespace GlobalTheory.UnitaryStd
theorem _root_.solution (i : Fin r) : (0 : Lat ρ g) i = 0 := rfl
end GlobalTheory.UnitaryStd
