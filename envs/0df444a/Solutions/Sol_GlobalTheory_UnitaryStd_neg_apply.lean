-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.neg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:11.163665+00:00
-- url     : https://prove2.me/submissions/3150f828-7e8e-400b-ac4b-9827f5ae606d

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
theorem _root_.solution (x : Lat ρ g) (i : Fin r) : (-x) i = -x i := rfl
end GlobalTheory.UnitaryStd
