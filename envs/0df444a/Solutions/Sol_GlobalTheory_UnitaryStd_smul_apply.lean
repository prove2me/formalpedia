-- Prove2me | solution 1 for GlobalTheory.UnitaryStd.smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:11.873422+00:00
-- url     : https://prove2.me/submissions/c703c89d-dbc8-47b1-8768-70fa2af7f2da

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
theorem _root_.solution (a : 𝓞 E) (x : Lat ρ g) (i : Fin r) : (a • x) i = ∑ j, ρ a i j • x j := rfl
end GlobalTheory.UnitaryStd
