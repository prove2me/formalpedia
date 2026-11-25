-- Prove2me | solution 1 for GlobalTheory.UnitCase.sumElim_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:58.826739+00:00
-- url     : https://prove2.me/submissions/2eb862cb-f3b0-4e9e-952c-504d6f4064d5

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution {A B A' B' : κ →₀ ℕ} (h : Finsupp.sumElim A B = Finsupp.sumElim A' B') :
    A = A' ∧ B = B' :=
  ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
    Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
end GlobalTheory.UnitCase
