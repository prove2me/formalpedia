-- Prove2me | solution 1 for GlobalTheory.DiagBlock.restr_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:21.208204+00:00
-- url     : https://prove2.me/submissions/2948fbe0-ca55-4f6e-9541-ef5028556ddb

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (G : MvPowerSeries (PVar n) C) :
    restr hn G = MvPowerSeries.killCompl ⟨embV hn, embV_inj hn⟩ G := by
  ext m
  rw [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_eq_mapDomain]
  rfl
end GlobalTheory.DiagBlock
