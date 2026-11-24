-- Prove2me | solution 1 for GlobalTheory.IsoLift.cls_eq_iff_modN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:06.739931+00:00
-- url     : https://prove2.me/submissions/c017ab7e-aeaa-4463-a503-a987e2b96f8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoLift
open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.IsoLift
theorem _root_.solution {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ D.ModN n (a - b) := by
  rw [Submodule.Quotient.eq, mem_nLa]
  rfl
end GlobalTheory.IsoLift
