-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.antitone_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:54.50338+00:00
-- url     : https://prove2.me/submissions/e9250961-b93a-4710-80d9-c307d17759d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution {a : (E →+* ℂ) × ℕ → ℕ} (h : RowsDominant Dw a) (τ : E →+* ℂ) :
    Antitone fun i => trunc Dw a (τ, i) := by
  intro i j hij
  simp only [trunc]
  split_ifs with hj hi hi
  · exact h τ (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  · omega
  · exact Nat.zero_le _
  · exact le_rfl
end GlobalTheory.ThetaClaimsCompare
