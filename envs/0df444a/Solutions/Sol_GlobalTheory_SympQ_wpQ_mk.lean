-- Prove2me | solution 1 for GlobalTheory.SympQ.wpQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:20.21974+00:00
-- url     : https://prove2.me/submissions/960f3665-e330-4f68-904c-1ecb1101721b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WpQTrivRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open GlobalTheory GlobalTheory.SympQ
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.SympQ
theorem _root_.solution (k : ℕ) (p q : N.QT k) : wpQ N k (QuotientGroup.mk p) (QuotientGroup.mk q) = N.wp p q := rfl
end GlobalTheory.SympQ
