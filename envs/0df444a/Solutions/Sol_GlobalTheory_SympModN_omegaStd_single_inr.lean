-- Prove2me | solution 1 for GlobalTheory.SympModN.omegaStd_single_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:02:45.239072+00:00
-- url     : https://prove2.me/submissions/090c82b4-44ea-47b7-b5df-f3afed1139c9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticSimilitudeInvertibleModN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SympModN
namespace GlobalTheory.SympModN
theorem _root_.solution {h : ℕ} (a : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    omegaStd a (Pi.single (.inr i) 1) = a (.inl i) := by
  simp [omegaStd, Pi.single_apply]
end GlobalTheory.SympModN
