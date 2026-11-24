-- Prove2me | solution 1 for GlobalTheory.SympModN.omegaStd_single_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:02:44.209638+00:00
-- url     : https://prove2.me/submissions/815f2c91-0f81-4ae5-b0eb-1d5daa051e62

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
    omegaStd a (Pi.single (.inl i) 1) = -a (.inr i) := by
  simp [omegaStd, Pi.single_apply]
end GlobalTheory.SympModN
