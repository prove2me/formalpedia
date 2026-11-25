-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi_vv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:58.979075+00:00
-- url     : https://prove2.me/submissions/49e52ec1-911d-4ac2-a6bb-4a695e254e36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_OnePlusPowerAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam
namespace GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
theorem _root_.solution (k : Type) [Field k] (l : ℕ) [Fact l.Prime] : phiPi k l (vv k) = vv k ^ l := by
  unfold phiPi vv
  erw [HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]
  simp [HahnSeries.single_pow]
end GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters
