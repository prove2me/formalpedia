-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.isFirst_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:33.143589+00:00
-- url     : https://prove2.me/submissions/9b903b3b-565c-405b-ae56-4a5ad70b8501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {a : ℕ} {m : Fin a →₀ ℕ} (hm : m ≠ 0) : ∃ i, IsFirst m i := by
  have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
  refine ⟨m.support.min' hne, Finsupp.mem_support_iff.mp (Finset.min'_mem _ _), fun j hj => ?_⟩
  by_contra h
  exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hj)
end GlobalTheory.FiltrationMultiplicative
