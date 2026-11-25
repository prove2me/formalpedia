-- Prove2me | solution 1 for GlobalTheory.Per.prime_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:57.322025+00:00
-- url     : https://prove2.me/submissions/7142b69c-0eee-44c7-8969-26948308a07c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
import Theorems.Thm_GlobalTheory_Per_X_dvd_ev_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per
variable {O : Type} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {L : Type} [Field L] [Algebra O L]
namespace GlobalTheory.Per
theorem _root_.solution (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w) :
    Prime (PowerSeries.X - PowerSeries.C x : PowerSeries O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp at h1
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hx
  · intro a b h
    rw [← X_dvd_ev_iff hinj hx ev hev, map_mul] at h
    rw [← X_dvd_ev_iff hinj hx ev hev a, ← X_dvd_ev_iff hinj hx ev hev b]
    exact PowerSeries.X_prime.2.2 _ _ h
end GlobalTheory.Per
