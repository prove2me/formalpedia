-- Prove2me | solution 1 for GlobalTheory.Per.X_dvd_ev_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:00.224912+00:00
-- url     : https://prove2.me/submissions/8f33320a-1215-4b5d-87c6-ab4564fd2fe1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProdPrimePowDvd
import Theorems.Thm_GlobalTheory_Per_exists_div_X_sub_C
import Theorems.Thm_GlobalTheory_Per_ev_C

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
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (a : PowerSeries O) :
    PowerSeries.X ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  constructor
  · intro h
    obtain ⟨b, c, rfl⟩ := exists_div_X_sub_C x hx a
    rw [map_add, map_mul, hXev, ev_C] at h
    have h2 : PowerSeries.X ∣ PowerSeries.C (algebraMap O L c) :=
      (dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).1 h
    rw [PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C] at h2
    have hc : c = 0 := hinj (by rw [h2, map_zero])
    subst hc
    rw [map_zero, add_zero]
    exact dvd_mul_right _ _
  · rintro ⟨b, rfl⟩
    rw [map_mul, hXev, mul_assoc]
    exact dvd_mul_right _ _
end GlobalTheory.Per
