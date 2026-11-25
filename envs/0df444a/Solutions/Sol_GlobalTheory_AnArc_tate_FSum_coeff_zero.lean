-- Prove2me | solution 1 for GlobalTheory.AnArc.tate_FSum_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:17.875904+00:00
-- url     : https://prove2.me/submissions/6a4d5a7b-03c8-4119-a3cc-b3b486901cf9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum
import Theorems.Thm_GlobalTheory_AnArc_tate_exponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (τ₀ : ℂ) (v : (tate τ₀).V) : ((tate τ₀).FSum 1 0 1 v).coeff 0 = 1 := by
  have h : (tate τ₀).level 1 0 0 = {0} := by
    ext μ
    rw [mem_level, Finset.mem_singleton]
    exact (Eq.congr_left (tate_exponent τ₀ μ)).trans (pow_eq_zero_iff (M₀ := ℤ) two_ne_zero)
  rw [coeff_FSum, h, Finset.sum_singleton]
  simp [term]
end GlobalTheory.AnArc
