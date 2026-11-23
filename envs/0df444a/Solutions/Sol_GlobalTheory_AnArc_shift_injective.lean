-- Prove2me | solution 1 for GlobalTheory.AnArc.shift_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:57.043841+00:00
-- url     : https://prove2.me/submissions/e05e8655-fa96-4fd4-9669-938b3937d5be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_shift_shift

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
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]
namespace GlobalTheory.AnArc
theorem _root_.solution (la : A.La) (α : A.X) : Function.Injective (A.shift k la α) := by
  rw [injective_iff_map_eq_zero]
  intro th h
  have := A.shift_shift k (-la) la α th
  rw [h, map_zero, neg_add_cancel, shift_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (Complex.exp_ne_zero _)
end GlobalTheory.AnArc
