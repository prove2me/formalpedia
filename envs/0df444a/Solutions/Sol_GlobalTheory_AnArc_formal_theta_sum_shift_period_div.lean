-- Prove2me | solution 1 for GlobalTheory.AnArc.formal_theta_sum_shift_period_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:54.094515+00:00
-- url     : https://prove2.me/submissions/2fb24a4a-b0b9-49bb-b60f-f4c3a721724b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add_P0_div
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum


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
theorem _root_.solution {la : A.La} (hy : la.y = 0) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum k α th (v + (k : ℂ)⁻¹ • A.P0 la) = Complex.exp (A.lin la v) • A.FSum k α (A.shift k la α th) v := by
  ext n
  simp only [coeff_FSum, HahnSeries.coeff_smul, smul_eq_mul, term_add_P0_div, hy, add_zero, Finset.mul_sum]
end GlobalTheory.AnArc
