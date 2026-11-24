-- Prove2me | solution 1 for GlobalTheory.AnArc.norm_ah
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:49.121811+00:00
-- url     : https://prove2.me/submissions/d46bd0c3-3903-442b-a261-dba4c2c7b96c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (l : A.abelian₂) (z : Fin A.gB → ℂ) :
    ‖A.ah l z‖ = Real.exp (Real.pi * (A.H z l).re + Real.pi / 2 * (A.H l l).re) := by
  rw [ah, norm_mul, A.chi_norm, one_mul, Complex.norm_exp]
  congr 1
  rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by simp, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
end GlobalTheory.AnArc
