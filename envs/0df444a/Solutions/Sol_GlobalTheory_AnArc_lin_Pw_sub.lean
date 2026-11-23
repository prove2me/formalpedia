-- Prove2me | solution 1 for GlobalTheory.AnArc.lin_Pw_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:18:14.691662+00:00
-- url     : https://prove2.me/submissions/2db51198-7115-4b65-a84b-5d8ddc7ebe7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_H_sub_H
import Theorems.Thm_GlobalTheory_AnArc_EF_apply


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
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (la la' : A.La) :
    A.lin la (A.Pw w la') - A.lin la' (A.Pw w la) = -(2 * Real.pi * Complex.I * A.EF la la') := by
  have h2 := A.H_sub_H la.l la'.l
  have hI := Complex.I_ne_zero
  simp only [lin_apply, Pw_snd, Pw_fst_apply, H_add_left, EF_apply, A.T_symm la'.y la.y, A.be_symm la'.y la.y]
  push_cast
  have h3 : ∀ x : ℂ, x / (2 * Complex.I) = -(Complex.I * x / 2) := fun x => by
    field_simp; simp
  simp only [h3]
  linear_combination (-Real.pi : ℂ) * h2 +
    (Real.pi * (A.H (A.ct la'.y) la.l - A.H (A.ct la.y) la'.l) : ℂ) * Complex.I_mul_I
end GlobalTheory.AnArc
