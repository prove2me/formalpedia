-- Prove2me | solution 1 for GlobalTheory.AnArc.dualForm_re_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:32.732072+00:00
-- url     : https://prove2.me/submissions/da767b4d-9d20-4006-a010-c28c141ef762

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_dualForm_apply

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
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (r r' : A.X →+ ℂ) (M : Matrix _ _ ℝ) (hM : M = by classical exact (A.BwMat w)⁻¹) :
    (A.dualForm w r r').re = (fun i => (A.coord r i).re) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).re) +
      (fun i => (A.coord r i).im) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).im) ∧
    (A.dualForm w r r').im = (fun i => (A.coord r i).im) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).re) -
      (fun i => (A.coord r i).re) ⬝ᵥ M *ᵥ (fun i => (A.coord r' i).im) := by
  subst hM
  simp only [dualForm_apply, dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, Complex.im_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  constructor <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_ <;> simp <;> ring
end GlobalTheory.AnArc
