-- Prove2me | solution 1 for GlobalTheory.AnArc.dualForm_BwC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:12.27538+00:00
-- url     : https://prove2.me/submissions/5b2425a2-bada-4bd9-ae06-6c49383ba0cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_Bw_symm
import Theorems.Thm_GlobalTheory_AnArc_BwMat_apply
import Theorems.Thm_GlobalTheory_AnArc_map_eq_sum_repr
import Theorems.Thm_GlobalTheory_AnArc_dualForm_apply
import Theorems.Thm_GlobalTheory_AnArc_coord_apply


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
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) (r : A.X →+ ℂ) (y : A.X) :
    A.dualForm w r (A.BwC w y) = r y := by
  classical
  have h1 : star (A.coord (A.BwC w y)) =
      ((A.BwMat w).map Complex.ofReal) *ᵥ fun i => ((Module.Free.chooseBasis ℤ A.X).repr y i : ℂ) := by
    funext i
    rw [Pi.star_apply, coord_apply, BwC_apply, Bw_symm, A.map_eq_sum_repr (A.Bw w _) y]
    simp [mulVec, dotProduct, BwMat_apply, mul_comm]
  have h2 : (A.BwMat w)⁻¹.map Complex.ofReal * (A.BwMat w).map Complex.ofReal = 1 := by
    have := Matrix.map_mul (f := Complex.ofRealHom) (L := (A.BwMat w)⁻¹) (M := A.BwMat w)
    rw [nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hw.isUnit), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  rw [dualForm_apply, h1, mulVec_mulVec, h2, one_mulVec, A.map_eq_sum_repr r y]
  simp [dotProduct, coord_apply, mul_comm]
end GlobalTheory.AnArc
