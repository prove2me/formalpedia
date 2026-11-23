-- Prove2me | solution 1 for GlobalTheory.AnArc.shift_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:04.081218+00:00
-- url     : https://prove2.me/submissions/daf95bf9-d404-437e-8c5f-6853f8ac02d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
import Theorems.Thm_GlobalTheory_AnArc_H_smul_left


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
theorem _root_.solution (la la' : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) :
    A.shift k la (α + la'.y) (A.shift k la' α th) =
      Complex.exp (-(A.lin la' (A.P0 la) / k)) • A.shift k (la + la') α th := by
  funext z
  have h1 : z + (k : ℂ)⁻¹ • (A.P0 la).2 + (k : ℂ)⁻¹ • (A.P0 la').2 = z + (k : ℂ)⁻¹ • (A.P0 (la + la')).2 := by
    rw [map_add, Prod.snd_add, smul_add, add_assoc]
  rw [Pi.smul_apply, smul_eq_mul, shift_apply', shift_apply', shift_apply', h1, ← mul_assoc _ _ (th _), ← mul_assoc _ _ (th _)]
  congr 1
  rw [map_add A.P0, Prod.fst_add, AddMonoidHom.add_apply, map_add, lin_apply, La.add_l, Submodule.coe_add,
    H_add_left, H_add_right, H_smul_left]
  simp only [e_def, ← Complex.exp_add]
  congr 1; ring
end GlobalTheory.AnArc
