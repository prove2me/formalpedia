-- Prove2me | solution 1 for GlobalTheory.HTLat.logAbs_vp_of_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:48:32.430745+00:00
-- url     : https://prove2.me/submissions/8ddb7359-dec8-4ed4-8c40-9b1c8d9a7314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
theorem _root_.solution {p : ℕ} (hp : 1 < p) (v : Valuation C ℝ≥0)
    (h : v (p : C) = (p : ℝ≥0)⁻¹) (r : ℝ≥0) : logAbs_vp p v r = Real.log r := by
  have : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [logAbs_vp, h, NNReal.coe_inv, NNReal.coe_natCast, Real.log_inv]
  field_simp
end GlobalTheory.HTLat
