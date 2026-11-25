-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.trans_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:36.905087+00:00
-- url     : https://prove2.me/submissions/13ce2015-dfd9-4d47-9a4d-92e21bd15321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_trans_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (H : HermSpace K V) (h z : V) (T τ : K) (hT : T ≠ 0) (hT' : star T = T)
    (hτ : τ + star τ = 1) (hh : H.B h h = 0) (hz : H.B h z = 0) (zz : H.B z z = -T) (x y : V) :
    H.B (trans H h z T τ x) (trans H h z T τ y) = H.B x y := by
  have hzh : H.B z h = 0 := by rw [← H.herm h z, hz, star_zero]
  have hTi : star T⁻¹ = T⁻¹ := by rw [star_inv₀, hT']
  have hTT : T * T⁻¹ = 1 := mul_inv_cancel₀ hT
  rw [trans_apply, trans_apply]
  simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul', hTi, hh, hz, hzh, zz]
  simp only [← H.herm y h, ← H.herm y z]
  linear_combination (T⁻¹ * H.B x h * star (H.B y h)) * hτ - (T⁻¹ * H.B x h * star (H.B y h)) * hTT
end GlobalTheory.DegCnt.LiftS
