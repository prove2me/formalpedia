-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.hermForm_second_flag_X_z_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:38:59.206009+00:00
-- url     : https://prove2.me/submissions/19138a2e-cc4e-4eae-a081-7e0a14841453

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_hermFlag_isotropicPart_orthogonal_anisotropicVector
import Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_z__eq_3b4bb3d0338d
import Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution {y : V} (hy : y ∈ N.F'.X) : H.B y N.F.z = 0 := by
  have h1 : H.B y N.F'.z = 0 := hermFlag_isotropicPart_orthogonal_anisotropicVector N.F' hy
  rw [z'_eq N, map_smulₛₗ, smul_eq_mul] at h1
  have hc : starRingEnd K N.c ≠ 0 := by
    intro h
    have h2 := N.c_norm
    rw [← starRingEnd_apply, h, mul_zero] at h2
    exact zero_ne_one h2
  exact (mul_eq_zero.1 h1).resolve_left hc
end GlobalTheory.DegCnt.LiftS
