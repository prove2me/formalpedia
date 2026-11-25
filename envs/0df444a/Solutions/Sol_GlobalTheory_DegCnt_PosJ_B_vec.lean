-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.B_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:09.617169+00:00
-- url     : https://prove2.me/submissions/7995f7c2-2020-46cd-a547-1c2090bb7efa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
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
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) {j : ℕ}
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution (e d : Fin j → V) (u v : Matrix (Fin j) (Fin j) K) (a b : Fin j) :
    H.B (vec e u a) (vec d v b) = (uᵀ * (Matrix.of fun a b => H.B (e a) (d b)) * v.map star) a b := by
  simp only [vec, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.DegCnt.PosJ
