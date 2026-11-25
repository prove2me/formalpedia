-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.pair_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:49.157809+00:00
-- url     : https://prove2.me/submissions/71020499-2e8c-4854-bb7c-559fe1d17559

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_pair_int
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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (𝔫 : Ideal (𝓞 K)) (hn : ∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) {x y : V}
    (hx : x ∈ Pst N) (hy : y ∈ 𝔫 • N.P0) : ∃ m ∈ 𝔫, (m : K) = H.B x y := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro c hc v hv
    obtain ⟨k, hk⟩ := Submodule.mem_one.1 (pair_int N hx hv)
    obtain ⟨c', hc', hc'e⟩ := hn c hc
    refine ⟨c' * k, Ideal.mul_mem_right _ _ hc', ?_⟩
    rw [← algebraMap_smul K c v, LinearMap.map_smulₛₗ, smul_eq_mul, ← hk, starRingEnd_apply]
    change algebraMap (𝓞 K) K (c' * k) = _
    rw [map_mul]
    congr 1
    all_goals exact hc'e
  · rintro a b ⟨m1, hm1, e1⟩ ⟨m2, hm2, e2⟩
    refine ⟨m1 + m2, Ideal.add_mem _ hm1 hm2, ?_⟩
    rw [map_add, ← e1, ← e2]
    simp
end GlobalTheory.DegCnt.LiftS
