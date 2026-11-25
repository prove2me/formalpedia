-- Prove2me | solution 1 for GlobalTheory.DegCnt.GlueZ.Good.proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:26.620812+00:00
-- url     : https://prove2.me/submissions/80de2c65-98f0-4981-a7ff-83a9f3709c38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardInnerLatticesWithDefiniteTraceLeNorm
import Theorems.Thm_GlobalTheory_DegCnt_GlueZ_Good_z_mem
import Theorems.Thm_GlobalTheory_DegCnt_GlueZ_Good_int
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.GlueZ
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}
namespace GlobalTheory.DegCnt.GlueZ
namespace Good
theorem _root_.solution (h : Good H S z M) {y m : V} (hy : y ∈ M) (hy1 : H.B y z = 1) (hm : m ∈ M) :
    ∃ a : 𝓞 K, m - a • y ∈ M ∧ H.B (m - a • y) z = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hm h.z_mem)
  refine ⟨a, M.sub_mem hm (M.smul_mem a hy), ?_⟩
  rw [← algebraMap_smul K a y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy1, ← ha]
  simp
end Good
end GlobalTheory.DegCnt.GlueZ
