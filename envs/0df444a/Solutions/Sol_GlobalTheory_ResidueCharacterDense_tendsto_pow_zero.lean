-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.tendsto_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:49.512532+00:00
-- url     : https://prove2.me/submissions/990ba518-f564-463f-accd-8a1309626405

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (z : K) (hz : valuation K z < 1) :
    Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) := by
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hz γ
  filter_upwards [eventually_ge_atTop n] with m hm
  simp only [Set.mem_setOf_eq, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hz.le hm) hn
end GlobalTheory.ResidueCharacterDense
