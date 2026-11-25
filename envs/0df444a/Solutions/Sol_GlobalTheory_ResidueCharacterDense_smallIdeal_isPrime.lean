-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.smallIdeal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:44.971328+00:00
-- url     : https://prove2.me/submissions/4912dcd0-6b18-4499-9cdf-e5b60e3875fc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_mem_smallIdeal
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
theorem _root_.solution {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω]
    (σ : F →+* Ω) : (smallIdeal σ).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  mem_or_mem' := by
    intro x y h
    simp only [mem_smallIdeal] at *
    by_contra h'
    push Not at h'
    simp only [map_mul, norm_mul] at h
    nlinarith [h'.1, h'.2]
end GlobalTheory.ResidueCharacterDense
