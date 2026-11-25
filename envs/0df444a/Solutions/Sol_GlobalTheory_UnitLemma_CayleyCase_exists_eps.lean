-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.exists_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:53.305804+00:00
-- url     : https://prove2.me/submissions/6681f651-7463-4ceb-a4b3-0445001fff11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution (K : UQ) : ∃ ε : K.O, IsUnit ε ∧ K.c (algebraMap K.O K.E ε) = -algebraMap K.O K.E ε := by
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  refine ⟨x - y, ?_, ?_⟩
  · by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  · have : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
    simp only [map_sub, hxy, this]; ring
end GlobalTheory.UnitLemma.CayleyCase
