-- Prove2me | solution 1 for GlobalTheory.StdChar.exists_stdChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:47.491993+00:00
-- url     : https://prove2.me/submissions/202b4fb9-fd54-4c5c-8bd6-cc113f767dda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Theorems.Thm_GlobalTheory_StdChar_ce_eq_one
import Theorems.Thm_GlobalTheory_StdChar_mem_intSub
import Theorems.Thm_GlobalTheory_StdChar_exists_unif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
variable {F : Type} [NontriviallyNormedField F]
variable (F)
namespace GlobalTheory.StdChar
theorem _root_.solution [IsUltrametricDist F] [ProperSpace F] : ∃ ψ : AddChar F ℂ, IsStdChar ψ := by
  obtain ⟨ϖ, hϖ0, hϖ1, hle⟩ := exists_unif (F := F)
  have hpos : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hx : (QuotientAddGroup.mk ϖ⁻¹ : F ⧸ intSub F) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, mem_intSub, norm_inv, not_le]
    exact one_lt_inv_iff₀.2 ⟨hpos, hϖ1⟩
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let c' : F →+ AddCircle (1 : ℚ) := AddMonoidHom.comp c (QuotientAddGroup.mk' (intSub F))
  refine ⟨charOf c', fun x hx1 => ?_, ϖ⁻¹, fun h => hc ?_, fun y hy => ?_⟩
  · show ce (c (QuotientAddGroup.mk x)) = 1
    rw [(QuotientAddGroup.eq_zero_iff x).2 hx1, map_zero, ce_zero]
  · exact ce_eq_one h
  · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hle y hy
end GlobalTheory.StdChar
