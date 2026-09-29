-- Prove2me | solution 1 for ModularCurve.laurentBaseChange_modularFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/506d7936-d4d7-5270-83b8-310c8cb62fbb

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_modularFunctionField

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionField N) = ModularCurve.modularFunctionFieldC L N := by
  apply le_antisymm
  ·

    change IntermediateField.adjoin L (⇑(coeffEmb L) '' (modularFunctionField N : Set (LaurentSeries ℚ)))
      ≤ modularFunctionFieldC L N
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq} at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        rcases hx with rfl | rfl
        · rw [coeffEmb_jq]; exact jqModC_mem L N
        · rw [show qExpand ℚ N jq = jqN N from rfl, coeffEmb_jqN]; exact jqNModC_mem L N
    | algebraMap c =>
        have h : (coeffEmb L).comp (algebraMap ℚ (LaurentSeries ℚ))
            = (algebraMap L (LaurentSeries L)).comp (algebraMap ℚ L) := RingHom.ext_rat _ _
        have hc := congrArg (fun f : ℚ →+* LaurentSeries L => f c) h
        simp only [RingHom.coe_comp, Function.comp_apply] at hc
        simp only [SetLike.mem_coe, hc]
        exact (modularFunctionFieldC L N).algebraMap_mem _
    | add x y _ _ hx hy => simpa only [SetLike.mem_coe, map_add] using add_mem hx hy
    | inv x _ hx => simpa only [SetLike.mem_coe, map_inv₀] using inv_mem hx
    | mul x y _ _ hx hy => simpa only [SetLike.mem_coe, map_mul] using mul_mem hx hy
  ·
    change IntermediateField.adjoin L {jqModC L, jqNModC L N}
      ≤ IntermediateField.adjoin L (⇑(coeffEmb L) '' (modularFunctionField N : Set (LaurentSeries ℚ)))
    apply IntermediateField.adjoin.mono
    rintro _ (rfl | rfl)
    · exact ⟨jq, jq_mem N, coeffEmb_jq L⟩
    · exact ⟨qExpand ℚ N jq, jqN_mem N, coeffEmb_jqN L N⟩

end S_ModularCurve_laurentBaseChange_modularFunctionField
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_modularFunctionField (solution)
