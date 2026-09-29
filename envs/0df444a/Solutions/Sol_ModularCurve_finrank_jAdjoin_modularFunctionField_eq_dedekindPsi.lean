-- Prove2me | solution 1 for ModularCurve.finrank_jAdjoin_modularFunctionField_eq_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a3867f15-63bb-590f-aef2-a879d84c52d0

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_jAdjoin_modularFunctionField_eq_dedekindPsi
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IntermediateField

noncomputable section

namespace S12H3

variable (N : ℕ) [NeZero N]

local notation "𝔽" => (ModularCurve.modularFunctionField N : Type)
local notation "𝕃" => (ℚ⟮ModularCurve.jq⟯ : Type)

attribute [local instance] ModularCurve.jAdjoinAlgebra

theorem finrank_jAdjoin : Module.finrank 𝕃 𝔽 = ModularCurve.dedekindPsi N := by
  have hmem : ∀ x : LaurentSeries ℚ, x ∈ ModularCurve.modularFunctionField N ↔
      x ∈ IntermediateField.adjoin 𝕃 ({ModularCurve.jqN N} : Set (LaurentSeries ℚ)) := by
    intro x
    constructor
    · intro hx
      have hx' : x ∈ (ModularCurve.modularFunctionField N).toSubfield := hx
      rw [ModularCurve.modularFunctionField, IntermediateField.adjoin_toSubfield] at hx'
      refine (Subfield.closure_le.mpr ?_) hx'
      rintro y (⟨r, rfl⟩ | hy)
      · rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem _ r
      · rcases hy with rfl | rfl
        · exact (IntermediateField.adjoin 𝕃 ({ModularCurve.jqN N} : Set (LaurentSeries ℚ))).algebraMap_mem
            ⟨ModularCurve.jq, IntermediateField.mem_adjoin_simple_self ℚ ModularCurve.jq⟩
        · exact IntermediateField.mem_adjoin_simple_self _ (ModularCurve.jqN N)
    · intro hx
      have hx' : x ∈ (IntermediateField.adjoin 𝕃 ({ModularCurve.jqN N} : Set (LaurentSeries ℚ))).toSubfield := hx
      rw [IntermediateField.adjoin_toSubfield] at hx'
      refine (Subfield.closure_le.mpr ?_) hx'
      rintro y (⟨z, rfl⟩ | rfl)
      · exact ModularCurve.adjoin_jq_le N z.2
      · exact ModularCurve.jqN_mem N
  let e : (IntermediateField.adjoin 𝕃 ({ModularCurve.jqN N} : Set (LaurentSeries ℚ))) ≃+* 𝔽 :=
    { toFun := fun x => ⟨(x : LaurentSeries ℚ), (hmem _).mpr x.2⟩
      invFun := fun y => ⟨(y : LaurentSeries ℚ), (hmem _).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let eₐ : (IntermediateField.adjoin 𝕃 ({ModularCurve.jqN N} : Set (LaurentSeries ℚ))) ≃ₐ[𝕃] 𝔽 :=
    AlgEquiv.ofRingEquiv (f := e) fun _ => Subtype.ext rfl
  rw [← eₐ.toLinearEquiv.finrank_eq]
  exact ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi N

end S12H3

end

theorem solution (N : ℕ) [NeZero N] :
    @Module.finrank ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) _ _
      (ModularCurve.jAdjoinAlgebra N).toModule = ModularCurve.dedekindPsi N := by
  exact S12H3.finrank_jAdjoin N

end S_ModularCurve_finrank_jAdjoin_modularFunctionField_eq_dedekindPsi
end P2MW
export P2MW.S_ModularCurve_finrank_jAdjoin_modularFunctionField_eq_dedekindPsi (solution)
