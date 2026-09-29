-- Prove2me | solution 1 for ModularCurve.CompEq.finrank_adjoin_jBar_eq_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/de37d365-9571-5cb8-9260-a02d8e64f163

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve

theorem solution (N : ℕ) [NeZero N] :
    Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) = dedekindPsi N := by
  have hN : ((N : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)

  have key : ∀ (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
      (_hE : E = modularFunctionFieldFullC (AlgebraicClosure ℚ) N) (x : E)
      (_hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)),
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set E)) E = dedekindPsi N := by
    intro E hE x hx
    subst hE
    have hx' : x = ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) N⟩ := Subtype.ext hx
    subst hx'
    exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (AlgebraicClosure ℚ) N hN
  exact key (modularFunctionFieldBar N) (laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N)
    (jBar N) (coeffEmb_jq (AlgebraicClosure ℚ))

end S_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
end P2MW
export P2MW.S_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi (solution)
