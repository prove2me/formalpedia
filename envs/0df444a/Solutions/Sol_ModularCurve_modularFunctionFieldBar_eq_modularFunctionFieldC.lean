-- Prove2me | solution 1 for ModularCurve.modularFunctionFieldBar_eq_modularFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f5a52378-5ece-50e0-975f-fcfb90edcb0e

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem solution (N : ℕ) [NeZero N] :
    modularFunctionFieldBar N = modularFunctionFieldC (AlgebraicClosure ℚ) N := by

  show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      = modularFunctionFieldC (AlgebraicClosure ℚ) N
  rw [ModularCurve.laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N,
      ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
        (AlgebraicClosure ℚ) N]

  first
  | rfl
  | (show IntermediateField.adjoin (AlgebraicClosure ℚ)
        {x : LaurentSeries (AlgebraicClosure ℚ) |
          ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC (AlgebraicClosure ℚ) d}
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
        (divisorExpansionsC (AlgebraicClosure ℚ) N)
     congr 1
     ext x
     constructor
     · rintro ⟨d, hd, hdN, rfl⟩; exact ⟨d, hd, hdN, rfl⟩
     · rintro ⟨d, hd, hdN, rfl⟩; exact ⟨d, hd, hdN, rfl⟩)

end S_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC (solution)
