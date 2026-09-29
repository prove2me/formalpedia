-- Prove2me | solution 1 for LanglandsTunnell.finrank_fixFld_sylowH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d51ace40-e3c3-5d36-ae62-7c7bb774a68d

import Mathlib
import Definitions.Def_LanglandsTunnell_C8Tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_finrank_fixFld_sylowH

set_option autoImplicit false

open NumberField LanglandsTunnell

theorem card_GL2_F3_aux : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [ZMod.card, Fin.prod_univ_two]

theorem solution {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(fixFld (sylowH e)) = 3 := by
  have h16 : Module.finrank ↥(fixFld (sylowH e)) L = 16 := by
    rw [show fixFld (sylowH e) = IntermediateField.fixedField (sylowH e) from rfl,
      IntermediateField.finrank_fixedField_eq_card, card_sylowH]
  have h48 : Module.finrank ℚ L = 48 := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, card_GL2_F3_aux]
  have htower := Module.finrank_mul_finrank ℚ ↥(fixFld (sylowH e)) L
  rw [h16, h48] at htower
  omega

end S_LanglandsTunnell_finrank_fixFld_sylowH
end P2MW
export P2MW.S_LanglandsTunnell_finrank_fixFld_sylowH (solution)
