-- Prove2me | solution 1 for ModularCurve.heckeOperatorOneBar_comm_diamondOneBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ded9ecf7-a0c5-539f-bd4d-55d64070f73d

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut ModularCurve

theorem solution (M : ℕ) [NeZero M] (ℓ : Nat.Primes) (d : ℕ) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.diamondOneBar M d =
      ModularCurve.diamondOneBar M d * ModularCurve.heckeOperatorOneBar M ℓ := by
  haveI hℓ : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, heckeOperatorOneBar_apply, diamondOneBar_apply]
  by_cases h : HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorOneAlong_eq h0 hα hβ hFI hfin hN]
    obtain ⟨τ, hτα, hτβ⟩ := exists_algEquiv_intertwinesAlong_diamondAutBar M ℓ d
    exact SemilinearAut.pic0_correspondence_smul (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
      (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hβ hα hFI hfin hN hτβ hτα x
  · rw [heckeOperatorOneAlong_of_not h]
    simp

end S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar
end P2MW
export P2MW.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar (solution)
