-- Prove2me | solution 1 for GordanGenProof.mem_gcone_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:30.733723+00:00
-- url     : https://prove2.me/submissions/57ce2d22-710c-46d2-8fff-cf9625945144

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
import Theorems.Thm_GordanGenProof_zero_mem_gcone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} (x : Fin n → ℚ) :
    x ∈ gcone (∅ : Finset (Fin n → ℚ)) id ↔ x = 0 := by
  constructor
  · rintro ⟨c, -, hx⟩
    simpa using hx
  · rintro rfl
    exact zero_mem_gcone _ _
end GordanGenProof
