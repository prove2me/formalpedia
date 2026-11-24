-- Prove2me | solution 1 for GordanGenProof.zero_mem_gcone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:34.319979+00:00
-- url     : https://prove2.me/submissions/059cdaa1-16a7-4421-b9c0-e463ce63db40

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple

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
theorem _root_.solution {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) :
    (0 : Fin n → ℚ) ∈ gcone s f :=
  ⟨0, fun _ _ => le_rfl, by simp⟩
end GordanGenProof
