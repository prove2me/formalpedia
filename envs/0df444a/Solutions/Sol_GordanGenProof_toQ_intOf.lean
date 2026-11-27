-- Prove2me | solution 1 for GordanGenProof.toQ_intOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:12.740838+00:00
-- url     : https://prove2.me/submissions/465df4df-0b55-42f1-afd2-25bd9546d923

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
theorem _root_.solution {n : ℕ} (v : Fin n → ℚ) : GordanCones.toQ (intOf v) = mulOf v • v :=
  (exists_int_multiple v).choose_spec.2.choose_spec
end GordanGenProof
