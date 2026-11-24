-- Prove2me | solution 1 for GordanGenProof.mem_gcone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:30.997786+00:00
-- url     : https://prove2.me/submissions/dd4e631f-182c-4f13-b3c2-dadabd6c84e7

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
theorem _root_.solution {n : ℕ} {ι : Type*} {s : Finset ι} {f : ι → Fin n → ℚ} {i : ι} (hi : i ∈ s) :
    f i ∈ gcone s f := by
  classical
  refine ⟨fun j => if j = i then 1 else 0, fun j _ => ?_, ?_⟩
  · by_cases h : j = i <;> simp [h]
  · simp [ite_smul, hi]
end GordanGenProof
