-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.localIdele_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:18.52683+00:00
-- url     : https://prove2.me/submissions/f8349e42-78a2-42fe-bb7f-6e5e33f2d974

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_finSingle_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr.Model
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))
end GlobalTheory.Mem.Chr.Model
