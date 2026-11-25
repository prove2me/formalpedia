-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.norm_nat_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:46.603663+00:00
-- url     : https://prove2.me/submissions/9b69d25b-7e99-4add-8e34-56208a4bfc69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_le_one_iff_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (natCast_mem _ m)
end GlobalTheory.HeckeSplitAll.Approx
