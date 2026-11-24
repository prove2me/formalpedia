-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.norm_int_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:56.272479+00:00
-- url     : https://prove2.me/submissions/9bef67c9-4c23-46ee-9112-2783335e924a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_int_le_one
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_val_R


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) (ho : o ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ = 1 := by
  refine le_antisymm (norm_int_le_one v o) (not_lt.1 fun h => ho ?_)
  rw [Valued.toNormedField.norm_lt_one_iff] at h
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v o
  rw [show algebraMap F (v.adicCompletion F) (o : F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F o) from rfl,
    e] at h
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v o).1 h
end GlobalTheory.HeckeSplitAll.Approx
