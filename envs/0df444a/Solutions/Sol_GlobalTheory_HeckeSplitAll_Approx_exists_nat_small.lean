-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.exists_nat_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:42.312166+00:00
-- url     : https://prove2.me/submissions/0a3a3d61-ecb9-4587-89c2-a29a4795ff1e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_norm_natCast_lt_one
import Theorems.Thm_GlobalTheory_HeckeSplitAll_Approx_exists_finset_norm_one

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
theorem _root_.solution (x : F) (hx : x ≠ 0) : ∃ P : ℕ, P ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖algebraMap F (v.adicCompletion F) x‖ ≠ 1 → ‖(P : v.adicCompletion F)‖ < 1 := by
  classical
  obtain ⟨B, hB⟩ := exists_finset_norm_one x hx
  refine ⟨∏ v ∈ B, Ideal.absNorm v.asIdeal, ?_, fun v hv => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  · exact norm_natCast_lt_one v _ (Finset.dvd_prod_of_mem _ (by_contra fun h => hv (hB v h)))
end GlobalTheory.HeckeSplitAll.Approx
