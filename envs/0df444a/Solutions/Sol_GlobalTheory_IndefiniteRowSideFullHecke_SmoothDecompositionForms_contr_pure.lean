-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.contr_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:47.366498+00:00
-- url     : https://prove2.me/submissions/3d56333c-73d7-4762-a544-d0f179672cd2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmoothDecompositionForms_flat_dotProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete
variable {k r : ℕ}
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
theorem _root_.solution (A : Matrix ι ι ℂ) (ω a : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (v : E) :
    contr A ω (pureT a v) = herm A a ω • v := by
  simp only [contr, pureT, smul_smul, ← Finset.sum_smul, ← flat_dotProduct, dotProduct]
end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
