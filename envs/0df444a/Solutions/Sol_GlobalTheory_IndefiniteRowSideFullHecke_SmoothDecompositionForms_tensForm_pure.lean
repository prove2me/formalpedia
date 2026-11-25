-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.tensForm_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:58.944033+00:00
-- url     : https://prove2.me/submissions/7c42d92d-a7f0-4472-8993-f81f634e7960

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms

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
theorem _root_.solution (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : ι → ℂ) (v w : H) : tensForm A (pureT a v) (pureT b w) = herm A a b * ⟪w, v⟫_ℂ := by
  simp only [tensForm, pureT, herm, dotProduct, Matrix.mulVec, inner_smul_left, inner_smul_right, Finset.sum_mul,
    Finset.mul_sum, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
