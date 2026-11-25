-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.herm_dualGram_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:49.494933+00:00
-- url     : https://prove2.me/submissions/7ef08d34-6f18-40d8-861d-7251236851f7

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
theorem _root_.solution [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : Aᴴ = A) (h2 : A * A = 1) (y y' : ι → ℂ) :
    herm (dualGram A) (flat A y) (flat A y') = herm A y' y := by
  have hinv : A⁻¹ = A := Matrix.inv_eq_left_inv h2
  have h1 : star (star y' ᵥ* A) = A *ᵥ y' := by
    rw [Matrix.star_vecMul, hA, star_star]
  unfold herm dualGram flat
  rw [hinv, h1, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one, dotProduct_comm]
end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
