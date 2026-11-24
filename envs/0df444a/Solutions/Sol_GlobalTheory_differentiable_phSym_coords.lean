-- Prove2me | solution 1 for GlobalTheory.differentiable_phSym_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:58.249285+00:00
-- url     : https://prove2.me/submissions/50f1499e-698a-46cc-b923-152349e43b38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
variable {g : ℕ}
open Complex Matrix
variable {g : ℕ}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    Differentiable ℂ (fun x : Fin g → Fin g → ℂ =>
      (Matrix.of.symm (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) : Fin g → Fin g → ℂ)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul]
  fun_prop
end _root_.GlobalTheory
end GlobalTheory
