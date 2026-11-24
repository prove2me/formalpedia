-- Prove2me | solution 1 for GlobalTheory.isSymm_phSym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:41.663935+00:00
-- url     : https://prove2.me/submissions/756ffb6d-f3ad-41f9-8a6d-4a85ba788154

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
theorem _root_.solution (x : Matrix (Fin g) (Fin g) ℂ) : (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x).IsSymm := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  ext i j
  simp only [transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring
end _root_.GlobalTheory
end GlobalTheory
