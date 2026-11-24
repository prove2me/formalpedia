-- Prove2me | solution 1 for GlobalTheory.phSym_eq_self_of_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:38.647394+00:00
-- url     : https://prove2.me/submissions/73cf2720-fcf7-4de3-84d2-2601755096bb

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
theorem _root_.solution {x : Matrix (Fin g) (Fin g) ℂ} (hx : x.IsSymm) :
    _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  rw [hx.eq, ← two_smul ℂ x, smul_smul]
  norm_num
end _root_.GlobalTheory
end GlobalTheory
