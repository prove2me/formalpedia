-- Prove2me | solution 1 for GlobalTheory.PullHermitian.hermForm_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:23.833933+00:00
-- url     : https://prove2.me/submissions/f3cabc6b-ce20-41ac-b67e-c9ffd971854f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
namespace GlobalTheory.PullHermitian
theorem _root_.solution {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ) (a b : ℂ) (z w : Fin g → ℂ) :
    hermForm (a • H - b • H') z w = a * hermForm H z w - b * hermForm H' z w := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec]
end GlobalTheory.PullHermitian
