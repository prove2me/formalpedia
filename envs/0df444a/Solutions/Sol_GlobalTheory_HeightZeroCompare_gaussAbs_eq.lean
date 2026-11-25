-- Prove2me | solution 1 for GlobalTheory.HeightZeroCompare.gaussAbs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:53.167716+00:00
-- url     : https://prove2.me/submissions/b7efeb72-3766-4049-a0c9-d9106baaeabd

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SjIffJensenInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.HeightZeroCompare
open ReciprocityTheory.MultiplicativeHeights GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
namespace GlobalTheory.HeightZeroCompare
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} (w : FinitePlace K)
    (f : MvPolynomial ι K) : gaussAbs w f = gaussAbsValue w f := rfl
end GlobalTheory.HeightZeroCompare
