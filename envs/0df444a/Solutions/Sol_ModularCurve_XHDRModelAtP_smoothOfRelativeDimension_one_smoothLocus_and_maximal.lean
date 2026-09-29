-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.smoothOfRelativeDimension_one_smoothLocus_and_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0e199080-90be-5659-85ba-30229154454a

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_smoothOfRelativeDimension_one_smoothLocus_and_maximal

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel"

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    SmoothOfRelativeDimension 1 (𝔛.smoothLocus.ι ≫ (toBase p (ΓM M H) hj)) ∧
    (∀ W : (X p (ΓM M H) hj).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (toBase p (ΓM M H) hj)) → W ≤ 𝔛.smoothLocus) := by
  exact ⟨𝔛.smoothLocus_relDim, fun W hW => 𝔛.smoothLocus_maximal W (SmoothOfRelativeDimension.smooth 1 _)⟩

end S_ModularCurve_XHDRModelAtP_smoothOfRelativeDimension_one_smoothLocus_and_maximal
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_smoothOfRelativeDimension_one_smoothLocus_and_maximal (solution)
