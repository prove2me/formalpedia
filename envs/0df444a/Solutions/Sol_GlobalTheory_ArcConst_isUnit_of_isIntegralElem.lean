-- Prove2me | solution 1 for GlobalTheory.ArcConst.isUnit_of_isIntegralElem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:01.542581+00:00
-- url     : https://prove2.me/submissions/77983243-fbd6-4514-906b-54695c85381f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
namespace GlobalTheory.ArcConst
theorem _root_.solution {K A : Type} [Field K] [CommRing A] [IsDomain A] (f : K →+* A)
    {s : A} (hs : f.IsIntegralElem s) (h0 : s ≠ 0) : IsUnit s := by
  let := f.toAlgebra
  exact IsIntegral.isUnit (R := K) hs h0
end GlobalTheory.ArcConst
