-- Prove2me | solution 1 for GlobalTheory.ArcConst.isIntegralElem_of_isAlgebraic_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:21:50.109627+00:00
-- url     : https://prove2.me/submissions/f72084ff-44df-4fcd-ab0e-f5cc5a9dcdcc

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
theorem _root_.solution {K A : Type} [Field K] [CharZero K] [CommRing A] (f : K →+* A)
    {s : A} (hs : AlgZ s) : f.IsIntegralElem s := by
  let := f.toAlgebra
  have h : IsAlgebraic K s := IsAlgebraic.extendScalars (R := ℤ) (A_alg := hs) (RingHom.injective_int (algebraMap ℤ K))
  exact h.isIntegral
end GlobalTheory.ArcConst
