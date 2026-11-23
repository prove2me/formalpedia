-- Prove2me | solution 1 for GlobalTheory.ArcConst.AlgZ.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:08.032985+00:00
-- url     : https://prove2.me/submissions/665c61d0-f546-401e-bec0-daf616e52101

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
namespace AlgZ
theorem _root_.solution {A : Type} [CommRing A] {s t : A} (h : AlgZ s) (h' : AlgZ t) : AlgZ (s - t) :=
  IsAlgebraic.sub (R := ℤ) h h'
end AlgZ
end GlobalTheory.ArcConst
