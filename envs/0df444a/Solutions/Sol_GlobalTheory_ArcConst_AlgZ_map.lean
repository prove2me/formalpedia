-- Prove2me | solution 1 for GlobalTheory.ArcConst.AlgZ.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:21:50.117384+00:00
-- url     : https://prove2.me/submissions/159b7883-080a-409b-8c6e-35b89259e8b3

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
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {s : A} (h : AlgZ s) : AlgZ (f s) :=
  IsAlgebraic.algHom f.toIntAlgHom h
end AlgZ
end GlobalTheory.ArcConst
