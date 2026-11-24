-- Prove2me | solution 1 for GlobalTheory.ArcConst.algZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:10.614187+00:00
-- url     : https://prove2.me/submissions/196cef91-8c66-40ba-826a-641da066e6c2

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
theorem _root_.solution {A : Type} [CommRing A] [inst : Algebra ℤ A] {s : A} (h : IsAlgebraic ℤ s) : AlgZ s := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact h
end GlobalTheory.ArcConst
