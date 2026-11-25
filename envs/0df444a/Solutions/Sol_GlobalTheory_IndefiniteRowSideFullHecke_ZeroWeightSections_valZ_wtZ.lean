-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.valZ_wtZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:10.955593+00:00
-- url     : https://prove2.me/submissions/b8f32945-3301-4650-aa24-6302f150244e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
theorem _root_.solution (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    valZ h (wtZ a n) f = valC h a n f := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
