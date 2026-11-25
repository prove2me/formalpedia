-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.neOnComps_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:56.54321+00:00
-- url     : https://prove2.me/submissions/47329257-6346-4818-b3de-ab7a1bc513d0

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
variable (Xo c)
variable {Xo c}
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
theorem _root_.solution (h : GenFrEx Xo c) (G : WTZ E) (f : Rul Xo c) :
    NeOnComps h f ↔ ∀ Z, valZ h G f Z ≠ 0 := by
  simp [NeOnComps, valZ]
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
