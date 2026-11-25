-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.ofSection_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:19.049829+00:00
-- url     : https://prove2.me/submissions/b33ad0e0-9562-44bc-8bba-849da93f4a1f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_isSecZ_one
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_IsSecZ_mul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_IsSecZ_pow

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
theorem _root_.solution (D T : ℕ) {L : WTZ E} {s : Rul Xo c} (hs : IsSecZ L s) :
    (ofSection D T L s).Weighted where
  Mr := by rintro f rfl; exact (hs.pow _).mul (hs.pow _)
  w := fun _ => hs
  thp := fun _ => hs.pow _
  th0 := fun _ => (hs.pow _).mul (hs.pow _)
  thk := fun _ => (hs.pow _).mul (hs.pow _)
  et := by simpa [Input.wet, ofSection] using hs
  ta1 := by simpa [Input.wG₁, ofSection] using (isSecZ_one (Xo := Xo) (c := c))
  ta2 := by
    have : (ofSection D T L s).wG₂ = 0 := sub_self _
    rw [this]; exact isSecZ_one
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
