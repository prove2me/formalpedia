-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.isSecZ_wtZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:36.164738+00:00
-- url     : https://prove2.me/submissions/e9b12df3-ac1f-47d9-b764-f925fa4914dd

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
theorem _root_.solution (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    IsSecZ (wtZ a n) f ↔ f ∈ sec Xo c a n := by
  have key : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      ((∏ i, t i ^ exZ Dw (wtZ a n) i : Sˣ) : S) = wchar (ex Dw a n) t := by
    intro S _ t
    rw [wchar, Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, wtZ, ex]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [← key]; exact h2 p t y y' hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [key]; exact h2 p t y y' hb⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
