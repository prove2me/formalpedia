-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.toData_torsionSection_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:08.841637+00:00
-- url     : https://prove2.me/submissions/eae8613d-af5b-40df-a317-01f094235221

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_valZ_mem

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
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
theorem _root_.solution (Z : Comp Xo c) :
    (I.toData h δ fn yP).ta1 Z ∈ AG Z ((2 : ℕ) • (I.toData h δ fn yP).G1) := valZ_mem h _ _ Z
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
