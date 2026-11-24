-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.IsSecZ.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:34.565213+00:00
-- url     : https://prove2.me/submissions/debe863b-bdba-466c-a815-e5afd9a115ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_isSecZ_one
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_IsSecZ_mul

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
namespace IsSecZ
theorem _root_.solution {G : WTZ E} {f : Rul Xo c} (hf : IsSecZ G f) (k : ℕ) : IsSecZ (k • G) (f ^ k) := by
  induction k with
  | zero => simpa using isSecZ_one
  | succ k ih => rw [succ_nsmul, pow_succ]; exact ih.mul hf
end IsSecZ
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
