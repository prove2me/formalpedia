-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.IsSecZ.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:12.797328+00:00
-- url     : https://prove2.me/submissions/7ab30b31-d72b-407a-bd6d-4c415982b646

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
import Theorems.Thm_Formalism_L2_Pj_exZ_add


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
theorem _root_.solution {G G' : WTZ E} {f g : Rul Xo c} (hf : IsSecZ G f) (hg : IsSecZ G' g) :
    IsSecZ (G + G') (f * g) := by
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · show f q z * g q z = φ (f p y * g p y)
    rw [hf.1 p q φ y z h, hg.1 p q φ y z h, map_mul]
  · show f p y' * g p y' = _ * (f p y * g p y)
    rw [hf.2 p t y y' h, hg.2 p t y y' h]
    simp only [exZ_add, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
    ring
end IsSecZ
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
