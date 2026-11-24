-- Prove2me | solution 1 for GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:14:17.928803+00:00
-- url     : https://prove2.me/submissions/ccbaf8a5-b278-48fd-b96c-d373962d6c55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSection
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSectionStatement
import Theorems.Thm_GlobalTheory_Frames_SecPull_existsUnique_secBC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  first | exact @GlobalTheory.Frames.SecPull.existsUnique_secBC | exact GlobalTheory.Frames.SecPull.existsUnique_secBC | (intros; apply GlobalTheory.Frames.SecPull.existsUnique_secBC <;> assumption)
end _root_.GlobalTheory.T
