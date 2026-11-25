-- Prove2me | solution 1 for GlobalTheory.T.frame_eq_of_baseChange_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:49.035336+00:00
-- url     : https://prove2.me/submissions/26224b39-eaca-4e12-9256-997039b27a58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameEqOfBaseChangeInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameEqOfBaseChangeInjectiveStatement
import Theorems.Thm_GlobalTheory_Frames_frPt_eq_of_frMap_injective


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
theorem _root_.solution : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (z z' : FrPt Xo c S) (w : FrPt Xo c T), Function.Injective φ → z'.x = z.x → FrMap φ z w → FrMap φ z' w → z = z' := by
  first | exact @GlobalTheory.Frames.frPt_eq_of_frMap_injective | exact GlobalTheory.Frames.frPt_eq_of_frMap_injective | (intros; apply GlobalTheory.Frames.frPt_eq_of_frMap_injective <;> assumption)
end _root_.GlobalTheory.T
