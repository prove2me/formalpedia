-- Prove2me | solution 1 for GlobalTheory.T.frameChangeByMatrices_refl_and_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:56.071518+00:00
-- url     : https://prove2.me/submissions/7cd57604-cba2-473f-b9fd-37f05a7db98a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeByMatricesReflAndComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeByMatricesReflAndCompStatement
import Theorems.Thm_GlobalTheory_Frames_frChg_refl_and_comp


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrChg (fun _ => 1) 1 y y ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y' y'' → FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  first | exact @GlobalTheory.Frames.frChg_refl_and_comp | exact GlobalTheory.Frames.frChg_refl_and_comp | (intros; apply GlobalTheory.Frames.frChg_refl_and_comp <;> assumption)
end _root_.GlobalTheory.T
