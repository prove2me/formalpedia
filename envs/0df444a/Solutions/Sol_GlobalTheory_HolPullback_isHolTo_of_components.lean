-- Prove2me | solution 1 for GlobalTheory.HolPullback.isHolTo_of_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:15.036906+00:00
-- url     : https://prove2.me/submissions/8193e408-980b-4c52-8fb6-f76d87d4c47c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToOfComponents
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_of_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.HolPullback
namespace GlobalTheory.HolPullback
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (Y Y' S S' : Scheme.{0}) (φ : Y' ⟶ Y) (p' : Y' ⟶ S') (p : Y ⟶ S) (f : S' ⟶ S) (a : V → (Sp ℂ ⟶ Y')), IsPullback φ p' p f → IsOpen B → IsHolTo B (fun b => a b ≫ φ) → IsHolTo B (fun b => a b ≫ p') → IsHolTo B a :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ H _ h₁ h₂ => GlobalTheory.HolFibre.isHolTo_of_isPullback H h₁ h₂
end GlobalTheory.HolPullback
