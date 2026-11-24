-- Prove2me | solution 1 for GlobalTheory.KaUnique.exists_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:07.40345+00:00
-- url     : https://prove2.me/submissions/2b693e09-d681-469f-879c-58a0a846d87a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Theorems.Thm_P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b
import Theorems.Thm_GlobalTheory_KaUnique_IsComb_single
import Theorems.Thm_GlobalTheory_KaUnique_comb_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {R : Type} [CommRing R]
namespace GlobalTheory.KaUnique
theorem _root_.solution {x : KeyIn R} {l N : ℕ} {b b' : Fin N → RR x l} (hb : IsBasis x b) (hb' : IsBasis x b') :
    ∃ B : (Matrix (Fin N) (Fin N) R)ˣ, ∀ k, IsComb x.P.A.hom x.P.L (fam x b) (fun k' => B.val k' k) (fam x b' k) := by
  choose c hc using fun k => (hb (b' k)).exists
  choose c' hc' using fun k => (hb' (b k)).exists
  have h1 : ∀ k, IsComb x.P.A.hom x.P.L (fam x b) (fun k' => (Matrix.of fun a k => c k a) k' k) (fam x b' k) := hc
  have h2 : ∀ k, IsComb x.P.A.hom x.P.L (fam x b') (fun k' => (Matrix.of fun a k => c' k a) k' k) (fam x b k) := hc'
  refine ⟨⟨Matrix.of fun a k => c k a, Matrix.of fun a k => c' k a, ?_, ?_⟩, h1⟩
  · ext a k
    exact congrFun (comb_unique hb (IsComb.mulVec' h1 (h2 k)) (IsComb.single _ k)) a
  · ext a k
    exact congrFun (comb_unique hb' (IsComb.mulVec' h2 (h1 k)) (IsComb.single _ k)) a
end GlobalTheory.KaUnique
