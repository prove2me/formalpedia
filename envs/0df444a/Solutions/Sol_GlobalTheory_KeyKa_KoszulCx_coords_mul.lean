-- Prove2me | solution 1 for GlobalTheory.KeyKa.KoszulCx.coords_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:53.792237+00:00
-- url     : https://prove2.me/submissions/c0ca8d23-8a8a-4635-8be0-ff83b990d918

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_ring_coords

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
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulCx
variable {R : Type} [CommRing R]
namespace GlobalTheory.KeyKa.KoszulCx
theorem _root_.solution (x : KeyIn R) {l₀ l₁ N₀ N₁ : ℕ} (b₀ : Fin N₀ → RR x l₀) (b₁ : Fin N₁ → RR x l₁)
    (M : Matrix (Fin N₀) (Fin N₁) R) (u f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) (c : Fin N₁ → R)
    (hM : ∀ k, Coords x b₀ (fun k' => M k' k) (fun i => u i * (show Γ(x.P.A.left, x.P.L.U i) from (b₁ k).f i)))
    (hc : Coords x b₁ c f) : Coords x b₀ (fun k' => ∑ k, M k' k * c k) (fun i => u i * f i) := by
  exact fun i => ring_coords (cst x.P.A.hom (x.P.L.U i)) _ _ M (u i) (f i) c (fun k => hM k i) (hc i)
end GlobalTheory.KeyKa.KoszulCx
