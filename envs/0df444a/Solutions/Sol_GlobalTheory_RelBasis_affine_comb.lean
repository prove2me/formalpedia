-- Prove2me | solution 1 for GlobalTheory.RelBasis.affine_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:55:13.844751+00:00
-- url     : https://prove2.me/submissions/657b1bcd-7be6-4007-8842-f7a7070e9aee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisAffineBaseChangeOfAffine
import Theorems.Thm_GlobalTheory_RelBasis_affine_gs_appLE
import Theorems.Thm_GlobalTheory_RelBasis_comb_comp


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
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}
namespace GlobalTheory.RelBasis
theorem _root_.solution (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) (w : j ≫ p₁ = p₁' ≫ g) (e : ⊤ ≤ g ⁻¹ᵁ W)
    (c : Fin N → Γ(T, W)) (z : Y') (i : L.ι) (h₂ : p₂ (j z) ∈ L.U i) :
    comb b p₁' (j ≫ p₂) ⊤ (fun k => (g.appLE W ⊤ e).hom (c k)) z i =
      (j.stalkMap z).hom (comb b p₁ p₂ W c (j z) i) := by
  have h₁ : p₁ (j z) ∈ W := by
    have : (j ≫ p₁) z ∈ W := by rw [w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  rw [← comb_comp b j p₁ p₂ W c z i h₁ h₂, comb, comb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [affine_gs_appLE g W ⊤ e p₁' z trivial, w]
end GlobalTheory.RelBasis
