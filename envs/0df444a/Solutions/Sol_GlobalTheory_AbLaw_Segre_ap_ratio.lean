-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.ap_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:07.128795+00:00
-- url     : https://prove2.me/submissions/43e0c57d-48ae-4ef9-b77c-937ebe87b8f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution {U V : X.Opens} {x y : Γ(X, V)} {r : Γ(X, U)}
    (e : rs X (inf_le_right : U ⊓ V ≤ V) x =
      rs X (inf_le_left : U ⊓ V ≤ U) r * rs X (inf_le_right : U ⊓ V ≤ V) y)
    {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ p ⁻¹ᵁ V) :
    ap p h₂ x = ap p h₁ r * ap p h₂ y := by
  have e' := congrArg (ap p (le_pre p h₁ h₂)) e
  simpa only [ap_rs, map_mul] using e'
end GlobalTheory.AbLaw.Segre
