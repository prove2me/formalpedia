-- Prove2me | solution 1 for GlobalTheory.obj_lower_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:17.711476+00:00
-- url     : https://prove2.me/submissions/9242229f-ec8d-4be4-a018-105b396dbe5d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l l₂ : Level H) (B : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B)
    (o₂ : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) →
    ∃ (o : Obj D l b s) (m : SABMap o₂.t o.t (𝟙 S)),
      (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left) := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o₂ h hρ hζ
  exact ⟨ObjLower.lower o₂ h hρ hζ, ObjLower.sabId o₂.t,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm,
    fun _ => (Category.comp_id _).trans (Category.id_comp _).symm⟩
end GlobalTheory
