-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.exists_twists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:58:53.7515+00:00
-- url     : https://prove2.me/submissions/1e371202-6de6-4037-a8c4-9f5d6e3187ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_exists_inv_sabMap
import Theorems.Thm_GlobalTheory_Moduli_LevelAction_exists_comp_sabMap

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
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.Moduli.LevelAction
theorem _root_.solution {l : Level H} (Xo : Moduli D l) (g : Sim D) (hred : IsReduced Xo.X)
    (i : SABMap Xo.univ.t Xo.univ.t (𝟙 _)) (hi : i.φ = 𝟙 _)
    (o' : Obj D l (baseKA l) Xo.s) (m : SABMap o'.t Xo.univ.t (𝟙 _))
    (h₁ : ∀ a, (o'.eta a).left ≫ m.φ = (Xo.univ.eta (g.f l.M a)).left)
    (h₂ : ∀ a, (o'.etaA a).left ≫ m.φ = (Xo.univ.etaA (g.f l.A a)).left) : ∃ f, Twists Xo g f := by
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ Xo.s hred o'
  obtain ⟨k, hk⟩ := exists_inv_sabMap m i hi
  obtain ⟨ν, hν⟩ := exists_comp_sabMap k n.toSABMap (Category.id_comp f)
  refine ⟨f, hf, ν, fun a => ?_, fun a => ?_⟩
  · rw [hν, ← h₁, Category.assoc, ← Category.assoc m.φ, hk, Category.id_comp]; exact n.eta a
  · rw [hν, ← h₂, Category.assoc, ← Category.assoc m.φ, hk, Category.id_comp]; exact n.etaA a
end GlobalTheory.Moduli.LevelAction
