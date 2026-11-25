-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.exists_inv_sabMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:18.020242+00:00
-- url     : https://prove2.me/submissions/07a3fbc8-5b5b-4ab8-bb1c-834c784ea5f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabCancel


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
theorem _root_.solution {S : Scheme.{0}} {t t' : SAB H S} (m : SABMap t' t (𝟙 S)) (i : SABMap t t (𝟙 S))
    (hi : i.φ = 𝟙 _) : ∃ k : SABMap t t' (𝟙 S), m.φ ≫ k.φ = 𝟙 _ := by
  have i' : {n : SABMap t t (𝟙 S ≫ 𝟙 S) // n.φ = 𝟙 _} := by
    rw [Category.comp_id]; exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m i'.1
  rw [i'.2] at hk
  refine ⟨k, ?_⟩
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [← cancel_mono m.φ, Category.assoc, ← hk, Category.comp_id, Category.id_comp]
end GlobalTheory.Moduli.LevelAction
