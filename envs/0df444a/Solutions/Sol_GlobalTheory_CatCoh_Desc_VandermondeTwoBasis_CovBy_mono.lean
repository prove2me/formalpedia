-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:57.842906+00:00
-- url     : https://prove2.me/submissions/ee5eae51-3672-44f7-ac0d-4b8307b9e625

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory GlobalTheory.CatCoh
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
namespace CovBy
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {Φ Ψ : C → Prop} (h : ∀ S, Φ S → Ψ S) {S : C} (hS : CovBy F Φ S) : CovBy F Ψ S := by
  obtain ⟨n, b, hb, hc⟩ := hS
  exact ⟨n, b, hb, fun i S' u hu ↦ h _ (hc i S' u hu)⟩
end CovBy
end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
