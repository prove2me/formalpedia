-- Prove2me | solution 1 for GlobalTheory.ZJ.isPullback_of_comp_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:51.321629+00:00
-- url     : https://prove2.me/submissions/be3c6fb3-eb34-4f7b-94d9-03bf0435d48b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution {𝒞 : Type*} [Category 𝒞] {A G P U Z : 𝒞} {a : A ⟶ G} {i : G ⟶ P} [Mono i]
    {s : A ⟶ U} {t : P ⟶ Z} {u : U ⟶ Z} (h : IsPullback (a ≫ i) s t u) : IsPullback a s (i ≫ t) u :=
  ⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift (c.fst ≫ i) c.snd (by rw [Category.assoc, c.condition]))
    (fun c ↦ by rw [← cancel_mono i, Category.assoc, h.lift_fst]) (fun c ↦ h.lift_snd _ _ _)
    (fun c m h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, ← Category.assoc, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩
end GlobalTheory.ZJ
