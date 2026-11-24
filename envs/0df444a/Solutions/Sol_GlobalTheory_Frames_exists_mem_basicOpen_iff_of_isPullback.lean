-- Prove2me | solution 1 for GlobalTheory.Frames.exists_mem_basicOpen_iff_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:33:34.495731+00:00
-- url     : https://prove2.me/submissions/48667baf-23f5-4b4c-a0a5-6fdcf0ec74ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionNonvanishingIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution {P X Y Z : Scheme.{0}} {pm : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ Z}
    {f : Y ⟶ Z} (hP : IsPullback pm g' g f) {J : Type} (U : J → X.Opens) (U' : J → P.Opens)
    (hU : ∀ i, U' i = pm ⁻¹ᵁ U i) (s : ∀ i, Γ(X, U i)) (s' : ∀ i, Γ(P, U' i))
    (hs : ∀ i, (pm.appLE _ _ (hU i).le).hom (s i) = s' i) (p' : Y) :
    (∃ (q : P) (i : J), g' q = p' ∧ q ∈ P.basicOpen (s' i)) ↔
      ∃ (q : X) (i : J), g q = f p' ∧ q ∈ X.basicOpen (s i) := by
  have key : ∀ (i : J) (q : P), q ∈ P.basicOpen (s' i) ↔ pm q ∈ X.basicOpen (s i) := by
    intro i q
    have e := Scheme.basicOpen_appLE pm (U' i) (U i) (hU i).le (s i)
    have e' : P.basicOpen (s' i) = U' i ⊓ pm ⁻¹ᵁ (X.basicOpen (s i)) := by
      rw [← hs i]; exact e
    rw [e']
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hU i]
    exact X.basicOpen_le (s i) h
  constructor
  · rintro ⟨q, i, rfl, hq⟩
    refine ⟨pm q, i, ?_, (key i q).1 hq⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hP.w]
  · rintro ⟨q, i, hq, hq'⟩
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback hP q p' hq
    exact ⟨z, i, hz, (key i z).2 hq'⟩
end GlobalTheory.Frames
