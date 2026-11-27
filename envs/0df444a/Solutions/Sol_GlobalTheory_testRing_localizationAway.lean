-- Prove2me | solution 1 for GlobalTheory.testRing_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:44.181301+00:00
-- url     : https://prove2.me/submissions/a3a2fe4b-22aa-4fb7-8f9e-3a6bacb2c1ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ReducedFiniteTypeIffTestRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TestRingLocalizationAway
import Theorems.Thm_GlobalTheory_reduced_finiteType_iff_testRing


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (p : TRing K) (g : p.R), ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R), IsUnit (lam g) ∧ ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T), IsUnit (ψ g) → ∃ k : p'.R →ₐ[K] T, k.comp lam = ψ := by
  intro K _ p g
  obtain ⟨h1, h2⟩ := reduced_finiteType_iff_testRing K
  obtain ⟨hft, hred⟩ := h2 p
  have hft1 : Algebra.FiniteType p.R (Localization.Away g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) _
  have hft' : Algebra.FiniteType K (Localization.Away g) := Algebra.FiniteType.trans hft hft1
  have hred' : IsReduced (Localization.Away g) :=
    isReduced_localizationPreserves (Submonoid.powers g) _ hred
  obtain ⟨p', ⟨e⟩⟩ := h1 (Localization.Away g) hft' hred'
  refine ⟨p', e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K p.R (Localization.Away g)), ?_, ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map e.symm
  · intro T _ _ ψ hψ
    have hu : ∀ y : Submonoid.powers g, IsUnit (ψ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hψ.pow n
    refine ⟨(IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := ψ) hu).comp e.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro x
    simp [IsLocalization.liftAlgHom]
end GlobalTheory
