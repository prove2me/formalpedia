-- Prove2me | solution 1 for GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:36.997512+00:00
-- url     : https://prove2.me/submissions/b2092a80-4c82-43cf-959b-555bf429fbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescend
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isFinite
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isProper
import Theorems.Thm_GlobalTheory_IsAffineQuotient_isSeparated
import Theorems.Thm_GlobalTheory_IsAffineQuotient_locallyOfFiniteType
import Theorems.Thm_GlobalTheory_IsAffineQuotient_quasiCompact


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s' : X' ⟶ S), LocallyOfFiniteType (π ≫ s') → IsFinite π ∧ LocallyOfFiniteType s' ∧ (QuasiCompact (π ≫ s') → QuasiCompact s') ∧ (IsSeparated (π ≫ s') → IsSeparated s') ∧ (IsProper (π ≫ s') → IsProper s') := by
  intro G _ _ X X' ρ π hπ S _ s' hft
  obtain ⟨hA, hc, hV⟩ := hπ
  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hc
      isAffineHom := hA
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        intro g hg
        unfold IsInvariantSection at hs
        obtain ⟨_, e⟩ := hs g
        exact e) }
  exact ⟨hq.isFinite s', hq.locallyOfFiniteType s',
    fun _ => hq.quasiCompact s', fun _ => hq.isSeparated s', fun _ => hq.isProper s'⟩
end GlobalTheory
