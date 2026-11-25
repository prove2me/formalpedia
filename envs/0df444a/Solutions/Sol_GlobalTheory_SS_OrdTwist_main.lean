-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:37.653201+00:00
-- url     : https://prove2.me/submissions/34518388-c3a1-48c2-886b-2e21afada27a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Theorems.Thm_GlobalTheory_SS_OrdTwist_exists_const
import Theorems.Thm_GlobalTheory_SS_OrdTwist_app_cstR

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdTwist
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  intro R K _ _ _ _ _ _ π hπ A _ hA I _ _ D hD f
  obtain ⟨c₀, hc₀, key⟩ := exists_const hA D hD f
  obtain ⟨c, u, hc⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hc₀
  have hπ0 : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  refine ⟨c, fun M n hM => ?_⟩
  have step : ∀ (j : A.left ⟶ M.Y.left), j = f.inv.left ≫ M.j → ∀ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U))
      (s : Γ(M.Y.left, U)),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) = cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s →
      jac D (j ⁻¹ᵁ U) (fun i => (j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ (n + c)) * (j.app U).hom (cstR M U u * s) := by
    rintro j rfl U t s h
    have h1 := key (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i))
    rw [h, map_mul, app_cstK] at h1
    refine Eq.trans h1 ?_
    show _ = cstK A (f.inv.left ⁻¹ᵁ M.j ⁻¹ᵁ U) _ * (f.inv.left.app (M.j ⁻¹ᵁ U)).hom ((M.j.app U).hom (cstR M U u * s))
    rw [map_mul, map_mul, app_cstR, app_cstK, hc, zpow_add₀ hπ0, Units.smul_def, Algebra.smul_def]
    simp only [map_mul]
    ring
  have hj : (M.twist f).j = f.inv.left ≫ M.j := by simp [Model.j, Model.twist]
  refine ⟨fun U t => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hM.1 U t
    exact ⟨_, step _ hj U t s hs⟩
  · obtain ⟨U, t, s, hU, hs, h⟩ := hM.2
    exact ⟨U, t, _, hU, (u.isUnit.map _).mul hs, step _ hj U t s h⟩
end GlobalTheory.SS.OrdTwist
