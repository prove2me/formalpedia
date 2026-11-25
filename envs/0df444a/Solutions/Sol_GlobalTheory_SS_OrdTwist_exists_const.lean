-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:39.765171+00:00
-- url     : https://prove2.me/submissions/05061407-73f3-4c5b-bdb5-51b8bf288d92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Theorems.Thm_GlobalTheory_SS_OrdTwist_rs_jac
import Theorems.Thm_GlobalTheory_SS_OrdTwist_exists_ratio
import Theorems.Thm_GlobalTheory_SS_OrdTwist_app_jac
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_field
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth


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
theorem _root_.solution [GrpObj A] (hA : IsAbelianScheme A) (D : I → VF A) (hD : IsFrame D) (f : A ≅ A) :
    ∃ c : K, c ≠ 0 ∧ ∀ (V : A.left.Opens) (t : I → Γ(A.left, V)),
      jac D _ (fun i => (f.inv.left.app V).hom (t i)) = cstK A _ c * (f.inv.left.app V).hom (jac D V t) := by
  have : IsIso f.inv.left := inferInstanceAs (IsIso ((Over.forget _).map f.inv))
  obtain ⟨h, hh⟩ := exists_ratio D (fun i => transport f.inv (D i)) hD
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsIso A.hom.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_field A.hom
  obtain ⟨c', rfl⟩ := (ConcreteCategory.bijective_of_isIso A.hom.appTop).2 h
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 c'
  have key : ∀ (V : A.left.Opens) (t : I → Γ(A.left, V)),
      jac D _ (fun i => (f.inv.left.app V).hom (t i)) = cstK A _ c * (f.inv.left.app V).hom (jac D V t) := by
    intro V t
    rw [← app_jac, hh, map_mul, ← app_cstK f.inv V c]
    rfl
  refine ⟨c, ?_, key⟩
  rintro rfl
  obtain ⟨x⟩ : Nonempty A.left := inferInstance
  obtain ⟨U, t, hx, hu⟩ := hD.2 x
  have e : f.inv.left ⁻¹ᵁ (f.hom.left ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, f.inv_hom_id]; rfl
  have h1 := key (f.hom.left ⁻¹ᵁ U) (fun i => (appE f.inv _).symm (rs e.le (t i)))
  simp only [app_symm, map_zero, zero_mul] at h1
  have h2 := hu.map (rs e.le)
  rw [rs_jac, h1] at h2
  have : Nonempty (f.inv.left ⁻¹ᵁ (f.hom.left ⁻¹ᵁ U) : A.left.Opens) := ⟨⟨x, e.ge hx⟩⟩
  exact not_isUnit_zero h2
end GlobalTheory.SS.OrdTwist
