-- Prove2me | solution 1 for GlobalTheory.VVRank.exists_geomPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:46.739896+00:00
-- url     : https://prove2.me/submissions/cbc0ce29-c56a-4e53-8e04-618ef62825ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution (X : Scheme.{0}) [IsAffine X] (𝔪 : Ideal Γ(X, ⊤)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Spec (CommRingCat.of K) ⟶ X),
      ∀ r, u.appTop.hom r = 0 ↔ r ∈ 𝔪 := by
  letI := Ideal.Quotient.field 𝔪
  let K := AlgebraicClosure (Γ(X, ⊤) ⧸ 𝔪)
  let f : Γ(X, ⊤) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom ((algebraMap (Γ(X, ⊤) ⧸ 𝔪) K).comp (Ideal.Quotient.mk 𝔪))
  refine ⟨K, inferInstance, inferInstance, Spec.map f ≫ X.isoSpec.inv, fun r => ?_⟩
  have e : (Spec.map f ≫ X.isoSpec.inv).appTop = f ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    have e₀ : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
      rw [← Category.comp_id X.isoSpec.inv.appTop, ← (Scheme.ΓSpecIso Γ(X, ⊤)).hom_inv_id,
        ← Category.assoc, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
        Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop, Category.id_comp]
    rw [Scheme.Hom.comp_appTop, e₀, Scheme.ΓSpecIso_inv_naturality]
  rw [e]
  refine (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1).trans ?_
  exact (map_eq_zero_iff _ (algebraMap (Γ(X, ⊤) ⧸ 𝔪) K).injective).trans Ideal.Quotient.eq_zero_iff_mem
end GlobalTheory.VVRank
