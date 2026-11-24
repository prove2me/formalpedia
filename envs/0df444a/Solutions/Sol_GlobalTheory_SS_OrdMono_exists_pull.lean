-- Prove2me | solution 1 for GlobalTheory.SS.OrdMono.exists_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:36.499569+00:00
-- url     : https://prove2.me/submissions/10db8975-b697-43de-ae44-cdf3584d96a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel
import Theorems.Thm_GlobalTheory_SS_OrdMono_appLE_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdMono
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.OrdMono
theorem _root_.solution {M N : Model R A} {W : M.Y.left.Opens} {g : W.toScheme ⟶ N.Y.left}
    (h : Extends M N (𝟙 A) W g) (V : N.Y.left.Opens) (hV : ⊤ ≤ g ⁻¹ᵁ V) :
    ∃ (ψ : Γ(N.Y.left, V) →+* Γ(M.Y.left, W)) (hle : M.j ⁻¹ᵁ W ≤ N.j ⁻¹ᵁ V), ψ.comp (cst N V) = cst M W ∧
      (∀ u, (M.j.app W).hom (ψ u) = rs _ hle ((N.j.app V).hom u)) ∧
      (IsAffineOpen W → IsAffineOpen V → ψ.Etale → Etale g) := by
  have h2 : M.j ∣_ W ≫ g = (M.j ⁻¹ᵁ W).ι ≫ N.j := by simpa using h.2
  have hle : M.j ⁻¹ᵁ W ≤ N.j ⁻¹ᵁ V := fun x hx => by
    have : ((M.j ⁻¹ᵁ W).ι ≫ N.j) ⟨x, hx⟩ ∈ V := by
      rw [← h2]; exact hV (x := (M.j ∣_ W) ⟨x, hx⟩) trivial
    exact this
  refine ⟨(g.appLE V ⊤ hV ≫ inv (th W)).hom, hle, ?_, ?_, ?_⟩
  · have : N.Y.hom.appLE ⊤ V le_top ≫ g.appLE V ⊤ hV ≫ inv (th W) = M.Y.hom.appLE ⊤ W le_top := by
      rw [← Category.assoc, IsIso.comp_inv_eq, th, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr h.1 _ _ _ _
    ext r
    exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) this
  · have a : M.j.app W ≫ th (M.j ⁻¹ᵁ W) = th W ≫ (M.j ∣_ W).appLE ⊤ ⊤ le_top := by
      rw [th, th, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr (morphismRestrict_ι _ _).symm _ _ _ _
    have : (g.appLE V ⊤ hV ≫ inv (th W)) ≫ M.j.app W = N.j.appLE V _ hle := by
      rw [← cancel_mono (th (M.j ⁻¹ᵁ W)), Category.assoc, a, Category.assoc, IsIso.inv_hom_id_assoc, th,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr h2 _ _ _ _
    intro u
    exact congrArg (fun q => q.hom u) this
  · intro hW hV' he
    have : IsAffine W.toScheme := hW
    have he' : (g.appLE V ⊤ hV).hom.Etale := (RingHom.Etale.respectsIso.cancel_right_isIso _ _).1 he
    have h3 : Etale (g.resLE V ⊤ hV) := by
      have : IsAffine V.toScheme := hV'
      have : IsAffine (⊤ : W.toScheme.Opens).toScheme := isAffineOpen_top _
      rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
      exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso g V ⊤ hV)).2 he'
    have h4 : Etale ((⊤ : W.toScheme.Opens).ι ≫ g) := by
      rw [← Scheme.Hom.resLE_comp_ι g hV]; infer_instance
    have h5 : g = W.toScheme.topIso.inv ≫ (⊤ : W.toScheme.Opens).ι ≫ g := by simp
    rw [h5]; infer_instance
end GlobalTheory.SS.OrdMono
