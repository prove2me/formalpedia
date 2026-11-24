-- Prove2me | solution 1 for GlobalTheory.SS.Ord.isOpenImmersion_of_extends_id_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:35:52.944001+00:00
-- url     : https://prove2.me/submissions/51b7d681-c0cb-4441-aeaa-7646324479ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
import Theorems.Thm_GlobalTheory_schemeTheoreticallyDominant_fractionField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
namespace GlobalTheory.SS.Ord
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma model_isPullback_genericFibre_spMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm
end GlobalTheory.SS.Ord
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
namespace GlobalTheory.SS.Ord
namespace _root_.GlobalTheory.SS.Ord
theorem _root_.solution :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M N : _root_.GlobalTheory.SS.Model R A)
      (U : M.Y.left.Opens) (g : U.toScheme ⟶ N.Y.left),
      _root_.GlobalTheory.SS.Extends M N (𝟙 A) U g → Etale g → IsOpenImmersion g := by
  intro R K _ _ _ _ _ _ A M N U g hE _
  haveI := M.smooth
  haveI := M.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI : IsSeparated (g ≫ N.Y.hom) := by rw [hE.1]; infer_instance
  haveI : IsSeparated g := IsSeparated.of_comp g N.Y.hom
  haveI := FormallyUnramified.isOpenImmersion_diagonal g
  let ψ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)
  let q := pullback.fst g g ≫ U.ι ≫ M.Y.hom
  let φ := pullback.fst q ψ
  haveI : IsSchemeTheoreticallyDominant φ :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback q ψ).flip
  have hU := ((isPullback_morphismRestrict M.j U).paste_vert
    (model_isPullback_genericFibre_spMap M))
  have hN := model_isPullback_genericFibre_spMap N
  have hs : (φ ≫ pullback.fst g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [Category.assoc]
    exact pullback.condition
  have hs' : (φ ≫ pullback.snd g g) ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ := by
    rw [← hs, ← hE.1]
    simp only [Category.assoc, pullback.condition_assoc]
  have key : ∀ (c : pullback q ψ ⟶ U) (hc : c ≫ U.ι ≫ M.Y.hom = pullback.snd q ψ ≫ ψ),
      (hU.lift c _ hc ≫ (M.j ⁻¹ᵁ U).ι) ≫ N.j = c ≫ g := by
    intro c hc
    have h2 := hE.2
    conv_rhs => rw [← hU.lift_fst c _ hc]
    rw [Category.assoc (hU.lift c _ hc) (M.j ∣_ U) g, h2]
    simp
  have hl : hU.lift _ _ hs ≫ (M.j ⁻¹ᵁ U).ι =
      hU.lift _ _ hs' ≫ (M.j ⁻¹ᵁ U).ι := by
    apply hN.hom_ext
    · rw [key _ hs, key _ hs']
      simp only [Category.assoc, pullback.condition]
    · have e1 := hU.lift_snd _ _ hs
      have e2 := hU.lift_snd _ _ hs'
      simp only [Category.assoc] at e1 e2 ⊢
      rw [e1, e2]
  have hab : φ ≫ pullback.fst g g = φ ≫ pullback.snd g g := by
    rw [← hU.lift_fst _ _ hs, ← hU.lift_fst _ _ hs', (cancel_mono _).1 hl]
  have hφ : φ = (φ ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    apply pullback.hom_ext <;> simp [hab]
  have hrange : Set.range φ ⊆ Set.range (pullback.diagonal g) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(φ ≫ pullback.fst g g) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) :=
    (pullback.diagonal g).isClosedEmbedding.isClosed_range
  have huniv : Set.range (pullback.diagonal g) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (IsDominant.denseRange (f := φ)).closure_eq]
    exact closure_minimal hrange hclosed
  haveI : IsIso (pullback.diagonal g) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using huniv))
  haveI : Mono g := (pullback.isIso_diagonal_iff g).mp inferInstance
  exact IsOpenImmersion.of_flat_of_mono g
end _root_.GlobalTheory.SS.Ord
end GlobalTheory.SS.Ord
