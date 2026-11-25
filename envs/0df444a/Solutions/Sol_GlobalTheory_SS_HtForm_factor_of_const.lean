-- Prove2me | solution 1 for GlobalTheory.SS.HtForm.factor_of_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:40.621506+00:00
-- url     : https://prove2.me/submissions/124879ff-f7cf-4249-bb99-4a89cf8c0606

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphisms
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.HtForm
namespace GlobalTheory.SS.HtForm
theorem _root_.solution {k K : Type} [Field k] [Field K] [Algebra k K] (B : Over (Sp k))
    (x : Over.mk (spMap (algebraMap k K)) ⟶ B) {D : B.left.Opens} (hD : IsAffineOpen D)
    {I : Type} (O : I → ValuationSubring K) (hO : ∀ a : K, (∀ i, a ∈ O i) → a ∈ Set.range (algebraMap k K))
    (hx : Set.range x.left ⊆ D)
    (hb : ∀ i, ∃ b : Sp (O i) ⟶ B.left, spMap (O i).subtype ≫ b = x.left ∧ Set.range b ⊆ D) :
    ∃ c : 𝟙_ (Over (Sp k)) ⟶ B, x = toUnit _ ≫ c := by
  let ψ : Γ(B.left, D) ⟶ CommRingCat.of K :=
    Spec.preimage (IsOpenImmersion.lift hD.fromSpec x.left (by rw [hD.range_fromSpec]; exact hx))
  have hψ : Spec.map ψ ≫ hD.fromSpec = x.left := by
    simp only [ψ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hmem : ∀ a, ψ.hom a ∈ Set.range (algebraMap k K) := fun a => hO _ fun i => by
    obtain ⟨b, hb1, hb2⟩ := hb i
    let χ : Γ(B.left, D) ⟶ CommRingCat.of (O i) :=
      Spec.preimage (IsOpenImmersion.lift hD.fromSpec b (by rw [hD.range_fromSpec]; exact hb2))
    have hχ : Spec.map χ ≫ hD.fromSpec = b := by
      simp only [χ, Spec.map_preimage]
      exact IsOpenImmersion.lift_fac _ _ _
    have : ψ = χ ≫ CommRingCat.ofHom (O i).subtype := by
      apply Spec.map_injective
      rw [← cancel_mono hD.fromSpec, hψ, Spec.map_comp, Category.assoc, hχ, hb1]
    rw [this]
    exact (χ.hom a).2
  let e : k ≃+* (algebraMap k K).range := RingEquiv.ofBijective (algebraMap k K).rangeRestrict
    ⟨fun a b h => (algebraMap k K).injective (congrArg Subtype.val h), (algebraMap k K).rangeRestrict_surjective⟩
  let ρ : Γ(B.left, D) →+* k := e.symm.toRingHom.comp (ψ.hom.codRestrict (algebraMap k K).range hmem)
  have hρ : ψ = CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (algebraMap k K) := by
    ext a
    exact (congrArg Subtype.val (e.apply_symm_apply (ψ.hom.codRestrict (algebraMap k K).range hmem a))).symm
  have h1 : spMap (algebraMap k K) ≫ Spec.map (CommRingCat.ofHom ρ) ≫ hD.fromSpec = x.left := by
    rw [← hψ, hρ, Spec.map_comp, Category.assoc]
  have h2 : (Spec.map (CommRingCat.ofHom ρ) ≫ hD.fromSpec) ≫ B.hom = 𝟙 _ := by
    have : IsDominant (spMap (algebraMap k K)) := by
      rw [isDominant_iff]
      show DenseRange (PrimeSpectrum.comap (algebraMap k K))
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap k K).injective]
      exact bot_le
    refine ext_of_isDominant (spMap (algebraMap k K)) ?_
    rw [← Category.assoc, h1, Category.comp_id]
    exact Over.w x
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ρ) ≫ hD.fromSpec) h2, Over.OverMorphism.ext ?_⟩
  rw [← h1]
  rfl
end GlobalTheory.SS.HtForm
