-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.exists_pairModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:10.24479+00:00
-- url     : https://prove2.me/submissions/0a7167b3-b85c-4afe-91a3-c29388bc2f3b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_GlobalTheory_SpreadScheme_finiteType_of_fg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}
variable {V : Type} [CommRing V]
namespace GlobalTheory.SpreadScheme
theorem _root_.solution {p : U ⟶ Sp V} (h : HasModel p) (a : T ⟶ U) [IsOpenImmersion a] [CompactSpace T] :
    ∃ (R : Type) (_ : CommRing R) (f : R →+* V), Algebra.FiniteType ℤ R ∧ Nonempty (PairModel (spMap f) p a) := by
  classical
  obtain ⟨k, _, f, X₀, p₀, φ, hk, _, _, _, hφ⟩ := h
  letI := f.toAlgebra
  have hφ' : IsPullback φ p p₀ (spMap (algebraMap k V)) := hφ
  obtain ⟨s, O, hO, hs⟩ := exists_preimage_eq (bcDiagram p₀ V) (bcCone p₀ V) (isLimitBcCone p₀ V)
    (a ≫ hφ'.isoPullback.hom).opensRange (isCompact_range (Scheme.Hom.continuous _))
  let R := Algebra.adjoin k (s.unop : Set V)
  let O' : (pullback p₀ (spMap (algebraMap k R))).Opens := O
  have hs' : bcMap p₀ R.val ⁻¹ᵁ O' = (a ≫ hφ'.isoPullback.hom).opensRange := hs
  have hO' : CompactSpace O' := isCompact_iff_compactSpace.1 hO
  have : QuasiSeparatedSpace ↥(pullback p₀ (spMap (algebraMap k R))) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p₀ _)).mp inferInstance
  have hqc : QuasiCompact O'.ι := quasiCompact_of_compactSpace _
  have hr : (hφ'.isoPullback.hom ≫ bcMap p₀ R.val) ⁻¹ᵁ O'.ι.opensRange = a.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage, hs']
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hφ'.isoPullback.hom.isOpenEmbedding.injective (by simpa using hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
  have hle : Set.range (a ≫ hφ'.isoPullback.hom ≫ bcMap p₀ R.val) ⊆ Set.range O'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hr.ge ⟨y, rfl⟩
  refine ⟨R, inferInstance, R.val.toRingHom, finiteType_of_fg hk (Subalgebra.fg_adjoin_finset _),
    ⟨⟨_, O', pullback.snd p₀ _, O'.ι, hφ'.isoPullback.hom ≫ bcMap p₀ R.val, IsOpenImmersion.lift O'.ι _ hle,
      inferInstance, inferInstance, inferInstance, inferInstance, hqc, ?_, ?_⟩⟩⟩
  · have h₁ : IsPullback hφ'.isoPullback.hom p (pullback.snd _ _) (𝟙 _) := .of_horiz_isIso ⟨by simp⟩
    simpa using h₁.paste_horiz (isPullback_bcMap p₀ R.val)
  · exact IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm hr
end GlobalTheory.SpreadScheme
