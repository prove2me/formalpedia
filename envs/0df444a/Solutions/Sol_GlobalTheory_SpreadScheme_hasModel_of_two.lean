-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.hasModel_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:54:19.610851+00:00
-- url     : https://prove2.me/submissions/3f955437-cc6e-48f4-ba7f-260a0a114ec5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_GlobalTheory_SpreadScheme_models_iso
import Theorems.Thm_P2M_GlobalTheory_SpreadScheme_PairModel_baseChange_a__p__b9f293c1f024
import Theorems.Thm_GlobalTheory_SpreadScheme_exists_glued
import Theorems.Thm_GlobalTheory_SpreadScheme_finiteType_of_fg
import Theorems.Thm_GlobalTheory_SpreadScheme_exists_pairModel
import Theorems.Thm_GlobalTheory_SpreadScheme_exists_common_level
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution {X W : Scheme.{0}} (q : X ⟶ Sp V) [QuasiSeparated q] (u : U ⟶ X) (v : W ⟶ X)
    [IsOpenImmersion u] [IsOpenImmersion v] (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    [CompactSpace U] [CompactSpace W] (hU : HasModel (u ≫ q)) (hW : HasModel (v ≫ q)) : HasModel q := by
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace q).mp inferInstance
  have : CompactSpace ↥(pullback u v) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst u v)
  obtain ⟨R₁, _, f₁, h₁, ⟨M₁⟩⟩ := exists_pairModel hU (pullback.fst u v)
  obtain ⟨R₂, _, f₂, h₂, ⟨N₁⟩⟩ := exists_pairModel hW (pullback.snd u v)
  obtain ⟨k, _, f, g₁, g₂, hk, e₁, e₂⟩ := exists_common_level f₁ f₂ h₁ h₂
  letI := f.toAlgebra
  obtain ⟨M⟩ : Nonempty (PairModel (spMap (algebraMap k V)) (u ≫ q) (pullback.fst u v)) := ⟨M₁.baseChange _ _ e₁⟩
  obtain ⟨N⟩ : Nonempty (PairModel (spMap (algebraMap k V)) (v ≫ q) (pullback.snd u v)) := ⟨N₁.baseChange _ _ e₂⟩
  have hN := N.hτ.paste_vert N.hφ
  rw [← pullback.condition_assoc] at hN
  obtain ⟨R, e, hR, he, he'⟩ := models_iso (p := M.a₀ ≫ M.p₀) (q := N.a₀ ≫ N.p₀)
    (M.hτ.paste_vert M.hφ) hN
  have w := spMap_algHom_comp R.val
  obtain ⟨X₀, q₀, φ, _, _, hφ⟩ := exists_glued q (IsPullback.of_hasPullback u v) hc
    (M.baseChange _ _ w) (N.baseChange _ _ w) e (by
      apply pullback.hom_ext
      · refine (Category.assoc _ _ _).trans ?_
        exact (he' _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans (pullback.lift_fst _ _ _).symm
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg _ he).trans ((pullback.lift_snd _ _ _).trans (Eq.trans ?_ (pullback.lift_snd _ _ _).symm))
        simp only [Category.assoc, pullback.condition_assoc])
    (by rw [PairModel.baseChange_a₀_p₀, PairModel.baseChange_a₀_p₀]; exact he)
  have hRZ := finiteType_of_fg hk hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian q₀
  exact ⟨R, inferInstance, R.val.toRingHom, X₀, q₀, φ, hRZ, ‹_›,
    (quasiSeparated_iff_quasiSeparatedSpace q₀).mpr inferInstance, ‹_›, hφ⟩
end GlobalTheory.SpreadScheme
