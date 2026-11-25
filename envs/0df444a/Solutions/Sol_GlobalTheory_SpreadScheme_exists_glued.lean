-- Prove2me | solution 1 for GlobalTheory.SpreadScheme.exists_glued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:26:28.791649+00:00
-- url     : https://prove2.me/submissions/687a393a-82ad-4414-b954-8b6918ef4514

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Theorems.Thm_GlobalTheory_SpreadScheme_lfp_of_two
import Theorems.Thm_GlobalTheory_GlueModels_exists_glue
import Theorems.Thm_GlobalTheory_GlueModels_exists_of_inl_eq_inr
import Theorems.Thm_GlobalTheory_GlueModels_isOpenImmersion_inl
import Theorems.Thm_GlobalTheory_GlueModels_isOpenImmersion_inr
import Theorems.Thm_GlobalTheory_GlueModels_isPullback_of_two
import Theorems.Thm_GlobalTheory_GlueModels_pushout_cover
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
namespace GlobalTheory.SpreadScheme
theorem _root_.solution {X W : Scheme.{0}} (q : X ⟶ S) {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    {b : T ⟶ W} (h : IsPullback a b u v) (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    (M : PairModel f (u ≫ q) a) (N : PairModel f (v ≫ q) b) (e : M.T₀ ≅ N.T₀) (he : M.τ ≫ e.hom = N.τ)
    (he' : e.hom ≫ N.a₀ ≫ N.p₀ = M.a₀ ≫ M.p₀) [CompactSpace S₀] [QuasiSeparatedSpace S₀] :
    ∃ (X₀ : Scheme.{0}) (q₀ : X₀ ⟶ S₀) (φ : X ⟶ X₀), LocallyOfFinitePresentation q₀ ∧ QuasiCompact q₀ ∧ IsPullback φ q q₀ f := by
  have Hp := M.hτ
  have Hq : IsPullback M.τ b (e.hom ≫ N.a₀) N.φ :=
    N.hτ.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp [← he]) (by simp) (by simp) (by simp)
  have := isOpenImmersion_inl M.a₀ (e.hom ≫ N.a₀)
  have := isOpenImmersion_inr M.a₀ (e.hom ≫ N.a₀)
  obtain ⟨φ, h1, h2⟩ := exists_glue h hc (M.φ ≫ pushout.inl M.a₀ (e.hom ≫ N.a₀))
    (N.φ ≫ pushout.inr M.a₀ (e.hom ≫ N.a₀)) (by
    rw [← Hp.w_assoc, ← Hq.w_assoc, pushout.condition])
  have e1 (x : U) : φ (u x) = pushout.inl M.a₀ (e.hom ≫ N.a₀) (M.φ x) := congrArg (fun g => g x) h1
  have e2 (x : W) : φ (v x) = pushout.inr M.a₀ (e.hom ≫ N.a₀) (N.φ x) := congrArg (fun g => g x) h2
  have e3 (w : T) : u (a w) = v (b w) := congrArg (fun g => g w) h.w
  have hcov := pushout_cover M.a₀ (e.hom ≫ N.a₀)
  refine ⟨_, pushout.desc M.p₀ N.p₀ (by rw [Category.assoc, he']), φ, ?_, ?_, ?_⟩
  · refine lfp_of_two hcov _ ?_ ?_
    · rw [pushout.inl_desc]
      infer_instance
    · rw [pushout.inr_desc]
      infer_instance
  · have : CompactSpace M.U₀ := QuasiCompact.compactSpace_of_compactSpace M.p₀
    have : CompactSpace N.U₀ := QuasiCompact.compactSpace_of_compactSpace N.p₀
    have : CompactSpace (pushout M.a₀ (e.hom ≫ N.a₀) : Scheme.{0}) := by
      refine ⟨?_⟩
      rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl M.a₀ (e.hom ≫ N.a₀)) ∪
        Set.range (pushout.inr M.a₀ (e.hom ≫ N.a₀))) hcov]
      exact (isCompact_range (Scheme.Hom.continuous _)).union (isCompact_range (Scheme.Hom.continuous _))
    infer_instance
  refine isPullback_of_two hcov (u' := u) (v' := v) (aU := M.φ) (aV := N.φ) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hq w x hw
        exact ⟨a z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨M.φ y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hp w x hw
        exact ⟨b z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨N.φ y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using M.hφ
  · simpa only [pushout.inr_desc] using N.hφ
end GlobalTheory.SpreadScheme
