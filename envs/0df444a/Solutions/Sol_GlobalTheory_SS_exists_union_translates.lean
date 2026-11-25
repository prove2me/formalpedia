-- Prove2me | solution 1 for GlobalTheory.SS.exists_union_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:07.661239+00:00
-- url     : https://prove2.me/submissions/4d9ee6d0-5205-4497-94dc-0c2422f98803

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates
import Theorems.Thm_GlobalTheory_SS_FinUnion_twist_j
import Theorems.Thm_GlobalTheory_SS_FinUnion_irr_union
import Theorems.Thm_GlobalTheory_SS_FinUnion_defAt_of_le
import Theorems.Thm_GlobalTheory_SS_FinUnion_transl_one
import Theorems.Thm_GlobalTheory_SS_FinUnion_le_of_law
import Theorems.Thm_GlobalTheory_SS_FinUnion_sp_inter
import Theorems.Thm_GlobalTheory_SS_FinUnion_meet
import Theorems.Thm_GlobalTheory_SS_GI_twist_j
import Theorems.Thm_GlobalTheory_SS_Translates_twist_j
import Theorems.Thm_GlobalTheory_SS_isoAt_id
import Theorems.Thm_GlobalTheory_T_existsUnique_model_extension_of_definedAtPoints
import Theorems.Thm_GlobalTheory_T_exists_glue_finitely_many_compatible_smoothModels
import Theorems.Thm_GlobalTheory_T_modelGroupLaw_definedAt_translate
import Theorems.Thm_GlobalTheory_T_strictModel_translates_twist_compatible
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open GlobalTheory GlobalTheory.SS
open FinUnion
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ G : Model R A, G.Irr ∧ (∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → (M.twist (transl a)).Le G) ∧ (∀ y : G.Y.left, ∃ (a : (𝟙_ (Over (Sp K)) ⟶ A)) (g : M.Y ⟶ G.Y), GenIso M M (transl a).hom ∧ IsOpenImmersion g.left ∧ (M.twist (transl a)).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ z, DefAt (M.prod M) G (μ[A]) z := by
  intro R K _ _ _ _ _ hS A _ _ hA M hM
  obtain ⟨_, -, -, _⟩ := id hS
  choose a ha U φ hU hφ using GlobalTheory.T.modelGroupLaw_definedAt_translate R K hS A hA M hM
  have := (M.prod M).qc
  have : CompactSpace (M.prod M).Y.left := QuasiCompact.compactSpace_of_compactSpace (M.prod M).Y.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z => (U z : Set (M.prod M).Y.left))
    (fun z => (U z).isOpen) (fun z _ => Set.mem_iUnion.2 ⟨z, hU z⟩)
  let b : Fin (T.card + 1) → (𝟙_ (Over (Sp K)) ⟶ A) := Fin.cons 1 fun i => a (T.equivFin.symm i)
  have hb : ∀ i, GenIso M M (transl (b i)).hom := by
    intro i
    refine Fin.cases ?_ (fun i => ha _) i
    change GenIso M M (transl 1).hom
    rw [transl_one]
    obtain ⟨y, hy⟩ := hM.1.1.1
    exact ⟨y, hy, isoAt_id M y⟩
  obtain ⟨G, hle, hcov, hcomp⟩ := GlobalTheory.T.exists_glue_finitely_many_compatible_smoothModels R K A T.card (fun i => M.twist (transl (b i)))
    fun i j => GlobalTheory.T.strictModel_translates_twist_compatible R K hS A hA M hM _ _ (hb i) (hb j)
  have hdef : ∀ z, DefAt (M.prod M) G (μ[A]) z := by
    intro z
    obtain ⟨z', hz', hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
    refine defAt_of_le ?_ (hle (T.equivFin ⟨z', hz'⟩).succ)
    have : b (T.equivFin ⟨z', hz'⟩).succ = a z' := by simp [b]
    rw [this]
    exact ⟨U z', φ z', hz, hφ z'⟩
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints R K _ _ _ _ _ hdef
  refine ⟨G, ?_, fun c hc => le_of_law hM m hm c hc (hcomp _ fun i => GlobalTheory.T.strictModel_translates_twist_compatible R K hS A hA M hM _ _ hc (hb i)),
    fun y => ?_, hdef⟩
  · obtain ⟨g₀, o₀, e₀⟩ := hle 0
    have e₁ : M.j ≫ g₀.left = G.j := by
      have := twist_j M (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A))
      rw [transl_one, Over.id_left, Category.id_comp] at this
      rw [← this]; exact e₀
    refine irr_union (I := {p : Σ i, ((M.twist (transl (b i))).Y ⟶ G.Y) //
      IsOpenImmersion p.2.left ∧ (M.twist (transl (b p.1))).j ≫ p.2.left = G.j}) G.sp
      (fun p => Set.range p.1.2.left) ⟨⟨0, g₀⟩, o₀, e₀⟩ (fun p => ?_) (fun p => ?_) (fun y _ => ?_)
      (fun p => meet _ (hb p.1.1) p.1.2 p.2.2 g₀ e₁)
    · have := p.2.1
      exact p.1.2.left.isOpenEmbedding.isOpen_range
    · rw [sp_inter]
      exact hM.1.1.2.image _ p.1.2.left.continuous.continuousOn
    · obtain ⟨i, g, h1, h2, h3⟩ := hcov y
      exact ⟨⟨⟨i, g⟩, h1, h2⟩, h3⟩
  · obtain ⟨i, g, h1, h2, h3⟩ := hcov y
    exact ⟨b i, g, hb i, h1, h2, h3⟩
end GlobalTheory.SS
