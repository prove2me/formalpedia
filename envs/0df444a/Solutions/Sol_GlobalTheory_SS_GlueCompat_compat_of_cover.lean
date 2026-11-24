-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.compat_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:52:53.536396+00:00
-- url     : https://prove2.me/submissions/33379755-8d25-40fd-b70a-e94c90c0d8de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
import Theorems.Thm_GlobalTheory_SS_GlueCompat_target_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_qc_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_pb_mono
import Theorems.Thm_GlobalTheory_SS_GlueCompat_closed_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_ext_of_schemeDominant
import Theorems.Thm_GlobalTheory_SS_GlueCompat_exists_sup
import Theorems.Thm_GlobalTheory_SS_GlueCompat_j_isPullback
import Theorems.Thm_GlobalTheory_SS_GlueCompat_ofSquare_j
import Theorems.Thm_GlobalTheory_SS_GlueCompat_schDom_open
import Theorems.Thm_GlobalTheory_SS_GlueCompat_pb_of_closed
import Theorems.Thm_GlobalTheory_GlueModels_exists_glue


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
namespace GlobalTheory.SS.GlueCompat
theorem _root_.solution {M₁ M₂ G N : Model R A} (g₁ : M₁.Y ⟶ G.Y) (g₂ : M₂.Y ⟶ G.Y) [IsOpenImmersion g₁.left]
    [IsOpenImmersion g₂.left] (j₁ : M₁.j ≫ g₁.left = G.j) (j₂ : M₂.j ≫ g₂.left = G.j)
    (cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left) (h₁ : Compat N M₁) (h₂ : Compat N M₂) :
    Compat N G := by
  obtain ⟨W₁, p₁, b₁, hp₁, hb₁, jp₁, jb₁, hc₁⟩ := h₁
  obtain ⟨W₂, p₂, b₂, hp₂, hb₂, jp₂, jb₂, hc₂⟩ := h₂
  obtain ⟨X, p, a₁, a₂, op, rfl, rfl, cx⟩ := exists_sup p₁ p₂
  rw [Over.comp_left] at hp₁ hp₂ jp₁ jp₂
  have o₁ : IsOpenImmersion a₁.left := IsOpenImmersion.of_comp _ p.left
  have o₂ : IsOpenImmersion a₂.left := IsOpenImmersion.of_comp _ p.left
  have ej : W₂.j ≫ a₂.left = W₁.j ≫ a₁.left := by
    rw [← cancel_mono p.left, Category.assoc, Category.assoc, jp₁, jp₂]
  have := G.sep
  have hab : pullback.fst a₁.left a₂.left ≫ b₁.left ≫ g₁.left = pullback.snd a₁.left a₂.left ≫ b₂.left ≫ g₂.left := by
    have : IsSchemeTheoreticallyDominant (pullback.lift W₁.j W₂.j ej.symm) :=
      schDom_open W₁ (pullback.fst a₁.left a₂.left) (pullback.lift_fst _ _ _)
    refine ext_of_schemeDominant G.Y.hom ?_ (pullback.lift W₁.j W₂.j ej.symm) ?_
    · simp only [Category.assoc, Over.w]
      rw [← Over.w a₁, ← Over.w a₂, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% jb₁, reassoc_of% jb₂, j₁, j₂]
  obtain ⟨φ, f₁, f₂⟩ := GlobalTheory.GlueModels.exists_glue (IsPullback.of_hasPullback a₁.left a₂.left) cx _ _ hab
  have hφ : φ ≫ G.Y.hom = X.hom := by
    refine (coverTwo a₁.left a₂.left cx).hom_ext _ _ ?_
    rintro (_ | _)
    · change a₁.left ≫ φ ≫ _ = a₁.left ≫ _
      rw [reassoc_of% f₁]; simp only [Over.w]
    · change a₂.left ≫ φ ≫ _ = a₂.left ≫ _
      rw [reassoc_of% f₂]; simp only [Over.w]
  let q : X ⟶ G.Y := Over.homMk φ hφ
  have pb₁ : IsPullback a₁.left b₁.left q.left g₁.left := pb_of_closed N p q g₁ a₁ b₁ f₁ hc₁ W₁.j jp₁
  have pb₂ : IsPullback a₂.left b₂.left q.left g₂.left := pb_of_closed N p q g₂ a₂ b₂ f₂ hc₂ W₂.j jp₂
  have := N.smooth
  have := N.sep
  have sm : Smooth X.hom := by rw [← Over.w p]; infer_instance
  have sep : IsSeparated X.hom := by rw [← Over.w p]; infer_instance
  have qc : QuasiCompact X.hom := qc_two cx (by rw [Over.w a₁]; exact W₁.qc) (by rw [Over.w a₂]; exact W₂.qc)
  have sq : IsPullback (W₁.j ≫ a₁.left) A.hom X.hom (spMap (algebraMap R K)) := by
    have := (pb_mono (a := W₁.j ≫ a₁.left) (i := p.left) (j := N.j) (by rw [Category.assoc, jp₁])).paste_vert
      (j_isPullback N)
    rwa [Category.id_comp, Over.w p] at this
  refine ⟨ofSquare X sm sep qc sq, p, q, op, target_two @IsOpenImmersion cov pb₁ pb₂ hb₁ hb₂, ?_, ?_,
    closed_two p q cov pb₁ pb₂ hc₁ hc₂⟩
  · rw [ofSquare_j, Category.assoc, jp₁]
  · rw [ofSquare_j, Category.assoc]
    change W₁.j ≫ a₁.left ≫ φ = _
    rw [f₁, reassoc_of% jb₁, j₁]
end GlobalTheory.SS.GlueCompat
