-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.exists_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:33.958117+00:00
-- url     : https://prove2.me/submissions/cab5036b-a2bd-44fb-8064-759c54e722a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
import Theorems.Thm_GlobalTheory_SS_GlueCompat_source_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_qc_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_pb_mono
import Theorems.Thm_GlobalTheory_SS_GlueCompat_closed_two
import Theorems.Thm_GlobalTheory_SS_GlueCompat_closed_swap
import Theorems.Thm_GlobalTheory_SS_GlueCompat_sep_iff
import Theorems.Thm_GlobalTheory_SS_GlueCompat_j_isPullback
import Theorems.Thm_GlobalTheory_SS_GlueCompat_ofSquare_j
import Theorems.Thm_GlobalTheory_SS_GlueCompat_pb_of_closed
import Theorems.Thm_GlobalTheory_GlueModels_isOpenImmersion_inl
import Theorems.Thm_GlobalTheory_GlueModels_isOpenImmersion_inr
import Theorems.Thm_GlobalTheory_GlueModels_isPullback_of_two
import Theorems.Thm_GlobalTheory_GlueModels_pushout_cover


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
theorem _root_.solution {M N : Model R A} (h : Compat M N) :
    ∃ (G : Model R A) (g₁ : M.Y ⟶ G.Y) (g₂ : N.Y ⟶ G.Y), IsOpenImmersion g₁.left ∧ IsOpenImmersion g₂.left ∧
      M.j ≫ g₁.left = G.j ∧ N.j ≫ g₂.left = G.j ∧ ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left := by
  obtain ⟨W, a, b, ha, hb, ja, jb, hc⟩ := h
  let Y : Over (Sp R) := Over.mk (pushout.desc M.Y.hom N.Y.hom ((Over.w a).trans (Over.w b).symm))
  let g₁ : M.Y ⟶ Y := Over.homMk (pushout.inl a.left b.left) (pushout.inl_desc _ _ _)
  let g₂ : N.Y ⟶ Y := Over.homMk (pushout.inr a.left b.left) (pushout.inr_desc _ _ _)
  have o₁ : IsOpenImmersion g₁.left := GlobalTheory.GlueModels.isOpenImmersion_inl a.left b.left
  have o₂ : IsOpenImmersion g₂.left := GlobalTheory.GlueModels.isOpenImmersion_inr a.left b.left
  have cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left := GlobalTheory.GlueModels.pushout_cover a.left b.left
  have w : a.left ≫ g₁.left = b.left ≫ g₂.left := pushout.condition
  have ej : N.j ≫ g₂.left = M.j ≫ g₁.left := by rw [← ja, ← jb, Category.assoc, Category.assoc, w]
  have sm : Smooth Y.hom := source_two @Smooth cov (by rw [Over.w g₁]; exact M.smooth) (by rw [Over.w g₂]; exact N.smooth)
  have qc : QuasiCompact Y.hom := qc_two cov (by rw [Over.w g₁]; exact M.qc) (by rw [Over.w g₂]; exact N.qc)
  have oi : ∀ Z : Over (Sp R), IsOpenImmersion (𝟙 Z : Z ⟶ Z).left := fun Z => by rw [Over.id_left]; infer_instance
  have self : ∀ {Z : Over (Sp R)} (g : Z ⟶ Y) [IsOpenImmersion g.left],
      IsPullback (𝟙 Z : Z ⟶ Z).left (𝟙 Z : Z ⟶ Z).left g.left g.left := fun g _ => by
    rw [Over.id_left]; exact pb_mono (Category.id_comp _)
  have pb : IsPullback a.left b.left g₁.left g₂.left := by
    have := oi M.Y
    exact pb_of_closed M (𝟙 _) g₁ g₂ a b w (by rwa [Category.comp_id]) W.j (by simpa using ja)
  have c₁ : IsClosedImmersion (lift (𝟙 M.Y) g₁).left :=
    closed_two _ _ cov (self g₁) pb (by rw [Category.comp_id]; exact (sep_iff _).1 M.sep) (by rwa [Category.comp_id])
  have c₂ : IsClosedImmersion (lift (𝟙 N.Y) g₂).left :=
    closed_two _ _ cov pb.flip (self g₂) (by rw [Category.comp_id]; exact closed_swap hc)
      (by rw [Category.comp_id]; exact (sep_iff _).1 N.sep)
  have top : ∀ {Z : Over (Sp R)} (g : Z ⟶ Y),
      IsPullback g.left (𝟙 Z : Z ⟶ Z).left (𝟙 Y : Y ⟶ Y).left g.left := fun g => by
    rw [Over.id_left, Over.id_left]; exact pb_mono (Category.comp_id _)
  have sep : IsSeparated Y.hom := (sep_iff _).2 (closed_two _ _ cov (top g₁) (top g₂)
    (by rw [Category.comp_id]; exact closed_swap c₁) (by rw [Category.comp_id]; exact closed_swap c₂))
  have sq : IsPullback (M.j ≫ g₁.left) A.hom Y.hom (spMap (algebraMap R K)) :=
    GlobalTheory.GlueModels.isPullback_of_two cov (pb_mono rfl) (pb_mono ej)
      (by rw [Category.id_comp, Over.w g₁]; exact j_isPullback M)
      (by rw [Category.id_comp, Over.w g₂]; exact j_isPullback N)
  exact ⟨ofSquare Y sm sep qc sq, g₁, g₂, o₁, o₂, (ofSquare_j Y sm sep qc sq).symm,
    ej.trans (ofSquare_j Y sm sep qc sq).symm, cov⟩
end GlobalTheory.SS.GlueCompat
