-- Prove2me | solution 1 for GlobalTheory.SS.compat_twist_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:42.276777+00:00
-- url     : https://prove2.me/submissions/13597a9f-192b-4040-be5d-e8e395217c01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
import Theorems.Thm_GlobalTheory_SS_Translates_val_eq
import Theorems.Thm_GlobalTheory_SS_Translates_isoAt_iff
import Theorems.Thm_GlobalTheory_SS_Translates_Ext_comp
import Theorems.Thm_GlobalTheory_SS_Translates_isoAt_div
import Theorems.Thm_GlobalTheory_SS_Translates_Ext_mem_sp
import Theorems.Thm_GlobalTheory_SS_Translates_exists_meet
import Theorems.Thm_GlobalTheory_SS_Translates_exists_section_closed
import Theorems.Thm_GlobalTheory_SS_Translates_transl_comm
import Theorems.Thm_GlobalTheory_SS_Translates_exists_translation
import Theorems.Thm_GlobalTheory_SS_Translates_twist_j
import Theorems.Thm_GlobalTheory_SS_Model_j_hom
import Theorems.Thm_GlobalTheory_SS_compat_of_isoAt_closure
import Theorems.Thm_GlobalTheory_isIntegral_of_isAbelianScheme_field


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
open Translates
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ a b : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → GenIso M M (transl b).hom → Compat (M.twist (transl a)) (M.twist (transl b)) := by
  intro R K _ _ _ _ _ hR A _ _ hA M hM a b ⟨xa, hxa, ha⟩ ⟨xb, hxb, hb⟩
  have := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  have := M.sep
  have hirr : M.Irr := hM.1.1
  let u : A ⟶ A := (transl a).hom ≫ (transl b).inv
  obtain ⟨Xa, ia, ga, oa, hia, hga, ea, rfl⟩ := isoAt_iff.1 ha
  obtain ⟨Xb, ib, gb, ob, hib, hgb, eb, rfl⟩ := isoAt_iff.1 hb
  obtain ⟨p, p', hp, hp'⟩ := exists_meet hirr ga gb ((ea.mem_sp _).1 hxa) ((eb.mem_sp _).1 hxb)
  have hu : IsoAt M M u (ia p) := isoAt_div (f' := transl b) (by simpa [u] using ea) eb hp'
  obtain ⟨W, k, h, q, hk, hh, eu, hq⟩ := isoAt_iff.1 hu
  have hw : ((transl a).inv.left ≫ M.j) ≫ M.Y.hom = ((transl b).inv.left ≫ M.j) ≫ M.Y.hom := by
    simp only [Category.assoc, M.j_hom, Over.w_assoc]
  let d : A.left ⟶ (M.Y ⊗ M.Y).left := pullback.lift _ _ hw
  have d1 : d ≫ (fst M.Y M.Y).left = (transl a).inv.left ≫ M.j := pullback.lift_fst _ _ _
  have d2 : d ≫ (snd M.Y M.Y).left = (transl b).inv.left ≫ M.j := pullback.lift_snd _ _ _
  refine GlobalTheory.SS.compat_of_isoAt_closure R K hR A _ _ d (d1.trans (twist_j M _).symm) (d2.trans (twist_j M _).symm) ?_
  intro (z : (M.Y ⊗ M.Y).left) hz hc hs
  obtain ⟨s, hs'⟩ := exists_section_closed hR (M.prod M) (z := z) hs hc
  have hs'' : (show 𝟙_ (Over (Sp R)) ⟶ M.Y ⊗ M.Y from s).left (IsLocalRing.closedPoint R) = z := hs'
  obtain ⟨c, X, i, g, o, q', hi, hg, e, ho, hgo, h₂⟩ := exists_translation hR hA hM
    ((show 𝟙_ (Over (Sp R)) ⟶ M.Y ⊗ M.Y from s) ≫ fst M.Y M.Y) ((show 𝟙_ (Over (Sp R)) ⟶ M.Y ⊗ M.Y from s) ≫ snd M.Y M.Y)
    k (q := q) (hq ▸ (ea.mem_sp _).2 hp)
  obtain ⟨X', i', g', o', hi', hg', e', ho'⟩ := isoAt_iff.1 h₂
  have ho1 : i o = (fst M.Y M.Y).left z := by rw [ho, ← hs'']; rfl
  have ho2 : i' o' = (snd M.Y M.Y).left z := by rw [ho', ← hs'']; rfl
  obtain ⟨r, hr, -⟩ := Scheme.Pullback.exists_preimage_pullback o q' hgo
  have hcu : (transl c).hom ≫ u = u ≫ (transl c).hom := by
    have : (transl c).hom ≫ (transl b).inv = (transl b).inv ≫ (transl c).hom := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, transl_comm]
    simp only [u]
    rw [← Category.assoc, transl_comm, Category.assoc, this, Category.assoc]
  have E := e.comp eu
  rw [hcu] at E
  have hr' : (pullback.fst g k ≫ i) r = (fst M.Y M.Y).left z := by rw [Scheme.Hom.comp_apply, hr, ho1]
  have hv : (pullback.snd g k ≫ h) r = g' o' := by
    refine val_eq d hz (fst M.Y M.Y).left (snd M.Y M.Y).left (pullback.fst g k ≫ i) i' _ _ M.Y.hom M.Y.hom M.Y.hom
      E.1 e'.1 (by rw [Over.w, Over.w]) ?_ hr' ho2
    intro T x t₁ t₂ e₁ e₂
    rw [E.2 T t₁ (x ≫ (transl a).inv.left) (by rw [e₁, d1, Category.assoc]),
      e'.2 T t₂ (x ≫ (transl b).inv.left) (by rw [e₂, d2, Category.assoc])]
    have : (transl a).inv ≫ u ≫ (transl c).hom = (transl b).inv ≫ (transl c).hom := by simp [u]
    have h3 : (transl a).inv.left ≫ (u ≫ (transl c).hom).left = (transl b).inv.left ≫ (transl c).hom.left :=
      congr(($this).left)
    rw [Category.assoc x, Category.assoc x, reassoc_of% h3]
  have hfin := isoAt_div (f' := transl c) E e' hv
  rw [hr'] at hfin
  obtain ⟨Z, l, m, n, hl, hm, en, hn⟩ := isoAt_iff.1 hfin
  refine isoAt_iff.2 ⟨Z, l, m, n, hl, hm, ⟨en.1, fun T t x ex => ?_⟩, hn⟩
  have ex' : t ≫ l = (x ≫ (transl a).inv.left) ≫ M.j := by
    rw [Category.assoc, ← twist_j]; exact ex
  have : (transl a).inv ≫ u = (transl b).inv := by simp [u]
  have h3 : (transl a).inv.left ≫ u.left = (transl b).inv.left := congr(($this).left)
  refine (en.2 T t _ ex').trans ?_
  rw [Category.assoc, reassoc_of% h3, ← twist_j]
  exact congrArg _ (Category.id_comp _).symm
end GlobalTheory.SS
