-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:46.697022+00:00
-- url     : https://prove2.me/submissions/bd9ee6ee-7382-4d7f-b10c-d56a9adacbfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_cst
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_ratio
import Theorems.Thm_GlobalTheory_AbLaw_Segre_isLB_box
import Theorems.Thm_GlobalTheory_AbLaw_Segre_nonzeroLocus_boxSec
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ratio_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
    (sq : IsPullback p q f g) (hf : IsProjBy f) (hg : IsProjBy g) : IsProjBy (p ≫ f) := by
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  obtain ⟨K, hK, n, t, ht, ht'⟩ := hg
  let e : Fin (m * n + m + n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans finProdFinEquiv.symm
  refine ⟨box p q H K, isLB_box p q hH hK, m * n + m + n,
    fun a => boxSec p q (s (e a).1) (t (e a).2), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show q y ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (i, j), ?_⟩
    rw [nonzeroLocus_boxSec, e.apply_symm_apply]
    exact ⟨hi, hj⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' (e a).1
  obtain ⟨aff₂, r₂, hr₂, sj₂⟩ := ht' (e a).2
  have loc := nonzeroLocus_boxSec p q (s (e a).1) (t (e a).2)
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  have o₁ : r₁ (e a).1 = 1 := ratio_self _ _ (hr₁ _)
  have o₂ : r₂ (e a).2 = 1 := ratio_self _ _ (hr₂ _)
  refine ⟨?_, fun b => ap p l₁ (r₁ (e b).1) * ap q l₂ (r₂ (e b).2), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg₂ (· * ·) (ap_ratio p (hr₁ (e b).1 k.1) _ _) (ap_ratio q (hr₂ (e b).2 k.2) _ _)).trans
      (mul_mul_mul_comm _ _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm (i, (e a).2)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₂, map_one, _root_.mul_one]
    · obtain ⟨F, rfl⟩ := sj₂ d
      change ap q l₂ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C c, by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X (e.symm ((e a).1, i)), ?_⟩
        simp only [MvPolynomial.eval₂Hom_X', e.apply_symm_apply, o₁, map_one, _root_.one_mul]
end GlobalTheory.AbLaw.Segre
