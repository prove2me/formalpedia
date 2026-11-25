-- Prove2me | solution 1 for GlobalTheory.AbLaw.isProjBy_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:49.011669+00:00
-- url     : https://prove2.me/submissions/12ee3e12-275e-4843-ac97-4affb95f405f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsProjByBaseChange
import Theorems.Thm_GlobalTheory_AbLaw_BaseChange_cst_comp_specMap
import Theorems.Thm_GlobalTheory_AbLaw_BaseChange_ap_top_eq_cst
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_cst
import Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_ratio
import Theorems.Thm_GlobalTheory_AbLaw_Segre_isLB_box
import Theorems.Thm_GlobalTheory_AbLaw_Segre_nonzeroLocus_boxSec


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
open GlobalTheory.AbLaw.BaseChange
namespace GlobalTheory.AbLaw
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsProjBy f → IsProjBy f' := by
  intro R R' _ _ g X X' f p q sq hf
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  have hloc : ∀ a, nonzeroLocus (boxSec p q (s a) (oneSec _)) = p ⁻¹ᵁ nonzeroLocus (s a) ⊓ q ⁻¹ᵁ ⊤ := fun a => by
    rw [nonzeroLocus_boxSec, nonzeroLocus_oneSec]
  refine ⟨box p q H (Inh.trivLB _), isLB_box p q hH (Inh.trivLB_isLB _), m,
    fun a => boxSec p q (s a) (oneSec _), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [hloc]
    exact ⟨hi, trivial⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' a
  have aff₂ : IsAffineOpen (⊤ : (Spec (CommRingCat.of R')).Opens) := isAffineOpen_top _
  have loc := hloc a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => ap p l₁ (r₁ b), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_ap p _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg (· * _) (ap_ratio p (hr₁ b k.1) _ _)).trans (_root_.mul_assoc _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C (g c), by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w, cst_comp_specMap]⟩
      | add F G hF hG => rw [map_add, map_add]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X i, ?_⟩
        simp only [MvPolynomial.eval₂Hom_X']
    · change ap q l₂ _ ∈ _
      obtain ⟨r, hr⟩ := ap_top_eq_cst q l₂ d
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.eval₂Hom_C, hr]⟩
end GlobalTheory.AbLaw
