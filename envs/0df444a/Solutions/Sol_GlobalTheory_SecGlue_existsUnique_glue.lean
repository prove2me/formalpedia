-- Prove2me | solution 1 for GlobalTheory.SecGlue.existsUnique_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:39.496594+00:00
-- url     : https://prove2.me/submissions/f09d82b9-d65b-4de7-89cd-f6af035ccf73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
import Theorems.Thm_GlobalTheory_SecGlue_exists_rel
import Theorems.Thm_GlobalTheory_SecGlue_glue_rel
import Theorems.Thm_GlobalTheory_SecGlue_exists_can
import Theorems.Thm_GlobalTheory_SecGlue_Can_unique
import Theorems.Thm_GlobalTheory_SecGlue_Can_isPullback
import Theorems.Thm_GlobalTheory_SecGlue_away_open
import Theorems.Thm_GlobalTheory_SecGlue_away_range
import Theorems.Thm_P2M_GlobalTheory_SecGlue_spMap_comp__8f671bc530ae
import Theorems.Thm_GlobalTheory_SecGlue_secBC_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.SecGlue
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ s : ∀ i, LB.Sec (PPx (spMap (algebraMap S (Localization.Away (h i))) ≫ x)), (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ t : LB.Sec (PPx (spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)), SecBC α 1 _ _ (s i) t → SecBC β 1 _ _ (s j) t) → ∃! s₀ : LB.Sec (PPx x), ∀ i, SecBC (algebraMap S (Localization.Away (h i))) 1 x _ s₀ (s i) := by
  intro E _ _ _ H Dw l Xo S _ x n h hspan s hs
  choose a ha using fun i => exists_can (G := Xo.univ.t.G)
    (f := spMap (algebraMap S (Localization.Away (h i)))) (x := x) rfl
  have hop : ∀ (r : S) {pm}, Can Xo.univ.t.G (spMap (algebraMap S (Localization.Away r))) x
      (spMap (algebraMap S (Localization.Away r)) ≫ x) pm → IsOpenImmersion pm := fun r pm hp =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hp.isPullback rfl).flip (away_open r)
  have hra : ∀ (r : S) {pm}, Can Xo.univ.t.G (spMap (algebraMap S (Localization.Away r))) x
      (spMap (algebraMap S (Localization.Away r)) ≫ x) pm → ∀ p : Gx x,
      (∃ y, pm y = p) ↔ r ∉ PrimeSpectrum.asIdeal ((fst (Over.mk x) Xo.univ.t.G).left p) := by
    intro r pm hp p
    refine Iff.trans ⟨?_, ?_⟩ (away_range r _)
    · rintro ⟨y, rfl⟩
      exact ⟨_, (congrArg (fun q => q y) hp.2).symm⟩
    · rintro ⟨w, hw⟩
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (hp.isPullback rfl) p w hw.symm
      exact ⟨y, hy⟩
  haveI : ∀ i, IsOpenImmersion (a i) := fun i => hop _ (ha i)
  simp only [fun i => secBC_iff (ha i)]
  refine glue_rel a (fun p => ?_) _ _ (fun i => (ha i).1) s fun i j y y' hy => ?_
  · by_contra hp
    let P : PrimeSpectrum S := (fst (Over.mk x) Xo.univ.t.G).left p
    refine P.isPrime.ne_top (top_le_iff.1 (hspan ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    by_contra hi
    exact hp ⟨i, (hra _ (ha i) p).2 hi⟩
  · let α : Localization.Away (h i) →+* Localization.Away (h i * h j) :=
      IsLocalization.Away.awayToAwayRight (h i) (h j)
    let β : Localization.Away (h j) →+* Localization.Away (h i * h j) :=
      IsLocalization.Away.awayToAwayLeft (h j) (h i)
    have hα : α.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayRight_eq (h i) (h j) r
    have hβ : β.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayLeft_eq (h j) (h i) r
    obtain ⟨b, hb⟩ := exists_can (G := Xo.univ.t.G) (f := spMap α)
      (x := spMap (algebraMap S (Localization.Away (h i))) ≫ x)
      (x' := spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)
      (by rw [← Category.assoc, spMap_comp', hα])
    obtain ⟨c, hc⟩ := exists_can (G := Xo.univ.t.G) (f := spMap β)
      (x := spMap (algebraMap S (Localization.Away (h j))) ≫ x)
      (x' := spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)
      (by rw [← Category.assoc, spMap_comp', hβ])
    have h1 := (ha i).comp hb
    have h2 := (ha j).comp hc
    rw [spMap_comp', hα] at h1
    rw [spMap_comp', hβ] at h2
    obtain ⟨t, ht⟩ := exists_rel hb.1 (s i)
    obtain ⟨z, hz⟩ := (hra _ h1 (a i y)).2 fun hm => by
      rcases (PrimeSpectrum.isPrime _).mem_or_mem hm with hm | hm
      · exact (hra _ (ha i) _).1 ⟨y, rfl⟩ hm
      · exact (hra _ (ha j) _).1 ⟨y', hy.symm⟩ hm
    exact ⟨_, b, c, z, _, t, hop _ h1, h1.unique h2, (a i).isOpenEmbedding.injective hz, hb.1, ht,
      (secBC_iff hc _ _).1 (hs i j α β hα hβ t ((secBC_iff hb _ _).2 ht))⟩
end GlobalTheory.SecGlue
