-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict.isChart_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:52:42.73282+00:00
-- url     : https://prove2.me/submissions/2bdcb934-69ff-499b-9147-5694f4acbef1

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_ChartRestrict_opensRange_homOfLE_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_apply_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict
namespace GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict
theorem _root_.solution {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
    (h : IsChart a b V q) (D : Y.Opens) (W : X.Opens) (hle : W ≤ V)
    (hW : ∀ u : V.toScheme, V.ι u ∈ W ↔ q u ∈ D) :
    ∃ q' : W.toScheme ⟶ D.toScheme, IsChart a b W q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  obtain ⟨hst, hfin, hflat, hlfp, hsurj, a', ha', hpbV⟩ := h

  have hrange : Set.range (X.homOfLE hle ≫ q) ⊆ Set.range D.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show q (X.homOfLE hle w) ∈ D
    rw [← hW, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact w.2
  let q' : W.toScheme ⟶ D.toScheme := IsOpenImmersion.lift D.ι (X.homOfLE hle ≫ q) hrange
  have hq' : q' ≫ D.ι = X.homOfLE hle ≫ q := IsOpenImmersion.lift_fac _ _ _

  have hS2 : IsPullback q' (X.homOfLE hle) D.ι q := by
    refine IsOpenImmersion.isPullback q' (X.homOfLE hle) D.ι q hq'.symm ?_
    rw [Scheme.Opens.opensRange_ι, opensRange_homOfLE_eq hle]
    ext u
    exact (hW u).symm

  have hstW : a ⁻¹ᵁ W = b ⁻¹ᵁ W := by
    ext p
    show a p ∈ W ↔ b p ∈ W
    by_cases hpa : a p ∈ V
    · have hpb : b p ∈ V := by
        have : p ∈ a ⁻¹ᵁ V := hpa
        rw [hst] at this
        exact this
      obtain ⟨u, hu⟩ : a p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hpa
      obtain ⟨u', hu'⟩ : b p ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hpb
      have hq : q u = q u' :=
        (IsChart.apply_eq_iff ⟨hst, hfin, hflat, hlfp, hsurj, a', ha', hpbV⟩ u u').mpr ⟨p, hu.symm, hu'.symm⟩
      have e1 := hW u
      have e2 := hW u'
      rw [hu] at e1
      rw [hu'] at e2
      rw [e1, e2, hq]
    · have hpb : b p ∉ V := fun hb => hpa (by
        have : p ∈ b ⁻¹ᵁ V := hb
        rw [← hst] at this
        exact this)
      exact ⟨fun hw => absurd (hle hw) hpa, fun hw => absurd (hle hw) hpb⟩

  have hrange' : Set.range ((b ⁻¹ᵁ W).ι ≫ a) ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : p.1 ∈ a ⁻¹ᵁ W := by rw [hstW]; exact p.2
    exact this
  let a'' : (b ⁻¹ᵁ W).toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι ((b ⁻¹ᵁ W).ι ≫ a) hrange'
  have ha'' : a'' ≫ W.ι = (b ⁻¹ᵁ W).ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  let ιK : (b ⁻¹ᵁ W).toScheme ⟶ (b ⁻¹ᵁ V).toScheme := P.homOfLE (b.preimage_mono hle)
  have hL : IsPullback (b ∣_ W) ιK (X.homOfLE hle) (b ∣_ V) := by
    refine IsOpenImmersion.isPullback (b ∣_ W) ιK (X.homOfLE hle) (b ∣_ V) ?_ ?_
    · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι,
        morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    · rw [opensRange_homOfLE_eq hle, opensRange_homOfLE_eq (b.preimage_mono hle)]
      ext p
      show (b ∣_ V) p ∈ V.ι ⁻¹ᵁ W ↔ (b ⁻¹ᵁ V).ι p ∈ b ⁻¹ᵁ W
      rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
        morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hcomm : ιK ≫ a' = a'' ≫ X.homOfLE hle := by
    rw [← cancel_mono V.ι, Category.assoc, ha', Category.assoc, Scheme.homOfLE_ι, ha'',
      ← Category.assoc, Scheme.homOfLE_ι]
  have hs : IsPullback (a'' ≫ X.homOfLE hle) (b ∣_ W) q (q' ≫ D.ι) := by
    have := hL.flip.paste_horiz hpbV
    rw [hcomm, ← hq'] at this
    exact this
  have hpW : IsPullback a'' (b ∣_ W) q' q' := by
    refine hs.of_right ?_ hS2.flip
    rw [← cancel_mono D.ι, Category.assoc, Category.assoc, hq']
    simpa [hq'] using hs.w
  exact ⟨q', ⟨hstW, MorphismProperty.of_isPullback hS2.flip hfin,
    MorphismProperty.of_isPullback hS2.flip hflat, MorphismProperty.of_isPullback hS2.flip hlfp,
    MorphismProperty.of_isPullback hS2.flip hsurj, a'', ha'', hpW⟩, hq'⟩
end GlobalTheory.CompanionTheory.FreeQuotGlue.ChartRestrict
