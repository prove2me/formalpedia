-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.isIso_restrict_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:33.47703+00:00
-- url     : https://prove2.me/submissions/cb4ceed8-0d77-4a8d-9190-4bca2f096134

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedCharts
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_isPullback_of_preimage_opensRange

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
namespace IsChart
theorem _root_.solution {P X Y Y' : Scheme.{0}} {a b : P ⟶ X} {π : X ⟶ Y'} {V : X.Opens}
    {q : V.toScheme ⟶ Y} {em : Y ⟶ Y'} [IsOpenImmersion em] (h : IsChart a b V q)
    (hc : V.ι ≫ π = q ≫ em) (hpre : π ⁻¹ᵁ em.opensRange = V) (w : a ≫ π = b ≫ π) :
    IsIso (pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V)) := by
  obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := h

  have h1 : IsPullback (b ∣_ V) (a' ≫ V.ι) (V.ι ≫ π) π := by
    have h0 := hsq.paste_horiz (isPullback_of_preimage_opensRange π V q em hc hpre).flip
    rw [← hc] at h0
    exact h0.flip

  have h2 : IsPullback (pullback.snd π π ∣_ V) ((pullback.snd π π ⁻¹ᵁ V).ι ≫ pullback.fst π π)
      (V.ι ≫ π) π :=
    (isPullback_morphismRestrict (pullback.snd π π) V).paste_vert (IsPullback.of_hasPullback π π).flip
  have hdom : pullback.lift a b w ⁻¹ᵁ (pullback.snd π π ⁻¹ᵁ V) = b ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_snd]

  have key : pullback.lift a b w ∣_ (pullback.snd π π ⁻¹ᵁ V) =
      (P.isoOfEq hdom).hom ≫ (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc]
      rw [IsPullback.isoIsPullback_hom_fst_assoc]
      simp only [morphismRestrict_ι, morphismRestrict_ι_assoc, pullback.lift_snd,
        Scheme.isoOfEq_hom_ι_assoc]
    · rw [morphismRestrict_ι_assoc, pullback.lift_fst, Category.assoc,
        IsPullback.isoIsPullback_hom_snd, ha', Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance
end IsChart
end GlobalTheory.CompanionTheory.FreeQuotGlue
