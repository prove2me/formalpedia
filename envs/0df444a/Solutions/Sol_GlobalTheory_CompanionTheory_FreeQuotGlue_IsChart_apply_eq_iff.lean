-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.apply_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:13.436195+00:00
-- url     : https://prove2.me/submissions/6f58f2df-9e6b-4af8-9879-c30d445355d4

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
namespace IsChart
theorem _root_.solution (h : IsChart a b V q) (u v : V.toScheme) :
    q u = q v ↔ ∃ p : P, a p = V.ι u ∧ b p = V.ι v := by
  obtain ⟨hs, -, -, -, -, a', ha, hp⟩ := id h
  constructor
  · intro e
    obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback u v e
    let p : (b ⁻¹ᵁ V).toScheme := hp.isoPullback.inv z
    have e1 : a' p = u := by
      rw [← h1]
      exact congr($(hp.isoPullback_inv_fst) z)
    have e2 : (b ∣_ V) p = v := by
      rw [← h2]
      exact congr($(hp.isoPullback_inv_snd) z)
    refine ⟨(b ⁻¹ᵁ V).ι p, ?_, ?_⟩
    · rw [← e1]; exact (congr($ha p)).symm
    · rw [← e2]; exact (congr($(morphismRestrict_ι b V) p)).symm
  · rintro ⟨p, h1, h2⟩
    have hp' : p ∈ b ⁻¹ᵁ V := by
      change b p ∈ V
      rw [h2]; exact v.2
    let p' : (b ⁻¹ᵁ V).toScheme := ⟨p, hp'⟩
    have hi : (b ⁻¹ᵁ V).ι p' = p := rfl
    have e1 : a' p' = u := V.ι.isOpenEmbedding.injective (by
      rw [← h1, ← hi]; exact congr($ha p'))
    have e2 : (b ∣_ V) p' = v := V.ι.isOpenEmbedding.injective (by
      rw [← h2, ← hi]; exact congr($(morphismRestrict_ι b V) p'))
    rw [← e1, ← e2]
    exact congr($(hp.w) p')
end IsChart
end GlobalTheory.CompanionTheory.FreeQuotGlue
