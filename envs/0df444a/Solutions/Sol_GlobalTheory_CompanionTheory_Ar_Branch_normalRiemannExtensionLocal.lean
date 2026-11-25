-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Branch.normalRiemannExtensionLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:52.348055+00:00
-- url     : https://prove2.me/submissions/7b6798af-068b-402a-b97f-0e575ab50a5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtensionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalUniversalDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormalRiemannExtensionLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_subset_closure_diff_d630fe876a88


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Branch
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial Topology Filter Metric
namespace GlobalTheory.CompanionTheory.Ar.Branch
theorem _root_.solution (hud : LocalUniversalDenominator.Statement)
    (hbq : NormalBoundedQuotient.Statement) (hvan : VanishNearPoint.Statement) :
    NormalRiemannExtensionLocal.Statement := by
  intro σ _ I h w U f hI hIc hh hw hU hf hb
  classical
  have hpoly : ∀ q : MvPolynomial σ ℂ, Differentiable ℂ (fun z : σ → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [eval_add]; exact hp.add hq
    | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)
  obtain ⟨g, hg, N, hNo, hwN, hNU, F, hF, hFg⟩ := hud σ I h w U f hI hh hw hU hf hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hhg : h * g ∉ I := fun hm => (hI.mem_or_mem hm).elim hh hg
  obtain ⟨B, hBo, hwB, hBN, hdense⟩ : ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ N ∧
      zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0}) := by
    refine ⟨N, hNo, hwN, subset_rfl, fun z hz => ?_⟩
    have h1 := hNo.inter_closure ⟨hz.2, zeroSetIn_subset_closure_diff hvan I (h * g) hI hhg hz.1⟩
    refine closure_mono (fun y hy => ?_) h1
    exact ⟨⟨hy.2.1, hy.1⟩, hy.2.2⟩
  set T := (zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0} with hT
  have hGd : Differentiable ℂ (fun z : σ → ℂ => eval z g) := hpoly g

  have hTS : ∀ z ∈ T, z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} ∧ eval z g ≠ 0 ∧
      eval z g * f z = F z := by
    intro z hz
    have hz2 : eval z h ≠ 0 ∧ eval z g ≠ 0 := by
      simpa only [Set.mem_ofPred_eq, eval_mul, mul_eq_zero, not_or] using hz.2
    exact ⟨⟨⟨hz.1.1, hNU (hBN hz.1.2)⟩, hz2.1⟩, hz2.2,
      hFg z ⟨⟨hz.1.1, hBN hz.1.2⟩, hz2.1⟩⟩
  have hTf : ∀ z ∈ T, F z / eval z g = f z := fun z hz => by
    obtain ⟨-, hg0, he⟩ := hTS z hz
    rw [← he, mul_div_cancel_left₀ _ hg0]
  have hbound : (fun z => F z / eval z g) '' ((zeroSetIn I ∩ B) \ {z | eval z g = 0}) ⊆
      Metric.closedBall 0 M := by
    rintro _ ⟨p, hp, rfl⟩
    have hpc : p ∈ closure T := hdense hp.1
    have hcont : ContinuousWithinAt (fun z => F z / eval z g) T p :=
      (((hF.continuousOn.continuousAt (hNo.mem_nhds (hBN hp.1.2))).div
        (hGd p).continuousAt hp.2)).continuousWithinAt
    refine closure_minimal ?_ Metric.isClosed_closedBall (hcont.mem_closure_image hpc)
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖F z / eval z g‖ ≤ M
    rw [hTf z hz]
    exact hM _ ⟨z, (hTS z hz).1, rfl⟩
  have hnv : ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z g = 0) := by
    intro hev
    obtain ⟨z, hzW, hzT⟩ := mem_closure_iff_nhds.1 (hdense ⟨hw, hwB⟩) _ hev
    exact (hTS z hzT).2.1 (hzW hzT.1.1)
  obtain ⟨V, hVo, hwV, H, hH, hFGH⟩ := hbq σ I w B F (fun z => eval z g) hI hIc hw hBo hwB
    (hF.mono hBN) hGd.differentiableOn hnv ((Metric.isBounded_closedBall).subset hbound)
  refine ⟨V ∩ B, hVo.inter hBo, ⟨hwV, hwB⟩, fun z hz => hNU (hBN hz.2), H, hH.mono Set.inter_subset_left, ?_⟩
  intro p hp
  obtain ⟨Up, hUpo, hpUp, Fp, hFp, hfFp⟩ :=
    hf p ⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩
  rw [hfFp ⟨⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩, hpUp⟩]

  set O := V ∩ Up
  have hOo : IsOpen O := hVo.inter hUpo
  have hpO : p ∈ O := ⟨hp.1.2.1, hpUp⟩
  set s := O ∩ T
  have heq : Set.EqOn H Fp s := by
    intro z hz
    obtain ⟨hzS, hg0, he⟩ := hTS z hz.2
    have h1 : eval z g * H z = eval z g * f z := by
      rw [he, hFGH z ⟨hz.2.1.1, hz.1.1⟩]
    rw [mul_left_cancel₀ hg0 h1, hfFp ⟨hzS, hz.1.2⟩]
  have hsO : insert p s ⊆ O := Set.insert_subset_iff.2 ⟨hpO, fun z hz => hz.1⟩
  exact heq.of_subset_closure ((hH.mono Set.inter_subset_left).continuousOn.mono hsO)
    ((hFp.mono Set.inter_subset_right).continuousOn.mono hsO) (Set.subset_insert p s)
    (Set.insert_subset_iff.2 ⟨hOo.inter_closure ⟨hpO, hdense ⟨hp.1.1, hp.1.2.2⟩⟩, subset_closure⟩)
    (Set.mem_insert p s)
end GlobalTheory.CompanionTheory.Ar.Branch
