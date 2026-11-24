-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.DiscCover.cover_of_radii
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:19.470007+00:00
-- url     : https://prove2.me/submissions/10e8c1e7-3c14-4686-a1f6-9ab5216a0317

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_const_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_line_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_mem_line_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric
namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover
theorem _root_.solution (hCount : UnbranchedProperCountConstant.Statement) (σ : Type) [Fintype σ]
    (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (hw : w ∈ Y) (hcomp : IsCompact (Y ∩ closedBall w r))
    (hsph : ∀ x ∈ Y, dist x w = r → A x ∉ ball (A w) ρ)
    (hiso : ∀ x ∈ Y ∩ closedBall w r, A x = A w → x = w)
    (hsheet : ∀ x ∈ Y ∩ closedBall w r, A x ≠ A w → A x ∈ ball (A w) ρ →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ Y ∩ V = g '' O)
    (hsurj : A '' (Y ∩ ball w r) ∈ 𝓝 (A w)) :
    ∃ N : ℕ, IsCentredDiscCover (Y ∩ (ball w r ∩ A ⁻¹' ball (A w) ρ)) w
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) ρ N := by
  set B := ball w r ∩ A ⁻¹' ball (A w) ρ with hBdef
  have hBopen : IsOpen B := isOpen_ball.inter (isOpen_ball.preimage A.continuous)
  have hclosed : ∀ C : Set (Fin 1 → ℂ), IsClosed C → C ⊆ ball (A w) ρ →
      IsCompact {x | x ∈ Y ∩ B ∧ A x ∈ C} := by
    intro C hC hCD
    have heq : {x | x ∈ Y ∩ B ∧ A x ∈ C} = (Y ∩ closedBall w r) ∩ A ⁻¹' C := by
      ext x
      constructor
      · rintro ⟨⟨hxY, hxb, -⟩, hxC⟩
        exact ⟨⟨hxY, ball_subset_closedBall hxb⟩, hxC⟩
      · rintro ⟨⟨hxY, hxb⟩, hxC⟩
        have hD := hCD hxC
        refine ⟨⟨hxY, ?_, hD⟩, hxC⟩
        rcases (mem_closedBall.1 hxb).lt_or_eq with h | h
        · exact mem_ball.2 h
        · exact absurd hD (hsph x hxY h)
    rw [heq]
    exact hcomp.inter_right (hC.preimage A.continuous)
  have hsec : ∀ x ∈ Y ∩ B, A x ≠ A w →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        DifferentiableOn ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ (Y ∩ B) ∩ V = g '' O := by
    intro x hx hne
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ :=
      hsheet x ⟨hx.1, ball_subset_closedBall hx.2.1⟩ hne hx.2.2
    have hgc : ContinuousOn g O := hg.continuousOn
    refine ⟨O ∩ g ⁻¹' B, V ∩ B, g, hgc.isOpen_inter_preimage hO hBopen, hV.inter hBopen, ⟨hxV, hx.2⟩,
      hg.differentiableOn.mono Set.inter_subset_left, fun t ht => hAg t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    simp only [Set.mem_inter_iff]
    tauto
  obtain ⟨N, hN⟩ := hCount σ (Y ∩ B) 1 A (ball (A w) ρ) (fun y => y 0 - A w 0) isOpen_ball
    (convex_ball (A w) ρ).isPreconnected (fun x hx => hx.2.2)
    (fun K hK hKc => hclosed K hKc.isClosed hK)
    (fun y _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt y).sub
      analyticAt_const)
    (fun x hx hne => by
      obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx (fun h => hne (by simp [h]))
      exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩)
  refine ⟨N, ?_⟩
  unfold IsCentredDiscCover
  refine ⟨⟨hw, mem_ball_self hr, mem_ball_self hρ⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnh := Filter.inter_mem hsurj (ball_mem_nhds (A w) hρ)
    have hnb : (𝓝[≠] (A w)).NeBot := Module.punctured_nhds_neBot ℂ (Fin 1 → ℂ) (A w)
    obtain ⟨y, ⟨⟨x, hx, hxy⟩, hyD⟩, hyne⟩ :=
      Filter.nonempty_of_mem
        (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hnh) self_mem_nhdsWithin : _ ∈ 𝓝[≠] (A w))
    have hc := hN y hyD (sub_ne_zero.2 fun h => hyne (line_ext h))
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      subst h0
      have hempty : {z | z ∈ Y ∩ B ∧ A z = y} = ∅ := Set.encard_eq_zero.1 (by simpa using hc)
      have hmem : x ∈ {z | z ∈ Y ∩ B ∧ A z = y} :=
        ⟨⟨hx.1, hx.2, by simpa [Set.mem_preimage, hxy] using hyD⟩, hxy⟩
      rw [hempty] at hmem
      exact hmem
    · exact h0
  · exact fun x hx => mem_line_ball.1 hx.2.2
  · exact fun x hx hpx => hiso x ⟨hx.1, ball_subset_closedBall hx.2.1⟩ (line_ext hpx)
  · intro t ht hne
    have hc : (fun _ : Fin 1 => t) ∈ ball (A w) ρ := mem_line_ball.2 ht
    have h := hN (fun _ => t) hc (sub_ne_zero.2 hne)
    have heq : {x | x ∈ Y ∩ B ∧
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) x = t} =
        {x | x ∈ Y ∩ B ∧ A x = fun _ => t} := by
      ext x
      constructor
      · rintro ⟨hx, h1⟩
        exact ⟨hx, line_ext h1⟩
      · rintro ⟨hx, h1⟩
        refine ⟨hx, ?_⟩
        show A x 0 = t
        rw [h1]
    rw [heq]
    exact h
  · intro K hK hKc
    exact hclosed ((fun y : Fin 1 → ℂ => y 0) ⁻¹' K) (hKc.isClosed.preimage (continuous_apply 0))
      (fun y hy => mem_line_ball.2 (hK hy))
  · intro x hx hne
    have hne' : A x ≠ A w := fun h => hne (by
      show A x 0 = A w 0
      rw [h])
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hne'
    have hcc : Continuous (fun (t : ℂ) (_ : Fin 1) => t) := continuous_pi fun _ => continuous_id
    have hcd : Differentiable ℂ (fun (t : ℂ) (_ : Fin 1) => t) :=
      differentiable_pi.2 fun _ => differentiable_id
    have hcs : Function.Surjective (fun (t : ℂ) (_ : Fin 1) => t) := fun y => ⟨y 0, const_coord y⟩
    refine ⟨(fun (t : ℂ) (_ : Fin 1) => t) ⁻¹' O, V, g ∘ (fun (t : ℂ) (_ : Fin 1) => t),
      hO.preimage hcc, hV, hxV, hg.comp hcd.differentiableOn (fun t ht => ht), fun t ht => ?_, ?_⟩
    · show A (g (fun _ => t)) 0 = t
      rw [hAg _ ht]
    · rw [Set.image_comp, Set.image_preimage_eq O hcs]
      exact hYV
end GlobalTheory.CompanionTheory.ComplexSets.DiscCover
