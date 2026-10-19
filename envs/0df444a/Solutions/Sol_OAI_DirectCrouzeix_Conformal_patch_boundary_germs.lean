-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.patch_boundary_germs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:02:31.690175+00:00
-- url     : https://prove2.me/submissions/57aa5b10-58a5-4fea-97d7-6d548808aa71

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Continuation.lean:L69-L114
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.patch_boundary_germs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection

-- ---- from OAI.Analysis.DirectCrouzeix.Continuation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

theorem boundary_germs_compatible {U : Set ℂ} (hU : IsOpen U)
    {p q z : ℂ} (hp : p ∈ closure U) (hq : q ∈ closure U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hzp : z ∈ ball p r) (hzq : z ∈ ball q s)
    {E G f : ℂ → ℂ}
    (hE : AnalyticOnNhd ℂ E (ball p (3*r)))
    (hG : AnalyticOnNhd ℂ G (ball q (3*s)))
    (he : EqOn E f (ball p (3*r) ∩ U))
    (hg : EqOn G f (ball q (3*s) ∩ U)) : E z = G z := by
  let V := ball p (3*r) ∩ ball q (3*s)
  have hVo : IsOpen V := isOpen_ball.inter isOpen_ball
  have hmeet : (V ∩ closure U).Nonempty := by
    have hd : dist p q < r + s := by
      have := dist_triangle p z q
      rw [dist_comm p z] at this
      have hpz := mem_ball.mp hzp
      have hqz := mem_ball.mp hzq
      linarith
    rcases le_total r s with hrs | hsr
    · refine ⟨p, ⟨mem_ball_self (by positivity), ?_⟩, hp⟩
      rw [mem_ball]
      linarith
    · refine ⟨q, ⟨?_, mem_ball_self (by positivity)⟩, hq⟩
      rw [mem_ball, dist_comm]
      linarith
  obtain ⟨b, hbV, hbU⟩ := hmeet
  obtain ⟨a, haV, haU⟩ := mem_closure_iff_nhds.mp hbU V (hVo.mem_nhds hbV)
  have heq : E =ᶠ[𝓝 a] G := by
    filter_upwards [(hVo.inter hU).mem_nhds ⟨haV, haU⟩] with w hw
    exact (he ⟨hw.1.1, hw.2⟩).trans (hg ⟨hw.1.2, hw.2⟩).symm
  exact (hE.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono inter_subset_right)
    ((convex_ball p (3*r)).inter (convex_ball q (3*s))).isPreconnected haV heq
    ⟨ball_subset_ball (by linarith) hzp, ball_subset_ball (by linarith) hzq⟩

theorem patch_boundary_germs {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hloc : ∀ p ∈ closure U, ∃ r > 0, ∃ E : ℂ → ℂ,
      AnalyticOnNhd ℂ E (ball p (3*r)) ∧ EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0) :
    ∃ V : Set ℂ, ∃ F : ℂ → ℂ, IsOpen V ∧ closure U ⊆ V ∧
      AnalyticOnNhd ℂ F V ∧ EqOn F f U ∧
      (∀ z ∈ V, ‖F z‖ < 1 ↔ z ∈ U) ∧ (∀ p ∈ closure U, deriv F p ≠ 0) := by
  classical
  choose r hr E hE he hside hd using hloc
  let V : Set ℂ := ⋃ p : closure U, ball (p : ℂ) (r p p.property)
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_ball
  have hUV : closure U ⊆ V := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩, mem_ball_self (hr p hp)⟩
  have hchoose : ∀ z ∈ V, ∃ p : closure U, z ∈ ball (p : ℂ) (r p p.property) := by
    intro z hz
    exact mem_iUnion.mp hz
  let F : ℂ → ℂ := fun z => if hz : z ∈ V then
    E (hchoose z hz).choose (hchoose z hz).choose.property z else f z
  have hFE : ∀ p : closure U, EqOn F (E p p.property) (ball (p : ℂ) (r p p.property)) := by
    intro p z hz
    have hzV : z ∈ V := mem_iUnion.mpr ⟨p,hz⟩
    dsimp only [F]
    rw [dite_eq_left hzV]
    exact boundary_germs_compatible hU (hchoose z hzV).choose.property p.property
      (hr _ _) (hr _ _) (hchoose z hzV).choose_spec hz
      (hE _ _) (hE _ _) (he _ _) (he _ _)
  refine ⟨V,F,hV,hUV,?_,?_,?_,?_⟩
  · intro z hz
    obtain ⟨p,hp⟩ := hchoose z hz
    apply (hE p p.property z (ball_subset_ball (by linarith [hr p p.property]) hp)).congr
    filter_upwards [isOpen_ball.mem_nhds hp] with w hw
    exact (hFE p hw).symm
  · intro z hz
    exact (hFE ⟨z,subset_closure hz⟩ (mem_ball_self (hr _ _))).trans
      (he z (subset_closure hz) ⟨mem_ball_self (by linarith [hr z (subset_closure hz)]),hz⟩)
  · intro z hz
    obtain ⟨p,hp⟩ := hchoose z hz
    rw [hFE p hp]
    exact hside p p.property z (ball_subset_ball (by linarith [hr p p.property]) hp)
  · intro p hp
    have hevent : F =ᶠ[𝓝 p] E p hp := by
      filter_upwards [ball_mem_nhds p (hr p hp)] with z hz
      exact hFE ⟨p,hp⟩ hz
    rw [hevent.deriv_eq]
    exact hd p hp

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.patch_boundary_germs := @_root_.OAI.DirectCrouzeix.Conformal.patch_boundary_germs
