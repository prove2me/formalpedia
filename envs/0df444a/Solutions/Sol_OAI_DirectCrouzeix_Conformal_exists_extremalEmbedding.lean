-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.exists_extremalEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:44:41.06763+00:00
-- url     : https://prove2.me/submissions/1201ac5f-1cf7-4a52-8ee0-56ef4edec79a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExtremalEmbedding.lean:L164-L233
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.exists_extremalEmbedding. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_bounded_holomorphic_compact
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_constant_or_injective_limit
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_exists_injective_not_dense_image_deriv_ne_zero
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_zero_or_nonvanishing_limit

-- ---- from OAI.Analysis.DirectCrouzeix.NormalFamilies ----
namespace OAI

universe u_131

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

theorem continuousMap_limit {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → C(U, ℂ)} {g : C(U, ℂ)} (hl : Tendsto F atTop (𝓝 g)) :
    TendstoLocallyUniformlyOn (fun n => extend U (F n)) (extend U g) atTop U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [extend_coe, Function.comp_def] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hl

theorem bounded_holomorphic_closure {U : Set ℂ} (hU : IsOpen U)
    {S : Set C(U, ℂ)}
    (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1)
    {g : C(U, ℂ)} (hg : g ∈ closure S) :
    DifferentiableOn ℂ (extend U g) U ∧ ∀ z : U, ‖g z‖ ≤ 1 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨F, hF, hl⟩ := mem_closure_iff_seq_limit.mp hg
  have hl' := continuousMap_limit hU hl
  refine ⟨hl'.differentiableOn (Eventually.of_forall (fun n => (hS _ (hF n)).1)) hU, ?_⟩
  intro z
  have ht := (hl'.tendsto_at z.property).norm
  simpa only [extend_coe] using le_of_tendsto ht
    (Eventually.of_forall (fun n => by simpa only [extend_coe] using (hS _ (hF n)).2 z))

theorem derivative_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {S : Set C(U, ℂ)} (hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U)
    {a : ℂ} (ha : a ∈ U) :
    ContinuousOn (fun f : C(U, ℂ) => deriv (extend U f) a) S := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro F g hl
  have ht : Tendsto (fun n => (F n : C(U, ℂ))) atTop (𝓝 (g : C(U, ℂ))) :=
    continuous_subtype_val.continuousAt.tendsto.comp hl
  have hlu := (continuousMap_limit hU ht).deriv
    (Eventually.of_forall (fun n => hS _ (F n).property)) hU
  exact hlu.tendsto_at ha

theorem strict_bound_of_normalized {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {a : ℂ} (ha : a ∈ U) (hfa : f a = 0) :
    MapsTo f U (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra hn
  have he : ‖f z‖ = 1 := le_antisymm (hb _ hz) (le_of_not_gt hn)
  have hm : IsMaxOn (norm ∘ f) U z := fun w hw => by
    change ‖f w‖ ≤ ‖f z‖
    rw [he]
    exact hb w hw
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hUc hU hf hz hm ha
  simp [hfa, he] at heq

open Function Complex

open scoped Pointwise

end Conformal

end DirectCrouzeix

end

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.ExtremalEmbedding ----
/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

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

/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

The following conformal embedding declarations are adapted from Mathlib.Analysis.Complex.RiemannMapping.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Complex/RiemannMapping.lean

This code has been modified.
-/

lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by

  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩

  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)

  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

theorem exists_normalizedEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f := by
  obtain ⟨e, hed, hei, he'⟩ :=
    exists_mapsTo_unitBall_injOn_deriv_ne_zero hU hUc hproper
  have he : DifferentiableOn ℂ e U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (he' z hz)).differentiableWithinAt
  let f : ℂ → ℂ := fun z => (e z - e a) / 2
  have hf' (z : ℂ) (hz : z ∈ U) : HasDerivAt f (deriv e z / 2) z :=
    ((he.hasDerivAt (hU.mem_nhds hz)).sub_const _).div_const _
  refine ⟨f, ⟨he.sub_const _ |>.div_const _, ?_, ?_, ?_, by simp [f]⟩⟩
  · intro z hz
    rw [mem_ball_zero_iff]
    dsimp [f]
    rw [norm_div]
    norm_num
    have h1 := norm_sub_le (e z) (e a)
    have h2 : ‖e z‖ < 1 := mem_ball_zero_iff.mp (hed hz)
    have h3 : ‖e a‖ < 1 := mem_ball_zero_iff.mp (hed ha)
    linarith
  · intro z hz w hw heq
    apply hei hz hw
    dsimp [f] at heq
    exact sub_left_injective ((div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp heq)
  · intro z hz
    rw [(hf' z hz).deriv]
    exact div_ne_zero (he' z hz) (by norm_num)

theorem extend_restrict_eventuallyEq {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {a : ℂ} (ha : a ∈ U) :
    extend U (fun z : U => f z) =ᶠ[𝓝 a] f := by
  filter_upwards [hU.mem_nhds ha] with z hz
  simp [extend, hz]

theorem exists_extremalEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧
      ∀ g, NormalizedEmbedding U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let S : Set C(U, ℂ) := {f | NormalizedEmbedding U a (extend U f)}
  have hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1 := by
    intro f hf
    refine ⟨hf.holomorphic, fun z => ?_⟩
    simpa only [extend_coe] using (mem_ball_zero_iff.mp (hf.disk z.property)).le
  have hCS := bounded_holomorphic_compact hU S hS
  have hLS (g : C(U, ℂ)) (hg : g ∈ closure S) := bounded_holomorphic_closure hU hS hg
  have hmk (f : ℂ → ℂ) (hf : NormalizedEmbedding U a f) :
      (⟨fun z : U => f z, hf.holomorphic.continuousOn.domRestrict⟩ : C(U, ℂ)) ∈ S := by
    let g : C(U, ℂ) := ⟨fun z : U => f z, hf.holomorphic.continuousOn.domRestrict⟩
    have heq (z : ℂ) (hz : z ∈ U) : extend U g =ᶠ[𝓝 z] f :=
      extend_restrict_eventuallyEq hU hz
    change NormalizedEmbedding U a (extend U g)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact ((hf.holomorphic.differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq
        (heq z hz)).differentiableWithinAt
    · intro z hz
      rw [(heq z hz).self_of_nhds]
      exact hf.disk hz
    · intro z hz w hw he
      apply hf.injective hz hw
      rwa [(heq z hz).self_of_nhds, (heq w hw).self_of_nhds] at he
    · intro z hz
      rw [(heq z hz).deriv_eq]
      exact hf.derivative z hz
    · rw [(heq a ha).self_of_nhds]
      exact hf.normalized
  obtain ⟨f₀, hf₀⟩ := exists_normalizedEmbedding hU hUc hproper ha
  let F₀ : C(U, ℂ) := ⟨fun z : U => f₀ z, hf₀.holomorphic.continuousOn.domRestrict⟩
  have hF₀ : F₀ ∈ S := hmk _ hf₀
  obtain ⟨g, hg, hmax⟩ := hCS.exists_isMaxOn ⟨F₀, subset_closure hF₀⟩
    (derivative_continuousOn hU (fun f hf => (hLS _ hf).1) ha).norm
  have hpos : 0 < ‖deriv (extend U g) a‖ :=
    (norm_pos_iff.mpr (hF₀.derivative a ha)).trans_le (hmax (subset_closure hF₀))
  obtain ⟨F, hF, hl⟩ := mem_closure_iff_seq_limit.mp hg
  have hlu := continuousMap_limit hU hl
  have hd := (hLS _ hg).1
  have hn : extend U g a = 0 := by
    exact tendsto_nhds_unique (hlu.tendsto_at ha)
      (by simpa only [(hF _).normalized] using tendsto_const_nhds (x := (0 : ℂ)))
  have hi : InjOn (extend U g) U := by
    apply (constant_or_injective_limit hU hUc.isPathConnected.isConnected.isPreconnected
      (fun n => (hF n).holomorphic) (fun n => (hF n).injective) hlu).resolve_left
    rintro ⟨c, hc⟩
    have he : extend U g =ᶠ[𝓝 a] (fun _ => c) := by
      filter_upwards [hU.mem_nhds ha] with z hz
      exact hc hz
    have hz := he.deriv_eq
    simp only [deriv_const] at hz
    exact (ne_of_gt hpos) (by rw [hz, norm_zero])
  have hder : ∀ z ∈ U, deriv (extend U g) z ≠ 0 := by
    have hdl := hlu.deriv (Eventually.of_forall (fun n => (hF n).holomorphic)) hU
    apply (zero_or_nonvanishing_limit hU hUc.isPathConnected.isConnected.isPreconnected
      (fun n => ((hF n).holomorphic.analyticOnNhd hU).deriv.differentiableOn)
      (fun n => (hF n).derivative) hdl).resolve_left
    intro he
    exact (ne_of_gt hpos) (by rw [he ha, Pi.zero_apply, norm_zero])
  have hgN : NormalizedEmbedding U a (extend U g) :=
    ⟨hd, strict_bound_of_normalized hU hUc.isPathConnected.isConnected.isPreconnected hd
      (fun z hz => by simpa [extend, hz] using (hLS _ hg).2 ⟨z, hz⟩) ha hn, hi, hder, hn⟩
  refine ⟨extend U g, hgN, fun f hf => ?_⟩
  have hm := hmax (subset_closure (hmk f hf))
  change ‖deriv (extend U (fun z : U => f z)) a‖ ≤ _ at hm
  rwa [(extend_restrict_eventuallyEq hU ha).deriv_eq] at hm

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.exists_extremalEmbedding := @_root_.OAI.DirectCrouzeix.Conformal.exists_extremalEmbedding
