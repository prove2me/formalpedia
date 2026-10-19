-- Prove2me | solution 1 for OAI.DirectCrouzeix.Conformal.local_riemann_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:06:10.000142+00:00
-- url     : https://prove2.me/submissions/df09ab8b-a5c4-449d-a7fd-165ee45ac92a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ConformalCollar.lean:L43-L127
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Conformal.local_riemann_extension. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_holomorphic_reflection_modulus
import Theorems.Thm_OAI_DirectCrouzeix_Conformal_norm_tendsto_one_boundary

-- ---- from OAI.Analysis.DirectCrouzeix.ConformalCollar ----
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

theorem local_riemann_extension {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U)
    (C : AnalyticBoundaryChart U p) :
    ∃ r > 0, ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball p (3*r)) ∧
      EqOn E f (ball p (3*r) ∩ U) ∧
      (∀ z ∈ ball p (3*r), ‖E z‖ < 1 ↔ z ∈ U) ∧ deriv E p ≠ 0 := by
  have hphia : C.chart 0 ≠ a := by rw [C.at_zero]; intro he; exact hp (he ▸ ha)
  have hcn := (C.analytic 0 C.zero_mem).continuousAt
  have hav : ∀ᶠ z in 𝓝 (0 : ℂ), C.chart z ≠ a :=
    hcn.eventually (isClosed_singleton.isOpen_compl.mem_nhds hphia)
  obtain ⟨R,hR,hRB⟩ : ∃ R > 0, closedBall (0 : ℂ) R ⊆
      C.chart.source ∩ {z | C.chart z ≠ a} :=
    nhds_basis_closedBall.mem_iff.mp
      (inter_mem (C.chart.open_source.mem_nhds C.zero_mem) hav)
  have hRU : ∀ z ∈ closedBall (0 : ℂ) R, 0 < z.im → C.chart z ∈ U :=
    fun z hz hi => (C.side z (hRB hz).1).mpr hi
  have hfa : AnalyticOnNhd ℂ f U := hf.holomorphic.analyticOnNhd hU
  have hfcomp : AnalyticOnNhd ℂ (f ∘ C.chart) (closedBall 0 R ∩ {z | 0 < z.im}) := by
    intro z hz
    exact (hfa _ (hRU z hz.1 hz.2)).comp (C.analytic z (hRB hz.1).1)
  have hncomp : ∀ z ∈ closedBall 0 R ∩ {z : ℂ | 0 < z.im}, (f ∘ C.chart) z ≠ 0 := by
    intro z hz he
    exact (hRB hz.1).2 (hf.injective (hRU z hz.1 hz.2) ha (he.trans hf.normalized.symm))
  have hbcomp : ∀ z ∈ closedBall 0 R ∩ {z : ℂ | 0 < z.im}, ‖(f ∘ C.chart) z‖ < 1 := by
    intro z hz
    exact mem_ball_zero_iff.mp (hf.disk (hRU z hz.1 hz.2))
  have hlcomp : ∀ z ∈ closedBall 0 R, z.im = 0 →
      Tendsto (fun w => ‖(f ∘ C.chart) w‖) (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 1) := by
    intro z hz hi
    have hzS := (hRB hz).1
    have hpU : C.chart z ∉ U := by
      rw [C.side z hzS, hi]
      exact lt_irrefl _
    apply (norm_tendsto_one_boundary hU hf hs hpU).comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(C.analytic z hzS).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [(nhdsWithin_le_nhds : 𝓝[{w : ℂ | 0 < w.im}] z ≤ 𝓝 z)
      (C.chart.open_source.mem_nhds hzS), self_mem_nhdsWithin] with w hwS hwIm
    exact (C.side w hwS).mpr hwIm
  obtain ⟨G,hG,hGe,hGreal,hGd,hGside⟩ :=
    holomorphic_reflection_modulus hR hfcomp hncomp hbcomp hlcomp
  have hpT : p ∈ C.chart.target := by
    simpa only [C.at_zero] using C.chart.map_source C.zero_mem
  have hInv : C.chart.symm p = 0 :=
    (congrArg C.chart.symm C.at_zero.symm).trans (C.chart.left_inv C.zero_mem)
  have hNear : {z : ℂ | z ∈ C.chart.target ∧ C.chart.symm z ∈ ball 0 R} ∈ 𝓝 p := by
    apply inter_mem (C.chart.open_target.mem_nhds hpT)
    have := (C.inverse_analytic p hpT).continuousAt.preimage_mem_nhds
      (ball_mem_nhds (C.chart.symm p) hR)
    change C.chart.symm ⁻¹' ball (0 : ℂ) R ∈ 𝓝 p
    simpa only [hInv] using this
  obtain ⟨S,hS,hSB⟩ := Metric.mem_nhds_iff.mp hNear
  let E : ℂ → ℂ := G ∘ C.chart.symm
  have hE : AnalyticOnNhd ℂ E (ball p S) := by
    intro z hz
    exact (hG _ (hSB hz).2).comp (C.inverse_analytic z (hSB hz).1)
  have hEs : ∀ z ∈ ball p S, ‖E z‖ < 1 ↔ z ∈ U := by
    intro z hz
    have ht := (hSB hz).1
    change ‖G (C.chart.symm z)‖ < 1 ↔ z ∈ U
    rw [hGside _ (hSB hz).2, ← C.side _ (C.chart.map_target ht), C.chart.right_inv ht]
  have hEe : EqOn E f (ball p S ∩ U) := by
    intro z hz
    have ht := (hSB hz.1).1
    have him : 0 < (C.chart.symm z).im := by
      apply (C.side _ (C.chart.map_target ht)).mp
      rw [C.chart.right_inv ht]
      exact hz.2
    change G (C.chart.symm z) = f z
    rw [hGe ⟨(hSB hz.1).2,him⟩]
    simp only [Function.comp_apply, C.chart.right_inv ht]
  have hEd : deriv E p ≠ 0 := by
    have hGc := (hG 0 (mem_ball_self hR)).differentiableAt.hasDerivAt
    have hiC := (C.inverse_analytic p hpT).differentiableAt.hasDerivAt
    have hGc' : HasDerivAt G (deriv G 0) (C.chart.symm p) := by
      simpa only [hInv] using hGc
    have hh := hGc'.comp p hiC
    change deriv (G ∘ C.chart.symm) p ≠ 0
    rw [hh.deriv]
    exact mul_ne_zero hGd C.inverse_derivative
  refine ⟨S/3,by positivity,E,?_,?_,?_,hEd⟩
  · simpa only [show 3*(S/3) = S by ring] using hE
  · simpa only [show 3*(S/3) = S by ring] using hEe
  · simpa only [show 3*(S/3) = S by ring] using hEs

end Conformal

end DirectCrouzeix

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Conformal.local_riemann_extension := @_root_.OAI.DirectCrouzeix.Conformal.local_riemann_extension
