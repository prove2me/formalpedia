-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.normalized_implicit_graph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:12:11.394983+00:00
-- url     : https://prove2.me/submissions/566cb7b7-279d-491a-bab5-5228f3e33549

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean:L60-L124
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.normalized_implicit_graph. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Theorems.Thm_OAI_DirectCrouzeix_Geometry_analytic_inverse_chart

-- ---- from OAI.Analysis.DirectCrouzeix.AnalyticCharts ----
namespace OAI

universe u_133 u_134 u_135

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

theorem conjugatePair_continuous : Continuous conjugatePair :=
  (Complex.continuous_conj.comp continuous_fst).prodMk (Complex.continuous_conj.comp continuous_snd)

theorem normalized_implicit_graph {F : ℂ × ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = 1) {b : ℝ} (hb : 0 < b)
    (hd : HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0)
    (hconj : ∀ z, F (conjugatePair z) = conj (F z)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, F (z,g z) = 1) ∧
      (∀ᶠ z in 𝓝 0, g (conj z) = conj (g z)) := by
  let H := fun z : ℂ × ℂ => (z.1,F z-1)
  have hH0 : H 0 = 0 := by simp [H,hF0]
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (b:ℂ) hbC))
  have hH : AnalyticAt ℂ H 0 := analyticAt_fst.prod (hF.sub analyticAt_const)
  have hHd : HasFDerivAt H e.toContinuousLinearMap 0 := by
    convert! (hasFDerivAt_fst (𝕜 := ℂ) (p := (0:ℂ × ℂ))).prodMk (hd.sub_const 1) using 1
    ext <;> simp [e]
  obtain ⟨U,hU,h0,hUi⟩ := analytic_inverse_chart hH e hHd
  rw [hH0] at hUi
  have hU0 : U 0 = 0 := by rw [hU]; exact hH0
  have hi0 : U.symm 0 = 0 := by simpa only [hU0] using U.left_inv h0
  have ht0 : (0:ℂ × ℂ) ∈ U.target := hU0 ▸ U.map_source h0
  let V := fun z : ℂ => U.symm (z,0)
  have hV : AnalyticAt ℂ V 0 := hUi.comp (f := fun z : ℂ => (z,0)) (analyticAt_id.prod analyticAt_const)
  have hV0 : V 0 = 0 := hi0
  let g := fun z => (V z).2
  have hg : AnalyticAt ℂ g 0 := analyticAt_snd.comp hV
  have hvT : ∀ᶠ z in 𝓝 (0:ℂ), (z,0) ∈ U.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (U.open_target.mem_nhds ht0)
  have hvEq : ∀ᶠ z in 𝓝 (0:ℂ), H (V z) = (z,0) := by
    filter_upwards [hvT] with z hz
    exact hU ▸ U.right_inv hz
  have hvfst : ∀ᶠ z in 𝓝 (0:ℂ), (V z).1 = z := by
    filter_upwards [hvEq] with z hz
    exact congrArg Prod.fst hz
  have heq : ∀ᶠ z in 𝓝 (0:ℂ), F (z,g z) = 1 := by
    filter_upwards [hvEq,hvfst] with z hz hzf
    have hs : F (V z)-1 = 0 := congrArg Prod.snd hz
    have hev : V z = (z,g z) := Prod.ext hzf rfl
    simpa only [hev,sub_eq_zero] using hs
  have hg0 : g 0 = 0 := congrArg Prod.snd hV0
  have hgd : deriv g 0 = 0 := by
    have hdcomp := (show HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) (0,g 0) by simpa only [hg0,Prod.zero_eq_mk] using hd).comp 0 ((hasDerivAt_id (0:ℂ)).prodMk hg.differentiableAt.hasDerivAt).hasFDerivAt
    have hdconst : HasDerivAt (fun z => F (z,g z)) (b*deriv g 0) 0 := by
      convert! hdcomp.hasDerivAt using 1 ; simp [ContinuousLinearMap.comp_apply]
    have heder := hdconst.congr_of_eventuallyEq (show (fun _ : ℂ => (1:ℂ)) =ᶠ[𝓝 0] (fun z => F (z,g z)) from by filter_upwards [heq] with z hz; exact hz.symm)
    have hzero := heder.unique (hasDerivAt_const (0:ℂ) (1:ℂ))
    exact (mul_eq_zero.mp hzero).resolve_left hbC
  have hconjH (z : ℂ × ℂ) : H (conjugatePair z) = conjugatePair (H z) := by
    change (conj z.1,F (conjugatePair z)-1) = (conj z.1,conj (F z-1))
    rw [hconj]; simp
  have hvSC : ∀ᶠ z in 𝓝 (0:ℂ), conjugatePair (V z) ∈ U.source := by
    have hc : ContinuousAt (fun z => conjugatePair (V z)) 0 := conjugatePair_continuous.continuousAt.comp hV.continuousAt
    have he0 : conjugatePair (V 0) = 0 := by rw [hV0]; simp
    exact hc.preimage_mem_nhds (he0 ▸ U.open_source.mem_nhds h0)
  have htconj : ∀ᶠ z in 𝓝 (0:ℂ), (conj z,0) ∈ U.target := by
    have ht : Tendsto (conj : ℂ → ℂ) (𝓝 0) (𝓝 0) := by simpa using Complex.continuous_conj.tendsto (0:ℂ)
    exact ht.eventually hvT
  refine ⟨g,hg,hg0,hgd,heq,?_⟩
  filter_upwards [hvEq,hvSC,htconj] with z hz hzS hzT
  have he : V (conj z) = conjugatePair (V z) := by
    apply U.injOn (U.map_target hzT) hzS
    rw [hU]
    rw [hconjH,hz]
    simpa [conjugatePair] using (show H (U.symm (conj z,0)) = (conj z,0) from hU ▸ U.right_inv hzT)
  exact congrArg Prod.snd he

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.normalized_implicit_graph := @_root_.OAI.DirectCrouzeix.Geometry.normalized_implicit_graph
