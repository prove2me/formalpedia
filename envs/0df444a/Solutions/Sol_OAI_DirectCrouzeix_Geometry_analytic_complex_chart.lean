-- Prove2me | solution 1 for OAI.DirectCrouzeix.Geometry.analytic_complex_chart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:16:20.412208+00:00
-- url     : https://prove2.me/submissions/e46cc075-a7fe-4aca-8946-e15221227c18

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean:L187-L223
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Geometry.analytic_complex_chart. The node keeps its source
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

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

theorem analytic_complex_chart {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hd : deriv f 0 ≠ 0) {P : ℂ → Prop} (hP : ∀ᶠ z in 𝓝 0, P z) :
    ∃ U : OpenPartialHomeomorph ℂ ℂ, (U : ℂ → ℂ) = f ∧ 0 ∈ U.source ∧
      AnalyticOnNhd ℂ U U.source ∧ AnalyticOnNhd ℂ U.symm U.target ∧
      deriv U.symm (f 0) ≠ 0 ∧ (∀ z ∈ U.source, P z) := by
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f 0) hd)
  have hed : HasFDerivAt f e.toContinuousLinearMap 0 := by
    convert! hf.differentiableAt.hasDerivAt.hasFDerivAt using 1
  obtain ⟨U,hU,h0,hi⟩ := analytic_inverse_chart hf e hed
  have he : ∀ᶠ z in 𝓝 (0:ℂ), AnalyticAt ℂ f z ∧ AnalyticAt ℂ U.symm (f z) ∧ P z := by
    filter_upwards [hf.eventually_analyticAt,hf.continuousAt.eventually hi.eventually_analyticAt,hP] with z hz hzi hzP
    exact ⟨hz,hzi,hzP⟩
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp he
  let V := U.restr (ball 0 r)
  have hs : V.source = U.source ∩ ball 0 r := by simp [V,isOpen_ball.interior_eq]
  have ht : V.target = U.target ∩ U.symm ⁻¹' ball 0 r := by simp [V,isOpen_ball.interior_eq]
  have hV : (V : ℂ → ℂ) = f := by simpa [V] using hU
  have hVi : (V.symm : ℂ → ℂ) = U.symm := rfl
  have ht0 : f 0 ∈ U.target := hU ▸ U.map_source h0
  have hui0 : U.symm (f 0) = 0 := by simpa only [hU] using U.left_inv h0
  have hdi := U.hasDerivAt_symm ht0 hd (show HasDerivAt U (deriv f 0) (U.symm (f 0)) by
    rw [hui0,hU]; exact hf.differentiableAt.hasDerivAt)
  refine ⟨V,hV,?_,?_,?_,?_,?_⟩
  · rw [hs]; exact ⟨h0,mem_ball_self hr⟩
  · intro z hz
    rw [hV]
    exact (hrB ((hs ▸ hz).2)).1
  · intro z hz
    rw [hVi]
    have hzS := U.map_target ((ht ▸ hz).1)
    have hi := (hrB ((ht ▸ hz).2)).2.1
    rw [← hU,U.right_inv ((ht ▸ hz).1)] at hi
    exact hi
  · rw [hVi,hdi.deriv]
    exact inv_ne_zero hd
  · intro z hz
    exact (hrB ((hs ▸ hz).2)).2.2

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


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Geometry.analytic_complex_chart := @_root_.OAI.DirectCrouzeix.Geometry.analytic_complex_chart
