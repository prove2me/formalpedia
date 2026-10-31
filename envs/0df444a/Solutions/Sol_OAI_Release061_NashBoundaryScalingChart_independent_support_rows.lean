-- Prove2me | solution 1 for OAI.Release061.NashBoundaryScalingChart.independent_support_rows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:59:56.971982+00:00
-- url     : https://prove2.me/submissions/fcfb3ab0-a8c3-4733-85ef-5ab0146766e1

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


open Set Filter Topology

theorem analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : HasFDerivAt f (i : E →L[ℂ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℂ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℂ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm
      (i : E →L[ℂ] F) := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateDerivativeRank
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology

theorem complex_span_real_linear_range {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Submodule.span ℂ (range L) =
      Submodule.span ℂ (range (fun i => L (Pi.single i 1))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    change ((x i : ℂ) • L (Pi.single i 1)) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact mem_range_self _

theorem matrix_rank_eq_complex_tangent_dimension {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Matrix.rank (fun j i => L (Pi.single i 1) j) =
      Module.finrank ℂ (Submodule.span ℂ (range L)) := by
  rw [complex_span_real_linear_range L]
  exact Matrix.rank_eq_finrank_span_cols _

theorem complex_tangent_eq_of_rank_ge {d N m : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ))
    (T : Submodule ℂ (Fin N → ℂ)) (hT : Module.finrank ℂ T = m)
    (hLT : ∀ x, L x ∈ T)
    (hr : m ≤ Matrix.rank (fun j i => L (Pi.single i 1) j)) :
    Submodule.span ℂ (range L) = T := by
  have hle : Submodule.span ℂ (range L) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact hLT x
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  simpa only [matrix_rank_eq_complex_tangent_dimension,hT] using hr

theorem chart_tangent_finrank {m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ)) {a : Fin m → ℂ}
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id) :
    Module.finrank ℂ (LinearMap.range (fderiv ℂ F a).toLinearMap) = m := by
  have hcomp := hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    hid.unique (hasFDerivAt_id a)
  have hinj : Function.Injective (fderiv ℂ F a) := by
    intro x y hxy
    have hh := congrArg (fderiv ℂ G (F a)) hxy
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh
  simpa using LinearMap.finrank_range_of_inj (f := (fderiv ℂ F a).toLinearMap) hinj

theorem real_derivative_mem_chart_tangent {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF : AnalyticAt ℂ F (G (q x))) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) (v : Fin d → ℝ) :
    fderiv ℝ q x v ∈ LinearMap.range (fderiv ℂ F (G (q x))).toLinearMap := by
  have hGc := hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFc := hF.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hc := hFc.comp x (hGc.comp x hq.hasFDerivAt)
  have he := hc.congr_of_eventuallyEq hFG.symm
  have hd := he.fderiv
  refine ⟨fderiv ℂ G (q x) (fderiv ℝ q x v),?_⟩
  exact (congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) hd).symm

theorem coordinate_derivative_rank {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hq : DifferentiableAt ℝ q x) :
    Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) =
      Module.finrank ℂ (Submodule.span ℂ (range (fderiv ℝ q x))) := by
  have he (j : Fin N) : fderiv ℝ (fun y => q y j) x =
      (ContinuousLinearMap.proj j).comp (fderiv ℝ q x) := by
    exact ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hq.hasFDerivAt).fderiv
  simp_rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  exact matrix_rank_eq_complex_tangent_dimension (fderiv ℝ q x).toLinearMap

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicSupportIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology
open scoped Classical

theorem log_norm_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : E → ℂ) {x : E} (ha : AnalyticAt ℂ (fun z => Complex.log (h z)) x) :
    fderiv ℝ (fun z => Real.log ‖h z‖) x =
      Complex.reCLM.comp ((fderiv ℂ (fun z => Complex.log (h z)) x).restrictScalars ℝ) := by
  have hr := Complex.reCLM.hasFDerivAt.comp x (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun z => (Complex.log (h z)).re) _ x at hr
  have he : (fun z => (Complex.log (h z)).re) = (fun z => Real.log ‖h z‖) :=
    funext (fun _ => Complex.log_re _)
  rw [he] at hr
  exact hr.fderiv

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashCellGeometricRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology

theorem real_parametric_span_eq_chart_of_rank_ge {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ (range (fderiv ℝ q x)) =
      LinearMap.range (fderiv ℂ F 0).toLinearMap := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  apply complex_tangent_eq_of_rank_ge (fderiv ℝ q x).toLinearMap
    (LinearMap.range (fderiv ℂ F 0).toLinearMap)
  · exact chart_tangent_finrank F G hF (hF0 ▸ hG) hGF
  · intro v
    have hv := real_derivative_mem_chart_tangent F G q (hG0 ▸ hF) hG hq hFG v
    change fderiv ℝ q x v ∈ _
    simpa only [hG0] using hv
  · rw [matrix_rank_eq_complex_tangent_dimension]
    rwa [coordinate_derivative_rank q hq] at hr

end

open Set Filter Topology MeasureTheory

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InjectiveConormalFinrank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem chart_tangent_identities {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) :
    G (q x) = 0 ∧
    (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ ∧
    ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ (G ∘ q) x) = fderiv ℝ q x ∧
    Function.Injective (fderiv ℂ F 0) := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have hg : AnalyticAt ℂ G (F 0) := hF0 ▸ hG
  have hid := (hg.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ := by
    simpa only [hF0] using hid.unique (hasFDerivAt_id (0 : Affine m))
  refine ⟨hG0,hi,?_,?_⟩
  · have hr : DifferentiableAt ℝ (G ∘ q) x := hG.differentiableAt.restrictScalars ℝ |>.comp x hq
    have hf : AnalyticAt ℂ F ((G ∘ q) x) := by simpa only [Function.comp_apply,hG0] using hF
    have hh := (hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFG.symm
    simpa only [Function.comp_apply,hG0] using he.fderiv.symm
  · intro a b hab
    have hh := congrArg (fderiv ℂ G (q x)) hab
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem chart_parametric_generic {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (G ∘ q) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x)) = ⊤ := by
  obtain ⟨hG0,hi,hd,hFi⟩ := chart_tangent_identities F G q hF0 hF hG hq hGF hFG
  have hspan := real_parametric_span_eq_chart_of_rank_ge F G q hF0 hF hG hq hGF hFG hr
  have hder : fderiv ℝ (G ∘ q) x = ((fderiv ℂ G (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  refine ⟨?_,?_⟩
  · intro a b hab
    apply hqi
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  · let W := Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x))
    have hle : Submodule.span ℂ (range (fderiv ℝ q x)) ≤
        W.comap (fderiv ℂ G (q x)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      change fderiv ℂ G (q x) (fderiv ℝ q x v) ∈ W
      have he : fderiv ℂ G (q x) (fderiv ℝ q x v) = fderiv ℝ (G ∘ q) x v := by
        rw [hder]; rfl
      rw [he]
      exact Submodule.subset_span (mem_range_self v)
    apply top_unique
    intro v _
    have hv : fderiv ℂ F 0 v ∈ Submodule.span ℂ (range (fderiv ℝ q x)) := by
      rw [hspan]; exact ⟨v,rfl⟩
    have hh := hle hv
    change fderiv ℂ G (q x) (fderiv ℂ F 0 v) ∈ W at hh
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OldOffsetOldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

theorem analytic_chart_right_inverse_of_dimension {m N : ℕ} {V : Set (Affine N)}
    {a : Affine m} (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id)
    (hFV : ∀ᶠ z in 𝓝 a, F z ∈ V)
    (H : Affine m → Affine N) (J : Affine N → Affine m)
    (hH0 : H 0 = F a) (hH : AnalyticAt ℂ H 0) (hJ : AnalyticAt ℂ J (F a))
    (hJH : (J ∘ H) =ᶠ[𝓝 (0 : Affine m)] id)
    (hHJ : ∀ᶠ y in 𝓝[V] (F a), H (J y) = y) :
    ∀ᶠ y in 𝓝[V] (F a), F (G y) = y := by
  have hJ0 : J (F a) = 0 := by simpa only [Function.comp_apply,hH0,id_eq] using hJH.eq_of_nhds
  let A : Affine m → Affine m := J ∘ F
  have hA : AnalyticAt ℂ A a := hJ.comp hF
  have hA0 : A a = 0 := hJ0
  have htF : Tendsto F (𝓝 a) (𝓝[V] (F a)) := tendsto_nhdsWithin_iff.mpr ⟨hF.continuousAt,hFV⟩
  have hHA : (H ∘ A) =ᶠ[𝓝 a] F := htF hHJ
  have hH' : AnalyticAt ℂ H (A a) := hA0.symm ▸ hH
  have hdHA : (fderiv ℂ H (A a)).comp (fderiv ℂ A a) = fderiv ℂ F a :=
    ((hH'.differentiableAt.hasFDerivAt.comp a hA.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hHA.symm).unique hF.differentiableAt.hasFDerivAt
  have hdGF : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    ((hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm).unique (hasFDerivAt_id a)
  have hi : Function.Injective (fderiv ℂ A a) := by
    intro u v huv
    have hw : (fderiv ℂ F a) u = (fderiv ℂ F a) v := by
      rw [← hdHA]
      exact congrArg (fderiv ℂ H (A a)) huv
    have hx := congrArg (fderiv ℂ G (F a)) hw
    simpa only [← ContinuousLinearMap.comp_apply,hdGF,ContinuousLinearMap.id_apply] using hx
  let L := ((fderiv ℂ A a).toLinearMap.linearEquivOfInjective hi rfl).toContinuousLinearEquiv
  have hL : (L : Affine m →L[ℂ] Affine m) = fderiv ℂ A a := rfl
  obtain ⟨e,he,hes,hea⟩ := analytic_local_inverse hA L (hL.symm ▸ hA.differentiableAt.hasFDerivAt)
  have heAa : e a = A a := congrFun he a
  have hesym : e.symm (A a) = a := by rw [← heAa]; exact e.left_inv hes
  have hetarget : A a ∈ e.target := heAa ▸ e.map_source hes
  have het : Tendsto e.symm (𝓝 (A a)) (𝓝 a) := by
    simpa only [ContinuousAt,hesym] using hea.continuousAt
  let B : Affine N → Affine m := e.symm ∘ J
  have hB : Tendsto B (𝓝 (F a)) (𝓝 a) := het.comp hJ.continuousAt
  have hBHA : ∀ᶠ y in 𝓝 (F a), H (A (B y)) = F (B y) := hB hHA
  have hBGF : ∀ᶠ y in 𝓝 (F a), G (F (B y)) = B y := hB hGF
  have hJt : ∀ᶠ y in 𝓝 (F a), J y ∈ e.target :=
    hJ.continuousAt (e.open_target.mem_nhds hetarget)
  filter_upwards [hHJ,mem_nhdsWithin_of_mem_nhds hBHA,
    mem_nhdsWithin_of_mem_nhds hBGF,mem_nhdsWithin_of_mem_nhds hJt] with y hy hya hyb hyt
  have hAB : A (B y) = J y := by
    simpa only [he,B,Function.comp_apply] using e.right_inv hyt
  have hFB : F (B y) = y := by rw [← hya,hAB,hy]
  rw [hFB] at hyb
  rw [hyb,hFB]

theorem ProjectionNashChart.right_inverse_at {N m : ℕ} {V : Set (Affine N)}
    {p : Affine N} (c : ProjectionNashChart V p m) {a : Affine m}
    (ha : ‖complexRealEquiv m a‖ < c.radius)
    (H : Affine m → Affine N) (J : Affine N → Affine m)
    (hH0 : H 0 = c.inverse a) (hH : AnalyticAt ℂ H 0)
    (hJ : AnalyticAt ℂ J (c.inverse a))
    (hJH : (J ∘ H) =ᶠ[𝓝 (0 : Affine m)] id)
    (hHJ : ∀ᶠ y in 𝓝[V] (c.inverse a), H (J y) = y) :
    ∀ᶠ y in 𝓝[V] (c.inverse a), c.inverse (c.projection (y-p)) = y := by
  have hT : IsOpen {z : Affine m | ‖complexRealEquiv m z‖ < c.radius} :=
    isOpen_lt ((complexRealEquiv m).continuous.norm) continuous_const
  apply analytic_chart_right_inverse_of_dimension c.inverse (fun y => c.projection (y-p))
    (c.inverse_analytic a ha) ((c.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
    _ _ H J hH0 hH hJ hJH hHJ
  · filter_upwards [hT.mem_nhds ha] with z hz
    exact c.left_inverse z hz
  · filter_upwards [hT.mem_nhds ha] with z hz
    exact c.inverse_mem z hz

theorem NashNormalCoordinates.graph_germ_at {d m : ℕ}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine m} {a x : Fin d → ℝ}
    (c : NashNormalCoordinates B q a) (hx : x ∈ c.parameters.source)
    (hxb : c.parameters x ∈ ball 0 c.radius) :
    ∀ᶠ y in 𝓝 x, c.parameters y ∈ ball 0 c.radius ∧
      c.realCoordinates (q y-q a) = (c.parameters y,c.graph (c.parameters y)) := by
  have hs := c.parameters.open_source.mem_nhds hx
  have hb := (c.parameters.continuousAt hx).preimage_mem_nhds (isOpen_ball.mem_nhds hxb)
  filter_upwards [hs,hb] with y hy hyb
  refine ⟨hyb,?_⟩
  change complexGraphRealEquiv _ _ (c.coordinates (q y-q a)) = _
  simpa only [c.parameters.left_inv hy] using c.graph_identity (c.parameters y) hyb

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

 theorem oldPosition_inverse (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.chart.inverse (c.oldPosition (c.normal.parameters x)) = q x := by
  simpa only [oldPosition,c.normal.parameters.left_inv hgood.1] using
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.2

 theorem oldPosition_projection (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.oldPosition (c.normal.parameters x) = c.chart.projection (q x-q c.center) := by
  have h := c.chart.left_inverse (c.oldPosition (c.normal.parameters x))
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.1
  rw [c.oldPosition_inverse hgood] at h
  exact h.symm

 theorem oldOffset_projection_germ (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) :
    (fun y => c.oldOffset (c.chart.projection (q y-q c.center))) =ᶠ[𝓝 x] fun _ => 0 := by
  have hg := c.normal.graph_germ_at hgood.1 (ball_subset_ball c.graphRadius_le hgood.2.1)
  have h0 : c.chart.projection (q c.center-q c.center) = 0 := by rw [sub_self,map_zero]
  filter_upwards [hg] with y hy
  simp only [h0,sub_zero] at hy
  simp only [oldOffset,oldParameter,hy.2,sub_self]
end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectionTangentGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem projection_inverse_germ (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) :
    (fun y => c.chart.inverse (c.chart.projection (q y-q c.center))) =ᶠ[𝓝 x] q := by
  have hs := c.normal.parameters.open_source.mem_nhds hgood.1
  have hb := (c.normal.parameters.continuousAt hgood.1).preimage_mem_nhds
    (isOpen_ball.mem_nhds hgood.2.1)
  have h0 : c.chart.projection (q c.center-q c.center) = 0 := by rw [sub_self,map_zero]
  filter_upwards [hs,hb] with y hy hyb
  have hgr := c.normal.graph_identity (c.normal.parameters y) (ball_subset_ball c.graphRadius_le hyb)
  simp only [c.normal.parameters.left_inv hy,h0,sub_zero] at hgr
  have hpos : c.oldPosition (c.normal.parameters y) = c.chart.projection (q y-q c.center) := by
    apply c.normal.realCoordinates.injective
    rw [oldPosition,ContinuousLinearEquiv.apply_symm_apply]
    exact hgr.symm
  rw [← hpos]
  simpa only [oldPosition,c.normal.parameters.left_inv hy] using (c.graph_boundary _ hyb).2.2

theorem projection_tangent_generic (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x)) = ⊤ := by
  let a := c.oldPosition (c.normal.parameters x)
  let F := fun z => c.chart.inverse (z+a)
  let G := fun y => c.chart.projection (y-q c.center)-a
  have ha : ‖complexRealEquiv m a‖ < c.chart.radius := (c.graph_boundary _ hgood.2.1).2.1
  have hF0 : F 0 = q x := by simpa only [F,zero_add] using c.oldPosition_inverse hgood
  have hF : AnalyticAt ℂ F 0 := by
    have hfa : AnalyticAt ℂ c.chart.inverse ((0 : Affine m)+a) := by
      simpa only [zero_add] using c.chart.inverse_analytic a ha
    exact hfa.comp (f := fun z : Affine m => z+a) (x := 0) (analyticAt_id.add analyticAt_const)
  have hG : AnalyticAt ℂ G (q x) :=
    ((c.chart.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)).sub analyticAt_const
  have hT : IsOpen {z : Affine m | ‖complexRealEquiv m (z+a)‖ < c.chart.radius} :=
    isOpen_lt (((complexRealEquiv m).continuous.comp (continuous_id.add continuous_const)).norm) continuous_const
  have hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id := by
    filter_upwards [hT.mem_nhds (by simpa using ha)] with z hz
    change c.chart.projection (c.chart.inverse (z+a)-q c.center)-a = z
    rw [c.chart.left_inverse (z+a) hz,add_sub_cancel_right]
  have hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q := by
    simpa only [F,G,Function.comp_def,sub_add_cancel] using c.projection_inverse_germ hgood
  have ht := chart_parametric_generic F G q hF0 hF hG hq hqi hGF hFG hr
  have hd : fderiv ℝ (G ∘ q) x = fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x := by
    have hh := (((c.chart.projection.restrictScalars ℝ).differentiableAt.comp x
      (hq.sub_const (q c.center))).hasFDerivAt.sub_const a).fderiv
    exact hh
  rwa [hd] at ht
end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericSurjectiveRealNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

 theorem oldOffset_hasFDerivAt (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    HasFDerivAt c.oldOffset (c.oldOffsetDerivative s) (c.oldPosition s) := by
  have hC := c.normal.realCoordinates.toContinuousLinearMap.hasFDerivAt (x := c.oldPosition s)
  have hP := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hQ := (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hφ := (c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)).differentiableAt.hasFDerivAt
  have hφ' : HasFDerivAt c.normal.graph (fderiv ℝ c.normal.graph s)
      (c.oldParameter (c.oldPosition s)) := by simpa only [oldParameter_oldPosition] using hφ
  exact hQ.sub (hφ'.comp (c.oldPosition s) hP)

 theorem oldOffsetDerivative_surjective (c : NashBoundaryChart (m := m) U V B q) (s) :
    Function.Surjective (c.oldOffsetDerivative s) := by
  intro v
  refine ⟨c.normal.realCoordinates.symm (0,v),?_⟩
  change (c.normal.realCoordinates (c.normal.realCoordinates.symm (0,v))).2 -
    fderiv ℝ c.normal.graph s (c.normal.realCoordinates (c.normal.realCoordinates.symm (0,v))).1 = v
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_zero,sub_zero]

end Release061.NashBoundaryChart

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ForwardBackwardGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

@[simp] theorem forward_zero (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.forward 0=q x := by
  simpa only [forward,map_zero,zero_add] using c.oldPosition_inverse hgood

@[simp] theorem backward_center (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.backward (q x)=0 := by
  simp only [backward,← c.oldPosition_projection hgood,sub_self,map_zero]

theorem forward_mem_variety (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    s.forward z ∈ V := c.chart.inverse_mem _ (hcut z hz).2.1

theorem forward_backward_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y) :
    ∀ᶠ y in 𝓝[V] (q x), s.forward (s.backward y)=y := by
  have he := c.chart.right_inverse_at (a := c.oldPosition (c.normal.parameters x)) (c.graph_boundary _ hgood.2.1).2.1 F G
    (by simpa only [c.oldPosition_inverse hgood] using hF0) hF
    (by simpa only [c.oldPosition_inverse hgood] using hG) hGF
    (by simpa only [c.oldPosition_inverse hgood] using hFG)
  rw [c.oldPosition_inverse hgood] at he
  filter_upwards [he] with y hy
  simpa only [forward,backward,s.coordinates.symm_apply_apply,sub_add_cancel] using hy
end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentComplexConormalRows
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex

theorem complex_conormal_normal_form
    {E : Type*} [AddCommGroup E] [Module ℂ E] {k : ℕ}
    (L : (E × (Fin k → ℂ)) →ₗ[ℂ] ℂ)
    (hL : ∀ z : E, ∀ x : Fin k → ℝ, (L (z,fun i => x i)).re = 0) :
    ∃ β : Fin k → ℝ, ∀ z w, L (z,w) = Complex.I * ∑ i, (β i : ℂ) * w i := by
  classical
  have hzfun : (fun i : Fin k => ((0 : Fin k → ℝ) i : ℂ)) = 0 := by ext i; simp
  have hz : ∀ z : E, L (z,0) = 0 := by
    intro z
    apply Complex.ext
    · simpa only [hzfun,zero_re] using hL z 0
    · have h := hL (Complex.I • z) 0
      have he : (Complex.I • z, (0 : Fin k → ℂ)) = Complex.I • (z,0) := by simp
      rw [hzfun,he,L.map_smul] at h
      simpa using h
  let β : Fin k → ℝ := fun i => (L (0,Pi.single i 1)).im
  have he : ∀ i, L (0,Pi.single i 1) = Complex.I * (β i : ℂ) := by
    intro i
    apply Complex.ext
    · have h := hL 0 (Pi.single i 1)
      have hi : (fun j : Fin k => ((Pi.single i 1 : Fin k → ℝ) j : ℂ)) = Pi.single i 1 := by
        ext j
        simp only [Pi.single_apply]
        split_ifs <;> simp
      rw [hi] at h
      simpa using h
    · simp [β]
  refine ⟨β,?_⟩
  intro z w
  have hw : (0,w) = ∑ i : Fin k, w i • ((0 : E),Pi.single i 1) := by
    apply Prod.ext
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum]
      ext j
      simp [Finset.sum_apply,Pi.single_apply]
  calc
    L (z,w) = L (z,0)+L (0,w) := by rw [←map_add]; simp
    _ = L (0,w) := by rw [hz,zero_add]
    _ = ∑ i, w i * (Complex.I*(β i : ℂ)) := by rw [hw,map_sum]; simp only [map_smul,smul_eq_mul,he]
    _ = Complex.I * ∑ i, (β i : ℂ)*w i := by rw [Finset.mul_sum]; congr 1; funext i; ring

theorem normalRealCovector_apply {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (β : Fin k → ℝ) (x : E × (Fin k → ℂ)) :
    normalRealCovector β x = -∑ i, β i * (x.2 i).im := by
  simp [normalRealCovector]

theorem independent_complex_conormal_rows
    {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
    {ι : Type*} {k : ℕ} (L : ι → (E × (Fin k → ℂ)) →ₗ[ℂ] ℂ)
    (hL : ∀ j (z : E) (x : Fin k → ℝ), (L j (z,fun i => x i)).re = 0)
    (hI : LinearIndependent ℝ (fun j => Complex.reLm.comp ((L j).restrictScalars ℝ))) :
    ∃ β : ι → Fin k → ℝ, LinearIndependent ℝ β ∧
      ∀ j z w, L j (z,w) = Complex.I * ∑ i, (β j i : ℂ)*w i := by
  classical
  choose β hβ using fun j => complex_conormal_normal_form (L j) (hL j)
  refine ⟨β,?_,hβ⟩
  apply LinearIndependent.of_comp (normalRealCovector (E := E))
  have he : (fun j => normalRealCovector (E := E) (β j)) =
      (fun j => Complex.reLm.comp ((L j).restrictScalars ℝ)) := by
    funext j
    apply LinearMap.ext
    intro x
    rw [normalRealCovector_apply]
    change _ = (L j x).re
    rcases x with ⟨z,w⟩
    rw [hβ]
    simp [Complex.mul_re,Complex.im_sum]
  change LinearIndependent ℝ (fun j => normalRealCovector (E := E) (β j))
  rw [he]
  exact hI

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealDirectionsTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical

theorem support_along_chart_fderiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {d : ℕ}
    (h : H → ℂ) (f : E → H) (g : H → E) (q : (Fin d → ℝ) → H)
    {x : Fin d → ℝ} (hg0 : g (q x)=0) (hg : DifferentiableAt ℝ g (q x))
    (hq : DifferentiableAt ℝ q x)
    (hfgq : (f ∘ g ∘ q) =ᶠ[𝓝 x] q)
    (hlog : AnalyticAt ℂ (fun z => Complex.log (h (f z))) 0) :
    fderiv ℝ (fun y => Real.log ‖h (q y)‖) x =
      (fderiv ℝ (fun z => Real.log ‖h (f z)‖) 0).comp (fderiv ℝ (g ∘ q) x) := by
  have hr : DifferentiableAt ℝ (fun z => Real.log ‖h (f z)‖) 0 := by
    have hh := Complex.reCLM.differentiableAt.comp 0 (hlog.differentiableAt.restrictScalars ℝ)
    simpa only [Function.comp_def,Complex.reCLM_apply,Complex.log_re] using hh
  have hD : DifferentiableAt ℝ (fun z => Real.log ‖h (f z)‖) ((g ∘ q) x) := by
    simpa only [Function.comp_apply,hg0] using hr
  have hh := hD.hasFDerivAt.comp x (hg.comp x hq).hasFDerivAt
  have he : (fun y => Real.log ‖h (q y)‖) =ᶠ[𝓝 x]
      ((fun z => Real.log ‖h (f z)‖) ∘ (g ∘ q)) := by
    filter_upwards [hfgq] with y hy
    exact congrArg (fun z => Real.log ‖h z‖) hy.symm
  have hh' := hh.congr_of_eventuallyEq he
  simpa only [Function.comp_apply,hg0] using hh'.fderiv
end

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem oldOffsetDerivative_kernel_range (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap =
      LinearMap.range (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x).toLinearMap := by
  let f := fun y => c.chart.projection (q y-q c.center)
  let M := fderiv ℝ f x
  let D := c.oldOffsetDerivative (c.normal.parameters x)
  have hf : DifferentiableAt ℝ f x := (c.chart.projection.restrictScalars ℝ).differentiableAt.comp x (hq.sub_const (q c.center))
  have hD : HasFDerivAt c.oldOffset D (f x) := by
    dsimp only [f]
    rw [←c.oldPosition_projection hgood]
    exact c.oldOffset_hasFDerivAt hgood.2.1
  have hz : D.comp M=0 :=
    ((hD.comp x hf.hasFDerivAt).congr_of_eventuallyEq (c.oldOffset_projection_germ hgood).symm).unique (hasFDerivAt_const (0 : Fin c.normal.normalDim → ℝ) x)
  have hle : LinearMap.range M.toLinearMap ≤ LinearMap.ker D.toLinearMap := by
    rintro _ ⟨v,rfl⟩
    exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin c.normal.normalDim → ℝ) => L v) hz
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hMi := (c.projection_tangent_generic hgood hq hqi hr).1
  have hMd : Module.finrank ℝ (LinearMap.range M.toLinearMap)=d := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using LinearMap.finrank_range_of_inj hMi
  have hDD := D.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (c.oldOffsetDerivative_surjective _),finrank_top] at hDD
  have hdim : Module.finrank ℝ (Affine m)=2*m := by simp [Affine,Module.finrank_pi_fintype,Nat.mul_comm]
  simp only [Module.finrank_pi,Fintype.card_fin,hdim] at hDD
  rw [hMd]
  have hc := c.normal.complex_dimension
  have hd := c.normal.real_dimension
  omega
end NashBoundaryChart

namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem real_directions_tangent (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)))
    (z : Affine s.tangentDim) (w : Fin s.normalDim → ℝ) :
    ∃ v, fderiv ℝ (s.backward ∘ q) x v = (z,fun i => (w i : ℂ)) := by
  let y : Affine s.tangentDim × Affine s.normalDim := (z,fun i => (w i : ℂ))
  have hy : s.coordinates.symm y ∈ LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap := by
    change c.oldOffsetDerivative (c.normal.parameters x) (s.coordinates.symm y) = 0
    rw [s.differential]
    have he : Flatten.imaginaryPart s.normalDim y.2 = 0 := by ext i; simp [y,Flatten.imaginaryPart]
    rw [he,map_zero]
  rw [c.oldOffsetDerivative_kernel_range hgood hq hqi hr] at hy
  obtain ⟨v,hv⟩ := hy
  refine ⟨v,?_⟩
  let f := fun y => c.chart.projection (q y-q c.center)
  have hf : DifferentiableAt ℝ f x := (c.chart.projection.restrictScalars ℝ).differentiableAt.comp x (hq.sub_const (q c.center))
  have hd : fderiv ℝ (s.backward ∘ q) x =
      (s.coordinates.toContinuousLinearMap.restrictScalars ℝ).comp (fderiv ℝ f x) := by
    exact ((s.coordinates.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
      (hf.hasFDerivAt.sub_const (c.oldPosition (c.normal.parameters x)))).fderiv
  rw [hd,ContinuousLinearMap.comp_apply]
  change s.coordinates (fderiv ℝ f x v)=y
  rw [show fderiv ℝ f x v=s.coordinates.symm y from hv,s.coordinates.apply_symm_apply]
end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportDifferentialsChangeChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem analytic_chart_transition
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {V : Set H} {p : H} (f : E → H) (g : H → E) (Φ : F → H) (Ψ : H → F)
    (hf0 : f 0=p) (hΦ0 : Φ 0=p)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g p)
    (hΦ : AnalyticAt ℂ Φ 0) (hΨ : AnalyticAt ℂ Ψ p)
    (hgf : (g ∘ f) =ᶠ[𝓝 (0 : E)] id) (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 (0 : F)] id)
    (hfg : ∀ᶠ y in 𝓝[V] p, f (g y)=y) (hΦΨ : ∀ᶠ y in 𝓝[V] p, Φ (Ψ y)=y)
    (hfV : ∀ᶠ z in 𝓝 (0 : E), f z ∈ V) (hΦV : ∀ᶠ z in 𝓝 (0 : F), Φ z ∈ V) :
    ∃ A : E ≃L[ℂ] F, A.toContinuousLinearMap = fderiv ℂ (Ψ ∘ f) 0 ∧
      (Φ ∘ (Ψ ∘ f)) =ᶠ[𝓝 (0 : E)] f := by
  have hg0 : g p=0 := by simpa only [Function.comp_apply,hf0,id_eq] using hgf.eq_of_nhds
  have hΨ0 : Ψ p=0 := by simpa only [Function.comp_apply,hΦ0,id_eq] using hΨΦ.eq_of_nhds
  let T := Ψ ∘ f
  let S := g ∘ Φ
  have hT0 : T 0=0 := by simp only [T,Function.comp_apply,hf0,hΨ0]
  have hS0 : S 0=0 := by simp only [S,Function.comp_apply,hΦ0,hg0]
  have hT : AnalyticAt ℂ T 0 := (hf0.symm ▸ hΨ).comp hf
  have hS : AnalyticAt ℂ S 0 := (hΦ0.symm ▸ hg).comp hΦ
  have ht : Tendsto f (𝓝 (0 : E)) (𝓝[V] p) := tendsto_nhdsWithin_iff.mpr ⟨hf0 ▸ hf.continuousAt,hfV⟩
  have hs : Tendsto Φ (𝓝 (0 : F)) (𝓝[V] p) := tendsto_nhdsWithin_iff.mpr ⟨hΦ0 ▸ hΦ.continuousAt,hΦV⟩
  have hΦT : (Φ ∘ T) =ᶠ[𝓝 (0 : E)] f := ht hΦΨ
  have hST : (S ∘ T) =ᶠ[𝓝 (0 : E)] id := by
    filter_upwards [hΦT,hgf] with z hz hzz
    change g (Φ (T z))=z
    rw [show Φ (T z)=f z from hz]
    exact hzz
  have hTS : (T ∘ S) =ᶠ[𝓝 (0 : F)] id := by
    filter_upwards [hs hfg,hΨΦ] with z hz hzz
    change Ψ (f (g (Φ z)))=z
    rw [hz]
    exact hzz
  let A := fderiv ℂ T 0
  let B := fderiv ℂ S 0
  have hBA : B.comp A = ContinuousLinearMap.id ℂ E := by
    have hSa : AnalyticAt ℂ S (T 0) := hT0.symm ▸ hS
    have hd := ((hSa.differentiableAt.hasFDerivAt.comp 0 hT.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hST.symm).unique (hasFDerivAt_id 0)
    simpa only [hT0] using hd
  have hAB : A.comp B = ContinuousLinearMap.id ℂ F := by
    have hTa : AnalyticAt ℂ T (S 0) := hS0.symm ▸ hT
    have hd := ((hTa.differentiableAt.hasFDerivAt.comp 0 hS.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hTS.symm).unique (hasFDerivAt_id 0)
    simpa only [hS0] using hd
  refine ⟨ContinuousLinearEquiv.equivOfInverse A B ?_ ?_,rfl,hΦT⟩
  · intro z
    change (B.comp A) z=z
    rw [hBA,ContinuousLinearMap.id_apply]
  · intro z
    change (A.comp B) z=z
    rw [hAB,ContinuousLinearMap.id_apply]

theorem support_differentials_change_chart
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {ι : Type*} (h : ι → H → ℂ) (f : E → H) (Φ : F → H) (T : E → F)
    (hT0 : T 0=0) (hT : AnalyticAt ℂ T 0)
    (hchart : (Φ ∘ T) =ᶠ[𝓝 (0 : E)] f)
    (hlog : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (Φ z))) 0)
    (hI : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (Φ z)‖) 0).toLinearMap))
    (A : E ≃L[ℂ] F) (hA : A.toContinuousLinearMap = fderiv ℂ T 0) :
    (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (f z))) 0) ∧
    LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (f z)‖) 0).toLinearMap) := by
  have he (i : ι) : (fun z => Complex.log (h i (Φ (T z)))) =ᶠ[𝓝 (0 : E)]
      (fun z => Complex.log (h i (f z))) := hchart.mono (fun z hz => congrArg (fun y => Complex.log (h i y)) hz)
  have ha (i : ι) : AnalyticAt ℂ (fun z => Complex.log (h i (Φ (T z)))) 0 :=
    (hT0.symm ▸ hlog i).comp hT
  have ha' (i : ι) := (ha i).congr (he i)
  refine ⟨ha',?_⟩
  have hd (i : ι) : fderiv ℝ (fun z => Real.log ‖h i (f z)‖) 0 =
      (fderiv ℝ (fun z => Real.log ‖h i (Φ z)‖) 0).comp (A.toContinuousLinearMap.restrictScalars ℝ) := by
    rw [log_norm_fderiv _ (ha' i),log_norm_fderiv _ (hlog i)]
    have hℂ : fderiv ℂ (fun z => Complex.log (h i (f z))) 0 =
        (fderiv ℂ (fun z => Complex.log (h i (Φ z))) 0).comp A.toContinuousLinearMap := by
      have hlogT : AnalyticAt ℂ (fun z => Complex.log (h i (Φ z))) (T 0) := hT0.symm ▸ hlog i
      have hh := (hlogT.differentiableAt.hasFDerivAt.comp 0 hT.differentiableAt.hasFDerivAt).congr_of_eventuallyEq (he i).symm
      simpa only [hT0,←hA] using hh.fderiv
    rw [hℂ]
    rfl
  let R : E ≃ₗ[ℝ] F := A.toLinearEquiv.restrictScalars ℝ
  have hi : Function.Injective R.toLinearMap.dualMap :=
    LinearMap.dualMap_injective_of_surjective R.surjective
  have hmap := hI.map' R.toLinearMap.dualMap (LinearMap.ker_eq_bot.mpr hi)
  simp_rw [hd]
  exact hmap
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentSupportRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

lemma forward_backward_boundary_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    (s.forward ∘ s.backward ∘ q) =ᶠ[𝓝 x] q := by
  simpa only [Function.comp_def,forward,backward,s.coordinates.symm_apply_apply,sub_add_cancel] using
    c.projection_inverse_germ hgood

lemma boundary_variety_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (hcut : s.HasCutoffs) (hq : ContinuousAt q x) :
    ∀ᶠ y in 𝓝 x, q y ∈ V := by
  have hback : ContinuousAt (s.backward ∘ q) x :=
    (s.backward_analytic (q x) (mem_univ _)).continuousAt.comp hq
  have hs : ∀ᶠ y in 𝓝 x, s.backward (q y) ∈ s.offsets.source := by
    apply hback.preimage_mem_nhds
    change s.offsets.source ∈ 𝓝 (s.backward (q x))
    rw [s.backward_center hgood]
    exact s.offsets.open_source.mem_nhds s.source_zero
  filter_upwards [hs,s.forward_backward_boundary_germ hgood] with y hy hyy
  rw [←show s.forward (s.backward (q y))=q y from hyy]
  exact s.forward_mem_variety hcut hy

theorem independent_support_rows_oai (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)))
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0=q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V)
    {k : ℕ} (h : Fin k → Affine N → ℂ)
    (hlog : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0)
    (hI : LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap))
    (hzero : ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ q) x)=0) :
    (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (s.forward z))) 0) ∧
    ∃ β : Fin k → Fin s.normalDim → ℝ, LinearIndependent ℝ β ∧
      ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
        Complex.I * ∑ j, (β i j : ℂ)*z.2 j := by
  have hG0 : G (q x)=0 := by simpa only [Function.comp_apply,hF0,id_eq] using hGF.eq_of_nhds
  have hsf := s.forward_analytic hcut 0 s.source_zero
  have hsg := s.backward_analytic (q x) (mem_univ _)
  have hbgf : (s.backward ∘ s.forward) =ᶠ[𝓝 (0 : Affine s.tangentDim × Affine s.normalDim)] id := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.backward_forward hcut hz
  have hsfV : ∀ᶠ z in 𝓝 (0 : Affine s.tangentDim × Affine s.normalDim), s.forward z ∈ V := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.forward_mem_variety hcut hz
  obtain ⟨A,hA,hchart⟩ := analytic_chart_transition s.forward s.backward F G
    (s.forward_zero hgood) hF0 hsf hsg hF hG hbgf hGF
    (s.forward_backward_germ hgood F G hF0 hF hG hGF hFG) hFG hsfV hFV
  have hT0 : (G ∘ s.forward) 0=0 := by simp only [Function.comp_apply,s.forward_zero hgood,hG0]
  have hT : AnalyticAt ℂ (G ∘ s.forward) 0 := ((s.forward_zero hgood).symm ▸ hG).comp hsf
  obtain ⟨hnew,hnewI⟩ := support_differentials_change_chart h s.forward F (G ∘ s.forward)
    hT0 hT hchart hlog hI A hA
  have hqV := s.boundary_variety_germ hgood hcut hq.continuousAt
  have htq : Tendsto q (𝓝 x) (𝓝[V] (q x)) := tendsto_nhdsWithin_iff.mpr ⟨hq.continuousAt,hqV⟩
  have hzeroNew (i : Fin k) : (fderiv ℝ (fun z => Real.log ‖h i (s.forward z)‖) 0).comp
      (fderiv ℝ (s.backward ∘ q) x)=0 := by
    have hdold := support_along_chart_fderiv (h i) F G q hG0 (hG.differentiableAt.restrictScalars ℝ)
      hq (htq hFG) (hlog i)
    have hdnew := support_along_chart_fderiv (h i) s.forward s.backward q
      (s.backward_center hgood) (hsg.differentiableAt.restrictScalars ℝ) hq
      (s.forward_backward_boundary_germ hgood) (hnew i)
    exact hdnew.symm.trans (hdold.trans (hzero i))
  let L : Fin k → (Affine s.tangentDim × Affine s.normalDim) →ₗ[ℂ] ℂ :=
    fun i => (fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0).toLinearMap
  have he : (fun i => (fderiv ℝ (fun z => Real.log ‖h i (s.forward z)‖) 0).toLinearMap) =
      (fun i => Complex.reLm.comp ((L i).restrictScalars ℝ)) := by
    funext i
    rw [log_norm_fderiv _ (hnew i)]
    rfl
  have hLI : LinearIndependent ℝ (fun i => Complex.reLm.comp ((L i).restrictScalars ℝ)) := he ▸ hnewI
  have hLzero : ∀ i (z : Affine s.tangentDim) (w : Fin s.normalDim → ℝ), (L i (z,fun j => (w j : ℂ))).re=0 := by
    intro i z w
    obtain ⟨v,hv⟩ := s.real_directions_tangent hgood hq hqi hr z w
    have hh := congrArg (fun M : (Fin d → ℝ) →L[ℝ] ℝ => M v) (hzeroNew i)
    rw [ContinuousLinearMap.comp_apply,hv,log_norm_fderiv _ (hnew i)] at hh
    exact hh
  obtain ⟨β,hβ,hβeq⟩ := independent_complex_conormal_rows L hLzero hLI
  exact ⟨hnew,β,hβ,fun i z => hβeq i z.1 z.2⟩
end NashBoundaryScalingChart
end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.NashBoundaryScalingChart.independent_support_rows_oai := @OAI.Release061.NashBoundaryScalingChart.independent_support_rows_oai
