-- Prove2me | solution 1 for K24.Global.coverHolderVectorCovectorNativeRegularity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:08:53.350118+00:00
-- url     : https://prove2.me/submissions/dc8039dc-285b-403a-a545-fd370601f743

import Definitions.Def_K24GlobalAnalysis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter IsManifold
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal

namespace K24.Global.NativeRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

omit [IsManifold I4 ∞ M] in
lemma lift_smoothAt (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  have hc : c.coordinate ∈ maximalAtlas I4 ∞ F.TotalSpace :=
    subset_maximalAtlas c.coordinate_mem_atlas
  exact F.projectionSmooth.contMDiffAt.comp x
    (contMDiffAt_symm_of_mem_maximalAtlas hc (c.outerSubsetTarget hx))

lemma coord_smoothAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace d) ∘ c.lift) x := by
  exact ((contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I4) (n := ∞) d) hd).comp x
    (lift_smoothAt c x hx)).contDiffAt

def frame (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) : FourSpace ≃L[ℝ] FourSpace :=
  (c.tangentMap x).trans
    ((trivializationAt FourSpace (TangentSpace I4) d).continuousLinearEquivAt ℝ (c.lift x) hd)

lemma frame_eq_fderiv (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    (frame c d x hd).toContinuousLinearMap =
      fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x := by
  change (((trivializationAt FourSpace (TangentSpace I4) d).continuousLinearEquivAt ℝ
    (c.lift x) hd).toContinuousLinearMap).comp (c.tangentMap x).toContinuousLinearMap = _
  rw [Trivialization.coe_continuousLinearEquivAt_eq',
    TangentBundle.continuousLinearMapAt_trivializationAt hd]
  change (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)).comp
    (c.tangentMap x).toContinuousLinearMap = _
  rw [c.tangentMap_eq x hx]
  erw [← mfderiv_comp x
    ((contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I4) (n := ∞) d) hd).mdifferentiableAt (by simp))
    ((lift_smoothAt c x hx).mdifferentiableAt (by simp))]
  exact mfderiv_eq_fderiv

lemma frame_apply (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (v : FourSpace) :
    frame c d x hd v = mfderiv I4 I4 (chartAt FourSpace d) (c.lift x) (c.tangentMap x v) := by
  change ((trivializationAt FourSpace (TangentSpace I4) d).continuousLinearEquivAt ℝ
    (c.lift x) hd) (c.tangentMap x v) = _
  rw [← ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq',
    TangentBundle.continuousLinearMapAt_trivializationAt hd]
  rfl

omit [IsManifold I4 ∞ M] in
lemma liftedCovector_apply (c : LocalCoverChart F) (eta : RawCovector M)
    (x a : FourSpace) :
    coefficientsToCovector (c.liftedCovector eta x) a = eta (c.lift x) (c.tangentMap x a) := by
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L a)
    (coefficientsToCovector_recover ((eta (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap))

lemma vector_coord_lift (c : LocalCoverChart F) (Y : RawVector M) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    vectorInChart Y d (chartAt FourSpace d (c.lift x)) =
      fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (c.liftedVector Y x) := by
  rw [← frame_eq_fderiv c d x hx hd]
  rw [ContinuousLinearEquiv.coe_coe, frame_apply]
  dsimp only [vectorInChart, LocalCoverChart.liftedVector]
  erw [(chartAt FourSpace d).left_inv hd, ContinuousLinearEquiv.apply_symm_apply]

lemma covector_coord_lift (c : LocalCoverChart F) (eta : RawCovector M) (d : M)
    (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    covectorInChart eta d (chartAt FourSpace d (c.lift x)) i =
      coefficientsToCovector (c.liftedCovector eta x)
        ((fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x).inverse (basisVector i)) := by
  rw [← frame_eq_fderiv c d x hx hd, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.coe_coe, liftedCovector_apply]
  have hr := congrArg (fun L => L (c.tangentMap x ((frame c d x hd).symm (basisVector i))))
    (covector_chart_recovery eta d (c.lift x) hd)
  change coefficientsToCovector (covectorInChart eta d (chartAt FourSpace d (c.lift x)))
    (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)
      (c.tangentMap x ((frame c d x hd).symm (basisVector i)))) = _ at hr
  rw [← frame_apply c d x hd, ContinuousLinearEquiv.apply_symm_apply] at hr
  simpa [coefficientsToCovector, coordProj, basisVector] using hr

lemma inverse_frame_contDiffAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (k : ℕ) :
    ContDiffAt ℝ k (fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse) x := by
  have hi := contDiffAt_map_inverse (𝕜 := ℝ) (n := (k : ℕ∞ω)) (frame c d x hd)
  rw [frame_eq_fderiv c d x hx hd] at hi
  exact hi.comp x ((coord_smoothAt c d x hx hd).fderiv_right (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))

lemma covector_eval_contDiff (k : ℕ) :
    ContDiff ℝ k (fun q : (Fin 4 → ℝ) × FourSpace => coefficientsToCovector q.1 q.2) := by
  simp only [coefficientsToCovector, sum_apply,
    smul_apply, smul_eq_mul, coordProj]
  fun_prop

lemma contDiffAt_of_coord_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (k : ℕ) (f : FourSpace → E)
    (hf : ContDiffAt ℝ k (f ∘ (chartAt FourSpace d) ∘ c.lift) x) :
    ContDiffAt ℝ k f (chartAt FourSpace d (c.lift x)) := by
  let g := (chartAt FourSpace d) ∘ c.lift
  have hg : ContDiffAt ℝ ∞ g x := coord_smoothAt c d x hx hd
  have hgd : HasFDerivAt g (frame c d x hd).toContinuousLinearMap x := by
    rw [frame_eq_fderiv c d x hx hd]
    exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let gi := hg.localInverse hgd hn
  have hgi : ContDiffAt ℝ k gi (g x) := (hg.to_localInverse hgd hn).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hleft : gi (g x) = x := hg.localInverse_apply_image hgd hn
  have hright : ∀ᶠ y in 𝓝 (g x), g (gi y) = y :=
    (hg.hasStrictFDerivAt' hgd hn).eventually_right_inverse
  have hcomp : ContDiffAt ℝ k ((f ∘ g) ∘ gi) (g x) := by
    apply ContDiffAt.comp (g x) _ hgi
    simpa only [hleft] using hf
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hright] with y hy
  simp only [Function.comp_apply, hy]

lemma vector_coord_lift_contDiffAt (c : LocalCoverChart F) (Y : RawVector M) (d : M)
    (k : ℕ) (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hY : ContDiffOn ℝ k (c.liftedVector Y) c.innerDomain) :
    ContDiffAt ℝ k (vectorInChart Y d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hY.contDiffAt (c.innerOpen.mem_nhds hx)
  have hderiv := (coord_smoothAt c d x hxo hd).fderiv_right (m := (k : ℕ∞ω)) (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤))
  have hlocal := hderiv.clm_apply hcoeff
  apply contDiffAt_of_coord_lift c d x hxo hd k
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact vector_coord_lift c Y d y hy hyd

lemma covector_coord_lift_contDiffAt (c : LocalCoverChart F) (eta : RawCovector M) (d : M)
    (k : ℕ) (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (heta : ContDiffOn ℝ k (c.liftedCovector eta) c.innerDomain) :
    ContDiffAt ℝ k (covectorInChart eta d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := heta.contDiffAt (c.innerOpen.mem_nhds hx)
  have hinv := inverse_frame_contDiffAt c d x hxo hd k
  apply contDiffAt_of_coord_lift c d x hxo hd k
  apply contDiffAt_pi.mpr
  intro i
  have hlocal := (covector_eval_contDiff k).contDiffAt.comp x
    (hcoeff.prodMk (hinv.clm_apply (contDiffAt_const (c := basisVector i))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact covector_coord_lift c eta d y hy hyd i


theorem vectorContDiff_of_lifted_contDiff (C : BoundedLocalCover M) (k : ℕ) (Y : RawVector M)
    (hY : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector Y) (C.chart ν).innerDomain) :
    VectorContDiff k Y := by
  intro d z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := vector_coord_lift_contDiffAt (C.chart ν) Y d k x hx hd (hY ν)
  rw [hchart] at h
  exact h.contDiffWithinAt

theorem covectorContDiff_of_lifted_contDiff (C : BoundedLocalCover M) (k : ℕ) (eta : RawCovector M)
    (heta : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector eta) (C.chart ν).innerDomain) :
    CovectorContDiff k eta := by
  intro d z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := covector_coord_lift_contDiffAt (C.chart ν) eta d k x hx hd (heta ν)
  rw [hchart] at h
  exact h.contDiffWithinAt

end K24.Global.NativeRegularity

open K24.Global
universe u

theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0),
      (∀ eta : RawCovector M, C.CovectorHolder k α eta → CovectorContDiff k eta) ∧
      (∀ Y : RawVector M, C.VectorHolder k α Y → VectorContDiff k Y) := by
  intro M _ _ _ C k α
  constructor
  · intro eta heta
    exact NativeRegularity.covectorContDiff_of_lifted_contDiff C k eta heta.1
  · intro Y hY
    exact NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1

theorem K24NATIVE_exact_type_wrapper :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0),
      (∀ eta : RawCovector M, C.CovectorHolder k α eta → CovectorContDiff k eta) ∧
      (∀ Y : RawVector M, C.VectorHolder k α Y → VectorContDiff k Y) := solution

#print axioms solution
#print axioms K24NATIVE_exact_type_wrapper
