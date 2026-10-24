-- Prove2me | solution 1 for K24.Global.coverHolderToBundleContinuity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:22:16.148583+00:00
-- url     : https://prove2.me/submissions/2e31fdbd-3888-4487-9820-4ad5c2598784

import Definitions.Def_K24GlobalAnalysis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise

namespace K24.Global.NativeContinuity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable {k : ℕ∞ω}

lemma trivialization_eq_chart_differential (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) (v : TangentSpace I4 p) :
    (trivializationAt FourSpace (TangentSpace I4) c ⟨p, v⟩).2 =
      mfderiv I4 I4 (chartAt FourSpace c) p v := by
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hp v,
    TangentBundle.continuousLinearMapAt_trivializationAt hp]
  rfl

lemma vector_trivialization_eq_coordinates (Y : RawVector M) (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) :
    (trivializationAt FourSpace (TangentSpace I4) c ⟨p, Y p⟩).2 =
      vectorInChart Y c (chartAt FourSpace c p) := by
  rw [trivialization_eq_chart_differential c p hp]
  change mfderiv I4 I4 (chartAt FourSpace c) p (Y p) =
    mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (Y ((chartAt FourSpace c).symm (chartAt FourSpace c p)))
  rw [(chartAt FourSpace c).left_inv hp]

lemma vector_section_continuous (Y : RawVector M) (hY : VectorContDiff k Y) :
    Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [FiberBundle.continuousAt_section FourSpace]
  have hcoord : ContinuousAt (vectorInChart Y p) (chartAt FourSpace p p) :=
    (hY p).continuousOn.continuousAt
      ((chartAt FourSpace p).open_target.mem_nhds (mem_chart_target FourSpace p))
  have hchart : ContinuousAt (chartAt FourSpace p) p :=
    (chartAt FourSpace p).continuousOn.continuousAt (chart_source_mem_nhds FourSpace p)
  apply (hcoord.comp hchart).congr_of_eventuallyEq
  filter_upwards [chart_source_mem_nhds FourSpace p] with q hq
  exact vector_trivialization_eq_coordinates Y p q hq

lemma covector_evaluation_in_trivialization (eta : RawCovector M) (c : M)
    (q : TangentBundle I4 M) (hq : q.proj ∈ (chartAt FourSpace c).source) :
    eta q.proj q.2 = ∑ i : Fin 4,
      covectorInChart eta c (chartAt FourSpace c q.proj) i *
        (trivializationAt FourSpace (TangentSpace I4) c q).2 i := by
  have hr := congrArg (fun L => L q.2) (covector_chart_recovery eta c q.proj hq)
  rw [← hr]
  change coefficientsToCovector (covectorInChart eta c (chartAt FourSpace c q.proj))
    (mfderiv I4 I4 (chartAt FourSpace c) q.proj q.2) = _
  rw [← trivialization_eq_chart_differential c q.proj hq q.2]
  simp [coefficientsToCovector, coordProj]

lemma covector_evaluation_continuous (eta : RawCovector M)
    (heta : CovectorContDiff k eta) :
    Continuous (fun q : TangentBundle I4 M => eta q.proj q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := q.proj
  have hproj : ContinuousAt (fun z : TangentBundle I4 M => z.proj) q :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt
  have hchart : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousOn.continuousAt (chart_source_mem_nhds FourSpace c)
  have hcoord : ContinuousAt (covectorInChart eta c) (chartAt FourSpace c c) :=
    (heta c).continuousOn.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds (mem_chart_target FourSpace c))
  have hc := hcoord.comp_of_eq (hchart.comp_of_eq hproj rfl) rfl
  have htriv : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.proj ∈ (chartAt FourSpace c).source
        exact mem_chart_source FourSpace c))
  have hlocal : ContinuousAt (fun z : TangentBundle I4 M => ∑ i : Fin 4,
      covectorInChart eta c (chartAt FourSpace c z.proj) i *
        (trivializationAt FourSpace (TangentSpace I4) c z).2 i) q := by
    apply tendsto_finsetSum
    intro i hi
    exact ((continuous_apply i).continuousAt.comp hc).mul
      ((coordProj i).continuous.continuousAt.comp htriv.snd)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.preimage_mem_nhds (chart_source_mem_nhds FourSpace c)] with z hz
  exact covector_evaluation_in_trivialization eta c z hz

abbrev TangentPair (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  {q : TangentBundle I4 M × TangentBundle I4 M // q.1.proj = q.2.proj}

lemma cov2_evaluation_in_trivialization (U : RawCov2 M) (c : M)
    (q : TangentPair M) (hq : q.val.1.proj ∈ (chartAt FourSpace c).source) :
    U q.val.1.proj q.val.1.2 q.val.2.2 = ∑ i : Fin 4, ∑ j : Fin 4,
      (trivializationAt FourSpace (TangentSpace I4) c q.val.1).2 i *
        (cov2InChart U c (chartAt FourSpace c q.val.1.proj) i j *
          (trivializationAt FourSpace (TangentSpace I4) c q.val.2).2 j) := by
  rcases q with ⟨⟨⟨p, v⟩, ⟨r, w⟩⟩, hpr⟩
  change p = r at hpr
  subst r
  have hr := congrArg (fun L => L v w) (cov2_chart_recovery U c p hq)
  rw [← hr]
  change matrixToBilinear (cov2InChart U c (chartAt FourSpace c p))
    (mfderiv I4 I4 (chartAt FourSpace c) p v)
    (mfderiv I4 I4 (chartAt FourSpace c) p w) = _
  rw [← trivialization_eq_chart_differential c p hq v,
    ← trivialization_eq_chart_differential c p hq w]
  simp [matrixToBilinear, coordProj]

lemma cov2_evaluation_continuous (U : RawCov2 M) (hU : Cov2ContDiff k U) :
    Continuous (fun q : TangentPair M => U q.val.1.proj q.val.1.2 q.val.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := q.val.1.proj
  have hp1 : Continuous (fun z : TangentPair M => z.val.1) := continuous_subtype_val.fst
  have hp2 : Continuous (fun z : TangentPair M => z.val.2) := continuous_subtype_val.snd
  have hproj : ContinuousAt (fun z : TangentPair M => z.val.1.proj) q :=
    ((FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp hp1).continuousAt
  have hchart : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousOn.continuousAt (chart_source_mem_nhds FourSpace c)
  have hcoord : ContinuousAt (cov2InChart U c) (chartAt FourSpace c c) :=
    (hU c).continuousOn.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds (mem_chart_target FourSpace c))
  have hc := hcoord.comp_of_eq (hchart.comp_of_eq hproj rfl) rfl
  have ht1 : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q.val.1 :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.val.1.proj ∈ (chartAt FourSpace c).source
        exact mem_chart_source FourSpace c))
  have ht2 : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q.val.2 :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.val.2.proj ∈ (chartAt FourSpace c).source
        rw [← q.property]
        exact mem_chart_source FourSpace c))
  have hlocal : ContinuousAt (fun z : TangentPair M => ∑ i : Fin 4, ∑ j : Fin 4,
      (trivializationAt FourSpace (TangentSpace I4) c z.val.1).2 i *
        (cov2InChart U c (chartAt FourSpace c z.val.1.proj) i j *
          (trivializationAt FourSpace (TangentSpace I4) c z.val.2).2 j)) q := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact ((coordProj i).continuous.continuousAt.comp (ht1.comp_of_eq hp1.continuousAt rfl).snd).mul
      (((continuous_apply_apply i j).continuousAt.comp hc).mul
        ((coordProj j).continuous.continuousAt.comp (ht2.comp_of_eq hp2.continuousAt rfl).snd))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.preimage_mem_nhds (chart_source_mem_nhds FourSpace c)] with z hz
  exact cov2_evaluation_in_trivialization U c z hz

end K24.Global.NativeContinuity


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter IsManifold
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal

namespace K24.Global.CoverContinuity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

lemma projection_isOpenMap (F : LocalFiniteCover M) : IsOpenMap F.projection := by
  exact F.baseOpen.isOpenMap_subtype_val.comp F.covering.isOpenMap

lemma lift_smoothAt (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  have hc : c.coordinate ∈ maximalAtlas I4 ∞ F.TotalSpace :=
    subset_maximalAtlas c.coordinate_mem_atlas
  exact F.projectionSmooth.contMDiffAt.comp x
    (contMDiffAt_symm_of_mem_maximalAtlas hc (c.outerSubsetTarget hx))

lemma lift_map_nhds (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : map c.lift (𝓝 x) = 𝓝 (c.lift x) := by
  change map (F.projection ∘ c.coordinate.symm) (𝓝 x) = _
  rw [← map_map, c.coordinate.symm.map_nhds_eq (c.outerSubsetTarget hx)]
  exact (projection_isOpenMap F).map_nhds_eq F.projectionSmooth.continuous.continuousAt

lemma coord_smoothAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace d) ∘ c.lift) x := by
  exact ((contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I4) (n := ∞) d) hd).comp x
    (lift_smoothAt c x hx)).contDiffAt

lemma coord_map_nhds (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    map ((chartAt FourSpace d) ∘ c.lift) (𝓝 x) =
      𝓝 (chartAt FourSpace d (c.lift x)) := by
  rw [← map_map, lift_map_nhds c x hx, (chartAt FourSpace d).map_nhds_eq hd]

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

lemma liftedCovector_apply (c : LocalCoverChart F) (eta : RawCovector M)
    (x a : FourSpace) :
    coefficientsToCovector (c.liftedCovector eta x) a = eta (c.lift x) (c.tangentMap x a) := by
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L a)
    (coefficientsToCovector_recover ((eta (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap))

lemma liftedCov2_apply (c : LocalCoverChart F) (U : RawCov2 M)
    (x a b : FourSpace) :
    matrixToBilinear (c.liftedCov2 U x) a b =
      U (c.lift x) (c.tangentMap x a) (c.tangentMap x b) := by
  exact congrArg (fun L : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) => L a b)
    (matrixToBilinear_recover (bilinearPullback (U (c.lift x)) (c.tangentMap x).toContinuousLinearMap))

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

lemma cov2_coord_lift (c : LocalCoverChart F) (U : RawCov2 M) (d : M)
    (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    cov2InChart U d (chartAt FourSpace d (c.lift x)) i j =
      matrixToBilinear (c.liftedCov2 U x)
        ((fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x).inverse (basisVector i))
        ((fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x).inverse (basisVector j)) := by
  rw [← frame_eq_fderiv c d x hx hd, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.coe_coe, liftedCov2_apply]
  have hr := congrArg (fun L =>
      L (c.tangentMap x ((frame c d x hd).symm (basisVector i)))
        (c.tangentMap x ((frame c d x hd).symm (basisVector j))))
    (cov2_chart_recovery U d (c.lift x) hd)
  change matrixToBilinear (cov2InChart U d (chartAt FourSpace d (c.lift x)))
    (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)
      (c.tangentMap x ((frame c d x hd).symm (basisVector i))))
    (mfderiv I4 I4 (chartAt FourSpace d) (c.lift x)
      (c.tangentMap x ((frame c d x hd).symm (basisVector j)))) = _ at hr
  rw [← frame_apply c d x hd, ← frame_apply c d x hd, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply] at hr
  simpa [matrixToBilinear, coordProj, basisVector] using hr

lemma inverse_frame_continuousAt (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContinuousAt (fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse) x := by
  have hi := (contDiffAt_map_inverse (𝕜 := ℝ) (n := (0 : ℕ∞ω)) (frame c d x hd)).continuousAt
  rw [frame_eq_fderiv c d x hx hd] at hi
  exact hi.comp ((coord_smoothAt c d x hx hd).continuousAt_fderiv (by simp))

lemma covector_eval_continuous :
    Continuous (fun q : (Fin 4 → ℝ) × FourSpace => coefficientsToCovector q.1 q.2) := by
  simp only [coefficientsToCovector, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, coordProj]
  fun_prop

lemma cov2_eval_continuous :
    Continuous (fun q : Mat4 × (FourSpace × FourSpace) => matrixToBilinear q.1 q.2.1 q.2.2) := by
  simp only [matrixToBilinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, coordProj]
  fun_prop

lemma continuousAt_of_coord_lift {E : Type*} [TopologicalSpace E]
    (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (f : FourSpace → E) (hf : ContinuousAt (f ∘ (chartAt FourSpace d) ∘ c.lift) x) :
    ContinuousAt f (chartAt FourSpace d (c.lift x)) := by
  change map f (𝓝 (chartAt FourSpace d (c.lift x))) ≤ _
  rw [← coord_map_nhds c d x hx hd, map_map]
  exact hf

lemma vector_coord_lift_continuousAt (c : LocalCoverChart F) (Y : RawVector M) (d : M)
    (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hY : ContinuousOn (c.liftedVector Y) c.innerDomain) :
    ContinuousAt (vectorInChart Y d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hY.continuousAt (c.innerOpen.mem_nhds hx)
  have hderiv := (coord_smoothAt c d x hxo hd).continuousAt_fderiv (by simp)
  have hlocal := hderiv.clm_apply hcoeff
  apply continuousAt_of_coord_lift c d x hxo hd
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact vector_coord_lift c Y d y hy hyd

lemma covector_coord_lift_continuousAt (c : LocalCoverChart F) (eta : RawCovector M) (d : M)
    (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (heta : ContinuousOn (c.liftedCovector eta) c.innerDomain) :
    ContinuousAt (covectorInChart eta d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := heta.continuousAt (c.innerOpen.mem_nhds hx)
  have hinv := inverse_frame_continuousAt c d x hxo hd
  apply continuousAt_of_coord_lift c d x hxo hd
  apply continuousAt_pi.mpr
  intro i
  have hlocal := covector_eval_continuous.continuousAt.comp
    (hcoeff.prodMk (hinv.clm_apply (continuousAt_const (y := basisVector i))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact covector_coord_lift c eta d y hy hyd i

lemma cov2_coord_lift_continuousAt (c : LocalCoverChart F) (U : RawCov2 M) (d : M)
    (x : FourSpace) (hx : x ∈ c.innerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source)
    (hU : ContinuousOn (c.liftedCov2 U) c.innerDomain) :
    ContinuousAt (cov2InChart U d) (chartAt FourSpace d (c.lift x)) := by
  have hxo := c.closureInnerSubset (subset_closure hx)
  have hcoeff := hU.continuousAt (c.innerOpen.mem_nhds hx)
  have hinv := inverse_frame_continuousAt c d x hxo hd
  apply continuousAt_of_coord_lift c d x hxo hd
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hlocal := cov2_eval_continuous.continuousAt.comp
    (hcoeff.prodMk ((hinv.clm_apply (continuousAt_const (y := basisVector i))).prodMk
      (hinv.clm_apply (continuousAt_const (y := basisVector j)))))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.outerOpen.mem_nhds hxo,
    (lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact cov2_coord_lift c U d y hy hyd i j

theorem vectorContDiff_zero_of_lifted_continuous (C : BoundedLocalCover M) (Y : RawVector M)
    (hY : ∀ ν : C.Index, ContinuousOn ((C.chart ν).liftedVector Y) (C.chart ν).innerDomain) :
    VectorContDiff 0 Y := by
  intro d
  rw [contDiffOn_zero]
  intro z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := vector_coord_lift_continuousAt (C.chart ν) Y d x hx hd (hY ν)
  rw [hchart] at h
  exact h.continuousWithinAt

theorem covectorContDiff_zero_of_lifted_continuous (C : BoundedLocalCover M) (eta : RawCovector M)
    (heta : ∀ ν : C.Index, ContinuousOn ((C.chart ν).liftedCovector eta) (C.chart ν).innerDomain) :
    CovectorContDiff 0 eta := by
  intro d
  rw [contDiffOn_zero]
  intro z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := covector_coord_lift_continuousAt (C.chart ν) eta d x hx hd (heta ν)
  rw [hchart] at h
  exact h.continuousWithinAt

theorem cov2ContDiff_zero_of_lifted_continuous (C : BoundedLocalCover M) (U : RawCov2 M)
    (hU : ∀ ν : C.Index, ContinuousOn ((C.chart ν).liftedCov2 U) (C.chart ν).innerDomain) :
    Cov2ContDiff 0 U := by
  intro d
  rw [contDiffOn_zero]
  intro z hz
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  have hd : (C.chart ν).lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  have hchart : chartAt FourSpace d ((C.chart ν).lift x) = z := by
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  have h := cov2_coord_lift_continuousAt (C.chart ν) U d x hx hd (hU ν)
  rw [hchart] at h
  exact h.continuousWithinAt

theorem vectorHolder_native_contDiff_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (Y : RawVector M) (hY : C.VectorHolder k α Y) : VectorContDiff 0 Y :=
  vectorContDiff_zero_of_lifted_continuous C Y (fun ν => (hY.1 ν).continuousOn)

theorem covectorHolder_native_contDiff_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (eta : RawCovector M) (heta : C.CovectorHolder k α eta) : CovectorContDiff 0 eta :=
  covectorContDiff_zero_of_lifted_continuous C eta (fun ν => (heta.1 ν).continuousOn)

theorem cov2Holder_native_contDiff_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U : RawCov2 M) (hU : C.Cov2Holder k α U) : Cov2ContDiff 0 U :=
  cov2ContDiff_zero_of_lifted_continuous C U (fun ν => (hU.1 ν).continuousOn)

end K24.Global.CoverContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff NNReal
universe u

theorem solution {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    (∀ U : RawCov2 M, C.Cov2Holder k α U →
      Cov2ContDiff 0 U ∧
      Continuous (fun q : {q : TangentBundle I4 M × TangentBundle I4 M //
        q.1.proj = q.2.proj} => U q.val.1.proj q.val.1.2 q.val.2.2)) ∧
    (∀ eta : RawCovector M, C.CovectorHolder k α eta →
      CovectorContDiff 0 eta ∧
      Continuous (fun q : TangentBundle I4 M => eta q.proj q.2)) ∧
    (∀ Y : RawVector M, C.VectorHolder k α Y →
      VectorContDiff 0 Y ∧
      Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    have h0 := CoverContinuity.cov2Holder_native_contDiff_zero C k α U hU
    exact ⟨h0, NativeContinuity.cov2_evaluation_continuous U h0⟩
  · intro eta heta
    have h0 := CoverContinuity.covectorHolder_native_contDiff_zero C k α eta heta
    exact ⟨h0, NativeContinuity.covector_evaluation_continuous eta h0⟩
  · intro Y hY
    have h0 := CoverContinuity.vectorHolder_native_contDiff_zero C k α Y hY
    exact ⟨h0, NativeContinuity.vector_section_continuous Y h0⟩

theorem K24CONTCoverExactType {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    (∀ U : RawCov2 M, C.Cov2Holder k α U →
      Cov2ContDiff 0 U ∧
      Continuous (fun q : {q : TangentBundle I4 M × TangentBundle I4 M //
        q.1.proj = q.2.proj} => U q.val.1.proj q.val.1.2 q.val.2.2)) ∧
    (∀ eta : RawCovector M, C.CovectorHolder k α eta →
      CovectorContDiff 0 eta ∧
      Continuous (fun q : TangentBundle I4 M => eta q.proj q.2)) ∧
    (∀ Y : RawVector M, C.VectorHolder k α Y →
      VectorContDiff 0 Y ∧
      Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M))) :=
  solution C k α

set_option pp.universes true in
#check @solution
#print axioms solution
#print axioms K24CONTCoverExactType
