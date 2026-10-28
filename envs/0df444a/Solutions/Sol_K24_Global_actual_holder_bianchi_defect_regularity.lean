-- Prove2me | solution 1 for K24.Global.actual_holder_bianchi_defect_regularity
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:34:46.450991+00:00
-- url     : https://prove2.me/submissions/a26ea461-084c-48af-a260-b02d56fb0527

import Definitions.Def_K24GlobalStatement
import Theorems.Thm_K24_Global_pointwiseHaarProjectionSectors
import Theorems.Thm_K24_Global_holderHaarProjectionAllOrders
import Theorems.Thm_K24_Global_fixed_cover_holder_lowering
import Theorems.Thm_K24_Global_cover_cov2_regularity
import Theorems.Thm_K24_Global_coverHolderVectorCovectorNativeRegularity
import Theorems.Thm_K24_Global_tensorHolderBanachAllOrders
import Theorems.Thm_K24_Global_vectorCovectorHolderBanachAllOrders
import Theorems.Thm_K24_Global_nativeBianchiDeltaStarChartRecovery

/- Compact proof: accepted dependencies plus explicit new proof bodies. -/

/- BEGIN Holder20261026.Operators.NativeFoundation -/

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



/- END Holder20261026.Operators.NativeFoundation -/

/- BEGIN Holder20261026.Operators.OuterRegularity -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter IsManifold
open scoped Manifold ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}

                                                                            
                                                            


theorem liftedCovector_eq_native (c : LocalCoverChart F) (eta : RawCovector M)
    (d : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    c.liftedCovector eta x i =
      coefficientsToCovector (covectorInChart eta d (chartAt FourSpace d (c.lift x)))
        (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (basisVector i)) := by
  rw [← NativeRegularity.frame_eq_fderiv c d x hx hd,
    ContinuousLinearEquiv.coe_coe, NativeRegularity.frame_apply]
  exact (congrArg (fun L => L (c.tangentMap x (basisVector i)))
    (covector_chart_recovery eta d (c.lift x) hd)).symm

                                                              


theorem liftedCov2_eq_native (c : LocalCoverChart F) (u : RawCov2 M)
    (d : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hd : c.lift x ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    c.liftedCov2 u x i j =
      matrixToBilinear (cov2InChart u d (chartAt FourSpace d (c.lift x)))
        (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (basisVector i))
        (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (basisVector j)) := by
  rw [← NativeRegularity.frame_eq_fderiv c d x hx hd,
    ContinuousLinearEquiv.coe_coe, NativeRegularity.frame_apply,
    NativeRegularity.frame_apply]
  exact (congrArg (fun L => L (c.tangentMap x (basisVector i))
    (c.tangentMap x (basisVector j)))
    (cov2_chart_recovery u d (c.lift x) hd)).symm



end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.OuterRegularity -/

/- BEGIN Holder20261026.Operators.NativeLocalCoordinates -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter IsManifold
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

                                                                             
                                                                             
                
theorem exists_inner_coordinate_inverse (C : BoundedLocalCover M) (d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target) :
    ∃ (nu : C.Index) (x : FourSpace), x ∈ (C.chart nu).innerDomain ∧
      (C.chart nu).lift x = (chartAt FourSpace d).symm z ∧
      ∃ psi : FourSpace → FourSpace, ContDiffAt ℝ ∞ psi z ∧ psi z = x ∧
        ∀ᶠ y in 𝓝 z, psi y ∈ (C.chart nu).innerDomain ∧
          (C.chart nu).lift (psi y) ∈ (chartAt FourSpace d).source ∧
          chartAt FourSpace d ((C.chart nu).lift (psi y)) = y := by
  obtain ⟨nu, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  let c := C.chart nu
  have hxo : x ∈ c.outerDomain := c.closureInnerSubset (subset_closure hx)
  have hd : c.lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]
    exact (chartAt FourSpace d).map_target hz
  let F := (chartAt FourSpace d) ∘ c.lift
  have hF : ContDiffAt ℝ ∞ F x := NativeRegularity.coord_smoothAt c d x hxo hd
  have hFd : HasFDerivAt F (NativeRegularity.frame c d x hd).toContinuousLinearMap x := by
    rw [NativeRegularity.frame_eq_fderiv c d x hxo hd]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let psi := hF.localInverse hFd hn
  have hpsi : ContDiffAt ℝ ∞ psi (F x) := hF.to_localInverse hFd hn
  have hleft : psi (F x) = x := hF.localInverse_apply_image hFd hn
  have hright : ∀ᶠ y in 𝓝 (F x), F (psi y) = y :=
    (hF.hasStrictFDerivAt' hFd hn).eventually_right_inverse
  have hFx : F x = z := by
    change chartAt FourSpace d (c.lift x) = z
    rw [hxp, (chartAt FourSpace d).right_inv hz]
  rw [hFx] at hpsi hleft hright
  refine ⟨nu, x, hx, hxp, psi, hpsi, hleft, ?_⟩
  have hnear : ∀ᶠ y in 𝓝 z, psi y ∈ c.innerDomain ∧
      c.lift (psi y) ∈ (chartAt FourSpace d).source := by
    have hN : ∀ᶠ y in 𝓝 (psi z), y ∈ c.innerDomain ∧
        c.lift y ∈ (chartAt FourSpace d).source := by
      rw [hleft]
      exact inter_mem (c.innerOpen.mem_nhds hx)
        ((NativeRegularity.lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
          ((chartAt FourSpace d).open_source.mem_nhds hd))
    exact hpsi.continuousAt.tendsto.eventually hN
  filter_upwards [hnear, hright] with y hy hr
  exact ⟨hy.1, hy.2, hr⟩

theorem inverse_frame_contDiffAt_infty {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse) x := by
  have hi := contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞) (NativeRegularity.frame c d x hd)
  rw [NativeRegularity.frame_eq_fderiv c d x hx hd] at hi
  exact hi.comp x ((NativeRegularity.coord_smoothAt c d x hx hd).fderiv_right (by simp))

end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.NativeLocalCoordinates -/

/- BEGIN Holder20261026.JetNorm -/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal ContDiff

namespace K24.Global.HolderJetNorm

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma eHolderNorm_isometry {D W Z : Type*} [PseudoEMetricSpace D]
    [PseudoEMetricSpace W] [PseudoEMetricSpace Z] (alpha : ℝ≥0)
    (f : D → W) (L : W → Z) (hL : Isometry L) :
    eHolderNorm alpha (L ∘ f) = eHolderNorm alpha f := by
  simp only [eHolderNorm, HolderWith, Function.comp_apply, hL.edist_eq]

lemma derivativeENorm_fderiv (j : ℕ) {s : Set E} (hs : IsOpen s) (f : E → V) :
    derivativeENorm j s (fderiv ℝ f) = derivativeENorm (j + 1) s f := by
  unfold derivativeENorm
  congr 1
  funext x
  simp only [iteratedFDerivWithin_of_isOpen _ hs x.property]
  congr 1
  exact NNReal.eq (norm_iteratedFDeriv_fderiv (𝕜 := ℝ))

lemma highestHolder_fderiv (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) :
    eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k (fderiv ℝ f) s x) =
      eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ (k + 1) f s x) := by
  simp only [iteratedFDerivWithin_of_isOpen _ hs (Subtype.property _)]
  let L := (continuousMultilinearCurryRightEquiv' ℝ k E V).symm
  have heq : (fun x : s => iteratedFDeriv ℝ (k + 1) f x) =
      L ∘ (fun x : s => iteratedFDeriv ℝ k (fderiv ℝ f) x) := by
    funext x
    exact iteratedFDeriv_succ_eq_comp_right
  rw [heq]
  exact (eHolderNorm_isometry alpha _ L L.isometry).symm

                                                                              
                                                                                      
theorem coordinateHolderENorm_succ (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) :
    coordinateHolderENorm (k + 1) alpha s f =
      derivativeENorm 0 s f + coordinateHolderENorm k alpha s (fderiv ℝ f) := by
  unfold coordinateHolderENorm
  simp_rw [derivativeENorm_fderiv _ hs, highestHolder_fderiv _ _ hs]
  rw [Finset.sum_range_succ']
  ac_rfl

theorem coordinateHolderENorm_fderiv_le (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) :
    coordinateHolderENorm k alpha s (fderiv ℝ f) ≤
      coordinateHolderENorm (k + 1) alpha s f := by
  rw [coordinateHolderENorm_succ k alpha hs f]
  exact le_add_self

theorem bigHolderOn_fderiv (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) (hf : BigHolderOn (k + 1) alpha s f) :
    BigHolderOn k alpha s (fderiv ℝ f) := by
  refine ⟨hf.1.fderiv_of_isOpen hs (by simp), ?_⟩
  exact (coordinateHolderENorm_fderiv_le k alpha hs f).trans_lt hf.2

end K24.Global.HolderJetNorm

/- END Holder20261026.JetNorm -/

/- BEGIN Holder20261026.Bilinear -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff NNReal ENNReal BigOperators Matrix.Norms.Elementwise

namespace K24.Global.HolderProductsProof

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivative_le_holder (k j : ℕ) (α : ℝ≥0) (s : Set E) (f : E → V)
    (hj : j ≤ k) : derivativeENorm j s f ≤ coordinateHolderENorm k α s f := by
  exact (Finset.single_le_sum (f := fun i => derivativeENorm i s f)
    (fun _ _ => zero_le) (Finset.mem_range.mpr (show j < k + 1 by omega))).trans le_self_add

theorem derivative_point_bound (k j : ℕ) (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) (B : ℝ≥0)
    (hB : coordinateHolderENorm k α s f ≤ B) (hj : j ≤ k)
    (x : E) (hx : x ∈ s) : ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have hb := (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) ⟨x, hx⟩).trans
    ((derivative_le_holder k j α s f hj).trans hB)
  rw [iteratedFDerivWithin_of_isOpen j hs hx] at hb
  exact_mod_cast hb




def chooseSum (k : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ≥0)


omit [NormedSpace ℝ V] in
theorem holderWith_of_enorm_le {X : Type*} [MetricSpace X]
    (alpha A : ℝ≥0) (f : X → V) (h : eHolderNorm alpha f ≤ A) : HolderWith A alpha f := by
  have hm : MemHolder alpha f := eHolderNorm_lt_top.mp (h.trans_lt ENNReal.coe_lt_top)
  apply hm.holderWith.mono
  exact_mod_cast (hm.coe_nnHolderNorm_eq_eHolderNorm ▸ h)

omit [NormedSpace ℝ V] in
theorem holderWith_of_norm_bound {X : Type*} [MetricSpace X]
    (alpha A : ℝ≥0) (f : X → V)
    (h : ∀ x y, ‖f x - f y‖ ≤ (A : ℝ) * dist x y ^ (alpha : ℝ)) :
    HolderWith A alpha f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ alpha.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm] using h x y


variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bilinear_derivative_bound_at (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x : E) (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ‖iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ := by
  obtain ⟨s, hs, hx, hfg⟩ := (hf.prodMk hg).contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.univ_inter] at hfg
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hfg.fst hfg.snd hs.uniqueDiffOn hx
    (n := k) le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ hs hx] using hb

theorem bilinear_derivative_difference (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x y : E)
    (hfx : ContDiffAt ℝ k f x) (hfy : ContDiffAt ℝ k f y)
    (hgx : ContDiffAt ℝ k g x) (hgy : ContDiffAt ℝ k g y) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x -
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x‖ +
      ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x - iteratedFDeriv ℝ (k-i) g y‖ := by
  let fs : E → V := fun z => f (z + (x-y))
  let gs : E → F := fun z => g (z + (x-y))
  have hfs : ContDiffAt ℝ k fs y := by
    have ht : y + (x-y) = x := by abel
    exact ht ▸ hfx |>.comp y (contDiffAt_id.add contDiffAt_const)
  have hgs : ContDiffAt ℝ k gs y := by
    have ht : y + (x-y) = x := by abel
    exact ht ▸ hgx |>.comp y (contDiffAt_id.add contDiffAt_const)
  have hDfs (i : ℕ) : iteratedFDeriv ℝ i fs y = iteratedFDeriv ℝ i f x := by
    dsimp [fs]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    abel
  have hDgs (i : ℕ) : iteratedFDeriv ℝ i gs y = iteratedFDeriv ℝ i g x := by
    dsimp [gs]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    abel
  let q : E → G := fun z => B (f z) (g z)
  let qs : E → G := fun z => q (z + (x-y))
  let a : E → G := fun z => B ((fs - f) z) (gs z)
  let b : E → G := fun z => B (f z) ((gs - g) z)
  have hq : ContDiffAt ℝ k q y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y (hfy.prodMk hgy)
  have hqs : ContDiffAt ℝ k qs y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y (hfs.prodMk hgs)
  have ha : ContDiffAt ℝ k a y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y ((hfs.sub hfy).prodMk hgs)
  have hb : ContDiffAt ℝ k b y := B.isBoundedBilinearMap.contDiff.contDiffAt.comp y (hfy.prodMk (hgs.sub hgy))
  have heq : qs - q = a + b := by
    funext z
    simp [qs, q, a, b, fs, gs, map_sub]
  have hDq : iteratedFDeriv ℝ k qs y = iteratedFDeriv ℝ k q x := by
    dsimp [qs]
    rw [iteratedFDeriv_comp_add_right]
    congr 1
    abel
  have hleft := bilinear_derivative_bound_at k B (fs-f) gs y (hfs.sub hfy) hgs
  have hright := bilinear_derivative_bound_at k B f (gs-g) y hfy (hgs.sub hgy)
  have hsubf (i : ℕ) (hi : i ≤ k) : iteratedFDeriv ℝ i (fs-f) y =
      iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y := by
    rw [iteratedFDeriv_sub_apply (hfs.of_le (by exact_mod_cast hi))
      (hfy.of_le (by exact_mod_cast hi)), hDfs]
  have hsubg (i : ℕ) (hi : i ≤ k) : iteratedFDeriv ℝ i (gs-g) y =
      iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y := by
    rw [iteratedFDeriv_sub_apply (hgs.of_le (by exact_mod_cast hi))
      (hgy.of_le (by exact_mod_cast hi)), hDgs]
  have hleft' : ‖iteratedFDeriv ℝ k a y‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x‖ := by
    convert hleft using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsubf i (by simpa using Finset.mem_range.mp hi), hDgs]
  have hright' : ‖iteratedFDeriv ℝ k b y‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x - iteratedFDeriv ℝ (k-i) g y‖ := by
    convert hright using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsubg (k-i) (Nat.sub_le _ _)]
  change ‖iteratedFDeriv ℝ k q x - iteratedFDeriv ℝ k q y‖ ≤ _
  rw [← hDq, ← iteratedFDeriv_sub_apply hqs hq, heq, iteratedFDeriv_add_apply ha hb]
  exact (norm_add_le _ _).trans (add_le_add hleft' hright')


theorem bilinear_derivative_uniform (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x : E) (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (A D : ℝ≥0) (hA : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hD : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * (chooseSum k : ℝ) * A * D := by
  apply (bilinear_derivative_bound_at k B f g x hf hg).trans
  calc
    ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k-i) g x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * A * D := by
      gcongr with i hi
      · exact hA i (by simpa using Finset.mem_range.mp hi)
      · exact hD (k-i) (Nat.sub_le _ _)
    _ = ‖B‖ * (chooseSum k : ℝ) * A * D := by
      simp [chooseSum, Finset.sum_mul, mul_assoc]

theorem bilinear_difference_uniform (k : ℕ) (B : V →L[ℝ] F →L[ℝ] G)
    (f : E → V) (g : E → F) (x y : E)
    (hfx : ContDiffAt ℝ k f x) (hfy : ContDiffAt ℝ k f y)
    (hgx : ContDiffAt ℝ k g x) (hgy : ContDiffAt ℝ k g y)
    (A D L d : ℝ≥0)
    (hA : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f y‖ ≤ A)
    (hD : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ D)
    (hf : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ A * L * d)
    (hg : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ D * L * d) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x -
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) y‖ ≤
        ‖B‖ * (2 * chooseSum k) * A * D * L * d := by
  apply (bilinear_derivative_difference k B f g x y hfx hfy hgx hgy).trans
  calc
    ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ * ‖iteratedFDeriv ℝ (k-i) g x‖ +
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
        ‖iteratedFDeriv ℝ (k-i) g x - iteratedFDeriv ℝ (k-i) g y‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * (A * L * d) * D +
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * A * (D * L * d) := by
      gcongr with i hi i hi
      · exact hf i (by simpa using Finset.mem_range.mp hi)
      · exact hD (k-i) (Nat.sub_le _ _)
      · exact hA i (by simpa using Finset.mem_range.mp hi)
      · exact hg (k-i) (Nat.sub_le _ _)
    _ = ‖B‖ * (2 * chooseSum k) * A * D * L * d := by
      simp only [← Finset.sum_mul, chooseSum, NNReal.coe_sum, NNReal.coe_natCast]
      ring


end K24.Global.HolderProductsProof

namespace K24.Global
universe v w z


end K24.Global
/- END Holder20261026.Bilinear -/

/- BEGIN Holder20261026.AllJetsProduct -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal ContDiff BigOperators

namespace K24.Global.HolderAllJets
open HolderProductsProof

variable {E V F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def factor (k : ℕ) : ℝ≥0 :=
  1 + ∑ j ∈ Finset.range (k + 1), chooseSum j + 2 * chooseSum k

                                                                          
                                                                                    
theorem bilinear_bound (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s)
    (B : V →L[ℝ] F →L[ℝ] G) (f : E → V) (g : E → F) (A D : ℝ≥0)
    (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s)
    (hA : ∀ i ≤ k, coordinateHolderENorm i alpha s f ≤ A)
    (hD : ∀ i ≤ k, coordinateHolderENorm i alpha s g ≤ D) :
    coordinateHolderENorm k alpha s (fun x => B (f x) (g x)) ≤
      ((factor k * ‖B‖₊ * A * D : ℝ≥0) : ℝ≥0∞) := by
  have hfp (i : ℕ) (hi : i ≤ k) (x : s) : ‖iteratedFDeriv ℝ i f x‖ ≤ A :=
    derivative_point_bound k i alpha hs f A (hA k le_rfl) hi x x.property
  have hgp (i : ℕ) (hi : i ≤ k) (x : s) : ‖iteratedFDeriv ℝ i g x‖ ≤ D :=
    derivative_point_bound k i alpha hs g D (hD k le_rfl) hi x x.property
  have hfc (x : s) : ContDiffAt ℝ k f x :=
    (hf x x.property).contDiffAt (hs.mem_nhds x.property)
  have hgc (x : s) : ContDiffAt ℝ k g x :=
    (hg x x.property).contDiffAt (hs.mem_nhds x.property)
  have hfh (i : ℕ) (hi : i ≤ k) :
      HolderWith A alpha (fun x : s => iteratedFDeriv ℝ i f x) := by
    have h := holderWith_of_enorm_le alpha A
      (fun x : s => iteratedFDerivWithin ℝ i f s x) (le_add_self.trans (hA i hi))
    simpa only [iteratedFDerivWithin_of_isOpen i hs (Subtype.property _)] using h
  have hgh (i : ℕ) (hi : i ≤ k) :
      HolderWith D alpha (fun x : s => iteratedFDeriv ℝ i g x) := by
    have h := holderWith_of_enorm_le alpha D
      (fun x : s => iteratedFDerivWithin ℝ i g s x) (le_add_self.trans (hD i hi))
    simpa only [iteratedFDerivWithin_of_isOpen i hs (Subtype.property _)] using h
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (fun x => B (f x) (g x)) ≤
      ((‖B‖₊ * chooseSum j * A * D : ℝ≥0) : ℝ≥0∞) := by
    apply iSup_le
    intro x
    rw [iteratedFDerivWithin_of_isOpen j hs x.property]
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    exact bilinear_derivative_uniform j B f g x ((hfc x).of_le (by exact_mod_cast hj))
      ((hgc x).of_le (by exact_mod_cast hj)) A D
      (fun i hi => hfp i (hi.trans hj) x) (fun i hi => hgp i (hi.trans hj) x)
  let H : ℝ≥0 := ‖B‖₊ * (2 * chooseSum k) * A * D
  have hh : HolderWith H alpha
      (fun x : s => iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x) := by
    apply holderWith_of_norm_bound
    intro x y
    let d : ℝ≥0 := (nndist x y) ^ (alpha : ℝ)
    have hfd (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ A * 1 * d := by
      simpa only [d, mul_one, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm]
        using (hfh i hi).dist_le x y
    have hgd (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ D * 1 * d := by
      simpa only [d, mul_one, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, dist_eq_norm]
        using (hgh i hi).dist_le x y
    have h := bilinear_difference_uniform k B f g x y (hfc x) (hfc y) (hgc x) (hgc y)
      A D 1 d (fun i hi => hfp i hi y) (fun i hi => hgp i hi x) hfd hgd
    simpa only [H, d, mul_one, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_rpow,
      coe_nndist, coe_nnnorm, NNReal.coe_ofNat] using h
  have hhbound : eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k
      (fun y => B (f y) (g y)) s x) ≤ (H : ℝ≥0∞) := by
    simpa only [iteratedFDerivWithin_of_isOpen k hs (Subtype.property _)]
      using hh.eHolderNorm_le
  unfold coordinateHolderENorm
  apply (add_le_add (Finset.sum_le_sum fun j hj => hd j
    (by simpa using Finset.mem_range.mp hj)) hhbound).trans
  rw [← ENNReal.ofNNReal_finsetSum, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  dsimp [H, factor]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  nlinarith [mul_nonneg (show 0 ≤ ‖B‖₊ * A * D from zero_le) (show 0 ≤ (1 : ℝ≥0) from zero_le)]

theorem bigHolderOn_bilinear (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s)
    (B : V →L[ℝ] F →L[ℝ] G) (f : E → V) (g : E → F)
    (hf : ∀ i ≤ k, BigHolderOn i alpha s f)
    (hg : ∀ i ≤ k, BigHolderOn i alpha s g) :
    BigHolderOn k alpha s (fun x => B (f x) (g x)) := by
  classical
  let A : ℝ≥0 := ∑ i ∈ Finset.range (k + 1), (coordinateHolderENorm i alpha s f).toNNReal
  let D : ℝ≥0 := ∑ i ∈ Finset.range (k + 1), (coordinateHolderENorm i alpha s g).toNNReal
  have hA (i : ℕ) (hi : i ≤ k) : coordinateHolderENorm i alpha s f ≤ (A : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal (hf i hi).2.ne]
    exact_mod_cast (Finset.single_le_sum (f := fun j => (coordinateHolderENorm j alpha s f).toNNReal)
      (fun _ _ => zero_le) (Finset.mem_range.mpr (show i < k + 1 by omega)))
  have hD (i : ℕ) (hi : i ≤ k) : coordinateHolderENorm i alpha s g ≤ (D : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal (hg i hi).2.ne]
    exact_mod_cast (Finset.single_le_sum (f := fun j => (coordinateHolderENorm j alpha s g).toNNReal)
      (fun _ _ => zero_le) (Finset.mem_range.mpr (show i < k + 1 by omega)))
  refine ⟨B.isBoundedBilinearMap.contDiff.comp_contDiffOn
    ((hf k le_rfl).1.prodMk (hg k le_rfl).1), ?_⟩
  exact (bilinear_bound k alpha hs B f g A D (hf k le_rfl).1
    (hg k le_rfl).1 hA hD).trans_lt ENNReal.coe_lt_top

end K24.Global.HolderAllJets

/- END Holder20261026.AllJetsProduct -/

/- BEGIN Holder20261026.Foundations -/

                                                                            
                                                                        
                                                                           
                                                                   
                                                                                         
                                                                         
                                                               


                                                                          
                                                         
                                                                            
                                                                   
                                                                   
                                                                        
                                                                                          
                                                                                         
                                                                                
                                                                                    
                                                                       
                                                                        
                                                                        
                                                 



   
                                                       
                                                                                  
                                                                                            
                                                                            
                                                                             
                                                                           
  

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace K24.Global.HaarSectors

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

lemma circleHaar_leftInvariant : circleHaar.IsMulLeftInvariant := by
  unfold circleHaar
  infer_instance

attribute [local instance] circleHaar_leftInvariant

lemma coefficientsToCovector_apply (a : Fin 4 → ℝ) (v : FourSpace) :
    coefficientsToCovector a v = ∑ i : Fin 4, a i * v i := by
  simp [coefficientsToCovector, coordProj]

lemma matrixToBilinear_apply (a : Mat4) (v w : FourSpace) :
    matrixToBilinear a v w = ∑ i : Fin 4, ∑ j : Fin 4, v i * (a i j * w j) := by
  simp [matrixToBilinear, coordProj]





variable [IsManifold I4 ∞ M]

























end K24.Global.HaarSectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace K24.Global.HaarSectors

attribute [local instance] circleHaar_leftInvariant

                                                                            
                                                                               
private noncomputable def modelNormedTangent {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] (p : N) : NormedAddCommGroup (TangentSpace I4 p) :=
  inferInstanceAs (NormedAddCommGroup FourSpace)

attribute [local instance] modelNormedTangent

private noncomputable def modelNormedSpaceTangent {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] (p : N) : NormedSpace ℝ (TangentSpace I4 p) :=
  inferInstanceAs (NormedSpace ℝ FourSpace)

attribute [local instance] modelNormedSpaceTangent

private def modelCompleteTangent {N : Type*} [TopologicalSpace N]
    [ChartedSpace FourSpace N] (p : N) : CompleteSpace (TangentSpace I4 p) :=
  inferInstanceAs (CompleteSpace FourSpace)

attribute [local instance] modelCompleteTangent

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]













end K24.Global.HaarSectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators

namespace K24.Global.HaarSectors

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

                                                             
def CovectorEvaluationContinuous (u : RawCovector M) : Prop :=
  Continuous (fun q : TangentBundle I4 M => u q.proj q.2)

                                                                    






lemma covector_haar_integrable_of_continuous (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) : CovectorHaarIntegrable rho u := by
  exact ((pointwiseHaarProjectionSectors rho).2.1 u hu).1









end K24.Global.HaarSectors


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














end K24.Global.CoverContinuity



                                                                             
                                                                           
                                      
                                                                      
                                                                             
                                                                               

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]



end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

                                                                         


end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem coordinateHolderENorm_add_le (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f g : E → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k alpha s (f + g) ≤
      coordinateHolderENorm k alpha s f + coordinateHolderENorm k alpha s g := by
  have hjet (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (f + g) s x =
        iteratedFDerivWithin ℝ j f s x + iteratedFDerivWithin ℝ j g s x :=
    iteratedFDerivWithin_add_apply
      ((hf.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property)
      ((hg.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property) hs.uniqueDiffOn x.property
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (f + g) ≤
      derivativeENorm j s f + derivativeENorm j s g := by
    apply iSup_le
    intro x
    change ‖iteratedFDerivWithin ℝ j (f + g) s x‖ₑ ≤ _
    rw [hjet j hj x]
    exact (enorm_add_le (iteratedFDerivWithin ℝ j f s x) (iteratedFDerivWithin ℝ j g s x)).trans (add_le_add
      (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)) x)
      (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j g s x‖₊ : ℝ≥0∞)) x))
  have heq : (fun x : s => iteratedFDerivWithin ℝ k (f + g) s x) =
      (fun x : s => iteratedFDerivWithin ℝ k f s x) +
      (fun x : s => iteratedFDerivWithin ℝ k g s x) := funext (hjet k le_rfl)
  unfold coordinateHolderENorm
  rw [heq]
  calc
    _ ≤ (∑ j ∈ Finset.range (k+1), (derivativeENorm j s f + derivativeENorm j s g)) +
        (eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k f s x) +
        eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k g s x)) := by
      exact add_le_add (Finset.sum_le_sum fun j hj => hd j (by simpa using hj)) eHolderNorm_add_le
    _ = _ := by rw [Finset.sum_add_distrib]; ac_rfl

theorem coordinateHolderENorm_smul (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (c : ℝ) (f : E → V) (hf : ContDiffOn ℝ k f s) :
    coordinateHolderENorm k alpha s (c • f) =
      ENNReal.ofReal |c| * coordinateHolderENorm k alpha s f := by
  have hjet (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (c • f) s x = c • iteratedFDerivWithin ℝ j f s x :=
    iteratedFDerivWithin_const_smul_apply
      ((hf.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property) hs.uniqueDiffOn x.property
  have hcn : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal |c| := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s (c • f) =
      ENNReal.ofReal |c| * derivativeENorm j s f := by
    unfold derivativeENorm
    simp only [hjet j hj, nnnorm_smul, ENNReal.coe_mul, hcn, ENNReal.mul_iSup]
  have heq : (fun x : s => iteratedFDerivWithin ℝ k (c • f) s x) =
      c • (fun x : s => iteratedFDerivWithin ℝ k f s x) := funext (hjet k le_rfl)
  unfold coordinateHolderENorm
  rw [heq]
  have hh := eHolderNorm_smul (r := alpha) (f := fun x : s => iteratedFDerivWithin ℝ k f s x) c
  rw [hh, hcn, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hd j (by simpa using hj)

theorem coordinateHolderENorm_neg (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f : E → V) (hf : ContDiffOn ℝ k f s) :
    coordinateHolderENorm k alpha s (-f) = coordinateHolderENorm k alpha s f := by
  simpa using coordinateHolderENorm_smul k alpha hs (-1) f hf

theorem coordinateHolderENorm_sub_le (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    (hs : IsOpen s) (f g : E → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k alpha s (f - g) ≤
      coordinateHolderENorm k alpha s f + coordinateHolderENorm k alpha s g := by
  simpa only [sub_eq_add_neg, coordinateHolderENorm_neg k alpha hs g hg] using
    coordinateHolderENorm_add_le k alpha hs f (-g) hf hg.neg

theorem coordinateHolderENorm_zero (k : ℕ) (alpha : ℝ≥0) (s : Set E) :
    coordinateHolderENorm k alpha s (0 : E → V) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm]
  exact eHolderNorm_const s alpha (0 : E [×k]→L[ℝ] V)



end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]




end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8

noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def Cov2Regular (C : BoundedLocalCover M) (k : ℕ) (u : RawCov2 M) : Prop :=
  ∀ nu : C.Index, ContDiffOn ℝ k ((C.chart nu).liftedCov2 u) (C.chart nu).innerDomain

theorem Cov2Regular.add {C : BoundedLocalCover M} {k : ℕ} {u v : RawCov2 M}
    (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) : Cov2Regular C k (u+v) :=
  fun nu => (hu nu).add (hv nu)

theorem Cov2Regular.smul {C : BoundedLocalCover M} {k : ℕ} {u : RawCov2 M}
    (hu : Cov2Regular C k u) (c : ℝ) : Cov2Regular C k (c • u) :=
  fun nu => (hu nu).const_smul c

theorem Cov2Regular.sub {C : BoundedLocalCover M} {k : ℕ} {u v : RawCov2 M}
    (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) : Cov2Regular C k (u-v) :=
  fun nu => (hu nu).sub (hv nu)











end K24.Global




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global
namespace CoverHolder
variable {X I E V : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def norm (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E)
    (k : ℕ) (alpha : ℝ≥0) (u : X) : ℝ≥0∞ :=
  ⨆ nu, coordinateHolderENorm k alpha (s nu) (L nu u)

def regular (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (k : ℕ) (u : X) : Prop :=
  ∀ nu, ContDiffOn ℝ k (L nu u) (s nu)




theorem norm_add_le (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (k : ℕ) (alpha : ℝ≥0) (u v : X) (hu : regular L s k u) (hv : regular L s k v) :
    norm L s k alpha (u+v) ≤ norm L s k alpha u + norm L s k alpha v := by
  apply iSup_le
  intro nu
  rw [map_add]
  exact (coordinateHolderENorm_add_le k alpha (hs nu) _ _ (hu nu) (hv nu)).trans
    (add_le_add
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu u)) nu)
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu v)) nu))

theorem norm_sub_le (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (k : ℕ) (alpha : ℝ≥0) (u v : X) (hu : regular L s k u) (hv : regular L s k v) :
    norm L s k alpha (u-v) ≤ norm L s k alpha u + norm L s k alpha v := by
  apply iSup_le
  intro nu
  rw [map_sub]
  exact (coordinateHolderENorm_sub_le k alpha (hs nu) _ _ (hu nu) (hv nu)).trans
    (add_le_add
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu u)) nu)
      (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu v)) nu))

theorem norm_smul (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (k : ℕ) (alpha : ℝ≥0) (c : ℝ) (u : X) (hu : regular L s k u) :
    norm L s k alpha (c • u) = ENNReal.ofReal |c| * norm L s k alpha u := by
  unfold norm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro nu
  rw [map_smul]
  exact coordinateHolderENorm_smul k alpha (hs nu) c _ (hu nu)

theorem norm_zero (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (k : ℕ) (alpha : ℝ≥0) :
    norm L s k alpha 0 = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro nu
  rw [map_zero, coordinateHolderENorm_zero]
  exact le_rfl



end CoverHolder
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]









end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                           
                                                         



end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
namespace HolderPerp
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]









end HolderPerp
end K24.Global



                                                                         
                                                                        
                                                                         

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal Topology

namespace K24.Global.SectionBanachSpace

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}

                                                                  
def submodule (h : SectionBanachSpace S nx) : Submodule ℝ X where
  carrier := S
  zero_mem' := h.zero_mem
  add_mem' := fun hu hv => h.add_mem _ hu _ hv
  smul_mem' := fun c _ hu => h.smul_mem c _ hu

                                                                        
@[instance_reducible]
def sectionNorm (h : SectionBanachSpace S nx) : Norm h.submodule :=
  ⟨fun u => (nx u).toReal⟩

theorem normCore (h : SectionBanachSpace S nx) :
    letI := h.sectionNorm
    NormedSpace.Core ℝ h.submodule := by
  letI := h.sectionNorm
  refine
    { norm_nonneg := fun _ => ENNReal.toReal_nonneg
      norm_smul := ?_
      norm_triangle := ?_
      norm_eq_zero_iff := ?_ }
  · intro c u
    change (nx (c • (u : X))).toReal = ‖c‖ * (nx u).toReal
    rw [h.homogeneous c u u.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  · intro u v
    change (nx ((u : X) + v)).toReal ≤ (nx u).toReal + (nx v).toReal
    calc
      _ ≤ (nx u + nx v).toReal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(h.finite u u.property).ne,
          (h.finite v v.property).ne⟩) (h.triangle u u.property v v.property)
      _ = _ := ENNReal.toReal_add (h.finite u u.property).ne (h.finite v v.property).ne
  · intro u
    change (nx u).toReal = 0 ↔ u = 0
    constructor
    · intro hu
      apply Subtype.ext
      exact h.definite u u.property
        ((ENNReal.toReal_eq_zero_iff _).mp hu |>.resolve_right (h.finite u u.property).ne)
    · intro hu
      subst u
      simp [h.zero_norm]

                                                                             
abbrev normedAddCommGroup (h : SectionBanachSpace S nx) :
    NormedAddCommGroup h.submodule :=
  letI := h.sectionNorm
  NormedAddCommGroup.ofCore h.normCore

                                                                      


theorem ofReal_norm (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ENNReal.ofReal ‖u‖ = nx u :=
  ENNReal.ofReal_toReal (h.finite u u.property).ne

                                                                           
                                                                          

end K24.Global.SectionBanachSpace




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology
namespace K24.Global
namespace HolderPerpAll

                                                                        
                                                                                  
def averageFunctional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : Circle → E →L[ℝ] ℝ) (hc : ∀ u, Continuous (fun t => L t u)) : E →L[ℝ] ℝ := by
  have hi (u : E) : Integrable (fun t => L t u) circleHaar :=
    (hc u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hUB := banach_steinhaus (g := L) (by
    intro u
    obtain ⟨B,hB⟩ := (isCompact_range (hc u).norm).bddAbove
    exact ⟨B,fun t => hB (Set.mem_range_self t)⟩)
  let C : ℝ := Classical.choose hUB
  have hC : ∀ t, ‖L t‖ ≤ C := Classical.choose_spec hUB
  let A : E →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∫ t, L t u ∂circleHaar
      map_add' := by
        intro u v
        simp only [map_add]
        exact integral_add (hi u) (hi v)
      map_smul' := by
        intro c u
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c (fun t => L t u) }
  apply A.mkContinuous C
  intro u
  have hbound : ∀ᵐ t ∂circleHaar, ‖L t u‖ ≤ C * ‖u‖ :=
    Filter.Eventually.of_forall fun t => (L t).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hC t) (norm_nonneg u))
  change ‖∫ t, L t u ∂circleHaar‖ ≤ C * ‖u‖
  simpa using norm_integral_le_of_norm_le_const hbound

@[simp] theorem averageFunctional_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : Circle → E →L[ℝ] ℝ) (hc : ∀ u, Continuous (fun t => L t u)) (u : E) :
    averageFunctional L hc u = ∫ t, L t u ∂circleHaar := rfl

                                                                            
                                                                            

end HolderPerpAll
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
namespace HolderPerpAll

                                                                            
                                                               



variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                                    



end HolderPerpAll
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global
namespace HolderPerpAll
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]







end HolderPerpAll
end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global
namespace HolderPerpAll
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

                                                                               
                                               




end HolderPerpAll
end K24.Global



                                                                           
                                                           
                                                                 
                                                                                 
                                                                 
                                                                           
                                                                             



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global.HolderProjectionZero

variable {D V : Type*} [MetricSpace D] [NormedAddCommGroup V] [NormedSpace ℝ V]

def zeroENorm (α : ℝ≥0) (f : D → V) : ℝ≥0∞ :=
  (⨆ x, ‖f x‖ₑ) + eHolderNorm α f






lemma coordinateHolderENorm_zero_eq (α : ℝ≥0) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set E) (f : E → V) :
    coordinateHolderENorm 0 α s f = zeroENorm α (fun x : s => f x) := by
  have hnorm (x : s) :
      (‖iteratedFDerivWithin ℝ 0 f s x‖₊ : ℝ≥0∞) = ‖f x‖ₑ := by
    change (‖iteratedFDerivWithin ℝ 0 f s x‖₊ : ℝ≥0∞) = (‖f x‖₊ : ℝ≥0∞)
    congr 1
    apply Subtype.ext
    exact norm_iteratedFDerivWithin_zero
  have hholder (C : ℝ≥0) :
      HolderWith C α (fun x : s => iteratedFDerivWithin ℝ 0 f s x) ↔
        HolderWith C α (fun x : s => f x) := by
    simp only [HolderWith, edist_dist, dist_iteratedFDerivWithin_zero]
  simp only [coordinateHolderENorm, zero_add, Finset.range_one, Finset.sum_singleton,
    derivativeENorm, hnorm, zeroENorm, eHolderNorm, hholder]


end K24.Global.HolderProjectionZero


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.HolderProjectionZero
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}











lemma liftedCovector_sub (c : LocalCoverChart F) (U V : RawCovector M) (x : FourSpace) :
    c.liftedCovector (U - V) x = c.liftedCovector U x - c.liftedCovector V x := by
  rfl










end K24.Global.HolderProjectionZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global.HolderProjectionFinite

variable {T V : Type*} [MeasurableSpace T] {μ : Measure T}
  [NormedAddCommGroup V] [NormedSpace ℝ V]







end K24.Global.HolderProjectionFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff

namespace K24.Global.HolderProjectionFinite
open HolderProjectionZero


variable {D T : Type*} [MetricSpace D] [Nonempty D] [MeasurableSpace T]
    {W : ℕ → Type*} [∀ j, NormedAddCommGroup (W j)] [∀ j, NormedSpace ℝ (W j)]
    [∀ j, CompleteSpace (W j)]

def jetENorm (k : ℕ) (α : ℝ≥0) (g : ∀ j, D → W j) : ℝ≥0∞ :=
  (∑ j ∈ Finset.range (k + 1), ⨆ x, ‖g j x‖ₑ) + eHolderNorm α (g k)


lemma jetENorm_sub_le (k : ℕ) (α : ℝ≥0) (f g : ∀ j, D → W j) :
    jetENorm k α (fun j x => f j x - g j x) ≤ jetENorm k α f + jetENorm k α g := by
  have hsup (j : ℕ) : (⨆ x, ‖f j x - g j x‖ₑ) ≤ (⨆ x, ‖f j x‖ₑ) + (⨆ x, ‖g j x‖ₑ) := by
    apply iSup_le
    intro x
    exact (show ‖f j x - g j x‖ₑ ≤ ‖f j x‖ₑ + ‖g j x‖ₑ from enorm_sub_le).trans (add_le_add (le_iSup (fun x => ‖f j x‖ₑ) x) (le_iSup (fun x => ‖g j x‖ₑ) x))
  have he : eHolderNorm α (fun x => f k x - g k x) ≤ eHolderNorm α (f k) + eHolderNorm α (g k) := by
    have hneg : eHolderNorm α (-g k) = eHolderNorm α (g k) := by
      simpa using (eHolderNorm_smul (r := α) (f := g k) (-1 : ℝ))
    change eHolderNorm α (f k - g k) ≤ _
    simpa only [sub_eq_add_neg, hneg] using
      (eHolderNorm_add_le (r := α) (f := f k) (g := -g k))
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), ((⨆ x, ‖f j x‖ₑ) + (⨆ x, ‖g j x‖ₑ))) +
        (eHolderNorm α (f k) + eHolderNorm α (g k)) :=
      add_le_add (Finset.sum_le_sum (fun j hj => hsup j)) he
    _ = _ := by rw [Finset.sum_add_distrib]; unfold jetENorm; ac_rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]


lemma coordinateHolderENorm_sub_le (k : ℕ) (α : ℝ≥0)
    {s : Set FourSpace} (hs : IsOpen s) (hne : s.Nonempty)
    (f g : FourSpace → V) (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k α s (f - g) ≤
      coordinateHolderENorm k α s f + coordinateHolderENorm k α s g := by
  letI : Nonempty s := hne.to_subtype
  have hd (j : ℕ) (hj : j ≤ k) (x : s) :
      iteratedFDerivWithin ℝ j (f - g) s x =
        iteratedFDerivWithin ℝ j f s x - iteratedFDerivWithin ℝ j g s x :=
    iteratedFDerivWithin_sub_apply
      ((hf.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property)
      ((hg.of_le (by exact_mod_cast hj)).contDiffWithinAt x.property) hs.uniqueDiffOn x.property
  have hi := jetENorm_sub_le k α
    (fun j (x : s) => iteratedFDerivWithin ℝ j f s x)
    (fun j (x : s) => iteratedFDerivWithin ℝ j g s x)
  have heq : coordinateHolderENorm k α s (f - g) =
      jetENorm k α (fun j (x : s) => iteratedFDerivWithin ℝ j f s x - iteratedFDerivWithin ℝ j g s x) := by
    unfold coordinateHolderENorm derivativeENorm jetENorm
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      apply iSup_congr
      intro x
      rw [hd j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x]
      rfl
    · congr 1
      funext x
      exact hd k le_rfl x
  exact heq ▸ hi

end K24.Global.HolderProjectionFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.HolderProjectionFinite
open HolderProjectionZero
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]





lemma covectorENorm_sub_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawCovector M) (hU : C.CovectorHolder k α U) (hV : C.CovectorHolder k α V) :
    C.covectorENorm k α (U - V) ≤ C.covectorENorm k α U + C.covectorENorm k α V := by
  apply iSup_le
  intro ν
  have hsub : (C.chart ν).liftedCovector (U - V) =
      (C.chart ν).liftedCovector U - (C.chart ν).liftedCovector V := by
    funext x
    exact liftedCovector_sub (C.chart ν) U V x
  rw [hsub]
  apply (coordinateHolderENorm_sub_le k α (C.chart ν).innerOpen (C.chart ν).innerNonempty
    _ _ (hU.1 ν) (hV.1 ν)).trans
  exact add_le_add (le_iSup (fun ν => coordinateHolderENorm k α (C.chart ν).innerDomain
    ((C.chart ν).liftedCovector U)) ν) (le_iSup (fun ν => coordinateHolderENorm k α
      (C.chart ν).innerDomain ((C.chart ν).liftedCovector V)) ν)

lemma covectorHolder_sub (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (U V : RawCovector M) (hU : C.CovectorHolder k α U) (hV : C.CovectorHolder k α V) :
    C.CovectorHolder k α (U - V) := by
  constructor
  · intro ν
    have hsub : (C.chart ν).liftedCovector (U - V) =
        (C.chart ν).liftedCovector U - (C.chart ν).liftedCovector V := by
      funext x
      exact liftedCovector_sub (C.chart ν) U V x
    rw [hsub]
    exact (hU.1 ν).sub (hV.1 ν)
  · exact (covectorENorm_sub_le C k α U V hU hV).trans_lt (ENNReal.add_lt_top.mpr ⟨hU.2,hV.2⟩)





end K24.Global.HolderProjectionFinite


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global

                                                             
section
section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
                                                                                       




end
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]







end

                                                                    
section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem pos_coordinate_restrict (k : ℕ) (alpha : ℝ≥0) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (hst : s ⊆ t) (f : E → V) :
    coordinateHolderENorm k alpha s f ≤ coordinateHolderENorm k alpha t f := by
  have heq (j : ℕ) (x : s) : iteratedFDerivWithin ℝ j f s x =
      iteratedFDerivWithin ℝ j f t x := by
    rw [iteratedFDerivWithin_of_isOpen j hs x.property,
      iteratedFDerivWithin_of_isOpen j ht (hst x.property)]
  unfold coordinateHolderENorm
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    unfold derivativeENorm
    apply iSup_le
    intro x
    rw [heq j x]
    exact le_iSup_of_le (⟨x,hst x.property⟩ : t) le_rfl
  · unfold eHolderNorm
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    apply HolderWith.eHolderNorm_le
    intro x y
    simpa only [heq k x, heq k y, Subtype.edist_eq] using
      hC (⟨x,hst x.property⟩ : t) (⟨y,hst y.property⟩ : t)

theorem pos_coordinate_bound (k : ℕ) (alpha B D : ℝ≥0) (s : Set E) (f : E → V)
    (hjet : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDerivWithin ℝ j f s x‖ ≤ B)
    (hh : HolderWith D alpha (fun x : s => iteratedFDerivWithin ℝ k f s x)) :
    coordinateHolderENorm k alpha s f ≤ (k+1 : ℕ) * (B : ℝ≥0∞) + D := by
  unfold coordinateHolderENorm
  apply add_le_add _ hh.eHolderNorm_le
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (B : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro j hj
      apply iSup_le
      intro x
      apply ENNReal.coe_le_coe.mpr
      exact hjet j (by simpa using Finset.mem_range.mp hj) x x.property
    _ = _ := by simp



end

                                                                   
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem pos_admissible_holder [IsManifold I4 ∞ M] [CompactSpace M] (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (z : RawCov2 M) (hz : MetricAdmissible C b z) (k : ℕ) (hk : k ≤ b.order) :
    C.Cov2Holder k b.exponent.value z := by
  have hsub (nu : C.Index) : (C.chart nu).innerDomain ⊆ (C.chart nu).outerDomain :=
    fun _ hx => (C.chart nu).closureInnerSubset (subset_closure hx)
  have horder : C.Cov2Holder b.order b.exponent.value z := by
    refine ⟨fun nu => ((hz.regularity nu).1).mono (hsub nu), ?_⟩
    apply lt_of_le_of_lt (b := (b.coefficientBound : ℝ≥0∞)) _ ENNReal.coe_lt_top
    apply iSup_le
    intro nu
    exact (pos_coordinate_restrict b.order b.exponent.value (C.chart nu).innerOpen
      (C.chart nu).outerOpen (hsub nu) _).trans (le_self_add.trans (hz.coefficientBound nu))
  exact (fixed_cover_holder_lowering M C b.order k hk b.exponent.value
    b.exponent.lessThanOne.le).2.2.1 z horder



end

end K24.Global
/- END Holder20261026.Foundations -/

/- BEGIN Holder20261026.Composition -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal ContDiff

namespace K24.Global.HolderComposition

variable {D E V : Type u} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coordinateHolderENorm_congr (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    {f g : E → V} (h : Set.EqOn f g s) :
    coordinateHolderENorm k alpha s f = coordinateHolderENorm k alpha s g := by
  have hj (j : ℕ) : (fun x : s => iteratedFDerivWithin ℝ j f s x) =
      (fun x : s => iteratedFDerivWithin ℝ j g s x) := by
    funext x
    exact h.iteratedFDerivWithin j x.property
  have hd (j : ℕ) : derivativeENorm j s f = derivativeENorm j s g := by
    unfold derivativeENorm
    apply iSup_congr
    intro x
    rw [h.iteratedFDerivWithin j x.property]
  unfold coordinateHolderENorm
  simp_rw [hd, hj]

lemma bigHolderOn_congr (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    {f g : E → V} (h : Set.EqOn f g s) (hf : BigHolderOn k alpha s f) :
    BigHolderOn k alpha s g := by
  refine ⟨hf.1.congr (fun x hx => (h hx).symm), ?_⟩
  rw [← coordinateHolderENorm_congr k alpha h]
  exact hf.2

lemma bigHolderOn_zero_comp (alpha : ℝ≥0) {s : Set E} {t : Set D}
    (f : E → V) (g : D → E) (hf : BigHolderOn 0 alpha s f)
    (hg : ContinuousOn g t) (hmap : Set.MapsTo g t s)
    (L : ℝ≥0) (hL : LipschitzOnWith L g t) :
    BigHolderOn 0 alpha t (f ∘ g) := by
  have hn := hf.2
  rw [HolderProjectionZero.coordinateHolderENorm_zero_eq] at hn
  have hparts := ENNReal.add_lt_top.mp hn
  have hmem : MemHolder alpha (fun x : s => f x) := eHolderNorm_lt_top.mp hparts.2
  let gs : t → s := fun x => ⟨g x, hmap x.property⟩
  have hgs : LipschitzWith L gs := by
    intro x y
    exact hL x.property y.property
  have hH : MemHolder alpha (fun x : t => f (g x)) := by
    change MemHolder alpha ((fun x : s => f x) ∘ gs)
    have hh := hmem.holderWith.comp hgs.holderWith
    simpa only [mul_one] using hh.memHolder
  refine ⟨?_, ?_⟩
  · simpa only [Nat.cast_zero] using
      (contDiffOn_zero.mpr (hf.1.continuousOn.comp hg hmap))
  · rw [HolderProjectionZero.coordinateHolderENorm_zero_eq]
    apply ENNReal.add_lt_top.mpr
    refine ⟨?_, hH.eHolderNorm_lt_top⟩
    apply lt_of_le_of_lt (b := ⨆ x : s, ‖f x‖ₑ) _ hparts.1
    exact iSup_le fun x => le_iSup_of_le (⟨g x, hmap x.property⟩ : s) le_rfl

                                                                        
                                                                                  
theorem bigHolderOn_comp_all (k : ℕ) (alpha : ℝ≥0) {s : Set E} {t : Set D}
    (hs : IsOpen s) (ht : IsOpen t) (f : E → V) (g : D → E)
    (hf : ∀ j ≤ k, BigHolderOn j alpha s f)
    (hg : ∀ j ≤ k, BigHolderOn j alpha t g)
    (hmap : Set.MapsTo g t s) (L : ℝ≥0) (hL : LipschitzOnWith L g t) :
    ∀ j ≤ k, BigHolderOn j alpha t (f ∘ g) := by
  induction k generalizing V with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact bigHolderOn_zero_comp alpha f g (hf 0 le_rfl)
      (hg 0 le_rfl).1.continuousOn hmap L hL
  | succ k ih =>
    have hsmall := ih f (fun j hj => hf j (by omega))
      (fun j hj => hg j (by omega))
    have hdf : ∀ j ≤ k, BigHolderOn j alpha s (fderiv ℝ f) := by
      intro j hj
      exact HolderJetNorm.bigHolderOn_fderiv j alpha hs f (hf (j+1) (by omega))
    have hdg : ∀ j ≤ k, BigHolderOn j alpha t (fderiv ℝ g) := by
      intro j hj
      exact HolderJetNorm.bigHolderOn_fderiv j alpha ht g (hg (j+1) (by omega))
    have hdfg : ∀ j ≤ k, BigHolderOn j alpha t (fderiv ℝ f ∘ g) :=
      ih (fderiv ℝ f) hdf (fun j hj => hg j (by omega))
    have hprod := HolderAllJets.bigHolderOn_bilinear k alpha ht
      (ContinuousLinearMap.compL ℝ D E V) (fderiv ℝ f ∘ g) (fderiv ℝ g) hdfg hdg
    have heq : Set.EqOn (fun x => (fderiv ℝ f (g x)).comp (fderiv ℝ g x))
        (fderiv ℝ (f ∘ g)) t := by
      intro x hx
      have hfx : DifferentiableAt ℝ f (g x) :=
        (((hf (k+1) le_rfl).1 (g x) (hmap hx)).contDiffAt
          (hs.mem_nhds (hmap hx))).differentiableAt (by simp)
      have hgx : DifferentiableAt ℝ g x :=
        (((hg (k+1) le_rfl).1 x hx).contDiffAt
          (ht.mem_nhds hx)).differentiableAt (by simp)
      exact (fderiv_comp x hfx hgx).symm
    have hder : BigHolderOn k alpha t (fderiv ℝ (f ∘ g)) :=
      bigHolderOn_congr k alpha heq hprod
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hj
    · refine ⟨((hf (k+1) le_rfl).1.comp (hg (k+1) le_rfl).1 hmap), ?_⟩
      rw [HolderJetNorm.coordinateHolderENorm_succ k alpha ht]
      apply ENNReal.add_lt_top.mpr
      refine ⟨?_, hder.2⟩
      exact (HolderProductsProof.derivative_le_holder 0 0 alpha t (f ∘ g) le_rfl).trans_lt
        (hsmall 0 (Nat.zero_le _)).2
    · exact hsmall j (by omega)

end K24.Global.HolderComposition

/- END Holder20261026.Composition -/

/- BEGIN Holder20261026Lower.FiniteIndex -/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Lower

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                               
                                                                                   
theorem finite_chartIndex (C : BoundedLocalCover M) (a : C.CoverIndex) :
    Finite (C.ChartIndex a) := by
  have hfin := (C.internalLocallyFinite a).finite_nonempty_inter_compact
    (C.cover a).innerCompactClosure
  apply Finite.of_finite_univ
  apply hfin.subset
  intro j _
  obtain ⟨x, hx⟩ := (C.localChart a j).innerNonempty
  refine ⟨(C.localChart a j).coordinate.symm x, ?_, ?_⟩
  · exact (C.localChart a j).coordinate.map_target
      ((C.localChart a j).outerSubsetTarget
        ((C.localChart a j).closureInnerSubset (subset_closure hx)))
  · exact subset_closure ((C.localChart a j).innerMapsToBase x hx)

                                                                             
                                                                                 
theorem baseDomain_nonempty_of_chart (C : BoundedLocalCover M)
    (a : C.CoverIndex) (j : C.ChartIndex a) : (C.cover a).baseDomain.Nonempty := by
  obtain ⟨x, hx⟩ := (C.localChart a j).innerNonempty
  exact ⟨(C.localChart a j).lift x,
    (C.cover a).innerBaseSubset ((C.localChart a j).innerMapsToBase x hx)⟩

                                                                         
                                                                         
                        
theorem finite_coverIndex [CompactSpace M] (C : BoundedLocalCover M) :
    Finite C.Index := by
  let A := {a : C.CoverIndex // (C.cover a).baseDomain.Nonempty}
  have hA : {a : C.CoverIndex | (C.cover a).baseDomain.Nonempty}.Finite :=
    C.locallyFinite.finite_nonempty_of_compact
  let : Finite A := hA.to_subtype
  let : ∀ a : A, Finite (C.ChartIndex a.val) := fun a => finite_chartIndex C a.val
  let f : C.Index → Sigma (fun a : A => C.ChartIndex a.val) := fun ν =>
    ⟨⟨ν.1, baseDomain_nonempty_of_chart C ν.1 ν.2⟩, ν.2⟩
  let g : Sigma (fun a : A => C.ChartIndex a.val) → C.Index := fun ν => ⟨ν.1.val, ν.2⟩
  exact Finite.of_injective f (Function.LeftInverse.injective (show Function.LeftInverse g f by
    intro ν
    rfl))

                                                                                

theorem covectorENorm_lt_top_iff [CompactSpace M] (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) (u : RawCovector M) :
    C.covectorENorm k alpha u < ⊤ ↔
      ∀ ν : C.Index, coordinateHolderENorm k alpha (C.chart ν).innerDomain
        ((C.chart ν).liftedCovector u) < ⊤ := by
  let : Finite C.Index := finite_coverIndex C
  constructor
  · intro h ν
    exact (le_iSup (fun μ : C.Index => coordinateHolderENorm k alpha
      (C.chart μ).innerDomain ((C.chart μ).liftedCovector u)) ν).trans_lt h
  · intro h
    exact lt_top_iff_ne_top.mpr (iSup_ne_top fun ν => ne_of_lt (h ν))

                                                                                
theorem cov2ENorm_lt_top_iff [CompactSpace M] (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) (u : RawCov2 M) :
    C.cov2ENorm k alpha u < ⊤ ↔
      ∀ ν : C.Index, coordinateHolderENorm k alpha (C.chart ν).innerDomain
        ((C.chart ν).liftedCov2 u) < ⊤ := by
  let : Finite C.Index := finite_coverIndex C
  constructor
  · intro h ν
    exact (le_iSup (fun μ : C.Index => coordinateHolderENorm k alpha
      (C.chart μ).innerDomain ((C.chart μ).liftedCov2 u)) ν).trans_lt h
  · intro h
    exact lt_top_iff_ne_top.mpr (iSup_ne_top fun ν => ne_of_lt (h ν))


end K24.Global.Holder20261026Lower
/- END Holder20261026Lower.FiniteIndex -/

/- BEGIN Holder20261026.Operators.TensorDescent -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Bundle Filter IsManifold
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal

namespace K24.Global.Holder20261026Operators.TensorDescent
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
variable {F : LocalFiniteCover M}



theorem cov2ContDiff_of_lifted_contDiff (C : BoundedLocalCover M) (k : ℕ) (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain) :
    Cov2ContDiff k u := by
  exact cover_cov2_regularity M C k u hu

theorem cov2Holder_native (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) : Cov2ContDiff k u :=
  cov2ContDiff_of_lifted_contDiff C k u hu.1

                                                                                             
theorem metricAdmissible_native (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g : RawCov2 M) (hg : MetricAdmissible C b g) (k : ℕ) (hk : k ≤ b.order) :
    Cov2ContDiff k g := by
  apply cov2ContDiff_of_lifted_contDiff C k g
  intro ν
  apply ((hg.regularity ν).1.of_le (by exact_mod_cast hk)).mono
  intro x hx
  exact (C.chart ν).closureInnerSubset (subset_closure hx)

theorem metricAdmissible_native_two (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g : RawCov2 M) (hg : MetricAdmissible C b g) : Cov2ContDiff 2 g :=
  metricAdmissible_native C b g hg 2 b.order_ge_two

end K24.Global.Holder20261026Operators.TensorDescent
/- END Holder20261026.Operators.TensorDescent -/

/- BEGIN Holder20261026Lower.LowerFiniteness -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Lower

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

                                                                           
                                                                        
theorem lower_jet_lipschitz_compact (m j : ℕ) (hjm : j < m)
    {s t : Set E} (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t)
    (f : E → V) (hf : ContDiffOn ℝ m f t) :
    ∃ L : ℝ≥0, LipschitzOnWith L (iteratedFDeriv ℝ j f) s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs
  intro x hx
  have hc : ContDiffAt ℝ 1 (iteratedFDeriv ℝ j f) x :=
    (hf.contDiffAt (ht.mem_nhds (hst hx))).iteratedFDeriv_right (by exact_mod_cast (show 1+j ≤ m by omega))
  obtain ⟨L,u,hu,hL⟩ := hc.exists_lipschitzOnWith
  exact ⟨L,u,mem_nhdsWithin_of_mem_nhds hu,hL⟩

                                                                           
                                                                            
theorem coordinate_lower_finite (m j : ℕ) (hjm : j < m) (alpha : ℝ≥0)
    (ha : alpha ≤ 1) {s t : Set E} (hs : IsOpen s) (ht : IsOpen t)
    (hc : IsCompact (closure s)) (hst : closure s ⊆ t)
    (f : E → V) (hf : ContDiffOn ℝ m f t) :
    coordinateHolderENorm j alpha s f < ⊤ := by
  have hcont (i : ℕ) (hi : i ≤ m) : ContinuousOn (iteratedFDeriv ℝ i f) (closure s) := by
    intro x hx
    exact ((hf.contDiffAt (ht.mem_nhds (hst hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast hi)).continuousWithinAt
  have hjet (i : ℕ) (hi : i ≤ m) : derivativeENorm i s f < ⊤ := by
    obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (hcont i hi)
    apply lt_of_le_of_lt (b := ENNReal.ofReal B) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro x
    change ‖iteratedFDerivWithin ℝ i f s x‖ₑ ≤ _
    rw [iteratedFDerivWithin_of_isOpen i hs x.property, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB x (subset_closure x.property))
  obtain ⟨L,hL⟩ := lower_jet_lipschitz_compact m j hjm hc ht hst f hf
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (hcont j hjm.le)
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hb (x : s) : ‖iteratedFDeriv ℝ j f x‖ ≤ Bn :=
    (hB x (subset_closure x.property)).trans (le_max_left _ _)
  have hz : HolderWith (2*Bn) 0 (fun x : s => iteratedFDeriv ℝ j f x) := by
    intro x y
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      linarith [hb x,hb y])
  have hl : LipschitzWith L (fun x : s => iteratedFDeriv ℝ j f x) := by
    intro x y
    exact hL (subset_closure x.property) (subset_closure y.property)
  have hh := hz.of_le_of_le hl.holderWith (bot_le : 0 ≤ alpha) ha
  have hh' : eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ j f s x) < ⊤ := by
    have heq : (fun x : s => iteratedFDerivWithin ℝ j f s x) =
        (fun x : s => iteratedFDeriv ℝ j f x) := by
      funext x
      exact iteratedFDerivWithin_of_isOpen j hs x.property
    rw [heq]
    exact hh.memHolder.eHolderNorm_lt_top
  apply ENNReal.add_lt_top.mpr
  refine ⟨?_,hh'⟩
  exact ENNReal.sum_lt_top.mpr fun i hi => hjet i (by have := Finset.mem_range.mp hi; omega)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M]

                                                                            
                                                                             
                                

theorem covectorHolder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCovector M)
    (hu : C.CovectorHolder m alpha u) : C.CovectorHolder j alpha u := by
  exact (fixed_cover_holder_lowering M C m j hjm alpha ha).2.1 u hu


theorem cov2Holder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCov2 M)
    (hu : C.Cov2Holder m alpha u) : C.Cov2Holder j alpha u := by
  exact (fixed_cover_holder_lowering M C m j hjm alpha ha).2.2.1 u hu

end K24.Global.Holder20261026Lower
/- END Holder20261026Lower.LowerFiniteness -/

/- BEGIN Holder20261026Lower.CompactHolder -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set Metric
open scoped NNReal ENNReal

namespace K24.Global.Holder20261026Lower

variable {E V : Type*} [PseudoMetricSpace E] [NormedAddCommGroup V]

                                                                               
                                                           
theorem compact_holder_of_local {s : Set E} (hs : IsCompact s)
    (alpha : ℝ≥0) (ha : 0 < alpha) (f : E → V)
    (hloc : ∀ x ∈ s, ∃ L : ℝ≥0, ∃ u ∈ 𝓝[s] x, HolderOnWith L alpha f u) :
    ∃ L : ℝ≥0, HolderOnWith L alpha f s := by
  have hf : ContinuousOn f s := by
    intro x hx
    obtain ⟨L,u,hu,hL⟩ := hloc x hx
    exact ((hL.continuousOn ha) x (mem_of_mem_nhdsWithin hx hu)).mono_of_mem_nhdsWithin hu
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuousOn hf
  let Bn : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hb (x : E) (hx : x ∈ s) : ‖f x‖ ≤ Bn := (hB x hx).trans (le_max_left _ _)
  have hlocal : ∀ x ∈ s, ∃ eps > 0, ∃ L : ℝ≥0,
      HolderOnWith L alpha f (ball x eps ∩ s) := by
    intro x hx
    obtain ⟨L,u,hu,hL⟩ := hloc x hx
    obtain ⟨eps,heps,hsub⟩ := Metric.mem_nhdsWithin_iff.mp hu
    exact ⟨eps,heps,L,hL.mono hsub⟩
  choose eps heps L hL using hlocal
  let smallRadius (x : E) (hx : x ∈ s) : ℝ≥0 := ⟨eps x hx / 2,(half_pos (heps x hx)).le⟩
  let bound (x : E) (hx : x ∈ s) : ℝ≥0 :=
    max (L x hx) (2*Bn / (smallRadius x hx) ^ (alpha : ℝ))
  obtain ⟨t,ht⟩ := hs.elim_nhdsWithin_subcover' (fun x hx => s ∩ ball x (eps x hx / 2))
    (fun x hx => inter_mem_nhdsWithin s (ball_mem_nhds x (half_pos (heps x hx))))
  refine ⟨t.sup (fun x => bound x x.property), ?_⟩
  intro x hx y hy
  obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (ht hx)
  have hbound : bound z z.property ≤ t.sup (fun z => bound z z.property) :=
    Finset.le_sup (f := fun z : s => bound z z.property) hz
  by_cases hyz : y ∈ ball (z : E) (eps z z.property)
  · have hxz' : x ∈ ball (z : E) (eps z z.property) :=
      hxz.2.trans (half_lt_self (heps z z.property))
    exact (hL z z.property x ⟨hxz',hx⟩ y ⟨hyz,hy⟩).trans (by
      gcongr
      exact (le_max_left _ _).trans hbound)
  · have hr : 0 < eps z z.property / 2 := half_pos (heps z z.property)
    have hdist : eps z z.property / 2 ≤ dist x y := by
      have hnear : dist x z < eps z z.property / 2 := hxz.2
      have hfar : eps z z.property ≤ dist y z := not_lt.mp hyz
      linarith [dist_triangle y x z, dist_comm y x]
    have hp : (eps z z.property / 2) ^ (alpha : ℝ) ≤ dist x y ^ (alpha : ℝ) :=
      Real.rpow_le_rpow hr.le hdist alpha.coe_nonneg
    have hpowpos : 0 < (eps z z.property / 2) ^ (alpha : ℝ) := Real.rpow_pos_of_pos hr _
    have hd : dist (f x) (f y) ≤ 2 * (Bn : ℝ) := by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hb x hx,hb y hy])
    have hlarge : dist (f x) (f y) ≤
        (2 * (Bn : ℝ) / (eps z z.property / 2) ^ (alpha : ℝ)) * dist x y ^ (alpha : ℝ) := by
      apply hd.trans
      calc
        2 * (Bn : ℝ) = (2 * (Bn : ℝ) / (eps z z.property / 2) ^ (alpha : ℝ)) *
            (eps z z.property / 2) ^ (alpha : ℝ) := (div_mul_cancel₀ _ hpowpos.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
    have hcoeff : (2 * (Bn : ℝ) / (eps z z.property / 2) ^ (alpha : ℝ)) ≤
        ((t.sup (fun z : s => bound z z.property) : ℝ≥0) : ℝ) := by
      have h' := (le_max_right (L z z.property)
        (2*Bn / (smallRadius z z.property) ^ (alpha : ℝ))).trans hbound
      exact_mod_cast h'
    have hdistBound : dist (f x) (f y) ≤
        ((t.sup (fun z : s => bound z z.property) : ℝ≥0) : ℝ) * dist x y ^ (alpha : ℝ) :=
      hlarge.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg dist_nonneg _))
    rw [edist_dist,edist_dist,ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul (t.sup (fun z => bound z z.property)).coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hdistBound

                                                                          


variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [CompactSpace M]

                                                                            
                                                          

end K24.Global.Holder20261026Lower
/- END Holder20261026Lower.CompactHolder -/

/- BEGIN Holder20261026Lower.HolderGerm -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set Metric
open scoped NNReal ENNReal ContDiff BigOperators

namespace K24.Global.Holder20261026Lower

variable {E V F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

                                                                                   
def LocallyAllHolder (k : ℕ) (alpha : ℝ≥0) (f : E → V) (x : E) : Prop :=
  ∃ s : Set E, IsOpen s ∧ x ∈ s ∧ ∀ j ≤ k, BigHolderOn j alpha s f

theorem bigHolderOn_restrict (k : ℕ) (alpha : ℝ≥0) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (hst : s ⊆ t) (f : E → V)
    (hf : BigHolderOn k alpha t f) : BigHolderOn k alpha s f :=
  ⟨hf.1.mono hst,(pos_coordinate_restrict k alpha hs ht hst f).trans_lt hf.2⟩

theorem LocallyAllHolder.mono {k j : ℕ} {alpha : ℝ≥0} {f : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hjk : j ≤ k) :
    LocallyAllHolder j alpha f x := by
  obtain ⟨s,hs,hx,hf⟩ := hf
  exact ⟨s,hs,hx,fun i hi => hf i (hi.trans hjk)⟩

theorem LocallyAllHolder.contDiffAt {k : ℕ} {alpha : ℝ≥0} {f : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) : ContDiffAt ℝ k f x := by
  obtain ⟨s,hs,hx,hf⟩ := hf
  exact (hf k le_rfl).1.contDiffAt (hs.mem_nhds hx)

private theorem bigHolderOn_congr_generic (k : ℕ) (alpha : ℝ≥0) {s : Set E}
    {f g : E → V} (h : Set.EqOn f g s) (hf : BigHolderOn k alpha s f) :
    BigHolderOn k alpha s g := by
  refine ⟨hf.1.congr (fun x hx => (h hx).symm), ?_⟩
  have hd (j : ℕ) : derivativeENorm j s g = derivativeENorm j s f := by
    unfold derivativeENorm
    apply iSup_congr
    intro x
    rw [h.iteratedFDerivWithin j x.property]
  have hj : (fun x : s => iteratedFDerivWithin ℝ k g s x) =
      (fun x : s => iteratedFDerivWithin ℝ k f s x) := by
    funext x
    exact (h.iteratedFDerivWithin k x.property).symm
  unfold coordinateHolderENorm
  simp_rw [hd,hj]
  exact hf.2

theorem LocallyAllHolder.congr {k : ℕ} {alpha : ℝ≥0} {f g : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hfg : f =ᶠ[𝓝 x] g) :
    LocallyAllHolder k alpha g x := by
  obtain ⟨s,hs,hx,hf⟩ := hf
  obtain ⟨u,hu,hxu,hus⟩ := _root_.mem_nhds_iff.mp hfg
  refine ⟨s ∩ u,hs.inter hxu,⟨hx,hus⟩,?_⟩
  intro j hj
  exact bigHolderOn_congr_generic j alpha (show Set.EqOn f g (s ∩ u) from fun y hy => hu hy.2)
    (bigHolderOn_restrict j alpha (hs.inter hxu) hs inter_subset_left f (hf j hj))

theorem LocallyAllHolder.const (k : ℕ) (alpha : ℝ≥0) (c : V) (x : E) :
    LocallyAllHolder k alpha (fun _ : E => c) x := by
  refine ⟨univ,isOpen_univ,mem_univ x,?_⟩
  intro j hj
  refine ⟨contDiffOn_const,?_⟩
  have hjets (i : ℕ) (hi : i ≤ j) (y : E) (hy : y ∈ (univ : Set E)) :
      ‖iteratedFDerivWithin ℝ i (fun _ : E => c) univ y‖ ≤ ‖c‖₊ := by
    by_cases hi0 : i = 0
    · subst i
      simp only [norm_iteratedFDerivWithin_zero, coe_nnnorm]
      exact le_rfl
    · simp only [iteratedFDerivWithin_const_of_ne hi0,Pi.zero_apply,norm_zero]
      exact (nnnorm c).coe_nonneg
  have hh : HolderWith 0 alpha
      (fun y : (univ : Set E) => iteratedFDerivWithin ℝ j (fun _ : E => c) univ y) := by
    intro y z
    by_cases hj0 : j = 0
    · subst j
      simp only [edist_dist,dist_iteratedFDerivWithin_zero,dist_self,ENNReal.ofReal_zero]
      exact bot_le
    · simp only [iteratedFDerivWithin_const_of_ne hj0,Pi.zero_apply,edist_self]
      exact bot_le
  exact (pos_coordinate_bound j alpha ‖c‖₊ 0 univ (fun _ : E => c) hjets hh).trans_lt
    (by finiteness)

theorem LocallyAllHolder.bilinear {k : ℕ} {alpha : ℝ≥0} {f : E → V} {g : E → F} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hg : LocallyAllHolder k alpha g x)
    (B : V →L[ℝ] F →L[ℝ] G) : LocallyAllHolder k alpha (fun y => B (f y) (g y)) x := by
  obtain ⟨s,hs,hxs,hf⟩ := hf
  obtain ⟨t,ht,hxt,hg⟩ := hg
  refine ⟨s ∩ t,hs.inter ht,⟨hxs,hxt⟩,?_⟩
  intro j hj
  exact HolderAllJets.bigHolderOn_bilinear j alpha (hs.inter ht) B f g
    (fun i hi => bigHolderOn_restrict i alpha (hs.inter ht) hs inter_subset_left f (hf i (hi.trans hj)))
    (fun i hi => bigHolderOn_restrict i alpha (hs.inter ht) ht inter_subset_right g (hg i (hi.trans hj)))

theorem LocallyAllHolder.clm {k : ℕ} {alpha : ℝ≥0} {f : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) (L : V →L[ℝ] F) :
    LocallyAllHolder k alpha (fun y => L (f y)) x :=
  hf.bilinear (LocallyAllHolder.const k alpha L x) (ContinuousLinearMap.apply ℝ F)

theorem LocallyAllHolder.add {k : ℕ} {alpha : ℝ≥0} {f g : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hg : LocallyAllHolder k alpha g x) :
    LocallyAllHolder k alpha (fun y => f y + g y) x := by
  obtain ⟨s,hs,hxs,hf⟩ := hf
  obtain ⟨t,ht,hxt,hg⟩ := hg
  refine ⟨s ∩ t,hs.inter ht,⟨hxs,hxt⟩,?_⟩
  intro j hj
  have hfj := bigHolderOn_restrict j alpha (hs.inter ht) hs inter_subset_left f (hf j hj)
  have hgj := bigHolderOn_restrict j alpha (hs.inter ht) ht inter_subset_right g (hg j hj)
  exact ⟨hfj.1.add hgj.1,(coordinateHolderENorm_add_le j alpha (hs.inter ht) f g
    hfj.1 hgj.1).trans_lt (ENNReal.add_lt_top.mpr ⟨hfj.2,hgj.2⟩)⟩

theorem LocallyAllHolder.neg {k : ℕ} {alpha : ℝ≥0} {f : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) : LocallyAllHolder k alpha (fun y => -f y) x := by
  simpa using hf.clm (-ContinuousLinearMap.id ℝ V)

theorem LocallyAllHolder.sub {k : ℕ} {alpha : ℝ≥0} {f g : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hg : LocallyAllHolder k alpha g x) :
    LocallyAllHolder k alpha (fun y => f y - g y) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem LocallyAllHolder.smul {k : ℕ} {alpha : ℝ≥0} {f : E → ℝ} {g : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hg : LocallyAllHolder k alpha g x) :
    LocallyAllHolder k alpha (fun y => f y • g y) x :=
  hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)

theorem LocallyAllHolder.finset_sum {ι : Type*} (t : Finset ι)
    {k : ℕ} {alpha : ℝ≥0} {f : ι → E → V} {x : E}
    (hf : ∀ i ∈ t, LocallyAllHolder k alpha (f i) x) :
    LocallyAllHolder k alpha (fun y => ∑ i ∈ t, f i y) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using LocallyAllHolder.const k alpha (0 : V) x
  | @insert i t hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem LocallyAllHolder.pi {ι : Type*} [Fintype ι]
    {k : ℕ} {alpha : ℝ≥0} {f : E → ι → V} {x : E}
    (hf : ∀ i, LocallyAllHolder k alpha (fun y => f y i) x) :
    LocallyAllHolder k alpha f x := by
  classical
  have hs := LocallyAllHolder.finset_sum Finset.univ
    (fun i _ => (hf i).clm (ContinuousLinearMap.single ℝ (fun _ : ι => V) i))
  convert hs using 1
  funext y i
  simp

theorem LocallyAllHolder.fderiv {k : ℕ} {alpha : ℝ≥0} {f : E → V} {x : E}
    (hf : LocallyAllHolder (k+1) alpha f x) :
    LocallyAllHolder k alpha (fderiv ℝ f) x := by
  obtain ⟨s,hs,hx,hf⟩ := hf
  exact ⟨s,hs,hx,fun j hj => HolderJetNorm.bigHolderOn_fderiv j alpha hs f
    (hf (j+1) (by omega))⟩

theorem LocallyAllHolder.of_contDiffAt [ProperSpace E]
    (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) (f : E → V) (x : E)
    (hf : ContDiffAt ℝ (k+1) f x) : LocallyAllHolder k alpha f x := by
  obtain ⟨u,hu,hreg⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r,hr,hru⟩ := Metric.mem_nhds_iff.mp hu
  have hreg' := hreg.mono hru
  have hcompact : IsCompact (closure (ball x (r/2))) :=
    (isCompact_closedBall x (r/2)).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hsub : closure (ball x (r/2)) ⊆ ball x r := by
    intro y hy
    have h := closure_ball_subset_closedBall hy
    exact lt_of_le_of_lt h (half_lt_self hr)
  refine ⟨ball x (r/2),isOpen_ball,mem_ball_self (half_pos hr),?_⟩
  intro j hj
  refine ⟨(hreg'.mono (fun y hy => hsub (subset_closure hy))).of_le
    (by exact_mod_cast (show j ≤ k+1 by omega)), ?_⟩
  exact coordinate_lower_finite (k+1) j (by omega) alpha ha isOpen_ball isOpen_ball
    hcompact hsub f hreg'

section Composition
universe uGerm
variable {D E' V' : Type uGerm} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

                                                                             
                                                                           
theorem LocallyAllHolder.comp_of_lipschitz {k : ℕ} {alpha : ℝ≥0}
    {f : E' → V'} {g : D → E'} {x : D}
    (hf : LocallyAllHolder k alpha f (g x)) (hg : LocallyAllHolder k alpha g x)
    (hLip : ∃ L : ℝ≥0, ∃ u ∈ 𝓝 x, LipschitzOnWith L g u) :
    LocallyAllHolder k alpha (f ∘ g) x := by
  have hgc := hg.contDiffAt.continuousAt
  obtain ⟨s,hs,hxs,hf⟩ := hf
  obtain ⟨t,ht,hxt,hg⟩ := hg
  obtain ⟨L,u,hu,hL⟩ := hLip
  obtain ⟨v,hvu,hv,hxv⟩ := _root_.mem_nhds_iff.mp hu
  obtain ⟨w,hws,hw,hxw⟩ := _root_.mem_nhds_iff.mp
    (hgc.preimage_mem_nhds (hs.mem_nhds hxs))
  let z := t ∩ v ∩ w
  have hz : IsOpen z := (ht.inter hv).inter hw
  have hzreg : ∀ j ≤ k, BigHolderOn j alpha z g :=
    fun j hj => bigHolderOn_restrict j alpha hz ht (fun _ hy => hy.1.1) g (hg j hj)
  have hmap : MapsTo g z s := fun _ hy => hws hy.2
  exact ⟨z,hz,⟨⟨hxt,hxv⟩,hxw⟩,
    HolderComposition.bigHolderOn_comp_all k alpha hs hz f g hf hzreg hmap L
      (hL.mono (fun _ hy => hvu hy.1.2))⟩

theorem LocallyAllHolder.comp {k : ℕ} {alpha : ℝ≥0}
    {f : E' → V'} {g : D → E'} {x : D}
    (hf : LocallyAllHolder k alpha f (g x)) (hg : LocallyAllHolder k alpha g x)
    (hgd : ContDiffAt ℝ 1 g x) : LocallyAllHolder k alpha (f ∘ g) x :=
  hf.comp_of_lipschitz hg hgd.exists_lipschitzOnWith

theorem LocallyAllHolder.comp_smooth [ProperSpace D] {k : ℕ} {alpha : ℝ≥0}
    {f : E' → V'} {g : D → E'} {x : D}
    (hf : LocallyAllHolder k alpha f (g x)) (ha : alpha ≤ 1)
    (hg : ContDiffAt ℝ (k+1) g x) : LocallyAllHolder k alpha (f ∘ g) x :=
  hf.comp (LocallyAllHolder.of_contDiffAt k alpha ha g x hg)
    (hg.of_le (by exact_mod_cast (show 1 ≤ k+1 by omega)))

theorem LocallyAllHolder.comp_of_contDiffAt [ProperSpace D] {k : ℕ} {alpha : ℝ≥0}
    {f : E' → V'} {g : D → E'} {x : D}
    (hf : LocallyAllHolder k alpha f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    (ha : alpha ≤ 1) : LocallyAllHolder k alpha (f ∘ g) x :=
  hf.comp_smooth ha (hg.of_le (by exact_mod_cast (le_top : (k+1 : ℕ∞) ≤ ⊤)))

end Composition

end K24.Global.Holder20261026Lower


/- END Holder20261026Lower.HolderGerm -/

/- BEGIN Holder20261026Lower.GermGluing -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Set Metric
open scoped NNReal ENNReal ContDiff Manifold Matrix.Norms.Elementwise
namespace K24.Global.Holder20261026Lower

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem LocallyAllHolder.topJet_local {k : ℕ} {alpha : ℝ≥0} {f : E → V} {x : E}
    (hf : LocallyAllHolder k alpha f x) :
    ∃ L : ℝ≥0, ∃ s ∈ 𝓝 x, HolderOnWith L alpha (iteratedFDeriv ℝ k f) s := by
  obtain ⟨s,hs,hx,hf⟩ := hf
  have hh : eHolderNorm alpha (fun y : s => iteratedFDerivWithin ℝ k f s y) < ⊤ :=
    le_add_self.trans_lt (hf k le_rfl).2
  have hm := eHolderNorm_lt_top.mp hh
  refine ⟨nnHolderNorm alpha (fun y : s => iteratedFDerivWithin ℝ k f s y),s,
    hs.mem_nhds hx,?_⟩
  intro y hy z hz
  have h := hm.holderWith (⟨y,hy⟩ : s) (⟨z,hz⟩ : s)
  simpa only [iteratedFDerivWithin_of_isOpen k hs hy,
    iteratedFDerivWithin_of_isOpen k hs hz,Subtype.edist_eq] using h

                                                                         
                                                          
theorem coordinate_bigHolder_of_germs (k : ℕ) (alpha : ℝ≥0) (ha : 0 < alpha)
    {s : Set E} (hs : IsOpen s) (hc : IsCompact (closure s)) (f : E → V)
    (hg : ∀ x ∈ closure s, LocallyAllHolder k alpha f x) : BigHolderOn k alpha s f := by
  have hreg (x : E) (hx : x ∈ closure s) : ContDiffAt ℝ k f x := (hg x hx).contDiffAt
  refine ⟨fun x hx => (hreg x (subset_closure hx)).contDiffWithinAt,?_⟩
  have hjet (i : ℕ) (hi : i ≤ k) : derivativeENorm i s f < ⊤ := by
    have hcont : ContinuousOn (iteratedFDeriv ℝ i f) (closure s) :=
      fun x hx => ((hreg x hx).continuousAt_iteratedFDeriv (by exact_mod_cast hi)).continuousWithinAt
    obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn hcont
    apply lt_of_le_of_lt (b := ENNReal.ofReal B) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro x
    change ‖iteratedFDerivWithin ℝ i f s x‖ₑ ≤ _
    rw [iteratedFDerivWithin_of_isOpen i hs x.property,← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB x (subset_closure x.property))
  have hloc : ∀ x ∈ closure s, ∃ L : ℝ≥0, ∃ u ∈ 𝓝[closure s] x,
      HolderOnWith L alpha (iteratedFDeriv ℝ k f) u := by
    intro x hx
    obtain ⟨L,u,hu,hL⟩ := (hg x hx).topJet_local
    exact ⟨L,u,mem_nhdsWithin_of_mem_nhds hu,hL⟩
  obtain ⟨L,hL⟩ := compact_holder_of_local hc alpha ha (iteratedFDeriv ℝ k f) hloc
  have hh : HolderWith L alpha (fun x : s => iteratedFDerivWithin ℝ k f s x) := by
    intro x y
    simpa only [iteratedFDerivWithin_of_isOpen k hs x.property,
      iteratedFDerivWithin_of_isOpen k hs y.property,Subtype.edist_eq] using
      hL x (subset_closure x.property) y (subset_closure y.property)
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr
    (fun i hi => hjet i (by have := Finset.mem_range.mp hi; omega)),
    hh.memHolder.eHolderNorm_lt_top⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [CompactSpace M]


theorem covectorHolder_of_lifted_germs (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : 0 < alpha) (u : RawCovector M)
    (hg : ∀ nu : C.Index, ∀ x ∈ closure (C.chart nu).innerDomain,
      LocallyAllHolder k alpha ((C.chart nu).liftedCovector u) x) : C.CovectorHolder k alpha u := by
  have hc (nu : C.Index) := coordinate_bigHolder_of_germs k alpha ha
    (C.chart nu).innerOpen (C.chart nu).innerCompactClosure _ (hg nu)
  exact ⟨fun nu => (hc nu).1,(covectorENorm_lt_top_iff C k alpha u).mpr (fun nu => (hc nu).2)⟩

theorem cov2Holder_of_lifted_germs (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : 0 < alpha) (u : RawCov2 M)
    (hg : ∀ nu : C.Index, ∀ x ∈ closure (C.chart nu).innerDomain,
      LocallyAllHolder k alpha ((C.chart nu).liftedCov2 u) x) : C.Cov2Holder k alpha u := by
  have hc (nu : C.Index) := coordinate_bigHolder_of_germs k alpha ha
    (C.chart nu).innerOpen (C.chart nu).innerCompactClosure _ (hg nu)
  exact ⟨fun nu => (hc nu).1,(cov2ENorm_lt_top_iff C k alpha u).mpr (fun nu => (hc nu).2)⟩

variable [IsManifold I4 ∞ M]


theorem covectorHolder_inner_germ (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCovector M) (hu : C.CovectorHolder k alpha u)
    (nu : C.Index) (x : FourSpace) (hx : x ∈ (C.chart nu).innerDomain) :
    LocallyAllHolder k alpha ((C.chart nu).liftedCovector u) x := by
  refine ⟨(C.chart nu).innerDomain,(C.chart nu).innerOpen,hx,?_⟩
  intro j hj
  have h := covectorHolder_lower C k j hj alpha ha u hu
  exact ⟨h.1 nu,(le_iSup (fun mu : C.Index => coordinateHolderENorm j alpha
    (C.chart mu).innerDomain ((C.chart mu).liftedCovector u)) nu).trans_lt h.2⟩

theorem cov2Holder_inner_germ (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u)
    (nu : C.Index) (x : FourSpace) (hx : x ∈ (C.chart nu).innerDomain) :
    LocallyAllHolder k alpha ((C.chart nu).liftedCov2 u) x := by
  refine ⟨(C.chart nu).innerDomain,(C.chart nu).innerOpen,hx,?_⟩
  intro j hj
  have h := cov2Holder_lower C k j hj alpha ha u hu
  exact ⟨h.1 nu,(le_iSup (fun mu : C.Index => coordinateHolderENorm j alpha
    (C.chart mu).innerDomain ((C.chart mu).liftedCov2 u)) nu).trans_lt h.2⟩

end K24.Global.Holder20261026Lower
/- END Holder20261026Lower.GermGluing -/

/- BEGIN Holder20261026.Operators.NativeHolderTransport -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators
open Holder20261026Lower

theorem holder_clm_apply {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : ℕ} {alpha : ℝ≥0} {A : E → V →L[ℝ] W} {f : E → V} {x : E}
    (hA : LocallyAllHolder k alpha A x) (hf : LocallyAllHolder k alpha f x) :
    LocallyAllHolder k alpha (fun y => A y (f y)) x :=
  hA.bilinear hf (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ W))

theorem holder_covector_eval {k : ℕ} {alpha : ℝ≥0}
    {a : FourSpace → Fin 4 → ℝ} {v : FourSpace → FourSpace} {x : FourSpace}
    (ha : LocallyAllHolder k alpha a x) (hv : LocallyAllHolder k alpha v x) :
    LocallyAllHolder k alpha (fun y => coefficientsToCovector (a y) (v y)) x := by
  have h := LocallyAllHolder.finset_sum Finset.univ (fun i _ =>
    (ha.clm (ContinuousLinearMap.proj i)).smul (hv.clm (coordProj i)))
  simpa [HaarSectors.coefficientsToCovector_apply, smul_eq_mul, coordProj] using h

theorem holder_matrix_eval {k : ℕ} {alpha : ℝ≥0}
    {a : FourSpace → Mat4} {v w : FourSpace → FourSpace} {x : FourSpace}
    (ha : LocallyAllHolder k alpha a x) (hv : LocallyAllHolder k alpha v x)
    (hw : LocallyAllHolder k alpha w x) :
    LocallyAllHolder k alpha (fun y => matrixToBilinear (a y) (v y) (w y)) x := by
  have h := LocallyAllHolder.finset_sum Finset.univ (fun i _ =>
    LocallyAllHolder.finset_sum Finset.univ (fun j _ =>
      (hv.clm (coordProj i)).smul
        (((ha.clm (ContinuousLinearMap.proj i)).clm (ContinuousLinearMap.proj j)).smul
          (hw.clm (coordProj j)))))
  change LocallyAllHolder k alpha
    (fun y => ∑ i : Fin 4, ∑ j : Fin 4, v y i * (a y i j * w y j)) x at h
  simpa only [HaarSectors.matrixToBilinear_apply] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M]

                                                                         
                                    

theorem covectorHolder_native_germ (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (ha : alpha ≤ 1) (eta : RawCovector M) (heta : C.CovectorHolder k alpha eta)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target) :
    LocallyAllHolder k alpha (covectorInChart eta d) z := by
  obtain ⟨nu, x, hx, hxp, psi, hpsi, hleft, hnear⟩ := exists_inner_coordinate_inverse C d z hz
  let c := C.chart nu
  have hxo : x ∈ c.outerDomain := c.closureInnerSubset (subset_closure hx)
  have hd : c.lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]; exact (chartAt FourSpace d).map_target hz
  let J := fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse
  have hJ : LocallyAllHolder k alpha J x :=
    LocallyAllHolder.of_contDiffAt k alpha ha J x
      ((inverse_frame_contDiffAt_infty c d x hxo hd).of_le
        (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))
  have hf := covectorHolder_inner_germ C k alpha ha eta heta nu x hx
  apply LocallyAllHolder.pi
  intro i
  have hv := holder_clm_apply hJ (LocallyAllHolder.const k alpha (basisVector i) x)
  have hp := holder_covector_eval hf hv
  have hp' : LocallyAllHolder k alpha
      ((fun y => coefficientsToCovector (c.liftedCovector eta y) (J y (basisVector i))) ∘ psi) z := by
    apply LocallyAllHolder.comp_of_contDiffAt (g := psi) _ hpsi ha
    simpa only [hleft] using hp
  apply hp'.congr
  filter_upwards [hnear] with y hy
  have he := NativeRegularity.covector_coord_lift c eta d (psi y)
    (c.closureInnerSubset (subset_closure hy.1)) hy.2.1 i
  have hr : chartAt FourSpace d (c.lift (psi y)) = y := hy.2.2
  rw [hr] at he
  simpa only [J, Function.comp_apply] using he.symm

theorem cov2Holder_native_germ (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (ha : alpha ≤ 1) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target) :
    LocallyAllHolder k alpha (cov2InChart u d) z := by
  obtain ⟨nu, x, hx, hxp, psi, hpsi, hleft, hnear⟩ := exists_inner_coordinate_inverse C d z hz
  let c := C.chart nu
  have hxo : x ∈ c.outerDomain := c.closureInnerSubset (subset_closure hx)
  have hd : c.lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]; exact (chartAt FourSpace d).map_target hz
  let J := fun y => (fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) y).inverse
  have hJ : LocallyAllHolder k alpha J x :=
    LocallyAllHolder.of_contDiffAt k alpha ha J x
      ((inverse_frame_contDiffAt_infty c d x hxo hd).of_le
        (by exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))
  have hf := cov2Holder_inner_germ C k alpha ha u hu nu x hx
  apply LocallyAllHolder.pi
  intro i
  apply LocallyAllHolder.pi
  intro j
  have hv := holder_clm_apply hJ (LocallyAllHolder.const k alpha (basisVector i) x)
  have hw := holder_clm_apply hJ (LocallyAllHolder.const k alpha (basisVector j) x)
  have hp := holder_matrix_eval hf hv hw
  have hp' : LocallyAllHolder k alpha
      ((fun y => matrixToBilinear (c.liftedCov2 u y) (J y (basisVector i))
        (J y (basisVector j))) ∘ psi) z := by
    apply LocallyAllHolder.comp_of_contDiffAt (g := psi) _ hpsi ha
    simpa only [hleft] using hp
  apply hp'.congr
  filter_upwards [hnear] with y hy
  have he := CoverContinuity.cov2_coord_lift c u d (psi y)
    (c.closureInnerSubset (subset_closure hy.1)) hy.2.1 i j
  have hr : chartAt FourSpace d (c.lift (psi y)) = y := hy.2.2
  rw [hr] at he
  simpa only [J, Function.comp_apply] using he.symm

theorem liftedCovector_germ_of_native {F : LocalFiniteCover M} (c : LocalCoverChart F)
    (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) (eta : RawCovector M)
    (hnative : ∀ (d : M) (z : FourSpace), z ∈ (chartAt FourSpace d).target →
      LocallyAllHolder k alpha (covectorInChart eta d) z)
    (x : FourSpace) (hx : x ∈ c.outerDomain) :
    LocallyAllHolder k alpha (c.liftedCovector eta) x := by
  let d := c.lift x
  have hd : c.lift x ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  let F := (chartAt FourSpace d) ∘ c.lift
  have hF : ContDiffAt ℝ ∞ F x := NativeRegularity.coord_smoothAt c d x hx hd
  have hc := (hnative d (F x) ((chartAt FourSpace d).map_source hd)).comp_of_contDiffAt hF ha
  have hJ : LocallyAllHolder k alpha (fderiv ℝ F) x :=
    LocallyAllHolder.of_contDiffAt k alpha ha _ x
      (hF.fderiv_right (by exact_mod_cast (le_top : (k + 1 + 1 : ℕ∞) ≤ ⊤)))
  apply LocallyAllHolder.pi
  intro i
  have hv := holder_clm_apply hJ (LocallyAllHolder.const k alpha (basisVector i) x)
  apply (holder_covector_eval hc hv).congr
  filter_upwards [c.outerOpen.mem_nhds hx,
    (NativeRegularity.lift_smoothAt c x hx).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact (liftedCovector_eq_native c eta d y hy hyd i).symm

theorem liftedCov2_germ_of_native {F : LocalFiniteCover M} (c : LocalCoverChart F)
    (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCov2 M)
    (hnative : ∀ (d : M) (z : FourSpace), z ∈ (chartAt FourSpace d).target →
      LocallyAllHolder k alpha (cov2InChart u d) z)
    (x : FourSpace) (hx : x ∈ c.outerDomain) :
    LocallyAllHolder k alpha (c.liftedCov2 u) x := by
  let d := c.lift x
  have hd : c.lift x ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  let F := (chartAt FourSpace d) ∘ c.lift
  have hF : ContDiffAt ℝ ∞ F x := NativeRegularity.coord_smoothAt c d x hx hd
  have hc := (hnative d (F x) ((chartAt FourSpace d).map_source hd)).comp_of_contDiffAt hF ha
  have hJ : LocallyAllHolder k alpha (fderiv ℝ F) x :=
    LocallyAllHolder.of_contDiffAt k alpha ha _ x
      (hF.fderiv_right (by exact_mod_cast (le_top : (k + 1 + 1 : ℕ∞) ≤ ⊤)))
  apply LocallyAllHolder.pi
  intro i
  apply LocallyAllHolder.pi
  intro j
  have hv := holder_clm_apply hJ (LocallyAllHolder.const k alpha (basisVector i) x)
  have hw := holder_clm_apply hJ (LocallyAllHolder.const k alpha (basisVector j) x)
  apply (holder_matrix_eval hc hv hw).congr
  filter_upwards [c.outerOpen.mem_nhds hx,
    (NativeRegularity.lift_smoothAt c x hx).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)] with y hy hyd
  exact (liftedCov2_eq_native c u d y hy hyd i j).symm

theorem covectorHolder_of_native_germs (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (hpos : 0 < alpha) (eta : RawCovector M)
    (hnative : ∀ (d : M) (z : FourSpace), z ∈ (chartAt FourSpace d).target →
      LocallyAllHolder k alpha (covectorInChart eta d) z) : C.CovectorHolder k alpha eta := by
  apply covectorHolder_of_lifted_germs C k alpha hpos eta
  intro nu x hx
  exact liftedCovector_germ_of_native (C.chart nu) k alpha ha eta hnative x
    ((C.chart nu).closureInnerSubset hx)

theorem cov2Holder_of_native_germs (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (hpos : 0 < alpha) (u : RawCov2 M)
    (hnative : ∀ (d : M) (z : FourSpace), z ∈ (chartAt FourSpace d).target →
      LocallyAllHolder k alpha (cov2InChart u d) z) : C.Cov2Holder k alpha u := by
  apply cov2Holder_of_lifted_germs C k alpha hpos u
  intro nu x hx
  exact liftedCov2_germ_of_native (C.chart nu) k alpha ha u hnative x
    ((C.chart nu).closureInnerSubset hx)

end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.NativeHolderTransport -/

/- BEGIN Holder20261026.Operators.ArchiveREG -/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.NativeLinearityArchiveREGK24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                            

theorem cov2_coefficient_contDiffOn (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (i j : Fin 4) :
    ContDiffOn ℝ 2 (fun x => cov2InChart g c x i j) (chartAt FourSpace c).target := by
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) j

                                                                       


end K24.Global.NativeLinearityArchiveREGK24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.NativeLinearityArchiveREGK24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

                                                                 

@[simp] theorem matrixToBilinear_basis (A : Mat4) (i j : Fin 4) :
    matrixToBilinear A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToBilinear, basisVector, coordProj, Pi.single_apply]

                                                                           







end K24.Global.NativeLinearityArchiveREGK24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveREGK24REG








end K24.Global.NativeLinearityArchiveREGK24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveREGK24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]








end K24.Global.NativeLinearityArchiveREGK24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveREGK24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]






end K24.Global.NativeLinearityArchiveREGK24REG
/- END Holder20261026.Operators.ArchiveREG -/

/- BEGIN Holder20261026.Operators.ArchiveLOC -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]



lemma cov2InChart_symm (g : RawCov2 M) (hs : IsSymmetricCov2 g)
    (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart g c x i j = cov2InChart g c x j i := by
  exact hs _ _ _


variable [IsManifold I4 ∞ M]

theorem metric_chart_det_ne_zero (g : RawCov2 M) (hg : IsMetric g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    (cov2InChart g c x).det ≠ 0 := by
  have hpos : (cov2InChart g c x).PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · ext i j
      change cov2InChart g c x j i = cov2InChart g c x i j
      exact cov2InChart_symm g hg.1 c x j i
    · intro v hv
      let V : FourSpace := ∑ i : Fin 4, v i • basisVector i
      let di := mfderiv I4 I4 (chartAt FourSpace c).symm x
      have hV : V ≠ 0 := by
        intro h
        apply hv
        funext j
        have hj := congrArg (fun w : FourSpace => w j) h
        simpa [V, basisVector, Pi.single_apply] using hj
      have hleft : Function.LeftInverse
          (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)) di := by
        intro w
        have h := (mdifferentiable_chart (I := I4) c).comp_symm_deriv hx
        exact congrArg (fun A => A w) h
      have hdi : di V ≠ 0 := by
        simpa only [map_zero] using hleft.injective.ne hV
      have hp := hg.2 ((chartAt FourSpace c).symm x) (di V) hdi
      convert hp using 1 <;> try rfl
      simp [dotProduct, Matrix.mulVec, cov2InChart, V, di, map_sum, Finset.mul_sum,
        mul_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact congrArg (fun t : ℝ => v a * (v b * t)) (hg.1 _ _ _)
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hpos.isUnit).ne_zero

end K24.Global.NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection

namespace K24.Global.NativeLinearityArchiveLOCK24OP

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]









end K24.Global.NativeLinearityArchiveLOCK24OP




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveLOCK24SYM

                                                                      
def frequencyLinear (xi : Fin 4 → ℝ) : FourSpace →L[ℝ] ℝ := coefficientsToCovector xi

def jetPhase (x : FourSpace) (xi : Fin 4 → ℝ) (y : FourSpace) : ℝ :=
  ∑ a : Fin 4, xi a * (y a - x a)

def jetCoefficient (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ) (y : FourSpace) : ℝ :=
  (1 / 2 : ℝ) * jetPhase x xi y ^ 2 * a

@[simp] theorem frequencyLinear_basis (xi : Fin 4 → ℝ) (i : Fin 4) :
    frequencyLinear xi (basisVector i) = xi i := by
  simp [frequencyLinear, coefficientsToCovector, coordProj, basisVector]






@[simp] theorem jetPhase_center (x : FourSpace) (xi : Fin 4 → ℝ) : jetPhase x xi x = 0 := by
  simp [jetPhase]

@[simp] theorem jetCoefficient_center (x : FourSpace) (xi : Fin 4 → ℝ) (a : ℝ) :
    jetCoefficient x xi a x = 0 := by simp [jetCoefficient]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]

                                                                                       




end K24.Global.NativeLinearityArchiveLOCK24SYM


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveLOCK24SYM

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable [IsManifold I4 ∞ M]






theorem matrix_det_contDiffAt (A : FourSpace → Mat4) (x : FourSpace) (k : ℕ∞ω)
    (hA : ∀ a b, ContDiffAt ℝ k (fun y => A y a b) x) :
    ContDiffAt ℝ k (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  exact contDiffAt_prod fun i _ => hA (σ i) i

theorem matrix_inv_coefficient_contDiffAt (A : FourSpace → Mat4) (x : FourSpace) (k : ℕ∞ω)
    (hA : ∀ a b, ContDiffAt ℝ k (fun y => A y a b) x)
    (hdet : (A x).det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ k (fun y => (A y)⁻¹ a b) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_apply]
  apply ContDiffAt.mul
  · exact (matrix_det_contDiffAt A x k hA).inv hdet
  · apply matrix_det_contDiffAt
    intro i j
    by_cases hi : i = b
    · subst i
      simp only [Matrix.updateRow_self]
      exact contDiffAt_const
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j

theorem metric_inverse_coefficient_C2 (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun y => inverseMetricInChart g c y a b) x := by
  apply matrix_inv_coefficient_contDiffAt
  · intro i j
    exact (NativeLinearityArchiveREGK24REG.cov2_coefficient_contDiffOn g hg c i j).contDiffAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  · exact NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero g hm c x hx

theorem coordDeriv_contDiffAt {f : FourSpace → ℝ} {x : FourSpace}
    (hf : ContDiffAt ℝ 2 f x) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun y => coordDeriv f i y) x := by
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem christoffel_contDiffAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 2 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (k i j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => christoffelInChart g c y k i j) x := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul
  · exact (metric_inverse_coefficient_C2 g hm hg c x hx k l).of_le (by norm_num)
  · apply ContDiffAt.sub
    · apply ContDiffAt.add
      · exact coordDeriv_contDiffAt
          ((NativeLinearityArchiveREGK24REG.cov2_coefficient_contDiffOn g hg c j l).contDiffAt
            ((chartAt FourSpace c).open_target.mem_nhds hx)) i
      · exact coordDeriv_contDiffAt
          ((NativeLinearityArchiveREGK24REG.cov2_coefficient_contDiffOn g hg c i l).contDiffAt
            ((chartAt FourSpace c).open_target.mem_nhds hx)) j
    · exact coordDeriv_contDiffAt
        ((NativeLinearityArchiveREGK24REG.cov2_coefficient_contDiffOn g hg c i j).contDiffAt
          ((chartAt FourSpace c).open_target.mem_nhds hx)) l







end K24.Global.NativeLinearityArchiveLOCK24SYM


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
/- END Holder20261026.Operators.ArchiveLOC -/

/- BEGIN Holder20261026.Operators.NativeLinearity -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise NNReal

namespace K24.Global.Holder20261026Operators.NativeLinearity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

@[simp] theorem vectorInChart_add (Y Z : RawVector M) (c : M) (x : FourSpace) (i : Fin 4) :
    vectorInChart (Y + Z) c x i = vectorInChart Y c x i + vectorInChart Z c x i := by
  change (coordProj i) (vectorInChart (Y + Z) c x) =
    (coordProj i) (vectorInChart Y c x) + (coordProj i) (vectorInChart Z c x)
  simp [vectorInChart]

@[simp] theorem vectorInChart_smul (a : ℝ) (Y : RawVector M) (c : M) (x : FourSpace) (i : Fin 4) :
    vectorInChart (a • Y) c x i = a * vectorInChart Y c x i := by
  change (coordProj i) (vectorInChart (a • Y) c x) =
    a • (coordProj i) (vectorInChart Y c x)
  simp [vectorInChart]

@[simp] theorem cov2InChart_add (u v : RawCov2 M) (c : M) (x : FourSpace) (i j : Fin 4) :
    cov2InChart (u + v) c x i j = cov2InChart u c x i j + cov2InChart v c x i j := by
  simp [cov2InChart]

@[simp] theorem cov2InChart_smul (a : ℝ) (u : RawCov2 M) (c : M)
    (x : FourSpace) (i j : Fin 4) :
    cov2InChart (a • u) c x i j = a * cov2InChart u c x i j := by
  simp [cov2InChart]












@[simp] theorem lieTensor_zero_vector (g : RawCov2 M) : lieTensor (0 : RawVector M) g = 0 := by
  ext p v w
  simp [lieTensor, lieTensorInChart, vectorInChart, coordDeriv,
    cov2FromCoordinates, cov2FromChartAt, matrixToBilinear]












@[simp] theorem bianchi_zero (g : RawCov2 M) : bianchi g (0 : RawCov2 M) = 0 := by
  have ht (c : M) : metricTraceInChart g (0 : RawCov2 M) c = fun _ => 0 := by
    funext x
    simp [metricTraceInChart, cov2InChart]
  ext p v
  simp [bianchi, bianchiInChart, nablaTensorInChart, ht, cov2InChart,
    coordDeriv, covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector]



@[simp] theorem covectorPiPerp_zero (rho : CircleAction M) :
    covectorPiPerp rho (0 : RawCovector M) = 0 := by
  ext p v
  simp [covectorPiPerp, covectorPi0, actionPullbackCovector, pullbackCovector,
    covectorInChart, covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector]

section Native
variable [IsManifold I4 ∞ M]



@[simp] theorem vectorOperator_zero (ghat g : RawCov2 M) :
    vectorOperator ghat g (0 : RawVector M) = 0 := by
  simp [vectorOperator, killing]
















end Native
end K24.Global.Holder20261026Operators.NativeLinearity
/- END Holder20261026.Operators.NativeLinearity -/

/- BEGIN Holder20261026.Operators.HigherRegularity -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators.HigherRegularity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]




theorem tensor_coefficient_contDiffAt (k : ℕ) (u : RawCov2 M) (hu : Cov2ContDiff k u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ k (fun y => cov2InChart u c y i j) x :=
  (contDiffOn_pi.mp (contDiffOn_pi.mp (hu c) i) j).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)

theorem coordDeriv_contDiffAt (k : ℕ) {f : FourSpace → ℝ} {x : FourSpace}
    (hf : ContDiffAt ℝ (k + 1) f x) (i : Fin 4) :
    ContDiffAt ℝ k (fun y => coordDeriv f i y) x :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem inverse_coefficient_contDiffAt (k : ℕ) (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff k g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ k (fun y => inverseMetricInChart g c y i j) x :=
  NativeLinearityArchiveLOCK24SYM.matrix_inv_coefficient_contDiffAt _ x k
    (tensor_coefficient_contDiffAt k g hg c x hx)
    (NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      g hm c x hx) i j

theorem christoffel_contDiffAt (k : ℕ) (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff (k + 1) g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (l i j : Fin 4) :
    ContDiffAt ℝ k (fun y => christoffelInChart g c y l i j) x := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro p _
  exact ((inverse_coefficient_contDiffAt (k + 1) g hm hg c x hx l p).of_le (by simp)).mul
    (((coordDeriv_contDiffAt k (tensor_coefficient_contDiffAt (k + 1) g hg c x hx j p) i).add
      (coordDeriv_contDiffAt k (tensor_coefficient_contDiffAt (k + 1) g hg c x hx i p) j)).sub
      (coordDeriv_contDiffAt k (tensor_coefficient_contDiffAt (k + 1) g hg c x hx i j) p))

theorem bianchiInChart_contDiffAt (k : ℕ) (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff (k + 1) g) (hu : Cov2ContDiff (k + 1) u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    ContDiffAt ℝ k (fun y => bianchiInChart g u c y j) x := by
  have htrace : ContDiffAt ℝ (k + 1) (metricTraceInChart g u c) x := by
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (inverse_coefficient_contDiffAt (k + 1) g hm hg c x hx a b).mul
      (tensor_coefficient_contDiffAt (k + 1) u hu c x hx a b)
  apply ContDiffAt.add
  · apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    apply ((inverse_coefficient_contDiffAt (k + 1) g hm hg c x hx a b).of_le (by simp)).mul
    apply ContDiffAt.sub
    · apply ContDiffAt.sub
      · exact coordDeriv_contDiffAt k (tensor_coefficient_contDiffAt (k + 1) u hu c x hx b j) a
      · apply ContDiffAt.sum
        intro p _
        exact (christoffel_contDiffAt k g hm hg c x hx p a b).mul
          ((tensor_coefficient_contDiffAt (k + 1) u hu c x hx p j).of_le (by simp))
    · apply ContDiffAt.sum
      intro p _
      exact (christoffel_contDiffAt k g hm hg c x hx p a j).mul
        ((tensor_coefficient_contDiffAt (k + 1) u hu c x hx b p).of_le (by simp))
  · exact contDiffAt_const.mul (coordDeriv_contDiffAt k htrace j)

theorem bianchi_contDiff (k : ℕ) (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff (k + 1) g) (hu : Cov2ContDiff (k + 1) u) :
    CovectorContDiff k (bianchi g u) := by
  have hg1 : Cov2ContDiff 1 g := fun c => (hg c).of_le (by simp)
  have hu1 : Cov2ContDiff 1 u := fun c => (hu c).of_le (by simp)
  intro c
  have hformula : ContDiffOn ℝ k (bianchiInChart g u c) (chartAt FourSpace c).target := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro j
    exact bianchiInChart_contDiffAt k g u hm hg hu c x hx j
  apply hformula.congr
  intro x hx
  exact (nativeBianchiDeltaStarChartRecovery M g hm hg1).1 u hu1 c x hx


end K24.Global.Holder20261026Operators.HigherRegularity

/- END Holder20261026.Operators.HigherRegularity -/

/- BEGIN Holder20261026.Operators.TensorOperatorRegularity -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal ENNReal

namespace K24.Global.Holder20261026Operators.TensorOperatorRegularity
open Holder20261026Lower

private theorem scalar_mul_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {alpha : ℝ≥0} {f g : E → ℝ} {x : E}
    (hf : LocallyAllHolder k alpha f x) (hg : LocallyAllHolder k alpha g x) :
    LocallyAllHolder k alpha (fun y => f y * g y) x := by
  simpa only [smul_eq_mul] using hf.smul hg

private theorem coordDeriv_germ {k : ℕ} {alpha : ℝ≥0} {f : FourSpace → ℝ} {x : FourSpace}
    (hf : LocallyAllHolder (k + 1) alpha f x) (i : Fin 4) :
    LocallyAllHolder k alpha (fun y => coordDeriv f i y) x :=
  hf.fderiv.clm (ContinuousLinearMap.apply ℝ ℝ (basisVector i))


private theorem scalar_prod_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {alpha : ℝ≥0} {x : E} {ι : Type*} (t : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ t, LocallyAllHolder k alpha (f i) x) :
    LocallyAllHolder k alpha (fun y => ∏ i ∈ t, f i y) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using LocallyAllHolder.const k alpha (1 : ℝ) x
  | @insert i t hi ih =>
    simpa only [Finset.prod_insert hi] using scalar_mul_germ
      (hf i (Finset.mem_insert_self i t)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem matrix_det_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {alpha : ℝ≥0} {x : E} (A : E → Mat4)
    (hA : ∀ i j, LocallyAllHolder k alpha (fun y => A y i j) x) :
    LocallyAllHolder k alpha (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply LocallyAllHolder.finset_sum Finset.univ
  intro σ _
  apply scalar_mul_germ (LocallyAllHolder.const k alpha _ x)
  exact scalar_prod_germ Finset.univ _ (fun i _ => hA (σ i) i)

                                                                                         
theorem reciprocal_germ (k : ℕ) (hk : 1 ≤ k) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    {f : FourSpace → ℝ} {x : FourSpace}
    (hf : LocallyAllHolder k alpha f x) (hn : f x ≠ 0) :
    LocallyAllHolder k alpha (fun y => (f y)⁻¹) x := by
  have hout : LocallyAllHolder k alpha (fun t : ℝ => t⁻¹) (f x) :=
    LocallyAllHolder.of_contDiffAt k alpha ha _ _ (contDiffAt_id.inv hn)
  exact hout.comp hf (hf.contDiffAt.of_le (by exact_mod_cast hk))

                                                                                      
theorem matrix_inv_germ (k : ℕ) (hk : 1 ≤ k) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, LocallyAllHolder k alpha (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (a b : Fin 4) :
    LocallyAllHolder k alpha (fun y => (A y)⁻¹ a b) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_apply]
  apply scalar_mul_germ
  · exact reciprocal_germ k hk alpha ha (matrix_det_germ A hA) hdet
  · apply matrix_det_germ
    intro i j
    by_cases hi : i = b
    · subst i
      simp only [Matrix.updateRow_self]
      exact LocallyAllHolder.const k alpha _ x
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem inverse_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g : RawCov2 M) (hm : IsMetric g) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target)
    (hgg : LocallyAllHolder (k + 1) alpha (cov2InChart g d) x) (i j : Fin 4) :
    LocallyAllHolder (k + 1) alpha (fun y => inverseMetricInChart g d y i j) x := by
  apply matrix_inv_germ (k + 1) (by omega) alpha ha
  · intro a b
    exact (hgg.clm (ContinuousLinearMap.proj a)).clm (ContinuousLinearMap.proj b)
  · exact NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      g hm d x hx

private theorem christoffel_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g : RawCov2 M) (hm : IsMetric g) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target)
    (hgg : LocallyAllHolder (k + 1) alpha (cov2InChart g d) x) (l i j : Fin 4) :
    LocallyAllHolder k alpha (fun y => christoffelInChart g d y l i j) x := by
  have hgc (i j : Fin 4) : LocallyAllHolder (k + 1) alpha
      (fun y => cov2InChart g d y i j) x :=
    (hgg.clm (ContinuousLinearMap.proj i)).clm (ContinuousLinearMap.proj j)
  apply scalar_mul_germ (LocallyAllHolder.const k alpha (1 / 2 : ℝ) x)
  apply LocallyAllHolder.finset_sum Finset.univ
  intro p _
  exact scalar_mul_germ ((inverse_germ k alpha ha g hm d x hx hgg l p).mono (by omega))
    (((coordDeriv_germ (hgc j p) i).add (coordDeriv_germ (hgc i p) j)).sub
      (coordDeriv_germ (hgc i j) p))

                                                                                  
                                                                              
theorem bianchi_native_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g u : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff 1 g)
    (hu : Cov2ContDiff (k + 1) u) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target)
    (hgg : LocallyAllHolder (k + 1) alpha (cov2InChart g d) x)
    (hug : LocallyAllHolder (k + 1) alpha (cov2InChart u d) x) :
    LocallyAllHolder k alpha (covectorInChart (bianchi g u) d) x := by
  have huc (i j : Fin 4) : LocallyAllHolder (k + 1) alpha
      (fun y => cov2InChart u d y i j) x :=
    (hug.clm (ContinuousLinearMap.proj i)).clm (ContinuousLinearMap.proj j)
  have htrace : LocallyAllHolder (k + 1) alpha (metricTraceInChart g u d) x := by
    apply LocallyAllHolder.finset_sum Finset.univ
    intro a _
    apply LocallyAllHolder.finset_sum Finset.univ
    intro b _
    exact scalar_mul_germ (inverse_germ k alpha ha g hm d x hx hgg a b) (huc a b)
  have hnabla (a b l : Fin 4) : LocallyAllHolder k alpha
      (fun y => nablaTensorInChart g u d y a b l) x := by
    have h1 : LocallyAllHolder k alpha (fun y => ∑ p : Fin 4,
        christoffelInChart g d y p a b * cov2InChart u d y p l) x := by
      apply LocallyAllHolder.finset_sum Finset.univ
      intro p _
      exact scalar_mul_germ (christoffel_germ k alpha ha g hm d x hx hgg p a b)
        ((huc p l).mono (by omega))
    have h2 : LocallyAllHolder k alpha (fun y => ∑ p : Fin 4,
        christoffelInChart g d y p a l * cov2InChart u d y b p) x := by
      apply LocallyAllHolder.finset_sum Finset.univ
      intro p _
      exact scalar_mul_germ (christoffel_germ k alpha ha g hm d x hx hgg p a l)
        ((huc b p).mono (by omega))
    exact ((coordDeriv_germ (huc b l) a).sub h1).sub h2
  have hformula : LocallyAllHolder k alpha (bianchiInChart g u d) x := by
    apply LocallyAllHolder.pi
    intro j
    have hdiv : LocallyAllHolder k alpha (fun y => ∑ a : Fin 4, ∑ b : Fin 4,
        inverseMetricInChart g d y a b * nablaTensorInChart g u d y a b j) x := by
      apply LocallyAllHolder.finset_sum Finset.univ
      intro a _
      apply LocallyAllHolder.finset_sum Finset.univ
      intro b _
      exact scalar_mul_germ ((inverse_germ k alpha ha g hm d x hx hgg a b).mono (by omega))
        (hnabla a b j)
    exact hdiv.neg.add (scalar_mul_germ (LocallyAllHolder.const k alpha (1 / 2 : ℝ) x)
      (coordDeriv_germ htrace j))
  apply hformula.congr
  filter_upwards [(chartAt FourSpace d).open_target.mem_nhds hx] with y hy
  symm
  exact (nativeBianchiDeltaStarChartRecovery M g hm hg).1 u
    (fun c => (hu c).of_le (by simp)) d y hy

section Global
variable [CompactSpace M]

                                                                                          
theorem bianchi_holder (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g u : RawCov2 M) (hg : MetricAdmissible C b g)
    (hu : C.Cov2Holder 2 b.exponent.value u) :
    C.CovectorHolder 1 b.exponent.value (bianchi g u) := by
  have ha : b.exponent.value ≤ 1 := b.exponent.lessThanOne.le
  have hgn := TensorDescent.metricAdmissible_native_two C b g hg
  have hun := TensorDescent.cov2Holder_native C 2 b.exponent.value u hu
  have hgh := pos_admissible_holder C b g hg 2 b.order_ge_two
  apply covectorHolder_of_native_germs C 1 b.exponent.value ha b.exponent.positive
  intro d x hx
  exact bianchi_native_germ 1 b.exponent.value ha g u hg.metric
    (fun c => (hgn c).of_le (by norm_num)) hun d x hx
    (cov2Holder_native_germ C 2 b.exponent.value ha g hgh d x hx)
    (cov2Holder_native_germ C 2 b.exponent.value ha u hu d x hx)

theorem bianchi_haarIntegrable (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (rho : CircleAction M) (g u : RawCov2 M) (hg : MetricAdmissible C b g)
    (hu : C.Cov2Holder 2 b.exponent.value u) :
    CovectorHaarIntegrable rho (bianchi g u) := by
  exact HaarSectors.covector_haar_integrable_of_continuous rho _
    (NativeContinuity.covector_evaluation_continuous _
      (HigherRegularity.bianchi_contDiff 1 g u hg.metric
        (TensorDescent.metricAdmissible_native_two C b g hg)
        (TensorDescent.cov2Holder_native C 2 b.exponent.value u hu)))

                                                                                     
theorem bianchi_regularity (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (rho : CircleAction M) (ghat z : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z) :
    ∀ u : RawCov2 M, C.Cov2Holder 2 b.exponent.value u →
      C.CovectorHolder 1 b.exponent.value (bianchi ghat u) ∧
      C.CovectorHolder 1 b.exponent.value (bianchi z u) ∧
      CovectorHaarIntegrable rho (bianchi ghat u) ∧
      CovectorHaarIntegrable rho (bianchi z u) := by
  intro u hu
  exact ⟨bianchi_holder C b ghat u hh hu, bianchi_holder C b z u hz hu,
    bianchi_haarIntegrable C b rho ghat u hh hu, bianchi_haarIntegrable C b rho z u hz hu⟩
end Global

end K24.Global.Holder20261026Operators.TensorOperatorRegularity
/- END Holder20261026.Operators.TensorOperatorRegularity -/

/- BEGIN Holder20261026.Operators.TensorOperatorRegularityDefect -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal ENNReal

namespace K24.Global.Holder20261026Operators.TensorOperatorRegularity
open Holder20261026Lower

private theorem mul_germ {k : ℕ} {alpha : ℝ≥0} {f g : FourSpace → ℝ} {x : FourSpace}
    (hf : LocallyAllHolder k alpha f x) (hg : LocallyAllHolder k alpha g x) :
    LocallyAllHolder k alpha (fun y => f y * g y) x := by
  simpa only [smul_eq_mul] using hf.smul hg

private theorem deriv_germ {alpha : ℝ≥0} {f : FourSpace → ℝ} {x : FourSpace}
    (hf : LocallyAllHolder 1 alpha f x) (i : Fin 4) :
    LocallyAllHolder 0 alpha (fun y => coordDeriv f i y) x :=
  hf.fderiv.clm (ContinuousLinearMap.apply ℝ ℝ (basisVector i))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

                                                                                           
theorem deltaStar_native_germ (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g : RawCov2 M) (eta : RawCovector M) (hm : IsMetric g) (hg : Cov2ContDiff 2 g)
    (heta : CovectorContDiff 1 eta) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target)
    (heg : LocallyAllHolder 1 alpha (covectorInChart eta d) x) :
    LocallyAllHolder 0 alpha (cov2InChart (deltaStar g eta) d) x := by
  have hec (j : Fin 4) : LocallyAllHolder 1 alpha (fun y => covectorInChart eta d y j) x :=
    heg.clm (ContinuousLinearMap.proj j)
  have hGamma (p i j : Fin 4) : LocallyAllHolder 0 alpha
      (fun y => christoffelInChart g d y p i j) x :=
    LocallyAllHolder.of_contDiffAt 0 alpha ha _ _
      (HigherRegularity.christoffel_contDiffAt 1 g hm hg d x hx p i j)
  have hnabla (i j : Fin 4) : LocallyAllHolder 0 alpha
      (fun y => nablaCovectorInChart g eta d y i j) x := by
    apply (deriv_germ (hec j) i).sub
    apply LocallyAllHolder.finset_sum Finset.univ
    intro p _
    exact mul_germ (hGamma p i j) ((hec p).mono (by omega))
  have hformula : LocallyAllHolder 0 alpha (deltaStarInChart g eta d) x := by
    apply LocallyAllHolder.pi
    intro i
    apply LocallyAllHolder.pi
    intro j
    exact mul_germ (LocallyAllHolder.const 0 alpha (1 / 2 : ℝ) x)
      ((hnabla i j).add (hnabla j i))
  apply hformula.congr
  filter_upwards [(chartAt FourSpace d).open_target.mem_nhds hx] with y hy
  symm
  exact (nativeBianchiDeltaStarChartRecovery M g hm
    (fun c => (hg c).of_le (by norm_num))).2 eta heta d y hy

section Global
variable [CompactSpace M]

                                                                                    
theorem deltaStar_holder (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (g : RawCov2 M) (hg : MetricAdmissible C b g)
    (eta : RawCovector M) (heta : C.CovectorHolder 1 b.exponent.value eta) :
    C.Cov2Holder 0 b.exponent.value (deltaStar g eta) := by
  have ha : b.exponent.value ≤ 1 := b.exponent.lessThanOne.le
  have hgn := TensorDescent.metricAdmissible_native_two C b g hg
  have hen := NativeRegularity.covectorContDiff_of_lifted_contDiff C 1 eta heta.1
  apply cov2Holder_of_native_germs C 0 b.exponent.value ha b.exponent.positive
  intro d x hx
  exact deltaStar_native_germ b.exponent.value ha g eta hg.metric hgn hen d x hx
    (covectorHolder_native_germ C 1 b.exponent.value ha eta heta d x hx)

                                                                                    
theorem tensorDefect_holder (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (ghat z : RawCov2 M) (hh : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z)
    (u : RawCov2 M) (hu : C.Cov2Holder 2 b.exponent.value u) :
    C.Cov2Holder 0 b.exponent.value (tensorDefect ghat z u) := by
  exact deltaStar_holder C b z hz _
    (HolderProjectionFinite.covectorHolder_sub C 1 b.exponent.value _ _
      (bianchi_holder C b ghat u hh hu) (bianchi_holder C b z u hz hu))

                                                                                    
theorem defect_regularity (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (ghat z : RawCov2 M) (hh : MetricAdmissible C b ghat) (hz : MetricAdmissible C b z) :
    ∀ u ∈ tensorHolderSpace C 2 b.exponent.value,
      C.Cov2Holder 0 b.exponent.value (tensorDefect ghat z u) := by
  intro u hu
  exact tensorDefect_holder C b ghat z hh hz u hu.2

end Global
end K24.Global.Holder20261026Operators.TensorOperatorRegularity
/- END Holder20261026.Operators.TensorOperatorRegularityDefect -/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators

def ActualHolderTensorRegularity : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M],
    ∀ (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
      (rho : CircleAction M) (ghat z : RawCov2 M),
      MetricAdmissible C b ghat → MetricAdmissible C b z →
      (∀ u : RawCov2 M, C.Cov2Holder 2 b.exponent.value u →
        C.CovectorHolder 1 b.exponent.value (bianchi ghat u) ∧
        C.CovectorHolder 1 b.exponent.value (bianchi z u) ∧
        CovectorHaarIntegrable rho (bianchi ghat u) ∧
        CovectorHaarIntegrable rho (bianchi z u)) ∧
      (∀ u ∈ tensorHolderSpace C 2 b.exponent.value,
        C.Cov2Holder 0 b.exponent.value (tensorDefect ghat z u))

end K24.Global.Holder20261026Operators

theorem solution : K24.Global.Holder20261026Operators.ActualHolderTensorRegularity.{u} := by
  intro M _ _ _ _ C b rho ghat z hh hz
  exact ⟨K24.Global.Holder20261026Operators.TensorOperatorRegularity.bianchi_regularity C b rho ghat z hh hz,
    K24.Global.Holder20261026Operators.TensorOperatorRegularity.defect_regularity C b ghat z hh hz⟩

set_option pp.universes true in
#check @solution
#print axioms solution
