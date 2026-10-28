-- Prove2me | solution 1 for K24.Global.actual_holder_vector_operators
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:34:45.458929+00:00
-- url     : https://prove2.me/submissions/3159f670-0169-45b7-bad0-481288106552

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

theorem derivativeENorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (alpha : ℝ≥0) (s : Set E) (f : E → V) :
    derivativeENorm j s f ≤ coordinateHolderENorm k alpha s f := by
  have hsum : derivativeENorm j s f ≤ ∑ l ∈ Finset.range (k+1), derivativeENorm l s f :=
    Finset.single_le_sum (f := fun l => derivativeENorm l s f) (fun _ _ => bot_le)
      (show j ∈ Finset.range (k+1) from Finset.mem_range.mpr (by omega))
  exact hsum.trans le_self_add

theorem jet_enorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (alpha : ℝ≥0) (s : Set E) (f : E → V) (x : E) (hx : x ∈ s) :
    ‖iteratedFDerivWithin ℝ j f s x‖ₑ ≤ coordinateHolderENorm k alpha s f := by
  exact (le_iSup (fun x : s => (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞)) ⟨x,hx⟩).trans
    (derivativeENorm_le_coordinateHolderENorm k j hj alpha s f)

theorem enorm_le_coordinateHolderENorm (k : ℕ) (alpha : ℝ≥0)
    (s : Set E) (f : E → V) (x : E) (hx : x ∈ s) :
    ‖f x‖ₑ ≤ coordinateHolderENorm k alpha s f := by
  have heq : ‖iteratedFDerivWithin ℝ 0 f s x‖ₑ = ‖f x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDerivWithin_zero]
  rw [← heq]
  exact jet_enorm_le_coordinateHolderENorm k 0 (Nat.zero_le k) alpha s f x hx

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



theorem coefficientsToCovector_eval_continuous (v : FourSpace) :
    Continuous (fun a : Fin 4 → ℝ => coefficientsToCovector a v) := by
  unfold coefficientsToCovector
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  fun_prop

theorem LocalCoverChart.covector_recover_eval {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u : RawCovector M) (x : FourSpace)
    (v : TangentSpace I4 (c.lift x)) :
    coefficientsToCovector (c.liftedCovector u x) ((c.tangentMap x).symm v) = u (c.lift x) v := by
  have h := coefficientsToCovector_recover ((u (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap)
  have h' := congrArg (fun a : FourSpace →L[ℝ] ℝ => a ((c.tangentMap x).symm v)) h
  change coefficientsToCovector (c.liftedCovector u x) ((c.tangentMap x).symm v) =
    u (c.lift x) ((c.tangentMap x) ((c.tangentMap x).symm v)) at h'
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h'





end K24.Global



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                           
                                                         
theorem covectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha eta}
      (C.covectorENorm k alpha) := by
  exact (vectorCovectorHolderBanachAllOrders C k alpha).1

theorem vectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha Y}
      (C.vectorENorm k alpha) := by
  exact (vectorCovectorHolderBanachAllOrders C k alpha).2


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

                                                                      
abbrev normedSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    NormedSpace ℝ h.submodule :=
  letI := h.normedAddCommGroup
  NormedSpace.ofCore h.normCore

theorem norm_eq_toReal (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ‖u‖ = (nx u).toReal := rfl

theorem ofReal_norm (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ENNReal.ofReal ‖u‖ = nx u :=
  ENNReal.ofReal_toReal (h.finite u u.property).ne

                                                                           
                                                                          
theorem completeSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    CompleteSpace h.submodule := by
  letI := h.normedAddCommGroup
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  obtain ⟨v, hv, hlim⟩ := h.complete (fun n => f n) (fun n => (f n).property) (by
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hij := hN i hi j hj
    rw [dist_eq_norm] at hij
    have hh := (ENNReal.ofReal_lt_ofReal_iff heps).mpr hij
    rwa [h.ofReal_norm (f i - f j)] at hh)
  refine ⟨⟨v, hv⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hlim eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  rw [h.ofReal_norm]
  exact hN i hi

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

                                                                            
                                                               
def boundedEvaluation {X V : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set X} {nx : X → ℝ≥0∞} (hS : SectionBanachSpace S nx)
    (L : X →ₗ[ℝ] V) (hb : ∀ u ∈ S, ‖L u‖ₑ ≤ nx u) (q : V →L[ℝ] ℝ) :
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := hS.normedSpace
    hS.submodule →L[ℝ] ℝ := by
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  let A : hS.submodule →ₗ[ℝ] ℝ := q.toLinearMap.comp (L.comp hS.submodule.subtype)
  apply A.mkContinuous ‖q‖
  intro u
  have hv : ‖L (u : X)‖ ≤ ‖u‖ := by
    change ‖L (u : X)‖ ≤ (nx u).toReal
    have hh := ENNReal.toReal_mono (hS.finite u u.property).ne (hb u u.property)
    simpa only [← ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg _)] using hh
  exact (q.le_opNorm (L u)).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg q))

def covectorCoefficientEvaluation (v : FourSpace) : (Fin 4 → ℝ) →L[ℝ] ℝ where
  toFun a := coefficientsToCovector a v
  map_add' a b := by
    simp [HaarSectors.coefficientsToCovector_apply,Finset.sum_add_distrib,add_mul,mul_add]
  map_smul' c a := by
    simp [HaarSectors.coefficientsToCovector_apply,Finset.mul_sum,mul_assoc,mul_left_comm]
  cont := coefficientsToCovector_eval_continuous v


variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                                    
theorem exists_covectorEvaluation (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (p : M) (v : TangentSpace I4 p) :
    let hS := covectorHolder_sectionBanach C k alpha
    letI := hS.normedAddCommGroup
    letI : TopologicalSpace hS.submodule :=
      hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := hS.normedSpace
    ∃ L : hS.submodule →L[ℝ] ℝ, ∀ u, L u = (u : RawCovector M) p v := by
  let hS := covectorHolder_sectionBanach C k alpha
  letI := hS.normedAddCommGroup
  letI : TopologicalSpace hS.submodule :=
    hS.normedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := hS.normedSpace
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  let c := C.chart nu
  let Lraw : RawCovector M →ₗ[ℝ] (Fin 4 → ℝ) :=
    { toFun := fun u => c.liftedCovector u x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb : ∀ u ∈ {u : RawCovector M | C.CovectorHolder k alpha u},
      ‖Lraw u‖ₑ ≤ C.covectorENorm k alpha u := by
    intro u _
    exact (enorm_le_coordinateHolderENorm k alpha c.innerDomain (c.liftedCovector u) x hx).trans
      (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCovector u)) nu)
  refine ⟨boundedEvaluation hS Lraw hb (covectorCoefficientEvaluation ((c.tangentMap x).symm v)),?_⟩
  intro u
  change coefficientsToCovector (c.liftedCovector (u : RawCovector M) x)
    ((c.tangentMap x).symm v) = (u : RawCovector M) (c.lift x) v
  exact c.covector_recover_eval u x v

                                                                                


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










theorem holder_projection_finite (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (order : ℕ) (rho : CircleAction M) (hact : HolderActionControl C α H order rho) :
    HolderProjectionConclusions C α H order rho := by
  exact holderHaarProjectionAllOrders C α H hα order rho hact

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

/- BEGIN Holder20261026.Operators.ClosedGraph -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology

namespace K24.Global.Holder20261026Operators

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

theorem exists_scalarBoundedLinearMap {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    {U : Set Z} {nz : Z → ℝ≥0∞} (hU : SectionBanachSpace U nz)
    (L : hU.submodule →ₗ[ℝ] ℝ) (D : ℝ≥0)
    (hb : ∀ u : hU.submodule, ‖L u‖ₑ ≤ (D : ℝ≥0∞) * nz u) :
    letI := hU.normedAddCommGroup
    letI := hU.normedSpace
    ∃ LC : hU.submodule →L[ℝ] ℝ, ∀ u, LC u = L u := by
  letI := hU.normedAddCommGroup
  letI := hU.normedSpace
  refine ⟨L.mkContinuous D (fun u => ?_), fun _ => rfl⟩
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hU.finite u u.property).ne) (hb u)
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_mul, ENNReal.coe_toReal, hU.norm_eq_toReal] using h

                                                                            
                                                                            
theorem sectionBoundedOn_of_scalar_observations
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    (A : X → Y) (hAT : Set.MapsTo A S T) (hAL : SectionLinearOn S A)
    {I : Type*} (eval : I → Y →ₗ[ℝ] ℝ)
    (hsep : ∀ v w : Y, (∀ i, eval i v = eval i w) → v = w)
    (hsource : ∀ i, SectionBoundedOn S nx (fun r : ℝ => ‖r‖ₑ) (fun u => eval i (A u)))
    (htarget : ∀ i, SectionBoundedOn T ny (fun r : ℝ => ‖r‖ₑ) (eval i)) :
    SectionBoundedOn S nx ny A := by
  letI := hS.normedAddCommGroup
  letI := hS.normedSpace
  letI := hS.completeSpace
  letI := hT.normedAddCommGroup
  letI := hT.normedSpace
  letI := hT.completeSpace
  let a : hS.submodule →ₗ[ℝ] hT.submodule :=
    { toFun := fun u => ⟨A u, hAT u.property⟩
      map_add' := fun u v => Subtype.ext (hAL.2.1 u u.property v v.property)
      map_smul' := fun c u => Subtype.ext (hAL.2.2 c u u.property) }
  have hs (i : I) : ∃ L : hS.submodule →L[ℝ] ℝ,
      ∀ u, L u = eval i (A u) := by
    obtain ⟨D, hD⟩ := hsource i
    let L := (eval i).comp (hT.submodule.subtype.comp a)
    exact exists_scalarBoundedLinearMap (nz := nx) hS L D (fun u => by
      change ‖eval i (A (u : X))‖ₑ ≤ (D : ℝ≥0∞) * nx u
      exact hD u u.property)
  have ht (i : I) : ∃ L : hT.submodule →L[ℝ] ℝ,
      ∀ u, L u = eval i u := by
    obtain ⟨D, hD⟩ := htarget i
    exact exists_scalarBoundedLinearMap (nz := ny) hT ((eval i).comp hT.submodule.subtype) D
      (fun u => by
        change ‖eval i (u : Y)‖ₑ ≤ (D : ℝ≥0∞) * ny u
        exact hD u u.property)
  have hc : Continuous a := by
    apply a.continuous_of_seq_closed_graph
    intro f u v hf hfa
    apply Subtype.ext
    apply hsep
    intro i
    obtain ⟨LS, hLS⟩ := hs i
    obtain ⟨LT, hLT⟩ := ht i
    have hsconv := LS.continuous.continuousAt.tendsto.comp hf
    have htconv := LT.continuous.continuousAt.tendsto.comp hfa
    have heq : (LT ∘ (a ∘ f)) = (LS ∘ f) := by
      funext n
      simp only [Function.comp_apply, hLS, hLT]
      rfl
    rw [heq] at htconv
    have he := tendsto_nhds_unique htconv hsconv
    change eval i (v : Y) = eval i (A u)
    simpa only [hLS, hLT] using he
  let ac : hS.submodule →L[ℝ] hT.submodule := ⟨a, hc⟩
  refine ⟨‖ac‖₊, fun u hu => ?_⟩
  have hb := ac.le_opNorm (⟨u, hu⟩ : hS.submodule)
  have hb' := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (norm_nonneg _), hT.ofReal_norm, hS.ofReal_norm] at hb'
  change ny (A u) ≤ ENNReal.ofReal ‖ac‖ * nx u at hb'
  simpa only [ofReal_norm, enorm_eq_nnnorm] using hb'

end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.ClosedGraph -/

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


lemma vector_coord_lift (c : LocalCoverChart F) (Y : RawVector M) (d : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hd : c.lift x ∈ (chartAt FourSpace d).source) :
    vectorInChart Y d (chartAt FourSpace d (c.lift x)) =
      fderiv ℝ ((chartAt FourSpace d) ∘ c.lift) x (c.liftedVector Y x) := by
  rw [← frame_eq_fderiv c d x hx hd]
  rw [ContinuousLinearEquiv.coe_coe, frame_apply]
  dsimp only [vectorInChart, LocalCoverChart.liftedVector]
  erw [(chartAt FourSpace d).left_inv hd, ContinuousLinearEquiv.apply_symm_apply]




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

                                                                            
                                                                             
                                
theorem vectorHolder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (Y : RawVector M)
    (hY : C.VectorHolder m alpha Y) : C.VectorHolder j alpha Y := by
  exact (fixed_cover_holder_lowering M C m j hjm alpha ha).1 Y hY



theorem cov2Holder_lower (C : BoundedLocalCover M) (m j : ℕ) (hjm : j ≤ m)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (u : RawCov2 M)
    (hu : C.Cov2Holder m alpha u) : C.Cov2Holder j alpha u := by
  exact (fixed_cover_holder_lowering M C m j hjm alpha ha).2.2.1 u hu

end K24.Global.Holder20261026Lower
/- END Holder20261026Lower.LowerFiniteness -/

/- BEGIN Holder20261026.Operators.LowerBounds -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open Filter
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.Holder20261026Operators

theorem scalarBoundedOn_of_continuousLinearMap
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    {S : Set X} {nx : X → ℝ≥0∞} (hS : SectionBanachSpace S nx)
    (A : X → ℝ)
    (he : letI := hS.normedAddCommGroup
      letI := hS.normedSpace
      ∃ L : hS.submodule →L[ℝ] ℝ, ∀ u, L u = A u) :
    SectionBoundedOn S nx (fun r : ℝ => ‖r‖ₑ) A := by
  letI := hS.normedAddCommGroup
  letI := hS.normedSpace
  obtain ⟨L, hL⟩ := he
  refine ⟨‖L‖₊, fun u hu => ?_⟩
  have hb := ENNReal.ofReal_le_ofReal (L.le_opNorm (⟨u, hu⟩ : hS.submodule))
  rw [ENNReal.ofReal_mul (norm_nonneg _), hS.ofReal_norm] at hb
  simpa only [hL, ofReal_norm, enorm_eq_nnnorm] using hb

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def covectorEvaluation (q : Σ p : M, TangentSpace I4 p) : RawCovector M →ₗ[ℝ] ℝ where
  toFun u := u q.1 q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



theorem covectorEvaluation_bounded (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (q : Σ p : M, TangentSpace I4 p) :
    SectionBoundedOn {u : RawCovector M | C.CovectorHolder k alpha u}
      (C.covectorENorm k alpha) (fun r : ℝ => ‖r‖ₑ) (covectorEvaluation q) := by
  apply scalarBoundedOn_of_continuousLinearMap (covectorHolder_sectionBanach C k alpha)
  exact HolderPerpAll.exists_covectorEvaluation C k alpha q.1 q.2



variable [IsManifold I4 ∞ M] [CompactSpace M]

                                                                              
                                                                                



end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.LowerBounds -/

/- BEGIN Holder20261026.Operators.ArchiveREG -/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global.NativeLinearityArchiveREGK24REG

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

                                                                            
theorem coordDeriv_contDiffOn {s : Set FourSpace} (hs : IsOpen s)
    (f : FourSpace → ℝ) (hf : ContDiffOn ℝ 2 f s) (i : Fin 4) :
    ContDiffOn ℝ 1 (fun x => coordDeriv f i x) s := by
  exact (hf.fderiv_of_isOpen hs (by norm_num)).clm_apply contDiffOn_const

                                                                       
theorem cov2_coefficient_contDiffOn (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (c : M) (i j : Fin 4) :
    ContDiffOn ℝ 2 (fun x => cov2InChart g c x i j) (chartAt FourSpace c).target := by
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) j

                                                                       
theorem vector_coefficient_contDiffOn (Y : RawVector M) (hY : VectorContDiff 2 Y)
    (c : M) (p : Fin 4) :
    ContDiffOn ℝ 2 (fun x => vectorInChart Y c x p) (chartAt FourSpace c).target := by
  exact (coordProj p).contDiff.comp_contDiffOn (hY c)

                                                                                
theorem lieTensorInChart_contDiffOn (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) (c : M) :
    ContDiffOn ℝ 1 (lieTensorInChart Y g c) (chartAt FourSpace c).target := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply ContDiffOn.sum
  intro p _
  have hgij := cov2_coefficient_contDiffOn g hg c i j
  have hgpj := cov2_coefficient_contDiffOn g hg c p j
  have hgip := cov2_coefficient_contDiffOn g hg c i p
  have hYp := vector_coefficient_contDiffOn Y hY c p
  have hopen := (chartAt FourSpace c).open_target
  exact (((hYp.of_le (by norm_num)).mul (coordDeriv_contDiffOn hopen _ hgij p)).add
    ((coordDeriv_contDiffOn hopen _ hYp i).mul (hgpj.of_le (by norm_num)))).add
      ((coordDeriv_contDiffOn hopen _ hYp j).mul (hgip.of_le (by norm_num)))


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

                                                                 
def chartTransitionDerivative (c d : M) (x : FourSpace) : FourSpace →L[ℝ] FourSpace :=
  (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm x)).comp
    (mfderiv I4 I4 (chartAt FourSpace c).symm x)

@[simp] theorem matrixToBilinear_basis (A : Mat4) (i j : Fin 4) :
    matrixToBilinear A (basisVector i) (basisVector j) = A i j := by
  simp [matrixToBilinear, basisVector, coordProj, Pi.single_apply]

                                                                           
theorem cov2InChart_fixed_reconstruction (c : M) (A : FourSpace → Mat4)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (fun p => cov2FromChartAt c p (A (chartAt FourSpace c p))) c x = A x := by
  have hdi : ∀ v : FourSpace,
      mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
        (mfderiv I4 I4 (chartAt FourSpace c).symm x v) = v := by
    intro v
    exact congrArg (fun D => D v) ((mdifferentiable_chart (I := I4) c).comp_symm_deriv hx)
  ext i j
  change matrixToBilinear (A ((chartAt FourSpace c) ((chartAt FourSpace c).symm x)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i)))
    (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))) = A x i j
  rw [hdi, hdi, (chartAt FourSpace c).right_inv hx, matrixToBilinear_basis]

                                                                                   
theorem cov2InChart_transition (u : RawCov2 M) (c d : M) (x : FourSpace)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    matrixToBilinear (cov2InChart u c x) =
      bilinearPullback
        (matrixToBilinear (cov2InChart u d
          (chartAt FourSpace d ((chartAt FourSpace c).symm x))))
        (chartTransitionDerivative c d x) := by
  let p := (chartAt FourSpace c).symm x
  let dc : FourSpace →L[ℝ] TangentSpace I4 p := mfderiv I4 I4 (chartAt FourSpace c).symm x
  have hr := cov2_chart_recovery u d p hd
  have hrec := matrixToBilinear_recover (bilinearPullback (u p) dc)
  change matrixToBilinear (fun i j => u p (dc (basisVector i)) (dc (basisVector j))) = _
  erw [hrec]
  ext v w
  have h := congrArg (fun B => B (dc v) (dc w)) hr
  exact h.symm

                                                                                      
def Cov2CoordinateCompatible (A : M → FourSpace → Mat4) : Prop :=
  ∀ (c d p : M), p ∈ (chartAt FourSpace c).source →
    p ∈ (chartAt FourSpace d).source →
    matrixToBilinear (A c (chartAt FourSpace c p)) =
      bilinearPullback (matrixToBilinear (A d (chartAt FourSpace d p)))
        (chartTransitionDerivative c d (chartAt FourSpace c p))

                                                                                    
theorem compatible_reconstructions (A : M → FourSpace → Mat4)
    (hA : Cov2CoordinateCompatible A) (c d p : M)
    (hc : p ∈ (chartAt FourSpace c).source)
    (hd : p ∈ (chartAt FourSpace d).source) :
    cov2FromChartAt c p (A c (chartAt FourSpace c p)) =
      cov2FromChartAt d p (A d (chartAt FourSpace d p)) := by
  have hdi : ∀ v : TangentSpace I4 p,
      mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p v) = v := by
    intro v
    exact congrArg (fun D => D v) ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hc)
  have hcomp := hA c d p hc hd
  ext v w
  change matrixToBilinear (A c (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c) p v)
      (mfderiv I4 I4 (chartAt FourSpace c) p w) = _
  rw [hcomp]
  change matrixToBilinear (A d (chartAt FourSpace d p))
    (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p v)))
    (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm (chartAt FourSpace c p))
      (mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
        (mfderiv I4 I4 (chartAt FourSpace c) p w))) = _
  rw [hdi, hdi, (chartAt FourSpace c).left_inv hc]
  rfl

                                                                                          
theorem cov2InChart_reconstruction (A : M → FourSpace → Mat4)
    (hA : Cov2CoordinateCompatible A) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) :
    cov2InChart (cov2FromCoordinates A) c x = A c x := by
  have hp : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target hx
  have hrec := compatible_reconstructions A hA c ((chartAt FourSpace c).symm x)
    ((chartAt FourSpace c).symm x) hp (mem_chart_source FourSpace _)
  have hlocal := cov2InChart_fixed_reconstruction c (A c) x hx
  ext i j
  change cov2FromChartAt ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)
    (A ((chartAt FourSpace c).symm x)
      (chartAt FourSpace ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm x)))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j)) = A c x i j
  rw [← hrec]
  exact congrArg (fun B => B i j) hlocal

                                                                                        
theorem cov2FromCoordinates_contDiff (A : M → FourSpace → Mat4)
    (hA : Cov2CoordinateCompatible A) (k : ℕ∞ω)
    (hregular : ∀ c : M, ContDiffOn ℝ k (A c) (chartAt FourSpace c).target) :
    Cov2ContDiff k (cov2FromCoordinates A) := by
  intro c
  apply (hregular c).congr
  intro x hx
  exact cov2InChart_reconstruction A hA c x hx

                                                                                
theorem lieTensor_contDiff_of_compatible (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y)
    (hcompat : Cov2CoordinateCompatible (lieTensorInChart Y g)) :
    Cov2ContDiff 1 (lieTensor Y g) := by
  exact cov2FromCoordinates_contDiff (lieTensorInChart Y g) hcompat 1
    (lieTensorInChart_contDiffOn g Y hg hY)


end K24.Global.NativeLinearityArchiveREGK24REG


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise Topology

namespace K24.Global.NativeLinearityArchiveREGK24REG

abbrev Bilinear4 := FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)

                                                                              
def lieBilinearEval (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) : ℝ :=
  fderiv ℝ (fun y => Q y a b) x (V x) +
    Q x (fderiv ℝ V x a) b + Q x a (fderiv ℝ V x b)

theorem fderiv_bilinear_eval (Q : FourSpace → Bilinear4) (x a b v : FourSpace)
    (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y => Q y a b) x v = fderiv ℝ Q x v a b := by
  have h := (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).clm_apply
    (hasFDerivAt_const b x)
  rw [h.fderiv]
  simp

                                                                                           
theorem fderiv_bilinear_pullback_eval
    (F : FourSpace → FourSpace) (Q : FourSpace → Bilinear4)
    (x a b v : FourSpace)
    (hF : DifferentiableAt ℝ F x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hQ : DifferentiableAt ℝ Q (F x)) :
    fderiv ℝ (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y) a b) x v =
      fderiv ℝ Q (F x) (fderiv ℝ F x v) (fderiv ℝ F x a) (fderiv ℝ F x b) +
      Q (F x) (fderiv ℝ (fderiv ℝ F) x v a) (fderiv ℝ F x b) +
      Q (F x) (fderiv ℝ F x a) (fderiv ℝ (fderiv ℝ F) x v b) := by
  have ha := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const a x)
  have hb := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
  have hQF : HasFDerivAt (fun y => Q (F y))
      ((fderiv ℝ Q (F x)).comp (fderiv ℝ F x)) x :=
    by simpa only [Function.comp_def] using
      (HasFDerivAt.comp x (f := F) (g := Q) hQ.hasFDerivAt hF.hasFDerivAt)
  have h := (hQF.clm_apply ha).clm_apply hb
  change fderiv ℝ (fun y => Q (F y) (fderiv ℝ F y a) (fderiv ℝ F y b)) x v = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.comp_zero, map_add]
  ring

                                                                                       
theorem vector_relation_derivative
    (F V W : FourSpace → FourSpace) (x a : FourSpace)
    (hF : DifferentiableAt ℝ F x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hV : DifferentiableAt ℝ V (F x)) (hW : DifferentiableAt ℝ W x)
    (hrel : (fun y => V (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (W y))) :
    fderiv ℝ V (F x) (fderiv ℝ F x a) =
      fderiv ℝ F x (fderiv ℝ W x a) + fderiv ℝ (fderiv ℝ F) x a (W x) := by
  have h := hrel.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x hV hF, fderiv_clm_apply hJ hW] at h
  exact congrArg (fun D => D a) h

                                                                               
                                                                         
theorem lieBilinearEval_pullback
    (F V W : FourSpace → FourSpace) (Q : FourSpace → Bilinear4)
    (x a b : FourSpace)
    (hF : DifferentiableAt ℝ F x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hQ : DifferentiableAt ℝ Q (F x))
    (hV : DifferentiableAt ℝ V (F x)) (hW : DifferentiableAt ℝ W x)
    (hsymm : IsSymmSndFDerivAt ℝ F x)
    (hrel : (fun y => V (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (W y))) :
    lieBilinearEval (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y)) W x a b =
      lieBilinearEval Q V (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) := by
  have hxrel := hrel.eq_of_nhds
  have ha := vector_relation_derivative F V W x a hF hJ hV hW hrel
  have hb := vector_relation_derivative F V W x b hF hJ hV hW hrel
  unfold lieBilinearEval
  rw [fderiv_bilinear_pullback_eval F Q x a b (W x) hF hJ hQ,
    fderiv_bilinear_eval Q (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) (V (F x)) hQ]
  rw [hxrel, ha, hb, hsymm a (W x), hsymm b (W x)]
  simp only [bilinearPullback_apply, map_add, ContinuousLinearMap.add_apply]
  ring

                                                                                  
theorem lieBilinearEval_pullback_of_contDiff
    (F V W : FourSpace → FourSpace) (Q : FourSpace → Bilinear4)
    (x a b : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hQ : DifferentiableAt ℝ Q (F x))
    (hV : DifferentiableAt ℝ V (F x)) (hW : DifferentiableAt ℝ W x)
    (hrel : (fun y => V (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (W y))) :
    lieBilinearEval (fun y => bilinearPullback (Q (F y)) (fderiv ℝ F y)) W x a b =
      lieBilinearEval Q V (F x) (fderiv ℝ F x a) (fderiv ℝ F x b) := by
  exact lieBilinearEval_pullback F V W Q x a b
    (hF.differentiableAt (by norm_num))
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    hQ hV hW (hF.isSymmSndFDerivAt (by norm_num)) hrel


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

theorem matrixToBilinear_sum (A : Mat4) :
    matrixToBilinear A = ∑ i, ∑ j, A i j • (coordProj i).smulRight (coordProj j) := by
  ext v w
  simp [matrixToBilinear, mul_assoc, mul_comm, mul_left_comm]

theorem matrixToBilinear_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    DifferentiableAt ℝ (fun y => matrixToBilinear (A y)) x := by
  simp_rw [matrixToBilinear_sum]
  exact DifferentiableAt.fun_sum (𝕜 := ℝ) (E := FourSpace) (F := Bilinear4)
    (fun i _ => DifferentiableAt.fun_sum (𝕜 := ℝ) (E := FourSpace) (F := Bilinear4)
      (fun j _ => (hA i j).smul_const ((coordProj i).smulRight (coordProj j))))

theorem fderiv_vector_coefficient (V : FourSpace → FourSpace) (x v : FourSpace)
    (hV : DifferentiableAt ℝ V x) (p : Fin 4) :
    fderiv ℝ (fun y => V y p) x v = fderiv ℝ V x v p := by
  have h := (hasFDerivAt_const (coordProj p) x).clm_apply hV.hasFDerivAt
  change fderiv ℝ (fun y => (coordProj p) (V y)) x v = _
  rw [h.fderiv]
  simp [coordProj]

                                                                            
def lieBilinear (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x : FourSpace) : Bilinear4 :=
  fderiv ℝ Q x (V x) + (Q x).comp (fderiv ℝ V x) +
    (ContinuousLinearMap.precomp ℝ (fderiv ℝ V x)).comp (Q x)

theorem lieBilinear_apply (Q : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) (hQ : DifferentiableAt ℝ Q x) :
    lieBilinear Q V x a b = lieBilinearEval Q V x a b := by
  rw [lieBilinearEval, fderiv_bilinear_eval Q x a b (V x) hQ]
  rfl

                                                                                              
theorem lieTensorInChart_eq_bilinear (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x)
    (hY : DifferentiableAt ℝ (vectorInChart Y c) x) :
    matrixToBilinear (lieTensorInChart Y g c x) =
      lieBilinear (fun y => matrixToBilinear (cov2InChart g c y)) (vectorInChart Y c) x := by
  have hQ := matrixToBilinear_differentiableAt _ x hg
  rw [← matrixToBilinear_recover (lieBilinear
    (fun y => matrixToBilinear (cov2InChart g c y)) (vectorInChart Y c) x)]
  apply congrArg matrixToBilinear
  ext i j
  rw [lieBilinear_apply _ _ x _ _ hQ]
  unfold lieBilinearEval
  simp only [matrixToBilinear_basis]
  have hfirst : fderiv ℝ (fun y => cov2InChart g c y i j) x (vectorInChart Y c x) =
      ∑ p, vectorInChart Y c x p * coordDeriv (fun y => cov2InChart g c y i j) p x := by
    conv_lhs => rw [← sum_basisVector (vectorInChart Y c x)]
    simp [coordDeriv, map_sum]
  rw [hfirst]
  have hsecond : matrixToBilinear (cov2InChart g c x)
      (fderiv ℝ (vectorInChart Y c) x (basisVector i)) (basisVector j) =
      ∑ p, coordDeriv (fun y => vectorInChart Y c y p) i x * cov2InChart g c x p j := by
    conv_lhs => rw [← sum_basisVector (fderiv ℝ (vectorInChart Y c) x (basisVector i))]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, matrixToBilinear_basis]
    apply Finset.sum_congr rfl
    intro p _
    rw [coordDeriv, fderiv_vector_coefficient _ x _ hY p]
  have hthird : matrixToBilinear (cov2InChart g c x) (basisVector i)
      (fderiv ℝ (vectorInChart Y c) x (basisVector j)) =
      ∑ p, coordDeriv (fun y => vectorInChart Y c y p) j x * cov2InChart g c x i p := by
    conv_lhs => rw [← sum_basisVector (fderiv ℝ (vectorInChart Y c) x (basisVector j))]
    simp only [map_sum, map_smul, smul_eq_mul, matrixToBilinear_basis]
    apply Finset.sum_congr rfl
    intro p _
    rw [coordDeriv, fderiv_vector_coefficient _ x _ hY p]
  rw [hsecond, hthird]
  simp [lieTensorInChart, Finset.sum_add_distrib]

                                                                                       
theorem lieBilinearEval_congr (Q R : FourSpace → Bilinear4) (V : FourSpace → FourSpace)
    (x a b : FourSpace) (hQR : Q =ᶠ[𝓝 x] R) :
    lieBilinearEval Q V x a b = lieBilinearEval R V x a b := by
  unfold lieBilinearEval
  have hscalar : (fun y => Q y a b) =ᶠ[𝓝 x] (fun y => R y a b) :=
    hQR.mono fun y hy => congrArg (fun B => B a b) hy
  rw [hscalar.fderiv_eq, hQR.eq_of_nhds]


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

theorem chartTransitionDerivative_eq_fderiv (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    chartTransitionDerivative c d x =
      fderiv ℝ (fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)) x := by
  have h := mfderiv_comp x
    ((mdifferentiable_chart (I := I4) d).mdifferentiableAt hd)
    ((mdifferentiable_chart (I := I4) c).mdifferentiableAt_symm hx)
  simpa only [mfderiv_eq_fderiv, Function.comp_def, chartTransitionDerivative] using h.symm

theorem chartTransition_contDiffAt (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 2 (fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)) x := by
  have hc : ContMDiffAt I4 I4 2 (chartAt FourSpace c).symm x :=
    (contMDiffOn_chart_symm (I := I4) (n := 2) (x := c)).contMDiffAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hd' : ContMDiffAt I4 I4 2 (chartAt FourSpace d) ((chartAt FourSpace c).symm x) :=
    (contMDiffOn_chart (I := I4) (n := 2) (x := d)).contMDiffAt
      ((chartAt FourSpace d).open_source.mem_nhds hd)
  simpa only [Function.comp_def] using (hd'.comp x hc).contDiffAt

                                                                                   
theorem vectorInChart_transition (Y : RawVector M) (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    vectorInChart Y d (chartAt FourSpace d ((chartAt FourSpace c).symm x)) =
      chartTransitionDerivative c d x (vectorInChart Y c x) := by
  let p := (chartAt FourSpace c).symm x
  have hdi : ∀ v : TangentSpace I4 p,
      mfderiv I4 I4 (chartAt FourSpace c).symm x
        (mfderiv I4 I4 (chartAt FourSpace c) p v) = v := by
    intro v
    have h := congrArg (fun D => D v)
      ((mdifferentiable_chart (I := I4) c).symm_comp_deriv
        ((chartAt FourSpace c).map_target hx))
    change mfderiv I4 I4 (chartAt FourSpace c).symm
      (chartAt FourSpace c ((chartAt FourSpace c).symm x))
      (mfderiv I4 I4 (chartAt FourSpace c) p v) = v at h
    rw [(chartAt FourSpace c).right_inv hx] at h
    exact h
  change mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace d).symm (chartAt FourSpace d p))
    (Y ((chartAt FourSpace d).symm (chartAt FourSpace d p))) =
    mfderiv I4 I4 (chartAt FourSpace d) p
      (mfderiv I4 I4 (chartAt FourSpace c).symm x
        (mfderiv I4 I4 (chartAt FourSpace c) p (Y p)))
  rw [(chartAt FourSpace d).left_inv hd, hdi]

                                                                            
theorem lieTensorInChart_transition (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y)
    (c d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm x ∈ (chartAt FourSpace d).source) :
    matrixToBilinear (lieTensorInChart Y g c x) =
      bilinearPullback (matrixToBilinear (lieTensorInChart Y g d
        (chartAt FourSpace d ((chartAt FourSpace c).symm x))))
        (chartTransitionDerivative c d x) := by
  let F : FourSpace → FourSpace := fun y => chartAt FourSpace d ((chartAt FourSpace c).symm y)
  let Qc : FourSpace → Bilinear4 := fun y => matrixToBilinear (cov2InChart g c y)
  let Qd : FourSpace → Bilinear4 := fun y => matrixToBilinear (cov2InChart g d y)
  let Vc := vectorInChart Y c
  let Vd := vectorInChart Y d
  have hdx : F x ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hd
  have hgc : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g c y i j) x := by
    intro i j
    exact ((cov2_coefficient_contDiffOn g hg c i j).differentiableOn (by norm_num) x hx).differentiableAt ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hgd : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart g d y i j) (F x) := by
    intro i j
    exact ((cov2_coefficient_contDiffOn g hg d i j).differentiableOn (by norm_num) (F x) hdx).differentiableAt ((chartAt FourSpace d).open_target.mem_nhds hdx)
  have hVc : DifferentiableAt ℝ Vc x :=
    ((hY c).differentiableOn (by norm_num) x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hVd : DifferentiableAt ℝ Vd (F x) :=
    ((hY d).differentiableOn (by norm_num) (F x) hdx).differentiableAt
      ((chartAt FourSpace d).open_target.mem_nhds hdx)
  have hQc : DifferentiableAt ℝ Qc x := matrixToBilinear_differentiableAt _ x hgc
  have hQd : DifferentiableAt ℝ Qd (F x) := matrixToBilinear_differentiableAt _ (F x) hgd
  have hnear : ∀ᶠ y in 𝓝 x,
      y ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm y ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).symm.trans (chartAt FourSpace d)).open_source.mem_nhds ⟨hx, hd⟩
  have hQrel : Qc =ᶠ[𝓝 x] (fun y => bilinearPullback (Qd (F y)) (fderiv ℝ F y)) := by
    filter_upwards [hnear] with y hy
    exact (cov2InChart_transition g c d y hy.2).trans
      (congrArg (bilinearPullback (Qd (F y)))
        (chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  have hVrel : (fun y => Vd (F y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y (Vc y)) := by
    filter_upwards [hnear] with y hy
    exact (vectorInChart_transition Y c d y hy.1 hy.2).trans
      (congrArg (fun D => D (Vc y))
        (chartTransitionDerivative_eq_fderiv c d y hy.1 hy.2))
  rw [lieTensorInChart_eq_bilinear g Y c x hgc hVc,
    lieTensorInChart_eq_bilinear g Y d (F x) hgd hVd,
    chartTransitionDerivative_eq_fderiv c d x hx hd]
  ext a b
  change lieBilinear Qc Vc x a b =
    lieBilinear Qd Vd (F x) (fderiv ℝ F x a) (fderiv ℝ F x b)
  rw [lieBilinear_apply _ _ x a b hQc,
    lieBilinear_apply _ _ (F x) _ _ hQd,
    lieBilinearEval_congr Qc _ Vc x a b hQrel]
  exact lieBilinearEval_pullback_of_contDiff F Vd Vc Qd x a b
    (chartTransition_contDiffAt c d x hx hd) hQd hVd hVc hVrel

                                                                           
theorem lieTensor_contDiff (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) :
    Cov2ContDiff 1 (lieTensor Y g) := by
  apply lieTensor_contDiff_of_compatible g Y hg hY
  intro c d p hc hd
  have h := lieTensorInChart_transition g Y hg hY c d (chartAt FourSpace c p)
    ((chartAt FourSpace c).map_source hc) (by simpa only [(chartAt FourSpace c).left_inv hc] using hd)
  simpa only [(chartAt FourSpace c).left_inv hc] using h


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





theorem matrix_det_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ a b, DifferentiableAt ℝ (fun y => A y a b) x) :
    DifferentiableAt ℝ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  exact (HasFDerivAt.finsetProd (fun i _ => (hA (σ i) i).hasFDerivAt)).differentiableAt

theorem matrix_inv_coefficient_differentiableAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ a b, DifferentiableAt ℝ (fun y => A y a b) x)
    (hdet : (A x).det ≠ 0) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹ a b) x := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_apply]
  apply DifferentiableAt.mul
  · exact (matrix_det_differentiableAt A x hA).inv hdet
  · apply matrix_det_differentiableAt
    intro i j
    by_cases hi : i = b
    · subst i
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j

theorem cov2_coefficients_differentiableAt (u : RawCov2 M)
    (hu : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x := by
  have hmatrix : DifferentiableAt ℝ (cov2InChart u c) x :=
    ((hu c).differentiableOn_one x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx)
  exact (differentiableAt_apply b _).comp x ((differentiableAt_apply a _).comp x hmatrix)

theorem metricTraceInChart_differentiableAt (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ a b, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y a b) x)
    (hu : ∀ a b, DifferentiableAt ℝ (fun y => cov2InChart u c y a b) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (hg a b).mul (hu a b)

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

theorem cov2FromCoordinates_add (a b : M → FourSpace → Mat4) :
    cov2FromCoordinates (fun c x i j => a c x i j + b c x i j) =
      cov2FromCoordinates a + cov2FromCoordinates b := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear,
    add_mul, mul_add, Finset.sum_add_distrib]

theorem cov2FromCoordinates_smul (r : ℝ) (a : M → FourSpace → Mat4) :
    cov2FromCoordinates (fun c x i j => r * a c x i j) =
      r • cov2FromCoordinates a := by
  ext p v w
  simp [cov2FromCoordinates, cov2FromChartAt, matrixToBilinear,
    mul_assoc, Finset.mul_sum, mul_left_comm]

theorem covectorFromCoordinates_add (a b : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (fun c x i => a c x i + b c x i) =
      covectorFromCoordinates a + covectorFromCoordinates b := by
  ext p v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    add_mul, Finset.sum_add_distrib]

theorem covectorFromCoordinates_smul (r : ℝ) (a : M → FourSpace → Fin 4 → ℝ) :
    covectorFromCoordinates (fun c x i => r * a c x i) =
      r • covectorFromCoordinates a := by
  ext p v
  simp [covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector,
    mul_assoc, Finset.mul_sum]

theorem vector_coefficient_differentiableAt (Y : RawVector M) (hY : VectorContDiff 1 Y)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    DifferentiableAt ℝ (fun y => vectorInChart Y c y i) x := by
  exact (coordProj i).differentiableAt.comp x
    (((hY c).differentiableOn_one x hx).differentiableAt
      ((chartAt FourSpace c).open_target.mem_nhds hx))

theorem coordDeriv_add (f g : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    coordDeriv (fun y => f y + g y) i x = coordDeriv f i x + coordDeriv g i x := by
  exact congrArg (fun D : FourSpace →L[ℝ] ℝ => D (basisVector i)) (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

theorem coordDeriv_smul (r : ℝ) (f : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    coordDeriv (fun y => r * f y) i x = r * coordDeriv f i x := by
  simpa only [coordDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun D : FourSpace →L[ℝ] ℝ => D (basisVector i)) (fderiv_const_mul hf r)

theorem lieTensorInChart_add_vector (Y Z : RawVector M) (g : RawCov2 M)
    (c : M) (x : FourSpace)
    (hY : ∀ i, DifferentiableAt ℝ (fun y => vectorInChart Y c y i) x)
    (hZ : ∀ i, DifferentiableAt ℝ (fun y => vectorInChart Z c y i) x) (i j : Fin 4) :
    lieTensorInChart (Y + Z) g c x i j =
      lieTensorInChart Y g c x i j + lieTensorInChart Z g c x i j := by
  simp only [lieTensorInChart, vectorInChart_add]
  simp_rw [coordDeriv_add _ _ x (hY _) (hZ _)]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem lieTensor_add_vector (Y Z : RawVector M) (g : RawCov2 M)
    (hY : VectorContDiff 1 Y) (hZ : VectorContDiff 1 Z) :
    lieTensor (Y + Z) g = lieTensor Y g + lieTensor Z g := by
  unfold lieTensor
  rw [← cov2FromCoordinates_add]
  funext p
  change cov2FromChartAt p p _ = cov2FromChartAt p p _
  apply congrArg (cov2FromChartAt p p)
  ext i j
  exact lieTensorInChart_add_vector Y Z g p (chartAt FourSpace p p)
    (vector_coefficient_differentiableAt Y hY p _ (mem_chart_target FourSpace p))
    (vector_coefficient_differentiableAt Z hZ p _ (mem_chart_target FourSpace p)) i j

theorem lieTensorInChart_smul_vector (r : ℝ) (Y : RawVector M) (g : RawCov2 M)
    (c : M) (x : FourSpace)
    (hY : ∀ i, DifferentiableAt ℝ (fun y => vectorInChart Y c y i) x) (i j : Fin 4) :
    lieTensorInChart (r • Y) g c x i j = r * lieTensorInChart Y g c x i j := by
  simp only [lieTensorInChart, vectorInChart_smul]
  simp_rw [coordDeriv_smul r _ x (hY _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem lieTensor_smul_vector (r : ℝ) (Y : RawVector M) (g : RawCov2 M)
    (hY : VectorContDiff 1 Y) :
    lieTensor (r • Y) g = r • lieTensor Y g := by
  unfold lieTensor
  rw [← cov2FromCoordinates_smul]
  funext p
  change cov2FromChartAt p p _ = cov2FromChartAt p p _
  apply congrArg (cov2FromChartAt p p)
  ext i j
  exact lieTensorInChart_smul_vector r Y g p (chartAt FourSpace p p)
    (vector_coefficient_differentiableAt Y hY p _ (mem_chart_target FourSpace p)) i j

@[simp] theorem lieTensor_zero_vector (g : RawCov2 M) : lieTensor (0 : RawVector M) g = 0 := by
  ext p v w
  simp [lieTensor, lieTensorInChart, vectorInChart, coordDeriv,
    cov2FromCoordinates, cov2FromChartAt, matrixToBilinear]



private theorem tensor_coefficient_differentiableAt (u : RawCov2 M) (hu : Cov2ContDiff 1 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x :=
  NativeLinearityArchiveLOCK24OP.cov2_coefficients_differentiableAt u hu c x hx i j

private theorem trace_differentiableAt (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y i j) x)
    (hu : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x) :
    DifferentiableAt ℝ (metricTraceInChart g u c) x :=
  NativeLinearityArchiveLOCK24OP.metricTraceInChart_differentiableAt g u c x hg hu

theorem metricTraceInChart_add (g u v : RawCov2 M) (c : M) :
    metricTraceInChart g (u + v) c =
      fun x => metricTraceInChart g u c x + metricTraceInChart g v c x := by
  funext x
  simp [metricTraceInChart, mul_add, Finset.sum_add_distrib]

theorem metricTraceInChart_smul (r : ℝ) (g u : RawCov2 M) (c : M) :
    metricTraceInChart g (r • u) c = fun x => r * metricTraceInChart g u c x := by
  funext x
  simp [metricTraceInChart, Finset.mul_sum, mul_left_comm]

theorem bianchiInChart_add (g u v : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y i j) x)
    (hu : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x)
    (hv : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart v c y i j) x)
    (j : Fin 4) :
    bianchiInChart g (u + v) c x j = bianchiInChart g u c x j + bianchiInChart g v c x j := by
  unfold bianchiInChart
  rw [metricTraceInChart_add,
    coordDeriv_add _ _ x (trace_differentiableAt g u c x hg hu)
      (trace_differentiableAt g v c x hg hv)]
  simp only [nablaTensorInChart, cov2InChart_add]
  simp_rw [coordDeriv_add _ _ x (hu _ _) (hv _ _)]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem bianchiInChart_smul (r : ℝ) (g u : RawCov2 M) (c : M) (x : FourSpace)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => inverseMetricInChart g c y i j) x)
    (hu : ∀ i j, DifferentiableAt ℝ (fun y => cov2InChart u c y i j) x)
    (j : Fin 4) :
    bianchiInChart g (r • u) c x j = r * bianchiInChart g u c x j := by
  unfold bianchiInChart
  rw [metricTraceInChart_smul,
    coordDeriv_smul r _ x (trace_differentiableAt g u c x hg hu)]
  simp only [nablaTensorInChart, cov2InChart_smul]
  simp_rw [coordDeriv_smul r _ x (hu _ _)]
  simp only [mul_sub, mul_add, mul_neg, Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [mul_assoc, mul_left_comm]

private theorem inverse_differentiableAt (g : RawCov2 M) (hg : Cov2ContDiff 1 g)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (hdet : (cov2InChart g c x).det ≠ 0) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => inverseMetricInChart g c y i j) x :=
  NativeLinearityArchiveLOCK24OP.matrix_inv_coefficient_differentiableAt _ x
    (tensor_coefficient_differentiableAt g hg c x hx) hdet i j

theorem bianchi_add (g u v : RawCov2 M)
    (hg : Cov2ContDiff 1 g) (hu : Cov2ContDiff 1 u) (hv : Cov2ContDiff 1 v)
    (hdet : ∀ p : M, (cov2InChart g p (chartAt FourSpace p p)).det ≠ 0) :
    bianchi g (u + v) = bianchi g u + bianchi g v := by
  unfold bianchi
  rw [← covectorFromCoordinates_add]
  funext p
  change covectorFromChartAt p p _ = covectorFromChartAt p p _
  apply congrArg (covectorFromChartAt p p)
  ext j
  exact bianchiInChart_add g u v p (chartAt FourSpace p p)
    (inverse_differentiableAt g hg p _ (mem_chart_target FourSpace p) (hdet p))
    (tensor_coefficient_differentiableAt u hu p _ (mem_chart_target FourSpace p))
    (tensor_coefficient_differentiableAt v hv p _ (mem_chart_target FourSpace p)) j

theorem bianchi_smul (r : ℝ) (g u : RawCov2 M)
    (hg : Cov2ContDiff 1 g) (hu : Cov2ContDiff 1 u)
    (hdet : ∀ p : M, (cov2InChart g p (chartAt FourSpace p p)).det ≠ 0) :
    bianchi g (r • u) = r • bianchi g u := by
  unfold bianchi
  rw [← covectorFromCoordinates_smul]
  funext p
  change covectorFromChartAt p p _ = covectorFromChartAt p p _
  apply congrArg (covectorFromChartAt p p)
  ext j
  exact bianchiInChart_smul r g u p (chartAt FourSpace p p)
    (inverse_differentiableAt g hg p _ (mem_chart_target FourSpace p) (hdet p))
    (tensor_coefficient_differentiableAt u hu p _ (mem_chart_target FourSpace p)) j

@[simp] theorem bianchi_zero (g : RawCov2 M) : bianchi g (0 : RawCov2 M) = 0 := by
  have ht (c : M) : metricTraceInChart g (0 : RawCov2 M) c = fun _ => 0 := by
    funext x
    simp [metricTraceInChart, cov2InChart]
  ext p v
  simp [bianchi, bianchiInChart, nablaTensorInChart, ht, cov2InChart,
    coordDeriv, covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector]

theorem covectorPiPerp_add (rho : CircleAction M) (u v : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hv : CovectorHaarIntegrable rho v) :
    covectorPiPerp rho (u + v) = covectorPiPerp rho u + covectorPiPerp rho v := by
  have hi : covectorPi0 rho (u + v) = covectorPi0 rho u + covectorPi0 rho v := by
    unfold covectorPi0
    rw [← covectorFromCoordinates_add]
    funext p
    change covectorFromChartAt p p _ = covectorFromChartAt p p _
    apply congrArg (covectorFromChartAt p p)
    ext i
    simpa only [actionPullbackCovector, pullbackCovector, covectorInChart,
      Pi.add_apply, ContinuousLinearMap.add_comp, ContinuousLinearMap.add_apply] using
      integral_add (hu p _ (mem_chart_target FourSpace p) i)
        (hv p _ (mem_chart_target FourSpace p) i)
  simp only [covectorPiPerp, hi]
  abel

theorem covectorPiPerp_smul (r : ℝ) (rho : CircleAction M) (u : RawCovector M) :
    covectorPiPerp rho (r • u) = r • covectorPiPerp rho u := by
  have hi : covectorPi0 rho (r • u) = r • covectorPi0 rho u := by
    unfold covectorPi0
    rw [← covectorFromCoordinates_smul]
    funext p
    change covectorFromChartAt p p _ = covectorFromChartAt p p _
    apply congrArg (covectorFromChartAt p p)
    ext i
    simp [actionPullbackCovector, pullbackCovector, covectorInChart, integral_const_mul]
  simp only [covectorPiPerp, hi, smul_sub]

@[simp] theorem covectorPiPerp_zero (rho : CircleAction M) :
    covectorPiPerp rho (0 : RawCovector M) = 0 := by
  ext p v
  simp [covectorPiPerp, covectorPi0, actionPullbackCovector, pullbackCovector,
    covectorInChart, covectorFromCoordinates, covectorFromChartAt, coefficientsToCovector]

section Native
variable [IsManifold I4 ∞ M]

theorem vectorOperator_add (ghat g : RawCov2 M) (Y Z : RawVector M)
    (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat) (hg : Cov2ContDiff 2 g)
    (hY : VectorContDiff 2 Y) (hZ : VectorContDiff 2 Z) :
    vectorOperator ghat g (Y + Z) = vectorOperator ghat g Y + vectorOperator ghat g Z := by
  unfold vectorOperator
  rw [lieTensor_add_vector Y Z g (fun c => (hY c).of_le (by norm_num))
      (fun c => (hZ c).of_le (by norm_num))]
  exact bianchi_add ghat _ _ hh
    (NativeLinearityArchiveREGK24REG.lieTensor_contDiff g Y hg hY)
    (NativeLinearityArchiveREGK24REG.lieTensor_contDiff g Z hg hZ)
    (fun p => NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      ghat hm p _ (mem_chart_target FourSpace p))

theorem vectorOperator_smul (r : ℝ) (ghat g : RawCov2 M) (Y : RawVector M)
    (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat) (hg : Cov2ContDiff 2 g)
    (hY : VectorContDiff 2 Y) :
    vectorOperator ghat g (r • Y) = r • vectorOperator ghat g Y := by
  unfold vectorOperator
  rw [lieTensor_smul_vector r Y g (fun c => (hY c).of_le (by norm_num))]
  exact bianchi_smul r ghat _ hh
    (NativeLinearityArchiveREGK24REG.lieTensor_contDiff g Y hg hY)
    (fun p => NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      ghat hm p _ (mem_chart_target FourSpace p))

@[simp] theorem vectorOperator_zero (ghat g : RawCov2 M) :
    vectorOperator ghat g (0 : RawVector M) = 0 := by
  simp [vectorOperator, killing]



private theorem tensor_coefficient_C1 (u : RawCov2 M) (hu : Cov2ContDiff 1 u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => cov2InChart u c y i j) x :=
  (contDiffOn_pi.mp (contDiffOn_pi.mp (hu c) i) j).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)

private theorem coordDeriv_continuousAt {f : FourSpace → ℝ} {x : FourSpace}
    (hf : ContDiffAt ℝ 1 f x) (i : Fin 4) :
    ContinuousAt (fun y => coordDeriv f i y) x :=
  ((hf.fderiv_right (m := 0) (by norm_num)).clm_apply contDiffAt_const).continuousAt

private theorem inverse_coefficient_C1 (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => inverseMetricInChart g c y i j) x :=
  NativeLinearityArchiveLOCK24SYM.matrix_inv_coefficient_contDiffAt _ x 1
    (tensor_coefficient_C1 g hg c x hx)
    (NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      g hm c x hx) i j

private theorem christoffel_continuousAt (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (l i j : Fin 4) :
    ContinuousAt (fun y => christoffelInChart g c y l i j) x := by
  apply continuousAt_const.mul
  apply tendsto_finsetSum
  intro p _
  exact (inverse_coefficient_C1 g hm hg c x hx l p).continuousAt.mul
    (((coordDeriv_continuousAt (tensor_coefficient_C1 g hg c x hx j p) i).add
      (coordDeriv_continuousAt (tensor_coefficient_C1 g hg c x hx i p) j)).sub
      (coordDeriv_continuousAt (tensor_coefficient_C1 g hg c x hx i j) p))

private theorem bianchiInChart_continuousAt (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (hu : Cov2ContDiff 1 u) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    ContinuousAt (fun y => bianchiInChart g u c y j) x := by
  have htrace : ContDiffAt ℝ 1 (metricTraceInChart g u c) x := by
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (inverse_coefficient_C1 g hm hg c x hx a b).mul
      (tensor_coefficient_C1 u hu c x hx a b)
  apply ContinuousAt.add
  · apply ContinuousAt.neg
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro b _
    apply (inverse_coefficient_C1 g hm hg c x hx a b).continuousAt.mul
    apply ContinuousAt.sub
    · apply ContinuousAt.sub
      · exact coordDeriv_continuousAt (tensor_coefficient_C1 u hu c x hx b j) a
      · apply tendsto_finsetSum
        intro p _
        exact (christoffel_continuousAt g hm hg c x hx p a b).mul
          (tensor_coefficient_C1 u hu c x hx p j).continuousAt
    · apply tendsto_finsetSum
      intro p _
      exact (christoffel_continuousAt g hm hg c x hx p a j).mul
        (tensor_coefficient_C1 u hu c x hx b p).continuousAt
  · exact continuousAt_const.mul (coordDeriv_continuousAt htrace j)

                                                                                          
theorem bianchi_contDiff_zero (g u : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (hu : Cov2ContDiff 1 u) :
    CovectorContDiff 0 (bianchi g u) := by
  intro c
  rw [contDiffOn_zero]
  have hformula : ContinuousOn (bianchiInChart g u c) (chartAt FourSpace c).target := by
    intro x hx
    apply continuousWithinAt_pi.mpr
    intro j
    exact (bianchiInChart_continuousAt g u hm hg hu c x hx j).continuousWithinAt
  apply hformula.congr
  intro x hx
  exact (nativeBianchiDeltaStarChartRecovery M g hm hg).1 u hu c x hx

theorem vectorOperator_contDiff_zero (ghat g : RawCov2 M) (Y : RawVector M)
    (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat) (hg : Cov2ContDiff 2 g)
    (hY : VectorContDiff 2 Y) : CovectorContDiff 0 (vectorOperator ghat g Y) := by
  exact bianchi_contDiff_zero ghat (lieTensor Y g) hm hh
    (NativeLinearityArchiveREGK24REG.lieTensor_contDiff g Y hg hY)

                                                                                                    
theorem vectorOperator_haarIntegrable (rho : CircleAction M) (ghat g : RawCov2 M)
    (Y : RawVector M) (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) :
    CovectorHaarIntegrable rho (vectorOperator ghat g Y) :=
  HaarSectors.covector_haar_integrable_of_continuous rho _
    (NativeContinuity.covector_evaluation_continuous _
      (vectorOperator_contDiff_zero ghat g Y hh hm hg hY))

                                                                                         
theorem projectedVectorOperator_linearOn (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (rho : CircleAction M) (ghat g : RawCov2 M) (k : ℕ) (hk : 2 ≤ k)
    (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat) (hg : Cov2ContDiff 2 g) :
    SectionLinearOn (vectorHolderPerp C k alpha rho) (projectedVectorOperator rho ghat g) := by
  have hnative (Y : RawVector M) (hY : Y ∈ vectorHolderPerp C k alpha rho) :
      VectorContDiff 2 Y := by
    intro c
    exact (NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1.1 c).of_le
      (by exact_mod_cast hk)
  refine ⟨?_, ?_, ?_⟩
  · simp [projectedVectorOperator]
  · intro Y hY Z hZ
    simp only [projectedVectorOperator,
      vectorOperator_add ghat g Y Z hh hm hg (hnative Y hY) (hnative Z hZ)]
    exact covectorPiPerp_add rho _ _
      (vectorOperator_haarIntegrable rho ghat g Y hh hm hg (hnative Y hY))
      (vectorOperator_haarIntegrable rho ghat g Z hh hm hg (hnative Z hZ))
  · intro r Y hY
    simp only [projectedVectorOperator,
      vectorOperator_smul r ghat g Y hh hm hg (hnative Y hY)]
    exact covectorPiPerp_smul r rho _



                                                                                        
                                                  
theorem projectedVectorOperator_linearOn_admissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (rho : CircleAction M) (ghat g : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (k : ℕ) (hk : 2 ≤ k) :
    SectionLinearOn (vectorHolderPerp C k b.exponent.value rho)
      (projectedVectorOperator rho ghat g) := by
  apply projectedVectorOperator_linearOn C b.exponent.value rho ghat g k hk
  · exact TensorDescent.metricAdmissible_native C b ghat hh 1
      (Nat.le_trans (by decide : 1 ≤ 2) b.order_ge_two)
  · exact hh.metric
  · exact TensorDescent.metricAdmissible_native_two C b g hg

                                                                                              
theorem vectorOperator_haarIntegrable_admissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (rho : CircleAction M) (ghat g : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (k : ℕ) (hk : 2 ≤ k) (Y : RawVector M) (hY : C.VectorHolder k b.exponent.value Y) :
    CovectorHaarIntegrable rho (vectorOperator ghat g Y) := by
  apply vectorOperator_haarIntegrable rho ghat g Y
  · exact TensorDescent.metricAdmissible_native C b ghat hh 1 (Nat.le_trans (by decide : 1 ≤ 2) b.order_ge_two)
  · exact hh.metric
  · exact TensorDescent.metricAdmissible_native_two C b g hg
  · intro c
    exact (NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1 c).of_le
      (by exact_mod_cast hk)

                                                                                                    


end Native
end K24.Global.Holder20261026Operators.NativeLinearity
/- END Holder20261026.Operators.NativeLinearity -/

/- BEGIN Holder20261026.Operators.NativeJetBounds -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
noncomputable section
open Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal ENNReal

namespace K24.Global.Holder20261026Operators.NativeJetBounds
section LocalBounds
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

                                                                                             
theorem norm_iteratedFDeriv_clm_apply_at {A : E → F →L[ℝ] G} {f : E → F}
    {x : E} {n : ℕ} (hA : ContDiffAt ℝ n A x) (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n (fun y => A y (f y)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i A x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖ := by
  obtain ⟨u, hu, hxu, hAu⟩ := hA.contDiffOn' le_rfl (by simp)
  obtain ⟨v, hv, hxv, hfv⟩ := hf.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.univ_inter] at hAu hfv
  have hs := hu.inter hv
  have hx : x ∈ u ∩ v := ⟨hxu, hxv⟩
  have h := norm_iteratedFDerivWithin_clm_apply (hAu.mono Set.inter_subset_left)
    (hfv.mono Set.inter_subset_right) hs.uniqueDiffOn hx (le_refl (n : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hs hx] using h

                                               
theorem norm_iteratedFDeriv_comp_at {g : F → G} {f : E → F} {x : E} {n : ℕ}
    (hg : ContDiffAt ℝ n g (f x)) (hf : ContDiffAt ℝ n f x) {C D : ℝ}
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * D ^ n := by
  obtain ⟨t, ht, hxt, hgt⟩ := hg.contDiffOn' le_rfl (by simp)
  obtain ⟨u, hu, hxu, hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.insert_eq_of_mem (Set.mem_univ (f x)), Set.univ_inter] at hgt hfu
  have hn : u ∩ f ⁻¹' t ∈ 𝓝 x :=
    inter_mem (hu.mem_nhds hxu) (hf.continuousAt.preimage_mem_nhds (ht.mem_nhds hxt))
  obtain ⟨s, hss, hs, hxs⟩ := mem_nhds_iff.mp hn
  have hmap : Set.MapsTo f s t := fun y hy => (hss hy).2
  have h := norm_iteratedFDerivWithin_comp_le hgt
    (hfu.mono (fun y hy => (hss hy).1)) (le_refl (n : ℕ∞ω))
    ht.uniqueDiffOn hs.uniqueDiffOn hmap hxs
    (fun i hi => by simpa only [iteratedFDerivWithin_of_isOpen _ ht hxt] using hC i hi)
    (fun i hi hin => by simpa only [iteratedFDerivWithin_of_isOpen _ hs hxs] using hD i hi hin)
  simpa only [iteratedFDerivWithin_of_isOpen _ hs hxs] using h



                                                                                                       
theorem fixed_linear_differential_expression_bound {A : E → F →L[ℝ] G} {psi : E → E}
    {x : E} {n : ℕ} (hA : ContDiffAt ℝ n A (psi x)) (hpsi : ContDiffAt ℝ n psi x) :
    ∃ L : ℝ≥0, ∀ (f : E → F), ContDiffAt ℝ n f (psi x) →
      ∀ T : ℝ, 0 ≤ T → (∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f (psi x)‖ ≤ T) →
        ‖iteratedFDeriv ℝ n ((fun y => A y (f y)) ∘ psi) x‖ ≤ (L : ℝ) * T := by
  let coeff (p : ℕ) : ℝ := ∑ i ∈ Finset.range (p + 1),
    (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i A (psi x)‖
  have hcoeff (p : ℕ) : 0 ≤ coeff p := by unfold coeff; positivity
  let B : ℝ := ∑ p ∈ Finset.range (n + 1), coeff p
  have hB : 0 ≤ B := Finset.sum_nonneg (fun p _ => hcoeff p)
  let D : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i psi x‖
  have hD : 1 ≤ D := by
    have hs : 0 ≤ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i psi x‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    dsimp [D]
    linarith
  have hder (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i psi x‖ ≤ D ^ i := by
    have hsum : ‖iteratedFDeriv ℝ i psi x‖ ≤
        ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j psi x‖ :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j psi x‖)
        (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
    calc
      ‖iteratedFDeriv ℝ i psi x‖ ≤ D := by unfold D; linarith
      _ ≤ D ^ i := by simpa using pow_le_pow_right₀ hD hi
  refine ⟨⟨n.factorial * B * D ^ n, by positivity⟩, ?_⟩
  intro f hf T hT hjet
  have hprod (p : ℕ) (hp : p ≤ n) :
      ‖iteratedFDeriv ℝ p (fun y => A y (f y)) (psi x)‖ ≤ B * T := by
    have hp' : (p : ℕ∞ω) ≤ n := by exact_mod_cast hp
    have h := norm_iteratedFDeriv_clm_apply_at (hA.of_le hp') (hf.of_le hp')
    calc
      ‖iteratedFDeriv ℝ p (fun y => A y (f y)) (psi x)‖ ≤
          ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i A (psi x)‖ * T := by
        apply h.trans
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hjet (p - i) (by omega)) (by positivity)
      _ = coeff p * T := by simp only [coeff, Finset.sum_mul]
      _ ≤ B * T := by
        apply mul_le_mul_of_nonneg_right _ hT
        exact Finset.single_le_sum (fun i _ => hcoeff i) (Finset.mem_range.mpr (by omega))
  have h := norm_iteratedFDeriv_comp_at (hA.clm_apply hf) hpsi hprod hder
  change _ ≤ (n.factorial * B * D ^ n) * T
  convert h using 1 <;> ring

end LocalBounds


section Native
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

                                                                                                     
theorem lifted_vector_jet_norm_le (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (k j : ℕ) (hj : j ≤ k) (Y : RawVector M) (hY : C.VectorHolder k alpha Y)
    (ν : C.Index) (x : FourSpace) (hx : x ∈ (C.chart ν).innerDomain) :
    ‖iteratedFDeriv ℝ j ((C.chart ν).liftedVector Y) x‖ ≤ (C.vectorENorm k alpha Y).toReal := by
  have h := (jet_enorm_le_coordinateHolderENorm k j hj alpha
    (C.chart ν).innerDomain ((C.chart ν).liftedVector Y) x hx).trans
    (le_iSup (fun η : C.Index => coordinateHolderENorm k alpha
      (C.chart η).innerDomain ((C.chart η).liftedVector Y)) ν)
  rw [iteratedFDerivWithin_of_isOpen j (C.chart ν).innerOpen hx] at h
  have hr := ENNReal.toReal_mono hY.2.ne h
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using hr

                                                                               
                                                                                
theorem vector_native_jet_bound (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (k j : ℕ) (hj : j ≤ k) (d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace d).target) :
    ∃ D : ℝ≥0, ∀ Y : RawVector M, C.VectorHolder k alpha Y →
      ‖iteratedFDeriv ℝ j (vectorInChart Y d) z‖ₑ ≤ (D : ℝ≥0∞) * C.vectorENorm k alpha Y := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift ((chartAt FourSpace d).symm z)
  let c := C.chart ν
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
  let A := fderiv ℝ F
  have hA : ContDiffAt ℝ j A (psi (F x)) := by
    rw [hleft]
    exact hF.fderiv_right (by exact_mod_cast (le_top : (j + 1 : ℕ∞) ≤ ⊤))
  have hpsi_j : ContDiffAt ℝ j psi (F x) :=
    hpsi.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  obtain ⟨D, hD⟩ := fixed_linear_differential_expression_bound hA hpsi_j
  refine ⟨D, ?_⟩
  intro Y hY
  have hcoeff : ContDiffAt ℝ j (c.liftedVector Y) (psi (F x)) := by
    rw [hleft]
    exact ((hY.1 ν).contDiffAt (c.innerOpen.mem_nhds hx)).of_le (by exact_mod_cast hj)
  have hreal := hD (c.liftedVector Y) hcoeff (C.vectorENorm k alpha Y).toReal
    ENNReal.toReal_nonneg (fun i hi => by
      rw [hleft]
      exact lifted_vector_jet_norm_le C alpha k i (hi.trans hj) Y hY ν x hx)
  have hneigh : ∀ᶠ y in 𝓝 (F x), psi y ∈ c.outerDomain ∧
      c.lift (psi y) ∈ (chartAt FourSpace d).source := by
    have hN : ∀ᶠ y in 𝓝 (psi (F x)), y ∈ c.outerDomain ∧
        c.lift y ∈ (chartAt FourSpace d).source := by
      rw [hleft]
      exact inter_mem (c.outerOpen.mem_nhds hxo)
        ((NativeRegularity.lift_smoothAt c x hxo).continuousAt.preimage_mem_nhds
          ((chartAt FourSpace d).open_source.mem_nhds hd))
    exact hpsi.continuousAt.tendsto.eventually hN
  have heq : vectorInChart Y d =ᶠ[𝓝 (F x)] ((fun y => A y (c.liftedVector Y y)) ∘ psi) := by
    filter_upwards [hright, hneigh] with y hy hyd
    have he := NativeRegularity.vector_coord_lift c Y d (psi y) hyd.1 hyd.2
    change vectorInChart Y d (F (psi y)) = A (psi y) (c.liftedVector Y (psi y)) at he
    simpa only [hy, Function.comp_apply] using he
  have heqjet := (heq.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds
  rw [← heqjet, hFx] at hreal
  have hen := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_norm, ENNReal.ofReal_mul D.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hY.2.ne] using hen

end Native
end K24.Global.Holder20261026Operators.NativeJetBounds
/- END Holder20261026.Operators.NativeJetBounds -/

/- BEGIN Holder20261026.Operators.OperatorPointBound -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal ENNReal

namespace K24.Global.Holder20261026Operators.OperatorPointBound

section Calculus
variable {P E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

private def JetControl (S : Set P) (N : P → ℝ) (x : E) (n : ℕ) (f : P → E → V) : Prop :=
  (∀ p ∈ S, ContDiffAt ℝ n (f p) x) ∧
    ∀ j, j ≤ n → ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ S, ‖iteratedFDeriv ℝ j (f p) x‖ ≤ D * N p

private theorem JetControl.mono {S : Set P} {N : P → ℝ} {x : E} {m n : ℕ}
    {f : P → E → V} (h : JetControl S N x n f) (hmn : m ≤ n) : JetControl S N x m f :=
  ⟨fun p hp => (h.1 p hp).of_le (by exact_mod_cast hmn), fun j hj => h.2 j (hj.trans hmn)⟩

private theorem JetControl.common_bound {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f : P → E → V} (h : JetControl S N x n f) (hN : ∀ p ∈ S, 0 ≤ N p) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ S, ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j (f p) x‖ ≤ D * N p := by
  have hex (j : Fin (n + 1)) := h.2 j.val (by omega)
  choose D hD using hex
  refine ⟨∑ j : Fin (n + 1), D j, Finset.sum_nonneg (fun j _ => (hD j).1), ?_⟩
  intro p hp j hj
  let i : Fin (n + 1) := ⟨j, by omega⟩
  apply ((hD i).2 p hp).trans
  apply mul_le_mul_of_nonneg_right _ (hN p hp)
  exact Finset.single_le_sum (fun l _ => (hD l).1) (Finset.mem_univ i)

private theorem JetControl.linear {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f : P → E → V} (h : JetControl S N x n f) (L : V →L[ℝ] W) :
    JetControl S N x n (fun p => L ∘ f p) := by
  refine ⟨fun p hp => L.contDiff.contDiffAt.comp x (h.1 p hp), ?_⟩
  intro j hj
  obtain ⟨D, hD, hb⟩ := h.2 j hj
  refine ⟨‖L‖ * D, mul_nonneg (norm_nonneg _) hD, fun p hp => ?_⟩
  calc
    ‖iteratedFDeriv ℝ j (L ∘ f p) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f p) x‖ :=
      L.norm_iteratedFDeriv_comp_left (h.1 p hp) (by exact_mod_cast hj)
    _ ≤ ‖L‖ * (D * N p) := mul_le_mul_of_nonneg_left (hb p hp) (norm_nonneg _)
    _ = _ := by ring

private theorem JetControl.deriv_apply {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f : P → E → V} (h : JetControl S N x (n + 1) f) (v : E) :
    JetControl S N x n (fun p y => fderiv ℝ (f p) y v) := by
  refine ⟨fun p hp => ((h.1 p hp).fderiv_right (m := (n : ℕ∞ω)) (by simp)).clm_apply contDiffAt_const, ?_⟩
  intro j hj
  obtain ⟨D, hD, hb⟩ := h.2 (j + 1) (by omega)
  refine ⟨‖v‖ * D, mul_nonneg (norm_nonneg _) hD, fun p hp => ?_⟩
  calc
    ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (f p) y v) x‖ ≤
        ‖v‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (f p)) x‖ :=
      norm_iteratedFDeriv_clm_apply_const ((h.1 p hp).fderiv_right (m := (n : ℕ∞ω)) (by simp))
        (by exact_mod_cast hj)
    _ = ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) (f p) x‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖v‖ * (D * N p) := mul_le_mul_of_nonneg_left (hb p hp) (norm_nonneg _)
    _ = _ := by ring

private theorem JetControl.add {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f g : P → E → V} (hf : JetControl S N x n f) (hg : JetControl S N x n g) :
    JetControl S N x n (fun p y => f p y + g p y) := by
  refine ⟨fun p hp => (hf.1 p hp).add (hg.1 p hp), ?_⟩
  intro j hj
  obtain ⟨D, hD, hDb⟩ := hf.2 j hj
  obtain ⟨B, hB, hBb⟩ := hg.2 j hj
  refine ⟨D + B, add_nonneg hD hB, fun p hp => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((hf.1 p hp).of_le (by exact_mod_cast hj))
    ((hg.1 p hp).of_le (by exact_mod_cast hj))]
  exact (norm_add_le _ _).trans ((add_le_add (hDb p hp) (hBb p hp)).trans_eq (by ring))

private theorem JetControl.zero (S : Set P) (N : P → ℝ) (x : E) (n : ℕ) :
    JetControl S N x n (fun _ _ => (0 : V)) := by
  refine ⟨fun _ _ => contDiffAt_const, fun j _ => ⟨0, le_rfl, ?_⟩⟩
  intro p hp
  simp [iteratedFDeriv_zero_fun]

private theorem JetControl.sum {ι : Type*} (s : Finset ι) {S : Set P} {N : P → ℝ}
    {x : E} {n : ℕ} {f : ι → P → E → V} (h : ∀ i ∈ s, JetControl S N x n (f i)) :
    JetControl S N x n (fun p y => ∑ i ∈ s, f i p y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using JetControl.zero S N x n
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private theorem JetControl.fixed_mul {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f : P → E → ℝ} (hf : JetControl S N x n f) (hN : ∀ p ∈ S, 0 ≤ N p)
    (a : E → ℝ) (ha : ContDiffAt ℝ n a x) :
    JetControl S N x n (fun p y => a y * f p y) := by
  refine ⟨fun p hp => ha.mul (hf.1 p hp), ?_⟩
  intro j hj
  have hj' : (j : ℕ∞ω) ≤ n := by exact_mod_cast hj
  let A : E → ℝ →L[ℝ] ℝ := fun y => a y • ContinuousLinearMap.id ℝ ℝ
  have hA : ContDiffAt ℝ j A x := (ha.of_le hj').smul contDiffAt_const
  obtain ⟨L, hL⟩ := NativeJetBounds.fixed_linear_differential_expression_bound
    (psi := id) hA contDiffAt_id
  obtain ⟨B, hB, hb⟩ := hf.common_bound hN
  refine ⟨L * B, mul_nonneg L.coe_nonneg hB, fun p hp => ?_⟩
  have hb' : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i (f p) x‖ ≤ B * N p :=
    fun i hi => hb p hp i (hi.trans hj)
  have h := hL (f p) ((hf.1 p hp).of_le hj') (B * N p)
    (mul_nonneg hB (hN p hp)) hb'
  simpa only [A, Function.comp_id, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_assoc] using h

private theorem JetControl.congr {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f g : P → E → V} (hf : JetControl S N x n f)
    (hfg : ∀ p ∈ S, f p =ᶠ[𝓝 x] g p) : JetControl S N x n g := by
  refine ⟨fun p hp => (hf.1 p hp).congr_of_eventuallyEq (hfg p hp).symm, ?_⟩
  intro j hj
  obtain ⟨D, hD, hb⟩ := hf.2 j hj
  refine ⟨D, hD, fun p hp => ?_⟩
  rw [← ((hfg p hp).iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
  exact hb p hp



private def ValueControl (S : Set P) (N : P → ℝ) (f : P → V) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ S, ‖f p‖ ≤ D * N p

private theorem JetControl.value {S : Set P} {N : P → ℝ} {x : E} {n : ℕ}
    {f : P → E → V} (h : JetControl S N x n f) : ValueControl S N (fun p => f p x) := by
  obtain ⟨D, hD, hb⟩ := h.2 0 (Nat.zero_le n)
  refine ⟨D, hD, fun p hp => ?_⟩
  simpa only [norm_iteratedFDeriv_zero] using hb p hp

private theorem JetControl.deriv_value {S : Set P} {N : P → ℝ} {x : E}
    {f : P → E → V} (h : JetControl S N x 1 f) (v : E) :
    ValueControl S N (fun p => fderiv ℝ (f p) x v) := (h.deriv_apply v).value

private theorem ValueControl.add {S : Set P} {N : P → ℝ} {f g : P → V}
    (hf : ValueControl S N f) (hg : ValueControl S N g) :
    ValueControl S N (fun p => f p + g p) := by
  obtain ⟨D, hD, hDb⟩ := hf
  obtain ⟨B, hB, hBb⟩ := hg
  refine ⟨D + B, add_nonneg hD hB, fun p hp => ?_⟩
  exact (norm_add_le _ _).trans ((add_le_add (hDb p hp) (hBb p hp)).trans_eq (by ring))

private theorem ValueControl.sub {S : Set P} {N : P → ℝ} {f g : P → V}
    (hf : ValueControl S N f) (hg : ValueControl S N g) :
    ValueControl S N (fun p => f p - g p) := by
  obtain ⟨D, hD, hDb⟩ := hf
  obtain ⟨B, hB, hBb⟩ := hg
  refine ⟨D + B, add_nonneg hD hB, fun p hp => ?_⟩
  exact (norm_sub_le _ _).trans ((add_le_add (hDb p hp) (hBb p hp)).trans_eq (by ring))

private theorem ValueControl.neg {S : Set P} {N : P → ℝ} {f : P → V}
    (hf : ValueControl S N f) : ValueControl S N (fun p => -f p) := by
  simpa only [ValueControl, norm_neg] using hf

private theorem ValueControl.const_mul {S : Set P} {N : P → ℝ} {f : P → ℝ}
    (hf : ValueControl S N f) (a : ℝ) : ValueControl S N (fun p => a * f p) := by
  obtain ⟨D, hD, hb⟩ := hf
  refine ⟨‖a‖ * D, mul_nonneg (norm_nonneg _) hD, fun p hp => ?_⟩
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hb p hp) (norm_nonneg _)).trans_eq (by ring)

private theorem ValueControl.sum {ι : Type*} (s : Finset ι) {S : Set P} {N : P → ℝ}
    {f : ι → P → V} (h : ∀ i ∈ s, ValueControl S N (f i)) :
    ValueControl S N (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (h a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Calculus


section Native
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem native_vector_control (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (k : ℕ) (hk : 2 ≤ k) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target) :
    JetControl {Y | C.VectorHolder k alpha Y} (fun Y => (C.vectorENorm k alpha Y).toReal)
      x 2 (fun Y => vectorInChart Y d) := by
  refine ⟨?_, ?_⟩
  · intro Y hY
    exact ((NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1 d).contDiffAt
      ((chartAt FourSpace d).open_target.mem_nhds hx)).of_le (by exact_mod_cast hk)
  · intro j hj
    obtain ⟨D, hD⟩ := NativeJetBounds.vector_native_jet_bound C alpha k j (hj.trans hk) d x hx
    refine ⟨D, D.coe_nonneg, fun Y hY => ?_⟩
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hY.2.ne) (hD Y hY)
    simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
      ENNReal.toReal_mul, ENNReal.coe_toReal] using h

                                                           
private theorem lieTensor_coefficients (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target) :
    cov2InChart (lieTensor Y g) d x = lieTensorInChart Y g d x := by
  refine NativeLinearityArchiveREGK24REG.cov2InChart_reconstruction
    (lieTensorInChart Y g) ?_ d x hx
  intro c e p hc he
  have h := NativeLinearityArchiveREGK24REG.lieTensorInChart_transition g Y hg hY c e
    (chartAt FourSpace c p) ((chartAt FourSpace c).map_source hc)
    (by simpa only [(chartAt FourSpace c).left_inv hc] using he)
  simpa only [(chartAt FourSpace c).left_inv hc] using h

private theorem metric_coefficient_C2 (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace d).target) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun y => cov2InChart g d y i j) x :=
  (contDiffOn_pi.mp (contDiffOn_pi.mp (hg d) i) j).contDiffAt
    ((chartAt FourSpace d).open_target.mem_nhds hx)

private theorem lie_coefficient_control (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (k : ℕ) (hk : 2 ≤ k) (g : RawCov2 M) (hg : Cov2ContDiff 2 g)
    (d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace d).target) (i j : Fin 4) :
    JetControl {Y | C.VectorHolder k alpha Y} (fun Y => (C.vectorENorm k alpha Y).toReal)
      x 1 (fun Y y => cov2InChart (lieTensor Y g) d y i j) := by
  let S := {Y | C.VectorHolder k alpha Y}
  let N := fun Y => (C.vectorENorm k alpha Y).toReal
  have hN : ∀ Y ∈ S, 0 ≤ N Y := fun _ _ => ENNReal.toReal_nonneg
  have hV := native_vector_control C alpha k hk d x hx
  have hcomp (p : Fin 4) : JetControl S N x 2 (fun Y y => vectorInChart Y d y p) :=
    hV.linear (coordProj p)
  have hder (p a : Fin 4) : JetControl S N x 1
      (fun Y y => coordDeriv (fun z => vectorInChart Y d z p) a y) :=
    (hcomp p).deriv_apply (basisVector a)
  have hgc (a b : Fin 4) := metric_coefficient_C2 g hg d x hx a b
  have hgd (a b p : Fin 4) : ContDiffAt ℝ 1
      (fun y => coordDeriv (fun z => cov2InChart g d z a b) p y) x :=
    ((hgc a b).fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hformula : JetControl S N x 1 (fun Y y => lieTensorInChart Y g d y i j) := by
    apply JetControl.sum Finset.univ
    intro p _
    have h1 := ((hcomp p).mono (by decide : 1 ≤ 2)).fixed_mul hN _ (hgd i j p)
    have h2 := (hder p i).fixed_mul hN _ ((hgc p j).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
    have h3 := (hder p j).fixed_mul hN _ ((hgc i p).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
    simpa only [mul_comm] using (h1.add h2).add h3
  apply hformula.congr
  intro Y hY
  have hYn : VectorContDiff 2 Y := fun c =>
    (NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1 c).of_le
      (by exact_mod_cast hk)
  filter_upwards [(chartAt FourSpace d).open_target.mem_nhds hx] with y hy
  exact (congrFun (congrFun (lieTensor_coefficients g Y hg hYn d y hy) i) j).symm



private theorem inverse_coefficient_C1 (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff 1 g) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target) (i j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => inverseMetricInChart g d y i j) x := by
  apply NativeLinearityArchiveLOCK24SYM.matrix_inv_coefficient_contDiffAt
  · intro a b
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp (hg d) a) b).contDiffAt
      ((chartAt FourSpace d).open_target.mem_nhds hx)
  · exact NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      g hm d x hx

private theorem bianchi_lie_value_control (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (k : ℕ) (hk : 2 ≤ k) (ghat g : RawCov2 M)
    (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat) (hg : Cov2ContDiff 2 g)
    (d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace d).target) (j : Fin 4) :
    ValueControl {Y | C.VectorHolder k alpha Y} (fun Y => (C.vectorENorm k alpha Y).toReal)
      (fun Y => bianchiInChart ghat (lieTensor Y g) d x j) := by
  let S := {Y | C.VectorHolder k alpha Y}
  let N := fun Y => (C.vectorENorm k alpha Y).toReal
  have hN : ∀ Y ∈ S, 0 ≤ N Y := fun _ _ => ENNReal.toReal_nonneg
  have hU (a b : Fin 4) := lie_coefficient_control C alpha k hk g hg d x hx a b
  have htrace : JetControl S N x 1 (fun Y => metricTraceInChart ghat (lieTensor Y g) d) := by
    apply JetControl.sum Finset.univ
    intro a _
    apply JetControl.sum Finset.univ
    intro b _
    exact (hU a b).fixed_mul hN _ (inverse_coefficient_C1 ghat hm hh d x hx a b)
  have hnabla (a b l : Fin 4) : ValueControl S N
      (fun Y => nablaTensorInChart ghat (lieTensor Y g) d x a b l) := by
    have h1 : ValueControl S N (fun Y => ∑ p : Fin 4,
        christoffelInChart ghat d x p a b * cov2InChart (lieTensor Y g) d x p l) := by
      apply ValueControl.sum Finset.univ
      intro p _
      exact (hU p l).value.const_mul _
    have h2 : ValueControl S N (fun Y => ∑ p : Fin 4,
        christoffelInChart ghat d x p a l * cov2InChart (lieTensor Y g) d x b p) := by
      apply ValueControl.sum Finset.univ
      intro p _
      exact (hU b p).value.const_mul _
    exact (((hU b l).deriv_value (basisVector a)).sub h1).sub h2
  have hdiv : ValueControl S N (fun Y => ∑ a : Fin 4, ∑ b : Fin 4,
      inverseMetricInChart ghat d x a b * nablaTensorInChart ghat (lieTensor Y g) d x a b j) := by
    apply ValueControl.sum Finset.univ
    intro a _
    apply ValueControl.sum Finset.univ
    intro b _
    exact (hnabla a b j).const_mul _
  exact hdiv.neg.add ((htrace.deriv_value (basisVector j)).const_mul (1 / 2))

                                                                                   
                                                                                 
theorem vectorOperator_scalar_bound (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (k : ℕ) (hk : 2 ≤ k) (ghat g : RawCov2 M)
    (hh : Cov2ContDiff 1 ghat) (hm : IsMetric ghat) (hg : Cov2ContDiff 2 g)
    (p : M) (v : TangentSpace I4 p) :
    ∃ D : ℝ≥0, ∀ Y : RawVector M, C.VectorHolder k alpha Y →
      ‖vectorOperator ghat g Y p v‖ₑ ≤ (D : ℝ≥0∞) * C.vectorENorm k alpha Y := by
  have heval : ValueControl {Y | C.VectorHolder k alpha Y}
      (fun Y => (C.vectorENorm k alpha Y).toReal)
      (fun Y => vectorOperator ghat g Y p v) := by
    have hsum : ValueControl {Y | C.VectorHolder k alpha Y}
        (fun Y => (C.vectorENorm k alpha Y).toReal)
        (fun Y => ∑ i : Fin 4,
          (coordProj i) (mfderiv I4 I4 (chartAt FourSpace p) p v) *
            bianchiInChart ghat (lieTensor Y g) p (chartAt FourSpace p p) i) := by
      apply ValueControl.sum Finset.univ
      intro i _
      exact (bianchi_lie_value_control C alpha k hk ghat g hh hm hg p
        (chartAt FourSpace p p) (mem_chart_target FourSpace p) i).const_mul _
    have heq : (fun Y : RawVector M => vectorOperator ghat g Y p v) =
        (fun Y => ∑ i : Fin 4,
          (coordProj i) (mfderiv I4 I4 (chartAt FourSpace p) p v) *
            bianchiInChart ghat (lieTensor Y g) p (chartAt FourSpace p p) i) := by
      funext Y
      simp only [vectorOperator, bianchi, covectorFromCoordinates, covectorFromChartAt,
        coefficientsToCovector, ContinuousLinearMap.comp_apply, sum_apply,
        smul_apply, smul_eq_mul, mul_comm]
      rfl
    rw [heq]
    exact hsum
  obtain ⟨D, hD, hb⟩ := heval
  refine ⟨Real.toNNReal D, fun Y hY => ?_⟩
  have h := ENNReal.ofReal_le_ofReal (hb Y hY)
  rw [ofReal_norm, ENNReal.ofReal_mul hD, ENNReal.ofReal_toReal hY.2.ne] at h
  exact h

                                                                                         
theorem vectorOperator_scalar_bound_admissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (k : ℕ) (hk : 2 ≤ k) (ghat g : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (p : M) (v : TangentSpace I4 p) :
    ∃ D : ℝ≥0, ∀ Y : RawVector M, C.VectorHolder k b.exponent.value Y →
      ‖vectorOperator ghat g Y p v‖ₑ ≤ (D : ℝ≥0∞) * C.vectorENorm k b.exponent.value Y :=
  vectorOperator_scalar_bound C b.exponent.value k hk ghat g
    (TensorDescent.metricAdmissible_native C b ghat hh 1
      (Nat.le_trans (by decide : 1 ≤ 2) b.order_ge_two)) hh.metric
    (TensorDescent.metricAdmissible_native_two C b g hg) p v

                                                                                           
theorem vectorOperator_linearOn_holder (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (k : ℕ) (hk : 2 ≤ k) (ghat g : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g) :
    SectionLinearOn {Y | C.VectorHolder k b.exponent.value Y} (vectorOperator ghat g) := by
  have hhh : Cov2ContDiff 1 ghat := TensorDescent.metricAdmissible_native C b ghat hh 1
    (Nat.le_trans (by decide : 1 ≤ 2) b.order_ge_two)
  have hgg := TensorDescent.metricAdmissible_native_two C b g hg
  have hnative (Y : RawVector M) (hY : C.VectorHolder k b.exponent.value Y) :
      VectorContDiff 2 Y := fun c =>
    (NativeRegularity.vectorContDiff_of_lifted_contDiff C k Y hY.1 c).of_le
      (by exact_mod_cast hk)
  refine ⟨NativeLinearity.vectorOperator_zero ghat g, ?_, ?_⟩
  · intro Y hY Z hZ
    exact NativeLinearity.vectorOperator_add ghat g Y Z hhh hh.metric hgg
      (hnative Y hY) (hnative Z hZ)
  · intro r Y hY
    exact NativeLinearity.vectorOperator_smul r ghat g Y hhh hh.metric hgg (hnative Y hY)

end Native
end K24.Global.Holder20261026Operators.OperatorPointBound
/- END Holder20261026.Operators.OperatorPointBound -/

/- BEGIN Holder20261026.Operators.VectorBoundFromMapping -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Topology

namespace K24.Global.Holder20261026Operators
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

                                                                               
                                                                
theorem vectorOperator_bounded_of_holder_mapping (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (n m : ℕ) (hn : 2 ≤ n)
    (ghat g : RawCov2 M) (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (hreg : ∀ Y : RawVector M, C.VectorHolder n b.exponent.value Y →
      C.CovectorHolder m b.exponent.value (vectorOperator ghat g Y)) :
    SectionBoundedOn {Y : RawVector M | C.VectorHolder n b.exponent.value Y}
      (C.vectorENorm n b.exponent.value) (C.covectorENorm m b.exponent.value)
      (vectorOperator ghat g) := by
  apply sectionBoundedOn_of_scalar_observations
    (vectorHolder_sectionBanach C n b.exponent.value)
    (covectorHolder_sectionBanach C m b.exponent.value)
    (vectorOperator ghat g) (fun Y hY => hreg Y hY)
    (OperatorPointBound.vectorOperator_linearOn_holder C b n hn ghat g hh hg)
    covectorEvaluation
  · intro v w h
    ext p a
    exact h ⟨p, a⟩
  · intro q
    exact OperatorPointBound.vectorOperator_scalar_bound_admissible C b n hn
      ghat g hh hg q.1 q.2
  · exact covectorEvaluation_bounded C m b.exponent.value

                                                                            
                                                                          
                                                           
theorem projectedVectorOperator_fields_of_holder_mapping (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n)
    (H : ℝ≥0) (rho : CircleAction M)
    (hact : HolderActionControl C b.exponent.value H n rho)
    (ghat g : RawCov2 M) (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (hreg : ∀ Y : RawVector M, C.VectorHolder n b.exponent.value Y →
      C.CovectorHolder m b.exponent.value (vectorOperator ghat g Y)) :
    Set.MapsTo (projectedVectorOperator rho ghat g)
      (vectorHolderPerp C n b.exponent.value rho) (covectorHolderPerp C m b.exponent.value rho) ∧
    SectionLinearOn (vectorHolderPerp C n b.exponent.value rho)
      (projectedVectorOperator rho ghat g) ∧
    SectionBoundedOn (vectorHolderPerp C n b.exponent.value rho)
      (C.vectorENorm n b.exponent.value) (C.covectorENorm m b.exponent.value)
      (projectedVectorOperator rho ghat g) := by
  have hp := HolderProjectionFinite.holder_projection_finite C b.exponent.value H
    b.exponent.positive n rho hact
  refine ⟨?_, NativeLinearity.projectedVectorOperator_linearOn_admissible C b rho ghat g hh hg n hn, ?_⟩
  · intro Y hY
    obtain ⟨_, _, hmem, _, _, hzero, _, _⟩ := hp.covector m hm _ (hreg Y hY.1)
    exact ⟨hmem, hzero⟩
  · obtain ⟨D, hD⟩ := vectorOperator_bounded_of_holder_mapping C b n m hn ghat g hh hg hreg
    refine ⟨(1 + H) * D, fun Y hY => ?_⟩
    obtain ⟨_, _, _, _, _, _, _, hb⟩ := hp.covector m hm _ (hreg Y hY.1)
    calc
      C.covectorENorm m b.exponent.value (projectedVectorOperator rho ghat g Y) ≤
          ((1 + H : ℝ≥0) : ℝ≥0∞) * C.covectorENorm m b.exponent.value (vectorOperator ghat g Y) := hb
      _ ≤ ((1 + H : ℝ≥0) : ℝ≥0∞) * ((D : ℝ≥0∞) * C.vectorENorm n b.exponent.value Y) :=
        mul_le_mul' le_rfl (hD Y hY.1)
      _ = (((1 + H) * D : ℝ≥0) : ℝ≥0∞) * C.vectorENorm n b.exponent.value Y := by
        simp only [ENNReal.coe_mul, mul_assoc]

end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.VectorBoundFromMapping -/

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

theorem vectorHolder_inner_germ (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (ha : alpha ≤ 1) (Y : RawVector M) (hY : C.VectorHolder k alpha Y)
    (nu : C.Index) (x : FourSpace) (hx : x ∈ (C.chart nu).innerDomain) :
    LocallyAllHolder k alpha ((C.chart nu).liftedVector Y) x := by
  refine ⟨(C.chart nu).innerDomain,(C.chart nu).innerOpen,hx,?_⟩
  intro j hj
  have h := vectorHolder_lower C k j hj alpha ha Y hY
  exact ⟨h.1 nu,(le_iSup (fun mu : C.Index => coordinateHolderENorm j alpha
    (C.chart mu).innerDomain ((C.chart mu).liftedVector Y)) nu).trans_lt h.2⟩


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

                                                                         
                                    
theorem vectorHolder_native_germ (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (ha : alpha ≤ 1) (Y : RawVector M) (hY : C.VectorHolder k alpha Y)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target) :
    LocallyAllHolder k alpha (vectorInChart Y d) z := by
  obtain ⟨nu, x, hx, hxp, psi, hpsi, hleft, hnear⟩ := exists_inner_coordinate_inverse C d z hz
  let c := C.chart nu
  have hxo : x ∈ c.outerDomain := c.closureInnerSubset (subset_closure hx)
  have hd : c.lift x ∈ (chartAt FourSpace d).source := by
    rw [hxp]; exact (chartAt FourSpace d).map_target hz
  let F := (chartAt FourSpace d) ∘ c.lift
  have hF : ContDiffAt ℝ ∞ F x := NativeRegularity.coord_smoothAt c d x hxo hd
  have hJ : LocallyAllHolder k alpha (fderiv ℝ F) x :=
    LocallyAllHolder.of_contDiffAt k alpha ha _ x
      (hF.fderiv_right (by exact_mod_cast (le_top : (k + 1 + 1 : ℕ∞) ≤ ⊤)))
  have hf := vectorHolder_inner_germ C k alpha ha Y hY nu x hx
  have hp := holder_clm_apply hJ hf
  have hp' : LocallyAllHolder k alpha
      ((fun y => fderiv ℝ F y (c.liftedVector Y y)) ∘ psi) z := by
    apply LocallyAllHolder.comp_of_contDiffAt (g := psi) _ hpsi ha
    simpa only [hleft] using hp
  apply hp'.congr
  filter_upwards [hnear] with y hy
  have he := NativeRegularity.vector_coord_lift c Y d (psi y)
    (c.closureInnerSubset (subset_closure hy.1)) hy.2.1
  have hr : chartAt FourSpace d (c.lift (psi y)) = y := hy.2.2
  rw [hr] at he
  simpa only [F, Function.comp_apply] using he.symm


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

theorem coordDeriv_contDiffOn (k : ℕ) {s : Set FourSpace} (hs : IsOpen s)
    (f : FourSpace → ℝ) (hf : ContDiffOn ℝ (k + 1) f s) (i : Fin 4) :
    ContDiffOn ℝ k (fun x => coordDeriv f i x) s := by
  exact (hf.fderiv_of_isOpen hs (by simp)).clm_apply contDiffOn_const

theorem lieTensorInChart_contDiffOn (k : ℕ) (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff (k + 1) g) (hY : VectorContDiff (k + 1) Y) (c : M) :
    ContDiffOn ℝ k (lieTensorInChart Y g c) (chartAt FourSpace c).target := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply ContDiffOn.sum
  intro p _
  have hgij := contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) j
  have hgpj := contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) p) j
  have hgip := contDiffOn_pi.mp (contDiffOn_pi.mp (hg c) i) p
  have hYp := (coordProj p).contDiff.comp_contDiffOn (hY c)
  have hopen := (chartAt FourSpace c).open_target
  exact (((hYp.of_le (by simp)).mul (coordDeriv_contDiffOn k hopen _ hgij p)).add
    ((coordDeriv_contDiffOn k hopen _ hYp i).mul (hgpj.of_le (by simp)))).add
      ((coordDeriv_contDiffOn k hopen _ hYp j).mul (hgip.of_le (by simp)))

                                                                             
                                                                        
theorem lieTensor_contDiff_succ (k : ℕ) (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff (k + 2) g) (hY : VectorContDiff (k + 2) Y) :
    Cov2ContDiff (k + 1) (lieTensor Y g) := by
  refine NativeLinearityArchiveREGK24REG.cov2FromCoordinates_contDiff
    (lieTensorInChart Y g) ?_ (k + 1) ?_
  · intro c d p hc hd
    have hg2 : Cov2ContDiff 2 g := fun c => (hg c).of_le (by norm_cast; omega)
    have hY2 : VectorContDiff 2 Y := fun c => (hY c).of_le (by norm_cast; omega)
    have h := NativeLinearityArchiveREGK24REG.lieTensorInChart_transition g Y hg2 hY2
      c d (chartAt FourSpace c p) ((chartAt FourSpace c).map_source hc)
      (by simpa only [(chartAt FourSpace c).left_inv hc] using hd)
    simpa only [(chartAt FourSpace c).left_inv hc] using h
  · intro c
    exact lieTensorInChart_contDiffOn (k + 1) g Y
      (by convert hg using 1 <;> norm_num [Nat.cast_add, add_assoc])
      (by convert hY using 1 <;> norm_num [Nat.cast_add, add_assoc]) c

theorem tensor_coefficient_contDiffAt (k : ℕ) (u : RawCov2 M) (hu : Cov2ContDiff k u)
    (c : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ k (fun y => cov2InChart u c y i j) x :=
  (contDiffOn_pi.mp (contDiffOn_pi.mp (hu c) i) j).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hx)


theorem inverse_coefficient_contDiffAt (k : ℕ) (g : RawCov2 M) (hm : IsMetric g)
    (hg : Cov2ContDiff k g) (c : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ k (fun y => inverseMetricInChart g c y i j) x :=
  NativeLinearityArchiveLOCK24SYM.matrix_inv_coefficient_contDiffAt _ x k
    (tensor_coefficient_contDiffAt k g hg c x hx)
    (NativeLinearityArchiveLOCNativeLinearityArchiveLOCK24OPConnection.metric_chart_det_ne_zero
      g hm c x hx) i j





end K24.Global.Holder20261026Operators.HigherRegularity

/- END Holder20261026.Operators.HigherRegularity -/

/- BEGIN Holder20261026.Operators.NativeHolderOperators -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Manifold ContDiff BigOperators Topology Matrix.Norms.Elementwise NNReal ENNReal

namespace K24.Global.Holder20261026Operators.NativeHolderOperators
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem lieTensor_coefficients (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target) :
    cov2InChart (lieTensor Y g) d x = lieTensorInChart Y g d x := by
  refine NativeLinearityArchiveREGK24REG.cov2InChart_reconstruction
    (lieTensorInChart Y g) ?_ d x hx
  intro c e p hc he
  have h := NativeLinearityArchiveREGK24REG.lieTensorInChart_transition g Y hg hY c e
    (chartAt FourSpace c p) ((chartAt FourSpace c).map_source hc)
    (by simpa only [(chartAt FourSpace c).left_inv hc] using he)
  simpa only [(chartAt FourSpace c).left_inv hc] using h

                                                                                      
theorem lieTensor_native_germ (k : ℕ) (alpha : ℝ≥0) (g : RawCov2 M) (Y : RawVector M)
    (hg : Cov2ContDiff 2 g) (hY : VectorContDiff 2 Y) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target)
    (hgg : LocallyAllHolder (k + 2) alpha (cov2InChart g d) x)
    (hYg : LocallyAllHolder (k + 2) alpha (vectorInChart Y d) x) :
    LocallyAllHolder (k + 1) alpha (cov2InChart (lieTensor Y g) d) x := by
  have hgc (i j : Fin 4) : LocallyAllHolder (k + 2) alpha
      (fun y => cov2InChart g d y i j) x :=
    (hgg.clm (ContinuousLinearMap.proj i)).clm (ContinuousLinearMap.proj j)
  have hVc (p : Fin 4) : LocallyAllHolder (k + 2) alpha
      (fun y => vectorInChart Y d y p) x := hYg.clm (coordProj p)
  have hformula : LocallyAllHolder (k + 1) alpha (lieTensorInChart Y g d) x := by
    apply LocallyAllHolder.pi
    intro i
    apply LocallyAllHolder.pi
    intro j
    apply LocallyAllHolder.finset_sum Finset.univ
    intro p _
    exact ((scalar_mul_germ ((hVc p).mono (by omega)) (coordDeriv_germ (hgc i j) p)).add
      (scalar_mul_germ (coordDeriv_germ (hVc p) i) ((hgc p j).mono (by omega)))).add
      (scalar_mul_germ (coordDeriv_germ (hVc p) j) ((hgc i p).mono (by omega)))
  apply hformula.congr
  filter_upwards [(chartAt FourSpace d).open_target.mem_nhds hx] with y hy
  exact (lieTensor_coefficients g Y hg hY d y hy).symm

private theorem inverse_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff (k + 2) g)
    (d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace d).target) (i j : Fin 4) :
    LocallyAllHolder (k + 1) alpha (fun y => inverseMetricInChart g d y i j) x := by
  apply LocallyAllHolder.of_contDiffAt (k + 1) alpha ha
  exact HigherRegularity.inverse_coefficient_contDiffAt (k + 2) g hm hg d x hx i j

private theorem metric_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g : RawCov2 M) (hg : Cov2ContDiff (k + 2) g)
    (d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace d).target) (i j : Fin 4) :
    LocallyAllHolder (k + 1) alpha (fun y => cov2InChart g d y i j) x := by
  apply LocallyAllHolder.of_contDiffAt (k + 1) alpha ha
  exact HigherRegularity.tensor_coefficient_contDiffAt (k + 2) g hg d x hx i j

private theorem christoffel_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff (k + 2) g)
    (d : M) (x : FourSpace) (hx : x ∈ (chartAt FourSpace d).target) (l i j : Fin 4) :
    LocallyAllHolder k alpha (fun y => christoffelInChart g d y l i j) x := by
  apply scalar_mul_germ (LocallyAllHolder.const k alpha (1 / 2 : ℝ) x)
  apply LocallyAllHolder.finset_sum Finset.univ
  intro p _
  exact scalar_mul_germ ((inverse_germ k alpha ha g hm hg d x hx l p).mono (by omega))
    (((coordDeriv_germ (metric_germ k alpha ha g hg d x hx j p) i).add
      (coordDeriv_germ (metric_germ k alpha ha g hg d x hx i p) j)).sub
      (coordDeriv_germ (metric_germ k alpha ha g hg d x hx i j) p))

                                                                                  
                                                                              
theorem bianchi_native_germ (k : ℕ) (alpha : ℝ≥0) (ha : alpha ≤ 1)
    (g u : RawCov2 M) (hm : IsMetric g) (hg : Cov2ContDiff (k + 2) g)
    (hu : Cov2ContDiff (k + 1) u) (d : M) (x : FourSpace)
    (hx : x ∈ (chartAt FourSpace d).target)
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
    exact scalar_mul_germ (inverse_germ k alpha ha g hm hg d x hx a b) (huc a b)
  have hnabla (a b l : Fin 4) : LocallyAllHolder k alpha
      (fun y => nablaTensorInChart g u d y a b l) x := by
    have h1 : LocallyAllHolder k alpha (fun y => ∑ p : Fin 4,
        christoffelInChart g d y p a b * cov2InChart u d y p l) x := by
      apply LocallyAllHolder.finset_sum Finset.univ
      intro p _
      exact scalar_mul_germ (christoffel_germ k alpha ha g hm hg d x hx p a b)
        ((huc p l).mono (by omega))
    have h2 : LocallyAllHolder k alpha (fun y => ∑ p : Fin 4,
        christoffelInChart g d y p a l * cov2InChart u d y b p) x := by
      apply LocallyAllHolder.finset_sum Finset.univ
      intro p _
      exact scalar_mul_germ (christoffel_germ k alpha ha g hm hg d x hx p a l)
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
      exact scalar_mul_germ ((inverse_germ k alpha ha g hm hg d x hx a b).mono (by omega))
        (hnabla a b j)
    exact hdiv.neg.add (scalar_mul_germ (LocallyAllHolder.const k alpha (1 / 2 : ℝ) x)
      (coordDeriv_germ htrace j))
  apply hformula.congr
  filter_upwards [(chartAt FourSpace d).open_target.mem_nhds hx] with y hy
  symm
  exact (nativeBianchiDeltaStarChartRecovery M g hm
    (fun c => (hg c).of_le (by norm_cast; omega))).1 u
      (fun c => (hu c).of_le (by simp)) d y hy

section Global
variable [CompactSpace M]

                                                                                           
theorem lieTensor_holder (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (k : ℕ) (hk : k + 2 ≤ b.order) (g : RawCov2 M) (hg : MetricAdmissible C b g)
    (Y : RawVector M) (hY : C.VectorHolder (k + 2) b.exponent.value Y) :
    C.Cov2Holder (k + 1) b.exponent.value (lieTensor Y g) := by
  have ha : b.exponent.value ≤ 1 := b.exponent.lessThanOne.le
  have hpos : 0 < b.exponent.value := b.exponent.positive
  have hgn := TensorDescent.metricAdmissible_native_two C b g hg
  have hYn : VectorContDiff 2 Y := fun c =>
    (NativeRegularity.vectorContDiff_of_lifted_contDiff C (k + 2) Y hY.1 c).of_le
      (by norm_cast; omega)
  have hgh := pos_admissible_holder C b g hg (k + 2) hk
  apply cov2Holder_of_native_germs C (k + 1) b.exponent.value ha hpos
  intro d x hx
  exact lieTensor_native_germ k b.exponent.value g Y hgn hYn d x hx
    (cov2Holder_native_germ C (k + 2) b.exponent.value ha g hgh d x hx)
    (vectorHolder_native_germ C (k + 2) b.exponent.value ha Y hY d x hx)

                                                                              
                                                                               
theorem vectorOperator_holder (C : BoundedLocalCover M) (b : MetricCoefficientNumerics)
    (k : ℕ) (hk : k + 2 ≤ b.order) (ghat g : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (Y : RawVector M) (hY : C.VectorHolder (k + 2) b.exponent.value Y) :
    C.CovectorHolder k b.exponent.value (vectorOperator ghat g Y) := by
  have ha : b.exponent.value ≤ 1 := b.exponent.lessThanOne.le
  have hpos : 0 < b.exponent.value := b.exponent.positive
  have hgn := TensorDescent.metricAdmissible_native C b g hg (k + 2) hk
  have hhn := TensorDescent.metricAdmissible_native C b ghat hh (k + 2) hk
  have hYn := NativeRegularity.vectorContDiff_of_lifted_contDiff C (k + 2) Y hY.1
  have hLieN := HigherRegularity.lieTensor_contDiff_succ k g Y hgn hYn
  have hLieH := lieTensor_holder C b k hk g hg Y hY
  apply covectorHolder_of_native_germs C k b.exponent.value ha hpos
  intro d x hx
  exact bianchi_native_germ k b.exponent.value ha ghat (lieTensor Y g) hh.metric hhn hLieN d x hx
    (cov2Holder_native_germ C (k + 1) b.exponent.value ha (lieTensor Y g) hLieH d x hx)

end Global
end K24.Global.Holder20261026Operators.NativeHolderOperators
/- END Holder20261026.Operators.NativeHolderOperators -/

/- BEGIN Holder20261026.Operators.VectorOperators -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Topology

namespace K24.Global.Holder20261026Operators
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M]

                                                                               
                                                                         
                                                          
theorem projectedVectorOperator_holder_fields (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (k : ℕ) (hk : k + 2 ≤ b.order)
    (H : ℝ≥0) (rho : CircleAction M)
    (hact : HolderActionControl C b.exponent.value H (k + 2) rho)
    (ghat g : RawCov2 M) (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g) :
    Set.MapsTo (projectedVectorOperator rho ghat g)
      (vectorHolderPerp C (k + 2) b.exponent.value rho)
      (covectorHolderPerp C k b.exponent.value rho) ∧
    SectionLinearOn (vectorHolderPerp C (k + 2) b.exponent.value rho)
      (projectedVectorOperator rho ghat g) ∧
    SectionBoundedOn (vectorHolderPerp C (k + 2) b.exponent.value rho)
      (C.vectorENorm (k + 2) b.exponent.value) (C.covectorENorm k b.exponent.value)
      (projectedVectorOperator rho ghat g) := by
  apply projectedVectorOperator_fields_of_holder_mapping C b (k + 2) k (by omega) (by omega)
    H rho hact ghat g hh hg
  exact NativeHolderOperators.vectorOperator_holder C b k hk ghat g hh hg

                                                                           
                                                                              
theorem vectorOperator_holder_regularity (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (k : ℕ) (hk : k + 2 ≤ b.order)
    (rho : CircleAction M) (ghat g : RawCov2 M)
    (hh : MetricAdmissible C b ghat) (hg : MetricAdmissible C b g)
    (Y : RawVector M) (hY : C.VectorHolder (k + 2) b.exponent.value Y) :
    C.Cov2Holder (k + 1) b.exponent.value (lieTensor Y g) ∧
    C.CovectorHolder k b.exponent.value (vectorOperator ghat g Y) ∧
    CovectorHaarIntegrable rho (vectorOperator ghat g Y) := by
  exact ⟨NativeHolderOperators.lieTensor_holder C b k hk g hg Y hY,
    NativeHolderOperators.vectorOperator_holder C b k hk ghat g hh hg Y hY,
    NativeLinearity.vectorOperator_haarIntegrable_admissible C b rho ghat g hh hg
      (k + 2) (by omega) Y hY⟩

end K24.Global.Holder20261026Operators

/- END Holder20261026.Operators.VectorOperators -/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff
namespace K24.Global.Holder20261026Operators

def ActualHolderVectorOperators : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M]
    (C : BoundedLocalCover M) (b : MetricCoefficientNumerics) (k : ℕ),
    k + 2 ≤ b.order →
    ∀ (H : ℝ≥0) (rho : CircleAction M),
      HolderActionControl C b.exponent.value H (k + 2) rho →
    ∀ (ghat g : RawCov2 M),
      MetricAdmissible C b ghat → MetricAdmissible C b g →
      (∀ Y : RawVector M, C.VectorHolder (k + 2) b.exponent.value Y →
        C.Cov2Holder (k + 1) b.exponent.value (lieTensor Y g) ∧
        C.CovectorHolder k b.exponent.value (vectorOperator ghat g Y) ∧
        CovectorHaarIntegrable rho (vectorOperator ghat g Y)) ∧
      Set.MapsTo (projectedVectorOperator rho ghat g)
        (vectorHolderPerp C (k + 2) b.exponent.value rho)
        (covectorHolderPerp C k b.exponent.value rho) ∧
      SectionLinearOn (vectorHolderPerp C (k + 2) b.exponent.value rho)
        (projectedVectorOperator rho ghat g) ∧
      SectionBoundedOn (vectorHolderPerp C (k + 2) b.exponent.value rho)
        (C.vectorENorm (k + 2) b.exponent.value) (C.covectorENorm k b.exponent.value)
        (projectedVectorOperator rho ghat g)

end K24.Global.Holder20261026Operators

theorem solution : K24.Global.Holder20261026Operators.ActualHolderVectorOperators.{u} := by
  intro M _ _ _ _ C b k hk H rho hact ghat g hh hg
  exact ⟨K24.Global.Holder20261026Operators.vectorOperator_holder_regularity C b k hk rho ghat g hh hg,
    K24.Global.Holder20261026Operators.projectedVectorOperator_holder_fields C b k hk H rho hact ghat g hh hg⟩

set_option pp.universes true in
#check @solution
#print axioms solution
