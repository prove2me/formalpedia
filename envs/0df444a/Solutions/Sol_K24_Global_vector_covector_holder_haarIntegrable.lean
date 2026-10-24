-- Prove2me | solution 1 for K24.Global.vector_covector_holder_haarIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:48:42.775563+00:00
-- url     : https://prove2.me/submissions/29479fb7-313b-4ecd-b25b-d959ae5b81a3

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

/- Inlined CoverSupport.lean; provenance in PROVENANCE.json. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.CoverRegularityProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}

omit [IsManifold I4 ∞ M] in
theorem contMDiffAt_lift (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  apply F.projectionSmooth.contMDiffAt.comp
  exact contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas c.coordinate_mem_atlas) (c.outerSubsetTarget hx)

theorem transition_smooth (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace q) ∘ c.lift) x := by
  apply ContMDiffAt.contDiffAt
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hq).comp x
    (contMDiffAt_lift c x hx)

theorem transition_derivative (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ∃ d : FourSpace ≃L[ℝ] FourSpace,
      HasFDerivAt ((chartAt FourSpace q) ∘ c.lift) (d : FourSpace →L[ℝ] FourSpace) x := by
  let e := chartAt FourSpace q
  let de := (mdifferentiable_chart (I := I4) q).mfderiv hq
  let d : FourSpace ≃L[ℝ] FourSpace := (c.tangentMap x).trans de
  have heq : (d : FourSpace →L[ℝ] FourSpace) =
      mfderiv I4 I4 (e ∘ c.lift) x := by
    rw [mfderiv_comp x ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
      ((contMDiffAt_lift c x hx).mdifferentiableAt (by simp))]
    have hc : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
      c.tangentMap_eq x hx
    rw [← hc]
    rfl
  refine ⟨d, ?_⟩
  rw [heq, mfderiv_eq_fderiv]
  exact ((transition_smooth c q x hx hq).differentiableAt (by simp)).hasFDerivAt

theorem local_inverse (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.innerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ∃ S : FourSpace → FourSpace,
      S (chartAt FourSpace q (c.lift x)) = x ∧
      ContDiffAt ℝ ∞ S (chartAt FourSpace q (c.lift x)) ∧
      (∀ᶠ y in 𝓝 (chartAt FourSpace q (c.lift x)), S y ∈ c.innerDomain) ∧
      (c.lift ∘ S =ᶠ[𝓝 (chartAt FourSpace q (c.lift x))] (chartAt FourSpace q).symm) := by
  have hxo : x ∈ c.outerDomain := c.closureInnerSubset (subset_closure hx)
  let f : FourSpace → FourSpace := (chartAt FourSpace q) ∘ c.lift
  have hf : ContDiffAt ℝ ∞ f x := transition_smooth c q x hxo hq
  obtain ⟨d, hd⟩ := transition_derivative c q x hxo hq
  have hd' : HasFDerivAt f (d : FourSpace →L[ℝ] FourSpace) x := hd
  let S := hf.localInverse hd' (by simp)
  have hSx : S (f x) = x := hf.localInverse_apply_image hd' (by simp)
  have hS : ContDiffAt ℝ ∞ S (f x) := hf.to_localInverse hd' (by simp)
  have hSt : Tendsto S (𝓝 (f x)) (𝓝 x) := by
    simpa only [hSx] using hS.continuousAt.tendsto
  have hinner : ∀ᶠ y in 𝓝 (f x), S y ∈ c.innerDomain :=
    hSt (c.innerOpen.mem_nhds hx)
  have hsource : ∀ᶠ y in 𝓝 (f x), c.lift (S y) ∈ (chartAt FourSpace q).source :=
    ((contMDiffAt_lift c x hxo).continuousAt.tendsto.comp hSt)
      ((chartAt FourSpace q).open_source.mem_nhds hq)
  have hright : ∀ᶠ y in 𝓝 (f x), f (S y) = y :=
    (hf.hasStrictFDerivAt' hd' (by simp)).eventually_right_inverse
  refine ⟨S, hSx, hS, hinner, ?_⟩
  filter_upwards [hsource, hright] with y hy hy'
  change c.lift (S y) = (chartAt FourSpace q).symm y
  calc
    c.lift (S y) = (chartAt FourSpace q).symm (f (S y)) :=
      ((chartAt FourSpace q).left_inv hy).symm
    _ = (chartAt FourSpace q).symm y := congrArg (chartAt FourSpace q).symm hy'

end K24.Global.CoverRegularityProof

/- Inlined CoverRegularity.lean; provenance in PROVENANCE.json. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Topology
open Filter
namespace K24.Global.VectorCovectorCoverRegularityProof
open CoverRegularityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}

def pullbackCovectorCoefficients (A : FourSpace → Fin 4 → ℝ) (S : FourSpace → FourSpace)
    (y : FourSpace) : Fin 4 → ℝ :=
  fun i => coefficientsToCovector (A (S y)) (fderiv ℝ S y (basisVector i))

theorem contDiffAt_pullbackCovectorCoefficients (A : FourSpace → Fin 4 → ℝ)
    (S : FourSpace → FourSpace) (y : FourSpace) (k : ℕ)
    (hA : ContDiffAt ℝ k A (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (pullbackCovectorCoefficients A S) y := by
  have hT : ContDiffAt ℝ k (fderiv ℝ S) y := hS.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hAS : ContDiffAt ℝ k (A ∘ S) y := hA.comp y (hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  apply contDiffAt_pi.mpr
  intro i
  simp only [pullbackCovectorCoefficients, coefficientsToCovector, sum_apply, smul_apply, smul_eq_mul]
  apply ContDiffAt.sum
  intro a _
  exact (contDiffAt_pi.mp hAS a).mul
    ((coordProj a).contDiff.contDiffAt.comp y (hT.clm_apply contDiffAt_const))

theorem pullbackCovectorCoefficients_eventually (c : LocalCoverChart F) (u : RawCovector M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hS : ContDiffAt ℝ ∞ S y)
    (hinner : ∀ᶠ z in 𝓝 y, S z ∈ c.innerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    pullbackCovectorCoefficients (c.liftedCovector u) S =ᶠ[𝓝 y] covectorInChart u q := by
  have hS1 : ContDiffAt ℝ 1 S y := hS.of_le (by simp)
  have hSnear := hS1.eventually (by simp)
  filter_upwards [hinner, heq.eventuallyEq_nhds, hSnear] with z hz heqz hSz
  have hzo : S z ∈ c.outerDomain := c.closureInnerSubset (subset_closure hz)
  have hDL := (contMDiffAt_lift c (S z) hzo).mdifferentiableAt (by simp)
  have hDS := (hSz.differentiableAt (by simp)).mdifferentiableAt
  have hder := heqz.mfderiv_eq (I := I4) (I' := I4)
  rw [mfderiv_comp z hDL hDS, mfderiv_eq_fderiv] at hder
  have hc : (c.tangentMap (S z)).toContinuousLinearMap =
      mfderiv I4 I4 c.lift (S z) := c.tangentMap_eq (S z) hzo
  rw [← hc] at hder
  have hvec (i : Fin 4) : c.tangentMap (S z) (fderiv ℝ S z (basisVector i)) =
      mfderiv I4 I4 (chartAt FourSpace q).symm z (basisVector i) :=
    congrArg (fun D : FourSpace →L[ℝ] FourSpace => D (basisVector i)) hder
  have hrec := coefficientsToCovector_recover
    ((u (c.lift (S z))).comp (c.tangentMap (S z)).toContinuousLinearMap)
  change coefficientsToCovector (c.liftedCovector u (S z)) = _ at hrec
  ext i
  change coefficientsToCovector (c.liftedCovector u (S z))
    (fderiv ℝ S z (basisVector i)) = _
  rw [hrec]
  change u (c.lift (S z)) (c.tangentMap (S z) (fderiv ℝ S z (basisVector i))) = _
  rw [hvec i]
  change u (c.lift (S z)) _ = u ((chartAt FourSpace q).symm z) _
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz.self_of_nhds]

def vectorCoefficients (A : FourSpace → FourSpace) (T S : FourSpace → FourSpace)
    (y : FourSpace) : FourSpace := fderiv ℝ T (S y) (A (S y))

theorem contDiffAt_vectorCoefficients (A T S : FourSpace → FourSpace)
    (y : FourSpace) (k : ℕ) (hA : ContDiffAt ℝ k A (S y))
    (hT : ContDiffAt ℝ ∞ T (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (vectorCoefficients A T S) y := by
  have hd : ContDiffAt ℝ k (fderiv ℝ T) (S y) :=
    hT.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hSk : ContDiffAt ℝ k S y := hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  exact (hd.comp y hSk).clm_apply (hA.comp y hSk)

theorem vectorCoefficients_eventually (c : LocalCoverChart F) (Y : RawVector M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hy : y ∈ (chartAt FourSpace q).target)
    (hinner : ∀ᶠ z in 𝓝 y, S z ∈ c.innerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    vectorCoefficients (c.liftedVector Y) ((chartAt FourSpace q) ∘ c.lift) S
      =ᶠ[𝓝 y] vectorInChart Y q := by
  filter_upwards [hinner, heq, (chartAt FourSpace q).open_target.mem_nhds hy] with z hz heqz hzt
  have hzo : S z ∈ c.outerDomain := c.closureInnerSubset (subset_closure hz)
  have hq : c.lift (S z) ∈ (chartAt FourSpace q).source := by
    rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz]
    exact (chartAt FourSpace q).map_target hzt
  have hd := mfderiv_comp (I := I4) (I' := I4) (I'' := I4) (S z)
    ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
    ((contMDiffAt_lift c (S z) hzo).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ ((chartAt FourSpace q) ∘ c.lift) (S z) (c.liftedVector Y (S z)) = _
  rw [hd]
  change mfderiv I4 I4 (chartAt FourSpace q) (c.lift (S z))
    (mfderiv I4 I4 c.lift (S z) (c.liftedVector Y (S z))) = _
  rw [c.differential_liftedVector Y (S z) hzo]
  change mfderiv I4 I4 (chartAt FourSpace q) (c.lift (S z)) (Y (c.lift (S z))) = _
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz]
  rfl
end K24.Global.VectorCovectorCoverRegularityProof

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]

theorem covectorContDiff_of_cover_coefficients (C : BoundedLocalCover M) (k : ℕ)
    (u : RawCovector M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain) :
    CovectorContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy⟩ := C.exists_inner_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]; exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, hinner, heq⟩ := CoverRegularityProof.local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]; exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS hinner heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCovector u) (S y) := by
    rw [hSx]; exact (hu ν x hx).contDiffAt ((C.chart ν).innerOpen.mem_nhds hx)
  have hpull := VectorCovectorCoverRegularityProof.contDiffAt_pullbackCovectorCoefficients _ S y k hA hS
  have hequal := VectorCovectorCoverRegularityProof.pullbackCovectorCoefficients_eventually
    (C.chart ν) u q S y hS hinner heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

theorem vectorContDiff_of_cover_coefficients (C : BoundedLocalCover M) (k : ℕ)
    (Y : RawVector M)
    (hY : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector Y) (C.chart ν).innerDomain) :
    VectorContDiff k Y := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy⟩ := C.exists_inner_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]; exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, hinner, heq⟩ := CoverRegularityProof.local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]; exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS hinner heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedVector Y) (S y) := by
    rw [hSx]; exact (hY ν x hx).contDiffAt ((C.chart ν).innerOpen.mem_nhds hx)
  have hT : ContDiffAt ℝ ∞ ((chartAt FourSpace q) ∘ (C.chart ν).lift) (S y) := by
    rw [hSx]
    exact CoverRegularityProof.transition_smooth (C.chart ν) q x
      ((C.chart ν).closureInnerSubset (subset_closure hx)) hq
  have hpull := VectorCovectorCoverRegularityProof.contDiffAt_vectorCoefficients _ _ S y k hA hT hS
  have hequal := VectorCovectorCoverRegularityProof.vectorCoefficients_eventually
    (C.chart ν) Y q S y hy hinner heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt
end K24.Global

/- Inlined HaarSupport.lean; provenance in PROVENANCE.json. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Topology
open Filter MeasureTheory
namespace K24.Global.VectorCovectorHaarProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
theorem continuousAt_action_differential_coordinates
    (rho : CircleAction M) (p : M) (t₀ : Circle) :
    ContinuousAt
      (inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
        (fun t => mfderiv I4 I4 (rho.act t) p) t₀) t₀ := by
  have h := rho.smooth.contMDiffAt.mfderiv rho.act (fun _ : Circle => p)
    (contMDiffAt_const : ContMDiffAt (𝓡 1) I4 0 (fun _ : Circle => p) t₀)
    (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)
  exact h.continuousAt

theorem action_differential_coordinates_eq
    (rho : CircleAction M) (p : M) (t₀ t : Circle)
    (ht : rho.act t p ∈ (chartAt FourSpace (rho.act t₀ p)).source) :
    inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
      (fun t => mfderiv I4 I4 (rho.act t) p) t₀ t =
      (mfderiv I4 I4 (chartAt FourSpace (rho.act t₀ p)) (rho.act t p)).comp
        (mfderiv I4 I4 (rho.act t) p) := by
  rw [inTangentCoordinates_eq_mfderiv_comp (mem_chart_source FourSpace p) ht]
  rw [mfderivWithin_range_extChartAt_symm, ContinuousLinearMap.comp_id]
  rfl

theorem continuous_actionPullbackCovector_eval
    (rho : CircleAction M) (u : RawCovector M)
    (hu : ∀ q : M, ContinuousOn (covectorInChart u q) (chartAt FourSpace q).target)
    (p : M) (v : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCovector rho t u p v) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let q := rho.act t₀ p
  let D := inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
    (fun t => mfderiv I4 I4 (rho.act t) p) t₀
  have hD : ContinuousAt D t₀ := continuousAt_action_differential_coordinates rho p t₀
  have hact : Continuous (fun t : Circle => rho.act t p) :=
    rho.smooth.continuous.comp (continuous_id.prodMk continuous_const)
  have hq : q ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hnear : ∀ᶠ t in 𝓝 t₀, rho.act t p ∈ (chartAt FourSpace q).source :=
    hact.continuousAt.preimage_mem_nhds ((chartAt FourSpace q).open_source.mem_nhds hq)
  have hchart : ContinuousAt (fun t : Circle => chartAt FourSpace q (rho.act t p)) t₀ :=
    ((chartAt FourSpace q).continuousAt hq).comp_of_eq hact.continuousAt rfl
  have hcoeff : ContinuousAt
      (fun t : Circle => covectorInChart u q (chartAt FourSpace q (rho.act t p))) t₀ := by
    apply ((hu q).continuousAt ((chartAt FourSpace q).open_target.mem_nhds
      ((chartAt FourSpace q).map_source hq))).comp_of_eq hchart rfl
  have hformula : ContinuousAt (fun t : Circle =>
      coefficientsToCovector (covectorInChart u q (chartAt FourSpace q (rho.act t p)))
        (D t v)) t₀ := by
    simp only [coefficientsToCovector, sum_apply, smul_apply, smul_eq_mul]
    apply tendsto_finsetSum
    intro a _ha
    exact ((continuous_apply a).continuousAt.comp hcoeff).mul
      ((coordProj a).continuous.continuousAt.comp (hD.clm_apply continuousAt_const))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  have hrec := covector_chart_recovery u q (rho.act t p) ht
  have hd := action_differential_coordinates_eq rho p t₀ t ht
  change D t = _ at hd
  rw [hd]
  dsimp only [actionPullbackCovector, pullbackCovector]
  change u (rho.act t p) (mfderiv I4 I4 (rho.act t) p v) = _
  rw [← hrec]
  rfl

theorem covectorHaarIntegrable_of_canonical_continuity
    (rho : CircleAction M) (u : RawCovector M)
    (hu : ∀ q : M, ContinuousOn (covectorInChart u q) (chartAt FourSpace q).target) :
    CovectorHaarIntegrable rho u := by
  intro c x _hx i
  exact Continuous.integrable_of_hasCompactSupport
    (continuous_actionPullbackCovector_eval rho u hu ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i)))
    (HasCompactSupport.of_compactSpace _)

theorem continuous_actionPullbackVector
    (rho : CircleAction M) (Y : RawVector M)
    (hY : ∀ q : M, ContinuousOn (vectorInChart Y q) (chartAt FourSpace q).target)
    (p : M) : Continuous (fun t : Circle => actionPullbackVector rho t Y p) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let f : Circle → M → M := fun t => rho.act t⁻¹
  let g : Circle → M := fun t => rho.act t p
  have hf : ContMDiff ((𝓡 1).prod I4) I4 ∞ (fun z : Circle × M => f z.1 z.2) :=
    rho.smooth.comp (contMDiff_fst.inv.prodMk contMDiff_snd)
  have hg : ContMDiff (𝓡 1) I4 ∞ g :=
    rho.smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have hcancel (t : Circle) : f t (g t) = p := by
    dsimp [f, g]
    rw [← rho.mul_act, inv_mul_cancel, rho.one_act]
  let D := inTangentCoordinates I4 I4 g (fun t => f t (g t))
    (fun t => mfderiv I4 I4 (f t) (g t)) t₀
  have hD : ContinuousAt D t₀ := by
    exact (hf.contMDiffAt.mfderiv f g (hg.contMDiffAt.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
      (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousAt
  let q := g t₀
  have hq : q ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hnear : ∀ᶠ t in 𝓝 t₀, g t ∈ (chartAt FourSpace q).source :=
    hg.continuous.continuousAt.preimage_mem_nhds ((chartAt FourSpace q).open_source.mem_nhds hq)
  have hchart : ContinuousAt (fun t : Circle => chartAt FourSpace q (g t)) t₀ :=
    ((chartAt FourSpace q).continuousAt hq).comp_of_eq hg.continuous.continuousAt rfl
  have hcoeff : ContinuousAt
      (fun t : Circle => vectorInChart Y q (chartAt FourSpace q (g t))) t₀ := by
    apply ((hY q).continuousAt ((chartAt FourSpace q).open_target.mem_nhds
      ((chartAt FourSpace q).map_source hq))).comp_of_eq hchart rfl
  let R := mfderiv I4 I4 (chartAt FourSpace p).symm (chartAt FourSpace p p)
  have hformula : ContinuousAt (fun t : Circle =>
      R (D t (vectorInChart Y q (chartAt FourSpace q (g t))))) t₀ :=
    R.continuous.continuousAt.comp (hD.clm_apply hcoeff)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  have hp : f t (g t) ∈ (chartAt FourSpace (f t₀ (g t₀))).source := by
    rw [hcancel, hcancel]; exact mem_chart_source FourSpace p
  have hd := inTangentCoordinates_eq_mfderiv_comp (I := I4) (I' := I4)
    (ϕ := fun t => mfderiv I4 I4 (f t) (g t)) ht hp
  change D t = _ at hd
  rw [hd]
  simp only [mfld_simps, mfderivWithin_univ]
  rw [hcancel t₀, hcancel t]
  have hrecq := (mdifferentiable_chart (I := I4) q).symm_comp_deriv ht
  have hrecp := (mdifferentiable_chart (I := I4) p).symm_comp_deriv (mem_chart_source FourSpace p)
  have hqvec : mfderiv I4 I4 (chartAt FourSpace q).symm (chartAt FourSpace q (g t))
      (vectorInChart Y q (chartAt FourSpace q (g t))) = Y (g t) := by
    dsimp only [vectorInChart]
    rw [(chartAt FourSpace q).left_inv ht]
    exact congrArg (fun L => L (Y (g t))) hrecq
  change actionPullbackVector rho t Y p =
    R (mfderiv I4 I4 (chartAt FourSpace p) p
      (mfderiv I4 I4 (f t) (g t)
        (mfderiv I4 I4 (chartAt FourSpace q).symm (chartAt FourSpace q (g t))
          (vectorInChart Y q (chartAt FourSpace q (g t))))))
  rw [hqvec]
  exact (congrArg (fun L => L (mfderiv I4 I4 (f t) (g t) (Y (g t)))) hrecp).symm

theorem vectorHaarIntegrable_of_canonical_continuity
    (rho : CircleAction M) (Y : RawVector M)
    (hY : ∀ q : M, ContinuousOn (vectorInChart Y q) (chartAt FourSpace q).target) :
    VectorHaarIntegrable rho Y := by
  intro c x _hx i
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact (coordProj i).continuous.comp
    ((mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm x)).continuous.comp
      (continuous_actionPullbackVector rho Y hY ((chartAt FourSpace c).symm x)))

theorem vectorHolder_haarIntegrable_proof
    (C : BoundedLocalCover M) (rho : CircleAction M) (k : ℕ) (alpha : ℝ≥0)
    (Y : RawVector M) (hY : C.VectorHolder k alpha Y) : VectorHaarIntegrable rho Y := by
  apply vectorHaarIntegrable_of_canonical_continuity rho Y
  intro q
  exact (vectorContDiff_of_cover_coefficients C k Y hY.1 q).continuousOn

theorem covectorHolder_haarIntegrable_proof
    (C : BoundedLocalCover M) (rho : CircleAction M) (k : ℕ) (alpha : ℝ≥0)
    (eta : RawCovector M) (heta : C.CovectorHolder k alpha eta) : CovectorHaarIntegrable rho eta := by
  apply covectorHaarIntegrable_of_canonical_continuity rho eta
  intro q
  exact (covectorContDiff_of_cover_coefficients C k eta heta.1 q).continuousOn
end K24.Global.VectorCovectorHaarProof

namespace K24.Global
universe u
theorem _root_.solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (rho : CircleAction M)
    (k : ℕ) (alpha : ℝ≥0),
    (∀ Y : RawVector M, C.VectorHolder k alpha Y → VectorHaarIntegrable rho Y) ∧
    (∀ eta : RawCovector M, C.CovectorHolder k alpha eta → CovectorHaarIntegrable rho eta) := by
  intro M _ _ _ C rho k alpha
  exact ⟨VectorCovectorHaarProof.vectorHolder_haarIntegrable_proof C rho k alpha,
    VectorCovectorHaarProof.covectorHolder_haarIntegrable_proof C rho k alpha⟩
end K24.Global
