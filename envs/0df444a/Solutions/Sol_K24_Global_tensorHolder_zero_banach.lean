-- Prove2me | solution 1 for K24.Global.tensorHolder_zero_banach
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:24:48.882201+00:00
-- url     : https://prove2.me/submissions/37f0a103-2fb4-4f8d-bbec-527b372087fb

import Definitions.Def_K24GlobalStatement


/- Standalone helper source: CoordinateZero. -/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Topology
open Filter

namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateHolderENorm_zero_eq (α : ℝ≥0) (s : Set E) (f : E → V) :
    coordinateHolderENorm 0 α s f =
      (⨆ x : s, (‖f x‖₊ : ℝ≥0∞)) + eHolderNorm α (fun x : s => f x) := by
  have hn : ∀ x : E, ‖iteratedFDerivWithin ℝ 0 f s x‖₊ = ‖f x‖₊ :=
    fun x => Subtype.ext (norm_iteratedFDerivWithin_zero (𝕜 := ℝ))
  have hh : eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ 0 f s x) =
      eHolderNorm α (fun x : s => f x) := by
    simp only [eHolderNorm, HolderWith, iteratedFDerivWithin_zero_eq_comp,
      Function.comp_apply, LinearIsometryEquiv.edist_map]
  simp [coordinateHolderENorm, derivativeENorm, hn, hh]

theorem enorm_le_coordinateHolderENorm_zero (α : ℝ≥0) (s : Set E)
    (f : E → V) (x : s) :
    (‖f x‖₊ : ℝ≥0∞) ≤ coordinateHolderENorm 0 α s f := by
  rw [coordinateHolderENorm_zero_eq]
  exact (le_iSup (fun y : s => (‖f y‖₊ : ℝ≥0∞)) x).trans le_self_add

theorem eHolderNorm_le_coordinateHolderENorm_zero (α : ℝ≥0) (s : Set E)
    (f : E → V) : eHolderNorm α (fun x : s => f x) ≤ coordinateHolderENorm 0 α s f := by
  rw [coordinateHolderENorm_zero_eq]
  exact le_add_self

theorem coordinateHolderENorm_zero_add_le (α : ℝ≥0) (s : Set E) (f g : E → V) :
    coordinateHolderENorm 0 α s (f + g) ≤
      coordinateHolderENorm 0 α s f + coordinateHolderENorm 0 α s g := by
  simp only [coordinateHolderENorm_zero_eq]
  have hu : (⨆ x : s, (‖(f + g) x‖₊ : ℝ≥0∞)) ≤
      (⨆ x : s, (‖f x‖₊ : ℝ≥0∞)) + (⨆ x : s, (‖g x‖₊ : ℝ≥0∞)) := by
    apply iSup_le
    intro x
    have hx : (‖(f + g) x‖₊ : ℝ≥0∞) ≤ (‖f x‖₊ : ℝ≥0∞) + (‖g x‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_add_le (f x) (g x)
    exact hx.trans
      (add_le_add (le_iSup (fun y : s => (‖f y‖₊ : ℝ≥0∞)) x)
        (le_iSup (fun y : s => (‖g y‖₊ : ℝ≥0∞)) x))
  exact (add_le_add hu eHolderNorm_add_le).trans_eq (by ac_rfl)

variable {X : Type*} [MetricSpace X]

theorem holderWith_of_eHolderNorm_le {α C : ℝ≥0} {f : X → V}
    (h : eHolderNorm α f ≤ (C : ℝ≥0∞)) : HolderWith C α f := by
  have hm : MemHolder α f := eHolderNorm_lt_top.mp (h.trans_lt ENNReal.coe_lt_top)
  apply hm.holderWith.mono
  exact_mod_cast (hm.coe_nnHolderNorm_eq_eHolderNorm ▸ h)

theorem eHolderNorm_le_of_pointwise_tendsto {α C : ℝ≥0} {f : ℕ → X → V} {g : X → V}
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ᶠ n in atTop, eHolderNorm α (f n) ≤ (C : ℝ≥0∞)) :
    eHolderNorm α g ≤ (C : ℝ≥0∞) := by
  apply HolderWith.eHolderNorm_le
  intro x y
  apply le_of_tendsto ((ht x).edist (ht y))
  exact hb.mono (fun n hn => holderWith_of_eHolderNorm_le hn x y)

end K24.Global

/- Standalone helper source: CoordinateComplete. -/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Topology
open Filter

namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateHolderENorm_zero_le_of_pointwise_tendsto
    {α C : ℝ≥0} {s : Set E} {f : ℕ → E → V} {g : E → V}
    (ht : ∀ x : s, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hb : ∀ᶠ n in atTop, coordinateHolderENorm 0 α s (f n) ≤ (C : ℝ≥0∞)) :
    coordinateHolderENorm 0 α s g ≤ (C : ℝ≥0∞) + C := by
  rw [coordinateHolderENorm_zero_eq]
  apply add_le_add
  · apply iSup_le
    intro x
    have h := le_of_tendsto (ENNReal.tendsto_ofReal (ht x).norm)
      (hb.mono (fun n hn => by
        simpa only [ofReal_norm, enorm] using
          (enorm_le_coordinateHolderENorm_zero α s (f n) x).trans hn))
    simpa only [ofReal_norm, enorm] using h
  · apply eHolderNorm_le_of_pointwise_tendsto ht
    exact hb.mono (fun n hn => (eHolderNorm_le_coordinateHolderENorm_zero α s (f n)).trans hn)

theorem coordinateHolderENorm_zero_pointwise_cauchy
    {α : ℝ≥0} {s : Set E} {f : ℕ → E → V}
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm 0 α s (f i - f j) < ENNReal.ofReal eps) (x : s) :
    CauchySeq (fun n => f n x) := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun i hi j hj => ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  simpa only [dist_eq_norm, ofReal_norm, enorm, Pi.sub_apply] using
    (enorm_le_coordinateHolderENorm_zero α s (f i - f j) x).trans_lt (hN i hi j hj)

theorem coordinateHolderENorm_zero_convergence
    {α : ℝ≥0} {s : Set E} {f : ℕ → E → V} {g : E → V}
    (ht : ∀ x : s, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm 0 α s (f i - f j) < ENNReal.ofReal eps) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      coordinateHolderENorm 0 α s (f i - g) < ENNReal.ofReal eps := by
  intro eps heps
  obtain ⟨N, hN⟩ := hc (eps / 4) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  let C : ℝ≥0 := ⟨eps / 4, by positivity⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal (eps / 4) := by
    exact (ENNReal.ofReal_coe_nnreal (p := C)).symm
  have hbound : coordinateHolderENorm 0 α s (f i - g) ≤ (C : ℝ≥0∞) + C := by
    apply coordinateHolderENorm_zero_le_of_pointwise_tendsto
      (f := fun j => f i - f j)
    · intro x
      exact tendsto_const_nhds.sub (ht x)
    · exact eventually_atTop.mpr ⟨N, fun j hj => by rw [hC]; exact (hN i hi j hj).le⟩
  apply hbound.trans_lt
  rw [hC, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_lt_ofReal_iff heps |>.mpr
  linarith

/-- Actual order-zero coefficient functions are sequentially complete in the
specified coordinate seminorm. The limit is a raw function, with the regularity
required by `BigHolderOn`; no function-space completion is introduced. -/
theorem coordinateHolder_zero_complete [CompleteSpace V]
    (α : ℝ≥0) (hα : 0 < α) (s : Set E) (f : ℕ → E → V)
    (hf : ∀ n, BigHolderOn 0 α s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm 0 α s (f i - f j) < ENNReal.ofReal eps) :
    ∃ g : E → V, BigHolderOn 0 α s g ∧
      (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        coordinateHolderENorm 0 α s (f i - g) < ENNReal.ofReal eps) := by
  classical
  have hp : ∀ x : s, ∃ y : V, Tendsto (fun n => f n x) atTop (𝓝 y) :=
    fun x => cauchySeq_tendsto_of_complete (coordinateHolderENorm_zero_pointwise_cauchy hc x)
  choose v hv using hp
  let g : E → V := fun x => if hx : x ∈ s then v ⟨x, hx⟩ else 0
  have ht : ∀ x : s, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    intro x
    simpa only [g, dif_pos x.property] using hv x
  have hconv := coordinateHolderENorm_zero_convergence ht hc
  have hb : ∃ C : ℝ≥0, ∀ᶠ n in atTop,
      coordinateHolderENorm 0 α s (f n) ≤ (C : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hc 1 zero_lt_one
    let R := 1 + coordinateHolderENorm 0 α s (f N)
    have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, (hf N).2.ne⟩
    refine ⟨R.toNNReal, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
    rw [ENNReal.coe_toNNReal hR]
    calc
      coordinateHolderENorm 0 α s (f n) =
          coordinateHolderENorm 0 α s ((f n - f N) + f N) := by rw [sub_add_cancel]
      _ ≤ coordinateHolderENorm 0 α s (f n - f N) + coordinateHolderENorm 0 α s (f N) :=
        coordinateHolderENorm_zero_add_le α s _ _
      _ ≤ R := add_le_add (by simpa using (hN n hn N le_rfl).le) le_rfl
  obtain ⟨C, hC⟩ := hb
  have hfinite : coordinateHolderENorm 0 α s g < ⊤ :=
    (coordinateHolderENorm_zero_le_of_pointwise_tendsto ht hC).trans_lt
      (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩)
  refine ⟨g, ⟨?_, hfinite⟩, hconv⟩
  apply contDiffOn_zero.mpr
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hm : MemHolder α (fun x : s => g x) := eHolderNorm_lt_top.mp
    ((eHolderNorm_le_coordinateHolderENorm_zero α s g).trans_lt hfinite)
  exact hm.holderWith.continuous hα

end K24.Global

/- Standalone helper source: CoordinateAlgebra. -/
set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Topology

namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateHolderENorm_zero_zero (α : ℝ≥0) (s : Set E) :
    coordinateHolderENorm 0 α s (0 : E → V) = 0 := by
  simp [coordinateHolderENorm_zero_eq]
  exact eHolderNorm_zero s α

theorem coordinateHolderENorm_zero_smul (α : ℝ≥0) (s : Set E) (c : ℝ) (f : E → V) :
    coordinateHolderENorm 0 α s (c • f) =
      ENNReal.ofReal |c| * coordinateHolderENorm 0 α s f := by
  rw [coordinateHolderENorm_zero_eq, coordinateHolderENorm_zero_eq]
  have hh : eHolderNorm α (fun x : s => (c • f) x) =
      (‖c‖₊ : ℝ≥0∞) * eHolderNorm α (fun x : s => f x) := eHolderNorm_smul c
  rw [hh]
  simp only [Pi.smul_apply, nnnorm_smul, ENNReal.coe_mul]
  rw [← ENNReal.mul_iSup, ← mul_add]
  have hn : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal |c| := by
    simpa only [enorm, Real.norm_eq_abs] using (ofReal_norm c).symm
  rw [hn]

theorem bigHolderOn_zero_of_finite {α : ℝ≥0} (hα : 0 < α) (s : Set E) (f : E → V)
    (hf : coordinateHolderENorm 0 α s f < ⊤) : BigHolderOn 0 α s f := by
  refine ⟨contDiffOn_zero.mpr (continuousOn_iff_continuous_domRestrict.mpr ?_), hf⟩
  exact (eHolderNorm_lt_top.mp
    ((eHolderNorm_le_coordinateHolderENorm_zero α s f).trans_lt hf)).holderWith.continuous hα

theorem coordinateHolderENorm_zero_definite_on {α : ℝ≥0} {s : Set E} {f : E → V}
    (hf : coordinateHolderENorm 0 α s f = 0) (x : s) : f x = 0 := by
  have hh := enorm_le_coordinateHolderENorm_zero α s f x
  rw [hf] at hh
  exact nnnorm_eq_zero.mp (ENNReal.coe_eq_zero.mp (le_antisymm hh zero_le))

end K24.Global

/- Standalone helper source: TensorZero. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) := by
  exact inferInstanceAs (FiniteDimensional ℝ FourSpace)

local instance tangentT2 (p : M) : T2Space (TangentSpace I4 p) := by
  exact inferInstanceAs (T2Space FourSpace)

def LocalCoverChart.cov2CoordinateLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    (TangentSpace I4 (c.lift x) →L[ℝ] (TangentSpace I4 (c.lift x) →L[ℝ] ℝ)) →ₗ[ℝ] Mat4 where
  toFun a := fun i j => a (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def LocalCoverChart.cov2ReconstructLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    Mat4 →ₗ[ℝ] (TangentSpace I4 (c.lift x) →L[ℝ]
      (TangentSpace I4 (c.lift x) →L[ℝ] ℝ)) where
  toFun A := bilinearPullback (matrixToBilinear A) (c.tangentMap x).symm.toContinuousLinearMap
  map_add' A B := by
    ext v w
    change matrixToBilinear (A + B) ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) =
      matrixToBilinear A ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) +
      matrixToBilinear B ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)
    simp [matrixToBilinear, Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' r A := by
    ext v w
    change matrixToBilinear (r • A) ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) =
      r * matrixToBilinear A ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)
    simp [matrixToBilinear, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem LocalCoverChart.cov2_reconstruct {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) (u : RawCov2 M) :
    c.cov2ReconstructLinearMap x (c.liftedCov2 u x) = u (c.lift x) := by
  have h := matrixToBilinear_recover (bilinearPullback (u (c.lift x)) (c.tangentMap x).toContinuousLinearMap)
  change (bilinearPullback (matrixToBilinear (c.liftedCov2 u x))
    (c.tangentMap x).symm.toContinuousLinearMap) = u (c.lift x)
  change matrixToBilinear (c.liftedCov2 u x) = _ at h
  rw [h]
  ext v w
  change u (c.lift x) ((c.tangentMap x) ((c.tangentMap x).symm v))
    ((c.tangentMap x) ((c.tangentMap x).symm w)) = u (c.lift x) v w
  rw [(c.tangentMap x).apply_symm_apply, (c.tangentMap x).apply_symm_apply]

@[simp] theorem LocalCoverChart.liftedCov2_sub {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCov2 M) :
    c.liftedCov2 (u - v) = c.liftedCov2 u - c.liftedCov2 v := rfl

@[simp] theorem LocalCoverChart.liftedCov2_add {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCov2 M) :
    c.liftedCov2 (u + v) = c.liftedCov2 u + c.liftedCov2 v := rfl

@[simp] theorem LocalCoverChart.liftedCov2_smul {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (r : ℝ) (u : RawCov2 M) :
    c.liftedCov2 (r • u) = r • c.liftedCov2 u := rfl

@[simp] theorem LocalCoverChart.liftedCov2_zero {F : LocalFiniteCover M}
    (c : LocalCoverChart F) : c.liftedCov2 (0 : RawCov2 M) = 0 := rfl

set_option maxHeartbeats 800000 in
theorem BoundedLocalCover.cov2Holder_zero_pointwise_cauchy
    (C : BoundedLocalCover M) (α : ℝ≥0) (f : ℕ → RawCov2 M)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm 0 α (f i - f j) < ENNReal.ofReal eps) (p : M) :
    CauchySeq (fun n => f n p) := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hcoord : CauchySeq (fun n => (C.chart ν).liftedCov2 (f n) x) := by
    apply coordinateHolderENorm_zero_pointwise_cauchy (s := (C.chart ν).innerDomain)
      (α := α) (x := ⟨x, hx⟩)
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hle := le_iSup (fun μ : C.Index => coordinateHolderENorm 0 α
      (C.chart μ).innerDomain ((C.chart μ).liftedCov2 (f i - f j))) ν
    simpa only [LocalCoverChart.liftedCov2_sub] using hle.trans_lt (hN i hi j hj)
  let r : Mat4 →L[ℝ] (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ]
      (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ] ℝ)) :=
    { (C.chart ν).cov2ReconstructLinearMap x with
      cont := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := Mat4)
        (F' := TangentSpace I4 ((C.chart ν).lift x) →L[ℝ]
          (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ] ℝ))
        ((C.chart ν).cov2ReconstructLinearMap x) }
  have hr : UniformContinuous r := ContinuousLinearMap.uniformContinuous
    (R₁ := ℝ) (R₂ := ℝ) (E₁ := Mat4)
    (E₂ := TangentSpace I4 ((C.chart ν).lift x) →L[ℝ]
      (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ] ℝ)) r
  have hh := hr.comp_cauchySeq hcoord
  change CauchySeq (fun n => (C.chart ν).cov2ReconstructLinearMap x
    ((C.chart ν).liftedCov2 (f n) x)) at hh
  simpa only [LocalCoverChart.cov2_reconstruct] using hh

theorem LocalCoverChart.liftedCov2_tendsto {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (f : ℕ → RawCov2 M) (u : RawCov2 M)
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) (x : FourSpace) :
    Tendsto (fun n => c.liftedCov2 (f n) x) atTop (𝓝 (c.liftedCov2 u x)) :=
  by
    change Tendsto (fun n => c.cov2CoordinateLinearMap x (f n (c.lift x))) atTop
      (𝓝 (c.cov2CoordinateLinearMap x (u (c.lift x))))
    exact ((c.cov2CoordinateLinearMap x).continuous_of_finiteDimensional.tendsto _).comp (ht (c.lift x))

end K24.Global

/- Standalone helper source: TensorNorm. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem BoundedLocalCover.cov2ENorm_zero_zero (C : BoundedLocalCover M) (α : ℝ≥0) :
    C.cov2ENorm 0 α 0 = 0 := by
  simp only [BoundedLocalCover.cov2ENorm, LocalCoverChart.liftedCov2_zero,
    coordinateHolderENorm_zero_zero]
  simp

theorem BoundedLocalCover.cov2ENorm_zero_add_le (C : BoundedLocalCover M) (α : ℝ≥0)
    (u v : RawCov2 M) : C.cov2ENorm 0 α (u + v) ≤ C.cov2ENorm 0 α u + C.cov2ENorm 0 α v := by
  apply iSup_le
  intro ν
  rw [LocalCoverChart.liftedCov2_add]
  exact (coordinateHolderENorm_zero_add_le α (C.chart ν).innerDomain _ _).trans
    (add_le_add (le_iSup (fun μ => coordinateHolderENorm 0 α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 u)) ν)
    (le_iSup (fun μ => coordinateHolderENorm 0 α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 v)) ν))

theorem BoundedLocalCover.cov2ENorm_zero_smul (C : BoundedLocalCover M) (α : ℝ≥0)
    (r : ℝ) (u : RawCov2 M) :
    C.cov2ENorm 0 α (r • u) = ENNReal.ofReal |r| * C.cov2ENorm 0 α u := by
  simp only [BoundedLocalCover.cov2ENorm, LocalCoverChart.liftedCov2_smul,
    coordinateHolderENorm_zero_smul, ENNReal.mul_iSup]

theorem BoundedLocalCover.cov2ENorm_zero_definite (C : BoundedLocalCover M) (α : ℝ≥0)
    (u : RawCov2 M) (hu : C.cov2ENorm 0 α u = 0) : u = 0 := by
  funext p
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hc : coordinateHolderENorm 0 α (C.chart ν).innerDomain ((C.chart ν).liftedCov2 u) = 0 := by
    apply le_antisymm _ zero_le
    exact (le_iSup (fun μ => coordinateHolderENorm 0 α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 u)) ν).trans_eq hu
  have hx0 := coordinateHolderENorm_zero_definite_on hc (⟨x, hx⟩ : (C.chart ν).innerDomain)
  have hrec := (C.chart ν).cov2_reconstruct x u
  rw [hx0, map_zero] at hrec
  exact hrec.symm

theorem BoundedLocalCover.cov2Holder_zero_of_finite (C : BoundedLocalCover M)
    {α : ℝ≥0} (hα : 0 < α) (u : RawCov2 M) (hu : C.cov2ENorm 0 α u < ⊤) :
    C.Cov2Holder 0 α u := by
  refine ⟨fun ν => ?_, hu⟩
  apply (bigHolderOn_zero_of_finite hα (C.chart ν).innerDomain _ ?_).1
  exact (le_iSup (fun μ => coordinateHolderENorm 0 α (C.chart μ).innerDomain
    ((C.chart μ).liftedCov2 u)) ν).trans_lt hu

theorem BoundedLocalCover.cov2ENorm_zero_le_of_pointwise_tendsto
    (C : BoundedLocalCover M) {α R : ℝ≥0} {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p)))
    (hb : ∀ᶠ n in atTop, C.cov2ENorm 0 α (f n) ≤ (R : ℝ≥0∞)) :
    C.cov2ENorm 0 α u ≤ (R : ℝ≥0∞) + R := by
  apply iSup_le
  intro ν
  apply coordinateHolderENorm_zero_le_of_pointwise_tendsto
    (fun x => (C.chart ν).liftedCov2_tendsto f u ht x)
  exact hb.mono (fun n hn =>
    (le_iSup (fun μ => coordinateHolderENorm 0 α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 (f n))) ν).trans hn)

theorem BoundedLocalCover.cov2ENorm_zero_convergence
    (C : BoundedLocalCover M) {α : ℝ≥0} {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm 0 α (f i - f j) < ENNReal.ofReal eps) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm 0 α (f i - u) < ENNReal.ofReal eps := by
  intro eps heps
  obtain ⟨N, hN⟩ := hc (eps / 4) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  let R : ℝ≥0 := ⟨eps / 4, by positivity⟩
  have hR : (R : ℝ≥0∞) = ENNReal.ofReal (eps / 4) := (ENNReal.ofReal_coe_nnreal (p := R)).symm
  have hb : C.cov2ENorm 0 α (f i - u) ≤ (R : ℝ≥0∞) + R := by
    apply C.cov2ENorm_zero_le_of_pointwise_tendsto (f := fun j => f i - f j)
    · intro p
      exact tendsto_const_nhds.sub (ht p)
    · exact eventually_atTop.mpr ⟨N, fun j hj => by rw [hR]; exact (hN i hi j hj).le⟩
  apply hb.trans_lt
  rw [hR, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_lt_ofReal_iff heps |>.mpr
  linarith

end K24.Global

/- Standalone helper source: TensorComplete. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

attribute [local instance] tangentFiniteDimensional tangentT2

def tensorEvaluationLinearMap (p : M) (v w : TangentSpace I4 p) :
    (TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ)) →ₗ[ℝ] ℝ where
  toFun a := a v w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isSymmetricCov2_of_pointwise_tendsto {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (hf : ∀ n, IsSymmetricCov2 (f n))
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) : IsSymmetricCov2 u := by
  intro p v w
  have h₁ : Tendsto (fun n => f n p v w) atTop (𝓝 (u p v w)) :=
    by
      change Tendsto (fun n => tensorEvaluationLinearMap p v w (f n p)) atTop
        (𝓝 (tensorEvaluationLinearMap p v w (u p)))
      exact ((tensorEvaluationLinearMap p v w).continuous_of_finiteDimensional.tendsto _).comp (ht p)
  have h₂ : Tendsto (fun n => f n p w v) atTop (𝓝 (u p w v)) :=
    by
      change Tendsto (fun n => tensorEvaluationLinearMap p w v (f n p)) atTop
        (𝓝 (tensorEvaluationLinearMap p w v (u p)))
      exact ((tensorEvaluationLinearMap p w v).continuous_of_finiteDimensional.tendsto _).comp (ht p)
  apply tendsto_nhds_unique h₁
  convert h₂ using 1
  exact funext (fun n => hf n p v w)

set_option maxHeartbeats 800000 in
theorem tensorHolder_zero_complete (C : BoundedLocalCover M) (α : ℝ≥0) (hα : 0 < α)
    (f : ℕ → RawCov2 M) (hf : ∀ n, f n ∈ tensorHolderSpace C 0 α)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm 0 α (f i - f j) < ENNReal.ofReal eps) :
    ∃ u ∈ tensorHolderSpace C 0 α, ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm 0 α (f i - u) < ENNReal.ofReal eps := by
  classical
  have hp : ∀ p : M, ∃ v : TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ),
      Tendsto (fun n => f n p) atTop (𝓝 v) := by
    intro p
    letI : CompleteSpace (TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ)) :=
      FiniteDimensional.complete ℝ _
    exact cauchySeq_tendsto_of_complete (C.cov2Holder_zero_pointwise_cauchy α f hc p)
  choose u hu using hp
  have hb : ∃ R : ℝ≥0, ∀ᶠ n in atTop, C.cov2ENorm 0 α (f n) ≤ (R : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hc 1 zero_lt_one
    let R := 1 + C.cov2ENorm 0 α (f N)
    have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, (hf N).2.2.ne⟩
    refine ⟨R.toNNReal, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
    rw [ENNReal.coe_toNNReal hR]
    calc
      C.cov2ENorm 0 α (f n) = C.cov2ENorm 0 α ((f n - f N) + f N) := by congr 1; ext p v w; simp
      _ ≤ C.cov2ENorm 0 α (f n - f N) + C.cov2ENorm 0 α (f N) := C.cov2ENorm_zero_add_le α _ _
      _ ≤ R := add_le_add (by simpa using (hN n hn N le_rfl).le) le_rfl
  obtain ⟨R, hR⟩ := hb
  have hfinite : C.cov2ENorm 0 α u < ⊤ :=
    (C.cov2ENorm_zero_le_of_pointwise_tendsto hu hR).trans_lt
      (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩)
  refine ⟨u, ⟨isSymmetricCov2_of_pointwise_tendsto (fun n => (hf n).1) hu,
    C.cov2Holder_zero_of_finite hα u hfinite⟩, C.cov2ENorm_zero_convergence hu hc⟩

end K24.Global

/- Standalone helper source: TensorBanach. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open scoped NNReal ENNReal

namespace K24.Global

universe u

/-- The actual symmetric tensor space measured by a bounded local cover is
Banach at order zero. The carrier and extended norm are exactly those used
by `HolderNaturalConclusions.tensor_target_banach`. -/
theorem tensorHolder_zero_banach_proof
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (C : BoundedLocalCover M) (α : ℝ≥0) (hα : 0 < α) :
    SectionBanachSpace (tensorHolderSpace C 0 α) (C.cov2ENorm 0 α) where
  zero_mem := ⟨fun _ _ _ => rfl,
    C.cov2Holder_zero_of_finite hα 0 (by rw [C.cov2ENorm_zero_zero]; exact ENNReal.zero_lt_top)⟩
  add_mem u hu v hv := by
    refine ⟨?_, C.cov2Holder_zero_of_finite hα _ ?_⟩
    · intro p x y
      change u p x y + v p x y = u p y x + v p y x
      rw [hu.1 p x y, hv.1 p x y]
    · exact (C.cov2ENorm_zero_add_le α u v).trans_lt (ENNReal.add_lt_top.mpr ⟨hu.2.2, hv.2.2⟩)
  smul_mem r u hu := by
    refine ⟨?_, C.cov2Holder_zero_of_finite hα _ ?_⟩
    · intro p x y
      change r * u p x y = r * u p y x
      rw [hu.1 p x y]
    · rw [C.cov2ENorm_zero_smul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2.2
  finite u hu := hu.2.2
  zero_norm := C.cov2ENorm_zero_zero α
  definite u _ hu := C.cov2ENorm_zero_definite α u hu
  triangle u _ v _ := C.cov2ENorm_zero_add_le α u v
  homogeneous r u _ := C.cov2ENorm_zero_smul α r u
  complete := tensorHolder_zero_complete C α hα

end K24.Global

universe u
theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
      (C : K24.Global.BoundedLocalCover M) (α : ℝ≥0), 0 < α →
      K24.Global.SectionBanachSpace (K24.Global.tensorHolderSpace C 0 α) (C.cov2ENorm 0 α) :=
  fun _ _ _ C α hα => K24.Global.tensorHolder_zero_banach_proof C α hα
