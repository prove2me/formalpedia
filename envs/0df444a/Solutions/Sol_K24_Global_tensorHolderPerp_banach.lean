-- Prove2me | solution 1 for K24.Global.tensorHolderPerp_banach
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:43:19.187207+00:00
-- url     : https://prove2.me/submissions/b79a4d59-a00e-4028-a3af-e60a7ce4a93e

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

/- Inlined from prior checked Holder lower semicontinuity; source and excerpt hashes in PROVENANCE.json. -/
namespace K24.Global
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

/- Inlined from prior checked actual fiber coordinate reconstruction; source and excerpt hashes in PROVENANCE.json. -/
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

theorem LocalCoverChart.liftedCov2_tendsto {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (f : ℕ → RawCov2 M) (u : RawCov2 M)
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) (x : FourSpace) :
    Tendsto (fun n => c.liftedCov2 (f n) x) atTop (𝓝 (c.liftedCov2 u x)) :=
  by
    change Tendsto (fun n => c.cov2CoordinateLinearMap x (f n (c.lift x))) atTop
      (𝓝 (c.cov2CoordinateLinearMap x (u (c.lift x))))
    exact ((c.cov2CoordinateLinearMap x).continuous_of_finiteDimensional.tendsto _).comp (ht (c.lift x))

end K24.Global

/- Inlined from prior checked symmetry closure; source and excerpt hashes in PROVENANCE.json. -/
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

end K24.Global

/- Inlined from JetBounds; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff
open Filter

namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem derivativeENorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (α : ℝ≥0) (s : Set E) (f : E → V) :
    derivativeENorm j s f ≤ coordinateHolderENorm k α s f := by
  have hsum : derivativeENorm j s f ≤ ∑ l ∈ Finset.range (k + 1), derivativeENorm l s f :=
    Finset.single_le_sum (s := Finset.range (k + 1)) (f := fun l => derivativeENorm l s f)
      (a := j) (fun _ _ => zero_le) (Finset.mem_range.mpr (by omega))
  exact hsum.trans le_self_add

theorem derivative_enorm_le_coordinateHolderENorm (k j : ℕ) (hj : j ≤ k)
    (α : ℝ≥0) (s : Set E) (f : E → V) (x : s) :
    (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞) ≤ coordinateHolderENorm k α s f :=
  (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) x).trans
    (derivativeENorm_le_coordinateHolderENorm k j hj α s f)

theorem enorm_le_coordinateHolderENorm (k : ℕ) (α : ℝ≥0) (s : Set E)
    (f : E → V) (x : s) : (‖f x‖₊ : ℝ≥0∞) ≤ coordinateHolderENorm k α s f := by
  have h := derivative_enorm_le_coordinateHolderENorm k 0 (Nat.zero_le _) α s f x
  have hnorm : ‖iteratedFDerivWithin ℝ 0 f s x‖₊ = ‖f x‖₊ :=
    Subtype.ext (norm_iteratedFDerivWithin_zero (𝕜 := ℝ))
  rwa [hnorm] at h

theorem coordinateHolderENorm_pointwise_cauchy
    {k : ℕ} {α : ℝ≥0} {s : Set E} {f : ℕ → E → V}
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k α s (f i - f j) < ENNReal.ofReal eps) (x : s) :
    CauchySeq (fun n => f n x) := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun i hi j hj => ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  simpa only [dist_eq_norm, ofReal_norm, enorm, Pi.sub_apply] using
    (enorm_le_coordinateHolderENorm k α s (f i - f j) x).trans_lt (hN i hi j hj)

theorem uniformCauchySeqOn_iteratedFDerivWithin
    {k : ℕ} {α : ℝ≥0} {s : Set E} (hs : IsOpen s) {f : ℕ → E → V}
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k α s (f i - f j) < ENNReal.ofReal eps)
    (j : ℕ) (hj : j ≤ k) :
    UniformCauchySeqOn (fun n => iteratedFDerivWithin ℝ j (f n) s) atTop s := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun i hi l hl x hx => ?_⟩
  have hfi : ContDiffOn ℝ j (f i) s := (hf i).of_le (by exact_mod_cast hj)
  have hfl : ContDiffOn ℝ j (f l) s := (hf l).of_le (by exact_mod_cast hj)
  have hh := (derivative_enorm_le_coordinateHolderENorm k j hj α s (f i - f l) ⟨x, hx⟩).trans_lt (hN i hi l hl)
  rw [iteratedFDerivWithin_sub_apply (hfi x hx) (hfl x hx) hs.uniqueDiffOn hx] at hh
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  simpa only [dist_eq_norm, ofReal_norm, enorm] using hh

theorem exists_uniform_limit_of_uniformCauchySeqOn [CompleteSpace V]
    {s : Set E} {f : ℕ → E → V} (hc : UniformCauchySeqOn f atTop s) :
    ∃ g : E → V, TendstoUniformlyOn f g atTop s := by
  classical
  have hp : ∀ x : s, ∃ v : V, Tendsto (fun n => f n x) atTop (𝓝 v) :=
    fun x => cauchySeq_tendsto_of_complete (hc.cauchySeq x.property)
  choose v hv using hp
  let g : E → V := fun x => if hx : x ∈ s then v ⟨x, hx⟩ else 0
  refine ⟨g, hc.tendstoUniformlyOn_of_tendsto (fun x hx => ?_)⟩
  simpa only [g, dif_pos hx] using hv ⟨x, hx⟩

theorem exists_uniform_iteratedFDerivWithin_limits [CompleteSpace V]
    {k : ℕ} {α : ℝ≥0} {s : Set E} (hs : IsOpen s) {f : ℕ → E → V}
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k α s (f i - f j) < ENNReal.ofReal eps) :
    ∀ j ≤ k, ∃ g : E → E [×j]→L[ℝ] V,
      TendstoUniformlyOn (fun n => iteratedFDerivWithin ℝ j (f n) s) g atTop s := by
  intro j hj
  exact exists_uniform_limit_of_uniformCauchySeqOn
    (uniformCauchySeqOn_iteratedFDerivWithin hs hf hc j hj)

end K24.Global

/- Inlined from JetLimit; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff
open Filter

namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A coordinate Holder-Cauchy sequence with an actual pointwise limit has
that limit's actual derivatives through order k, uniformly on the open set. -/
theorem coordinateHolder_limit_derivatives
    {k : ℕ} {α : ℝ≥0} {s : Set E} (hs : IsOpen s) {f : ℕ → E → V} {g : E → V}
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k α s (f i - f j) < ENNReal.ofReal eps)
    (ht : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ k g s ∧ ∀ j ≤ k,
      TendstoUniformlyOn (fun n => iteratedFDerivWithin ℝ j (f n) s)
        (iteratedFDerivWithin ℝ j g s) atTop s := by
  classical
  choose D hD using exists_uniform_iteratedFDerivWithin_limits hs hf hc
  have hstep : ∀ j (hj : j < k) (x : E), x ∈ s →
      HasFDerivAt (D j hj.le)
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V)
          (D (j + 1) (by omega) x)) x := by
    intro j hj x hx
    let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V
    apply hasFDerivAt_of_tendstoUniformlyOn hs
      (e.isometry.uniformContinuous.comp_tendstoUniformlyOn (hD (j + 1) (by omega)))
      (fun n y hy => ?_) (fun y hy => (hD j hj.le).tendsto_at hy) hx
    have hd := (((hf n).differentiableOn_iteratedFDerivWithin
      (by exact_mod_cast hj) hs.uniqueDiffOn y hy).hasFDerivWithinAt).hasFDerivAt (hs.mem_nhds hy)
    simpa only [fderivWithin_iteratedFDerivWithin, Function.comp_apply] using hd
  have heq : ∀ j (hj : j ≤ k), Set.EqOn (D j hj) (iteratedFDerivWithin ℝ j g s) s := by
    intro j
    induction j with
    | zero =>
      intro hj x hx
      have hlim := ((continuousMultilinearCurryFin0 ℝ E V).symm.isometry.continuous.tendsto (g x)).comp (ht x hx)
      exact tendsto_nhds_unique ((hD 0 hj).tendsto_at hx) hlim
    | succ j ih =>
      intro hj x hx
      have hj' : j < k := by omega
      have hd := (hstep j hj' x hx).hasFDerivWithinAt.fderivWithin (hs.uniqueDiffOn x hx)
      rw [fderivWithin_congr (ih hj'.le) (ih hj'.le hx)] at hd
      apply (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V).injective
      exact hd.symm
  refine ⟨?_, fun j hj => ?_⟩
  · apply (contDiffOn_nat_iff_continuousOn_differentiableOn hs.uniqueDiffOn).mpr
    constructor
    · intro j hj
      apply ((hD j hj).continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall
        (fun n => (hf n).continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hs.uniqueDiffOn)))).congr
      exact fun x hx => (heq j hj hx).symm
    · intro j hj
      have hd : DifferentiableOn ℝ (D j hj.le) s :=
        fun x hx => (hstep j hj x hx).differentiableAt.differentiableWithinAt
      exact hd.congr (fun x hx => (heq j hj.le hx).symm)
  · apply (uniformCauchySeqOn_iteratedFDerivWithin hs hf hc j hj).tendstoUniformlyOn_of_tendsto
    intro x hx
    rw [← heq j hj hx]
    exact (hD j hj).tendsto_at hx

end K24.Global

/- Inlined from HigherNorm; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff
open Filter

namespace K24.Global
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateHolderENorm_zero (k : ℕ) (α : ℝ≥0) (s : Set E) :
    coordinateHolderENorm k α s (0 : E → V) = 0 := by
  simp [coordinateHolderENorm, derivativeENorm, iteratedFDerivWithin_zero]
  exact eHolderNorm_zero s α

theorem coordinateHolderENorm_add_le {k : ℕ} (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) {f g : E → V} (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) :
    coordinateHolderENorm k α s (f + g) ≤
      coordinateHolderENorm k α s f + coordinateHolderENorm k α s g := by
  have hd : ∀ j ≤ k, derivativeENorm j s (f + g) ≤ derivativeENorm j s f + derivativeENorm j s g := by
    intro j hj
    apply iSup_le
    intro x
    have hfi := hf.of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
    have hgi := hg.of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
    rw [iteratedFDerivWithin_add_apply (hfi x x.property) (hgi x x.property) hs.uniqueDiffOn x.property]
    have hnorm : (‖iteratedFDerivWithin ℝ j f s x + iteratedFDerivWithin ℝ j g s x‖₊ : ℝ≥0∞) ≤
        (‖iteratedFDerivWithin ℝ j f s x‖₊ : ℝ≥0∞) + (‖iteratedFDerivWithin ℝ j g s x‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_add_le (iteratedFDerivWithin ℝ j f s x) (iteratedFDerivWithin ℝ j g s x)
    exact hnorm.trans (add_le_add
      (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j f s y‖₊ : ℝ≥0∞)) x)
      (le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ j g s y‖₊ : ℝ≥0∞)) x))
  have hh : (fun x : s => iteratedFDerivWithin ℝ k (f + g) s x) =
      (fun x : s => iteratedFDerivWithin ℝ k f s x) + (fun x : s => iteratedFDerivWithin ℝ k g s x) := by
    funext x
    exact iteratedFDerivWithin_add_apply (hf x x.property) (hg x x.property) hs.uniqueDiffOn x.property
  unfold coordinateHolderENorm
  rw [hh]
  have hsum := Finset.sum_le_sum (s := Finset.range (k + 1)) (fun j hj => hd j (by simpa using (Finset.mem_range.mp hj)))
  rw [Finset.sum_add_distrib] at hsum
  exact (add_le_add hsum eHolderNorm_add_le).trans_eq (by ac_rfl)

set_option maxHeartbeats 200000 in
theorem coordinateHolderENorm_smul {k : ℕ} (α : ℝ≥0) {s : Set E}
    (hs : IsOpen s) {f : E → V} (hf : ContDiffOn ℝ k f s) (c : ℝ) :
    coordinateHolderENorm k α s (c • f) = ENNReal.ofReal |c| * coordinateHolderENorm k α s f := by
  have hn : (‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal |c| := by
    simpa only [enorm, Real.norm_eq_abs] using (ofReal_norm c).symm
  have hd : ∀ j ≤ k, derivativeENorm j s (c • f) = ENNReal.ofReal |c| * derivativeENorm j s f := by
    intro j hj
    unfold derivativeENorm
    rw [ENNReal.mul_iSup]
    apply iSup_congr
    intro x
    rw [iteratedFDerivWithin_const_smul_apply ((hf.of_le (by exact_mod_cast hj)) x x.property) hs.uniqueDiffOn x.property,
      nnnorm_smul, ENNReal.coe_mul, hn]
  have hh : (fun x : s => iteratedFDerivWithin ℝ k (c • f) s x) =
      c • (fun x : s => iteratedFDerivWithin ℝ k f s x) := by
    funext x
    exact iteratedFDerivWithin_const_smul_apply (hf x x.property) hs.uniqueDiffOn x.property
  unfold coordinateHolderENorm
  have hh' : eHolderNorm α (c • (fun x : s => iteratedFDerivWithin ℝ k f s x)) =
      (‖c‖₊ : ℝ≥0∞) * eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k f s x) := eHolderNorm_smul c
  rw [hh, hh', hn]
  have hsum : (∑ j ∈ Finset.range (k + 1), derivativeENorm j s (c • f)) =
      ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal |c| * derivativeENorm j s f := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hd j (by simpa using (Finset.mem_range.mp hj))
  rw [hsum, ← Finset.mul_sum, ← mul_add]

theorem coordinateHolderENorm_le_of_derivative_tendsto
    {k : ℕ} {α R : ℝ≥0} {s : Set E} {f : ℕ → E → V} {g : E → V}
    (ht : ∀ j ≤ k, ∀ x : s, Tendsto (fun n => iteratedFDerivWithin ℝ j (f n) s x)
      atTop (𝓝 (iteratedFDerivWithin ℝ j g s x)))
    (hb : ∀ᶠ n in atTop, coordinateHolderENorm k α s (f n) ≤ (R : ℝ≥0∞)) :
    coordinateHolderENorm k α s g ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
  have hd : ∀ j ≤ k, derivativeENorm j s g ≤ (R : ℝ≥0∞) := by
    intro j hj
    apply iSup_le
    intro x
    have h := le_of_tendsto (ENNReal.tendsto_ofReal (ht j hj x).norm)
      (hb.mono (fun n hn => by
        simpa only [ofReal_norm, enorm] using
          (derivative_enorm_le_coordinateHolderENorm k j hj α s (f n) x).trans hn))
    simpa only [ofReal_norm, enorm] using h
  have hh : eHolderNorm α (fun x : s => iteratedFDerivWithin ℝ k g s x) ≤ (R : ℝ≥0∞) := by
    apply eHolderNorm_le_of_pointwise_tendsto (ht k le_rfl)
    exact hb.mono (fun n hn => le_add_self.trans hn)
  have hsum : (∑ j ∈ Finset.range (k + 1), derivativeENorm j s g) ≤
      ∑ _j ∈ Finset.range (k + 1), (R : ℝ≥0∞) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hd j (by simpa using (Finset.mem_range.mp hj))
  have h := add_le_add hsum hh
  change coordinateHolderENorm k α s g ≤ _ at h
  convert h using 1
  simp [nsmul_eq_mul, Nat.cast_add, add_mul, add_assoc, two_mul]

end K24.Global

/- Inlined from TensorHigherNorm; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem BoundedLocalCover.cov2ENorm_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    C.cov2ENorm k α 0 = 0 := by
  simp only [BoundedLocalCover.cov2ENorm, LocalCoverChart.liftedCov2_zero,
    coordinateHolderENorm_zero]
  simp

theorem BoundedLocalCover.cov2ENorm_add_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u v : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain)
    (hv : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 v) (C.chart ν).innerDomain) :
    C.cov2ENorm k α (u + v) ≤ C.cov2ENorm k α u + C.cov2ENorm k α v := by
  apply iSup_le
  intro ν
  rw [LocalCoverChart.liftedCov2_add]
  exact (coordinateHolderENorm_add_le α (C.chart ν).innerOpen (hu ν) (hv ν)).trans
    (add_le_add (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 u)) ν)
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 v)) ν))

theorem BoundedLocalCover.cov2ENorm_smul (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (r : ℝ) (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain) :
    C.cov2ENorm k α (r • u) = ENNReal.ofReal |r| * C.cov2ENorm k α u := by
  unfold BoundedLocalCover.cov2ENorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro ν
  rw [LocalCoverChart.liftedCov2_smul]
  exact coordinateHolderENorm_smul α (C.chart ν).innerOpen (hu ν) r

theorem BoundedLocalCover.cov2ENorm_definite (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawCov2 M) (hu : C.cov2ENorm k α u = 0) : u = 0 := by
  funext p
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hn : (‖(C.chart ν).liftedCov2 u x‖₊ : ℝ≥0∞) ≤ C.cov2ENorm k α u :=
    (enorm_le_coordinateHolderENorm k α (C.chart ν).innerDomain ((C.chart ν).liftedCov2 u) ⟨x, hx⟩).trans
      (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain ((C.chart μ).liftedCov2 u)) ν)
  rw [hu] at hn
  have hx0 : (C.chart ν).liftedCov2 u x = 0 :=
    nnnorm_eq_zero.mp (ENNReal.coe_eq_zero.mp (le_antisymm hn zero_le))
  have hrec := (C.chart ν).cov2_reconstruct x u
  rw [hx0, map_zero] at hrec
  exact hrec.symm

set_option maxHeartbeats 800000 in
theorem BoundedLocalCover.cov2Holder_pointwise_cauchy
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) (f : ℕ → RawCov2 M)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k α (f i - f j) < ENNReal.ofReal eps) (p : M) :
    CauchySeq (fun n => f n p) := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hcoord : CauchySeq (fun n => (C.chart ν).liftedCov2 (f n) x) := by
    apply coordinateHolderENorm_pointwise_cauchy (s := (C.chart ν).innerDomain)
      (k := k) (α := α) (x := ⟨x, hx⟩)
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hle := le_iSup (fun μ : C.Index => coordinateHolderENorm k α
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

theorem BoundedLocalCover.cov2ENorm_le_of_derivative_tendsto
    (C : BoundedLocalCover M) {k : ℕ} {α R : ℝ≥0} {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain x)))
    (hb : ∀ᶠ n in atTop, C.cov2ENorm k α (f n) ≤ (R : ℝ≥0∞)) :
    C.cov2ENorm k α u ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
  apply iSup_le
  intro ν
  apply coordinateHolderENorm_le_of_derivative_tendsto (ht ν)
  exact hb.mono (fun n hn =>
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCov2 (f n))) ν).trans hn)

end K24.Global

/- Inlined from TensorHigherComplete; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
attribute [local instance] tangentFiniteDimensional tangentT2

theorem BoundedLocalCover.cov2ENorm_convergence
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (hf : ∀ n, ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain)
    (ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain x)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k α (f i - f j) < ENNReal.ofReal eps) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm k α (f i - u) < ENNReal.ofReal eps := by
  intro eps heps
  let m : ℝ := (k + 2 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * m)) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  let R : ℝ≥0 := ⟨eps / (2 * m), by positivity⟩
  have hR : (R : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * m)) := (ENNReal.ofReal_coe_nnreal (p := R)).symm
  have hb : C.cov2ENorm k α (f i - u) ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
    apply C.cov2ENorm_le_of_derivative_tendsto (f := fun n => f i - f n)
    · intro ν j hj x
      simp only [LocalCoverChart.liftedCov2_sub]
      have hfi := (hf i ν).of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      have hfu := (hu ν).of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      have heq : (fun n => iteratedFDerivWithin ℝ j
          ((C.chart ν).liftedCov2 (f i) - (C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain x) =
          (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 (f i)) (C.chart ν).innerDomain x -
            iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain x) := by
        funext n
        exact iteratedFDerivWithin_sub_apply (hfi x x.property)
          (((hf n ν).of_le (by exact_mod_cast hj)) x x.property) (C.chart ν).innerOpen.uniqueDiffOn x.property
      rw [heq, iteratedFDerivWithin_sub_apply (hfi x x.property) (hfu x x.property)
        (C.chart ν).innerOpen.uniqueDiffOn x.property]
      exact tendsto_const_nhds.sub (ht ν j hj x)
    · exact eventually_atTop.mpr ⟨N, fun n hn => by rw [hR]; exact (hN i hi n hn).le⟩
  apply hb.trans_lt
  have hsmall : ((k + 2 : ℕ) : ℝ≥0∞) * (R : ℝ≥0∞) = ENNReal.ofReal (eps / 2) := by
    rw [hR, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    change m * (eps / (2 * m)) = eps / 2
    field_simp
  rw [hsmall]
  apply ENNReal.ofReal_lt_ofReal_iff heps |>.mpr
  linarith

/-- Completeness of the original symmetric tensor sections in the actual
full order-k Holder norm, with all regularity derived at the limit. -/
theorem tensorHolder_complete (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (f : ℕ → RawCov2 M) (hf : ∀ n, f n ∈ tensorHolderSpace C k α)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k α (f i - f j) < ENNReal.ofReal eps) :
    ∃ u ∈ tensorHolderSpace C k α, ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm k α (f i - u) < ENNReal.ofReal eps := by
  classical
  have hp : ∀ p : M, ∃ v : TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ),
      Tendsto (fun n => f n p) atTop (𝓝 v) := by
    intro p
    letI : CompleteSpace (TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ)) :=
      FiniteDimensional.complete ℝ _
    exact cauchySeq_tendsto_of_complete (C.cov2Holder_pointwise_cauchy k α f hc p)
  choose u hu using hp
  have hlocal : ∀ ν : C.Index,
      ContDiffOn ℝ k ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain ∧ ∀ j ≤ k,
      TendstoUniformlyOn (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain)
        (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain) atTop (C.chart ν).innerDomain := by
    intro ν
    apply coordinateHolder_limit_derivatives (α := α) (C.chart ν).innerOpen
      (fun n => (hf n).2.1 ν)
    · intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      have hle := le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
        ((C.chart μ).liftedCov2 (f i - f j))) ν
      simpa only [LocalCoverChart.liftedCov2_sub] using hle.trans_lt (hN i hi j hj)
    · intro x _
      exact (C.chart ν).liftedCov2_tendsto f u hu x
  have ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCov2 u) (C.chart ν).innerDomain x)) :=
    fun ν j hj x => ((hlocal ν).2 j hj).tendsto_at x.property
  have hb : ∃ R : ℝ≥0, ∀ᶠ n in atTop, C.cov2ENorm k α (f n) ≤ (R : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hc 1 zero_lt_one
    let R := 1 + C.cov2ENorm k α (f N)
    have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, (hf N).2.2.ne⟩
    refine ⟨R.toNNReal, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
    rw [ENNReal.coe_toNNReal hR]
    calc
      C.cov2ENorm k α (f n) = C.cov2ENorm k α ((f n - f N) + f N) := by congr 1; ext p v w; simp
      _ ≤ C.cov2ENorm k α (f n - f N) + C.cov2ENorm k α (f N) :=
        C.cov2ENorm_add_le k α _ _
          (fun ν => by
            rw [LocalCoverChart.liftedCov2_sub]
            convert ((hf n).2.1 ν).sub ((hf N).2.1 ν) using 1
            ext x; rfl)
          (hf N).2.1
      _ ≤ R := add_le_add (by simpa using (hN n hn N le_rfl).le) le_rfl
  obtain ⟨R, hR⟩ := hb
  have hfinite : C.cov2ENorm k α u < ⊤ :=
    (C.cov2ENorm_le_of_derivative_tendsto ht hR).trans_lt
      (ENNReal.mul_lt_top (by simp) ENNReal.coe_lt_top)
  refine ⟨u, ⟨isSymmetricCov2_of_pointwise_tendsto (fun n => (hf n).1) hu,
    ⟨fun ν => (hlocal ν).1, hfinite⟩⟩,
    C.cov2ENorm_convergence k α (fun n => (hf n).2.1) (fun ν => (hlocal ν).1) ht hc⟩

end K24.Global

/- Inlined from TensorHigherBanach; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open scoped NNReal ENNReal ContDiff Matrix.Norms.Elementwise

namespace K24.Global
universe u

/-- The original symmetric tensor Holder section space is Banach at every
finite order, with its actual cover supremum of full coordinate norms. -/
theorem tensorHolder_banach_proof
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    SectionBanachSpace (tensorHolderSpace C k α) (C.cov2ENorm k α) where
  zero_mem := ⟨fun _ _ _ => rfl, ⟨fun ν => by
      rw [LocalCoverChart.liftedCov2_zero]
      convert (contDiffOn_const : ContDiffOn ℝ k (fun _ : FourSpace => (0 : Mat4)) (C.chart ν).innerDomain) using 1
      ext x; rfl,
    by rw [C.cov2ENorm_zero]; exact ENNReal.zero_lt_top⟩⟩
  add_mem u hu v hv := by
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro p x y
      change u p x y + v p x y = u p y x + v p y x
      rw [hu.1 p x y, hv.1 p x y]
    · intro ν
      rw [LocalCoverChart.liftedCov2_add]
      convert (hu.2.1 ν).add (hv.2.1 ν) using 1
      ext x; rfl
    · exact (C.cov2ENorm_add_le k α u v hu.2.1 hv.2.1).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hu.2.2, hv.2.2⟩)
  smul_mem r u hu := by
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro p x y
      change r * u p x y = r * u p y x
      rw [hu.1 p x y]
    · intro ν
      rw [LocalCoverChart.liftedCov2_smul]
      convert (hu.2.1 ν).const_smul r using 1
      ext x; rfl
    · rw [C.cov2ENorm_smul k α r u hu.2.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2.2
  finite u hu := hu.2.2
  zero_norm := C.cov2ENorm_zero k α
  definite u _ hu := C.cov2ENorm_definite k α u hu
  triangle u hu v hv := C.cov2ENorm_add_le k α u v hu.2.1 hv.2.1
  homogeneous r u hu := C.cov2ENorm_smul k α r u hu.2.1
  complete := tensorHolder_complete C k α

end K24.Global

/- Inlined Haar-integrability bridge from frozen Solution SHA
 f7fc326db98679a3bcc145cdb1fd51b8c9194e93c1fc82ca423cf337d2685e91. -/

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


theorem matrixToBilinear_apply (A : Mat4) (v w : FourSpace) :
    matrixToBilinear A v w = ∑ a, ∑ b, v a * A a b * w b := by
  simp [matrixToBilinear, coordProj, mul_assoc]

def pullbackCoefficients (A : FourSpace → Mat4) (S : FourSpace → FourSpace)
    (y : FourSpace) : Mat4 :=
  fun i j => matrixToBilinear (A (S y))
    (fderiv ℝ S y (basisVector i)) (fderiv ℝ S y (basisVector j))

theorem contDiffAt_pullbackCoefficients (A : FourSpace → Mat4)
    (S : FourSpace → FourSpace) (y : FourSpace) (k : ℕ)
    (hA : ContDiffAt ℝ k A (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (pullbackCoefficients A S) y := by
  have hT : ContDiffAt ℝ k (fderiv ℝ S) y := hS.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hAS : ContDiffAt ℝ k (A ∘ S) y := hA.comp y (hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  have hV (i a : Fin 4) :
      ContDiffAt ℝ k (fun z => (fderiv ℝ S z (basisVector i)) a) y :=
    (coordProj a).contDiff.contDiffAt.comp y (hT.clm_apply contDiffAt_const)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [pullbackCoefficients, matrixToBilinear_apply]
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact ((hV i a).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hAS a) b)).mul (hV j b)

omit [IsManifold I4 ∞ M] in
theorem pullbackCoefficients_eventually (c : LocalCoverChart F) (u : RawCov2 M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hS : ContDiffAt ℝ ∞ S y)
    (hinner : ∀ᶠ z in 𝓝 y, S z ∈ c.innerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    pullbackCoefficients (c.liftedCov2 u) S =ᶠ[𝓝 y] cov2InChart u q := by
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
  have hmat := matrixToBilinear_recover
    (bilinearPullback (u (c.lift (S z))) (c.tangentMap (S z)).toContinuousLinearMap)
  change matrixToBilinear (c.liftedCov2 u (S z)) = _ at hmat
  ext i j
  change matrixToBilinear (c.liftedCov2 u (S z))
    (fderiv ℝ S z (basisVector i)) (fderiv ℝ S z (basisVector j)) = _
  rw [hmat]
  simp only [bilinearPullback_apply]
  change u (c.lift (S z)) (c.tangentMap (S z) (fderiv ℝ S z (basisVector i)))
    (c.tangentMap (S z) (fderiv ℝ S z (basisVector j))) = _
  rw [hvec i, hvec j]
  change u (c.lift (S z)) _ _ = u ((chartAt FourSpace q).symm z) _ _
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz.self_of_nhds]

end K24.Global.CoverRegularityProof

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem cov2ContDiff_of_cover_coefficients (C : BoundedLocalCover M) (k : ℕ)
    (u : RawCov2 M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCov2 u)
      (C.chart ν).innerDomain) : Cov2ContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy⟩ := C.exists_inner_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]
    exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, hinner, heq⟩ := CoverRegularityProof.local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]
    exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS hinner heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCov2 u) (S y) := by
    rw [hSx]
    exact (hu ν x hx).contDiffAt ((C.chart ν).innerOpen.mem_nhds hx)
  have hpull := CoverRegularityProof.contDiffAt_pullbackCoefficients _ S y k hA hS
  have hequal := CoverRegularityProof.pullbackCoefficients_eventually (C.chart ν) u q S y
    hS hinner heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

theorem cov2ContDiff_of_cov2Holder (C : BoundedLocalCover M) (k : ℕ)
    (alpha : ℝ≥0) (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) :
    Cov2ContDiff k u := cov2ContDiff_of_cover_coefficients C k u hu.1

theorem cov2ContDiff_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff b.order g := by
  apply cov2ContDiff_of_cover_coefficients C b.order g
  intro ν
  exact (hg.regularity ν).1.mono (fun x hx =>
    (C.chart ν).closureInnerSubset (subset_closure hx))

theorem cov2ContDiff_one_of_metricAdmissible (C : BoundedLocalCover M)
    (b : MetricCoefficientNumerics) (g : RawCov2 M) (hg : MetricAdmissible C b g) :
    Cov2ContDiff 1 g := by
  intro q
  exact (cov2ContDiff_of_metricAdmissible C b g hg q).of_le
    (by exact_mod_cast (show 1 ≤ b.order from le_trans (by omega) b.order_ge_two))

theorem cov2ContDiff_one_of_tensorHolderSpace (C : BoundedLocalCover M)
    (alpha : ℝ≥0) (u : RawCov2 M) (hu : u ∈ tensorHolderSpace C 2 alpha) :
    Cov2ContDiff 1 u := by
  intro q
  exact (cov2ContDiff_of_cov2Holder C 2 alpha u hu.2 q).of_le (by norm_num)

end K24.Global


namespace K24.Global.HolderHaarProof
open MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuousAt_action_differential_coordinates
    (rho : CircleAction M) (p : M) (t₀ : Circle) :
    ContinuousAt
      (inTangentCoordinates I4 I4 (fun _ : Circle => p) (fun t => rho.act t p)
        (fun t => mfderiv I4 I4 (rho.act t) p) t₀) t₀ := by
  have h := rho.smooth.contMDiffAt.mfderiv rho.act (fun _ : Circle => p)
    (contMDiffAt_const : ContMDiffAt (𝓡 1) I4 0 (fun _ : Circle => p) t₀)
    (by simp : (0 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))
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

theorem continuous_actionPullbackCov2_eval
    (rho : CircleAction M) (u : RawCov2 M)
    (hu : ∀ q : M, ContinuousOn (cov2InChart u q) (chartAt FourSpace q).target)
    (p : M) (v w : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCov2 rho t u p v w) := by
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
      (fun t : Circle => cov2InChart u q (chartAt FourSpace q (rho.act t p))) t₀ := by
    apply ((hu q).continuousAt ((chartAt FourSpace q).open_target.mem_nhds
      ((chartAt FourSpace q).map_source hq))).comp_of_eq hchart rfl
  have hformula : ContinuousAt (fun t : Circle =>
      matrixToBilinear (cov2InChart u q (chartAt FourSpace q (rho.act t p)))
        (D t v) (D t w)) t₀ := by
    simp only [matrixToBilinear, sum_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    apply tendsto_finsetSum
    intro a _ha
    apply tendsto_finsetSum
    intro b _hb
    exact ((coordProj a).continuous.continuousAt.comp (hD.clm_apply continuousAt_const)).mul
      (((continuous_apply b).continuousAt.comp
        ((continuous_apply a).continuousAt.comp hcoeff)).mul
        ((coordProj b).continuous.continuousAt.comp (hD.clm_apply continuousAt_const)))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hnear] with t ht
  have hrec := cov2_chart_recovery u q (rho.act t p) ht
  have hd := action_differential_coordinates_eq rho p t₀ t ht
  change D t = _ at hd
  rw [hd]
  dsimp only [actionPullbackCov2, pullbackCov2]
  change u (rho.act t p) (mfderiv I4 I4 (rho.act t) p v)
    (mfderiv I4 I4 (rho.act t) p w) = _
  rw [← hrec]
  rfl

theorem cov2HaarIntegrable_of_canonical_continuity
    (rho : CircleAction M) (u : RawCov2 M)
    (hu : ∀ q : M, ContinuousOn (cov2InChart u q) (chartAt FourSpace q).target) :
    Cov2HaarIntegrable rho u := by
  intro c x _hx i j
  exact Continuous.integrable_of_hasCompactSupport
    (continuous_actionPullbackCov2_eval rho u hu ((chartAt FourSpace c).symm x)
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
      (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j)))
    (HasCompactSupport.of_compactSpace _)

theorem cov2Holder_haarIntegrable_proof
    (C : BoundedLocalCover M) (rho : CircleAction M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) : Cov2HaarIntegrable rho u := by
  apply cov2HaarIntegrable_of_canonical_continuity rho u
  intro q
  exact (cov2ContDiff_of_cov2Holder C k alpha u hu q).continuousOn

theorem tensorHolderSpace_haarIntegrable
    (C : BoundedLocalCover M) (rho : CircleAction M) (k : ℕ) (alpha : ℝ≥0) :
    ∀ u ∈ tensorHolderSpace C k alpha, Cov2HaarIntegrable rho u := by
  intro u hu
  exact cov2Holder_haarIntegrable_proof C rho k alpha u hu.2

end K24.Global.HolderHaarProof


set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option maxRecDepth 1000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal Topology Matrix.Norms.Elementwise

namespace K24.Global.PerpProof

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

theorem sectionBanach_kernel {S : Set X} {nx : X → ℝ≥0∞} (hS : SectionBanachSpace S nx)
    (A : X → Y) (hA : SectionLinearOn S A)
    (hclosed : ∀ (f : ℕ → X), (∀ n, f n ∈ S ∧ A (f n) = 0) →
      ∀ v ∈ S, (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        nx (f i - v) < ENNReal.ofReal eps) → A v = 0) :
    SectionBanachSpace {u | u ∈ S ∧ A u = 0} nx where
  zero_mem := ⟨hS.zero_mem, hA.1⟩
  add_mem u hu v hv := ⟨hS.add_mem u hu.1 v hv.1, by rw [hA.2.1 u hu.1 v hv.1, hu.2, hv.2, add_zero]⟩
  smul_mem c u hu := ⟨hS.smul_mem c u hu.1, by rw [hA.2.2 c u hu.1, hu.2, smul_zero]⟩
  finite u hu := hS.finite u hu.1
  zero_norm := hS.zero_norm
  definite u hu := hS.definite u hu.1
  triangle u hu v hv := hS.triangle u hu.1 v hv.1
  homogeneous c u hu := hS.homogeneous c u hu.1
  complete f hf hc := by
    obtain ⟨v, hv, hconv⟩ := hS.complete f (fun n => (hf n).1) hc
    exact ⟨v, ⟨hv, hclosed f hf v hv hconv⟩, hconv⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

local instance tangentNormedAddCommGroup (p : M) : NormedAddCommGroup (TangentSpace I4 p) :=
  inferInstanceAs (NormedAddCommGroup FourSpace)
local instance tangentNormedSpace (p : M) : NormedSpace ℝ (TangentSpace I4 p) :=
  inferInstanceAs (NormedSpace ℝ FourSpace)
local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) :=
  inferInstanceAs (FiniteDimensional ℝ FourSpace)
local instance tangentCompleteSpace (p : M) : CompleteSpace (TangentSpace I4 p) :=
  inferInstanceAs (CompleteSpace FourSpace)

/-- A fixed point is controlled by one actual inner-cover chart. -/
theorem coordinate_value_bound (k : ℕ) (alpha : ℝ≥0) (s : Set FourSpace)
    (f : FourSpace → Mat4) (x : s) :
    (‖f x‖₊ : ℝ≥0∞) ≤ coordinateHolderENorm k alpha s f := by
  have h0 : (‖f x‖₊ : ℝ≥0∞) ≤ derivativeENorm 0 s f := by
    have hn : ‖iteratedFDerivWithin ℝ 0 f s x‖₊ = ‖f x‖₊ :=
      Subtype.ext (norm_iteratedFDerivWithin_zero (𝕜 := ℝ))
    exact hn ▸ le_iSup (fun y : s => (‖iteratedFDerivWithin ℝ 0 f s y‖₊ : ℝ≥0∞)) x
  exact h0.trans ((Finset.single_le_sum (fun j hj => (zero_le : 0 ≤ derivativeENorm j s f))
    (by simp : 0 ∈ Finset.range (k + 1))).trans le_self_add)

def cov2ReconstructCLM (c p : M) : Mat4 →L[ℝ]
    (TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := cov2FromChartAt c p
    map_add' := by
      intro a b
      ext v w
      simp [cov2FromChartAt, matrixToBilinear, add_mul, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext v w
      simp [cov2FromChartAt, matrixToBilinear, Finset.mul_sum, mul_left_comm, mul_assoc] }

variable [IsManifold I4 ∞ M]

theorem haar_fiber_integrable {rho : CircleAction M} {u : RawCov2 M}
    (hu : Cov2HaarIntegrable rho u) (p : M) :
    Integrable (fun t => actionPullbackCov2 rho t u p) circleHaar := by
  have hc : Integrable (fun t => cov2InChart (actionPullbackCov2 rho t u)
      p (chartAt FourSpace p p)) circleHaar :=
    Integrable.of_eval (fun i => Integrable.of_eval (hu p _
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)) i))
  have hr : ∀ t, cov2ReconstructCLM p p
      (cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p)) =
      actionPullbackCov2 rho t u p := fun t =>
    cov2_chart_recovery _ p p (mem_chart_source FourSpace p)
  simpa only [hr] using (cov2ReconstructCLM p p).integrable_comp hc

theorem mean_eq_fiberIntegral (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (p : M) :
    cov2Pi0 rho u p = ∫ t, actionPullbackCov2 rho t u p ∂circleHaar := by
  have hc := fun i j => hu p _
    ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)) i j
  have hci := Integrable.of_eval (fun i => Integrable.of_eval (hc i))
  change cov2ReconstructCLM p p
    (fun i j => ∫ t, cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p) i j ∂circleHaar) = _
  have heq : (fun i j => ∫ t, cov2InChart (actionPullbackCov2 rho t u)
      p (chartAt FourSpace p p) i j ∂circleHaar) =
      ∫ t, cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p) ∂circleHaar := by
    funext i j
    rw [eval_integral (fun i => Integrable.of_eval (hc i)), eval_integral (hc i)]
  rw [heq, ← (cov2ReconstructCLM p p).integral_comp_comm hci]
  apply integral_congr_ae
  filter_upwards [] with t
  exact cov2_chart_recovery _ p p (mem_chart_source FourSpace p)


omit [IsManifold I4 ∞ M] in
theorem actionPullback_add (rho : CircleAction M) (t : Circle) (u v : RawCov2 M) :
    actionPullbackCov2 rho t (u + v) = actionPullbackCov2 rho t u + actionPullbackCov2 rho t v := by
  ext p a b
  simp [actionPullbackCov2, pullbackCov2]

omit [IsManifold I4 ∞ M] in
theorem actionPullback_smul (rho : CircleAction M) (t : Circle) (c : ℝ) (u : RawCov2 M) :
    actionPullbackCov2 rho t (c • u) = c • actionPullbackCov2 rho t u := by
  ext p a b
  simp [actionPullbackCov2, pullbackCov2]

theorem haar_mean_linear {S : Set (RawCov2 M)} {nx : RawCov2 M → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (rho : CircleAction M)
    (hInt : ∀ u ∈ S, Cov2HaarIntegrable rho u) : SectionLinearOn S (cov2Pi0 rho) := by
  refine ⟨?_, ?_, ?_⟩
  · funext p
    rw [mean_eq_fiberIntegral rho 0 (hInt 0 hS.zero_mem)]
    simp [actionPullbackCov2, pullbackCov2, bilinearPullback]
  · intro u hu v hv
    funext p
    rw [mean_eq_fiberIntegral rho (u + v) (hInt (u + v) (hS.add_mem u hu v hv))]
    simp only [actionPullback_add, Pi.add_apply]
    rw [integral_add (haar_fiber_integrable (hInt u hu) p) (haar_fiber_integrable (hInt v hv) p),
      ← mean_eq_fiberIntegral rho u (hInt u hu), ← mean_eq_fiberIntegral rho v (hInt v hv)]
  · intro c u hu
    funext p
    rw [mean_eq_fiberIntegral rho (c • u) (hInt (c • u) (hS.smul_mem c u hu))]
    simp only [actionPullback_smul, Pi.smul_apply, integral_smul]
    rw [← mean_eq_fiberIntegral rho u (hInt u hu)]

omit [IsManifold I4 ∞ M] in
theorem sub_mem {S : Set (RawCov2 M)} {nx : RawCov2 M → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) {u v : RawCov2 M} (hu : u ∈ S) (hv : v ∈ S) :
    u - v ∈ S := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hS.add_mem u hu ((-1 : ℝ) • v) (hS.smul_mem (-1) v hv)

theorem haar_mean_sub {S : Set (RawCov2 M)} {nx : RawCov2 M → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (rho : CircleAction M)
    (hInt : ∀ u ∈ S, Cov2HaarIntegrable rho u) {u v : RawCov2 M} (hu : u ∈ S) (hv : v ∈ S) :
    cov2Pi0 rho (u - v) = cov2Pi0 rho u - cov2Pi0 rho v := by
  have hlin := haar_mean_linear hS rho hInt
  calc
    cov2Pi0 rho (u - v) = cov2Pi0 rho (u + (-1 : ℝ) • v) := by rw [neg_one_smul, sub_eq_add_neg]
    _ = cov2Pi0 rho u + cov2Pi0 rho ((-1 : ℝ) • v) := hlin.2.1 u hu _ (hS.smul_mem (-1) v hv)
    _ = cov2Pi0 rho u - cov2Pi0 rho v := by rw [hlin.2.2 (-1) v hv, neg_one_smul, sub_eq_add_neg]


omit [IsManifold I4 ∞ M] in
/-- A finite, point-dependent evaluation bound; no uniform atlas bound is needed. -/
theorem exists_fiber_value_bound (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) (p : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : RawCov2 M, C.cov2ENorm k alpha u < ⊤ →
      ‖u p‖ ≤ K * (C.cov2ENorm k alpha u).toReal := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  let r : Mat4 →L[ℝ] (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ]
      (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ] ℝ)) :=
    LinearMap.toContinuousLinearMap ((C.chart ν).cov2ReconstructLinearMap x)
  refine ⟨‖r‖, norm_nonneg _, ?_⟩
  intro u hu
  have hm : ‖(C.chart ν).liftedCov2 u x‖ ≤ (C.cov2ENorm k alpha u).toReal := by
    have hle : (‖(C.chart ν).liftedCov2 u x‖₊ : ℝ≥0∞) ≤ C.cov2ENorm k alpha u :=
      (coordinate_value_bound k alpha _ ((C.chart ν).liftedCov2 u) ⟨x, hx⟩).trans
        (le_iSup (fun μ => coordinateHolderENorm k alpha (C.chart μ).innerDomain
          ((C.chart μ).liftedCov2 u)) ν)
    exact_mod_cast ENNReal.toReal_mono hu.ne hle
  calc
    ‖u ((C.chart ν).lift x)‖ = ‖r ((C.chart ν).liftedCov2 u x)‖ := by
      change _ = ‖(C.chart ν).cov2ReconstructLinearMap x ((C.chart ν).liftedCov2 u x)‖
      rw [LocalCoverChart.cov2_reconstruct]
    _ ≤ ‖r‖ * ‖(C.chart ν).liftedCov2 u x‖ := r.le_opNorm _
    _ ≤ ‖r‖ * (C.cov2ENorm k alpha u).toReal := mul_le_mul_of_nonneg_left hm (norm_nonneg _)

theorem haar_mean_fiber_bound (C : BoundedLocalCover M) (k : ℕ) (alpha H : ℝ≥0)
    (rho : CircleAction M) (hAction : HolderActionControl C alpha H k rho)
    (p : M) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ u : RawCov2 M, C.cov2ENorm k alpha u < ⊤ →
      ‖u p‖ ≤ K * (C.cov2ENorm k alpha u).toReal)
    (u : RawCov2 M) (hu : C.Cov2Holder k alpha u) (hInt : Cov2HaarIntegrable rho u) :
    ‖cov2Pi0 rho u p‖ ≤ K * H * (C.cov2ENorm k alpha u).toReal := by
  rw [mean_eq_fiberIntegral rho u hInt]
  have ht (t : Circle) : ‖actionPullbackCov2 rho t u p‖ ≤
      K * H * (C.cov2ENorm k alpha u).toReal := by
    have hA := hAction.tensor k le_rfl t u hu
    have hnorm : (C.cov2ENorm k alpha (actionPullbackCov2 rho t u)).toReal ≤
        (H : ℝ) * (C.cov2ENorm k alpha u).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hu.2.ne) hA.2
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
    exact (hbound _ hA.1.2).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnorm hK)
  simpa using norm_integral_le_of_norm_le_const (μ := circleHaar)
    (f := fun t => actionPullbackCov2 rho t u p) (Filter.Eventually.of_forall ht)

theorem haar_kernel_closed (C : BoundedLocalCover M) (k : ℕ) (alpha H : ℝ≥0)
    (rho : CircleAction M) (hAction : HolderActionControl C alpha H k rho)
    (hInt : ∀ u ∈ tensorHolderSpace C k alpha, Cov2HaarIntegrable rho u)
    (f : ℕ → RawCov2 M)
    (hf : ∀ n, f n ∈ tensorHolderSpace C k alpha ∧ cov2Pi0 rho (f n) = 0)
    (v : RawCov2 M) (hv : v ∈ tensorHolderSpace C k alpha)
    (hconv : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm k alpha (f i - v) < ENNReal.ofReal eps) :
    cov2Pi0 rho v = 0 := by
  have hS := tensorHolder_banach_proof C k alpha
  funext p
  obtain ⟨K, hK, hbound⟩ := exists_fiber_value_bound C k alpha p
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro eps heps
  have hKH : 0 ≤ K * (H : ℝ) := mul_nonneg hK H.coe_nonneg
  have hden : 0 < K * (H : ℝ) + 1 := by positivity
  have hsmall : 0 < eps / (K * (H : ℝ) + 1) := div_pos heps hden
  obtain ⟨N, hN⟩ := hconv _ hsmall
  have hdiff := sub_mem hS (hf N).1 hv
  have hReal : (C.cov2ENorm k alpha (f N - v)).toReal < eps / (K * (H : ℝ) + 1) :=
    ENNReal.toReal_lt_of_lt_ofReal (hN N le_rfl)
  have hb := haar_mean_fiber_bound C k alpha H rho hAction p K hK hbound
    (f N - v) hdiff.2 (hInt _ hdiff)
  rw [haar_mean_sub hS rho hInt (hf N).1 hv, (hf N).2] at hb
  simp only [zero_sub, Pi.neg_apply, norm_neg] at hb
  have hle : K * (H : ℝ) * (C.cov2ENorm k alpha (f N - v)).toReal ≤
      (K * (H : ℝ) + 1) * (eps / (K * (H : ℝ) + 1)) := by
    apply mul_le_mul
    · linarith
    · exact hReal.le
    · exact ENNReal.toReal_nonneg
    · positivity
  have heq : (K * (H : ℝ) + 1) * (eps / (K * (H : ℝ) + 1)) = eps :=
    mul_div_cancel₀ eps hden.ne'
  simpa only [zero_add, heq] using hb.trans hle

theorem tensorHolderPerp_banach_conditional (C : BoundedLocalCover M) (k : ℕ)
    (alpha H : ℝ≥0) (rho : CircleAction M)
    (hAction : HolderActionControl C alpha H k rho)
    (hInt : ∀ u ∈ tensorHolderSpace C k alpha, Cov2HaarIntegrable rho u) :
    SectionBanachSpace (tensorHolderPerp C k alpha rho) (C.cov2ENorm k alpha) := by
  exact sectionBanach_kernel (tensorHolder_banach_proof C k alpha) (cov2Pi0 rho)
    (haar_mean_linear (tensorHolder_banach_proof C k alpha) rho hInt)
    (haar_kernel_closed C k alpha H rho hAction hInt)

end K24.Global.PerpProof




namespace K24.Global.PerpProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem holderActionControl_mono (C : BoundedLocalCover M) (alpha H : ℝ≥0)
    (rho : CircleAction M) {k order : ℕ} (h : HolderActionControl C alpha H order rho)
    (hk : k ≤ order) : HolderActionControl C alpha H k rho where
  tensor j hj := h.tensor j (hj.trans hk)
  covector j hj := h.covector j (hj.trans hk)
  vector j hj := h.vector j (hj.trans hk)

theorem tensorHolderPerp_banach_proof (C : BoundedLocalCover M) (k : ℕ)
    (alpha H : ℝ≥0) (rho : CircleAction M)
    (hAction : HolderActionControl C alpha H k rho) :
    SectionBanachSpace (tensorHolderPerp C k alpha rho) (C.cov2ENorm k alpha) :=
  tensorHolderPerp_banach_conditional C k alpha H rho hAction
    (HolderHaarProof.tensorHolderSpace_haarIntegrable C rho k alpha)

end K24.Global.PerpProof

universe u

theorem solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    [IsManifold K24.Global.I4 ∞ M] (C : K24.Global.BoundedLocalCover M) (k : ℕ)
    (alpha : K24.Global.HolderExponent) (H : ℝ≥0) (rho : K24.Global.CircleAction M),
    K24.Global.HolderActionControl C alpha.value H k rho →
    K24.Global.SectionBanachSpace (K24.Global.tensorHolderPerp C k alpha.value rho)
      (C.cov2ENorm k alpha.value) := by
  intro M _ _ _ C k alpha H rho hAction
  exact K24.Global.PerpProof.tensorHolderPerp_banach_proof C k alpha.value H rho hAction
