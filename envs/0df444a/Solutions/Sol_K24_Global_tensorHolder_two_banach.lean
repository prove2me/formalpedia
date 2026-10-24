-- Prove2me | solution 1 for K24.Global.tensorHolder_two_banach
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:37:14.725006+00:00
-- url     : https://prove2.me/submissions/8b51c2fb-9356-4387-8894-5aa39151c0b2

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

universe u
theorem solution :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
      (C : K24.Global.BoundedLocalCover M) (alpha : K24.Global.HolderExponent),
      K24.Global.SectionBanachSpace (K24.Global.tensorHolderSpace C 2 alpha.value)
        (C.cov2ENorm 2 alpha.value) := by
  intro M _ _ C alpha
  exact K24.Global.tensorHolder_banach_proof C 2 alpha.value
