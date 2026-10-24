-- Prove2me | solution 1 for K24.Global.vector_covector_holderPerp_banach
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:52:30.801932+00:00
-- url     : https://prove2.me/submissions/ebd6a577-9daa-4f27-abc1-0ed6ac23e270

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/- Inlined CoordinateSupport.lean; provenance in PROVENANCE.json. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff
open Filter

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

/- Inlined FiberSupport.lean; provenance in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

local instance tangentNormedAddCommGroup (p : M) : NormedAddCommGroup (TangentSpace I4 p) := by
  exact inferInstanceAs (NormedAddCommGroup FourSpace)
local instance tangentNormedSpace (p : M) : NormedSpace ℝ (TangentSpace I4 p) := by
  exact inferInstanceAs (NormedSpace ℝ FourSpace)
local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) := by
  exact inferInstanceAs (FiniteDimensional ℝ FourSpace)
local instance tangentT2 (p : M) : T2Space (TangentSpace I4 p) := by
  exact inferInstanceAs (T2Space FourSpace)

@[simp] theorem LocalCoverChart.liftedVector_sub {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawVector M) :
    c.liftedVector (u - v) = c.liftedVector u - c.liftedVector v := by
  funext x; exact map_sub (c.tangentMap x).symm _ _
@[simp] theorem LocalCoverChart.liftedVector_add {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawVector M) :
    c.liftedVector (u + v) = c.liftedVector u + c.liftedVector v := by
  funext x; exact map_add (c.tangentMap x).symm _ _
@[simp] theorem LocalCoverChart.liftedVector_smul {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (r : ℝ) (u : RawVector M) :
    c.liftedVector (r • u) = r • c.liftedVector u := by
  funext x; exact map_smul (c.tangentMap x).symm r _
@[simp] theorem LocalCoverChart.liftedVector_zero {F : LocalFiniteCover M}
    (c : LocalCoverChart F) : c.liftedVector (0 : RawVector M) = 0 := by
  funext x; exact map_zero (c.tangentMap x).symm

def LocalCoverChart.vectorReconstructLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    FourSpace →ₗ[ℝ] TangentSpace I4 (c.lift x) := (c.tangentMap x).toLinearMap

theorem LocalCoverChart.vector_reconstruct {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) (u : RawVector M) :
    c.vectorReconstructLinearMap x (c.liftedVector u x) = u (c.lift x) :=
  (c.tangentMap x).apply_symm_apply _

theorem LocalCoverChart.liftedVector_tendsto {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (f : ℕ → RawVector M) (u : RawVector M)
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) (x : FourSpace) :
    Tendsto (fun n => c.liftedVector (f n) x) atTop (𝓝 (c.liftedVector u x)) :=
  ((c.tangentMap x).symm.continuous.tendsto _).comp (ht (c.lift x))

def LocalCoverChart.covectorCoordinateLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    (TangentSpace I4 (c.lift x) →L[ℝ] ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun a := fun i => a (c.tangentMap x (basisVector i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def LocalCoverChart.covectorReconstructLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    (Fin 4 → ℝ) →ₗ[ℝ] (TangentSpace I4 (c.lift x) →L[ℝ] ℝ) where
  toFun a := (coefficientsToCovector a).comp (c.tangentMap x).symm.toContinuousLinearMap
  map_add' a b := by
    ext v
    simp [coefficientsToCovector, Finset.sum_add_distrib, add_mul]
  map_smul' r a := by
    ext v
    simp [coefficientsToCovector, Finset.mul_sum, mul_assoc]

theorem LocalCoverChart.covector_reconstruct {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) (u : RawCovector M) :
    c.covectorReconstructLinearMap x (c.liftedCovector u x) = u (c.lift x) := by
  have h := coefficientsToCovector_recover ((u (c.lift x)).comp (c.tangentMap x).toContinuousLinearMap)
  change coefficientsToCovector (c.liftedCovector u x) = _ at h
  change (coefficientsToCovector (c.liftedCovector u x)).comp
    (c.tangentMap x).symm.toContinuousLinearMap = _
  rw [h]
  ext v
  change u (c.lift x) ((c.tangentMap x) ((c.tangentMap x).symm v)) = u (c.lift x) v
  rw [(c.tangentMap x).apply_symm_apply]

@[simp] theorem LocalCoverChart.liftedCovector_sub {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCovector M) :
    c.liftedCovector (u - v) = c.liftedCovector u - c.liftedCovector v := rfl
@[simp] theorem LocalCoverChart.liftedCovector_add {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCovector M) :
    c.liftedCovector (u + v) = c.liftedCovector u + c.liftedCovector v := rfl
@[simp] theorem LocalCoverChart.liftedCovector_smul {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (r : ℝ) (u : RawCovector M) :
    c.liftedCovector (r • u) = r • c.liftedCovector u := rfl
@[simp] theorem LocalCoverChart.liftedCovector_zero {F : LocalFiniteCover M}
    (c : LocalCoverChart F) : c.liftedCovector (0 : RawCovector M) = 0 := rfl

theorem LocalCoverChart.liftedCovector_tendsto {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (f : ℕ → RawCovector M) (u : RawCovector M)
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) (x : FourSpace) :
    Tendsto (fun n => c.liftedCovector (f n) x) atTop (𝓝 (c.liftedCovector u x)) := by
  change Tendsto (fun n => c.covectorCoordinateLinearMap x (f n (c.lift x))) atTop
    (𝓝 (c.covectorCoordinateLinearMap x (u (c.lift x))))
  exact ((c.covectorCoordinateLinearMap x).continuous_of_finiteDimensional.tendsto _).comp (ht (c.lift x))
end K24.Global

/- Inlined VectorNorm.lean; provenance in PROVENANCE.json. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
attribute [local instance] tangentNormedAddCommGroup tangentNormedSpace tangentFiniteDimensional tangentT2

theorem BoundedLocalCover.vectorENorm_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    C.vectorENorm k α 0 = 0 := by
  simp only [BoundedLocalCover.vectorENorm, LocalCoverChart.liftedVector_zero,
    coordinateHolderENorm_zero]
  simp

theorem BoundedLocalCover.vectorENorm_add_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u v : RawVector M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector u) (C.chart ν).innerDomain)
    (hv : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector v) (C.chart ν).innerDomain) :
    C.vectorENorm k α (u + v) ≤ C.vectorENorm k α u + C.vectorENorm k α v := by
  apply iSup_le
  intro ν
  rw [LocalCoverChart.liftedVector_add]
  exact (coordinateHolderENorm_add_le α (C.chart ν).innerOpen (hu ν) (hv ν)).trans
    (add_le_add (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedVector u)) ν)
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedVector v)) ν))

theorem BoundedLocalCover.vectorENorm_smul (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (r : ℝ) (u : RawVector M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector u) (C.chart ν).innerDomain) :
    C.vectorENorm k α (r • u) = ENNReal.ofReal |r| * C.vectorENorm k α u := by
  unfold BoundedLocalCover.vectorENorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro ν
  rw [LocalCoverChart.liftedVector_smul]
  exact coordinateHolderENorm_smul α (C.chart ν).innerOpen (hu ν) r

theorem BoundedLocalCover.vectorENorm_definite (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawVector M) (hu : C.vectorENorm k α u = 0) : u = 0 := by
  funext p
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hn : (‖(C.chart ν).liftedVector u x‖₊ : ℝ≥0∞) ≤ C.vectorENorm k α u :=
    (enorm_le_coordinateHolderENorm k α (C.chart ν).innerDomain ((C.chart ν).liftedVector u) ⟨x, hx⟩).trans
      (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain ((C.chart μ).liftedVector u)) ν)
  rw [hu] at hn
  have hx0 : (C.chart ν).liftedVector u x = 0 :=
    nnnorm_eq_zero.mp (ENNReal.coe_eq_zero.mp (le_antisymm hn zero_le))
  have hrec := (C.chart ν).vector_reconstruct x u
  rw [hx0, map_zero] at hrec
  exact hrec.symm

set_option maxHeartbeats 800000 in
theorem BoundedLocalCover.vectorHolder_pointwise_cauchy
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) (f : ℕ → RawVector M)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.vectorENorm k α (f i - f j) < ENNReal.ofReal eps) (p : M) :
    CauchySeq (fun n => f n p) := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hcoord : CauchySeq (fun n => (C.chart ν).liftedVector (f n) x) := by
    apply coordinateHolderENorm_pointwise_cauchy (s := (C.chart ν).innerDomain)
      (k := k) (α := α) (x := ⟨x, hx⟩)
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hle := le_iSup (fun μ : C.Index => coordinateHolderENorm k α
      (C.chart μ).innerDomain ((C.chart μ).liftedVector (f i - f j))) ν
    simpa only [LocalCoverChart.liftedVector_sub] using hle.trans_lt (hN i hi j hj)
  let r : FourSpace →L[ℝ] TangentSpace I4 ((C.chart ν).lift x) :=
    { (C.chart ν).vectorReconstructLinearMap x with
      cont := ((C.chart ν).vectorReconstructLinearMap x).continuous_of_finiteDimensional }
  have hh := r.uniformContinuous.comp_cauchySeq hcoord
  change CauchySeq (fun n => (C.chart ν).vectorReconstructLinearMap x
    ((C.chart ν).liftedVector (f n) x)) at hh
  simpa only [LocalCoverChart.vector_reconstruct] using hh

theorem BoundedLocalCover.vectorENorm_le_of_derivative_tendsto
    (C : BoundedLocalCover M) {k : ℕ} {α R : ℝ≥0} {f : ℕ → RawVector M} {u : RawVector M}
    (ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector u) (C.chart ν).innerDomain x)))
    (hb : ∀ᶠ n in atTop, C.vectorENorm k α (f n) ≤ (R : ℝ≥0∞)) :
    C.vectorENorm k α u ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
  apply iSup_le
  intro ν
  apply coordinateHolderENorm_le_of_derivative_tendsto (ht ν)
  exact hb.mono (fun n hn =>
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedVector (f n))) ν).trans hn)

end K24.Global

/- Inlined CovectorNorm.lean; provenance in PROVENANCE.json. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
attribute [local instance] tangentNormedAddCommGroup tangentNormedSpace tangentFiniteDimensional tangentT2

theorem BoundedLocalCover.covectorENorm_zero (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    C.covectorENorm k α 0 = 0 := by
  simp only [BoundedLocalCover.covectorENorm, LocalCoverChart.liftedCovector_zero,
    coordinateHolderENorm_zero]
  simp

theorem BoundedLocalCover.covectorENorm_add_le (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u v : RawCovector M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain)
    (hv : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector v) (C.chart ν).innerDomain) :
    C.covectorENorm k α (u + v) ≤ C.covectorENorm k α u + C.covectorENorm k α v := by
  apply iSup_le
  intro ν
  rw [LocalCoverChart.liftedCovector_add]
  exact (coordinateHolderENorm_add_le α (C.chart ν).innerOpen (hu ν) (hv ν)).trans
    (add_le_add (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCovector u)) ν)
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCovector v)) ν))

theorem BoundedLocalCover.covectorENorm_smul (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (r : ℝ) (u : RawCovector M)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain) :
    C.covectorENorm k α (r • u) = ENNReal.ofReal |r| * C.covectorENorm k α u := by
  unfold BoundedLocalCover.covectorENorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro ν
  rw [LocalCoverChart.liftedCovector_smul]
  exact coordinateHolderENorm_smul α (C.chart ν).innerOpen (hu ν) r

theorem BoundedLocalCover.covectorENorm_definite (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (u : RawCovector M) (hu : C.covectorENorm k α u = 0) : u = 0 := by
  funext p
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hn : (‖(C.chart ν).liftedCovector u x‖₊ : ℝ≥0∞) ≤ C.covectorENorm k α u :=
    (enorm_le_coordinateHolderENorm k α (C.chart ν).innerDomain ((C.chart ν).liftedCovector u) ⟨x, hx⟩).trans
      (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain ((C.chart μ).liftedCovector u)) ν)
  rw [hu] at hn
  have hx0 : (C.chart ν).liftedCovector u x = 0 :=
    nnnorm_eq_zero.mp (ENNReal.coe_eq_zero.mp (le_antisymm hn zero_le))
  have hrec := (C.chart ν).covector_reconstruct x u
  rw [hx0, map_zero] at hrec
  exact hrec.symm

set_option maxHeartbeats 800000 in
theorem BoundedLocalCover.covectorHolder_pointwise_cauchy
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) (f : ℕ → RawCovector M)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.covectorENorm k α (f i - f j) < ENNReal.ofReal eps) (p : M) :
    CauchySeq (fun n => f n p) := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  have hcoord : CauchySeq (fun n => (C.chart ν).liftedCovector (f n) x) := by
    apply coordinateHolderENorm_pointwise_cauchy (s := (C.chart ν).innerDomain)
      (k := k) (α := α) (x := ⟨x, hx⟩)
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hle := le_iSup (fun μ : C.Index => coordinateHolderENorm k α
      (C.chart μ).innerDomain ((C.chart μ).liftedCovector (f i - f j))) ν
    simpa only [LocalCoverChart.liftedCovector_sub] using hle.trans_lt (hN i hi j hj)
  let r : (Fin 4 → ℝ) →L[ℝ] (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ] ℝ) :=
    { (C.chart ν).covectorReconstructLinearMap x with
      cont := ((C.chart ν).covectorReconstructLinearMap x).continuous_of_finiteDimensional }
  have hh := r.uniformContinuous.comp_cauchySeq hcoord
  change CauchySeq (fun n => (C.chart ν).covectorReconstructLinearMap x
    ((C.chart ν).liftedCovector (f n) x)) at hh
  simpa only [LocalCoverChart.covector_reconstruct] using hh

theorem BoundedLocalCover.covectorENorm_le_of_derivative_tendsto
    (C : BoundedLocalCover M) {k : ℕ} {α R : ℝ≥0} {f : ℕ → RawCovector M} {u : RawCovector M}
    (ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain x)))
    (hb : ∀ᶠ n in atTop, C.covectorENorm k α (f n) ≤ (R : ℝ≥0∞)) :
    C.covectorENorm k α u ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
  apply iSup_le
  intro ν
  apply coordinateHolderENorm_le_of_derivative_tendsto (ht ν)
  exact hb.mono (fun n hn =>
    (le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
      ((C.chart μ).liftedCovector (f n))) ν).trans hn)

end K24.Global

/- Inlined VectorComplete.lean; provenance in PROVENANCE.json. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
attribute [local instance] tangentNormedAddCommGroup tangentNormedSpace tangentFiniteDimensional tangentT2
attribute [local instance] tangentFiniteDimensional tangentT2

theorem BoundedLocalCover.vectorENorm_convergence
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) {f : ℕ → RawVector M} {u : RawVector M}
    (hf : ∀ n, ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedVector u) (C.chart ν).innerDomain)
    (ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector u) (C.chart ν).innerDomain x)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.vectorENorm k α (f i - f j) < ENNReal.ofReal eps) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.vectorENorm k α (f i - u) < ENNReal.ofReal eps := by
  intro eps heps
  let m : ℝ := (k + 2 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * m)) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  let R : ℝ≥0 := ⟨eps / (2 * m), by positivity⟩
  have hR : (R : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * m)) := (ENNReal.ofReal_coe_nnreal (p := R)).symm
  have hb : C.vectorENorm k α (f i - u) ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
    apply C.vectorENorm_le_of_derivative_tendsto (f := fun n => f i - f n)
    · intro ν j hj x
      simp only [LocalCoverChart.liftedVector_sub]
      have hfi := (hf i ν).of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      have hfu := (hu ν).of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      have heq : (fun n => iteratedFDerivWithin ℝ j
          ((C.chart ν).liftedVector (f i) - (C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain x) =
          (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector (f i)) (C.chart ν).innerDomain x -
            iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain x) := by
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

/-- Completeness of the original ambient vector sections in the actual
full order-k Holder norm, with all regularity derived at the limit. -/
theorem vectorHolder_complete (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (f : ℕ → RawVector M) (hf : ∀ n, f n ∈ {Y : RawVector M | C.VectorHolder k α Y})
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.vectorENorm k α (f i - f j) < ENNReal.ofReal eps) :
    ∃ u ∈ {Y : RawVector M | C.VectorHolder k α Y}, ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.vectorENorm k α (f i - u) < ENNReal.ofReal eps := by
  classical
  have hp : ∀ p : M, ∃ v : TangentSpace I4 p,
      Tendsto (fun n => f n p) atTop (𝓝 v) := by
    intro p
    letI : CompleteSpace (TangentSpace I4 p) :=
      FiniteDimensional.complete ℝ _
    exact cauchySeq_tendsto_of_complete (C.vectorHolder_pointwise_cauchy k α f hc p)
  choose u hu using hp
  have hlocal : ∀ ν : C.Index,
      ContDiffOn ℝ k ((C.chart ν).liftedVector u) (C.chart ν).innerDomain ∧ ∀ j ≤ k,
      TendstoUniformlyOn (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain)
        (iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector u) (C.chart ν).innerDomain) atTop (C.chart ν).innerDomain := by
    intro ν
    apply coordinateHolder_limit_derivatives (α := α) (C.chart ν).innerOpen
      (fun n => (hf n).1 ν)
    · intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      have hle := le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
        ((C.chart μ).liftedVector (f i - f j))) ν
      simpa only [LocalCoverChart.liftedVector_sub] using hle.trans_lt (hN i hi j hj)
    · intro x _
      exact (C.chart ν).liftedVector_tendsto f u hu x
  have ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedVector u) (C.chart ν).innerDomain x)) :=
    fun ν j hj x => ((hlocal ν).2 j hj).tendsto_at x.property
  have hb : ∃ R : ℝ≥0, ∀ᶠ n in atTop, C.vectorENorm k α (f n) ≤ (R : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hc 1 zero_lt_one
    let R := 1 + C.vectorENorm k α (f N)
    have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, (hf N).2.ne⟩
    refine ⟨R.toNNReal, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
    rw [ENNReal.coe_toNNReal hR]
    calc
      C.vectorENorm k α (f n) = C.vectorENorm k α ((f n - f N) + f N) := by congr 1; ext p; simp
      _ ≤ C.vectorENorm k α (f n - f N) + C.vectorENorm k α (f N) :=
        C.vectorENorm_add_le k α _ _
          (fun ν => by
            rw [LocalCoverChart.liftedVector_sub]
            convert ((hf n).1 ν).sub ((hf N).1 ν) using 1
            ext x; rfl)
          (hf N).1
      _ ≤ R := add_le_add (by simpa using (hN n hn N le_rfl).le) le_rfl
  obtain ⟨R, hR⟩ := hb
  have hfinite : C.vectorENorm k α u < ⊤ :=
    (C.vectorENorm_le_of_derivative_tendsto ht hR).trans_lt
      (ENNReal.mul_lt_top (by simp) ENNReal.coe_lt_top)
  refine ⟨u, ⟨fun ν => (hlocal ν).1, hfinite⟩,
    C.vectorENorm_convergence k α (fun n => (hf n).1) (fun ν => (hlocal ν).1) ht hc⟩

end K24.Global

/- Inlined CovectorComplete.lean; provenance in PROVENANCE.json. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
open Filter

namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
attribute [local instance] tangentNormedAddCommGroup tangentNormedSpace tangentFiniteDimensional tangentT2
attribute [local instance] tangentFiniteDimensional tangentT2

theorem BoundedLocalCover.covectorENorm_convergence
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) {f : ℕ → RawCovector M} {u : RawCovector M}
    (hf : ∀ n, ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain)
    (hu : ∀ ν : C.Index, ContDiffOn ℝ k ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain)
    (ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain x)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.covectorENorm k α (f i - f j) < ENNReal.ofReal eps) :
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.covectorENorm k α (f i - u) < ENNReal.ofReal eps := by
  intro eps heps
  let m : ℝ := (k + 2 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * m)) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  let R : ℝ≥0 := ⟨eps / (2 * m), by positivity⟩
  have hR : (R : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * m)) := (ENNReal.ofReal_coe_nnreal (p := R)).symm
  have hb : C.covectorENorm k α (f i - u) ≤ ((k + 2 : ℕ) : ℝ≥0∞) * R := by
    apply C.covectorENorm_le_of_derivative_tendsto (f := fun n => f i - f n)
    · intro ν j hj x
      simp only [LocalCoverChart.liftedCovector_sub]
      have hfi := (hf i ν).of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      have hfu := (hu ν).of_le (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      have heq : (fun n => iteratedFDerivWithin ℝ j
          ((C.chart ν).liftedCovector (f i) - (C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain x) =
          (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector (f i)) (C.chart ν).innerDomain x -
            iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain x) := by
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

/-- Completeness of the original ambient covector sections in the actual
full order-k Holder norm, with all regularity derived at the limit. -/
theorem covectorHolder_complete (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0)
    (f : ℕ → RawCovector M) (hf : ∀ n, f n ∈ {eta : RawCovector M | C.CovectorHolder k α eta})
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.covectorENorm k α (f i - f j) < ENNReal.ofReal eps) :
    ∃ u ∈ {eta : RawCovector M | C.CovectorHolder k α eta}, ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.covectorENorm k α (f i - u) < ENNReal.ofReal eps := by
  classical
  have hp : ∀ p : M, ∃ v : TangentSpace I4 p →L[ℝ] ℝ,
      Tendsto (fun n => f n p) atTop (𝓝 v) := by
    intro p
    letI : CompleteSpace (TangentSpace I4 p →L[ℝ] ℝ) :=
      FiniteDimensional.complete ℝ _
    exact cauchySeq_tendsto_of_complete (C.covectorHolder_pointwise_cauchy k α f hc p)
  choose u hu using hp
  have hlocal : ∀ ν : C.Index,
      ContDiffOn ℝ k ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain ∧ ∀ j ≤ k,
      TendstoUniformlyOn (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain)
        (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain) atTop (C.chart ν).innerDomain := by
    intro ν
    apply coordinateHolder_limit_derivatives (α := α) (C.chart ν).innerOpen
      (fun n => (hf n).1 ν)
    · intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      have hle := le_iSup (fun μ => coordinateHolderENorm k α (C.chart μ).innerDomain
        ((C.chart μ).liftedCovector (f i - f j))) ν
      simpa only [LocalCoverChart.liftedCovector_sub] using hle.trans_lt (hN i hi j hj)
    · intro x _
      exact (C.chart ν).liftedCovector_tendsto f u hu x
  have ht : ∀ ν : C.Index, ∀ j ≤ k, ∀ x : (C.chart ν).innerDomain,
      Tendsto (fun n => iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector (f n)) (C.chart ν).innerDomain x)
        atTop (𝓝 (iteratedFDerivWithin ℝ j ((C.chart ν).liftedCovector u) (C.chart ν).innerDomain x)) :=
    fun ν j hj x => ((hlocal ν).2 j hj).tendsto_at x.property
  have hb : ∃ R : ℝ≥0, ∀ᶠ n in atTop, C.covectorENorm k α (f n) ≤ (R : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := hc 1 zero_lt_one
    let R := 1 + C.covectorENorm k α (f N)
    have hR : R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, (hf N).2.ne⟩
    refine ⟨R.toNNReal, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
    rw [ENNReal.coe_toNNReal hR]
    calc
      C.covectorENorm k α (f n) = C.covectorENorm k α ((f n - f N) + f N) := by congr 1; ext p; simp
      _ ≤ C.covectorENorm k α (f n - f N) + C.covectorENorm k α (f N) :=
        C.covectorENorm_add_le k α _ _
          (fun ν => by
            rw [LocalCoverChart.liftedCovector_sub]
            convert ((hf n).1 ν).sub ((hf N).1 ν) using 1
            ext x; rfl)
          (hf N).1
      _ ≤ R := add_le_add (by simpa using (hN n hn N le_rfl).le) le_rfl
  obtain ⟨R, hR⟩ := hb
  have hfinite : C.covectorENorm k α u < ⊤ :=
    (C.covectorENorm_le_of_derivative_tendsto ht hR).trans_lt
      (ENNReal.mul_lt_top (by simp) ENNReal.coe_lt_top)
  refine ⟨u, ⟨fun ν => (hlocal ν).1, hfinite⟩,
    C.covectorENorm_convergence k α (fun n => (hf n).1) (fun ν => (hlocal ν).1) ht hc⟩

end K24.Global

/- Inlined SectionBanach.lean; provenance in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open scoped NNReal ENNReal ContDiff
namespace K24.Global
universe u

/-- Completeness and norm laws for actual ambient vector sections. -/
theorem vectorHolder_banach_proof
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k α Y} (C.vectorENorm k α) where
  zero_mem := ⟨fun ν => by
      rw [LocalCoverChart.liftedVector_zero]
      convert (contDiffOn_const : ContDiffOn ℝ k (fun _ : FourSpace => (0 : FourSpace)) (C.chart ν).innerDomain) using 1
      ext x; rfl,
    by rw [C.vectorENorm_zero]; exact ENNReal.zero_lt_top⟩
  add_mem u hu v hv := by
    refine ⟨?_, ?_⟩
    · intro ν
      rw [LocalCoverChart.liftedVector_add]
      convert (hu.1 ν).add (hv.1 ν) using 1
      ext x; rfl
    · exact (C.vectorENorm_add_le k α u v hu.1 hv.1).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hu.2, hv.2⟩)
  smul_mem r u hu := by
    refine ⟨?_, ?_⟩
    · intro ν
      rw [LocalCoverChart.liftedVector_smul]
      convert (hu.1 ν).const_smul r using 1
      ext x; rfl
    · rw [C.vectorENorm_smul k α r u hu.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2
  finite u hu := hu.2
  zero_norm := C.vectorENorm_zero k α
  definite u _ hu := C.vectorENorm_definite k α u hu
  triangle u hu v hv := C.vectorENorm_add_le k α u v hu.1 hv.1
  homogeneous r u hu := C.vectorENorm_smul k α r u hu.1
  complete := vectorHolder_complete C k α

/-- Completeness and norm laws for actual ambient covector sections. -/
theorem covectorHolder_banach_proof
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k α eta} (C.covectorENorm k α) where
  zero_mem := ⟨fun ν => by
      rw [LocalCoverChart.liftedCovector_zero]
      convert (contDiffOn_const : ContDiffOn ℝ k (fun _ : FourSpace => (0 : (Fin 4 → ℝ))) (C.chart ν).innerDomain) using 1
      ext x; rfl,
    by rw [C.covectorENorm_zero]; exact ENNReal.zero_lt_top⟩
  add_mem u hu v hv := by
    refine ⟨?_, ?_⟩
    · intro ν
      rw [LocalCoverChart.liftedCovector_add]
      convert (hu.1 ν).add (hv.1 ν) using 1
      ext x; rfl
    · exact (C.covectorENorm_add_le k α u v hu.1 hv.1).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hu.2, hv.2⟩)
  smul_mem r u hu := by
    refine ⟨?_, ?_⟩
    · intro ν
      rw [LocalCoverChart.liftedCovector_smul]
      convert (hu.1 ν).const_smul r using 1
      ext x; rfl
    · rw [C.covectorENorm_smul k α r u hu.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2
  finite u hu := hu.2
  zero_norm := C.covectorENorm_zero k α
  definite u _ hu := C.covectorENorm_definite k α u hu
  triangle u hu v hv := C.covectorENorm_add_le k α u v hu.1 hv.1
  homogeneous r u hu := C.covectorENorm_smul k α r u hu.1
  complete := covectorHolder_complete C k α

theorem vector_covector_holder_banach_proof
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (C : BoundedLocalCover M) (k : ℕ) (alpha : HolderExponent) :
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha.value Y}
      (C.vectorENorm k alpha.value) ∧
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha.value eta}
      (C.covectorENorm k alpha.value) :=
  ⟨vectorHolder_banach_proof C k alpha.value, covectorHolder_banach_proof C k alpha.value⟩
end K24.Global

/- Actual Haar integrability, inlined from the frozen sibling proof; see PROVENANCE.json. -/
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
    exact (hf.contMDiffAt.mfderiv f g (hg.contMDiffAt.of_le (by simp : (0 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))
      (by simp : (0 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).continuousAt
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

/- Actual closed Haar kernels. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal Topology Matrix.Norms.Elementwise

namespace K24.Global.VectorCovectorPerpProof
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


theorem section_sub_mem {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) {u v : X} (hu : u ∈ S) (hv : v ∈ S) : u - v ∈ S := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    hS.add_mem u hu ((-1 : ℝ) • v) (hS.smul_mem (-1) v hv)

theorem sectionLinear_sub {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (A : X → Y) (hA : SectionLinearOn S A)
    {u v : X} (hu : u ∈ S) (hv : v ∈ S) : A (u - v) = A u - A v := by
  calc
    A (u - v) = A (u + (-1 : ℝ) • v) := by rw [neg_one_smul, sub_eq_add_neg]
    _ = A u + A ((-1 : ℝ) • v) := hA.2.1 u hu _ (hS.smul_mem (-1) v hv)
    _ = A u - A v := by rw [hA.2.2 (-1) v hv, neg_one_smul, sub_eq_add_neg]

/-- A pointwise finite bound suffices to make the actual kernel closed. -/
theorem sectionBanach_fiber_kernel {P : Type*} {E : P → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    {S : Set (∀ p, E p)} {nx : (∀ p, E p) → ℝ≥0∞} (hS : SectionBanachSpace S nx)
    (A : (∀ p, E p) → (∀ p, E p)) (hA : SectionLinearOn S A)
    (hbound : ∀ p, ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ S, ‖A u p‖ ≤ K * (nx u).toReal) :
    SectionBanachSpace {u | u ∈ S ∧ A u = 0} nx := by
  apply sectionBanach_kernel hS A hA
  intro f hf v hv hconv
  funext p
  obtain ⟨K, hK, hKbound⟩ := hbound p
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro eps heps
  have hden : 0 < K + 1 := by positivity
  have hsmall : 0 < eps / (K + 1) := div_pos heps hden
  obtain ⟨N, hN⟩ := hconv _ hsmall
  have hdiff := section_sub_mem hS (hf N).1 hv
  have hReal : (nx (f N - v)).toReal < eps / (K + 1) :=
    ENNReal.toReal_lt_of_lt_ofReal (hN N le_rfl)
  have hb := hKbound (f N - v) hdiff
  rw [sectionLinear_sub hS A hA (hf N).1 hv, (hf N).2] at hb
  simp only [zero_sub, Pi.neg_apply, norm_neg] at hb
  have hle : K * (nx (f N - v)).toReal ≤ (K + 1) * (eps / (K + 1)) := by
    apply mul_le_mul
    · linarith
    · exact hReal.le
    · exact ENNReal.toReal_nonneg
    · positivity
  have heq : (K + 1) * (eps / (K + 1)) = eps := mul_div_cancel₀ eps hden.ne'
  simpa only [zero_add, heq] using hb.trans hle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

local instance tangentNormedAddCommGroup (p : M) : NormedAddCommGroup (TangentSpace I4 p) :=
  inferInstanceAs (NormedAddCommGroup FourSpace)
local instance tangentNormedSpace (p : M) : NormedSpace ℝ (TangentSpace I4 p) :=
  inferInstanceAs (NormedSpace ℝ FourSpace)
local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) :=
  inferInstanceAs (FiniteDimensional ℝ FourSpace)
local instance tangentCompleteSpace (p : M) : CompleteSpace (TangentSpace I4 p) :=
  inferInstanceAs (CompleteSpace FourSpace)

def covectorReconstructCLM (c p : M) : (Fin 4 → ℝ) →L[ℝ]
    (TangentSpace I4 p →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := covectorFromChartAt c p
    map_add' := by
      intro a b
      ext v
      simp [covectorFromChartAt, coefficientsToCovector, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext v
      simp [covectorFromChartAt, coefficientsToCovector, Finset.mul_sum, mul_assoc] }

def vectorReconstructCLM (c p : M) : (Fin 4 → ℝ) →L[ℝ] TangentSpace I4 p :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
      (∑ i : Fin 4, a i • basisVector i)
    map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
    map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }

variable [IsManifold I4 ∞ M]

theorem vector_chart_recovery (Y : RawVector M) (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) :
    vectorReconstructCLM c p (fun i => vectorInChart Y c (chartAt FourSpace c p) i) = Y p := by
  change mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c p)
    (∑ i, vectorInChart Y c (chartAt FourSpace c p) i • basisVector i) = Y p
  rw [sum_basisVector]
  dsimp only [vectorInChart]
  rw [(chartAt FourSpace c).left_inv hp]
  exact congrArg (fun A => A (Y p)) ((mdifferentiable_chart (I := I4) c).symm_comp_deriv hp)


theorem covector_haar_fiber_integrable {rho : CircleAction M} {u : RawCovector M}
    (hu : CovectorHaarIntegrable rho u) (p : M) :
    Integrable (fun t => actionPullbackCovector rho t u p) circleHaar := by
  have hc : Integrable (fun t => covectorInChart (actionPullbackCovector rho t u)
      p (chartAt FourSpace p p)) circleHaar :=
    Integrable.of_eval (hu p _
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)))
  have hr : ∀ t, covectorReconstructCLM p p
      (covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p)) =
      actionPullbackCovector rho t u p := fun t =>
    covector_chart_recovery _ p p (mem_chart_source FourSpace p)
  simpa only [hr] using (covectorReconstructCLM p p).integrable_comp hc


theorem vector_haar_fiber_integrable {rho : CircleAction M} {Y : RawVector M}
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    Integrable (fun t => actionPullbackVector rho t Y p) circleHaar := by
  have hc : Integrable (fun t i => vectorInChart (actionPullbackVector rho t Y)
      p (chartAt FourSpace p p) i) circleHaar :=
    Integrable.of_eval (hY p _
      ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p)))
  have hr : ∀ t, vectorReconstructCLM p p
      (fun i => vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i) =
      actionPullbackVector rho t Y p := fun t =>
    vector_chart_recovery _ p p (mem_chart_source FourSpace p)
  simpa only [hr] using (vectorReconstructCLM p p).integrable_comp hc


theorem covector_mean_eq_fiberIntegral (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (p : M) :
    covectorPi0 rho u p = ∫ t, actionPullbackCovector rho t u p ∂circleHaar := by
  have hc := hu p _ ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p))
  have hci := Integrable.of_eval hc
  change covectorReconstructCLM p p
    (fun i => ∫ t, covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p) i ∂circleHaar) = _
  have heq : (fun i => ∫ t, covectorInChart (actionPullbackCovector rho t u)
      p (chartAt FourSpace p p) i ∂circleHaar) =
      ∫ t, covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p) ∂circleHaar := by
    funext i
    rw [eval_integral hc]
  rw [heq, ← (covectorReconstructCLM p p).integral_comp_comm hci]
  apply integral_congr_ae
  filter_upwards [] with t
  exact covector_chart_recovery _ p p (mem_chart_source FourSpace p)


theorem vector_mean_eq_fiberIntegral (rho : CircleAction M) (Y : RawVector M)
    (hY : VectorHaarIntegrable rho Y) (p : M) :
    vectorPi0 rho Y p = ∫ t, actionPullbackVector rho t Y p ∂circleHaar := by
  have hc := hY p _ ((chartAt FourSpace p).map_source (mem_chart_source FourSpace p))
  have hci := Integrable.of_eval hc
  change vectorReconstructCLM p p
    (fun i => ∫ t, vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i ∂circleHaar) = _
  have heq : (fun i => ∫ t, vectorInChart (actionPullbackVector rho t Y)
      p (chartAt FourSpace p p) i ∂circleHaar) =
      ∫ t, (fun i => vectorInChart (actionPullbackVector rho t Y) p (chartAt FourSpace p p) i) ∂circleHaar := by
    funext i
    rw [eval_integral hc]
  rw [heq, ← (vectorReconstructCLM p p).integral_comp_comm hci]
  apply integral_congr_ae
  filter_upwards [] with t
  exact vector_chart_recovery _ p p (mem_chart_source FourSpace p)




omit [IsManifold I4 ∞ M] in
theorem actionPullbackVector_add (rho : CircleAction M) (t : Circle) (u v : RawVector M) :
    actionPullbackVector rho t (u + v) = actionPullbackVector rho t u + actionPullbackVector rho t v := by
  funext p
  simp [actionPullbackVector]

omit [IsManifold I4 ∞ M] in
theorem actionPullbackVector_smul (rho : CircleAction M) (t : Circle) (c : ℝ) (u : RawVector M) :
    actionPullbackVector rho t (c • u) = c • actionPullbackVector rho t u := by
  funext p
  simp [actionPullbackVector]

theorem vector_haar_mean_linear {S : Set (RawVector M)} {nx : RawVector M → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (rho : CircleAction M)
    (hInt : ∀ u ∈ S, VectorHaarIntegrable rho u) : SectionLinearOn S (vectorPi0 rho) := by
  refine ⟨?_, ?_, ?_⟩
  · funext p
    rw [vector_mean_eq_fiberIntegral rho 0 (hInt 0 hS.zero_mem)]
    simp [actionPullbackVector]
  · intro u hu v hv
    funext p
    rw [vector_mean_eq_fiberIntegral rho (u + v) (hInt (u + v) (hS.add_mem u hu v hv))]
    simp only [actionPullbackVector_add, Pi.add_apply]
    rw [integral_add (vector_haar_fiber_integrable (hInt u hu) p)
      (vector_haar_fiber_integrable (hInt v hv) p),
      ← vector_mean_eq_fiberIntegral rho u (hInt u hu),
      ← vector_mean_eq_fiberIntegral rho v (hInt v hv)]
  · intro c u hu
    funext p
    rw [vector_mean_eq_fiberIntegral rho (c • u) (hInt (c • u) (hS.smul_mem c u hu))]
    simp only [actionPullbackVector_smul, Pi.smul_apply, integral_smul]
    rw [← vector_mean_eq_fiberIntegral rho u (hInt u hu)]

omit [IsManifold I4 ∞ M] in
theorem actionPullbackCovector_add (rho : CircleAction M) (t : Circle) (u v : RawCovector M) :
    actionPullbackCovector rho t (u + v) = actionPullbackCovector rho t u + actionPullbackCovector rho t v := by
  ext p a
  simp [actionPullbackCovector, pullbackCovector]

omit [IsManifold I4 ∞ M] in
theorem actionPullbackCovector_smul (rho : CircleAction M) (t : Circle) (c : ℝ) (u : RawCovector M) :
    actionPullbackCovector rho t (c • u) = c • actionPullbackCovector rho t u := by
  ext p a
  simp [actionPullbackCovector, pullbackCovector]

theorem covector_haar_mean_linear {S : Set (RawCovector M)} {nx : RawCovector M → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (rho : CircleAction M)
    (hInt : ∀ u ∈ S, CovectorHaarIntegrable rho u) : SectionLinearOn S (covectorPi0 rho) := by
  refine ⟨?_, ?_, ?_⟩
  · funext p
    rw [covector_mean_eq_fiberIntegral rho 0 (hInt 0 hS.zero_mem)]
    simp [actionPullbackCovector, pullbackCovector]
  · intro u hu v hv
    funext p
    rw [covector_mean_eq_fiberIntegral rho (u + v) (hInt (u + v) (hS.add_mem u hu v hv))]
    simp only [actionPullbackCovector_add, Pi.add_apply]
    rw [integral_add (covector_haar_fiber_integrable (hInt u hu) p)
      (covector_haar_fiber_integrable (hInt v hv) p),
      ← covector_mean_eq_fiberIntegral rho u (hInt u hu),
      ← covector_mean_eq_fiberIntegral rho v (hInt v hv)]
  · intro c u hu
    funext p
    rw [covector_mean_eq_fiberIntegral rho (c • u) (hInt (c • u) (hS.smul_mem c u hu))]
    simp only [actionPullbackCovector_smul, Pi.smul_apply, integral_smul]
    rw [← covector_mean_eq_fiberIntegral rho u (hInt u hu)]

omit [IsManifold I4 ∞ M] in
theorem exists_vector_value_bound (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) (p : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : RawVector M, C.vectorENorm k alpha u < ⊤ →
      ‖u p‖ ≤ K * (C.vectorENorm k alpha u).toReal := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  let r : FourSpace →L[ℝ] TangentSpace I4 ((C.chart ν).lift x) :=
    LinearMap.toContinuousLinearMap ((C.chart ν).vectorReconstructLinearMap x)
  refine ⟨‖r‖, norm_nonneg _, ?_⟩
  intro u hu
  have hm : ‖(C.chart ν).liftedVector u x‖ ≤ (C.vectorENorm k alpha u).toReal := by
    have hle : (‖(C.chart ν).liftedVector u x‖₊ : ℝ≥0∞) ≤ C.vectorENorm k alpha u :=
      (enorm_le_coordinateHolderENorm k alpha _ ((C.chart ν).liftedVector u) ⟨x, hx⟩).trans
        (le_iSup (fun μ => coordinateHolderENorm k alpha (C.chart μ).innerDomain
          ((C.chart μ).liftedVector u)) ν)
    exact_mod_cast ENNReal.toReal_mono hu.ne hle
  calc
    ‖u ((C.chart ν).lift x)‖ = ‖r ((C.chart ν).liftedVector u x)‖ := by
      change _ = ‖(C.chart ν).vectorReconstructLinearMap x ((C.chart ν).liftedVector u x)‖
      rw [LocalCoverChart.vector_reconstruct]
    _ ≤ ‖r‖ * ‖(C.chart ν).liftedVector u x‖ := r.le_opNorm _
    _ ≤ ‖r‖ * (C.vectorENorm k alpha u).toReal := mul_le_mul_of_nonneg_left hm (norm_nonneg _)

theorem vector_haar_mean_fiber_bound (C : BoundedLocalCover M) (k : ℕ) (alpha H : ℝ≥0)
    (rho : CircleAction M) (hAction : HolderActionControl C alpha H k rho)
    (p : M) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ u : RawVector M, C.vectorENorm k alpha u < ⊤ →
      ‖u p‖ ≤ K * (C.vectorENorm k alpha u).toReal)
    (u : RawVector M) (hu : C.VectorHolder k alpha u) (hInt : VectorHaarIntegrable rho u) :
    ‖vectorPi0 rho u p‖ ≤ K * H * (C.vectorENorm k alpha u).toReal := by
  rw [vector_mean_eq_fiberIntegral rho u hInt]
  have ht (t : Circle) : ‖actionPullbackVector rho t u p‖ ≤
      K * H * (C.vectorENorm k alpha u).toReal := by
    have hA := hAction.vector k le_rfl t u hu
    have hnorm : (C.vectorENorm k alpha (actionPullbackVector rho t u)).toReal ≤
        (H : ℝ) * (C.vectorENorm k alpha u).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hu.2.ne) hA.2
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
    exact (hbound _ hA.1.2).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnorm hK)
  simpa using norm_integral_le_of_norm_le_const (μ := circleHaar)
    (f := fun t => actionPullbackVector rho t u p) (Filter.Eventually.of_forall ht)

theorem vectorHolderPerp_banach_conditional (C : BoundedLocalCover M) (k : ℕ)
    (alpha H : ℝ≥0) (rho : CircleAction M)
    (hAction : HolderActionControl C alpha H k rho)
    (hInt : ∀ u, C.VectorHolder k alpha u → VectorHaarIntegrable rho u) :
    SectionBanachSpace (vectorHolderPerp C k alpha rho) (C.vectorENorm k alpha) := by
  apply sectionBanach_fiber_kernel (vectorHolder_banach_proof C k alpha) (vectorPi0 rho)
    (vector_haar_mean_linear (vectorHolder_banach_proof C k alpha) rho hInt)
  intro p
  obtain ⟨K, hK, hbound⟩ := exists_vector_value_bound C k alpha p
  refine ⟨K * H, mul_nonneg hK H.coe_nonneg, ?_⟩
  intro u hu
  exact vector_haar_mean_fiber_bound C k alpha H rho hAction p K hK hbound u hu (hInt u hu)

omit [IsManifold I4 ∞ M] in
theorem exists_covector_value_bound (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) (p : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : RawCovector M, C.covectorENorm k alpha u < ⊤ →
      ‖u p‖ ≤ K * (C.covectorENorm k alpha u).toReal := by
  obtain ⟨ν, x, hx, hxp⟩ := C.exists_inner_lift p
  subst p
  let r : (Fin 4 → ℝ) →L[ℝ] (TangentSpace I4 ((C.chart ν).lift x) →L[ℝ] ℝ) :=
    LinearMap.toContinuousLinearMap ((C.chart ν).covectorReconstructLinearMap x)
  refine ⟨‖r‖, norm_nonneg _, ?_⟩
  intro u hu
  have hm : ‖(C.chart ν).liftedCovector u x‖ ≤ (C.covectorENorm k alpha u).toReal := by
    have hle : (‖(C.chart ν).liftedCovector u x‖₊ : ℝ≥0∞) ≤ C.covectorENorm k alpha u :=
      (enorm_le_coordinateHolderENorm k alpha _ ((C.chart ν).liftedCovector u) ⟨x, hx⟩).trans
        (le_iSup (fun μ => coordinateHolderENorm k alpha (C.chart μ).innerDomain
          ((C.chart μ).liftedCovector u)) ν)
    exact_mod_cast ENNReal.toReal_mono hu.ne hle
  calc
    ‖u ((C.chart ν).lift x)‖ = ‖r ((C.chart ν).liftedCovector u x)‖ := by
      change _ = ‖(C.chart ν).covectorReconstructLinearMap x ((C.chart ν).liftedCovector u x)‖
      rw [LocalCoverChart.covector_reconstruct]
    _ ≤ ‖r‖ * ‖(C.chart ν).liftedCovector u x‖ := r.le_opNorm _
    _ ≤ ‖r‖ * (C.covectorENorm k alpha u).toReal := mul_le_mul_of_nonneg_left hm (norm_nonneg _)

theorem covector_haar_mean_fiber_bound (C : BoundedLocalCover M) (k : ℕ) (alpha H : ℝ≥0)
    (rho : CircleAction M) (hAction : HolderActionControl C alpha H k rho)
    (p : M) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ u : RawCovector M, C.covectorENorm k alpha u < ⊤ →
      ‖u p‖ ≤ K * (C.covectorENorm k alpha u).toReal)
    (u : RawCovector M) (hu : C.CovectorHolder k alpha u) (hInt : CovectorHaarIntegrable rho u) :
    ‖covectorPi0 rho u p‖ ≤ K * H * (C.covectorENorm k alpha u).toReal := by
  rw [covector_mean_eq_fiberIntegral rho u hInt]
  have ht (t : Circle) : ‖actionPullbackCovector rho t u p‖ ≤
      K * H * (C.covectorENorm k alpha u).toReal := by
    have hA := hAction.covector k le_rfl t u hu
    have hnorm : (C.covectorENorm k alpha (actionPullbackCovector rho t u)).toReal ≤
        (H : ℝ) * (C.covectorENorm k alpha u).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hu.2.ne) hA.2
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
    exact (hbound _ hA.1.2).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnorm hK)
  simpa using norm_integral_le_of_norm_le_const (μ := circleHaar)
    (f := fun t => actionPullbackCovector rho t u p) (Filter.Eventually.of_forall ht)

theorem covectorHolderPerp_banach_conditional (C : BoundedLocalCover M) (k : ℕ)
    (alpha H : ℝ≥0) (rho : CircleAction M)
    (hAction : HolderActionControl C alpha H k rho)
    (hInt : ∀ u, C.CovectorHolder k alpha u → CovectorHaarIntegrable rho u) :
    SectionBanachSpace (covectorHolderPerp C k alpha rho) (C.covectorENorm k alpha) := by
  apply sectionBanach_fiber_kernel (covectorHolder_banach_proof C k alpha) (covectorPi0 rho)
    (covector_haar_mean_linear (covectorHolder_banach_proof C k alpha) rho hInt)
  intro p
  obtain ⟨K, hK, hbound⟩ := exists_covector_value_bound C k alpha p
  refine ⟨K * H, mul_nonneg hK H.coe_nonneg, ?_⟩
  intro u hu
  exact covector_haar_mean_fiber_bound C k alpha H rho hAction p K hK hbound u hu (hInt u hu)

end K24.Global.VectorCovectorPerpProof

namespace K24.Global.VectorCovectorPerpProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem holderActionControl_mono (C : BoundedLocalCover M) (alpha H : ℝ≥0)
    (rho : CircleAction M) {k order : ℕ} (h : HolderActionControl C alpha H order rho)
    (hk : k ≤ order) : HolderActionControl C alpha H k rho where
  tensor j hj := h.tensor j (hj.trans hk)
  covector j hj := h.covector j (hj.trans hk)
  vector j hj := h.vector j (hj.trans hk)

theorem vectorHolderPerp_banach_proof (C : BoundedLocalCover M) (k : ℕ)
    (alpha H : ℝ≥0) (rho : CircleAction M)
    (hAction : HolderActionControl C alpha H k rho) :
    SectionBanachSpace (vectorHolderPerp C k alpha rho) (C.vectorENorm k alpha) :=
  vectorHolderPerp_banach_conditional C k alpha H rho hAction
    (VectorCovectorHaarProof.vectorHolder_haarIntegrable_proof C rho k alpha)

theorem covectorHolderPerp_banach_proof (C : BoundedLocalCover M) (k : ℕ)
    (alpha H : ℝ≥0) (rho : CircleAction M)
    (hAction : HolderActionControl C alpha H k rho) :
    SectionBanachSpace (covectorHolderPerp C k alpha rho) (C.covectorENorm k alpha) :=
  covectorHolderPerp_banach_conditional C k alpha H rho hAction
    (VectorCovectorHaarProof.covectorHolder_haarIntegrable_proof C rho k alpha)
end K24.Global.VectorCovectorPerpProof

namespace K24.Global
universe u
theorem _root_.solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ)
    (alpha : HolderExponent) (H : ℝ≥0) (rho : CircleAction M),
    HolderActionControl C alpha.value H k rho →
    SectionBanachSpace (vectorHolderPerp C k alpha.value rho) (C.vectorENorm k alpha.value) ∧
    SectionBanachSpace (covectorHolderPerp C k alpha.value rho) (C.covectorENorm k alpha.value) := by
  intro M _ _ _ C k alpha H rho hAction
  exact ⟨VectorCovectorPerpProof.vectorHolderPerp_banach_proof C k alpha.value H rho hAction,
    VectorCovectorPerpProof.covectorHolderPerp_banach_proof C k alpha.value H rho hAction⟩
end K24.Global
