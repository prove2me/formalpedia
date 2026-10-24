-- Prove2me | solution 1 for K24.Global.vector_covector_holder_banach
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:44:40.638001+00:00
-- url     : https://prove2.me/submissions/cfaa8fe7-20b5-4b46-8be1-d5cf380cc9e6

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

namespace K24.Global
universe u
theorem _root_.solution
    {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    (C : BoundedLocalCover M) (k : ℕ) (alpha : HolderExponent) :
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha.value Y}
      (C.vectorENorm k alpha.value) ∧
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha.value eta}
      (C.covectorENorm k alpha.value) := vector_covector_holder_banach_proof C k alpha
end K24.Global
