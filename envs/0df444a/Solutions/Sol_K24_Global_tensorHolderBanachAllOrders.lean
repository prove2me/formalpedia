-- Prove2me | solution 1 for K24.Global.tensorHolderBanachAllOrders
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:29:50.926635+00:00
-- url     : https://prove2.me/submissions/785b4b44-a230-441f-ac9f-f778225bf5ed

import Definitions.Def_K24GlobalStatement

/- K24HB2: finite-order big Hölder Banach theorem for actual tensor sections.
The two matrix reconstruction helpers immediately below are reused verbatim
from the inspected K24HB source commit
0de8f6e6525f6012f32adda89cb7178d66708b4d, Solutions/K24HB_Tensor.lean.
The derivative-limit, canonical norm, and finite-order completeness arguments
are the K24HB2 continuation. No hidden solution-module imports are required. -/

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

theorem matrixToBilinear_eval_continuous (v w : FourSpace) :
    Continuous (fun a : Mat4 => matrixToBilinear a v w) := by
  unfold matrixToBilinear
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  fun_prop

theorem LocalCoverChart.matrix_recover_eval {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u : RawCov2 M) (x : FourSpace)
    (v w : TangentSpace I4 (c.lift x)) :
    matrixToBilinear (c.liftedCov2 u x) ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) =
      u (c.lift x) v w := by
  have h := matrixToBilinear_recover
    (bilinearPullback (u (c.lift x)) (c.tangentMap x).toContinuousLinearMap)
  have h' := congrArg (fun a : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) =>
    a ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)) h
  change matrixToBilinear (c.liftedCov2 u x) ((c.tangentMap x).symm v)
    ((c.tangentMap x).symm w) = u (c.lift x)
      ((c.tangentMap x) ((c.tangentMap x).symm v))
      ((c.tangentMap x) ((c.tangentMap x).symm w)) at h'
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h'


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

/-- Completeness produces an actual function limit on the same domain. -/
theorem exists_uniform_limit_of_uniformCauchy {s : Set E} (f : ℕ → E → V)
    (hc : UniformCauchySeqOn f atTop s) :
    ∃ g : E → V, TendstoUniformlyOn f g atTop s := by
  classical
  have hp (x : s) : CauchySeq (fun n => f n x) := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hc eps heps
    exact ⟨N, fun i hi j hj => hN i hi j hj x x.property⟩
  choose g₀ hg₀ using fun x : s => cauchySeq_tendsto_of_complete (hp x)
  let g : E → V := fun x => if hx : x ∈ s then g₀ ⟨x, hx⟩ else 0
  refine ⟨g, hc.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  simpa only [g, dif_pos hx] using hg₀ ⟨x, hx⟩

/-- Uniform Cauchy control of the actual finite jets forces compatibility of
their limits with derivatives of the actual pointwise function limit. -/
theorem contDiffOn_of_uniformCauchy_iteratedFDerivWithin
    (k : ℕ) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V) (g : E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ j : ℕ, j ≤ k →
      UniformCauchySeqOn (fun n => iteratedFDerivWithin ℝ j (f n) s) atTop s)
    (hlim : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ k g s ∧
      ∀ j : ℕ, j ≤ k → TendstoUniformlyOn
        (fun n => iteratedFDerivWithin ℝ j (f n) s)
        (iteratedFDerivWithin ℝ j g s) atTop s := by
  induction k generalizing f g with
  | zero =>
    have hcF : UniformCauchySeqOn f atTop s := by
      have hh := Metric.uniformCauchySeqOn_iff.mp (hc 0 le_rfl)
      apply Metric.uniformCauchySeqOn_iff.mpr
      simpa only [dist_iteratedFDerivWithin_zero] using hh
    have huF := hcF.tendstoUniformlyOn_of_tendsto hlim
    refine ⟨contDiffOn_zero.mpr (huF.continuousOn
      (Eventually.of_forall fun n => (hf n).continuousOn).frequently), ?_⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    apply (hc 0 le_rfl).tendstoUniformlyOn_of_tendsto
    intro x hx
    exact (continuousMultilinearCurryFin0 ℝ E V).symm.continuous.continuousAt.tendsto.comp (hlim x hx)
  | succ k ih =>
    have hfLow : ∀ n, ContDiffOn ℝ k (f n) s := fun n =>
      (hf n).of_le (by exact_mod_cast Nat.le_succ k)
    obtain ⟨hgLow, huLow⟩ := ih f g hfLow (fun j hj => hc j (hj.trans (Nat.le_succ k))) hlim
    obtain ⟨q, huq⟩ := exists_uniform_limit_of_uniformCauchy
      (fun n => iteratedFDerivWithin ℝ (k + 1) (f n) s) (hc (k + 1) le_rfl)
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) V
    have huD := curry.isometry.uniformContinuous.comp_tendstoUniformlyOn huq
    have hd : ∀ x ∈ s,
        HasFDerivAt (iteratedFDerivWithin ℝ k g s) (curry (q x)) x := by
      intro x hx
      apply hasFDerivAt_of_tendstoUniformlyOn (f := fun n => iteratedFDerivWithin ℝ k (f n) s) hs huD _ _ hx
      · intro n y hy
        exact ((hf n).ftaylorSeriesWithin hs.uniqueDiffOn |>.fderivWithin k
          (by exact_mod_cast Nat.lt_succ_self k) y hy).hasFDerivAt (hs.mem_nhds hy)
      · intro y hy
        exact (huLow k le_rfl).tendsto_at hy
    have hqEq : ∀ x ∈ s, q x = iteratedFDerivWithin ℝ (k + 1) g s x := by
      intro x hx
      have hh := (hd x hx).hasFDerivWithinAt.fderivWithin (hs.uniqueDiffOn x hx)
      rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, hh]
      exact (curry.symm_apply_apply (q x)).symm
    have huTop : TendstoUniformlyOn
        (fun n => iteratedFDerivWithin ℝ (k + 1) (f n) s)
        (iteratedFDerivWithin ℝ (k + 1) g s) atTop s :=
      huq.congr_right hqEq
    have hContTop : ContinuousOn (iteratedFDerivWithin ℝ (k + 1) g s) s := by
      apply huTop.continuousOn
      exact (Eventually.of_forall fun n =>
        (hf n).continuousOn_iteratedFDerivWithin (by simp) hs.uniqueDiffOn).frequently
    refine ⟨?_, ?_⟩
    · apply (contDiffOn_nat_iff_continuousOn_differentiableOn hs.uniqueDiffOn).mpr
      constructor
      · intro j hj
        by_cases hjLow : j ≤ k
        · exact hgLow.continuousOn_iteratedFDerivWithin (by exact_mod_cast hjLow) hs.uniqueDiffOn
        · have hjeq : j = k + 1 := by omega
          subst j
          exact hContTop
      · intro j hj
        by_cases hjLow : j < k
        · exact hgLow.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hjLow) hs.uniqueDiffOn
        · have hjeq : j = k := by omega
          subst j
          exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · intro j hj
      by_cases hjLow : j ≤ k
      · exact huLow j hjLow
      · have hjeq : j = k + 1 := by omega
        subst j
        exact huTop

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

theorem uniformCauchy_jets_of_coordinateHolderENorm_cauchy
    (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha s (f i - f j) < ENNReal.ofReal eps) :
    ∀ j : ℕ, j ≤ k → UniformCauchySeqOn
      (fun n => iteratedFDerivWithin ℝ j (f n) s) atTop s := by
  intro j hj
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  rw [dist_eq_norm, ofReal_norm]
  have heq := iteratedFDerivWithin_sub_apply
    (((hf m).of_le (by exact_mod_cast hj)).contDiffWithinAt hx)
    (((hf n).of_le (by exact_mod_cast hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx
  rw [← heq]
  exact (jet_enorm_le_coordinateHolderENorm k j hj alpha s (f m-f n) x hx).trans_lt
    (hN m hm n hn)

theorem coordinateHolderENorm_limit_le {k : ℕ} {alpha C : ℝ≥0} {s : Set E}
    {f : ℕ → E → V} {g : E → V}
    (hlim : ∀ j : ℕ, j ≤ k → ∀ x ∈ s, Tendsto
      (fun n => iteratedFDerivWithin ℝ j (f n) s x) atTop
      (𝓝 (iteratedFDerivWithin ℝ j g s x)))
    (hbound : ∀ᶠ n in atTop, coordinateHolderENorm k alpha s (f n) ≤ (C : ℝ≥0∞)) :
    coordinateHolderENorm k alpha s g ≤ (k+2 : ℕ) * (C : ℝ≥0∞) := by
  have hd (j : ℕ) (hj : j ≤ k) : derivativeENorm j s g ≤ (C : ℝ≥0∞) := by
    apply iSup_le
    intro x
    apply le_of_tendsto (hlim j hj x x.property).enorm
    exact hbound.mono fun n hn =>
      (jet_enorm_le_coordinateHolderENorm k j hj alpha s (f n) x x.property).trans hn
  have hh : HolderWith C alpha (fun x : s => iteratedFDerivWithin ℝ k g s x) := by
    intro x y
    apply le_of_tendsto ((hlim k le_rfl x x.property).edist (hlim k le_rfl y y.property))
    filter_upwards [hbound] with n hn
    have hle : eHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k (f n) s x) ≤
        (C : ℝ≥0∞) := le_add_self.trans hn
    have hm := eHolderNorm_lt_top.mp (hle.trans_lt ENNReal.coe_lt_top)
    have hHolder := hm.holderWith
    have hC : nnHolderNorm alpha (fun x : s => iteratedFDerivWithin ℝ k (f n) s x) ≤ C := by
      apply ENNReal.coe_le_coe.mp
      rwa [hm.coe_nnHolderNorm_eq_eHolderNorm]
    exact hHolder.mono hC x y
  unfold coordinateHolderENorm
  calc
    _ ≤ (∑ j ∈ Finset.range (k+1), (C : ℝ≥0∞)) + C :=
      add_le_add (Finset.sum_le_sum fun j hj => hd j (by simpa using hj)) hh.eHolderNorm_le
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul]; ring

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

theorem coordinateHolderENorm_sub_limit_le {k : ℕ} {alpha K : ℝ≥0}
    {s : Set E} (hs : IsOpen s) (f : ℕ → E → V) (g : E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s) (hg : ContDiffOn ℝ k g s)
    (hlim : ∀ j : ℕ, j ≤ k → ∀ x ∈ s, Tendsto
      (fun n => iteratedFDerivWithin ℝ j (f n) s x) atTop
      (𝓝 (iteratedFDerivWithin ℝ j g s x)))
    (i : ℕ) (hbound : ∀ᶠ n in atTop,
      coordinateHolderENorm k alpha s (f i-f n) ≤ (K : ℝ≥0∞)) :
    coordinateHolderENorm k alpha s (f i-g) ≤ (k+2 : ℕ) * (K : ℝ≥0∞) := by
  apply coordinateHolderENorm_limit_le (f := fun n => f i-f n) _ hbound
  intro j hj x hx
  have hjet (n : ℕ) := iteratedFDerivWithin_sub_apply
    (((hf i).of_le (by exact_mod_cast hj)).contDiffWithinAt hx)
    (((hf n).of_le (by exact_mod_cast hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx
  have hjetg := iteratedFDerivWithin_sub_apply
    (((hf i).of_le (by exact_mod_cast hj)).contDiffWithinAt hx)
    ((hg.of_le (by exact_mod_cast hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx
  simp_rw [hjet, hjetg]
  exact tendsto_const_nhds.sub (hlim j hj x hx)

theorem coordinateHolderENorm_cauchy_pointwise_limit [CompleteSpace V]
    (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V) (g : E → V)
    (hf : ∀ n, ContDiffOn ℝ k (f n) s)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha s (f i - f j) < ENNReal.ofReal eps)
    (hlim : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ k g s ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      coordinateHolderENorm k alpha s (f i-g) < ENNReal.ofReal eps := by
  obtain ⟨hg, hu⟩ := contDiffOn_of_uniformCauchy_iteratedFDerivWithin k hs f g hf
    (uniformCauchy_jets_of_coordinateHolderENorm_cauchy k alpha hs f hf hc) hlim
  refine ⟨hg, fun eps heps => ?_⟩
  have hdpos : 0 < (k+2 : ℝ) := by positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * (k+2 : ℝ))) (by positivity)
  let K : ℝ≥0 := (ENNReal.ofReal (eps / (2 * (k+2 : ℝ)))).toNNReal
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * (k+2 : ℝ))) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  refine ⟨N, fun i hi => ?_⟩
  have hb : ∀ᶠ n in atTop, coordinateHolderENorm k alpha s (f i-f n) ≤ (K : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hK]
    exact (hN i hi n hn).le
  refine (coordinateHolderENorm_sub_limit_le hs f g hf hg
    (fun j hj x hx => (hu j hj).tendsto_at hx) i hb).trans_lt ?_
  rw [hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
  push_cast
  have heq : (k+2 : ℝ) * (eps / (2 * (k+2 : ℝ))) = eps/2 := by
    field_simp
  rw [heq]
  linarith

/-- Completeness of the actual big Hölder coefficient functions on any open
domain at every finite order, with the canonical derivative-based norm. -/
theorem coordinateHolderENorm_complete [CompleteSpace V]
    (k : ℕ) (alpha : ℝ≥0) {s : Set E} (hs : IsOpen s) (f : ℕ → E → V)
    (hf : ∀ n, BigHolderOn k alpha s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha s (f i - f j) < ENNReal.ofReal eps) :
    ∃ g : E → V, BigHolderOn k alpha s g ∧
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        coordinateHolderENorm k alpha s (f i-g) < ENNReal.ofReal eps := by
  have hcu : UniformCauchySeqOn f atTop s := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
    rw [dist_eq_norm, ofReal_norm]
    exact (enorm_le_coordinateHolderENorm k alpha s (f m-f n) x hx).trans_lt (hN m hm n hn)
  obtain ⟨g, hu⟩ := exists_uniform_limit_of_uniformCauchy f hcu
  obtain ⟨hg, hconv⟩ := coordinateHolderENorm_cauchy_pointwise_limit k alpha hs f g
    (fun n => (hf n).1) hc (fun x hx => hu.tendsto_at hx)
  refine ⟨g, ⟨hg, ?_⟩, hconv⟩
  obtain ⟨N, hN⟩ := hconv 1 (by norm_num)
  have hEq : g = f N-(f N-g) := by ext x; simp
  have hbound := coordinateHolderENorm_sub_le k alpha hs (f N) (f N-g)
    (hf N).1 ((hf N).1.sub hg)
  rw [← hEq] at hbound
  exact hbound.trans_lt (ENNReal.add_lt_top.mpr
    ⟨(hf N).2, (hN N le_rfl).trans ENNReal.ofReal_lt_top⟩)

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

theorem cov2ENorm_add_le (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u v : RawCov2 M) (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) :
    C.cov2ENorm k alpha (u+v) ≤ C.cov2ENorm k alpha u + C.cov2ENorm k alpha v := by
  apply iSup_le
  intro nu
  exact (coordinateHolderENorm_add_le k alpha (C.chart nu).innerOpen
    _ _ (hu nu) (hv nu)).trans (add_le_add
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 u)) nu)
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 v)) nu))

theorem cov2ENorm_smul (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (c : ℝ) (u : RawCov2 M) (hu : Cov2Regular C k u) :
    C.cov2ENorm k alpha (c • u) = ENNReal.ofReal |c| * C.cov2ENorm k alpha u := by
  unfold BoundedLocalCover.cov2ENorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro nu
  exact coordinateHolderENorm_smul k alpha (C.chart nu).innerOpen c _ (hu nu)

theorem cov2ENorm_sub_le (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u v : RawCov2 M) (hu : Cov2Regular C k u) (hv : Cov2Regular C k v) :
    C.cov2ENorm k alpha (u-v) ≤ C.cov2ENorm k alpha u + C.cov2ENorm k alpha v := by
  apply iSup_le
  intro nu
  exact (coordinateHolderENorm_sub_le k alpha (C.chart nu).innerOpen
    _ _ (hu nu) (hv nu)).trans (add_le_add
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 u)) nu)
    (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 v)) nu))

theorem cov2ENorm_zero (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    C.cov2ENorm k alpha 0 = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro nu
  exact (coordinateHolderENorm_zero k alpha (C.chart nu).innerDomain).le

theorem liftedCov2_enorm_le_cov2ENorm_order (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (nu : C.Index) (x : FourSpace) (hx : x ∈ (C.chart nu).innerDomain) :
    ‖(C.chart nu).liftedCov2 u x‖ₑ ≤ C.cov2ENorm k alpha u :=
  (enorm_le_coordinateHolderENorm k alpha (C.chart nu).innerDomain
    ((C.chart nu).liftedCov2 u) x hx).trans
      (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCov2 u)) nu)

theorem cov2ENorm_pointwise_limit (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (f : ℕ → RawCov2 M)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k alpha (f i - f j) < ENNReal.ofReal eps) :
    ∃ g : RawCov2 M, ∀ p (v w : TangentSpace I4 p),
      Tendsto (fun n => f n p v w) atTop (𝓝 (g p v w)) := by
  classical
  have hpoint (p : M) : ∃ a : TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ),
      ∀ v w, Tendsto (fun n => f n p v w) atTop (𝓝 (a v w)) := by
    obtain ⟨nu, x, hx, rfl⟩ := C.exists_inner_lift p
    let c := C.chart nu
    have hcauchy : CauchySeq (fun n => c.liftedCov2 (f n) x) := by
      apply Metric.cauchySeq_iff.mpr
      intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
      rw [dist_eq_norm, ofReal_norm]
      exact (liftedCov2_enorm_le_cov2ENorm_order C k alpha (f i - f j) nu x hx).trans_lt
        (hN i hi j hj)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨bilinearPullback (matrixToBilinear a) (c.tangentMap x).symm.toContinuousLinearMap,
      fun v w => ?_⟩
    have hh := (matrixToBilinear_eval_continuous
      ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)).continuousAt.tendsto.comp ha
    change Tendsto (fun n => matrixToBilinear (c.liftedCov2 (f n) x)
      ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)) atTop
      (𝓝 (matrixToBilinear a ((c.tangentMap x).symm v) ((c.tangentMap x).symm w))) at hh
    change Tendsto (fun n => f n (c.lift x) v w) atTop
      (𝓝 (matrixToBilinear a ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)))
    convert hh using 1
    funext n
    exact (c.matrix_recover_eval (f n) x v w).symm
  choose g hg using hpoint
  exact ⟨g, hg⟩


theorem cov2ENorm_definite (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (u : RawCov2 M) (hu : C.cov2ENorm k alpha u = 0) : u = 0 := by
  ext p v w
  obtain ⟨nu, x, hx, rfl⟩ := C.exists_inner_lift p
  have ha : (C.chart nu).liftedCov2 u x = 0 := by
    apply enorm_eq_zero.mp
    exact le_antisymm (by simpa only [hu] using
      liftedCov2_enorm_le_cov2ENorm_order C k alpha u nu x hx) bot_le
  have hrec := (C.chart nu).matrix_recover_eval u x v w
  rw [ha] at hrec
  simpa [matrixToBilinear] using hrec.symm

/-- Actual global raw tensor limits retain all finite derivatives and converge
in the canonical supremum over every chart with one common Cauchy index. -/
theorem cov2ENorm_cauchy_pointwise_limit (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (f : ℕ → RawCov2 M) (g : RawCov2 M)
    (hf : ∀ n, Cov2Regular C k (f n))
    (hlim : ∀ p (v w : TangentSpace I4 p),
      Tendsto (fun n => f n p v w) atTop (𝓝 (g p v w)))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      C.cov2ENorm k alpha (f i-f j) < ENNReal.ofReal eps) :
    Cov2Regular C k g ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      C.cov2ENorm k alpha (f i-g) < ENNReal.ofReal eps := by
  have hclocal (nu : C.Index) : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      coordinateHolderENorm k alpha (C.chart nu).innerDomain
        ((C.chart nu).liftedCov2 (f i)-(C.chart nu).liftedCov2 (f j)) < ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨N,hN⟩ := hc eps heps
    exact ⟨N, fun i hi j hj => (le_iSup (fun nu => coordinateHolderENorm k alpha
      (C.chart nu).innerDomain ((C.chart nu).liftedCov2 (f i-f j))) nu).trans_lt (hN i hi j hj)⟩
  have hlimlocal (nu : C.Index) (x : FourSpace) :
      Tendsto (fun n => (C.chart nu).liftedCov2 (f n) x) atTop
        (𝓝 ((C.chart nu).liftedCov2 g x)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    exact hlim _ _ _
  have hlocal (nu : C.Index) := contDiffOn_of_uniformCauchy_iteratedFDerivWithin k
    (C.chart nu).innerOpen (fun n => (C.chart nu).liftedCov2 (f n)) ((C.chart nu).liftedCov2 g)
    (fun n => hf n nu)
    (uniformCauchy_jets_of_coordinateHolderENorm_cauchy k alpha (C.chart nu).innerOpen
      _ (fun n => hf n nu) (hclocal nu)) (fun x _ => hlimlocal nu x)
  have hg : Cov2Regular C k g := fun nu => (hlocal nu).1
  refine ⟨hg, fun eps heps => ?_⟩
  have hdpos : 0 < (k+2 : ℝ) := by positivity
  obtain ⟨N, hN⟩ := hc (eps / (2 * (k+2 : ℝ))) (by positivity)
  let K : ℝ≥0 := (ENNReal.ofReal (eps / (2 * (k+2 : ℝ)))).toNNReal
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * (k+2 : ℝ))) :=
    ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
  refine ⟨N, fun i hi => ?_⟩
  have hbound : C.cov2ENorm k alpha (f i-g) ≤ (k+2 : ℕ) * (K : ℝ≥0∞) := by
    apply iSup_le
    intro nu
    apply coordinateHolderENorm_sub_limit_le (C.chart nu).innerOpen
      (fun n => (C.chart nu).liftedCov2 (f n)) ((C.chart nu).liftedCov2 g)
      (fun n => hf n nu) (hg nu)
      (fun j hj x hx => ((hlocal nu).2 j hj).tendsto_at hx) i
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hK]
    exact (le_iSup (fun nu => coordinateHolderENorm k alpha (C.chart nu).innerDomain
      ((C.chart nu).liftedCov2 (f i-f n))) nu).trans (hN i hi n hn).le
  refine hbound.trans_lt ?_
  rw [hK, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
  push_cast
  have heq : (k+2 : ℝ) * (eps / (2 * (k+2 : ℝ))) = eps/2 := by field_simp
  rw [heq]
  linarith

/-- The actual symmetric tensor big Hölder space is Banach at every finite
order. Completeness is proved on the original raw tensor sections. -/
theorem tensorHolderSpace_sectionBanach (C : BoundedLocalCover M)
    (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace (tensorHolderSpace C k alpha) (C.cov2ENorm k alpha) := by
  refine
    { zero_mem := ?_
      add_mem := ?_
      smul_mem := ?_
      finite := fun u hu => hu.2.2
      zero_norm := cov2ENorm_zero C k alpha
      definite := fun u _ hu => cov2ENorm_definite C k alpha u hu
      triangle := fun u hu v hv => cov2ENorm_add_le C k alpha u v hu.2.1 hv.2.1
      homogeneous := fun c u hu => cov2ENorm_smul C k alpha c u hu.2.1
      complete := ?_ }
  · refine ⟨fun p v w => rfl, fun nu => ?_, ?_⟩
    · change ContDiffOn ℝ k (fun _ : FourSpace => (0 : Mat4)) (C.chart nu).innerDomain
      exact contDiffOn_const
    · rw [cov2ENorm_zero]
      exact ENNReal.zero_lt_top
  · intro u hu v hv
    refine ⟨?_, Cov2Regular.add hu.2.1 hv.2.1, ?_⟩
    · intro p a b
      change u p a b + v p a b = u p b a + v p b a
      rw [hu.1 p a b, hv.1 p a b]
    · exact (cov2ENorm_add_le C k alpha u v hu.2.1 hv.2.1).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hu.2.2, hv.2.2⟩)
  · intro c u hu
    refine ⟨?_, Cov2Regular.smul hu.2.1 c, ?_⟩
    · intro p a b
      change c * u p a b = c * u p b a
      rw [hu.1 p a b]
    · rw [cov2ENorm_smul C k alpha c u hu.2.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2.2
  · intro f hf hc
    obtain ⟨g, hg⟩ := cov2ENorm_pointwise_limit C k alpha f hc
    obtain ⟨hgReg, hconv⟩ := cov2ENorm_cauchy_pointwise_limit C k alpha f g
      (fun n => (hf n).2.1) hg hc
    refine ⟨g, ⟨?_, hgReg, ?_⟩, hconv⟩
    · intro p v w
      have heq : (fun n => f n p v w) = (fun n => f n p w v) := by
        funext n
        exact (hf n).1 p v w
      have h₁ := hg p v w
      rw [heq] at h₁
      exact tendsto_nhds_unique h₁ (hg p w v)
    · obtain ⟨N, hN⟩ := hconv 1 (by norm_num)
      have hEq : g = f N-(f N-g) := by
        ext p v w
        exact (sub_sub_cancel _ _).symm
      have hbound := cov2ENorm_sub_le C k alpha (f N) (f N-g) (hf N).2.1
        (Cov2Regular.sub (hf N).2.1 hgReg)
      rw [← hEq] at hbound
      exact hbound.trans_lt (ENNReal.add_lt_top.mpr
        ⟨(hf N).2.2, (hN N le_rfl).trans ENNReal.ofReal_lt_top⟩)

/-- The exact domain Banach input required by the natural C2α-to-C0α inverse. -/
theorem tensorHolderSpace_two_sectionBanach (C : BoundedLocalCover M)
    (alpha : ℝ≥0) (_halpha : 0 < alpha) :
    SectionBanachSpace (tensorHolderSpace C 2 alpha) (C.cov2ENorm 2 alpha) :=
  tensorHolderSpace_sectionBanach C 2 alpha

end K24.Global


universe u

theorem solution :
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    (C : K24.Global.BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0),
    K24.Global.SectionBanachSpace (K24.Global.tensorHolderSpace C k alpha)
      (C.cov2ENorm k alpha) :=
  K24.Global.tensorHolderSpace_sectionBanach

#check @solution
#print axioms solution
