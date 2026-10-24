-- Prove2me | solution 1 for K24.Global.vectorCovectorHolderBanachAllOrders
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:46:33.761696+00:00
-- url     : https://prove2.me/submissions/a14cfe5b-734e-4615-b320-81a67d4a4b88

import Definitions.Def_K24GlobalAnalysis

/- K24VCB: actual vector and covector finite-order Hölder Banach spaces.
The HB2 derivative-limit and canonical coordinate-norm proof bodies are
reused verbatim from source commit 2a069df20d73d303e930fd16b9f57bf67fbc166d,
frozen evidence commit 630e4f65fa733ee149e0581129b764fb05e65240.
K24VCB supplies the actual fiber reconstruction and cover assembly below.
Only the canonical definition module is imported; all helper proofs are here. -/


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

def space (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E)
    (k : ℕ) (alpha : ℝ≥0) : Set X :=
  {u | regular L s k u ∧ norm L s k alpha u < ⊤}

theorem regular_add {L : I → X →ₗ[ℝ] (E → V)} {s : I → Set E} {k : ℕ}
    {u v : X} (hu : regular L s k u) (hv : regular L s k v) : regular L s k (u+v) := by
  intro nu
  rw [map_add]
  exact (hu nu).add (hv nu)

theorem regular_sub {L : I → X →ₗ[ℝ] (E → V)} {s : I → Set E} {k : ℕ}
    {u v : X} (hu : regular L s k u) (hv : regular L s k v) : regular L s k (u-v) := by
  intro nu
  rw [map_sub]
  exact (hu nu).sub (hv nu)

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

theorem enorm_le_norm (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E)
    (k : ℕ) (alpha : ℝ≥0) (u : X) (nu : I) (x : E) (hx : x ∈ s nu) :
    ‖L nu u x‖ₑ ≤ norm L s k alpha u :=
  (enorm_le_coordinateHolderENorm k alpha (s nu) (L nu u) x hx).trans
    (le_iSup (fun nu => coordinateHolderENorm k alpha (s nu) (L nu u)) nu)

/-- An analytic assembly principle. Its reconstruction hypothesis is discharged
below on the actual vector and covector fibers; it assumes neither norm
completeness nor compatibility of limiting derivatives. -/
theorem sectionBanach [CompleteSpace V]
    (L : I → X →ₗ[ℝ] (E → V)) (s : I → Set E) (hs : ∀ nu, IsOpen (s nu))
    (hseparate : ∀ u : X, (∀ nu x, x ∈ s nu → L nu u x = 0) → u = 0)
    (hrecover : ∀ f : ℕ → X,
      (∀ nu x, x ∈ s nu → CauchySeq (fun n => L nu (f n) x)) →
      ∃ g : X, ∀ nu x, x ∈ s nu → Tendsto (fun n => L nu (f n) x) atTop (𝓝 (L nu g x)))
    (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace (space L s k alpha) (norm L s k alpha) := by
  refine
    { zero_mem := ?_
      add_mem := ?_
      smul_mem := ?_
      finite := fun u hu => hu.2
      zero_norm := norm_zero L s k alpha
      definite := ?_
      triangle := fun u hu v hv => norm_add_le L s hs k alpha u v hu.1 hv.1
      homogeneous := fun c u hu => norm_smul L s hs k alpha c u hu.1
      complete := ?_ }
  · refine ⟨?_, ?_⟩
    · intro nu
      rw [map_zero]
      exact contDiffOn_const
    · rw [norm_zero]
      exact ENNReal.zero_lt_top
  · intro u hu v hv
    exact ⟨regular_add hu.1 hv.1, (norm_add_le L s hs k alpha u v hu.1 hv.1).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hu.2,hv.2⟩)⟩
  · intro c u hu
    refine ⟨?_, ?_⟩
    · intro nu
      rw [map_smul]
      exact (hu.1 nu).const_smul c
    · rw [norm_smul L s hs k alpha c u hu.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2
  · intro u _ hzero
    apply hseparate u
    intro nu x hx
    apply enorm_eq_zero.mp
    exact le_antisymm (by simpa only [hzero] using enorm_le_norm L s k alpha u nu x hx) bot_le
  · intro f hf hc
    have hcpoint (nu : I) (x : E) (hx : x ∈ s nu) : CauchySeq (fun n => L nu (f n) x) := by
      apply Metric.cauchySeq_iff.mpr
      intro eps heps
      obtain ⟨N,hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
      rw [dist_eq_norm, ofReal_norm]
      have hb := enorm_le_norm L s k alpha (f i-f j) nu x hx
      rw [map_sub] at hb
      exact hb.trans_lt (hN i hi j hj)
    obtain ⟨g,hg⟩ := hrecover f hcpoint
    have hclocal (nu : I) : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
        coordinateHolderENorm k alpha (s nu) (L nu (f i)-L nu (f j)) < ENNReal.ofReal eps := by
      intro eps heps
      obtain ⟨N,hN⟩ := hc eps heps
      refine ⟨N,fun i hi j hj => ?_⟩
      rw [← map_sub]
      exact (le_iSup _ nu).trans_lt (hN i hi j hj)
    have hlocal (nu : I) := contDiffOn_of_uniformCauchy_iteratedFDerivWithin k
      (hs nu) (fun n => L nu (f n)) (L nu g) (fun n => (hf n).1 nu)
      (uniformCauchy_jets_of_coordinateHolderENorm_cauchy k alpha (hs nu)
        _ (fun n => (hf n).1 nu) (hclocal nu)) (hg nu)
    have hgReg : regular L s k g := fun nu => (hlocal nu).1
    have hconv : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        norm L s k alpha (f i-g) < ENNReal.ofReal eps := by
      intro eps heps
      have hdpos : 0 < (k+2 : ℝ) := by positivity
      obtain ⟨N,hN⟩ := hc (eps / (2 * (k+2 : ℝ))) (by positivity)
      let K : ℝ≥0 := (ENNReal.ofReal (eps / (2 * (k+2 : ℝ)))).toNNReal
      have hK : (K : ℝ≥0∞) = ENNReal.ofReal (eps / (2 * (k+2 : ℝ))) :=
        ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
      refine ⟨N,fun i hi => ?_⟩
      have hb : norm L s k alpha (f i-g) ≤ (k+2 : ℕ) * (K : ℝ≥0∞) := by
        apply iSup_le
        intro nu
        rw [map_sub]
        apply coordinateHolderENorm_sub_limit_le (hs nu) (fun n => L nu (f n)) (L nu g)
          (fun n => (hf n).1 nu) (hgReg nu)
          (fun j hj x hx => ((hlocal nu).2 j hj).tendsto_at hx) i
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [← map_sub,hK]
        exact (le_iSup _ nu).trans (hN i hi n hn).le
      refine hb.trans_lt ?_
      rw [hK,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
      apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
      push_cast
      have heq : (k+2 : ℝ) * (eps / (2 * (k+2 : ℝ))) = eps/2 := by field_simp
      rw [heq]
      linarith
    refine ⟨g,⟨hgReg,?_⟩,hconv⟩
    obtain ⟨N,hN⟩ := hconv 1 (by norm_num)
    have hbound := norm_sub_le L s hs k alpha (f N) (f N-g) (hf N).1
      (regular_sub (hf N).1 hgReg)
    rw [sub_sub_cancel] at hbound
    exact hbound.trans_lt (ENNReal.add_lt_top.mpr
      ⟨(hf N).2,(hN N le_rfl).trans ENNReal.ofReal_lt_top⟩)

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

def liftedCovectorLinear (C : BoundedLocalCover M) (nu : C.Index) :
    RawCovector M →ₗ[ℝ] (FourSpace → Fin 4 → ℝ) where
  toFun := (C.chart nu).liftedCovector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liftedVectorLinear (C : BoundedLocalCover M) (nu : C.Index) :
    RawVector M →ₗ[ℝ] (FourSpace → FourSpace) where
  toFun := (C.chart nu).liftedVector
  map_add' u v := by
    funext x
    exact map_add ((C.chart nu).tangentMap x).symm _ _
  map_smul' c u := by
    funext x
    exact map_smul ((C.chart nu).tangentMap x).symm c (u ((C.chart nu).lift x))

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

theorem covector_lifts_separate (C : BoundedLocalCover M) (u : RawCovector M)
    (h : ∀ nu x, x ∈ (C.chart nu).innerDomain → liftedCovectorLinear C nu u x = 0) : u = 0 := by
  ext p v
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  have hrec := (C.chart nu).covector_recover_eval u x v
  have hh : (C.chart nu).liftedCovector u x = 0 := h nu x hx
  rw [hh] at hrec
  simpa [coefficientsToCovector] using hrec.symm

/-- Coordinate Cauchy data reconstructs actual continuous linear covectors on
the original fibers. The result converges in every chart, not only the chosen
chart used in its construction. -/
theorem covector_lifts_reconstruct (C : BoundedLocalCover M) (f : ℕ → RawCovector M)
    (hc : ∀ nu x, x ∈ (C.chart nu).innerDomain →
      CauchySeq (fun n => liftedCovectorLinear C nu (f n) x)) :
    ∃ g : RawCovector M, ∀ nu x, x ∈ (C.chart nu).innerDomain →
      Tendsto (fun n => liftedCovectorLinear C nu (f n) x) atTop
        (𝓝 (liftedCovectorLinear C nu g x)) := by
  classical
  have hpoint (p : M) : ∃ a : TangentSpace I4 p →L[ℝ] ℝ,
      ∀ v, Tendsto (fun n => f n p v) atTop (𝓝 (a v)) := by
    obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
    let c := C.chart nu
    obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (hc nu x hx)
    refine ⟨(coefficientsToCovector a).comp (c.tangentMap x).symm.toContinuousLinearMap,fun v => ?_⟩
    have hh := (coefficientsToCovector_eval_continuous ((c.tangentMap x).symm v)).continuousAt.tendsto.comp ha
    change Tendsto (fun n => coefficientsToCovector (c.liftedCovector (f n) x)
      ((c.tangentMap x).symm v)) atTop (𝓝 (coefficientsToCovector a ((c.tangentMap x).symm v))) at hh
    change Tendsto (fun n => f n (c.lift x) v) atTop
      (𝓝 (coefficientsToCovector a ((c.tangentMap x).symm v)))
    convert hh using 1
    funext n
    exact (c.covector_recover_eval (f n) x v).symm
  choose g hg using hpoint
  refine ⟨g,fun nu x _ => ?_⟩
  apply tendsto_pi_nhds.mpr
  intro a
  exact hg _ _

theorem vector_lifts_separate (C : BoundedLocalCover M) (u : RawVector M)
    (h : ∀ nu x, x ∈ (C.chart nu).innerDomain → liftedVectorLinear C nu u x = 0) : u = 0 := by
  funext p
  obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
  change u ((C.chart nu).lift x) = 0
  have hh := congrArg ((C.chart nu).tangentMap x) (h nu x hx)
  change (C.chart nu).tangentMap x (((C.chart nu).tangentMap x).symm (u ((C.chart nu).lift x))) =
    (C.chart nu).tangentMap x 0 at hh
  simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using hh

/-- Vectors are reconstructed by the genuine tangent equivalence; continuity
of each other inverse tangent map gives convergence in every lifted chart. -/
theorem vector_lifts_reconstruct (C : BoundedLocalCover M) (f : ℕ → RawVector M)
    (hc : ∀ nu x, x ∈ (C.chart nu).innerDomain →
      CauchySeq (fun n => liftedVectorLinear C nu (f n) x)) :
    ∃ g : RawVector M, ∀ nu x, x ∈ (C.chart nu).innerDomain →
      Tendsto (fun n => liftedVectorLinear C nu (f n) x) atTop
        (𝓝 (liftedVectorLinear C nu g x)) := by
  classical
  have hpoint (p : M) : ∃ a : TangentSpace I4 p,
      Tendsto (fun n => f n p) atTop (𝓝 a) := by
    obtain ⟨nu,x,hx,rfl⟩ := C.exists_inner_lift p
    let c := C.chart nu
    obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (hc nu x hx)
    refine ⟨c.tangentMap x a,?_⟩
    have hh := (c.tangentMap x).continuous.continuousAt.tendsto.comp ha
    change Tendsto (fun n => c.tangentMap x ((c.tangentMap x).symm (f n (c.lift x))))
      atTop (𝓝 (c.tangentMap x a)) at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  choose g hg using hpoint
  refine ⟨g,fun nu x _ => ?_⟩
  exact ((C.chart nu).tangentMap x).symm.continuous.continuousAt.tendsto.comp (hg _)

end K24.Global


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
noncomputable section
open scoped NNReal ENNReal
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- The actual ambient covector Hölder sections, with their exact canonical
cover norm, form a Banach space at every finite order. -/
theorem covectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha eta}
      (C.covectorENorm k alpha) := by
  exact CoverHolder.sectionBanach (liftedCovectorLinear C)
    (fun nu => (C.chart nu).innerDomain) (fun nu => (C.chart nu).innerOpen)
    (covector_lifts_separate C) (covector_lifts_reconstruct C) k alpha

/-- The actual ambient vector Hölder sections, with their exact canonical
cover norm, form a Banach space at every finite order. -/
theorem vectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha Y}
      (C.vectorENorm k alpha) := by
  exact CoverHolder.sectionBanach (liftedVectorLinear C)
    (fun nu => (C.chart nu).innerDomain) (fun nu => (C.chart nu).innerOpen)
    (vector_lifts_separate C) (vector_lifts_reconstruct C) k alpha

/-- Ambient Banach foundations for both the natural and shifted vector pairs. -/
theorem vectorCovectorHolder_sectionBanach (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    SectionBanachSpace {eta : RawCovector M | C.CovectorHolder k alpha eta}
      (C.covectorENorm k alpha) ∧
    SectionBanachSpace {Y : RawVector M | C.VectorHolder k alpha Y}
      (C.vectorENorm k alpha) := by
  exact ⟨covectorHolder_sectionBanach C k alpha,vectorHolder_sectionBanach C k alpha⟩

end K24.Global


universe u

theorem solution :
  ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace K24.Global.FourSpace M]
    (C : K24.Global.BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0),
    K24.Global.SectionBanachSpace
      {eta : K24.Global.RawCovector M | C.CovectorHolder k alpha eta}
      (C.covectorENorm k alpha) ∧
    K24.Global.SectionBanachSpace
      {Y : K24.Global.RawVector M | C.VectorHolder k alpha Y}
      (C.vectorENorm k alpha) := by
  intro M _ _ C k alpha
  exact K24.Global.vectorCovectorHolder_sectionBanach C k alpha

#check @solution
#print axioms solution
