-- Prove2me | solution 1 for MarketInterferenceAudit.FluidLimit.theorem_1_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T11:02:13.653982+00:00
-- url     : https://prove2.me/submissions/695c8285-abbd-4a5a-a15f-f51e761b8c2d

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidLimit_PoissonCounts
import Definitions.Def_MarketInterferenceAudit_FluidLimit_Arrivals

set_option autoImplicit false

open MeasureTheory Filter MarketInterference.FluidBias Topology

namespace E81Fluid

open ProbabilityTheory
open scoped Pointwise

variable {nd ns : ℕ} {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]

/-! ## A. Deterministic LP facts -/

lemma feasible_zero (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d : Fin nd → ℝ}
    {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) : Feasible N τ d s 0 := by
  refine ⟨fun e => ⟨le_rfl, by simpa using mul_nonneg hτ (N.k_nonneg e)⟩, fun i => ?_,
    fun j => ?_, fun u => ?_⟩
  · simpa using hd i
  · simpa using hs j
  · simp

lemma obj_le_bound (N : Network nd ns I E) {τ : ℝ} {d : Fin nd → ℝ} {s : Fin ns → ℝ}
    {x : E → ℝ} (hx : Feasible N τ d s x) : obj N x ≤ ∑ e, |N.v e| * (τ * N.k e) := by
  unfold obj
  refine Finset.sum_le_sum fun e _ => ?_
  have h0 := (hx.1 e).1
  have h1 := (hx.1 e).2
  calc N.v e * x e ≤ |N.v e| * x e := mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |N.v e| * (τ * N.k e) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

lemma bddAbove_obj (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) :
    BddAbove (obj N '' {x | Feasible N τ d s x}) := by
  refine ⟨∑ e, |N.v e| * (τ * N.k e), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact obj_le_bound N hx

lemma obj_le_Phi (N : Network nd ns I E) {τ : ℝ} {d : Fin nd → ℝ} {s : Fin ns → ℝ}
    {x : E → ℝ} (hx : Feasible N τ d s x) : obj N x ≤ Phi N τ d s :=
  le_csSup (bddAbove_obj N τ d s) ⟨x, hx, rfl⟩

lemma Phi_nonneg (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d : Fin nd → ℝ}
    {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) : 0 ≤ Phi N τ d s := by
  have h := obj_le_Phi N (feasible_zero N hτ hd hs)
  simpa [obj] using h

lemma Phi_le_bound (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d : Fin nd → ℝ}
    {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) :
    Phi N τ d s ≤ ∑ e, |N.v e| * (τ * N.k e) := by
  refine csSup_le ⟨_, 0, feasible_zero N hτ hd hs, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact obj_le_bound N hx

lemma IsOptimal.obj_eq {N : Network nd ns I E} {τ : ℝ} {d : Fin nd → ℝ} {s : Fin ns → ℝ}
    {x : E → ℝ} (h : IsOptimal N τ d s x) : obj N x = Phi N τ d s := by
  refine le_antisymm (obj_le_Phi N h.1) (csSup_le ⟨_, x, h.1, rfl⟩ ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact h.2 y hy

/-- closedness of feasibility under limits of (x, d, s) -/
lemma feasible_of_tendsto (N : Network nd ns I E) {τ : ℝ} {d : ℕ → Fin nd → ℝ}
    {s : ℕ → Fin ns → ℝ} {x : ℕ → E → ℝ} {lam : Fin nd → ℝ} {pi : Fin ns → ℝ} {x0 : E → ℝ}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    (hx : Tendsto x atTop (𝓝 x0)) (hf : ∀ n, Feasible N τ (d n) (s n) (x n)) :
    Feasible N τ lam pi x0 := by
  have hxe : ∀ e, Tendsto (fun n => x n e) atTop (𝓝 (x0 e)) := tendsto_pi_nhds.1 hx
  have hdi : ∀ i, Tendsto (fun n => d n i) atTop (𝓝 (lam i)) := tendsto_pi_nhds.1 hd
  have hsj : ∀ j, Tendsto (fun n => s n j) atTop (𝓝 (pi j)) := tendsto_pi_nhds.1 hs
  have hsum : ∀ (T : Finset E), Tendsto (fun n => ∑ e ∈ T, x n e) atTop (𝓝 (∑ e ∈ T, x0 e)) :=
    fun T => tendsto_finsetSum _ fun e _ => hxe e
  refine ⟨fun e => ⟨?_, ?_⟩, fun i => ?_, fun j => ?_, fun u => ?_⟩
  · exact ge_of_tendsto' (hxe e) fun n => ((hf n).1 e).1
  · exact le_of_tendsto' (hxe e) fun n => ((hf n).1 e).2
  · exact le_of_tendsto_of_tendsto' (hsum _) (hdi i) fun n => (hf n).2.1 i
  · exact le_of_tendsto_of_tendsto' (hsum _) (hsj j) fun n => (hf n).2.2.1 j
  · exact tendsto_nhds_unique ((hsum _).congr fun n => ((hf n).2.2.2 u)) (hsum _)

lemma feasible_box {N : Network nd ns I E} {τ : ℝ} {d : Fin nd → ℝ} {s : Fin ns → ℝ}
    {x : E → ℝ} (hx : Feasible N τ d s x) :
    x ∈ Set.pi Set.univ (fun e => Set.Icc (0 : ℝ) (τ * N.k e)) :=
  fun e _ => hx.1 e

lemma isCompact_box (N : Network nd ns I E) (τ : ℝ) :
    IsCompact (Set.pi Set.univ (fun e => Set.Icc (0 : ℝ) (τ * N.k e))) :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma isClosed_feasible (N : Network nd ns I E) (τ : ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) :
    IsClosed {x | Feasible N τ d s x} := by
  refine IsSeqClosed.isClosed fun {x} {x0} hx hlim => ?_
  exact feasible_of_tendsto N (d := fun _ => d) (s := fun _ => s) tendsto_const_nhds
    tendsto_const_nhds hlim hx

lemma continuous_obj (N : Network nd ns I E) : Continuous (obj N) := by
  unfold obj
  exact continuous_finset_sum _ fun e _ => continuous_const.mul (continuous_apply e)

lemma obj_smul (N : Network nd ns I E) (t : ℝ) (y : E → ℝ) : obj N (t • y) = t * obj N y := by
  unfold obj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma exists_isOptimal (N : Network nd ns I E) {τ : ℝ} (hτ : 0 ≤ τ) {d : Fin nd → ℝ}
    {s : Fin ns → ℝ} (hd : ∀ i, 0 ≤ d i) (hs : ∀ j, 0 ≤ s j) :
    ∃ x, IsOptimal N τ d s x := by
  have hc : IsCompact {x | Feasible N τ d s x} :=
    (isCompact_box N τ).of_isClosed_subset (isClosed_feasible N τ d s) fun x hx => feasible_box hx
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn ⟨0, feasible_zero N hτ hd hs⟩
    (continuous_obj N).continuousOn
  exact ⟨x, hx, fun y hy => isMaxOn_iff.mp hmax y hy⟩

lemma feasible_smul_iff (N : Network nd ns I E) {τ : ℝ} (hτ : 0 < τ) (d : Fin nd → ℝ)
    (s : Fin ns → ℝ) (y : E → ℝ) :
    Feasible N τ d s (τ • y) ↔ Feasible N 1 (fun i => d i / τ) (fun j => s j / τ) y := by
  unfold Feasible
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ⟨?_, ?_⟩, fun i => (le_div_iff₀' hτ).2 (h2 i),
      fun j => (le_div_iff₀' hτ).2 (h3 j), fun u => mul_left_cancel₀ hτ.ne' (h4 u)⟩
    · nlinarith [(h1 e).1]
    · nlinarith [(h1 e).2]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ⟨?_, ?_⟩, fun i => (le_div_iff₀' hτ).1 (h2 i),
      fun j => (le_div_iff₀' hτ).1 (h3 j), fun u => by rw [h4 u]⟩
    · exact mul_nonneg hτ.le (h1 e).1
    · nlinarith [(h1 e).2]

lemma Phi_scale (N : Network nd ns I E) {τ : ℝ} (hτ : 0 < τ) (d : Fin nd → ℝ)
    (s : Fin ns → ℝ) :
    Phi N τ d s / τ = Phi N 1 (fun i => d i / τ) (fun j => s j / τ) := by
  have hset : obj N '' {x | Feasible N τ d s x} =
      τ • (obj N '' {x | Feasible N 1 (fun i => d i / τ) (fun j => s j / τ) x}) := by
    ext z
    simp only [Set.mem_image, Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨obj N (τ⁻¹ • x), ⟨τ⁻¹ • x, ?_, rfl⟩, ?_⟩
      · rw [← feasible_smul_iff N hτ, smul_inv_smul₀ hτ.ne']
        exact hx
      · rw [obj_smul, ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨τ • y, (feasible_smul_iff N hτ d s y).2 hy, obj_smul N τ y⟩
  unfold Phi
  rw [hset, Real.sSup_smul_of_nonneg hτ.le, smul_eq_mul, mul_div_cancel_left₀ _ hτ.ne']

/-- scaling a limit-feasible point into the sample-feasible set -/
lemma eventually_smul_feasible (N : Network nd ns I E) {lam : Fin nd → ℝ} {pi : Fin ns → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hpi : ∀ j, 0 ≤ pi j)
    {d : ℕ → Fin nd → ℝ} {s : ℕ → Fin ns → ℝ}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    (hd0 : ∀ n i, 0 ≤ d n i) (hs0 : ∀ n j, 0 ≤ s n j)
    {y : E → ℝ} (hy : Feasible N 1 lam pi y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∀ᶠ n in atTop, Feasible N 1 (d n) (s n) (t • y) := by
  have hD : ∀ i, ∀ᶠ n in atTop, t * lam i ≤ d n i := by
    intro i
    rcases (hlam i).eq_or_lt with h | h
    · exact Filter.Eventually.of_forall fun n => by rw [← h, mul_zero]; exact hd0 n i
    · have : t * lam i < lam i := by nlinarith
      exact ((tendsto_pi_nhds.1 hd i).eventually (lt_mem_nhds this)).mono fun n hn => hn.le
  have hS : ∀ j, ∀ᶠ n in atTop, t * pi j ≤ s n j := by
    intro j
    rcases (hpi j).eq_or_lt with h | h
    · exact Filter.Eventually.of_forall fun n => by rw [← h, mul_zero]; exact hs0 n j
    · have : t * pi j < pi j := by nlinarith
      exact ((tendsto_pi_nhds.1 hs j).eventually (lt_mem_nhds this)).mono fun n hn => hn.le
  filter_upwards [Filter.eventually_all.2 hD, Filter.eventually_all.2 hS] with n hn1 hn2
  refine ⟨fun e => ⟨?_, ?_⟩, fun i => ?_, fun j => ?_, fun u => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg ht0 (hy.1 e).1
  · simp only [Pi.smul_apply, smul_eq_mul]
    calc t * y e ≤ y e := mul_le_of_le_one_left (hy.1 e).1 ht1.le
      _ ≤ 1 * N.k e := (hy.1 e).2
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hy.2.1 i) ht0).trans (hn1 i)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hy.2.2.1 j) ht0).trans (hn2 j)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hy.2.2.2 u]

/-- every subsequence of sample optimizers has a further subsequence converging to a
limit optimizer -/
lemma cluster_isOptimal (N : Network nd ns I E) {lam : Fin nd → ℝ} {pi : Fin ns → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hpi : ∀ j, 0 ≤ pi j)
    {d : ℕ → Fin nd → ℝ} {s : ℕ → Fin ns → ℝ}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    (hd0 : ∀ n i, 0 ≤ d n i) (hs0 : ∀ n j, 0 ≤ s n j)
    {X : ℕ → E → ℝ} (hX : ∀ n, IsOptimal N 1 (d n) (s n) (X n))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ∃ ψ : ℕ → ℕ, ∃ x, StrictMono ψ ∧ IsOptimal N 1 lam pi x ∧
      Tendsto (fun n => X (φ (ψ n))) atTop (𝓝 x) := by
  obtain ⟨x, -, ψ, hψ, hx⟩ := (isCompact_box N 1).tendsto_subseq
    (x := fun n => X (φ n)) fun n => feasible_box (hX (φ n)).1
  have hmono : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  have hdm : Tendsto (fun n => d (φ (ψ n))) atTop (𝓝 lam) := hd.comp hmono
  have hsm : Tendsto (fun n => s (φ (ψ n))) atTop (𝓝 pi) := hs.comp hmono
  have hxf : Feasible N 1 lam pi x :=
    feasible_of_tendsto N hdm hsm hx fun n => (hX (φ (ψ n))).1
  refine ⟨ψ, x, hψ, ⟨hxf, fun y hy => ?_⟩, hx⟩
  have h2 : Tendsto (fun n => obj N (X (φ (ψ n)))) atTop (𝓝 (obj N x)) :=
    ((continuous_obj N).tendsto x).comp hx
  have key : ∀ t : ℝ, 0 ≤ t → t < 1 → t * obj N y ≤ obj N x := by
    intro t ht0 ht1
    have h1 := eventually_smul_feasible N hlam hpi hdm hsm (fun n => hd0 _) (fun n => hs0 _)
      hy ht0 ht1
    refine ge_of_tendsto h2 (h1.mono fun n hn => ?_)
    have := (hX (φ (ψ n))).2 _ hn
    rwa [obj_smul] at this
  have hlim : Tendsto (fun t : ℝ => t * obj N y) (𝓝[<] 1) (𝓝 (obj N y)) := by
    have h := (continuous_mul_right (obj N y)).tendsto 1
    rw [one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT one_pos)
    fun t ht => key t ht.1.le ht.2)

lemma tendsto_Phi (N : Network nd ns I E) {lam : Fin nd → ℝ} {pi : Fin ns → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hpi : ∀ j, 0 ≤ pi j)
    {d : ℕ → Fin nd → ℝ} {s : ℕ → Fin ns → ℝ}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    (hd0 : ∀ n i, 0 ≤ d n i) (hs0 : ∀ n j, 0 ≤ s n j) :
    Tendsto (fun n => Phi N 1 (d n) (s n)) atTop (𝓝 (Phi N 1 lam pi)) := by
  choose X hX using fun n => exists_isOptimal N zero_le_one (hd0 n) (hs0 n)
  have hPhi : (fun n => Phi N 1 (d n) (s n)) = fun n => obj N (X n) :=
    funext fun n => (IsOptimal.obj_eq (hX n)).symm
  rw [hPhi]
  refine tendsto_of_subseq_tendsto fun φ hφ => ?_
  obtain ⟨ψ, x, -, hx, hlim⟩ := cluster_isOptimal N hlam hpi hd hs hd0 hs0 hX hφ
  refine ⟨ψ, ?_⟩
  rw [← IsOptimal.obj_eq hx]
  exact ((continuous_obj N).tendsto x).comp hlim

lemma tendsto_primal (N : Network nd ns I E) {lam : Fin nd → ℝ} {pi : Fin ns → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hpi : ∀ j, 0 ≤ pi j)
    {d : ℕ → Fin nd → ℝ} {s : ℕ → Fin ns → ℝ}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    (hd0 : ∀ n i, 0 ≤ d n i) (hs0 : ∀ n j, 0 ≤ s n j)
    {X : ℕ → E → ℝ} (hX : ∀ n, IsOptimal N 1 (d n) (s n) (X n))
    {xstar : E → ℝ} (huniq : ∀ x, IsOptimal N 1 lam pi x → x = xstar) :
    Tendsto X atTop (𝓝 xstar) := by
  refine tendsto_of_subseq_tendsto fun φ hφ => ?_
  obtain ⟨ψ, x, -, hx, hlim⟩ := cluster_isOptimal N hlam hpi hd hs hd0 hs0 hX hφ
  refine ⟨ψ, ?_⟩
  rw [← huniq x hx]
  exact hlim

/-! ### Dual side: work in the vector space `DV`. -/

abbrev DV (nd ns : ℕ) (I E : Type) := (Fin nd → ℝ) × (Fin ns → ℝ) × (I → ℝ) × (E → ℝ)

def toVec (q : DualVar nd ns I E) : DV nd ns I E := (q.a, q.b, q.m, q.ξ)

def ofVec (v : DV nd ns I E) : DualVar nd ns I E := ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩

lemma continuous_tailPot (N : Network nd ns I E) (e : E) :
    Continuous fun v : DV nd ns I E => tailPot (N := N) (ofVec v) e := by
  unfold tailPot
  cases N.tail e with
  | inl j => exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  | inr u =>
    exact (continuous_apply u).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))

lemma continuous_headPot (N : Network nd ns I E) (e : E) :
    Continuous fun v : DV nd ns I E => headPot (N := N) (ofVec v) e := by
  unfold headPot
  cases N.head e with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr w =>
    exact ((continuous_apply w).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).neg

lemma tailPot_seg (N : Network nd ns I E) (a b : DV nd ns I E) (t : ℝ) (e : E) :
    tailPot (N := N) (ofVec (a + t • (b - a))) e =
      tailPot (N := N) (ofVec a) e +
        t * (tailPot (N := N) (ofVec b) e - tailPot (N := N) (ofVec a) e) := by
  unfold tailPot
  cases N.tail e <;> simp [ofVec]

lemma headPot_seg (N : Network nd ns I E) (a b : DV nd ns I E) (t : ℝ) (e : E) :
    headPot (N := N) (ofVec (a + t • (b - a))) e =
      headPot (N := N) (ofVec a) e +
        t * (headPot (N := N) (ofVec b) e - headPot (N := N) (ofVec a) e) := by
  unfold headPot
  cases N.head e <;> simp [ofVec] <;> ring

lemma seg_sum {X : Type} [Fintype X] (f g c : X → ℝ) (t : ℝ) :
    ∑ x, (f x + t * (g x - f x)) * c x =
      ∑ x, f x * c x + t * (∑ x, g x * c x - ∑ x, f x * c x) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma dualObj_seg (N : Network nd ns I E) (d : Fin nd → ℝ) (s : Fin ns → ℝ)
    (a b : DV nd ns I E) (t : ℝ) :
    dualObj N 1 d s (ofVec (a + t • (b - a))) = dualObj N 1 d s (ofVec a) +
      t * (dualObj N 1 d s (ofVec b) - dualObj N 1 d s (ofVec a)) := by
  simp only [dualObj, ofVec, mul_one, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [seg_sum, seg_sum, seg_sum]
  ring

lemma seg_obj_le (N : Network nd ns I E) {d : Fin nd → ℝ} {s : Fin ns → ℝ}
    {a b : DV nd ns I E} {t : ℝ} (ht : 0 ≤ t)
    (h : dualObj N 1 d s (ofVec b) ≤ dualObj N 1 d s (ofVec a)) :
    dualObj N 1 d s (ofVec (a + t • (b - a))) ≤ dualObj N 1 d s (ofVec a) := by
  rw [dualObj_seg]
  have := mul_nonneg ht (sub_nonneg.2 h)
  linarith

lemma dualFeasible_seg (N : Network nd ns I E) {a b : DV nd ns I E}
    (ha : DualFeasible N (ofVec a)) (hb : DualFeasible N (ofVec b)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : DualFeasible N (ofVec (a + t • (b - a))) := by
  refine ⟨fun e => ?_, fun i => ?_, fun j => ?_, fun e => ?_⟩
  · have hx : (ofVec (a + t • (b - a))).ξ e = a.2.2.2 e + t * (b.2.2.2 e - a.2.2.2 e) := rfl
    have h1 : N.v e ≤ tailPot (N := N) (ofVec a) e + headPot (N := N) (ofVec a) e + a.2.2.2 e :=
      ha.1 e
    have h2 : N.v e ≤ tailPot (N := N) (ofVec b) e + headPot (N := N) (ofVec b) e + b.2.2.2 e :=
      hb.1 e
    rw [tailPot_seg, headPot_seg, hx]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 ht1), mul_le_mul_of_nonneg_left h2 ht0]
  · have h1 : 0 ≤ a.1 i := ha.2.1 i
    have h2 : 0 ≤ b.1 i := hb.2.1 i
    show 0 ≤ a.1 i + t * (b.1 i - a.1 i)
    nlinarith [mul_nonneg ht0 h2, mul_nonneg (sub_nonneg.2 ht1) h1]
  · have h1 : 0 ≤ a.2.1 j := ha.2.2.1 j
    have h2 : 0 ≤ b.2.1 j := hb.2.2.1 j
    show 0 ≤ a.2.1 j + t * (b.2.1 j - a.2.1 j)
    nlinarith [mul_nonneg ht0 h2, mul_nonneg (sub_nonneg.2 ht1) h1]
  · have h1 : 0 ≤ a.2.2.2 e := ha.2.2.2 e
    have h2 : 0 ≤ b.2.2.2 e := hb.2.2.2 e
    show 0 ≤ a.2.2.2 e + t * (b.2.2.2 e - a.2.2.2 e)
    nlinarith [mul_nonneg ht0 h2, mul_nonneg (sub_nonneg.2 ht1) h1]

lemma dualFeasible_of_tendsto (N : Network nd ns I E) {v : ℕ → DV nd ns I E}
    {v0 : DV nd ns I E} (hv : Tendsto v atTop (𝓝 v0)) (hf : ∀ n, DualFeasible N (ofVec (v n))) :
    DualFeasible N (ofVec v0) := by
  have ha : Tendsto (fun n => (v n).1) atTop (𝓝 v0.1) := (continuous_fst.tendsto _).comp hv
  have hb : Tendsto (fun n => (v n).2.1) atTop (𝓝 v0.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hv
  have hx : Tendsto (fun n => (v n).2.2.2) atTop (𝓝 v0.2.2.2) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hv
  refine ⟨fun e => ?_, fun i => ?_, fun j => ?_, fun e => ?_⟩
  · have hT := ((continuous_tailPot N e).tendsto v0).comp hv
    have hH := ((continuous_headPot N e).tendsto v0).comp hv
    exact ge_of_tendsto ((hT.add hH).add (tendsto_pi_nhds.1 hx e))
      (Filter.Eventually.of_forall fun n => (hf n).1 e)
  · exact ge_of_tendsto (tendsto_pi_nhds.1 ha i) (Filter.Eventually.of_forall fun n => (hf n).2.1 i)
  · exact ge_of_tendsto (tendsto_pi_nhds.1 hb j)
      (Filter.Eventually.of_forall fun n => (hf n).2.2.1 j)
  · exact ge_of_tendsto (tendsto_pi_nhds.1 hx e)
      (Filter.Eventually.of_forall fun n => (hf n).2.2.2 e)

lemma tendsto_dualObj (N : Network nd ns I E) {d : ℕ → Fin nd → ℝ} {s : ℕ → Fin ns → ℝ}
    {lam : Fin nd → ℝ} {pi : Fin ns → ℝ} {v : ℕ → DV nd ns I E} {v0 : DV nd ns I E}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    (hv : Tendsto v atTop (𝓝 v0)) :
    Tendsto (fun n => dualObj N 1 (d n) (s n) (ofVec (v n))) atTop
      (𝓝 (dualObj N 1 lam pi (ofVec v0))) := by
  have h1 : Tendsto (fun n => (v n).1) atTop (𝓝 v0.1) := (continuous_fst.tendsto _).comp hv
  have h2 : Tendsto (fun n => (v n).2.1) atTop (𝓝 v0.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hv
  have h4 : Tendsto (fun n => (v n).2.2.2) atTop (𝓝 v0.2.2.2) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hv
  simp only [dualObj, ofVec]
  refine ((tendsto_finsetSum _ fun i _ => ?_).add (tendsto_finsetSum _ fun j _ => ?_)).add
    (tendsto_finsetSum _ fun e _ => ?_)
  · exact (tendsto_pi_nhds.1 h1 i).mul (tendsto_pi_nhds.1 hd i)
  · exact (tendsto_pi_nhds.1 h2 j).mul (tendsto_pi_nhds.1 hs j)
  · exact ((tendsto_pi_nhds.1 h4 e).mul tendsto_const_nhds).mul tendsto_const_nhds

lemma seg_mem_sphere (c u : DV nd ns I E) {ε : ℝ} (hε : 0 < ε) (hδ : 0 < dist u c) :
    c + (ε / dist u c) • (u - c) ∈ Metric.sphere c ε := by
  rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hε hδ), ← dist_eq_norm, div_mul_cancel₀ _ hδ.ne']

lemma tendsto_dual (N : Network nd ns I E) {lam : Fin nd → ℝ} {pi : Fin ns → ℝ}
    {d : ℕ → Fin nd → ℝ} {s : ℕ → Fin ns → ℝ}
    (hd : Tendsto d atTop (𝓝 lam)) (hs : Tendsto s atTop (𝓝 pi))
    {Q : ℕ → DualVar nd ns I E} (hQ : ∀ n, IsOptimalDual N 1 (d n) (s n) (Q n))
    {qstar : DualVar nd ns I E} (hq : IsOptimalDual N 1 lam pi qstar)
    (huniq : ∀ q, IsOptimalDual N 1 lam pi q → q = qstar) :
    Tendsto (fun n => toVec (Q n)) atTop (𝓝 (toVec qstar)) := by
  rw [Metric.tendsto_atTop]
  by_contra hcon
  push_neg at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop (Filter.frequently_atTop.2 hfreq)
  have hδ : ∀ n, 0 < dist (toVec (Q (φ n))) (toVec qstar) := fun n => hε.trans_le (hφP n)
  have hY : ∀ n, toVec qstar + (ε / dist (toVec (Q (φ n))) (toVec qstar)) •
      (toVec (Q (φ n)) - toVec qstar) ∈ Metric.sphere (toVec qstar) ε :=
    fun n => seg_mem_sphere _ _ hε (hδ n)
  obtain ⟨yl, hyl, ψ, hψ, hlim⟩ := (isCompact_sphere (toVec qstar) ε).tendsto_subseq hY
  have ht : ∀ n, 0 ≤ ε / dist (toVec (Q (φ n))) (toVec qstar) ∧
      ε / dist (toVec (Q (φ n))) (toVec qstar) ≤ 1 :=
    fun n => ⟨(div_pos hε (hδ n)).le, (div_le_one (hδ n)).2 (hφP n)⟩
  have hmono : Tendsto (fun n => φ (ψ n)) atTop atTop := (hφ.comp hψ).tendsto_atTop
  have hylf : DualFeasible N (ofVec yl) := dualFeasible_of_tendsto N hlim fun n =>
    dualFeasible_seg N (a := toVec qstar) (b := toVec (Q (φ (ψ n)))) hq.1 (hQ (φ (ψ n))).1
      (ht (ψ n)).1 (ht (ψ n)).2
  have hL := tendsto_dualObj N (hd.comp hmono) (hs.comp hmono) hlim
  have hR := tendsto_dualObj N (hd.comp hmono) (hs.comp hmono)
    (tendsto_const_nhds (x := toVec qstar))
  have hle : dualObj N 1 lam pi (ofVec yl) ≤ dualObj N 1 lam pi (ofVec (toVec qstar)) :=
    le_of_tendsto_of_tendsto' hL hR fun n =>
      seg_obj_le N (a := toVec qstar) (b := toVec (Q (φ (ψ n)))) (ht (ψ n)).1
        ((hQ (φ (ψ n))).2 qstar hq.1)
  have hopt : IsOptimalDual N 1 lam pi (ofVec yl) := ⟨hylf, fun q' hq' => hle.trans (hq.2 q' hq')⟩
  have heq : yl = toVec qstar := congrArg toVec (huniq _ hopt)
  rw [heq, Metric.mem_sphere, dist_self] at hyl
  exact hε.ne hyl

/-! ## B. Probability -/

lemma exp_sub_one_le {t : ℝ} (ht : |t| ≤ 1) : Real.exp t - 1 ≤ t + t ^ 2 := by
  have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le ht)).2
  linarith

lemma poisson_mgf (r : NNReal) (t : ℝ) :
    Integrable (fun k : ℕ => Real.exp (t * k)) (poissonMeasure r) ∧
    ∫ k : ℕ, Real.exp (t * k) ∂(poissonMeasure r) = Real.exp (r * (Real.exp t - 1)) := by
  have hterm : ∀ n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) *
      Real.exp (t * n) = Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp t) ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    rw [mul_comm t, Real.exp_nat_mul, mul_pow]
    ring
  have hint : Integrable (fun k : ℕ => Real.exp (t * k)) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    refine ((Real.summable_pow_div_factorial ((r : ℝ) * Real.exp t)).mul_left
      (Real.exp (-(r : ℝ)))).congr fun n => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, hterm]
  refine ⟨hint, ?_⟩
  have h1 := hasSum_integral_poissonMeasure hint
  have h0 : HasSum (fun n : ℕ => ((r : ℝ) * Real.exp t) ^ n / (Nat.factorial n : ℝ))
      (Real.exp ((r : ℝ) * Real.exp t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have h3 : HasSum (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ)) •
      Real.exp (t * n)) (Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * Real.exp t)) := by
    have hfun : (fun n : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ)) •
        Real.exp (t * n)) = fun n : ℕ => Real.exp (-(r : ℝ)) *
          (((r : ℝ) * Real.exp t) ^ n / (Nat.factorial n : ℝ)) :=
      funext fun n => by rw [smul_eq_mul, hterm]
    rw [hfun]
    exact h0.mul_left _
  rw [h1.unique h3, ← Real.exp_add]
  congr 1
  ring

lemma poisson_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {μ m : ℝ} (hμ : 0 ≤ μ) (hm : 0 ≤ m) (Y : Ω → ℕ) (hY : Measurable Y)
    (hlaw : Measure.map Y P = poissonMeasure (Real.toNNReal (μ * m)))
    {t ε : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htε : μ * t ≤ ε / 2) :
    P.real {ω | (μ + ε) * m ≤ (Y ω : ℝ)} ≤ Real.exp (-(t * ε / 2) * m) ∧
    P.real {ω | (Y ω : ℝ) ≤ (μ - ε) * m} ≤ Real.exp (-(t * ε / 2) * m) := by
  have hr : ((Real.toNNReal (μ * m) : NNReal) : ℝ) = μ * m :=
    Real.coe_toNNReal _ (mul_nonneg hμ hm)
  have hmgf : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * (Y ω : ℝ))) P ∧
      mgf (fun ω => (Y ω : ℝ)) P s = Real.exp (μ * m * (Real.exp s - 1)) := by
    intro s
    obtain ⟨hi, he⟩ := poisson_mgf (Real.toNNReal (μ * m)) s
    rw [← hlaw] at hi he
    rw [hr] at he
    have hae : AEStronglyMeasurable (fun k : ℕ => Real.exp (s * k)) (Measure.map Y P) :=
      .of_discrete
    refine ⟨(integrable_map_measure hae hY.aemeasurable).1 hi, ?_⟩
    rw [mgf, ← he]
    exact (integral_map hY.aemeasurable hae).symm
  have hq : μ * t * (t * m) ≤ ε / 2 * (t * m) :=
    mul_le_mul_of_nonneg_right htε (mul_nonneg ht0 hm)
  constructor
  · obtain ⟨hi, he⟩ := hmgf t
    refine (measure_ge_le_exp_mul_mgf ((μ + ε) * m) ht0 hi).trans ?_
    rw [he, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := exp_sub_one_le (t := t) (by rw [abs_of_nonneg ht0]; exact ht1)
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hμ hm)]
  · obtain ⟨hi, he⟩ := hmgf (-t)
    refine (measure_le_le_exp_mul_mgf ((μ - ε) * m) (neg_nonpos.2 ht0) hi).trans ?_
    rw [he, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := exp_sub_one_le (t := -t) (by rw [abs_neg, abs_of_nonneg ht0]; exact ht1)
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hμ hm)]

/-- Poisson strong law along densities `n+1`, for an arbitrary coupling (complete
convergence via Chernoff bounds and Borel–Cantelli). -/
lemma ae_tendsto_poisson {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {μ : ℝ} (hμ : 0 ≤ μ) (Y : ℕ → Ω → ℕ)
    (hY : ∀ n, Measurable (Y n))
    (hlaw : ∀ n, Measure.map (Y n) P =
      ProbabilityTheory.poissonMeasure (Real.toNNReal (μ * ((n + 1 : ℕ) : ℝ)))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 μ) := by
  have hm : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      |(Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ) - μ| < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / ((k : ℝ) + 1) := ⟨_, rfl⟩
    rw [← hεdef]
    have hε : 0 < ε := by rw [hεdef]; positivity
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = min 1 (ε / (2 * μ + 1)) := ⟨_, rfl⟩
    have htpos : 0 < t := by rw [htdef]; exact lt_min one_pos (div_pos hε (by positivity))
    have ht1 : t ≤ 1 := by rw [htdef]; exact min_le_left _ _
    have htε : μ * t ≤ ε / 2 := by
      have h1 : t ≤ ε / (2 * μ + 1) := by rw [htdef]; exact min_le_right _ _
      have h2 : μ * t ≤ μ * (ε / (2 * μ + 1)) := mul_le_mul_of_nonneg_left h1 hμ
      have h3 : μ * (ε / (2 * μ + 1)) ≤ ε / 2 := by
        have hq : μ / (2 * μ + 1) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        calc μ * (ε / (2 * μ + 1)) = ε * (μ / (2 * μ + 1)) := by ring
          _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left hq hε.le
          _ = ε / 2 := by ring
      linarith
    have hc : 0 < t * ε / 2 := by positivity
    have hA : ∀ n, P.real {ω | ε ≤ |(Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ) - μ|} ≤
        2 * Real.exp (-(t * ε / 2)) ^ n := by
      intro n
      obtain ⟨h1, h2⟩ := poisson_tail P hμ (hm n).le (Y n) (hY n) (hlaw n) htpos.le ht1 htε
      have hsub : {ω | ε ≤ |(Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ) - μ|} ⊆
          {ω | (μ + ε) * ((n + 1 : ℕ) : ℝ) ≤ (Y n ω : ℝ)} ∪
            {ω | (Y n ω : ℝ) ≤ (μ - ε) * ((n + 1 : ℕ) : ℝ)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        rcases le_abs.1 hω with h | h
        · exact Or.inl ((le_div_iff₀ (hm n)).1 (by linarith))
        · exact Or.inr ((div_le_iff₀ (hm n)).1 (by linarith))
      have hexp : Real.exp (-(t * ε / 2) * ((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-(t * ε / 2)) ^ n := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        push_cast
        nlinarith
      calc P.real {ω | ε ≤ |(Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ) - μ|}
          ≤ P.real ({ω | (μ + ε) * ((n + 1 : ℕ) : ℝ) ≤ (Y n ω : ℝ)} ∪
            {ω | (Y n ω : ℝ) ≤ (μ - ε) * ((n + 1 : ℕ) : ℝ)}) := measureReal_mono hsub
        _ ≤ P.real {ω | (μ + ε) * ((n + 1 : ℕ) : ℝ) ≤ (Y n ω : ℝ)} +
            P.real {ω | (Y n ω : ℝ) ≤ (μ - ε) * ((n + 1 : ℕ) : ℝ)} := measureReal_union_le _ _
        _ ≤ 2 * Real.exp (-(t * ε / 2)) ^ n := by linarith
    have hsum : Summable (fun n : ℕ => 2 * Real.exp (-(t * ε / 2)) ^ n) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith))).mul_left 2
    have hfin : ∑' n, P {ω | ε ≤ |(Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ) - μ|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top
        (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, 2 * Real.exp (-(t * ε / 2)) ^ n)) ?_
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
      refine ENNReal.tsum_le_tsum fun n => ?_
      rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
      exact ENNReal.ofReal_le_ofReal (hA n)
    filter_upwards [ae_eventually_notMem hfin] with ω hω
    exact hω.mono fun n hn => lt_of_not_ge hn
  filter_upwards [ae_all_iff.2 hk] with ω hω
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (hω k)
  exact ⟨N0, fun n hn => by rw [Real.dist_eq]; exact (hN0 n hn).trans hk'⟩

end E81Fluid

open MeasureTheory Filter MarketInterference.FluidBias in
theorem solution {nd ns : ℕ} {I E : Type} [Fintype I] [Fintype E]
    [DecidableEq I] (N : Network nd ns I E)
    (lam : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hpi : ∀ j, 0 ≤ pi j)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : MarketInterferenceAudit.FluidLimit.Arrivals P lam pi) :
    (∀ r, Integrable (R.scaledValue N r) P) ∧
    Tendsto (fun r => ∫ ω, R.scaledValue N r ω ∂P) atTop (nhds (Phi N 1 lam pi)) ∧
    (∀ (xstar : E → ℝ) (qstar : DualVar nd ns I E),
      IsOptimal N 1 lam pi xstar →
      (∀ x, IsOptimal N 1 lam pi x → x = xstar) →
      IsOptimalDual N 1 lam pi qstar →
      (∀ q, IsOptimalDual N 1 lam pi q → q = qstar) →
      ∀ (X : ℕ → Ω → E → ℝ) (Q : ℕ → Ω → DualVar nd ns I E),
        (∀ r, ∀ᵐ ω ∂P, IsOptimal N 1 (R.demand r ω) (R.supply r ω) (X r ω)) →
        (∀ r, ∀ᵐ ω ∂P, IsOptimalDual N 1 (R.demand r ω) (R.supply r ω) (Q r ω)) →
        ∀ᵐ ω ∂P,
          (∀ e, Tendsto (fun r => X r ω e) atTop (nhds (xstar e))) ∧
          (∀ i, Tendsto (fun r => (Q r ω).a i) atTop (nhds (qstar.a i))) ∧
          (∀ j, Tendsto (fun r => (Q r ω).b j) atTop (nhds (qstar.b j))) ∧
          (∀ u, Tendsto (fun r => (Q r ω).m u) atTop (nhds (qstar.m u))) ∧
          (∀ e, Tendsto (fun r => (Q r ω).ξ e) atTop (nhds (qstar.ξ e)))) := by
  have hpos : ∀ r : ℕ, (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := fun r => by positivity
  have hscale : ∀ r ω, R.scaledValue N r ω = Phi N 1 (R.demand r ω) (R.supply r ω) :=
    fun r ω => E81Fluid.Phi_scale N (hpos r) _ _
  have hdem0 : ∀ r ω i, 0 ≤ R.demand r ω i := fun r ω i =>
    div_nonneg (Nat.cast_nonneg _) (hpos r).le
  have hsup0 : ∀ r ω j, 0 ≤ R.supply r ω j := fun r ω j =>
    div_nonneg (Nat.cast_nonneg _) (hpos r).le
  have hbound : ∀ r ω, ‖R.scaledValue N r ω‖ ≤ ∑ e, |N.v e| * (1 * N.k e) := by
    intro r ω
    rw [hscale, Real.norm_eq_abs,
      abs_of_nonneg (E81Fluid.Phi_nonneg N zero_le_one (hdem0 r ω) (hsup0 r ω))]
    exact E81Fluid.Phi_le_bound N zero_le_one (hdem0 r ω) (hsup0 r ω)
  have hmeas : ∀ r, AEStronglyMeasurable (R.scaledValue N r) P := by
    intro r
    have : R.scaledValue N r = (fun z : (Fin nd → ℕ) × (Fin ns → ℕ) =>
        Phi N ((r + 1 : ℕ) : ℝ) (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ)) /
          ((r + 1 : ℕ) : ℝ)) ∘ R.counts r := rfl
    rw [this]
    exact (Measurable.of_discrete.comp (R.measurable_counts r)).aestronglyMeasurable
  have hint : ∀ r, Integrable (R.scaledValue N r) P := fun r =>
    Integrable.of_bound (hmeas r) _ (Filter.Eventually.of_forall fun ω => hbound r ω)
  have hlawD : ∀ i r, Measure.map (fun ω => (R.counts r ω).1 i) P =
      ProbabilityTheory.poissonMeasure (Real.toNNReal (lam i * ((r + 1 : ℕ) : ℝ))) := by
    intro i r
    have : (fun ω => (R.counts r ω).1 i) = Function.eval i ∘ (Prod.fst ∘ R.counts r) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i)
      (measurable_fst.comp (R.measurable_counts r)),
      ← Measure.map_map measurable_fst (R.measurable_counts r), R.law r]
    simp [MarketInterference.FluidLimit.fluidLaw, Measure.pi_map_eval]
  have hlawS : ∀ j r, Measure.map (fun ω => (R.counts r ω).2 j) P =
      ProbabilityTheory.poissonMeasure (Real.toNNReal (pi j * ((r + 1 : ℕ) : ℝ))) := by
    intro j r
    have : (fun ω => (R.counts r ω).2 j) = Function.eval j ∘ (Prod.snd ∘ R.counts r) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j)
      (measurable_snd.comp (R.measurable_counts r)),
      ← Measure.map_map measurable_snd (R.measurable_counts r), R.law r]
    simp [MarketInterference.FluidLimit.fluidLaw, Measure.pi_map_eval]
  have hD : ∀ᵐ ω ∂P, Tendsto (fun r => R.demand r ω) atTop (𝓝 lam) := by
    have h : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun r => R.demand r ω i) atTop (𝓝 (lam i)) := fun i =>
      E81Fluid.ae_tendsto_poisson P (hlam i) (fun r ω => (R.counts r ω).1 i)
        (fun r => (measurable_pi_apply i).comp (measurable_fst.comp (R.measurable_counts r)))
        (fun r => hlawD i r)
    filter_upwards [ae_all_iff.2 h] with ω hω using tendsto_pi_nhds.2 hω
  have hS : ∀ᵐ ω ∂P, Tendsto (fun r => R.supply r ω) atTop (𝓝 pi) := by
    have h : ∀ j, ∀ᵐ ω ∂P, Tendsto (fun r => R.supply r ω j) atTop (𝓝 (pi j)) := fun j =>
      E81Fluid.ae_tendsto_poisson P (hpi j) (fun r ω => (R.counts r ω).2 j)
        (fun r => (measurable_pi_apply j).comp (measurable_snd.comp (R.measurable_counts r)))
        (fun r => hlawS j r)
    filter_upwards [ae_all_iff.2 h] with ω hω using tendsto_pi_nhds.2 hω
  refine ⟨hint, ?_, ?_⟩
  · have hlim : ∀ᵐ ω ∂P, Tendsto (fun r => R.scaledValue N r ω) atTop
        (𝓝 (Phi N 1 lam pi)) := by
      filter_upwards [hD, hS] with ω h1 h2
      simp only [hscale]
      exact E81Fluid.tendsto_Phi N hlam hpi h1 h2 (fun r i => hdem0 r ω i) (fun r j => hsup0 r ω j)
    have := tendsto_integral_of_dominated_convergence (fun _ => ∑ e, |N.v e| * (1 * N.k e))
      hmeas (integrable_const _) (fun r => Filter.Eventually.of_forall fun ω => hbound r ω) hlim
    simpa using this
  · intro xstar qstar hx hxu hq hqu X Q hX hQ
    filter_upwards [hD, hS, ae_all_iff.2 hX, ae_all_iff.2 hQ] with ω h1 h2 h3 h4
    have hp := E81Fluid.tendsto_primal N hlam hpi h1 h2 (fun r i => hdem0 r ω i)
      (fun r j => hsup0 r ω j) h3 hxu
    have hdl := E81Fluid.tendsto_dual N h1 h2 h4 hq hqu
    refine ⟨fun e => tendsto_pi_nhds.1 hp e, fun i => ?_, fun j => ?_, fun u => ?_, fun e => ?_⟩
    · exact (((continuous_apply i).comp continuous_fst).tendsto _).comp hdl
    · exact (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).tendsto _).comp hdl
    · exact (((continuous_apply u).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))).tendsto _).comp hdl
    · exact (((continuous_apply e).comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto _).comp hdl
