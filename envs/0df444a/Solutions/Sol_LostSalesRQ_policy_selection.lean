-- Prove2me | solution 1 for LostSalesRQ.policy_selection
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T21:14:52.544571+00:00
-- url     : https://prove2.me/submissions/65dde9f7-86b9-4337-8703-86794b9684de

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_LostSalesRQ_model
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Theorems.Thm_LostSalesRQ_rq_policy_exists
import Theorems.Thm_LostSalesRQ_batching_upper_bound
import Theorems.Thm_LostSalesRQ_exact_base_stock_cost
import Theorems.Thm_LostSalesRQ_sqrt_two_zero_setup
import Theorems.Thm_LostSalesRQ_operating_transform

namespace LostSalesRQ
open Finset

lemma pm_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisMass μ j := by
  unfold poisMass; positivity

lemma pm_succ (μ : ℝ) (j : ℕ) :
    poisMass μ (j + 1) * ((j : ℝ) + 1) = μ * poisMass μ j := by
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pc_succ (μ : ℝ) (j : ℕ) : poisCdf μ (j + 1) = poisCdf μ j + poisMass μ (j + 1) := by
  unfold poisCdf; rw [Finset.sum_range_succ]

lemma pc_zero (μ : ℝ) : poisCdf μ 0 = poisMass μ 0 := by simp [poisCdf]

lemma pm_le_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le) (Finset.self_mem_range_succ j)

lemma pc_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisCdf μ j :=
  lt_of_lt_of_le (pm_pos hμ j) (pm_le_pc hμ j)

lemma sum_i_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i = μ * (poisCdf μ j - poisMass μ j) := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma sum_ii_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i
      = μ ^ 2 * (poisCdf μ j - poisMass μ j) - μ * (j : ℝ) * poisMass μ j := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + μ) * h

lemma lf_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < lossFraction μ j := by
  unfold lossFraction; exact div_pos (pm_pos hμ j) (pc_pos hμ j)

lemma lf_le_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction; rw [div_le_one (pc_pos hμ j)]; exact pm_le_pc hμ j

lemma moh_mul_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    meanOnHand μ j * poisCdf μ j = ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
  have hF := pc_pos hμ j
  have h1 := sum_i_pm μ j
  have h0 : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i
      = (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h0, h1]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma moh_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have hF := pc_pos hμ j
  have h := moh_mul_pc hμ j
  have hs : 0 ≤ ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hij : (i : ℝ) ≤ j := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_nonneg (by linarith) (pm_pos hμ i).le
  by_contra hneg
  push_neg at hneg
  have : meanOnHand μ j * poisCdf μ j < 0 := mul_neg_of_neg_of_pos hneg hF
  linarith

lemma lf_succ {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ (j + 1) = μ * lossFraction μ j / (μ + meanOnHand μ j + 1) := by
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have h := pm_succ μ j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hpe : poisMass μ j = lossFraction μ j * poisCdf μ j := by
    unfold lossFraction; field_simp
  have he := lf_pos hμ j
  rw [hHdef]
  set e := lossFraction μ j with he_def
  set F := poisCdf μ j with hF_def
  have hp' : poisMass μ (j + 1) = μ * e * F / ((j : ℝ) + 1) := by
    rw [eq_div_iff hj.ne', h, hpe]; ring
  show poisMass μ (j + 1) / poisCdf μ (j + 1) = _
  rw [pc_succ, hp']
  have h1 : 0 < F + μ * e * F / ((j : ℝ) + 1) := by positivity
  have h2 : 0 < μ + ((j : ℝ) - μ + μ * e) + 1 := by nlinarith
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

lemma ohv_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    onHandVariance μ j = μ * (1 - lossFraction μ j * (meanOnHand μ j + 1)) := by
  have hF := pc_pos hμ j
  have hFne : poisCdf μ j ≠ 0 := hF.ne'
  set H := meanOnHand μ j with hHdef
  -- reflect the sum
  have hrefl : onHandVariance μ j
      = ∑ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j) := by
    unfold onHandVariance
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : j + 1 - 1 - i = j - i := by omega
    have h2 : j - (j - i) = i := by omega
    rw [h1, h2]
    push_cast [hij]
    ring
  rw [hrefl]
  have hexp : ∀ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j)
      = ((((j : ℝ) - H) ^ 2) * poisMass μ i - (2 * ((j : ℝ) - H) - 1) * ((i : ℝ) * poisMass μ i)
          + (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i) / poisCdf μ j := by
    intro i _; field_simp; ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_i_pm, sum_ii_pm]
  have hFdef : ∑ i ∈ range (j + 1), poisMass μ i = poisCdf μ j := rfl
  rw [hFdef]
  rw [hHdef]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma en_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : erlangNormalizer μ j = 1 / lossFraction μ j := by
  unfold erlangNormalizer lossFraction
  rw [one_div_div]

end LostSalesRQ

noncomputable section

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

section TimeScale

variable {lam : ℝ}

lemma ts_rcont (hlam : 0 < lam) {f : ℝ → ℕ}
    (hf : ∀ t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → f s = f t) (t : ℝ) :
    ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → f (s / lam) = f (t / lam) := by
  obtain ⟨δ, hδ, h⟩ := hf (t / lam)
  refine ⟨δ * lam, mul_pos hδ hlam, fun s hts hs => h (s / lam) ?_ ?_⟩
  · exact div_le_div_of_nonneg_right hts hlam.le
  · rw [div_lt_iff₀ hlam]
    have : t / lam * lam = t := div_mul_cancel₀ t hlam.ne'
    nlinarith

/-- The time-rescaled filtration t ↦ 𝓕 (t / lam). -/
def tsFilt {Ω : Type} {m : MeasurableSpace Ω} (F : Filtration ℝ m) (hlam : 0 < lam) :
    Filtration ℝ m where
  seq := fun t => F (t / lam)
  mono' := fun _ _ hst => F.mono (div_le_div_of_nonneg_right hst hlam.le)
  le' := fun t => F.le (t / lam)

/-- The demand environment run on the clock t ↦ t / lam: a unit-rate environment. -/
def tsSpace (S : DemandSpace lam) (hlam : 0 < lam) : DemandSpace 1 where
  Ω := S.Ω
  mΩ := S.mΩ
  ν := S.ν
  prob := S.prob
  𝓕 := tsFilt S.𝓕 hlam
  N := fun t ω => S.N (t / lam) ω
  N_adapted := fun t => S.N_adapted (t / lam)
  N_nonpos := fun ω t ht => S.N_nonpos ω (t / lam) (div_nonpos_of_nonpos_of_nonneg ht hlam.le)
  N_mono := fun ω _ _ hst => S.N_mono ω (div_le_div_of_nonneg_right hst hlam.le)
  N_rcont := fun ω t => ts_rcont hlam (S.N_rcont ω) t
  N_law := fun s t hs hst k => by
    have h := S.N_law (s / lam) (t / lam) (div_nonneg hs hlam.le)
      (div_le_div_of_nonneg_right hst hlam.le) k
    have e : lam * (t / lam - s / lam) = 1 * (t - s) := by field_simp
    rw [e] at h
    exact h
  N_indep := fun s t hs hst => S.N_indep (s / lam) (t / lam) (div_nonneg hs hlam.le)
      (div_le_div_of_nonneg_right hst hlam.le)

/-- A policy run on the rescaled clock. -/
def tsPolicy {S : DemandSpace lam} (hlam : 0 < lam) (π : Policy S) : Policy (tsSpace S hlam) where
  init := fun t ω => π.init (t / lam) ω
  U := fun t ω => π.U (t / lam) ω
  init_meas := fun t => by
    show Measurable[S.𝓕 (0 / lam)] _
    rw [zero_div]
    exact π.init_meas (t / lam)
  init_nonpos := fun ω t ht => π.init_nonpos ω (t / lam) (div_neg_of_neg_of_pos ht hlam)
  init_mono := fun ω _ _ hst => π.init_mono ω (div_le_div_of_nonneg_right hst hlam.le)
  init_rcont := fun ω t => ts_rcont hlam (π.init_rcont ω) t
  init_bdd := fun ω => by
    obtain ⟨n, hn⟩ := π.init_bdd ω
    exact ⟨n, fun t => hn (t / lam)⟩
  U_adapted := fun t => π.U_adapted (t / lam)
  U_nonpos := fun ω t ht => π.U_nonpos ω (t / lam) (div_neg_of_neg_of_pos ht hlam)
  U_mono := fun ω _ _ hst => π.U_mono ω (div_le_div_of_nonneg_right hst hlam.le)
  U_rcont := fun ω t => ts_rcont hlam (π.U_rcont ω) t

lemma ts_image_Iio (hlam : 0 < lam) (t : ℝ) :
    (fun s => s / lam) '' Set.Iio t = Set.Iio (t / lam) := by
  ext x
  simp only [Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact div_lt_div_of_pos_right hs hlam
  · intro hx
    refine ⟨x * lam, ?_, by field_simp⟩
    rwa [lt_div_iff₀ hlam] at hx

lemma ts_leftLim (hlam : 0 < lam) (f : ℝ → ℕ) (t : ℝ) :
    leftLim (fun s => f (s / lam)) t = leftLim f (t / lam) := by
  unfold leftLim
  rw [← ts_image_Iio hlam t, Set.image_image]

lemma ts_delivered (hlam : 0 < lam) (L : ℝ) (init U : ℝ → ℕ) (t : ℝ) :
    delivered (lam * L) (fun s => init (s / lam)) (fun s => U (s / lam)) t =
      delivered L init U (t / lam) := by
  unfold delivered
  have e : (t - lam * L) / lam = t / lam - L := by field_simp
  show init (t / lam) + U ((t - lam * L) / lam) = _
  rw [e]

/-- Scaling by lam as an embedding. -/
def tsEmb (hlam : 0 < lam) : ℝ ↪ ℝ := ⟨fun τ => lam * τ, mul_right_injective₀ hlam.ne'⟩

lemma ts_served (hlam : 0 < lam) (L : ℝ) (init U N : ℝ → ℕ) (t : ℝ) :
    servedPath (lam * L) (fun s => init (s / lam)) (fun s => U (s / lam)) (fun s => N (s / lam)) t =
      servedPath L init U N (t / lam) := by
  unfold servedPath
  simp only []
  set E : Set ℝ := {τ | τ ∈ Set.Ioc 0 (t / lam) ∧ leftLim N τ < N τ} with hEdef
  have hset : {τ | τ ∈ Set.Ioc 0 t ∧ leftLim (fun s => N (s / lam)) τ < N (τ / lam)} =
      (tsEmb hlam) '' E := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_Ioc, ts_leftLim hlam, hEdef, tsEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h0, ht⟩, hj⟩
      refine ⟨τ / lam, ⟨⟨div_pos h0 hlam, div_le_div_of_nonneg_right ht hlam.le⟩, hj⟩, ?_⟩
      field_simp
    · rintro ⟨u, ⟨⟨h0, ht⟩, hj⟩, rfl⟩
      have e : lam * u / lam = u := by field_simp
      rw [e]
      refine ⟨⟨mul_pos hlam h0, ?_⟩, hj⟩
      rwa [le_div_iff₀ hlam, mul_comm] at ht
  by_cases hE : E.Finite
  · have hE' : ({τ | τ ∈ Set.Ioc 0 t ∧ leftLim (fun s => N (s / lam)) τ < N (τ / lam)} : Set ℝ).Finite := by
      rw [hset]; exact hE.image _
    rw [dif_pos hE', dif_pos hE]
    have hfs : hE'.toFinset = hE.toFinset.map (tsEmb hlam) := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.mem_map]
      rw [hset]
      simp only [Set.mem_image, Set.Finite.mem_toFinset]
    have hmono : StrictMonoOn (tsEmb hlam) (hE.toFinset : Set ℝ) := by
      intro x _ y _ hxy
      simp only [tsEmb, Function.Embedding.coeFn_mk]
      exact mul_lt_mul_of_pos_left hxy hlam
    rw [hfs, ← hmono.map_finsetSort, List.foldl_map]
    congr 1
    funext acc τ
    simp only [tsEmb, Function.Embedding.coeFn_mk, ts_leftLim hlam]
    have e1 : lam * τ / lam = τ := by field_simp
    have e2 : (lam * τ - lam * L) / lam = τ - L := by field_simp
    rw [e1, e2]
  · have hE' : ¬ ({τ | τ ∈ Set.Ioc 0 t ∧ leftLim (fun s => N (s / lam)) τ < N (τ / lam)} : Set ℝ).Finite := by
      rw [hset, Set.finite_image_iff (tsEmb hlam).injective.injOn]
      exact hE
    rw [dif_neg hE', dif_neg hE]

lemma ts_orderCount (hlam : 0 < lam) (U : ℝ → ℕ) (T : ℝ) :
    orderCount (fun s => U (s / lam)) T = orderCount U (T / lam) := by
  unfold orderCount
  have hset : {t | t ∈ Set.Icc 0 T ∧ leftLim (fun s => U (s / lam)) t < U (t / lam)} =
      (tsEmb hlam) '' {t | t ∈ Set.Icc 0 (T / lam) ∧ leftLim U t < U t} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc, ts_leftLim hlam, tsEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h0, ht⟩, hj⟩
      refine ⟨τ / lam, ⟨⟨div_nonneg h0 hlam.le, div_le_div_of_nonneg_right ht hlam.le⟩, hj⟩, ?_⟩
      field_simp
    · rintro ⟨u, ⟨⟨h0, ht⟩, hj⟩, rfl⟩
      have e : lam * u / lam = u := by field_simp
      rw [e]
      refine ⟨⟨mul_nonneg hlam.le h0, ?_⟩, hj⟩
      rwa [le_div_iff₀ hlam, mul_comm] at ht
  rw [hset, Set.ncard_image_of_injective _ (tsEmb hlam).injective]

end TimeScale

section TimeScale2

variable {lam : ℝ} {S : DemandSpace lam}

lemma ts_pol_served (hlam : 0 < lam) (π : Policy S) (L t : ℝ) (ω : (tsSpace S hlam).Ω) :
    (tsPolicy hlam π).served (lam * L) t ω = π.served L (t / lam) ω :=
  ts_served hlam L (fun s => π.init s ω) (fun s => π.U s ω) (fun s => S.N s ω) t

lemma ts_pol_onHand (hlam : 0 < lam) (π : Policy S) (L t : ℝ) (ω : (tsSpace S hlam).Ω) :
    (tsPolicy hlam π).onHand (lam * L) t ω = π.onHand L (t / lam) ω := by
  unfold Policy.onHand
  rw [ts_pol_served]
  congr 1
  exact ts_delivered hlam L (fun s => π.init s ω) (fun s => π.U s ω) t

lemma ts_pol_lost (hlam : 0 < lam) (π : Policy S) (L t : ℝ) (ω : (tsSpace S hlam).Ω) :
    (tsPolicy hlam π).lost (lam * L) t ω = π.lost L (t / lam) ω := by
  unfold Policy.lost
  rw [ts_pol_served]
  rfl

lemma ts_pol_orders (hlam : 0 < lam) (π : Policy S) (T : ℝ) (ω : (tsSpace S hlam).Ω) :
    (tsPolicy hlam π).orders T ω = π.orders (T / lam) ω :=
  ts_orderCount hlam (fun s => π.U s ω) T

lemma ts_lint (hlam : 0 < lam) (g : ℝ → ℝ≥0∞) (T : ℝ) :
    ∫⁻ t in Set.Icc 0 T, g (t / lam) = ENNReal.ofReal lam * ∫⁻ u in Set.Icc 0 (T / lam), g u := by
  have hind : ∀ t, (Set.Icc 0 T).indicator (fun t => g (t / lam)) t =
      (Set.Icc 0 (T / lam)).indicator g (t / lam) := by
    intro t
    by_cases ht : t ∈ Set.Icc 0 T
    · have ht' : t / lam ∈ Set.Icc 0 (T / lam) :=
        ⟨div_nonneg ht.1 hlam.le, div_le_div_of_nonneg_right ht.2 hlam.le⟩
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    · have ht' : t / lam ∉ Set.Icc 0 (T / lam) := by
        intro h
        apply ht
        refine ⟨?_, ?_⟩
        · have h1 := h.1
          rwa [le_div_iff₀ hlam, zero_mul] at h1
        · have h2 := h.2
          rwa [div_le_div_iff_of_pos_right hlam] at h2
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  simp_rw [hind]
  set G := (Set.Icc 0 (T / lam)).indicator g
  have hne : lam⁻¹ ≠ 0 := inv_ne_zero hlam.ne'
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ lam⁻¹ hne).toMeasurableEquiv
  have hmap : Measure.map (⇑e) volume = ENNReal.ofReal |lam⁻¹⁻¹| • volume :=
    Real.map_volume_mul_left hne
  have h1 := lintegral_map_equiv G e (μ := volume)
  rw [hmap, lintegral_smul_measure, smul_eq_mul, inv_inv, abs_of_pos hlam] at h1
  rw [h1]
  apply lintegral_congr
  intro t
  show G (t / lam) = G (lam⁻¹ * t)
  rw [div_eq_inv_mul]

lemma ts_hc (hlam : 0 < lam) (π : Policy S) (L h p K : ℝ) (hh : 0 < h) (T : ℝ)
    (ω : (tsSpace S hlam).Ω) :
    (tsPolicy hlam π).horizonCost (lam * L) 1 (p * lam / h) (K * lam / h) T ω =
      ENNReal.ofReal (lam / h) * π.horizonCost L h p K (T / lam) ω := by
  unfold Policy.horizonCost
  have hon : (fun t => (((tsPolicy hlam π).onHand (lam * L) t ω : ℕ) : ℝ≥0∞)) =
      (fun t => ((π.onHand L (t / lam) ω : ℕ) : ℝ≥0∞)) := by
    funext t; rw [ts_pol_onHand]
  have hl := ts_lint hlam (fun u => ((π.onHand L u ω : ℕ) : ℝ≥0∞)) T
  rw [hon, hl, ts_pol_lost, ts_pol_orders]
  have hlh : 0 ≤ lam / h := div_nonneg hlam.le hh.le
  have e1 : ENNReal.ofReal lam = ENNReal.ofReal (lam / h) * ENNReal.ofReal h := by
    rw [← ENNReal.ofReal_mul hlh]; congr 1; field_simp
  have e2 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x * lam / h) = ENNReal.ofReal (lam / h) * ENNReal.ofReal x := by
    intro x hx
    rw [← ENNReal.ofReal_mul hlh]; congr 1; ring
  rcases le_or_gt 0 p with hp | hp
  · rcases le_or_gt 0 K with hK | hK
    · rw [ENNReal.ofReal_one, one_mul, e1, e2 p hp, e2 K hK]
      ring
    · have hK' : K * lam / h ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hh.le; nlinarith
      rw [ENNReal.ofReal_one, one_mul, e1, e2 p hp, ENNReal.ofReal_of_nonpos hK',
        ENNReal.ofReal_of_nonpos hK.le]
      ring
  · have hp' : p * lam / h ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hh.le; nlinarith
    rcases le_or_gt 0 K with hK | hK
    · rw [ENNReal.ofReal_one, one_mul, e1, e2 K hK, ENNReal.ofReal_of_nonpos hp',
        ENNReal.ofReal_of_nonpos hp.le]
      ring
    · have hK' : K * lam / h ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg _ hh.le; nlinarith
      rw [ENNReal.ofReal_one, one_mul, e1, ENNReal.ofReal_of_nonpos hp',
        ENNReal.ofReal_of_nonpos hp.le, ENNReal.ofReal_of_nonpos hK', ENNReal.ofReal_of_nonpos hK.le]
      ring

/-- Cost scaling: the average cost on the original clock is h times the normalized cost. -/
lemma ts_avg (hlam : 0 < lam) (π : Policy S) (L h p K : ℝ) (hh : 0 < h) :
    π.avgCost L h p K =
      ENNReal.ofReal h * (tsPolicy hlam π).avgCost (lam * L) 1 (p * lam / h) (K * lam / h) := by
  unfold Policy.avgCost
  set g : ℝ → ℝ≥0∞ := fun T => (∫⁻ ω, π.horizonCost L h p K T ω ∂S.ν) / ENNReal.ofReal T
    with hg
  have key : ∀ T : ℝ, 0 < T →
      (∫⁻ ω, (tsPolicy hlam π).horizonCost (lam * L) 1 (p * lam / h) (K * lam / h) T ω
        ∂(tsSpace S hlam).ν) / ENNReal.ofReal T = ENNReal.ofReal (1 / h) * g (T / lam) := by
    intro T hT
    have h1 : ∫⁻ ω, (tsPolicy hlam π).horizonCost (lam * L) 1 (p * lam / h) (K * lam / h) T ω
        ∂(tsSpace S hlam).ν =
        ENNReal.ofReal (lam / h) * ∫⁻ ω, π.horizonCost L h p K (T / lam) ω ∂S.ν := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr (fun ω => ts_hc hlam π L h p K hh T ω)
    rw [h1, hg]
    simp only []
    have hT' : ENNReal.ofReal T = ENNReal.ofReal lam * ENNReal.ofReal (T / lam) := by
      rw [← ENNReal.ofReal_mul hlam.le]; congr 1; field_simp
    have hl : ENNReal.ofReal (lam / h) = ENNReal.ofReal lam * ENNReal.ofReal (1 / h) := by
      rw [← ENNReal.ofReal_mul hlam.le]; congr 1; ring
    rw [hT', hl, mul_assoc, ENNReal.mul_div_mul_left _ _ (by simp [hlam]) ENNReal.ofReal_ne_top,
      mul_div_assoc]
  have hlim : limsup (fun T => (∫⁻ ω, (tsPolicy hlam π).horizonCost (lam * L) 1 (p * lam / h)
        (K * lam / h) T ω ∂(tsSpace S hlam).ν) / ENNReal.ofReal T) atTop =
      limsup (fun T => ENNReal.ofReal (1 / h) * g (T / lam)) atTop :=
    limsup_congr ((eventually_gt_atTop 0).mono key)
  rw [hlim, ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  have hcomp : limsup (fun T => g (T / lam)) atTop = limsup g atTop := by
    have hm : Filter.map (fun T : ℝ => T / lam) atTop = atTop :=
      (OrderIso.divRight₀ lam hlam).map_atTop
    unfold limsup
    conv_rhs => rw [← hm]
    rw [Filter.map_map]
    rfl
  rw [hcomp, ← mul_assoc, ← ENNReal.ofReal_mul hh.le, mul_one_div_cancel hh.ne',
    ENNReal.ofReal_one, one_mul]

lemma ts_opt_ge (hlam : 0 < lam) (L h p K : ℝ) (hh : 0 < h) :
    ENNReal.ofReal h * OPTk (lam * L) (p * lam / h) (K * lam / h) ≤ OPT lam L h p K := by
  unfold OPT
  refine le_iInf₂ (fun S π => ?_)
  rw [ts_avg hlam π L h p K hh]
  gcongr
  unfold OPTk OPT
  exact iInf₂_le (tsSpace S hlam) (tsPolicy hlam π)

lemma ts_rq (hlam : 0 < lam) {π : Policy S} {L : ℝ} {r Q : ℕ} (h : IsRQPolicy L r Q π) :
    IsRQPolicy (lam * L) r Q (tsPolicy hlam π) := by
  refine ⟨fun ω t => ?_, fun ω t => ?_⟩
  · show π.init (t / lam) ω = _
    rw [h.1 ω (t / lam)]
    by_cases ht : 0 ≤ t
    · rw [if_pos (div_nonneg ht hlam.le), if_pos ht]
    · have ht' : ¬ 0 ≤ t / lam := by
        intro h'
        apply ht
        rwa [le_div_iff₀ hlam, zero_mul] at h'
      rw [if_neg ht', if_neg ht]
  · show π.U (t / lam) ω = Q * ((tsPolicy hlam π).served (lam * L) t ω / Q)
    rw [ts_pol_served, h.2 ω (t / lam)]

lemma ts_noOrder (hlam : 0 < lam) :
    tsPolicy hlam (noOrderPolicy S) = noOrderPolicy (tsSpace S hlam) := rfl

end TimeScale2

end LostSalesRQ

end

noncomputable section

namespace LostSalesRQ

open MeasureTheory Filter
open scoped ENNReal

lemma ps_L0 (μ a : ℝ) : baseStockCost μ a 0 = a := by
  unfold baseStockCost meanOnHand lossFraction poisCdf
  simp only [zero_add, Finset.range_one, Finset.sum_singleton]
  have hp : poisMass μ 0 ≠ 0 := by
    unfold poisMass; simp [Real.exp_ne_zero]
  rw [div_self hp]
  simp

lemma ps_noorder_k (S : DemandSpace 1) (μ a k : ℝ) :
    (noOrderPolicy S).avgCost μ 1 a k = (noOrderPolicy S).avgCost μ 1 a 0 := by
  have h : ∀ T ω, (noOrderPolicy S).horizonCost μ 1 a k T ω =
      (noOrderPolicy S).horizonCost μ 1 a 0 T ω := by
    intro T ω
    simp [Policy.horizonCost, Policy.orders, orderCount, noOrderPolicy]
  unfold Policy.avgCost
  simp_rw [h]

lemma ps_opt0_mono (μ : ℝ) {a a' : ℝ} (h : a ≤ a') : OPTk μ a 0 ≤ OPTk μ a' 0 := by
  unfold OPTk OPT
  apply iInf_mono
  intro S
  apply iInf_mono
  intro π
  unfold Policy.avgCost
  have hle : ∀ T : ℝ, (∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν) / ENNReal.ofReal T ≤
      (∫⁻ ω, π.horizonCost μ 1 a' 0 T ω ∂S.ν) / ENNReal.ofReal T := by
    intro T
    apply ENNReal.div_le_div_right
    apply lintegral_mono
    intro ω
    unfold Policy.horizonCost
    gcongr
  exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)

lemma ps_lot0 : lotSize 0 = 1 := by unfold lotSize; simp

lemma ps_b0 : batchSurcharge 0 = 0 := by unfold batchSurcharge; rw [ps_lot0]; simp

lemma ps_lot_pos (k : ℝ) : 1 ≤ lotSize k := by unfold lotSize; exact le_max_left _ _

lemma ps_b_nonneg {k : ℝ} (hk : 0 ≤ k) : 0 ≤ batchSurcharge k := by
  unfold batchSurcharge
  have h1 : (1 : ℝ) ≤ (lotSize k : ℝ) := by exact_mod_cast ps_lot_pos k
  have h2 : 0 ≤ ((lotSize k : ℝ) - 1) / 2 := by linarith
  have h3 : 0 ≤ k / (lotSize k : ℝ) := div_nonneg hk (by linarith)
  linarith

/-- The matching argument of Corollary 1 in normalized units. -/
lemma ps_key (μ a k c : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : 0 < c)
    (hprem : ENNReal.ofReal (minBaseStockCost μ a) ≤ ENNReal.ofReal c * OPTk μ a 0) :
    ENNReal.ofReal (min a (minBaseStockCost μ a + Real.sqrt (2 * k))) ≤
      ENNReal.ofReal ((c + Real.sqrt (c ^ 2 + 4)) / 2) * OPTk μ a k := by
  set R := (c + Real.sqrt (c ^ 2 + 4)) / 2 with hRdef
  have hsq : Real.sqrt (c ^ 2 + 4) ^ 2 = c ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hsq0 : 0 ≤ Real.sqrt (c ^ 2 + 4) := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = c * R + 1 := by rw [hRdef]; nlinarith
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hR1 : 1 < R := by nlinarith
  clear_value R
  set s := Real.sqrt (2 * k) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * k := Real.sq_sqrt (by linarith)
  by_cases hA : a ≤ R * s
  · have hlow := (operating_transform μ a k hμ ha hk).2
    have hamin : a ≤ R * min a s := by
      rcases le_total a s with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; exact hA
    calc ENNReal.ofReal (min a (minBaseStockCost μ a + s)) ≤ ENNReal.ofReal a :=
          ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ ≤ ENNReal.ofReal (R * min a s) := ENNReal.ofReal_le_ofReal hamin
      _ = ENNReal.ofReal R * ENNReal.ofReal (min a s) := ENNReal.ofReal_mul hR0.le
      _ ≤ ENNReal.ofReal R * OPTk μ a k := by gcongr
  · push Not at hA
    set θ := 1 / R ^ 2 with hθdef
    set b := s / R with hbdef
    have hR2pos : 0 < R ^ 2 := by positivity
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hR2pos]; nlinarith
    have hb : Real.sqrt (2 * k * θ) = b := by
      have e : 2 * k * θ = b ^ 2 := by
        rw [hθdef, hbdef, div_pow, hs2]; field_simp
      rw [e]
      exact Real.sqrt_sq (div_nonneg hs0 hR0.le)
    have hbR : b ≤ R * s := by
      rw [hbdef, div_le_iff₀ hR0]
      have e : R * s * R = R ^ 2 * s := by ring
      rw [e]
      nlinarith [mul_nonneg hs0 (by nlinarith : (0 : ℝ) ≤ R ^ 2 - 1)]
    have hba : Real.sqrt (2 * k * θ) ≤ a := by rw [hb]; linarith
    have hOT := (operating_transform μ a k hμ ha hk).1 θ hθ0 hθ1 hba
    rw [hb] at hOT
    have h1θ : 1 - θ = c / R := by
      rw [hθdef]; field_simp; nlinarith
    have h1θpos : 0 < 1 - θ := by linarith
    have ha' : a ≤ (a - b) / (1 - θ) := by
      rw [le_div_iff₀ h1θpos]
      have : b ≤ a * θ := by
        rw [hbdef, hθdef, div_le_iff₀ hR0]
        have e : a * (1 / R ^ 2) * R = a / R := by field_simp
        rw [e, le_div_iff₀ hR0]
        nlinarith
      nlinarith
    have hmono := ps_opt0_mono μ ha'
    have e1 : ENNReal.ofReal R * ENNReal.ofReal b = ENNReal.ofReal s := by
      rw [← ENNReal.ofReal_mul hR0.le]
      congr 1
      rw [hbdef]; field_simp
    have e2 : ENNReal.ofReal R * ENNReal.ofReal (1 - θ) = ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_mul hR0.le, h1θ]
      congr 1
      field_simp
    calc ENNReal.ofReal (min a (minBaseStockCost μ a + s))
        ≤ ENNReal.ofReal (minBaseStockCost μ a + s) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ ≤ ENNReal.ofReal (minBaseStockCost μ a) + ENNReal.ofReal s := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal c * OPTk μ a 0 + ENNReal.ofReal s := by gcongr
      _ ≤ ENNReal.ofReal c * OPTk μ ((a - b) / (1 - θ)) 0 + ENNReal.ofReal s := by gcongr
      _ = ENNReal.ofReal R *
            (ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * OPTk μ ((a - b) / (1 - θ)) 0) := by
          rw [mul_add, ← mul_assoc, e1, e2, add_comm]
      _ ≤ ENNReal.ofReal R * OPTk μ a k := by gcongr

/-- Cost of the selected policy in normalized units. -/
lemma ps_norm (S : DemandSpace 1) (μ a k : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (Sstar : ℕ) (hS : baseStockCost μ a Sstar = minBaseStockCost μ a) (π : Policy S)
    (hπ : IsSelectedPolicy μ μ a k Sstar π) :
    π.avgCost μ 1 a k ≤ ENNReal.ofReal (min a (minBaseStockCost μ a + batchSurcharge k)) := by
  unfold IsSelectedPolicy at hπ
  split_ifs at hπ with hcond
  · have hb := (batching_upper_bound μ a k hμ ha hk S Sstar hcond.1 π hπ).1
    rw [hS] at hb
    rw [min_eq_right hcond.2.le]
    exact hb
  · subst hπ
    rw [ps_noorder_k, (exact_base_stock_cost μ a hμ ha S).1]
    apply ENNReal.ofReal_le_ofReal
    apply le_min le_rfl
    have hb0 := ps_b_nonneg hk
    by_cases h0 : 1 ≤ Sstar
    · have : ¬ (minBaseStockCost μ a + batchSurcharge k < a) := fun h => hcond ⟨h0, h⟩
      linarith
    · have : Sstar = 0 := by omega
      rw [this, ps_L0] at hS
      linarith

lemma ps_sel_ts {lam : ℝ} {S : DemandSpace lam} (hlam : 0 < lam) {L μ a k : ℝ} {Sstar : ℕ}
    {π : Policy S} (hπ : IsSelectedPolicy L μ a k Sstar π) :
    IsSelectedPolicy (lam * L) μ a k Sstar (tsPolicy hlam π) := by
  unfold IsSelectedPolicy at hπ ⊢
  split_ifs at hπ ⊢ with hcond
  · exact ts_rq hlam hπ
  · subst hπ; exact ts_noOrder hlam

end LostSalesRQ

end

open LostSalesRQ in
theorem solution (lam L h p K : ℝ) (hlam : 0 < lam) (hL : 0 ≤ L) (hh : 0 < h)
    (hp : 0 ≤ p) (hK : 0 ≤ K) (S : DemandSpace lam) (Sstar : ℕ)
    (hS : ∀ j : ℕ, baseStockCost (lam * L) (p * lam / h) Sstar ≤
      baseStockCost (lam * L) (p * lam / h) j) :
    (∃ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) (K * lam / h) Sstar π) ∧
    ∀ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) (K * lam / h) Sstar π →
      π.avgCost L h p K ≤
          ENNReal.ofReal (if K = 0 then Real.sqrt 2 else (Real.sqrt 2 + Real.sqrt 6) / 2) *
            OPT lam L h p K ∧
        (K = 0 → π ∈ baseStockFamily S L ∧
          ∀ π' ∈ baseStockFamily S L, π.avgCost L h p 0 ≤ π'.avgCost L h p 0) := by
  set μ := lam * L with hμdef
  set a := p * lam / h with hadef
  have hμ : 0 ≤ μ := mul_nonneg hlam.le hL
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hp hlam.le) hh.le
  have hk : 0 ≤ K * lam / h := div_nonneg (mul_nonneg hK hlam.le) hh.le
  have hbdd : BddBelow (Set.range fun j => baseStockCost μ a j) :=
    ⟨baseStockCost μ a Sstar, by rintro _ ⟨j, rfl⟩; exact hS j⟩
  have hU : baseStockCost μ a Sstar = minBaseStockCost μ a :=
    le_antisymm (le_ciInf hS) (ciInf_le hbdd Sstar)
  have hUle : ∀ j, minBaseStockCost μ a ≤ baseStockCost μ a j := fun j => ciInf_le hbdd j
  refine ⟨?_, fun π hπ => ?_⟩
  · unfold IsSelectedPolicy
    split_ifs with hcond
    · exact rq_policy_exists lam L hlam.le hL S (Sstar - 1) (lotSize (K * lam / h)) (ps_lot_pos _)
    · exact ⟨noOrderPolicy S, rfl⟩
  set S' := tsSpace S hlam
  set π' := tsPolicy hlam π
  have hπ' : IsSelectedPolicy μ μ a (K * lam / h) Sstar π' := ps_sel_ts hlam hπ
  have hnorm := ps_norm S' μ a (K * lam / h) hμ ha hk Sstar hU π' hπ'
  have havg := ts_avg hlam π L h p K hh
  have hprem := (sqrt_two_zero_setup μ a hμ ha).2
  have hopt := ts_opt_ge hlam L h p K hh
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, fun hK0 => ?_⟩
  · by_cases hK0 : K = 0
    · subst hK0
      have hk0 : (0 : ℝ) * lam / h = 0 := by simp
      rw [if_pos rfl]
      rw [hk0] at hnorm havg hopt
      have hUa : minBaseStockCost μ a ≤ a := by
        have := hUle 0
        rwa [ps_L0] at this
      rw [ps_b0, add_zero, min_eq_right hUa] at hnorm
      calc π.avgCost L h p 0 = ENNReal.ofReal h * π'.avgCost μ 1 a 0 := havg
        _ ≤ ENNReal.ofReal h * ENNReal.ofReal (minBaseStockCost μ a) := by gcongr
        _ ≤ ENNReal.ofReal h * (ENNReal.ofReal (Real.sqrt 2) * OPTk μ a 0) := by gcongr
        _ = ENNReal.ofReal (Real.sqrt 2) * (ENNReal.ofReal h * OPTk μ a 0) := by ring
        _ ≤ ENNReal.ofReal (Real.sqrt 2) * OPT lam L h p 0 := by gcongr
    · rw [if_neg hK0]
      obtain ⟨π1, hπ1⟩ := rq_policy_exists 1 μ zero_le_one hμ S' 0 (lotSize (K * lam / h))
        (ps_lot_pos _)
      have hbk := (batching_upper_bound μ a (K * lam / h) hμ ha hk S' 1 le_rfl π1 hπ1).2
      have hkey := ps_key μ a (K * lam / h) (Real.sqrt 2) hμ ha hk (by positivity) hprem
      have hR : (Real.sqrt 2 + Real.sqrt (Real.sqrt 2 ^ 2 + 4)) / 2 =
          (Real.sqrt 2 + Real.sqrt 6) / 2 := by
        rw [hs2]; norm_num
      rw [hR] at hkey
      have hmin : min a (minBaseStockCost μ a + batchSurcharge (K * lam / h)) ≤
          min a (minBaseStockCost μ a + Real.sqrt (2 * (K * lam / h))) :=
        min_le_min le_rfl (by linarith)
      calc π.avgCost L h p K = ENNReal.ofReal h * π'.avgCost μ 1 a (K * lam / h) := havg
        _ ≤ ENNReal.ofReal h * ENNReal.ofReal
              (min a (minBaseStockCost μ a + batchSurcharge (K * lam / h))) := by gcongr
        _ ≤ ENNReal.ofReal h * ENNReal.ofReal
              (min a (minBaseStockCost μ a + Real.sqrt (2 * (K * lam / h)))) := by
            gcongr
        _ ≤ ENNReal.ofReal h * (ENNReal.ofReal ((Real.sqrt 2 + Real.sqrt 6) / 2) *
              OPTk μ a (K * lam / h)) := by gcongr
        _ = ENNReal.ofReal ((Real.sqrt 2 + Real.sqrt 6) / 2) *
              (ENNReal.ofReal h * OPTk μ a (K * lam / h)) := by ring
        _ ≤ ENNReal.ofReal ((Real.sqrt 2 + Real.sqrt 6) / 2) * OPT lam L h p K := by gcongr
  · subst hK0
    have hk0 : (0 : ℝ) * lam / h = 0 := by simp
    rw [hk0] at hπ'
    -- the normalized cost of the selected policy equals U
    have hcostU : π'.avgCost μ 1 a 0 = ENNReal.ofReal (minBaseStockCost μ a) := by
      unfold IsSelectedPolicy at hπ'
      split_ifs at hπ' with hcond
      · rw [ps_lot0] at hπ'
        rw [(exact_base_stock_cost μ a hμ ha S').2 Sstar hcond.1 π' hπ', hU]
      · rw [hπ', (exact_base_stock_cost μ a hμ ha S').1]
        congr 1
        rw [ps_b0, add_zero] at hcond
        by_cases h0 : 1 ≤ Sstar
        · have h1 : ¬ (minBaseStockCost μ a < a) := fun h => hcond ⟨h0, h⟩
          have h2 := hUle 0
          rw [ps_L0] at h2
          linarith
        · have : Sstar = 0 := by omega
          rw [this, ps_L0] at hU
          exact hU
    refine ⟨?_, fun π2 hπ2 => ?_⟩
    · unfold IsSelectedPolicy at hπ
      rw [hk0] at hπ
      split_ifs at hπ with hcond
      · rw [ps_lot0] at hπ
        exact Set.mem_union_left _ ⟨Sstar, hcond.1, hπ⟩
      · rw [hπ]; exact Set.mem_union_right _ (Set.mem_singleton _)
    · have havg0 := ts_avg hlam π L h p 0 hh
      have havg2 := ts_avg hlam π2 L h p 0 hh
      rw [hk0] at havg0 havg2
      rw [havg0, havg2, hcostU]
      gcongr
      rcases hπ2 with ⟨j, hj, hrq⟩ | hno
      · rw [(exact_base_stock_cost μ a hμ ha S').2 j hj _ (ts_rq hlam hrq)]
        exact ENNReal.ofReal_le_ofReal (hUle j)
      · rw [Set.mem_singleton_iff] at hno
        subst hno
        rw [ts_noOrder hlam, (exact_base_stock_cost μ a hμ ha S').1]
        have := hUle 0
        rw [ps_L0] at this
        exact ENNReal.ofReal_le_ofReal this
