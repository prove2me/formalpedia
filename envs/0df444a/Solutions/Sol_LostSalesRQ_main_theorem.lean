-- Prove2me | solution 1 for LostSalesRQ.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T21:22:47.121739+00:00
-- url     : https://prove2.me/submissions/fad87b64-5923-4776-bc8b-b2ccaa122710

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
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_LostSalesRQ_policy_selection
import Theorems.Thm_LostSalesRQ_sqrt_two_zero_setup
import Theorems.Thm_LostSalesRQ_tightness_bounds
import Theorems.Thm_LostSalesRQ_lower_curve_properties
import Theorems.Thm_LostSalesRQ_batching_upper_bound
import Theorems.Thm_LostSalesRQ_rq_policy_exists

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

open MeasureTheory Filter Finset
open scoped ENNReal Topology

lemma mt_pm_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ poisMass μ j := by
  unfold poisMass; positivity

lemma mt_pc_ge {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : poisMass μ 0 ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => mt_pm_nonneg hμ i) (Finset.mem_range.mpr (Nat.succ_pos j))

lemma mt_pc_pos {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 < poisCdf μ j := by
  have h0 : 0 < poisMass μ 0 := by unfold poisMass; simp [Real.exp_pos]
  exact lt_of_lt_of_le h0 (mt_pc_ge hμ j)

lemma mt_lf_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ lossFraction μ j :=
  div_nonneg (mt_pm_nonneg hμ j) (mt_pc_pos hμ j).le

lemma mt_lf_le_one {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction
  rw [div_le_one (mt_pc_pos hμ j)]
  unfold poisCdf
  rw [Finset.sum_range_succ]
  have : 0 ≤ ∑ i ∈ range j, poisMass μ i := Finset.sum_nonneg (fun i _ => mt_pm_nonneg hμ i)
  linarith

lemma mt_moh_ge {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 1 - lossFraction μ j ≤ meanOnHand μ j := by
  have hF := mt_pc_pos hμ j
  have hid : meanOnHand μ j * poisCdf μ j =
      ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    have hs := sum_i_pm μ j
    have e : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i =
        (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
      unfold poisCdf
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e, hs]
    unfold meanOnHand lossFraction
    field_simp
    ring
  have hge : poisCdf μ j - poisMass μ j ≤
      ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [sub_self, zero_mul, add_zero, add_sub_cancel_right]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    have h1 : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
      have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hi'
      linarith
    have := mt_pm_nonneg hμ i
    nlinarith
  have : (1 - lossFraction μ j) * poisCdf μ j = poisCdf μ j - poisMass μ j := by
    unfold lossFraction; field_simp
  have key : (1 - lossFraction μ j) * poisCdf μ j ≤ meanOnHand μ j * poisCdf μ j := by
    rw [this, hid]; exact hge
  exact le_of_mul_le_mul_right key hF

lemma mt_moh_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have h1 := mt_moh_ge hμ j
  have h2 := mt_lf_le_one hμ j
  linarith

lemma mt_L0 (μ a : ℝ) : baseStockCost μ a 0 = a := by
  unfold baseStockCost meanOnHand lossFraction poisCdf
  simp only [zero_add, Finset.range_one, Finset.sum_singleton]
  have hp : poisMass μ 0 ≠ 0 := by
    unfold poisMass; simp [Real.exp_ne_zero]
  rw [div_self hp]
  simp

lemma mt_lot_pos (k : ℝ) : 1 ≤ lotSize k := by unfold lotSize; exact le_max_left _ _

lemma mt_lot0 : lotSize 0 = 1 := by unfold lotSize; simp

/-- A minimizing integer base-stock level exists. -/
lemma mt_exists_min {μ a : ℝ} (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    ∃ S : ℕ, ∀ j : ℕ, baseStockCost μ a S ≤ baseStockCost μ a j := by
  set N := ⌈μ + a⌉₊ with hNdef
  obtain ⟨S, -, hS⟩ := (Finset.range (N + 1)).exists_min_image (fun j => baseStockCost μ a j)
    ⟨0, by simp⟩
  refine ⟨S, fun j => ?_⟩
  by_cases hj : j ∈ Finset.range (N + 1)
  · exact hS j hj
  · have hjN : N + 1 ≤ j := by
      rw [Finset.mem_range] at hj; omega
    have h0 := hS 0 (by simp)
    rw [mt_L0] at h0
    have hLj : (j : ℝ) - μ ≤ baseStockCost μ a j := by
      unfold baseStockCost meanOnHand
      have := mt_lf_nonneg hμ j
      nlinarith [mul_nonneg hμ this, mul_nonneg ha this]
    have hN : μ + a ≤ (N : ℝ) := Nat.le_ceil _
    have : ((N + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hjN
    push_cast at this
    linarith

/-- The Erlang loss fraction becomes arbitrarily small. -/
lemma mt_lf_small {μ : ℝ} (hμ : 0 ≤ μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ j : ℕ, 1 ≤ j ∧ lossFraction μ j ≤ δ := by
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop μ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  have h1 := hN (max 1 N) (le_max_right _ _)
  have hp0 : 0 < poisMass μ 0 := by unfold poisMass; simp [Real.exp_pos]
  unfold lossFraction
  calc poisMass μ (max 1 N) / poisCdf μ (max 1 N)
      ≤ poisMass μ (max 1 N) / poisMass μ 0 :=
        div_le_div_of_nonneg_left (mt_pm_nonneg hμ _) hp0 (mt_pc_ge hμ _)
    _ = μ ^ (max 1 N) / ((max 1 N).factorial : ℝ) := by
        unfold poisMass
        have := Real.exp_pos (-μ)
        field_simp
        simp
    _ ≤ δ := h1.le

lemma mt_avg_mono_h {lam : ℝ} {S : DemandSpace lam} (π : Policy S) {L h h' p K : ℝ}
    (hh : h ≤ h') : π.avgCost L h p K ≤ π.avgCost L h' p K := by
  unfold Policy.avgCost
  have hle : ∀ T : ℝ, (∫⁻ ω, π.horizonCost L h p K T ω ∂S.ν) / ENNReal.ofReal T ≤
      (∫⁻ ω, π.horizonCost L h' p K T ω ∂S.ν) / ENNReal.ofReal T := by
    intro T
    apply ENNReal.div_le_div_right
    apply lintegral_mono
    intro ω
    unfold Policy.horizonCost
    gcongr
  exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)

/-- With no demand the no-order policy costs nothing. -/
lemma mt_noorder_zero (S : DemandSpace 0) (L h p K : ℝ) :
    (noOrderPolicy S).avgCost L h p K = 0 := by
  have hN : ∀ T, ∀ᵐ ω ∂S.ν, S.N T ω = 0 := by
    intro T
    by_cases hT : T ≤ 0
    · exact Filter.Eventually.of_forall (fun ω => S.N_nonpos ω T hT)
    · push Not at hT
      have hlaw := S.N_law 0 T le_rfl hT.le 0
      have hm : Measurable (S.N T) := (S.N_adapted T).mono (S.𝓕.le T) le_rfl
      have hset : {ω | S.N T ω - S.N 0 ω = 0} = S.N T ⁻¹' {0} := by
        ext ω
        simp [S.N_nonpos ω 0 le_rfl]
      rw [hset] at hlaw
      have hp : poisMass (0 * (T - 0)) 0 = 1 := by unfold poisMass; simp
      rw [hp, ENNReal.ofReal_one] at hlaw
      have hms : MeasurableSet (S.N T ⁻¹' {0}) := hm (measurableSet_singleton 0)
      have hc : S.ν (S.N T ⁻¹' {0})ᶜ = 0 := (prob_compl_eq_zero_iff hms).mpr hlaw
      rw [ae_iff]
      have e : {ω | ¬ S.N T ω = 0} = (S.N T ⁻¹' {0})ᶜ := by
        ext ω; simp
      rw [e]
      exact hc
  have hzero : ∀ T, ∀ᵐ ω ∂S.ν, (noOrderPolicy S).horizonCost L h p K T ω = 0 := by
    intro T
    filter_upwards [hN T] with ω hω
    simp [Policy.horizonCost, Policy.onHand, Policy.lost, Policy.orders, orderCount, delivered,
      noOrderPolicy, hω]
  unfold Policy.avgCost
  have hfun : (fun T : ℝ => (∫⁻ ω, (noOrderPolicy S).horizonCost L h p K T ω ∂S.ν) /
      ENNReal.ofReal T) = fun _ => 0 := by
    funext T
    rw [lintegral_congr_ae (hzero T), lintegral_zero, ENNReal.zero_div]
  rw [hfun]
  exact limsup_const 0

/-- With zero holding cost, (r,Q) policies have arbitrarily small cost. -/
lemma mt_h0 {lam : ℝ} (L p K : ℝ) (hlam : 0 < lam) (hL : 0 ≤ L) (hp : 0 ≤ p) (hK : 0 ≤ K)
    (S : DemandSpace lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ (j : ℕ) (h' : ℝ), 1 ≤ j ∧ 0 < h' ∧ ∃ π : Policy S,
      IsRQPolicy L (j - 1) (lotSize (K * lam / h')) π ∧ π.avgCost L 0 p K ≤ ENNReal.ofReal ε := by
  set μ := lam * L with hμdef
  have hμ : 0 ≤ μ := mul_nonneg hlam.le hL
  have hpl : 0 ≤ p * lam := mul_nonneg hp hlam.le
  obtain ⟨j, hj, hej⟩ := mt_lf_small hμ (δ := ε / (3 * (p * lam + 1))) (by positivity)
  set H := meanOnHand μ j with hHdef
  have hH : 0 ≤ H := mt_moh_nonneg hμ j
  have he0 := mt_lf_nonneg hμ j
  set h' := min (ε / (3 * (H + 1))) ((ε / 3) ^ 2 / (2 * K * lam + 1)) with hh'def
  have hh' : 0 < h' := lt_min (by positivity) (by positivity)
  obtain ⟨π, hπ⟩ := rq_policy_exists lam L hlam.le hL S (j - 1) (lotSize (K * lam / h'))
    (mt_lot_pos _)
  refine ⟨j, h', hj, hh', π, hπ, ?_⟩
  set a' := p * lam / h' with ha'def
  set k' := K * lam / h' with hk'def
  have ha' : 0 ≤ a' := by positivity
  have hk' : 0 ≤ k' := by positivity
  have hmono := mt_avg_mono_h π (L := L) (p := p) (K := K) hh'.le
  have havg := ts_avg hlam π L h' p K hh'
  obtain ⟨hb1, hb2⟩ := batching_upper_bound μ a' k' hμ ha' hk' (tsSpace S hlam) j hj
    (tsPolicy hlam π) (ts_rq hlam hπ)
  have hreal : h' * (baseStockCost μ a' j + batchSurcharge k') ≤ ε := by
    have e1 : h' * baseStockCost μ a' j = h' * H + p * lam * lossFraction μ j := by
      unfold baseStockCost
      rw [ha'def, hHdef]
      field_simp
    have hA : h' * H ≤ ε / 3 := by
      have h1 : h' ≤ ε / (3 * (H + 1)) := min_le_left _ _
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hB : p * lam * lossFraction μ j ≤ ε / 3 := by
      have h1 : p * lam * lossFraction μ j ≤ p * lam * (ε / (3 * (p * lam + 1))) :=
        mul_le_mul_of_nonneg_left hej hpl
      have h2 : p * lam * (ε / (3 * (p * lam + 1))) ≤ (p * lam + 1) * (ε / (3 * (p * lam + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h3 : (p * lam + 1) * (ε / (3 * (p * lam + 1))) = ε / 3 := by field_simp
      linarith
    have hC : h' * batchSurcharge k' ≤ ε / 3 := by
      have h1 : h' * batchSurcharge k' ≤ h' * Real.sqrt (2 * k') :=
        mul_le_mul_of_nonneg_left hb2 hh'.le
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * k' by positivity)
      have hsq : (h' * Real.sqrt (2 * k')) ^ 2 ≤ (ε / 3) ^ 2 := by
        have e : (h' * Real.sqrt (2 * k')) ^ 2 = 2 * K * lam * h' := by
          rw [mul_pow, hs, hk'def]; field_simp
        rw [e]
        have h2 : h' ≤ (ε / 3) ^ 2 / (2 * K * lam + 1) := min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at h2
        nlinarith
      have h2 : h' * Real.sqrt (2 * k') ≤ ε / 3 :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
      linarith
    rw [mul_add, e1]
    linarith
  calc π.avgCost L 0 p K ≤ π.avgCost L h' p K := hmono
    _ = ENNReal.ofReal h' * (tsPolicy hlam π).avgCost μ 1 a' k' := havg
    _ ≤ ENNReal.ofReal h' * ENNReal.ofReal (baseStockCost μ a' j + batchSurcharge k') := by
        gcongr
    _ = ENNReal.ofReal (h' * (baseStockCost μ a' j + batchSurcharge k')) :=
        (ENNReal.ofReal_mul hh'.le).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal

/-- The tightness ratio approaches the square root of two. -/
lemma mt_sup_ge : ENNReal.ofReal (Real.sqrt 2) ≤
    ⨆ (μ : ℝ) (a : ℝ) (_ : 0 < μ ∧ 0 < a),
      ENNReal.ofReal (minBaseStockCost μ a) / OPTk μ a 0 := by
  apply le_of_forall_lt
  intro y hy
  have hytop : y ≠ ⊤ := ne_top_of_lt hy
  set c := y.toReal with hcdef
  have hc : c < Real.sqrt 2 := ENNReal.toReal_lt_of_lt_ofReal hy
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hyc : y = ENNReal.ofReal c := (ENNReal.ofReal_toReal hytop).symm
  set d := Real.sqrt 2 - c with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  set a := (3 / d) ^ 2 + 2 with hadef
  have ha2 : 2 ≤ a := by rw [hadef]; nlinarith [sq_nonneg (3 / d)]
  have ha0 : 0 < a := by linarith
  set μ := a ^ 2 with hμdef
  have hμ0 : 0 < μ := by positivity
  set r := Real.sqrt a with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr ha0
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha0.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hrd : 3 / d < r := by
    rw [hrdef]
    rw [Real.lt_sqrt (by positivity)]
    rw [hadef]; linarith
  have hr1 : Real.sqrt 2 ≤ r := by
    rw [hrdef]; exact Real.sqrt_le_sqrt ha2
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- lower bound on U
  have haμ : a / μ = 1 / a := by rw [hμdef]; field_simp
  have hLB : 2 * Real.sqrt (a * (1 - a / μ)) - (1 - a / μ) ≤ minBaseStockCost μ a := by
    unfold minBaseStockCost
    exact le_ciInf ((tightness_bounds).2 μ a ha0 (by rw [hμdef]; nlinarith))
  have hsqrt : r - 1 / r ≤ Real.sqrt (a * (1 - a / μ)) := by
    rw [haμ]
    have e : a * (1 - 1 / a) = a - 1 := by field_simp
    rw [e]
    have hpos : 0 ≤ r - 1 / r := by
      rw [sub_nonneg, div_le_iff₀ hr0]; nlinarith
    rw [Real.le_sqrt hpos (by linarith)]
    have e2 : (r - 1 / r) ^ 2 = r ^ 2 - 2 + 1 / r ^ 2 := by field_simp; ring
    rw [e2, hr2]
    have : 1 / a ≤ 1 := by rw [div_le_one ha0]; linarith
    linarith
  have h1a : 0 ≤ 1 - a / μ := by rw [haμ, sub_nonneg, div_le_one ha0]; linarith
  have h1a' : 1 - a / μ ≤ 1 := by rw [haμ]; have : 0 < 1 / a := by positivity
                                  linarith
  -- U > c * sqrt (2 a)
  have hsa : Real.sqrt (2 * a) = Real.sqrt 2 * r := by
    rw [hrdef, Real.sqrt_mul (by norm_num)]
  have hkey : c * Real.sqrt (2 * a) < minBaseStockCost μ a := by
    rw [hsa]
    have hc' : c = Real.sqrt 2 - d := by rw [hddef]; ring
    -- 2 r - 2 / r - 1 > c sqrt2 r
    have hinv : 1 / r ≤ 1 := by rw [div_le_one hr0]; linarith
    have hdr : 3 < d * r := by
      have := (div_lt_iff₀ hd).mp hrd
      linarith
    have hmain : c * (Real.sqrt 2 * r) < 2 * (r - 1 / r) - 1 := by
      rw [hc']
      have e : (Real.sqrt 2 - d) * (Real.sqrt 2 * r) = 2 * r - Real.sqrt 2 * (d * r) := by
        have : (Real.sqrt 2 - d) * (Real.sqrt 2 * r) = Real.sqrt 2 ^ 2 * r - Real.sqrt 2 * (d * r) := by
          ring
        rw [this, hs2]
      rw [e]
      nlinarith
    linarith
  -- assemble
  have hOPT : OPTk μ a 0 ≤ ENNReal.ofReal (Real.sqrt (2 * a)) :=
    (tightness_bounds).1 μ a hμ0.le (by linarith)
  have hsa_pos : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.mpr (by positivity)
  have hratio : ENNReal.ofReal (minBaseStockCost μ a / Real.sqrt (2 * a)) ≤
      ENNReal.ofReal (minBaseStockCost μ a) / OPTk μ a 0 := by
    rw [ENNReal.ofReal_div_of_pos hsa_pos]
    exact ENNReal.div_le_div_left hOPT _
  have hlt : ENNReal.ofReal c < ENNReal.ofReal (minBaseStockCost μ a / Real.sqrt (2 * a)) := by
    have hq : c < minBaseStockCost μ a / Real.sqrt (2 * a) := by
      rw [lt_div_iff₀ hsa_pos]; linarith
    rw [ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hc0 hq)]
    exact hq
  rw [hyc]
  calc ENNReal.ofReal c < ENNReal.ofReal (minBaseStockCost μ a / Real.sqrt (2 * a)) := hlt
    _ ≤ ENNReal.ofReal (minBaseStockCost μ a) / OPTk μ a 0 := hratio
    _ ≤ ⨆ (μ : ℝ) (a : ℝ) (_ : 0 < μ ∧ 0 < a),
          ENNReal.ofReal (minBaseStockCost μ a) / OPTk μ a 0 :=
        le_iSup_of_le μ (le_iSup_of_le a (le_iSup_of_le ⟨hμ0, ha0⟩ le_rfl))

end LostSalesRQ

end

open LostSalesRQ in
theorem solution :
    (∀ lam L h p K : ℝ, 0 ≤ lam → 0 ≤ L → 0 ≤ h → 0 ≤ p → 0 ≤ K →
      ∀ S : DemandSpace lam,
        rQFamilyCost S L h p K ≤
          ENNReal.ofReal ((Real.sqrt 2 + Real.sqrt 6) / 2) * OPT lam L h p K) ∧
    (∀ lam L h p : ℝ, 0 ≤ lam → 0 ≤ L → 0 ≤ h → 0 ≤ p →
      ∀ S : DemandSpace lam,
        baseStockFamilyCost S L h p ≤ ENNReal.ofReal (Real.sqrt 2) * OPT lam L h p 0) ∧
    (∀ lam L h p : ℝ, 0 < lam → 0 ≤ L → 0 < h → 0 ≤ p →
      ∀ S : DemandSpace lam, ∀ Sstar : ℕ,
        (∀ j : ℕ, baseStockCost (lam * L) (p * lam / h) Sstar ≤
          baseStockCost (lam * L) (p * lam / h) j) →
        (∃ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) 0 Sstar π) ∧
        ∀ π : Policy S, IsSelectedPolicy L (lam * L) (p * lam / h) 0 Sstar π →
          π ∈ baseStockFamily S L ∧ π.avgCost L h p 0 = baseStockFamilyCost S L h p) ∧
    (⨆ (μ : ℝ) (a : ℝ) (_ : 0 < μ ∧ 0 < a),
        ENNReal.ofReal (minBaseStockCost μ a) / OPTk μ a 0) = ENNReal.ofReal (Real.sqrt 2) ∧
    (∀ μ a : ℝ, 0 < μ → 0 < a →
      ENNReal.ofReal (lowerCurve μ a) ≤ OPTk μ a 0 ∧ min 1 a ≤ lowerCurve μ a ∧
        0 < min 1 a) := by
  have hs6 : Real.sqrt 2 ≤ (Real.sqrt 2 + Real.sqrt 6) / 2 := by
    have : Real.sqrt 2 ≤ Real.sqrt 6 := Real.sqrt_le_sqrt (by norm_num)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro lam L h p K hlam hL hh hp hK S
    rcases hlam.eq_or_lt with hl0 | hlpos
    · subst hl0
      have hmem : noOrderPolicy S ∈ rQFamily S L := Set.mem_union_right _ (Set.mem_singleton _)
      calc rQFamilyCost S L h p K ≤ (noOrderPolicy S).avgCost L h p K := iInf₂_le _ hmem
        _ = 0 := mt_noorder_zero S L h p K
        _ ≤ _ := zero_le
    · rcases hh.eq_or_lt with hh0 | hhpos
      · subst hh0
        have hz : rQFamilyCost S L 0 p K ≤ 0 := by
          apply ENNReal.le_of_forall_pos_le_add
          intro ε hε _
          obtain ⟨j, h', hj, hh', π, hπ, hcost⟩ :=
            mt_h0 L p K hlpos hL hp hK S (ε := (ε : ℝ)) (by exact_mod_cast hε)
          have hmem : π ∈ rQFamily S L :=
            Set.mem_union_left _ ⟨j - 1, lotSize (K * lam / h'), mt_lot_pos _, hπ⟩
          calc rQFamilyCost S L 0 p K ≤ π.avgCost L 0 p K := iInf₂_le _ hmem
            _ ≤ ENNReal.ofReal ε := hcost
            _ = 0 + ε := by rw [zero_add, ENNReal.ofReal_coe_nnreal]
        exact le_trans hz (zero_le)
      · obtain ⟨Sstar, hS⟩ := mt_exists_min (μ := lam * L) (a := p * lam / h)
          (mul_nonneg hlpos.le hL) (by positivity)
        have hps := policy_selection lam L h p K hlpos hL hhpos hp hK S Sstar hS
        obtain ⟨π, hπ⟩ := hps.1
        have hb := (hps.2 π hπ).1
        have hmem : π ∈ rQFamily S L := by
          unfold IsSelectedPolicy at hπ
          split_ifs at hπ with hcond
          · exact Set.mem_union_left _ ⟨Sstar - 1, _, mt_lot_pos _, hπ⟩
          · rw [hπ]; exact Set.mem_union_right _ (Set.mem_singleton _)
        calc rQFamilyCost S L h p K ≤ π.avgCost L h p K := iInf₂_le _ hmem
          _ ≤ ENNReal.ofReal (if K = 0 then Real.sqrt 2 else (Real.sqrt 2 + Real.sqrt 6) / 2) *
                OPT lam L h p K := hb
          _ ≤ ENNReal.ofReal ((Real.sqrt 2 + Real.sqrt 6) / 2) * OPT lam L h p K := by
              gcongr
              split_ifs
              · exact hs6
              · exact le_rfl
  · intro lam L h p hlam hL hh hp S
    rcases hlam.eq_or_lt with hl0 | hlpos
    · subst hl0
      have hmem : noOrderPolicy S ∈ baseStockFamily S L :=
        Set.mem_union_right _ (Set.mem_singleton _)
      calc baseStockFamilyCost S L h p ≤ (noOrderPolicy S).avgCost L h p 0 := iInf₂_le _ hmem
        _ = 0 := mt_noorder_zero S L h p 0
        _ ≤ _ := zero_le
    · rcases hh.eq_or_lt with hh0 | hhpos
      · subst hh0
        have hz : baseStockFamilyCost S L 0 p ≤ 0 := by
          apply ENNReal.le_of_forall_pos_le_add
          intro ε hε _
          obtain ⟨j, h', hj, hh', π, hπ, hcost⟩ :=
            mt_h0 L p 0 hlpos hL hp le_rfl S (ε := (ε : ℝ)) (by exact_mod_cast hε)
          rw [zero_mul, zero_div, mt_lot0] at hπ
          have hmem : π ∈ baseStockFamily S L := Set.mem_union_left _ ⟨j, hj, hπ⟩
          calc baseStockFamilyCost S L 0 p ≤ π.avgCost L 0 p 0 := iInf₂_le _ hmem
            _ ≤ ENNReal.ofReal ε := hcost
            _ = 0 + ε := by rw [zero_add, ENNReal.ofReal_coe_nnreal]
        exact le_trans hz (zero_le)
      · obtain ⟨Sstar, hS⟩ := mt_exists_min (μ := lam * L) (a := p * lam / h)
          (mul_nonneg hlpos.le hL) (by positivity)
        have hps := policy_selection lam L h p 0 hlpos hL hhpos hp le_rfl S Sstar hS
        obtain ⟨π, hπ⟩ := hps.1
        have hb := hps.2 π hπ
        have hmem := (hb.2 rfl).1
        calc baseStockFamilyCost S L h p ≤ π.avgCost L h p 0 := iInf₂_le _ hmem
          _ ≤ ENNReal.ofReal (if (0 : ℝ) = 0 then Real.sqrt 2 else (Real.sqrt 2 + Real.sqrt 6) / 2) *
                OPT lam L h p 0 := hb.1
          _ = ENNReal.ofReal (Real.sqrt 2) * OPT lam L h p 0 := by rw [if_pos rfl]
  · intro lam L h p hlam hL hh hp S Sstar hS
    have hps := policy_selection lam L h p 0 hlam hL hh hp le_rfl S Sstar hS
    have e0 : (0 : ℝ) * lam / h = 0 := by simp
    rw [e0] at hps
    refine ⟨hps.1, fun π hπ => ?_⟩
    have hb := (hps.2 π hπ).2 rfl
    refine ⟨hb.1, le_antisymm ?_ (iInf₂_le _ hb.1)⟩
    exact le_iInf₂ (fun π' hπ' => hb.2 π' hπ')
  · apply le_antisymm
    · apply iSup_le; intro μ; apply iSup_le; intro a; apply iSup_le; intro hμa
      exact ENNReal.div_le_of_le_mul ((sqrt_two_zero_setup μ a hμa.1.le hμa.2.le).2)
    · exact mt_sup_ge
  · intro μ a hμ ha
    have hlc := lower_curve_properties μ hμ.le
    exact ⟨hlc.1 a ha.le, (hlc.2.2.2.2.2 a ha.le).1, lt_min one_pos ha⟩
