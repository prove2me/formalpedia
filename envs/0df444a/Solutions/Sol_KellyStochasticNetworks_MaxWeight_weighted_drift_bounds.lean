-- Prove2me | solution 1 for KellyStochasticNetworks.MaxWeight.weighted_drift_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:12:57.36322+00:00
-- url     : https://prove2.me/submissions/a779ae6d-599a-4eb2-b994-2a9c2646a671

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Network

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

/-- Expectations under a pushed-forward PMF. -/
lemma tsum_map_mul {α β : Type*} (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' j, (p.map g) j * f j = ∑' a, p a * f (g a) := by
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  have : ∀ j, (if j = g a then p a else 0) * f j = if j = g a then p a * f (g a) else 0 := by
    intro j; split_ifs with h
    · rw [h]
    · simp
  simp only [this]
  exact tsum_ite_eq (g a) _

lemma tsum_bind_mul {α β : Type*} (p : PMF α) (h : α → PMF β) (f : β → ℝ≥0∞) :
    ∑' j, (p.bind h) j * f j = ∑' a, p a * ∑' j, h a j * f j := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

variable {R : Type*} [Fintype R]

lemma chain_exp (lam : R → ℝ≥0) (tie : (R → ℕ) → PMF (R → ℕ)) (q : R → ℕ)
    (f : (R → ℕ) → ℝ≥0∞) :
    ∑' j, queueChain lam tie q j * f j =
      ∑' σ, tie q σ * ∑' a, arrivalLaw lam a * f (nextQueue q σ a) := by
  unfold queueChain
  rw [tsum_bind_mul]
  refine tsum_congr (fun σ => ?_)
  rw [tsum_map_mul]

/-- Poisson mean. -/
lemma poisson_mean (l : ℝ≥0) :
    ∫⁻ x : ℕ, ENNReal.ofReal (x : ℝ) ∂(poissonMeasure l) = (l : ℝ≥0∞) := by
  rw [lintegral_countable']
  simp only [poissonMeasure_singleton]
  have hs : HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-(l : ℝ)) * (l : ℝ) ^ n / n.factorial))
      (l : ℝ) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (l : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at he
    have h1 : HasSum (fun n : ℕ => Real.exp (-(l : ℝ)) * (l : ℝ) * ((l : ℝ) ^ n / n.factorial))
        (Real.exp (-(l : ℝ)) * (l : ℝ) * Real.exp (l : ℝ)) := he.mul_left _
    have h2 : Real.exp (-(l : ℝ)) * (l : ℝ) * Real.exp (l : ℝ) = (l : ℝ) := by
      rw [mul_comm (Real.exp _) (l : ℝ), mul_assoc, ← Real.exp_add]; simp
    rw [h2] at h1
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    refine h1.congr_fun (fun n => ?_)
    rw [Nat.factorial_succ]; push_cast
    field_simp
    ring
  calc ∑' n : ℕ, ENNReal.ofReal (n : ℝ) *
        ENNReal.ofReal (Real.exp (-(l : ℝ)) * (l : ℝ) ^ n / n.factorial)
      = ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (Real.exp (-(l : ℝ)) * (l : ℝ) ^ n / n.factorial)) :=
        tsum_congr (fun n => (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm)
    _ = ENNReal.ofReal (l : ℝ) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
    _ = (l : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

lemma arrival_mean (lam : R → ℝ≥0) (r : R) :
    ∑' a, arrivalLaw lam a * ENNReal.ofReal (a r : ℝ) = (lam r : ℝ≥0∞) := by
  unfold arrivalLaw
  simp only [Measure.toPMF_apply]
  have : ∑' a : R → ℕ, (Measure.pi fun r => poissonMeasure (lam r)) {a} * ENNReal.ofReal (a r : ℝ) =
      ∫⁻ a : R → ℕ, ENNReal.ofReal (a r : ℝ) ∂(Measure.pi fun r => poissonMeasure (lam r)) := by
    rw [lintegral_countable']; exact tsum_congr (fun a => mul_comm _ _)
  rw [this]
  have hmp := measurePreserving_eval (fun r => poissonMeasure (lam r)) r
  rw [← poisson_mean (lam r)]
  exact hmp.lintegral_comp (f := fun x : ℕ => ENNReal.ofReal (x : ℝ)) (measurable_of_countable _)

lemma arrival_total (lam : R → ℝ≥0) : ∑' a, arrivalLaw lam a = 1 := PMF.tsum_coe _

end X5WD


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

variable {R : Type*} [Fintype R] (lam : R → ℝ≥0) (tie : (R → ℕ) → PMF (R → ℕ))

lemma next_cast (q σ a : R → ℕ) (r : R) :
    ((nextQueue q σ a r : ℕ) : ℝ) = ((q r - σ r : ℕ) : ℝ) + (a r : ℝ) := by
  unfold nextQueue; push_cast; ring

lemma exp_abs (q : R → ℕ) (r : R) :
    ∑' j, queueChain lam tie q j * ENNReal.ofReal |(j r : ℝ) - q r| ≤ (lam r : ℝ≥0∞) + q r := by
  rw [chain_exp]
  calc ∑' σ, tie q σ * ∑' a, arrivalLaw lam a *
        ENNReal.ofReal |((nextQueue q σ a r : ℕ) : ℝ) - q r|
      ≤ ∑' σ, tie q σ * ∑' a, arrivalLaw lam a * (ENNReal.ofReal (a r : ℝ) + q r) := by
        refine ENNReal.tsum_le_tsum (fun σ => mul_le_mul_right
          (ENNReal.tsum_le_tsum (fun a => mul_le_mul_right ?_ _)) _)
        rw [next_cast]
        have h1 : ((q r - σ r : ℕ) : ℝ) ≤ q r := by exact_mod_cast Nat.sub_le _ _
        have h2 : (0:ℝ) ≤ ((q r - σ r : ℕ) : ℝ) := Nat.cast_nonneg _
        have h3 : (0:ℝ) ≤ (a r : ℝ) := Nat.cast_nonneg _
        have : |((q r - σ r : ℕ) : ℝ) + (a r : ℝ) - q r| ≤ (a r : ℝ) + q r := by
          rw [abs_le]; constructor <;> linarith
        calc ENNReal.ofReal |((q r - σ r : ℕ) : ℝ) + (a r : ℝ) - q r|
            ≤ ENNReal.ofReal ((a r : ℝ) + q r) := ENNReal.ofReal_le_ofReal this
          _ = ENNReal.ofReal (a r : ℝ) + q r := by
            rw [ENNReal.ofReal_add h3 (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
              ENNReal.ofReal_natCast]
    _ = (lam r : ℝ≥0∞) + q r := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, arrival_mean, arrival_total,
          one_mul, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

lemma integrable (q : R → ℕ) (r : R) :
    DriftIntegrable (queueChain lam tie) (fun x => (x r : ℝ)) q := by
  unfold DriftIntegrable
  have hfin : ∑' j, queueChain lam tie q j * ENNReal.ofReal |(j r : ℝ) - q r| ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.natCast_ne_top _⟩)
      (exp_abs lam tie q r)
  refine (ENNReal.summable_toReal hfin).congr (fun j => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Expected number of unused-service-free departures complement. -/
noncomputable def Ex (q : R → ℕ) (r : R) : ℝ≥0∞ := ∑' σ, tie q σ * ((q r - σ r : ℕ) : ℝ≥0∞)

lemma Ex_le (q : R → ℕ) (r : R) : Ex tie q r ≤ q r := by
  unfold Ex
  calc ∑' σ, tie q σ * ((q r - σ r : ℕ) : ℝ≥0∞) ≤ ∑' σ, tie q σ * (q r : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum (fun σ => mul_le_mul_right (by exact_mod_cast Nat.sub_le _ _) _)
    _ = q r := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma Ex_ne_top (q : R → ℕ) (r : R) : Ex tie q r ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (Ex_le tie q r)

lemma exp_coord (q : R → ℕ) (r : R) :
    ∑' j, queueChain lam tie q j * ENNReal.ofReal (j r : ℝ) = Ex tie q r + lam r := by
  rw [chain_exp]
  have h : ∀ σ, ∑' a, arrivalLaw lam a * ENNReal.ofReal ((nextQueue q σ a r : ℕ) : ℝ) =
      ((q r - σ r : ℕ) : ℝ≥0∞) + lam r := by
    intro σ
    have : ∀ a, arrivalLaw lam a * ENNReal.ofReal ((nextQueue q σ a r : ℕ) : ℝ) =
        arrivalLaw lam a * ((q r - σ r : ℕ) : ℝ≥0∞) + arrivalLaw lam a * ENNReal.ofReal (a r : ℝ) := by
      intro a
      rw [next_cast, ENNReal.ofReal_add (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, mul_add]
    simp only [this]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, arrival_total, one_mul, arrival_mean]
  simp only [h, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rfl

lemma drift_formula (q : R → ℕ) (r : R) :
    drift (queueChain lam tie) (fun x => (x r : ℝ)) q = (Ex tie q r).toReal + lam r - q r := by
  set P := queueChain lam tie
  have hne : ∀ j, P q j ≠ ⊤ := PMF.apply_ne_top (P q)
  have hfin : ∑' j, P q j * ENNReal.ofReal (j r : ℝ) ≠ ⊤ := by
    rw [exp_coord]; exact ENNReal.add_ne_top.2 ⟨Ex_ne_top tie q r, ENNReal.coe_ne_top⟩
  have hs1 : Summable (fun j => (P q j).toReal * (j r : ℝ)) :=
    (ENNReal.summable_toReal hfin).congr (fun j => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _)])
  have hs2 : Summable (fun j => (P q j).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have htot : ∑' j, (P q j).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq hne, PMF.tsum_coe, ENNReal.toReal_one]
  have hmean : ∑' j, (P q j).toReal * (j r : ℝ) = (Ex tie q r).toReal + lam r := by
    rw [← ENNReal.toReal_ofReal_eq_iff.2 (show (0:ℝ) ≤ ∑' j, (P q j).toReal * (j r : ℝ) from
      tsum_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)))]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) hs1]
    have : ∀ j, ENNReal.ofReal ((P q j).toReal * (j r : ℝ)) = P q j * ENNReal.ofReal (j r : ℝ) := by
      intro j; rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hne j)]
    simp only [this]
    rw [exp_coord, ENNReal.toReal_add (Ex_ne_top tie q r) ENNReal.coe_ne_top]
    rfl
  unfold drift
  have : ∀ j, (P q j).toReal * ((j r : ℝ) - q r) = (P q j).toReal * (j r : ℝ) - (P q j).toReal * q r :=
    fun j => by ring
  simp only [this]
  rw [hs1.tsum_sub (hs2.mul_right _), tsum_mul_right, htot, hmean]
  ring

end X5WD


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

variable {R : Type*} [Fintype R]

/-- Strictly inside the capacity region: a uniform slack `δ`. -/
lemma interior_slack (N : Network R) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ c : (R → ℕ) → ℝ, (∀ σ ∈ N.schedules, 0 ≤ c σ) ∧
      (∑ σ ∈ N.schedules, c σ) = 1 ∧
      ∀ r, (lam r : ℝ) + δ ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hlam
  obtain ⟨ε, hε, hball⟩ := hlam
  refine ⟨ε / 2, by linarith, ?_⟩
  have hv : (fun r => (lam r : ℝ) + ε / 2) ∈ capacityRegion N := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro r
    rw [Real.dist_eq]
    simp only [add_sub_cancel_left]
    rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨-, c, hc0, hc1, hcle⟩ := hv
  exact ⟨c, hc0, hc1, hcle⟩

noncomputable def Bm (N : Network R) : ℝ := ∑ r, (serviceBound N r : ℝ)

lemma sched_le (N : Network R) {σ : R → ℕ} (hσ : σ ∈ N.schedules) (r : R) :
    (σ r : ℝ) ≤ Bm N := by
  have h1 : σ r ≤ serviceBound N r := Finset.le_sup (f := fun σ => σ r) hσ
  have h2 : (serviceBound N r : ℝ) ≤ Bm N :=
    Finset.single_le_sum (f := fun r => (serviceBound N r : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_univ r)
  exact le_trans (by exact_mod_cast h1) h2

/-- Per-schedule bound for a maximizing schedule. -/
lemma per_sched (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0) (δ : ℝ)
    (c : (R → ℕ) → ℝ) (hc0 : ∀ σ ∈ N.schedules, 0 ≤ c σ) (hc1 : (∑ σ ∈ N.schedules, c σ) = 1)
    (hcle : ∀ r, (lam r : ℝ) + δ ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ))
    (q σ : R → ℕ) (hσ : σ ∈ N.schedules)
    (hmax : ∀ π ∈ N.schedules, scheduleWeight α q π ≤ scheduleWeight α q σ) :
    ∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ) ≤
      ∑ r, (q r : ℝ) ^ α * (q r : ℝ) - ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) +
        Fintype.card R * (Bm N * Bm N ^ α) := by
  have hqa : ∀ r, 0 ≤ (q r : ℝ) ^ α := fun r => Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- convex combination is dominated by the max weight
  have h1 : ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) ≤ scheduleWeight α q σ := by
    calc ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ)
        ≤ ∑ r, (q r : ℝ) ^ α * ∑ π ∈ N.schedules, c π * (π r : ℝ) :=
          Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left (hcle r) (hqa r))
      _ = ∑ π ∈ N.schedules, c π * scheduleWeight α q π := by
          unfold scheduleWeight
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun r _ => by ring))
      _ ≤ ∑ π ∈ N.schedules, c π * scheduleWeight α q σ :=
          Finset.sum_le_sum (fun π hπ => mul_le_mul_of_nonneg_left (hmax π hπ) (hc0 π hπ))
      _ = scheduleWeight α q σ := by rw [← Finset.sum_mul, hc1, one_mul]
  -- unused service is bounded
  have hB0 : 0 ≤ Bm N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have h2 : ∀ r, (σ r : ℝ) * (q r : ℝ) ^ α ≤
      ((q r : ℝ) - ((q r - σ r : ℕ) : ℝ)) * (q r : ℝ) ^ α + Bm N * Bm N ^ α := by
    intro r
    have hBa : 0 ≤ Bm N * Bm N ^ α := mul_nonneg hB0 (Real.rpow_nonneg hB0 _)
    rcases le_or_gt (σ r) (q r) with h | h
    · rw [Nat.cast_sub h]; nlinarith [hqa r]
    · have hz : q r - σ r = 0 := by omega
      rw [hz, Nat.cast_zero, sub_zero]
      have hs := sched_le N hσ r
      have hq : (q r : ℝ) ≤ Bm N := le_trans (by exact_mod_cast h.le) hs
      have := Real.rpow_le_rpow (Nat.cast_nonneg (q r)) hq hα.le
      have : (σ r : ℝ) * (q r : ℝ) ^ α ≤ Bm N * Bm N ^ α :=
        mul_le_mul hs this (hqa r) hB0
      nlinarith [hqa r, (Nat.cast_nonneg (q r) : (0:ℝ) ≤ q r)]
  have h3 : scheduleWeight α q σ ≤ ∑ r, (((q r : ℝ) - ((q r - σ r : ℕ) : ℝ)) * (q r : ℝ) ^ α +
      Bm N * Bm N ^ α) := Finset.sum_le_sum (fun r _ => h2 r)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
  have e : ∑ r, ((q r : ℝ) - ((q r - σ r : ℕ) : ℝ)) * (q r : ℝ) ^ α =
      ∑ r, (q r : ℝ) ^ α * (q r : ℝ) - ∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun r _ => by ring)
  linarith

/-- Main drift estimate. -/
lemma drift_main (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0) (δ : ℝ)
    (c : (R → ℕ) → ℝ) (hc0 : ∀ σ ∈ N.schedules, 0 ≤ c σ) (hc1 : (∑ σ ∈ N.schedules, c σ) = 1)
    (hcle : ∀ r, (lam r : ℝ) + δ ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) (q : R → ℕ) :
    weightedDrift α (queueChain lam tie) q ≤
      -(δ * ∑ r, (q r : ℝ) ^ α) + Fintype.card R * (Bm N * Bm N ^ α) := by
  set U := ∑ r, (q r : ℝ) ^ α * (q r : ℝ) - ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) +
        Fintype.card R * (Bm N * Bm N ^ α)
  have hqa : ∀ r, 0 ≤ (q r : ℝ) ^ α := fun r => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsupp : ∀ σ, tie q σ ≠ 0 → ∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ) ≤ U := by
    intro σ hσ
    obtain ⟨hσs, hmax⟩ := htie q σ hσ
    exact per_sched N α hα lam δ c hc0 hc1 hcle q σ hσs hmax
  have hU : 0 ≤ U := by
    obtain ⟨σ, hσ⟩ := (tie q).support_nonempty
    refine le_trans (Finset.sum_nonneg (fun r _ => mul_nonneg (hqa r) (Nat.cast_nonneg _)))
      (hsupp σ ((PMF.mem_support_iff _ _).1 hσ))
  -- average over the tie rule
  have hE : ∑ r, (q r : ℝ) ^ α * (Ex tie q r).toReal ≤ U := by
    have hen : ∑ r, ENNReal.ofReal ((q r : ℝ) ^ α) * Ex tie q r =
        ∑' σ, tie q σ * ENNReal.ofReal (∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ)) := by
      unfold Ex
      simp only [← ENNReal.tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr (fun σ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg (hqa r) (Nat.cast_nonneg _)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [ENNReal.ofReal_mul (hqa r), ENNReal.ofReal_natCast]; ring
    have hle : ∑ r, ENNReal.ofReal ((q r : ℝ) ^ α) * Ex tie q r ≤ ENNReal.ofReal U := by
      rw [hen]
      calc ∑' σ, tie q σ * ENNReal.ofReal (∑ r, (q r : ℝ) ^ α * ((q r - σ r : ℕ) : ℝ))
          ≤ ∑' σ, tie q σ * ENNReal.ofReal U := by
            refine ENNReal.tsum_le_tsum (fun σ => ?_)
            by_cases h : tie q σ = 0
            · rw [h]; simp
            · exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hsupp σ h)) _
        _ = ENNReal.ofReal U := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    have hfin : ∀ r, ENNReal.ofReal ((q r : ℝ) ^ α) * Ex tie q r ≠ ⊤ :=
      fun r => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Ex_ne_top tie q r)
    have := ENNReal.toReal_le_of_le_ofReal hU hle
    rw [ENNReal.toReal_sum (fun r _ => hfin r)] at this
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hqa _)] using this
  unfold weightedDrift
  simp only [drift_formula]
  have e : ∑ r, (q r : ℝ) ^ α * ((Ex tie q r).toReal + lam r - q r) =
      ∑ r, (q r : ℝ) ^ α * (Ex tie q r).toReal + ∑ r, (q r : ℝ) ^ α * (lam r : ℝ) -
        ∑ r, (q r : ℝ) ^ α * (q r : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  have e2 : ∑ r, (q r : ℝ) ^ α * ((lam r : ℝ) + δ) =
      ∑ r, (q r : ℝ) ^ α * (lam r : ℝ) + δ * ∑ r, (q r : ℝ) ^ α := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e]
  simp only [U] at hE
  linarith

end X5WD


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Classical

namespace X5WD
open KellyStochasticNetworks.MaxWeight

variable {R : Type*} [Fintype R] [Nonempty R]

lemma norm_bound (α : ℝ) (hα : 0 < α) (q : R → ℕ) :
    queueNorm q ^ α ≤ Real.sqrt (Fintype.card R) ^ α * ∑ r, (q r : ℝ) ^ α := by
  obtain ⟨r0, -, hr0⟩ := Finset.exists_max_image Finset.univ (fun r => q r) Finset.univ_nonempty
  set m : ℝ := (q r0 : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have h1 : ∑ r, (q r : ℝ) ^ (2 : ℕ) ≤ Fintype.card R * m ^ 2 := by
    calc ∑ r, (q r : ℝ) ^ (2 : ℕ) ≤ ∑ _r : R, m ^ 2 := Finset.sum_le_sum (fun r _ => by
          have : (q r : ℝ) ≤ m := by simp only [m]; exact_mod_cast hr0 r (Finset.mem_univ r)
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2)
      _ = Fintype.card R * m ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : queueNorm q ≤ Real.sqrt (Fintype.card R) * m := by
    unfold queueNorm
    calc Real.sqrt (∑ r, (q r : ℝ) ^ (2 : ℕ)) ≤ Real.sqrt (Fintype.card R * m ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (Fintype.card R) * m := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hm]
  have hn0 : 0 ≤ queueNorm q := Real.sqrt_nonneg _
  calc queueNorm q ^ α ≤ (Real.sqrt (Fintype.card R) * m) ^ α :=
        Real.rpow_le_rpow hn0 h2 hα.le
    _ = Real.sqrt (Fintype.card R) ^ α * m ^ α := Real.mul_rpow (Real.sqrt_nonneg _) hm
    _ ≤ Real.sqrt (Fintype.card R) ^ α * ∑ r, (q r : ℝ) ^ α := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        exact Finset.single_le_sum (f := fun r => (q r : ℝ) ^ α)
          (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.mem_univ r0)

theorem main (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    (∀ q r, DriftIntegrable (queueChain lam tie) (fun x => (x r : ℝ)) q) ∧
    ∃ ε K b : ℝ, 0 < ε ∧ 0 < K ∧
      (∀ q, K < queueNorm q →
        weightedDrift α (queueChain lam tie) q < -ε * queueNorm q ^ α) ∧
      (∀ q, queueNorm q ≤ K → weightedDrift α (queueChain lam tie) q < b) := by
  refine ⟨fun q r => integrable lam tie q r, ?_⟩
  obtain ⟨δ, hδ, c, hc0, hc1, hcle⟩ := interior_slack N lam hlam
  set C0 : ℝ := Fintype.card R * (Bm N * Bm N ^ α)
  have hB0 : 0 ≤ Bm N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hC0 : 0 ≤ C0 := by positivity
  set s : ℝ := Real.sqrt (Fintype.card R) ^ α
  have hs : 0 < s := Real.rpow_pos_of_pos (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)) _
  have hD := fun q => drift_main N α hα lam δ c hc0 hc1 hcle tie htie q
  set x : ℝ := 2 * C0 * s / δ + 1
  have hx : 0 < x := by positivity
  refine ⟨δ / (2 * s), x ^ α⁻¹, C0 + 1, by positivity, Real.rpow_pos_of_pos hx _, ?_, ?_⟩
  · intro q hq
    have hK : (x ^ α⁻¹) ^ α < queueNorm q ^ α :=
      Real.rpow_lt_rpow (Real.rpow_nonneg hx.le _) hq hα
    rw [Real.rpow_inv_rpow hx.le hα.ne'] at hK
    have hnb := norm_bound α hα q
    have hsum : queueNorm q ^ α / s ≤ ∑ r, (q r : ℝ) ^ α := by
      rw [div_le_iff₀ hs]; linarith
    have h1 := hD q
    have h2 : 2 * C0 * s / δ < queueNorm q ^ α := by linarith
    rw [div_lt_iff₀ hδ] at h2
    have h3 : δ * (queueNorm q ^ α / s) ≤ δ * ∑ r, (q r : ℝ) ^ α :=
      mul_le_mul_of_nonneg_left hsum hδ.le
    have e1 : δ * (queueNorm q ^ α / s) = δ / s * queueNorm q ^ α := by ring
    have e2 : δ / (2 * s) * queueNorm q ^ α = δ / s * queueNorm q ^ α / 2 := by ring
    have h4 : C0 < δ / s * queueNorm q ^ α / 2 := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0:ℝ) < 2), div_mul_eq_mul_div,
        lt_div_iff₀ hs] at *
      nlinarith
    linarith
  · intro q _
    have h1 := hD q
    have : 0 ≤ δ * ∑ r, (q r : ℝ) ^ α :=
      mul_nonneg hδ.le (Finset.sum_nonneg (fun r _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    linarith

end X5WD


open KellyStochasticNetworks.MaxWeight in
theorem solution {R : Type*} [Fintype R] [Nonempty R]
    (N : Network R) (α : ℝ) (hα : 0 < α) (lam : R → ℝ≥0)
    (hlam : (fun r => (lam r : ℝ)) ∈ interior (capacityRegion N))
    (tie : (R → ℕ) → PMF (R → ℕ)) (htie : IsMaxWeight N α tie) :
    (∀ q r, DriftIntegrable (queueChain lam tie) (fun x => (x r : ℝ)) q) ∧
    ∃ ε K b : ℝ, 0 < ε ∧ 0 < K ∧
      (∀ q, K < queueNorm q →
        weightedDrift α (queueChain lam tie) q < -ε * queueNorm q ^ α) ∧
      (∀ q, queueNorm q ≤ K → weightedDrift α (queueChain lam tie) q < b) :=
  X5WD.main N α hα lam hlam tie htie
