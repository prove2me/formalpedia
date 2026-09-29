-- Prove2me | solution 1 for HairerSPDE.exists_fullMeasure_submodule_notMem
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T10:11:43.437907+00:00
-- url     : https://prove2.me/submissions/0c444c5f-b71a-4645-8631-c5a3fd2e49b9

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (L : ℕ → StrongDual ℝ B)
    (hL : ∀ n, covarianceBilinDual μ (L n) (L n) ≤ 1)
    (hLh : ∀ n, ((n : ℕ) : ℝ) ≤ (L n) h) :
    ∃ V : Submodule ℝ B, MeasurableSet (V : Set B) ∧ μ V = 1 ∧ h ∉ V := by
  -- The candidate full-measure subspace: points whose `L n`-coordinate grows slower
  -- than `n`, in the quantitative "for every `k`, eventually below `(n+1)/(k+1)`" form.
  let A : ℕ → Set B := fun k =>
    {x : B | ∀ᶠ n in atTop, |(L n) x| < (((n : ℝ) + 1) / ((k : ℝ) + 1))}
  have hmem : ∀ k : ℕ, A k = ⋃ N, ⋂ n : {n : ℕ // N ≤ n},
      {x : B | |(L n.1) x| < (((n.1 : ℝ) + 1) / ((k : ℝ) + 1))} := by
    intro k
    ext x
    simp only [A, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [Filter.eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n => hN n.1 n.2⟩
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => hN ⟨n, hn⟩⟩
  have hAmeas : ∀ k : ℕ, MeasurableSet (A k) := by
    intro k
    rw [hmem k]
    refine MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n => ?_))
    exact measurableSet_lt (by fun_prop) measurable_const
  -- Membership closure of the intersection.
  have hzero : (0 : B) ∈ ⋂ k, A k := by
    simp only [Set.mem_iInter, A, Set.mem_setOf_eq]
    intro k
    filter_upwards with n
    simp only [map_zero, abs_zero]
    positivity
  have hadd : ∀ x ∈ ⋂ k, A k, ∀ y ∈ ⋂ k, A k, x + y ∈ ⋂ k, A k := by
    intro x hx y hy
    simp only [Set.mem_iInter, A, Set.mem_setOf_eq] at hx hy ⊢
    intro k
    have hx' := hx (2 * k + 1)
    have hy' := hy (2 * k + 1)
    filter_upwards [hx', hy'] with n hxn hyn
    calc |(L n) (x + y)| = |(L n) x + (L n) y| := by rw [map_add]
      _ ≤ |(L n) x| + |(L n) y| := abs_add_le _ _
      _ < ((n : ℝ) + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1)
            + ((n : ℝ) + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1) := add_lt_add hxn hyn
      _ = ((n : ℝ) + 1) / ((k : ℝ) + 1) := by
            have hc : (((2 * k + 1 : ℕ) : ℝ) + 1) = 2 * ((k : ℝ) + 1) := by
              push_cast; ring
            rw [hc]
            field_simp
            ring
  have hsmul : ∀ c : ℝ, ∀ x ∈ ⋂ k, A k, c • x ∈ ⋂ k, A k := by
    intro c x hx
    by_cases hc : c = 0
    · rw [hc, zero_smul]; exact hzero
    · obtain ⟨m, hm⟩ := exists_nat_ge |c|
      have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (abs_pos.mpr hc) hm
      have hm1 : 1 ≤ m := by
        have : 0 < m := by exact_mod_cast hmpos
        omega
      simp only [Set.mem_iInter, A, Set.mem_setOf_eq] at hx ⊢
      intro k
      have hxk := hx (m * (k + 1))
      have hcast : (((m * (k + 1) : ℕ) : ℝ) + 1) = (m : ℝ) * ((k : ℝ) + 1) + 1 := by
        push_cast; ring
      rw [hcast] at hxk
      filter_upwards [hxk] with n hn
      calc |(L n) (c • x)| = |c * (L n) x| := by rw [map_smul]; rfl
        _ = |c| * |(L n) x| := abs_mul _ _
        _ ≤ (m : ℝ) * |(L n) x| := by gcongr
        _ < (m : ℝ) * (((n : ℝ) + 1) / ((m : ℝ) * ((k : ℝ) + 1) + 1)) := by
              gcongr
        _ ≤ ((n : ℝ) + 1) / ((k : ℝ) + 1) := by
              rw [mul_div_assoc']
              rw [div_le_div_iff₀
                (show (0 : ℝ) < (m : ℝ) * ((k : ℝ) + 1) + 1 by positivity)
                (show (0 : ℝ) < (k : ℝ) + 1 by positivity)]
              nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n,
                show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k, hmpos]
  -- Full measure of each `A k` via Chebyshev plus Borel-Cantelli.
  have hfull : ∀ k, μ (A k) = 1 := by
    intro k
    set s : ℕ → Set B := fun n =>
      {x : B | (((n : ℝ) + 1) / ((k : ℝ) + 1)) ≤ |(L n) x|} with hs
    have hbound : ∀ n, μ (s n) ≤ ENNReal.ofReal ((((k : ℝ) + 1) ^ 2) / (((n : ℝ) + 1) ^ 2)) := by
      intro n
      have hc : 0 < ((n : ℝ) + 1) / ((k : ℝ) + 1) := by positivity
      have hX : MemLp (L n) 2 μ := IsGaussian.memLp_dual μ (L n) 2 (by norm_num)
      have hmean : (∫ x, x ∂μ) = 0 := by simpa using hμ
      have hμL : μ[L n] = 0 := by
        rw [IsGaussian.integral_dual (μ := μ) (L := L n), hmean, map_zero]
      have hcheb := meas_ge_le_variance_div_sq (μ := μ) hX hc
      have hset : {ω : B | ((n : ℝ) + 1) / ((k : ℝ) + 1) ≤ |(L n) ω - μ[L n]|} = s n := by
        ext ω
        simp only [hs, Set.mem_setOf_eq]
        rw [hμL, sub_zero]
      rw [hset] at hcheb
      refine hcheb.trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hvar : variance (L n) μ ≤ 1 := by
        rw [← covarianceBilinDual_self_eq_variance (IsGaussian.memLp_two_id (μ := μ)) (L n)]
        exact hL n
      have hcle : variance (L n) μ / (((n : ℝ) + 1) / ((k : ℝ) + 1)) ^ 2
          ≤ (((k : ℝ) + 1) ^ 2) / (((n : ℝ) + 1) ^ 2) := by
        have hA : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := sq_nonneg _
        have hB : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
        have hkey : variance (L n) μ * (((k : ℝ) + 1) ^ 2) ≤ (((k : ℝ) + 1) ^ 2) := by
          simpa using mul_le_mul_of_nonneg_right hvar hA
        rw [div_pow, div_div_eq_mul_div, div_le_div_iff₀ hB hB]
        simpa using mul_le_mul_of_nonneg_right hkey (le_of_lt hB)
      exact hcle
    have hsumm : Summable (fun n : ℕ => (((k : ℝ) + 1) ^ 2) / (((n : ℝ) + 1) ^ 2)) := by
      have hbase : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
        have h0 : Summable (fun n : ℕ => (((n : ℕ) : ℝ) ^ 2)⁻¹) :=
          (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
        simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h0
      simpa only [div_eq_mul_inv, mul_comm] using hbase.mul_left (((k : ℝ) + 1) ^ 2)
    have hsum_ne_top : (∑' n, μ (s n)) ≠ ∞ := by
      have hle : (∑' n, μ (s n))
          ≤ ∑' (n : ℕ), ENNReal.ofReal ((((k : ℝ) + 1) ^ 2) / (((n : ℝ) + 1) ^ 2)) :=
        ENNReal.tsum_le_tsum (fun n => hbound n)
      refine ne_top_of_le_ne_top ?_ hle
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
      exact ENNReal.ofReal_ne_top
    have hBC : μ {x : B | ∃ᶠ n in atTop, x ∈ s n} = 0 :=
      measure_setOfPred_frequently_eq_zero hsum_ne_top
    have hae : ∀ᵐ x ∂μ, x ∈ A k := by
      filter_upwards [(ae_iff).mpr hBC] with x hx
      simp only [A, Set.mem_setOf_eq]
      filter_upwards [hx] with n hn
      simp only [hs, Set.mem_setOf_eq, not_le] at hn
      exact hn
    have hcompl : μ (A k)ᶜ = 0 := (ae_iff).mp hae
    have h1 := measure_add_measure_compl (μ := μ) (hAmeas k)
    rw [hcompl, add_zero, measure_univ] at h1
    exact h1
  -- The intersection has full measure.
  have hVmeas : MeasurableSet (⋂ k, A k) := MeasurableSet.iInter hAmeas
  have hV1 : μ (⋂ k, A k) = 1 := by
    have hae_k : ∀ k, ∀ᵐ x ∂μ, x ∈ A k := by
      intro k
      refine (ae_iff).mpr ?_
      have h := measure_compl (μ := μ) (hAmeas k) (measure_ne_top μ (A k))
      rw [hfull k, measure_univ, tsub_self] at h
      exact h
    have hae_all : ∀ᵐ x ∂μ, x ∈ ⋂ k, A k := by
      simpa only [Set.mem_iInter] using (ae_all_iff).mpr hae_k
    have hcompl : μ (⋂ k, A k)ᶜ = 0 := (ae_iff).mp hae_all
    have h1 := measure_add_measure_compl (μ := μ) hVmeas
    rw [hcompl, add_zero, measure_univ] at h1
    exact h1
  -- `h` is outside the intersection.
  have hnotmem : h ∉ ⋂ k, A k := by
    intro hmem'
    have h1 : h ∈ A 1 := (Set.mem_iInter.mp hmem') 1
    simp only [A, Set.mem_setOf_eq] at h1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h1
    set n := max N 1 with hn
    have hn1 : 1 ≤ n := le_max_right _ _
    have hNn : N ≤ n := le_max_left _ _
    have hge : (n : ℝ) ≤ (L n) h := hLh n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have habs : |(L n) h| = (L n) h := abs_of_nonneg (le_trans hnn hge)
    have hlt : |(L n) h| < ((n : ℝ) + 1) / 2 := by
      have h2 := hN n hNn
      norm_num at h2
      exact h2
    rw [habs] at hlt
    have hlt' : (n : ℝ) < ((n : ℝ) + 1) / 2 := lt_of_le_of_lt hge hlt
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  refine ⟨Submodule.ofLinearComb (⋂ k, A k) ⟨0, hzero⟩ ?_, hVmeas, hV1, hnotmem⟩
  intro x hx y hy a b
  exact hadd (a • x) (hsmul a x hx) (b • y) (hsmul b y hy)
