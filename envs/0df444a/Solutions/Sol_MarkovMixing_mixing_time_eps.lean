-- Prove2me | solution 1 for MarkovMixing.mixing_time_eps
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:12:46.39876+00:00
-- url     : https://prove2.me/submissions/4595e980-b59b-48cf-99c1-e72b3b34e31d

import Theorems.Thm_MarkovMixing_convergence_theorem
import Theorems.Thm_MarkovMixing_dist_le_distPairs
import Theorems.Thm_MarkovMixing_distPairs_submultiplicative
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ ℓ : ℕ, distStationary P π (ℓ * mixingTime P π ε) ≤ (2 * ε) ^ ℓ) ∧
    mixingTime P π ε ≤ ⌈Real.logb 2 ε⁻¹⌉₊ * tMix P π := by
  classical
  -- generic supremum facts
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have htv_ge : ∀ (μ ν : V → ℝ) (A : Finset V),
      |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν :=
    fun μ ν A => le_ciSup (hbdd μ ν) A
  have htv_nonneg : ∀ μ ν : V → ℝ, 0 ≤ tvDist μ ν := by
    intro μ ν
    have h := htv_ge μ ν ∅
    simpa using h
  have hbdd_d : ∀ n : ℕ, BddAbove (Set.range fun x : V => tvDist (rowDist P n x) π) :=
    fun n => Set.Finite.bddAbove (Set.range fun x : V => tvDist (rowDist P n x) π).toFinite
  have hd_nonneg : ∀ n : ℕ, 0 ≤ distStationary P π n := fun n =>
    le_trans (htv_nonneg _ _) (le_ciSup (hbdd_d n) (Classical.arbitrary V))
  have hbdd_dbar : ∀ n : ℕ,
      BddAbove (Set.range fun p : V × V => tvDist (rowDist P n p.1) (rowDist P n p.2)) :=
    fun n => Set.Finite.bddAbove
      (Set.range fun p : V × V => tvDist (rowDist P n p.1) (rowDist P n p.2)).toFinite
  have hdbar_nonneg : ∀ n : ℕ, 0 ≤ distPairs P n := fun n =>
    le_trans (htv_nonneg _ _)
      (le_ciSup (hbdd_dbar n) (Classical.arbitrary V, Classical.arbitrary V))
  -- the mixing-time set is nonempty, so the infimum is attained
  obtain ⟨α, hα, C, hC, hgeo⟩ := MarkovMixing.convergence_theorem P hP hirr hap π hπ
  have hattain : ∀ δ : ℝ, 0 < δ → distStationary P π (mixingTime P π δ) ≤ δ := by
    intro δ hδ
    have hne : {t : ℕ | distStationary P π t ≤ δ}.Nonempty := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := δ / C) (y := α) (by positivity) hα.2
      refine ⟨n, ?_⟩
      have h1 : C * α ^ n < C * (δ / C) := by
        exact mul_lt_mul_of_pos_left hn hC
      have h2 : C * (δ / C) = δ := by field_simp
      have := hgeo n
      simp only [Set.mem_setOf_eq]
      linarith
    exact Nat.sInf_mem hne
  -- the geometric decay of `d` along multiples of a mixing time
  have key : ∀ δ : ℝ, 0 < δ → ∀ ℓ : ℕ,
      distStationary P π (ℓ * mixingTime P π δ) ≤ (2 * δ) ^ ℓ := by
    intro δ hδ ℓ
    have hdbarT : distPairs P (mixingTime P π δ) ≤ 2 * δ := by
      have h := (MarkovMixing.dist_le_distPairs P hP π hπ (mixingTime P π δ)).2
      have h2 := hattain δ hδ
      linarith
    have hpowk : ∀ k : ℕ, distPairs P (k * mixingTime P π δ) ≤ (2 * δ) ^ k := by
      intro k
      induction k with
      | zero =>
          have h1 : distPairs P 0 ≤ 1 := by
            refine ciSup_le fun p => ciSup_le fun A => ?_
            have ha : (0:ℝ) ≤ ∑ z ∈ A, (rowDist P 0 p.1) z := by
              refine Finset.sum_nonneg fun z _ => ?_
              show (0:ℝ) ≤ (P ^ 0) p.1 z
              by_cases h : p.1 = z <;> simp [Matrix.one_apply, h]
            have hb : (0:ℝ) ≤ ∑ z ∈ A, (rowDist P 0 p.2) z := by
              refine Finset.sum_nonneg fun z _ => ?_
              show (0:ℝ) ≤ (P ^ 0) p.2 z
              by_cases h : p.2 = z <;> simp [Matrix.one_apply, h]
            have ha1 : ∑ z ∈ A, (rowDist P 0 p.1) z ≤ 1 := by
              have hsum : ∑ z, (rowDist P 0 p.1) z = 1 := by
                show ∑ z, (P ^ 0) p.1 z = 1
                simp [Matrix.one_apply]
              rw [← hsum]
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun z _ _ => ?_
              show (0:ℝ) ≤ (P ^ 0) p.1 z
              by_cases h : p.1 = z <;> simp [Matrix.one_apply, h]
            have hb1 : ∑ z ∈ A, (rowDist P 0 p.2) z ≤ 1 := by
              have hsum : ∑ z, (rowDist P 0 p.2) z = 1 := by
                show ∑ z, (P ^ 0) p.2 z = 1
                simp [Matrix.one_apply]
              rw [← hsum]
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) fun z _ _ => ?_
              show (0:ℝ) ≤ (P ^ 0) p.2 z
              by_cases h : p.2 = z <;> simp [Matrix.one_apply, h]
            rw [abs_le]
            constructor <;> linarith
          simpa using h1
      | succ m ih =>
          have hstep : distPairs P ((m + 1) * mixingTime P π δ)
              ≤ distPairs P (m * mixingTime P π δ) * distPairs P (mixingTime P π δ) := by
            have h := MarkovMixing.distPairs_submultiplicative P hP
              (m * mixingTime P π δ) (mixingTime P π δ)
            rwa [show m * mixingTime P π δ + mixingTime P π δ
              = (m + 1) * mixingTime P π δ by ring] at h
          calc distPairs P ((m + 1) * mixingTime P π δ)
              ≤ distPairs P (m * mixingTime P π δ) * distPairs P (mixingTime P π δ) := hstep
            _ ≤ (2 * δ) ^ m * (2 * δ) :=
                mul_le_mul ih hdbarT (hdbar_nonneg _) (by positivity)
            _ = (2 * δ) ^ (m + 1) := (pow_succ _ m).symm
    exact le_trans (MarkovMixing.dist_le_distPairs P hP π hπ _).1 (hpowk ℓ)
  refine ⟨key ε hε, ?_⟩
  -- the second inequality
  set L : ℝ := Real.logb 2 ε⁻¹ with hL
  have hLnonneg : 0 ≤ L := by
    rw [hL]
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_inv_comm₀ (by norm_num) hε]
    simpa using hε1
  set ℓ : ℕ := ⌈L⌉₊ with hℓ
  have hLle : L ≤ (ℓ : ℝ) := Nat.le_ceil L
  have hhalf : (1/2 : ℝ) ^ ℓ ≤ ε := by
    have h2 : (2:ℝ) ^ (L : ℝ) = ε⁻¹ := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    have h3 : (2:ℝ) ^ (L : ℝ) ≤ (2:ℝ) ^ ((ℓ : ℕ) : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hLle
    rw [Real.rpow_natCast] at h3
    rw [h2] at h3
    have h4 : (0:ℝ) < (2:ℝ) ^ ℓ := by positivity
    rw [div_pow, one_pow]
    rw [div_le_iff₀ h4]
    have := (inv_le_iff_one_le_mul₀ hε).mp h3
    nlinarith [h3, hε]
  have hmem : distStationary P π (ℓ * tMix P π) ≤ ε := by
    have h := key (1/4 : ℝ) (by norm_num) ℓ
    have heq : (2 * (1/4 : ℝ)) = 1/2 := by norm_num
    rw [heq] at h
    have htm : tMix P π = mixingTime P π (1/4) := rfl
    rw [htm]
    linarith [hhalf]
  exact Nat.sInf_le (by simpa using hmem)
