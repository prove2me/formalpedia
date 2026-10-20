-- Prove2me | solution 1 for OAI.LipschitzCounterexample.GraphObstruction.no_lower_of_coordinate_null
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:49:08.436312+00:00
-- url     : https://prove2.me/submissions/1d52a837-b621-4176-a38a-fc9bbbc4d6eb

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.GraphObstruction
universe uH uA uB
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
open NullSequences
theorem h50_step (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0)) (n : ℕ) :
    ∃ x : RealL2, ∃ N K : ℕ, ‖x‖^2 = n ∧ (∀ i, ‖T x i‖ ≤ ‖T‖ + 1 - (1/2:ℝ)^n) ∧
      (∀ i, N ≤ i → ‖T x i‖ ≤ (1/2:ℝ)^(n+1)) ∧ (∀ k, K ≤ k → x k = 0) := by
  induction n with
  | zero =>
    refine ⟨0, 0, 0, by simp, fun i => ?_, fun i _ => ?_, fun k _ => rfl⟩
    · have := norm_nonneg T
      simp
      linarith
    · simp
  | succ n ih =>
    obtain ⟨x, N, K, hx, hb, ht, hs⟩ := ih
    have hη : (0:ℝ) < (1/2)^(n+1) := by positivity
    have hev : ∀ᶠ k in atTop, K ≤ k ∧
        ∀ i ∈ Finset.range N, ‖T (unitVector k) i‖ < (1/2:ℝ)^(n+1) := by
      refine (eventually_ge_atTop K).and ?_
      rw [Filter.eventually_all_finset]
      intro i _
      have h0 := (hcoord i).norm
      rw [norm_zero] at h0
      exact h0.eventually (gt_mem_nhds hη)
    obtain ⟨k, hkK, hk⟩ := hev.exists
    have hnorm_e : ∀ i, ‖T (unitVector k) i‖ ≤ ‖T‖ := fun i =>
      (NullSequences.norm_apply_le _ i).trans ((T.le_opNorm _).trans (by simp))
    have htail := (NullSequences.tendsto_zero (T (x + unitVector k))).norm
    rw [norm_zero] at htail
    obtain ⟨N', hN'⟩ := eventually_atTop.mp
      (htail.eventually (gt_mem_nhds (by positivity : (0:ℝ) < (1/2)^(n+1+1))))
    refine ⟨x + unitVector k, N', max K (k+1), ?_, ?_, fun i hi => (hN' i hi).le, ?_⟩
    · rw [norm_add_sq_real, hx]
      have hin : inner ℝ x (unitVector k) = 0 := by
        simp [unitVector, lp.inner_single_right, hs k hkK]
      rw [hin]
      simp
    · intro i
      have hsplit : T (x + unitVector k) i = T x i + T (unitVector k) i := by
        rw [map_add]; rfl
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have hp : (1/2:ℝ)^(n+1) = (1/2)^n / 2 := by rw [pow_succ]; ring
      have hp1 : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      by_cases hi : i < N
      · have h1 := hk i (Finset.mem_range.mpr hi)
        have h2 := hb i
        linarith
      · have h1 := ht i (by omega)
        have h2 := hnorm_e i
        linarith
    · intro j hj
      have hjk : j ≠ k := by have := le_of_max_le_right hj; omega
      rw [lp.coeFn_add, Pi.add_apply, hs j (le_of_max_le_left hj), unitVector_coord, if_neg hjk]
      simp

theorem solution (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0))
    (b : ℝ) (hb : 0 < b) (hlower : ∀ x, b * ‖x‖ ≤ ‖T x‖) : False := by
  have hc := norm_nonneg T
  obtain ⟨n, hn⟩ := exists_nat_gt ((‖T‖ + 1)^2 / b^2)
  obtain ⟨x, N, K, hx, hbd, -, -⟩ := h50_step T hcoord n
  have h1 : ‖T x‖ ≤ ‖T‖ + 1 := by
    rw [NullSequences.norm_le (by positivity)]
    intro i
    have := hbd i
    have : (0:ℝ) < (1/2)^n := by positivity
    linarith
  have h4 : b * ‖x‖ ≤ ‖T‖ + 1 := (hlower x).trans h1
  have h5 := mul_self_le_mul_self (by positivity) h4
  rw [div_lt_iff₀ (by positivity)] at hn
  nlinarith

