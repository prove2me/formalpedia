-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dgs_ideal_short_spanning_pool
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:04:02.922223+00:00
-- url     : https://prove2.me/submissions/bde9b294-e1a4-417c-8d22-6a98f474cc10

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_pool_gaussian_tail
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_pool_rank_failure
import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

open Filter
open scoped Topology

namespace InfoLossLAR.WorstCase.RegevSketch

private theorem sameIte (p : Prop) (a b : Decidable p) :
    @ite ℝ p a 1 0 = @ite ℝ p b 1 0 :=
  congrArg (fun d => @ite ℝ p d 1 0) (Subsingleton.elim a b)

theorem _root_.solution :    ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 ≤ n →
      ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 →
      ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
        (7 : ℝ)/8 ≤ ∑' pool : Fin (16 * (n + 1)^2) → Fin n → ℤ,
          (∏ i, coefficientMass B r (pool i)) *
          (if ∃ pick : Fin n → Fin (16 * (n + 1)^2),
            LinearIndependent ℝ (fun i => latVec B (pool (pick i))) ∧
              ∀ i, ‖latVec B (pool (pick i))‖ ≤ 2 * Real.sqrt n * r
           then 1 else 0) := by
  classical
  obtain ⟨Nt, ht⟩ := dgs_pool_gaussian_tail
  obtain ⟨Ns, hs⟩ := dgs_pool_rank_failure
  have hq : Tendsto (fun n : ℕ => (n : ℝ)^2 * (1/4 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num) (by norm_num)
  have hq' : Tendsto (fun n : ℕ => 64 * ((n : ℝ)^2 * (1/4 : ℝ)^n)) atTop (𝓝 0) := by
    simpa using hq.const_mul 64
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp
    ((hq'.add hp).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1/8)))
  refine ⟨max (max Nt Ns) Nc, ?_⟩
  intro n hn hn1 B hB r hr hthreshold
  obtain ⟨hLaw, hTail⟩ := ht n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)) hn1 B hB r hr hthreshold
  have hRank := hs n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)) hn1 B hB r hr hthreshold
  let I := Fin (16 * (n + 1)^2)
  let Ω := I → Fin n → ℤ
  let mass (pool : Ω) : ℝ := ∏ i, coefficientMass B r (pool i)
  let tail (pool : Ω) : Prop := ∃ i, 2 * Real.sqrt n * r < ‖latVec B (pool i)‖
  let rankFail (pool : Ω) : Prop := ¬ ∃ pick : Fin n → I,
    LinearIndependent ℝ (fun i => latVec B (pool (pick i)))
  let good (pool : Ω) : Prop := ∃ pick : Fin n → I,
    LinearIndependent ℝ (fun i => latVec B (pool (pick i))) ∧
      ∀ i, ‖latVec B (pool (pick i))‖ ≤ 2 * Real.sqrt n * r
  let event (p : Ω → Prop) (pool : Ω) : ℝ := mass pool * (if p pool then 1 else 0)
  have hmass (pool : Ω) : 0 ≤ mass pool := by
    apply Finset.prod_nonneg
    intro i _
    unfold coefficientMass
    apply div_nonneg
    · unfold rhoInt RegevLWE.GaussConv.rho
      positivity
    · apply tsum_nonneg
      intro z
      unfold rhoInt RegevLWE.GaussConv.rho
      positivity
  have hEventSummable (p : Ω → Prop) : Summable (event p) :=
    hLaw.summable.of_nonneg_of_le
      (fun pool => by by_cases h : p pool <;> simp only [event, h, if_true, if_false, mul_one, mul_zero, hmass, le_refl])
      (fun pool => by change event p pool ≤ mass pool; by_cases h : p pool <;> simp only [event, h, if_true, if_false, mul_one, mul_zero, hmass, le_refl])
  have hPoint (pool : Ω) : mass pool ≤ event good pool + event tail pool + event rankFail pool := by
    by_cases ht' : tail pool
    · by_cases hg : good pool <;> by_cases hf : rankFail pool <;> simp [event, ht', hg, hf] <;> linarith [hmass pool]
    · by_cases hf : rankFail pool
      · by_cases hg : good pool <;> simp [event, ht', hg, hf] <;> linarith [hmass pool]
      · have hex : ∃ pick : Fin n → I, LinearIndependent ℝ (fun i => latVec B (pool (pick i))) := by simpa [rankFail] using hf
        obtain ⟨pick, hi⟩ := hex
        have hg : good pool := ⟨pick, hi, fun i => le_of_not_gt (fun hh => ht' ⟨pick i, hh⟩)⟩
        simp [event, hg, ht', hf]
  have hsum := Summable.tsum_le_tsum hPoint hLaw.summable
    (((hEventSummable good).add (hEventSummable tail)).add (hEventSummable rankFail))
  rw [hLaw.tsum_eq, ((hEventSummable good).add (hEventSummable tail)).tsum_add (hEventSummable rankFail),
    (hEventSummable good).tsum_add (hEventSummable tail)] at hsum
  have hTail' : ∑' pool, event tail pool ≤ (16 * ((n : ℝ) + 1)^2) * (1/4 : ℝ)^n := by
    convert hTail using 1
    apply tsum_congr
    intro pool
    exact congrArg (fun x : ℝ => mass pool * x) (sameIte _ _ _)
  have hRank' : ∑' pool, event rankFail pool ≤ (1/2 : ℝ)^n := by
    convert hRank using 1
    apply tsum_congr
    intro pool
    exact congrArg (fun x : ℝ => mass pool * x) (sameIte _ _ _)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcoeff : 16 * ((n : ℝ) + 1)^2 ≤ 64 * (n : ℝ)^2 := by
    have hh : ((n : ℝ) + 1)^2 ≤ (2 * (n : ℝ))^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ (1/4 : ℝ)^n)
  have hsmall := hc n (le_trans (le_max_right _ _) hn)
  change 64 * ((n : ℝ)^2 * (1/4 : ℝ)^n) + (1/2 : ℝ)^n < (1/8 : ℝ) at hsmall
  rw [← mul_assoc] at hsmall
  have hgood : (7 : ℝ)/8 ≤ ∑' pool, event good pool := by linarith
  convert hgood using 1
  apply tsum_congr
  intro pool
  exact congrArg (fun x : ℝ => mass pool * x) (sameIte _ _ _)

end InfoLossLAR.WorstCase.RegevSketch
