-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.gaussian_decision_to_dgs
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:12:29.127205+00:00
-- url     : https://prove2.me/submissions/0cc3f1b9-50a3-44a4-8556-e7ff91cb42eb

import Theorems.Thm_Integration9_9_LoadedBatch_Schedule_uniform_gaussian_search
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_search_to_dgs

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open QAlgorithms.Complexity InfoLossLAR.WorstCase AFT
open Integration9_9.LoadedBatch.Schedule Integration9_9.LARPlatformEncoding
open InfoLossLAR.WorstCase.RegevSketch InfoLossLAR.WorstCase.RegevSearch

theorem source_eq (dimension sec : ℕ) :
    (fixedGaussianSource dimension sec).weight = chiG (famq sec) dimension (famσ sec) := by
  funext e
  have hsigma : (0 : ℝ) < famσ sec := by
    have hnat : 0 < famσ sec := by change 0 < sec + 2; omega
    exact_mod_cast hnat
  change (GaussianSource.residueGaussian dimension (famq sec) (famσ sec) hsigma).weight e = _
  exact Integration.residueGaussian_weight_eq_chiG (famq sec) dimension (famσ sec) hsigma e

theorem search_from_adv (D : Family) (hD : IsQPT D)
    (t : ℕ → ℕ) (ht : ∀ n, 1 ≤ t n) (htpoly : PolyBoundedFn t)
    (b : ℕ) (S : Set ℕ)
    (hadv : ∃ n₀ : ℕ, ∀ n ∈ S, n₀ ≤ n → (n : ℝ)^(-(b : ℝ)) ≤
      advLWE D n (famPP n) (famq n) (famN n) (famd n) (t n)
        (chiG (famq n) (famd n) (famσ n))) :
    ∃ A : MFamily, IsMQPT A ∧ ∃ samples : Polynomial ℕ, ∃ cutoff : ℕ, SearchOn A samples cutoff S := by
  obtain ⟨n₀, hn₀⟩ := hadv
  obtain ⟨A,hA,samples,cutoff,hsearch⟩ := uniform_gaussian_search D hD t ht htpoly b []
  refine ⟨A,hA,samples,max n₀ cutoff,?_⟩
  intro n hn hlarge secret
  have hd : 0 < famd n := by
    have hL : 0 < famL n := by unfold famL; omega
    have hp : 0 < 2 * famL n ^ 128 := Nat.mul_pos (by norm_num) (pow_pos hL _)
    change 0 < famq n * famL n ^ 96 + 2 * famL n ^ 128
    exact Nat.add_pos_right _ hp
  have ha : (n : ℝ)^(-(b : ℝ)) ≤ advLWE D n (searchParameters n (famd n) (famσ n))
       (famq n) (famN n) (famd n) (t n) (fixedGaussianSource (famd n) n).weight := by
    simpa only [searchParameters, famPP, source_eq] using hn₀ n hn ((Nat.le_max_left n₀ cutoff).trans hlarge)
  simpa only [searchParameters, famPP] using
    hsearch n ((Nat.le_max_right n₀ cutoff).trans hlarge) (famd n) (famσ n) hd secret ha

theorem solution :
  ∀ D : Family, IsQPT D → ∀ t : ℕ → ℕ, (∀ n,1 ≤ t n) → PolyBoundedFn t →
    ∀ b : ℕ, ∀ S : Set ℕ, S.Infinite → (∀ n ∈ S,1 ≤ n) →
      (∃ n₀ : ℕ, ∀ n ∈ S, n₀ ≤ n → (n : ℝ)^(-(b : ℝ)) ≤
        advLWE D n (famPP n) (famq n) (famN n) (famd n) (t n)
          (chiG (famq n) (famd n) (famσ n))) →
      ∃ G : MFamily, IsMQPT G ∧ ∃ error : ℕ → ℝ, InfoLossLAR.WorstCase.Negligible error ∧
        ∃ cutoff : ℕ, ∀ n ∈ S, cutoff ≤ n → DGSAt G n (error n) := by
  intro D hD t ht htpoly b S hS hpositive hadv
  obtain ⟨A,hA,samples,cutoff,hsearch⟩ := search_from_adv D hD t ht htpoly b S hadv
  exact InfoLossLAR.WorstCase.RegevSearch.search_to_dgs S hS hpositive A hA samples cutoff hsearch
