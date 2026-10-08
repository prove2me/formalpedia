-- Prove2me | solution 1 for KellyReversibility.Clustering.poisson_product_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:06:21.404983+00:00
-- url     : https://prove2.me/submissions/95e70765-f49f-4a03-9a62-ce378ef0c982

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Clustering_ClusteringRates

set_option autoImplicit false

namespace P9cd1c8ec
open KellyReversibility.Clustering

variable {R : Type*} [LinearOrder R]

lemma pw_nonneg (c : R → ℝ) (hc : ∀ r, 0 < c r) (m : R →₀ ℕ) : 0 ≤ productWeight c m := by
  unfold productWeight
  exact Finset.prod_nonneg fun r _ => by have := (hc r).le; positivity

lemma pw_eq (c : R → ℝ) (m : R →₀ ℕ) (F : Finset R) (h : m.support ⊆ F) :
    productWeight c m = ∏ r ∈ F, c r ^ m r / ((m r).factorial : ℝ) := by
  unfold productWeight
  apply Finset.prod_subset h
  intro r _ hr
  rw [Finsupp.notMem_support_iff.mp hr]
  simp

lemma box_sum (c : R → ℝ) (F : Finset R) (t : R → Finset ℕ) :
    ∑ p ∈ F.pi t, productWeight c (Finsupp.indicator F p) =
      ∏ r ∈ F, ∑ n ∈ t r, c r ^ n / (n.factorial : ℝ) := by
  rw [Finset.prod_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pw_eq c _ F (Finsupp.support_indicator_subset F p), ← Finset.prod_attach]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finsupp.indicator_of_mem x.2]

lemma partial_le (c : R → ℝ) (hc : ∀ r, 0 < c r) (hs : Summable c) (s : Finset (R →₀ ℕ)) :
    ∑ m ∈ s, productWeight c m ≤ Real.exp (∑' r, c r) := by
  set M : R →₀ ℕ := ∑ m ∈ s, m with hM
  set F := M.support with hF
  set t : R → Finset ℕ := fun r => Finset.range (M r + 1) with ht
  have hsub : s ⊆ (F.pi t).map ⟨fun p => Finsupp.indicator F p, Finsupp.indicator_injective F⟩ := by
    intro m hm
    have hle : m ≤ M := Finset.single_le_sum (f := fun x => x) (fun _ _ => zero_le) hm
    rw [Finset.mem_map]
    refine ⟨fun i _ => m i, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro i _
      simp only [t, Finset.mem_range]
      exact Nat.lt_succ_of_le (hle i)
    · ext i
      by_cases hi : i ∈ F
      · simp [Finsupp.indicator_of_mem hi]
      · simp only [Function.Embedding.coeFn_mk]
        rw [Finsupp.indicator_of_notMem hi]
        have h0 : M i = 0 := Finsupp.notMem_support_iff.mp hi
        have := hle i
        omega
  calc ∑ m ∈ s, productWeight c m
      ≤ ∑ m ∈ (F.pi t).map ⟨fun p => Finsupp.indicator F p, Finsupp.indicator_injective F⟩,
          productWeight c m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => pw_nonneg c hc m)
    _ = ∏ r ∈ F, ∑ n ∈ t r, c r ^ n / (n.factorial : ℝ) := by
        rw [Finset.sum_map]; exact box_sum c F t
    _ ≤ ∏ r ∈ F, Real.exp (c r) :=
        Finset.prod_le_prod (fun r _ => Finset.sum_nonneg fun n _ => by
          have := (hc r).le; positivity) (fun r _ => Real.sum_le_exp_of_nonneg (hc r).le _)
    _ = Real.exp (∑ r ∈ F, c r) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' r, c r) := Real.exp_le_exp.mpr (hs.sum_le_tsum F (fun i _ => (hc i).le))

lemma hasSum_pw (c : R → ℝ) (hc : ∀ r, 0 < c r) (hs : Summable c) :
    HasSum (productWeight c) (Real.exp (∑' r, c r)) := by
  have hS : Summable (productWeight c) :=
    summable_of_sum_le (fun m => pw_nonneg c hc m) (partial_le c hc hs)
  have hup : ∑' m, productWeight c m ≤ Real.exp (∑' r, c r) :=
    Real.tsum_le_of_sum_le (fun m => pw_nonneg c hc m) (partial_le c hc hs)
  have hF : ∀ F : Finset R, Real.exp (∑ r ∈ F, c r) ≤ ∑' m, productWeight c m := by
    intro F
    have hbox : ∀ N : ℕ, ∏ r ∈ F, ∑ n ∈ Finset.range N, c r ^ n / (n.factorial : ℝ) ≤
        ∑' m, productWeight c m := by
      intro N
      rw [← box_sum c F (fun _ => Finset.range N)]
      have h := hS.sum_le_tsum ((F.pi (fun _ => Finset.range N)).map
          ⟨fun p => Finsupp.indicator F p, Finsupp.indicator_injective F⟩)
          (fun m _ => pw_nonneg c hc m)
      rw [Finset.sum_map] at h
      exact h
    have hlim : Filter.Tendsto
        (fun N : ℕ => ∏ r ∈ F, ∑ n ∈ Finset.range N, c r ^ n / (n.factorial : ℝ))
        Filter.atTop (nhds (∏ r ∈ F, Real.exp (c r))) := by
      apply tendsto_finsetProd
      intro r _
      have := (NormedSpace.expSeries_div_hasSum_exp (c r)).tendsto_sum_nat
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this
    rw [Real.exp_sum]
    exact le_of_tendsto' hlim hbox
  have hlo : Real.exp (∑' r, c r) ≤ ∑' m, productWeight c m :=
    le_of_tendsto' ((Real.continuous_exp.tendsto _).comp hs.hasSum) hF
  rw [← le_antisymm hup hlo]
  exact hS.hasSum

lemma ocp_eq (c : R → ℝ) (hs : Summable c) (m : R →₀ ℕ) :
    openClusterPi c m = Real.exp (-∑' r, c r) * productWeight c m := by
  have h1 : HasProd (fun r => Real.exp (-c r)) (Real.exp (-∑' r, c r)) := by
    have := hs.hasSum.neg.rexp
    simpa [Function.comp_def] using this
  have h2 : HasProd (fun r => c r ^ m r / ((m r).factorial : ℝ)) (productWeight c m) := by
    unfold productWeight
    exact hasProd_prod_of_ne_finset_one (fun r hr => by
      rw [Finsupp.notMem_support_iff.mp hr]; simp)
  unfold openClusterPi
  have := (h1.mul h2).tprod_eq
  simp_rw [mul_div_assoc]
  exact this

lemma main {R : Type*} [LinearOrder R] [Countable R]
    (c : R → ℝ) (hc : ∀ r, 0 < c r) :
    (Summable c ↔ Summable (productWeight c)) ∧
      (Summable c → HasSum (openClusterPi c) 1) := by
  refine ⟨⟨fun h => (hasSum_pw c hc h).summable, fun h => ?_⟩, fun h => ?_⟩
  · have := h.comp_injective (Finsupp.single_left_injective (one_ne_zero : (1:ℕ) ≠ 0))
    have e : (productWeight c ∘ fun a => Finsupp.single a 1) = c := by
      funext r
      simp [productWeight]
    rw [e] at this
    exact this
  · have := (hasSum_pw c hc h).mul_left (Real.exp (-∑' r, c r))
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    have e : openClusterPi c = fun i => Real.exp (-∑' r, c r) * productWeight c i :=
      funext (ocp_eq c h)
    rw [e]
    exact this

end P9cd1c8ec

open KellyStochasticNetworks in
open KellyReversibility.Clustering in
theorem solution {R : Type*} [LinearOrder R] [Countable R]
    (c : R → ℝ) (hc : ∀ r, 0 < c r) :
    (Summable c ↔ Summable (productWeight c)) ∧
      (Summable c → HasSum (openClusterPi c) 1) := by
  exact P9cd1c8ec.main c hc
