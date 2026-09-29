-- Prove2me | solution 1 for KServer.competitive_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T01:10:19.291427+00:00
-- url     : https://prove2.me/submissions/62063f8f-0a73-4dee-893b-ee667ecd0d2c

import Mathlib
import Definitions.Def_KServer_model
import Theorems.Thm_KServer_exists_lazy_algorithm
import Theorems.Thm_KServer_exists_cruel_sequence
import Theorems.Thm_KServer_offline_avg_bound

open KServer

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (hM : ∃ P : Finset M, P.card = k + 1)
    (A : OnlineAlgorithm k M) (c : ℝ) (hc : IsCompetitive A c) :
    (k : ℝ) ≤ c := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨P, hP⟩ := hM
  obtain ⟨a, ha⟩ := hc
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- Step 1: a positive separation `δ` of the `k+1` points of `P`.
  have hcard : 1 < P.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  set Q : Finset (M × M) := (P ×ˢ P).filter (fun p => p.1 ≠ p.2) with hQdef
  have hmemQ : ∀ p q : M, p ∈ P → q ∈ P → p ≠ q → (p, q) ∈ Q := by
    intro p q hp hq hpq
    simp [hQdef, Finset.mem_filter, Finset.mem_product, hp, hq, hpq]
  obtain ⟨p0, hp0Q, hp0min⟩ :=
    Q.exists_min_image (fun p => dist p.1 p.2) ⟨(x, y), hmemQ x y hx hy hxy⟩
  have hp0 : p0.1 ≠ p0.2 := (Finset.mem_filter.mp hp0Q).2
  set δ : ℝ := dist p0.1 p0.2 with hδdef
  have hδ0 : 0 < δ := dist_pos.mpr hp0
  have hδ : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q := fun p hp q hq hpq =>
    hp0min (p, q) (hmemQ p q hp hq hpq)
  -- Step 2: the offline optimum is nonnegative.
  have hopt : ∀ σ : List M, 0 ≤ offlineCost (A.conf []) σ := by
    intro σ
    apply Real.sInf_nonneg
    rintro z ⟨S, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => dist_nonneg
  -- Step 3: along a request list of pairwise-distinct consecutive points of `P`,
  -- the total consecutive distance is at least `(length - 1) * δ`.
  have hconsec_lb : ∀ σ : List M, (∀ r ∈ σ, r ∈ P) → (∀ p ∈ σ.zip σ.tail, p.1 ≠ p.2) →
      ((σ.length : ℝ) - 1) * δ ≤ ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum := by
    intro σ hmem hne
    have hstep : ((σ.zip σ.tail).map (fun _ => δ)).sum
        ≤ ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum := by
      apply List.sum_le_sum
      rintro ⟨u, v⟩ hp
      obtain ⟨hu, hv⟩ := List.of_mem_zip hp
      exact hδ u (hmem u hu) v (hmem v (List.tail_subset _ hv)) (hne (u, v) hp)
    have hconst : ((σ.zip σ.tail).map (fun _ => δ)).sum
        = ((σ.length - 1 : ℕ) : ℝ) * δ := by
      simp [List.map_const', List.sum_replicate, List.length_zip, List.length_tail,
        nsmul_eq_mul]
    have hcast : ((σ.length : ℝ) - 1) ≤ ((σ.length - 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos σ.length with h | h
      · rw [h]; norm_num
      · rw [Nat.cast_sub h]; norm_num
    calc ((σ.length : ℝ) - 1) * δ ≤ ((σ.length - 1 : ℕ) : ℝ) * δ :=
          mul_le_mul_of_nonneg_right hcast hδ0.le
      _ = ((σ.zip σ.tail).map (fun _ => δ)).sum := hconst.symm
      _ ≤ _ := hstep
  -- Step 4: the three child lemmas.
  obtain ⟨B, hB0, hBle, hBlazy⟩ := exists_lazy_algorithm k M A
  obtain ⟨E, hE⟩ := exists_cruel_sequence k M P hP B hBlazy
  obtain ⟨D, hD⟩ := offline_avg_bound k hk M P hP (A.conf [])
  -- Step 5: a uniform bound `K` on the online cost over the whole cruel family.
  set c' : ℝ := max c 0 with hc'def
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hcc' : c ≤ c' := le_max_left _ _
  have hc'k : c' < (k : ℝ) := max_lt hlt hk0
  have hden : 0 < (k : ℝ) - c' := by linarith
  set K : ℝ := (c' * (E + D) + (k : ℝ) * a) / ((k : ℝ) - c') with hKdef
  have key : ∀ n : ℕ, ((n : ℝ) - 1) * δ - E ≤ K := by
    intro n
    obtain ⟨σ, hlen, hmem, hne, hcost⟩ := hE n
    subst hlen
    set o : ℝ := offlineCost (A.conf []) σ with hodef
    set t : ℝ := A.cost σ with htdef
    set S : ℝ := ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum with hSdef
    have h3 : S ≤ t + E := le_trans hcost (by linarith [hBle σ])
    have h5 : (k : ℝ) * o ≤ t + E + D := le_trans (hD σ hmem) (by linarith)
    have h8 : t ≤ c' * o + a := by
      have := mul_le_mul_of_nonneg_right hcc' (hopt σ)
      linarith [ha σ]
    have h9 : c' * ((k : ℝ) * o) ≤ c' * (t + E + D) := mul_le_mul_of_nonneg_left h5 hc'0
    have hkt : (k : ℝ) * t ≤ (k : ℝ) * (c' * o + a) := mul_le_mul_of_nonneg_left h8 hk0.le
    have hring : (k : ℝ) * (c' * o + a) = c' * ((k : ℝ) * o) + (k : ℝ) * a := by ring
    have h11 : ((k : ℝ) - c') * t ≤ c' * (E + D) + (k : ℝ) * a := by nlinarith
    have h12 : t ≤ K := by rw [hKdef, le_div_iff₀ hden]; linarith
    have h14 : ((σ.length : ℝ) - 1) * δ ≤ S := hconsec_lb σ hmem hne
    linarith
  -- Step 6: the cruel family forces the online cost to infinity — contradiction.
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + E) / δ + 1)
  have h1 : (K + E) / δ < (n : ℝ) - 1 := by linarith
  rw [div_lt_iff₀ hδ0] at h1
  linarith [key n]
