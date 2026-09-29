-- Prove2me | solution 1 for MetricTSP.three_paths_cert_objective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T20:45:28.312858+00:00
-- url     : https://prove2.me/submissions/45cc491b-9681-403e-ac9d-a01cf3bc3c3b

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths
import Theorems.Thm_MetricTSP_three_paths_cert_feasible

namespace MetricTSP

open Finset

variable {k : ℕ}

lemma tpSpec'' (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    (tpPath k v = 3 ∧ (tpPos k v = 0 ∨ tpPos k v = k+1))
    ∨ (tpPath k v < 3 ∧ 1 ≤ tpPos k v ∧ tpPos k v ≤ k) := by
  have hv := v.isLt
  unfold tpPath tpPos
  by_cases h : v.val = 0 ∨ v.val = 3*k+1
  · rw [if_pos h]
    left
    rcases h with h | h <;> rw [h] <;> simp <;> omega
  · rw [if_neg h]
    right
    push_neg at h
    have hmod : (v.val - 1) % k < k := Nat.mod_lt _ (by omega)
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    rw [if_neg h.1, if_neg h.2]
    omega

lemma tpCoord_inj' (hk : 1 ≤ k) (u v : Fin (3*k+2))
    (hp : tpPath k u = tpPath k v) (hq : tpPos k u = tpPos k v) : u = v := by
  have hu := u.isLt
  have hv := v.isLt
  apply Fin.ext
  unfold tpPath at hp
  unfold tpPos at hq
  by_cases h1 : u.val = 0 ∨ u.val = 3*k+1 <;> by_cases h2 : v.val = 0 ∨ v.val = 3*k+1
  · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      rw [h1, h2] at hq
      rw [if_pos rfl] at hq
      rw [if_neg (by omega), if_pos rfl] at hq
      omega
    · exfalso
      rw [h1, h2] at hq
      rw [if_neg (by omega), if_pos rfl, if_pos rfl] at hq
      omega
    · rw [h1, h2]
  · rw [if_pos h1, if_neg h2] at hp
    push_neg at h2
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  · rw [if_neg h1, if_pos h2] at hp
    push_neg at h1
    have hdivlt : (u.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  · push_neg at h1 h2
    rw [if_neg h1.1, if_neg h1.2] at hq
    rw [if_neg h2.1, if_neg h2.2] at hq
    rw [if_neg (not_or.mpr h1), if_neg (not_or.mpr h2)] at hp
    have e1 : k * ((u.val - 1) / k) + (u.val - 1) % k = u.val - 1 := Nat.div_add_mod _ k
    have e2 : k * ((v.val - 1) / k) + (v.val - 1) % k = v.val - 1 := Nat.div_add_mod _ k
    rw [hp] at e1
    have e3 : (u.val - 1) % k = (v.val - 1) % k := by omega
    rw [e3] at e1
    omega

/-- Pointwise: cost times certificate equals the certificate plus a `1/6` bonus on the
distance-two triangle pairs. -/
lemma cost_mul_cert (hk : 2 ≤ k) (u v : Fin (3*k+2)) :
    tpCost k u v * tpCert k u v = tpCert k u v +
      (if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
          tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/6 : ℝ) else 0) := by
  have hk1 : 1 ≤ k := by omega
  unfold tpCost tpCert
  by_cases c1 : tpPath k u = tpPath k v ∧ tpPath k u ≠ 3 ∧
      Nat.dist (tpPos k u) (tpPos k v) = 1
  · rw [if_pos c1, if_neg (by omega)]
    have hd : tpDist k u v = 1 := by
      unfold tpDist
      rw [if_pos (Or.inr (Or.inr c1.1))]
      exact c1.2.2
    rw [hd]
    norm_num
  · rw [if_neg c1]
    by_cases c2 : ((tpPath k u = 3 ∧ tpPath k v ≠ 3) ∨ (tpPath k u ≠ 3 ∧ tpPath k v = 3)) ∧
        Nat.dist (tpPos k u) (tpPos k v) = 1
    · rw [if_pos c2, if_neg (by omega)]
      have hd : tpDist k u v = 1 := by
        unfold tpDist
        rw [if_pos (by omega)]
        exact c2.2
      rw [hd]
      norm_num
    · rw [if_neg c2]
      by_cases c3 : tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
          tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k)
      · rw [if_pos c3]
        have hd : tpDist k u v = 2 := by
          unfold tpDist
          rw [if_neg (by omega)]
          omega
        rw [hd]
        norm_num
      · rw [if_neg c3]
        simp

/-- At most six cities sit at positions `1` or `k` of the three paths. -/
lemma tri_carrier_card (hk : 2 ≤ k) :
    ((univ : Finset (Fin (3*k+2))).filter
      (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k))).card ≤ 6 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hinj : ∀ u ∈ (univ : Finset (Fin (3*k+2))).filter
      (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k)),
      ∀ v ∈ (univ : Finset (Fin (3*k+2))).filter
      (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k)),
      (fun u => (tpPath k u, tpPos k u)) u = (fun u => (tpPath k u, tpPos k u)) v → u = v := by
    intro u _ v _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact tpCoord_inj' hk1 u v h1 h2
  have hmap : ∀ u ∈ (univ : Finset (Fin (3*k+2))).filter
      (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k)),
      (fun u => (tpPath k u, tpPos k u)) u ∈
        (Finset.range 3) ×ˢ ({1, k} : Finset ℕ) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_product]
    rcases tpSpec'' hk1 u with ⟨h3, _⟩ | ⟨hlt, _, _⟩
    · exact absurd h3 hu.2.1
    · refine ⟨Finset.mem_range.mpr hlt, ?_⟩
      rcases hu.2.2 with h | h <;> simp [h]
  calc ((univ : Finset (Fin (3*k+2))).filter
      (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k))).card
      ≤ ((Finset.range 3) ×ˢ ({1, k} : Finset ℕ)).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ ≤ 6 := by
      rw [Finset.card_product, Finset.card_range]
      have := Finset.card_insert_le 1 ({k} : Finset ℕ)
      have h1 := Finset.card_singleton k
      omega

/-- Each city has at most two triangle partners. -/
lemma tri_partners_card (hk : 2 ≤ k) (u : Fin (3*k+2)) :
    ((univ : Finset (Fin (3*k+2))).filter
      (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
        tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k))).card ≤ 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hinj : ∀ a ∈ (univ : Finset (Fin (3*k+2))).filter
      (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
        tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k)),
      ∀ b ∈ (univ : Finset (Fin (3*k+2))).filter
      (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
        tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k)),
      (fun v => tpPath k v) a = (fun v => tpPath k v) b → a = b := by
    intro a ha b hb h
    rw [Finset.mem_filter] at ha hb
    exact tpCoord_inj' hk1 a b h (ha.2.2.2.2.1.symm.trans hb.2.2.2.2.1)
  have hmap : ∀ a ∈ (univ : Finset (Fin (3*k+2))).filter
      (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
        tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k)),
      (fun v => tpPath k v) a ∈ (Finset.range 3).erase (tpPath k u) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_erase]
    refine ⟨fun h => ha.2.2.2.1 h.symm, ?_⟩
    rcases tpSpec'' hk1 a with ⟨h3, _⟩ | ⟨hlt, _, _⟩
    · exact absurd h3 ha.2.2.1
    · exact Finset.mem_range.mpr hlt
  by_cases hu3 : tpPath k u = 3
  · have hemp : ((univ : Finset (Fin (3*k+2))).filter
        (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
          tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _
      intro hc
      exact hc.1 hu3
    omega
  · have hmem : tpPath k u ∈ Finset.range 3 := by
      rcases tpSpec'' hk1 u with ⟨h3, _⟩ | ⟨hlt, _, _⟩
      · exact absurd h3 hu3
      · exact Finset.mem_range.mpr hlt
    calc _ ≤ ((Finset.range 3).erase (tpPath k u)).card :=
          Finset.card_le_card_of_injOn _ hmap hinj
      _ = 2 := by
          rw [Finset.card_erase_of_mem hmem, Finset.card_range]

theorem three_paths_cert_objective_thm (k : ℕ) (hk : 2 ≤ k) :
    (1 / 2) * ∑ u, ∑ v, tpCost k u v * tpCert k u v ≤ 3 * k + 3 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hx := three_paths_cert_feasible k hk
  have hxdeg : ∀ v, ∑ u, tpCert k v u = 2 := hx.2.2.2.2.1
  have htotal : ∑ u : Fin (3*k+2), ∑ v : Fin (3*k+2), tpCert k u v = 2 * (3*k+2) := by
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ univ) => hxdeg u)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hpoint : ∑ u : Fin (3*k+2), ∑ v : Fin (3*k+2), tpCost k u v * tpCert k u v
      = 2 * (3*k+2) + ∑ u : Fin (3*k+2), ∑ v : Fin (3*k+2),
        (if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
          tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/6 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ univ) =>
      Finset.sum_congr rfl (fun v (_ : v ∈ univ) => cost_mul_cert hk u v))]
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ univ) => Finset.sum_add_distrib),
      Finset.sum_add_distrib, htotal]
  have htri : ∑ u : Fin (3*k+2), ∑ v : Fin (3*k+2),
      (if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
        tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/6 : ℝ) else 0)
      ≤ 2 := by
    have hinner : ∀ u : Fin (3*k+2), ∑ v : Fin (3*k+2),
        (if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
          tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/6 : ℝ) else 0)
        ≤ (if tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/3 : ℝ) else 0) := by
      intro u
      by_cases hu : tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k)
      · rw [if_pos hu]
        rw [← Finset.sum_filter]
        have hcard := tri_partners_card hk u
        calc ∑ v ∈ (univ : Finset (Fin (3*k+2))).filter
              (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
                tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k)), (1/6 : ℝ)
            = ((univ : Finset (Fin (3*k+2))).filter
              (fun v => tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
                tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k))).card * (1/6 : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 2 * (1/6 : ℝ) := by
              apply mul_le_mul_of_nonneg_right _ (by norm_num)
              exact_mod_cast hcard
          _ = 1/3 := by norm_num
      · rw [if_neg hu]
        apply Finset.sum_nonpos
        intro v _
        split_ifs with hc
        · exfalso
          apply hu
          exact ⟨hc.1, hc.2.2.2.2⟩
        · exact le_refl 0
    calc ∑ u : Fin (3*k+2), ∑ v : Fin (3*k+2),
        (if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
          tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/6 : ℝ) else 0)
        ≤ ∑ u : Fin (3*k+2),
          (if tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/3 : ℝ) else 0) :=
          Finset.sum_le_sum (fun u _ => hinner u)
      _ = ∑ u ∈ (univ : Finset (Fin (3*k+2))).filter
            (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k)), (1/3 : ℝ) := by
          rw [Finset.sum_filter]
      _ = ((univ : Finset (Fin (3*k+2))).filter
            (fun u => tpPath k u ≠ 3 ∧ (tpPos k u = 1 ∨ tpPos k u = k))).card * (1/3 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * (1/3 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact_mod_cast tri_carrier_card hk
      _ = 2 := by norm_num
  rw [hpoint] at *
  have : (1/2 : ℝ) * (2 * (3*k+2) + ∑ u : Fin (3*k+2), ∑ v : Fin (3*k+2),
      (if tpPath k u ≠ 3 ∧ tpPath k v ≠ 3 ∧ tpPath k u ≠ tpPath k v ∧
        tpPos k u = tpPos k v ∧ (tpPos k u = 1 ∨ tpPos k u = k) then (1/6 : ℝ) else 0))
      ≤ (1/2) * (2 * (3*k+2) + 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith
  calc (1/2 : ℝ) * (2 * (3*k+2) + _) ≤ (1/2) * (2 * (3*k+2) + 2) := this
    _ ≤ 3 * k + 3 := by push_cast; ring_nf; linarith

end MetricTSP

open MetricTSP

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    (1 / 2) * ∑ u, ∑ v, tpCost k u v * tpCert k u v ≤ 3 * k + 3 :=
  MetricTSP.three_paths_cert_objective_thm k hk
