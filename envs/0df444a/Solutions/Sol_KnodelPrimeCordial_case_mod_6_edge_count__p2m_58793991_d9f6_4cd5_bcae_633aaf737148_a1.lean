-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_edge_count__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:12:51.561005+00:00
-- url     : https://prove2.me/submissions/38f9ac1b-58d9-4289-bde1-8ae6fa5b49b8

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (KnodelPrimeCordial.knodel 3 n).edgeFinset.card = 3 * n / 2 := by
  classical
  let G := KnodelPrimeCordial.knodel 3 n
  have hdeg : ∀ v : Fin 2 × Fin (n / 2), G.degree v = 3 := by
    intro v
    exact KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
      n hn h10 v
  have hsum : ∑ v : Fin 2 × Fin (n / 2), G.degree v = 3 * Fintype.card (Fin 2 × Fin (n / 2)) := by
    simp_rw [hdeg]
    simp
    ring
  have hcard : Fintype.card (Fin 2 × Fin (n / 2)) = n := by
    simp
    omega
  have hn2 : n = 2 * (n / 2) := by omega
  have hh := G.sum_degrees_eq_twice_card_edges
  rw [hsum, hcard] at hh
  have hcard_edges : G.edgeFinset.card = 3 * (n / 2) := by
    have hmul : 3 * (2 * (n / 2)) = 2 * G.edgeFinset.card := by
      rw [← hn2]
      exact hh
    omega
  have h2dvd : 2 ∣ n := ⟨n / 2, hn2⟩
  change G.edgeFinset.card = 3 * n / 2
  rw [Nat.mul_div_assoc 3 h2dvd]
  exact hcard_edges
