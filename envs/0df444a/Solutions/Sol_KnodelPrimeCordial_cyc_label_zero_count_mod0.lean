-- Prove2me | solution 1 for KnodelPrimeCordial.cyc_label_zero_count_mod0
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T03:12:18.999488+00:00
-- url     : https://prove2.me/submissions/143b0356-7cb3-4a53-84af-0edf241499ed

import Theorems.Thm_KnodelPrimeCordial_cyc_label_one_count_mod0
import Theorems.Thm_KnodelPrimeCordial_labelF_cyc_bijective_mod0
import Theorems.Thm_KnodelPrimeCordial_cyclic_model
import Theorems.Thm_KnodelPrimeCordial_knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
import Theorems.Thm_KnodelPrimeCordial_edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1

open KnodelPrimeCordial

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    (edgesLabelZero (cyc n) (fun i : Fin n ↦ labelF i.val)).card = 3 * n / 4 := by
  have hbij := labelF_cyc_bijective_mod0 n hn h12
  have hpos (i : Fin n) : 0 < labelF i.val := by
    have hi := hbij.mapsTo (Set.mem_univ i)
    exact lt_of_lt_of_le Nat.zero_lt_one hi.1
  have hgcd : ∀ e ∈ (cyc n).edgeFinset,
      0 < edgeGcd (fun i : Fin n ↦ labelF i.val) e := by
    intro e _
    induction e using Sym2.inductionOn with
    | _ i j =>
      change 0 < Nat.gcd (labelF i.val) (labelF j.val)
      exact Nat.gcd_pos_of_pos_left _ (hpos i)
  have hpartition :=
    edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
      (cyc n) (fun i : Fin n ↦ labelF i.val) hgcd
  have hone := cyc_label_one_count_mod0 n hn h12
  have heven : Even n := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 12) h12)
  have h10 : 10 ≤ n := le_trans (by decide : 10 ≤ 12) (Nat.le_of_dvd hn h12)
  obtain ⟨hvtx, hadj⟩ := cyclic_model n heven (by omega)
  let E : cyc n ≃g knodel 3 n :=
    { Equiv.ofBijective (vtx n (by omega)) hvtx with
      map_rel_iff' := fun {a b} ↦ (hadj a b).symm }
  have hcard := E.card_edgeFinset_eq
  have hdegrees := (knodel 3 n).sum_degrees_eq_twice_card_edges
  simp_rw [knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
    n heven h10] at hdegrees
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    smul_eq_mul] at hdegrees
  rw [hone] at hpartition
  obtain ⟨k, rfl⟩ := h12
  omega
