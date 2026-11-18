-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_total_edge_labels__p2m_9c307d6d_3fd4_4597_abb0_7474cd510ca5_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:04:57.711919+00:00
-- url     : https://prove2.me/submissions/f015d0c3-c388-4c51-ba7d-6df7f27e4482

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_vtx
import Theorems.Thm_KnodelPrimeCordial_edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
import Theorems.Thm_KnodelPrimeCordial_cyclic_model
import Theorems.Thm_KnodelPrimeCordial_knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1

open KnodelPrimeCordial in
theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
      (fun i : Fin n =>
        if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card +
      (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card =
        3 * (n / 2) := by
  have hbij := KnodelPrimeCordial.cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
    n hn h10 hmod
  rw [KnodelPrimeCordial.edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1]
  · obtain ⟨hb, hadj⟩ := KnodelPrimeCordial.cyclic_model n hn (by omega)
    let iso : cyc n ≃g knodel 3 n :=
      ⟨Equiv.ofBijective _ hb, fun {a b} => (hadj a b).symm⟩
    rw [iso.card_edgeFinset_eq]
    have hsum := (knodel 3 n).sum_degrees_eq_twice_card_edges
    simp only [KnodelPrimeCordial.knodel_three_regular__p2m_411d5a68_c305_475b_bbd0_563e10602942_a1
      n hn h10, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      smul_eq_mul] at hsum
    omega
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [edgeGcd, Sym2.lift_mk]
      apply Nat.gcd_pos_of_pos_left
      exact (Set.mem_Icc.mp (hbij.mapsTo (Set.mem_univ u))).1
