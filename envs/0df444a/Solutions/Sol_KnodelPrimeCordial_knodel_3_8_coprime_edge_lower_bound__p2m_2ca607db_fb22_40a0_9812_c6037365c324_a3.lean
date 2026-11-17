-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_3_8_coprime_edge_lower_bound__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:16:01.286892+00:00
-- url     : https://prove2.me/submissions/3b54bae8-3e50-4b44-a1e3-977771f4a8fc

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_knodel_3_8_three_vertices_incident_edges_lower_bound__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
import Theorems.Thm_KnodelPrimeCordial_knodel_3_8_incident_edges_are_coprime__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2

theorem solution (f : Fin 2 × Fin 4 → ℕ)
    (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) :
    7 ≤ (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 8) f).card := by
  classical
  have hbij' := hbij
  rcases hbij with ⟨hmaps, hinj, hsurj⟩
  obtain ⟨x, -, hx⟩ := hsurj (show (1 : ℕ) ∈ Set.Icc 1 8 by norm_num)
  obtain ⟨y, -, hy⟩ := hsurj (show (5 : ℕ) ∈ Set.Icc 1 8 by norm_num)
  obtain ⟨z, -, hz⟩ := hsurj (show (7 : ℕ) ∈ Set.Icc 1 8 by norm_num)
  have hxy : x ≠ y := by
    intro h
    have heq := congrArg f h
    rw [hx, hy] at heq
    norm_num at heq
  have hxz : x ≠ z := by
    intro h
    have heq := congrArg f h
    rw [hx, hz] at heq
    norm_num at heq
  have hyz : y ≠ z := by
    intro h
    have heq := congrArg f h
    rw [hy, hz] at heq
    norm_num at heq
  have hsubset :=
    KnodelPrimeCordial.knodel_3_8_incident_edges_are_coprime__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
      f hbij' x y z hx hy hz
  have hcard := Finset.card_mono hsubset
  have hlarge :=
    KnodelPrimeCordial.knodel_3_8_three_vertices_incident_edges_lower_bound__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
      x y z hxy hxz hyz
  exact le_trans hlarge hcard
