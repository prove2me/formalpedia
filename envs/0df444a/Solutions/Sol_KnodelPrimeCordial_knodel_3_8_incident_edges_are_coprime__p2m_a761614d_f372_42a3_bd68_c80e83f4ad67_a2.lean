-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_3_8_incident_edges_are_coprime__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:34:08.610209+00:00
-- url     : https://prove2.me/submissions/38c6e296-3252-4680-a7c1-314c9cef6c4d

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
import Theorems.Thm_KnodelPrimeCordial_incident_edge_label_repr__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1

theorem solution (f : Fin 2 × Fin 4 → ℕ)
    (hbij : Set.BijOn f Set.univ (Set.Icc 1 8))
    (x y z : Fin 2 × Fin 4) (hx : f x = 1) (hy : f y = 5) (hz : f z = 7) :
    ((KnodelPrimeCordial.knodel 3 8).edgeFinset.filter
      (fun e => x ∈ e ∨ y ∈ e ∨ z ∈ e)) ⊆
      KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 8) f := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨heEdge, hincident⟩
  change e ∈ (KnodelPrimeCordial.knodel 3 8).edgeFinset.filter
    (fun e => KnodelPrimeCordial.edgeGcd f e = 1)
  rw [Finset.mem_filter]
  refine ⟨heEdge, ?_⟩
  rcases hincident with hincident | hincident
  · rcases KnodelPrimeCordial.incident_edge_label_repr__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
      (KnodelPrimeCordial.knodel 3 8) f hbij e heEdge x hincident with
      ⟨w, hrepr, hne, hrange⟩
    have hgcd := KnodelPrimeCordial.coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
      (a := f x) (b := f w) (by simp [hx]) hrange.1 hrange.2 (by simpa [hx] using hne)
    rw [hrepr, hx]
    simpa [hx] using hgcd
  · rcases hincident with hincident | hincident
    · rcases KnodelPrimeCordial.incident_edge_label_repr__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
        (KnodelPrimeCordial.knodel 3 8) f hbij e heEdge y hincident with
        ⟨w, hrepr, hne, hrange⟩
      have hgcd := KnodelPrimeCordial.coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
        (a := f y) (b := f w) (by simp [hy]) hrange.1 hrange.2 (by simpa [hy] using hne)
      rw [hrepr, hy]
      simpa [hy] using hgcd
    · rcases KnodelPrimeCordial.incident_edge_label_repr__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
        (KnodelPrimeCordial.knodel 3 8) f hbij e heEdge z hincident with
        ⟨w, hrepr, hne, hrange⟩
      have hgcd := KnodelPrimeCordial.coprime_special_label_range__p2m_df77e916_fdac_4de2_9395_a46d11d6721f_a1
        (a := f z) (b := f w) (by simp [hz]) hrange.1 hrange.2 (by simpa [hz] using hne)
      rw [hrepr, hz]
      simpa [hz] using hgcd
