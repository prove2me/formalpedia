-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_3_8_three_vertices_incident_edges_lower_bound__p2m_a761614d_f372_42a3_bd68_c80e83f4ad67_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:06:17.729631+00:00
-- url     : https://prove2.me/submissions/45ce654e-ba95-4199-9dd2-98cfc542542b

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem solution (x y z : Fin 2 × Fin 4) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    7 ≤ ((KnodelPrimeCordial.knodel 3 8).edgeFinset.filter
      (fun e => x ∈ e ∨ y ∈ e ∨ z ∈ e)).card := by
  decide +revert
