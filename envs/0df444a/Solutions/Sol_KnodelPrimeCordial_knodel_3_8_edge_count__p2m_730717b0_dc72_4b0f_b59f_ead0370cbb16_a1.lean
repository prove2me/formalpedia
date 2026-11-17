-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_3_8_edge_count__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T09:56:43.460195+00:00
-- url     : https://prove2.me/submissions/62cf249e-28a2-4b6f-a3cd-aef537535241

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem solution :
    (KnodelPrimeCordial.knodel 3 8).edgeFinset.card = 12 := by
  decide
