-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.real_constant_div_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:09:36.79851+00:00
-- url     : https://prove2.me/submissions/74edf748-3ced-4d06-b2b5-92af7b91373e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution (c : Real) :
    Tendsto (fun H : Real => c / H) atTop (𝓝 0) := by
  exact Filter.Tendsto.const_div_atTop tendsto_id c