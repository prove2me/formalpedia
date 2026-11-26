-- Prove2me | solution 1 for O3.one_lt_conjugateExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:40.542246+00:00
-- url     : https://prove2.me/submissions/97c15285-8df7-4914-91a9-24f7efd68899

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_holderConjugate_conjugateExponent

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : 1 < p) :
    1 < conjugateExponent p := by
  exact (holderConjugate_conjugateExponent hp).symm.lt
end O3
