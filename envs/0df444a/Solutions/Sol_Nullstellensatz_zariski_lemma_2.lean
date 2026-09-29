-- Prove2me | solution 2 for Nullstellensatz.zariski_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:17:43.717447+00:00
-- url     : https://prove2.me/submissions/cbd1dd3b-fd43-4575-823d-536bd821137a

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

end Nullstellensatz

open Nullstellensatz

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.FiniteType K L] :
    Module.Finite K L :=
  finite_of_finite_type_of_isJacobsonRing K L
