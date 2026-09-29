-- Prove2me | solution 1 for Nullstellensatz.zariski_lemma
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:16:44.78798+00:00
-- url     : https://prove2.me/submissions/1841b9b2-f660-4043-b735-b58b8f32d6ee

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.FiniteType K L] :
    Module.Finite K L :=
  finite_of_finite_type_of_isJacobsonRing K L
