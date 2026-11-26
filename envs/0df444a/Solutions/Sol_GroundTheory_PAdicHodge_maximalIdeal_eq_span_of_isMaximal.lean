-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maximalIdeal_eq_span_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T12:17:25.029644+00:00
-- url     : https://prove2.me/submissions/a0615f9f-e407-491c-bf43-72d71191c200

import Mathlib

open Ideal IsLocalRing

theorem solution {B : Type*} [CommRing B] [IsLocalRing B] {π : B}
    (hmax : (span {π}).IsMaximal) : maximalIdeal B = span {π} :=
  (eq_maximalIdeal hmax).symm
