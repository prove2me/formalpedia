-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeValueT_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:16.85904+00:00
-- url     : https://prove2.me/submissions/2249dc86-a579-4cfb-a86c-a902dde5c1e7

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ d : Fin 13, ∀ x y : F3T,
      planeValueT d (x - y) = planeValueT d x - planeValueT d y := by
  decide
end InverseZeroSum.Candidate3
