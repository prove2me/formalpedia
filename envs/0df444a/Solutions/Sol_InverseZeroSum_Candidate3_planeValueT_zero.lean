-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeValueT_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:23.862231+00:00
-- url     : https://prove2.me/submissions/25051529-4951-4b9d-aaf5-532a62db8cc3

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ d : Fin 13, planeValueT d (0 : F3T) = 0 := by
  decide
end InverseZeroSum.Candidate3
