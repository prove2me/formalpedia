-- Prove2me | solution 1 for InverseZeroSum.Candidate3.planeCoord_cap_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:00.058198+00:00
-- url     : https://prove2.me/submissions/5208d236-a28d-4a52-bcad-3dbc5b51944d

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution :
    ∀ A : Finset PlaneCoord,
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0) →
      A.card ≤ 4 := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 500000 in
    decide
end InverseZeroSum.Candidate3
