-- Prove2me | solution 1 for MooreGraphs.moore_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:15:57.320536+00:00
-- url     : https://prove2.me/submissions/c8ff4124-df0e-4c4d-93b1-a5699dd59edb

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution (k : ℕ) : 1 + (k + k * (k - 1)) = k ^ 2 + 1 := by
  cases k with
  | zero => rfl
  | succ k => simp; ring
end MooreGraphs
