-- Prove2me | solution 1 for MurtySimon.exists_adj_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:32.476158+00:00
-- url     : https://prove2.me/submissions/559d6d66-d8d1-478a-832f-87538f99e831

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {W : Type*} {H : SimpleGraph W} {v w : W} (h : H.Reachable v w)
    (hne : v ≠ w) : ∃ z, H.Adj v z := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hne
  | cons h _ => exact ⟨_, h⟩
end MurtySimon
