-- Prove2me | solution 1 for MurtySimon.isEdgeMatching_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:26.734553+00:00
-- url     : https://prove2.me/submissions/e8828527-5ed0-449d-9b3d-601c86987e16

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : IsEdgeMatching G {s(a, b), s(c, d)} := by
  have hdisj : ∀ v ∈ s(a, b), v ∉ s(c, d) := by
    intro v hv hv'
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> rcases Sym2.mem_iff.1 hv' with h | h
    · exact hac h
    · exact had h
    · exact hbc h
    · exact hbd h
  refine ⟨fun e he => ?_, fun e he f hf hef v hve hvf => ?_⟩
  · rcases mem_insert.1 he with rfl | he
    · exact hab
    · rw [mem_singleton.1 he]; exact hcd
  · rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
    · exact hef rfl
    · rw [mem_singleton.1 hf] at hvf; exact hdisj v hve hvf
    · rw [mem_singleton.1 he] at hve; exact hdisj v hvf hve
    · rw [mem_singleton.1 he, mem_singleton.1 hf] at hef; exact hef rfl
end MurtySimon
