-- Prove2me | solution 1 for MurtySimon.IsMaximalEdgeMatching.covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:21.84432+00:00
-- url     : https://prove2.me/submissions/9f1dabde-5ece-4e01-8de9-9b51ec338a73

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
namespace IsMaximalEdgeMatching
theorem _root_.solution (hmax : IsMaximalEdgeMatching G M) {a b : V}
    (hab : G.Adj a b) (h : s(a, b) ∉ M) : Covered M a ∨ Covered M b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hcov : ∀ v, ∀ f ∈ M, v ∈ f → Covered M v := by
    intro v f hf hv
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨w, hf⟩
  have hab' : ∀ v ∈ s(a, b), ¬ Covered M v := by
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha
    · exact hb
  apply hmax.2 s(a, b) hab h
  refine ⟨fun e he => ?_, fun e he f hf hef v hve hvf => ?_⟩
  · rcases mem_insert.1 he with rfl | he
    · exact hab
    · exact hmax.1.1 e he
  · rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
    · exact hef rfl
    · exact hab' v hve (hcov v f hf hvf)
    · exact hab' v hvf (hcov v e he hve)
    · exact hmax.1.2 e he f hf hef v hve hvf
end IsMaximalEdgeMatching
end MurtySimon
