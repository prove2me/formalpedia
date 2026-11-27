-- Prove2me | solution 1 for MatchingPolytope.Multi.InHull.push
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:02.332215+00:00
-- url     : https://prove2.me/submissions/b3fb0554-558b-4786-b639-72458a20fb98

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [Fintype E]
namespace MatchingPolytope.Multi
namespace InHull
theorem _root_.solution {ι : Type*} [Fintype ι] {Q : Finset E → Prop} (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∑ i, c i = 1) (φ : ι → Finset E) (hφ : ∀ i, c i ≠ 0 → Q (φ i)) :
    InHull Q (∑ i, c i • chi (φ i)) := by
  classical
  refine ⟨fun M => ∑ i ∈ univ.filter (fun i => φ i = M), c i,
    fun M => Finset.sum_nonneg (fun i _ => hc i), fun M hM => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
    rw [Finset.mem_filter] at hi
    exact hi.2 ▸ hφ i hci
  · rw [Finset.sum_fiberwise]; exact hc1
  · have : ∀ M, (∑ i ∈ univ.filter (fun i => φ i = M), c i) • chi M =
        ∑ i ∈ univ.filter (fun i => φ i = M), c i • chi (φ i) := by
      intro M
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.1 hi).2]
    simp_rw [this]
    rw [Finset.sum_fiberwise]
end InHull
end MatchingPolytope.Multi
