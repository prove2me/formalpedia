-- Prove2me | solution 1 for MatroidProphetKW.Single.identity_9_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:35:52.443954+00:00
-- url     : https://prove2.me/submissions/ac8fe2d2-7b14-487e-b4be-3c42418e5182

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace Aux_MPKW910
open MatroidProphetKW.Single

lemma Rset_sub {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (w' : α → ℝ) (A : Finset α) :
    Rset M A w' ⊆ maxBase M w' := by
  unfold Rset
  split_ifs with h
  · have hm := (Finset.exists_max_image (remCands M A w') (wt w') h).choose_spec.1
    unfold remCands at hm
    classical
    exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hm).1).trans Finset.sdiff_subset
  · exact Finset.empty_subset _

lemma crsplit {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (w' : α → ℝ) (A : Finset α) :
    wt w' (Cset M A w') + wt w' (Rset M A w') = wt w' (maxBase M w') := by
  unfold wt Cset
  exact Finset.sum_sdiff (Rset_sub M w' A)

end Aux_MPKW910

open MatroidProphetKW.Single in
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (w' : α → ℝ) (hw' : ∀ x, 0 ≤ w' x)
    (A : Finset α) (x : α) (hAx : M.Indep (↑(insert x A) : Set α)) :
    (wt w' (Cset M A w') + wt w' (Rset M A w') = wt w' (maxBase M w') ∧
      wt w' (maxBase M w') = wt w' (Cset M (insert x A) w') + wt w' (Rset M (insert x A) w')) ∧
    wt w' (Rset M A w') - wt w' (Rset M (insert x A) w')
      = wt w' (Cset M (insert x A) w') - wt w' (Cset M A w') := by
  have h1 := Aux_MPKW910.crsplit M w' A
  have h2 := Aux_MPKW910.crsplit M w' (insert x A)
  refine ⟨⟨h1, h2.symm⟩, ?_⟩
  linarith
