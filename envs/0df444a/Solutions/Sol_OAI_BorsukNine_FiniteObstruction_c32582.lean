-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32582
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:17:14.549855+00:00
-- url     : https://prove2.me/submissions/4a1c814a-7e10-4208-b8e2-887c75fb874f

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31520
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31527
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32571
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32577

section
-- module Solutions.OAIQ058_BK.Borsuk_TenLabels_Labels
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction

attribute [local instance] Classical.propDecidable

variable {T Q : Family}

lemma filter_card_eq_two_three_pos {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hs : s.card = 4) (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, p x := by
  by_contra hn
  have hsub : s.filter p ⊆ s \ r := by
    intro x hx
    obtain ⟨hxs, hpx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨hxs, ?_⟩
    intro hxr
    exact hn ⟨x, hxr, hpx⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hrs, hs, hr, hp] at hc
  norm_num at hc

lemma filter_card_eq_two_three_neg {s r : Finset Labels} {p : Labels → Prop}
    [DecidablePred p] (hr : r.card = 3) (hrs : r ⊆ s)
    (hp : (s.filter p).card = 2) : ∃ x ∈ r, ¬ p x := by
  by_contra hn
  have hsub : r ⊆ s.filter p := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨hrs hx, ?_⟩
    by_contra hnp
    exact hn ⟨x, hx, hnp⟩
  have hc := Finset.card_le_card hsub
  rw [hr, hp] at hc
  norm_num at hc

lemma three_pos (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, T (insert w P) := by
  classical
  apply filter_card_eq_two_three_pos (s := Sᶜ \ P) (r := R) ?_ hcR hR
    (h.pair_count S P hS hP hcP)
  rw [Finset.card_sdiff_of_subset hP, Finset.card_compl, h.tetra_card S hS, hcP]
  decide

lemma three_neg (h : TenSystem T Q) (S P R : Finset Labels)
    (hS : Q S) (hP : P ⊆ Sᶜ) (hcP : P.card = 2)
    (hR : R ⊆ Sᶜ \ P) (hcR : R.card = 3) :
    ∃ w ∈ R, ¬ T (insert w P) := by
  classical
  exact filter_card_eq_two_three_neg hcR hR (h.pair_count S P hS hP hcP)

lemma tetra_extension {S U : Finset Labels} (hU : U ⊆ S)
    (hcS : S.card = 4) (hcU : U.card = 3) :
    ∃ v, v ∉ U ∧ S = insert v U := by
  have hcard : (S \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hU, hcS, hcU]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  have hm : v ∈ S \ U := by rw [hv]; simp
  refine ⟨v, (Finset.mem_sdiff.mp hm).2, ?_⟩
  have he := Finset.sdiff_union_of_subset hU
  rw [hv] at he
  simpa using he.symm

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases001
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}
theorem c3 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 1, 2} → False := by
  intro a121 n1
  exact n1 (h.down {0, 1, 2, 3} {0, 1, 2} a121 (by decide) (by decide))

theorem c4 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 1, 2, 9} → False := by
  intro a121 n122 n123 n124 n125 n126 n127
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {0, 1, 2} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 2} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 2} = {0, 1, 2, 4} by decide)) hS)
  · exact n123 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 2} = {0, 1, 2, 5} by decide)) hS)
  · exact n124 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 2} = {0, 1, 2, 6} by decide)) hS)
  · exact n125 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 2} = {0, 1, 2, 7} by decide)) hS)
  · exact n126 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 2} = {0, 1, 2, 8} by decide)) hS)
  · exact n127 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 2} = {0, 1, 2, 9} by decide)) hS)

theorem c18 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 1, 3} → False := by
  intro a121 n2
  exact n2 (h.down {0, 1, 2, 3} {0, 1, 3} a121 (by decide) (by decide))

theorem c19 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 1, 3, 5} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 1, 3, 9} → False := by
  intro a121 n128 n129 n130 n131 n132 n133
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {0, 1, 3} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 3} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 3} = {0, 1, 3, 4} by decide)) hS)
  · exact n129 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 3} = {0, 1, 3, 5} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 3} = {0, 1, 3, 6} by decide)) hS)
  · exact n131 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 3} = {0, 1, 3, 7} by decide)) hS)
  · exact n132 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 3} = {0, 1, 3, 8} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 3} = {0, 1, 3, 9} by decide)) hS)

theorem c56 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {0, 1, 5} → False := by
  intro a140 n4
  exact n4 (h.down {0, 1, 5, 7} {0, 1, 5} a140 (by decide) (by decide))

theorem c84 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {0, 1, 7} → False := by
  intro a140 n6
  exact n6 (h.down {0, 1, 5, 7} {0, 1, 7} a140 (by decide) (by decide))

theorem c107 (h : TenSystem T Q) :
    T {0, 1, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 4, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 1, 8, 9} → False := by
  intro a8 n127 n133 n138 n142 n145 n147 n148
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 1, 9} a8
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n138 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 9} = {0, 1, 4, 9} by decide)) hS)
  · exact n142 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n147 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n148 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c113 (h : TenSystem T Q) :
    Q {0, 1, 4, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 1, 8, 9} → False := by
  intro a138 n127 n133 n142 n145 n147 n148
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 4, 9} {0, 1, 9} a138 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n142 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n147 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n148 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c123 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 2, 3} → False := by
  intro a121 n9
  exact n9 (h.down {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide))

theorem c124 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 3, 9} → False := by
  intro a121 n149 n150 n151 n152 n153 n154
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 3} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n149 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 3} = {0, 2, 3, 4} by decide)) hS)
  · exact n150 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 3} = {0, 2, 3, 5} by decide)) hS)
  · exact n151 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 3} = {0, 2, 3, 6} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 3} = {0, 2, 3, 7} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 3} = {0, 2, 3, 8} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 3} = {0, 2, 3, 9} by decide)) hS)

theorem c150 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 2, 4} → False := by
  intro a159 n10
  exact n10 (h.down {0, 2, 4, 9} {0, 2, 4} a159 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases002
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c155 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {0, 2, 5} → False := by
  intro a150 n11
  exact n11 (h.down {0, 2, 3, 5} {0, 2, 5} a150 (by decide) (by decide))

theorem c170 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {0, 2, 6} → False := by
  intro a151 n12
  exact n12 (h.down {0, 2, 3, 6} {0, 2, 6} a151 (by decide) (by decide))

theorem c200 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {0, 2, 8} → False := by
  intro a153 n14
  exact n14 (h.down {0, 2, 3, 8} {0, 2, 8} a153 (by decide) (by decide))

theorem c216 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a154 n127 n159 n163 n166 n168 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 9} {0, 2, 9} a154 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c217 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 2, 9} → False := by
  intro a159 n15
  exact n15 (h.down {0, 2, 4, 9} {0, 2, 9} a159 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases003
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c254 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {0, 1, 3, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 5, 9} → False := by
  intro a177 n129 n150 n170 n175 n176 n178
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {0, 3, 5} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n129 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 5} = {0, 1, 3, 5} by decide)) hS)
  · exact n150 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n175 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 5} = {0, 3, 5, 6} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 5} = {0, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n178 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 5} = {0, 3, 5, 9} by decide)) hS)

theorem c302 (h : TenSystem T Q) :
    T {0, 3, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a21 n133 n154 n174 n178 n181 n183 n184
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 9} a21
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases004
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c312 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a181 n133 n154 n174 n178 n183 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 6, 9} {0, 3, 9} a181 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n183 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c314 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a183 n133 n154 n174 n178 n181 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 9} {0, 3, 9} a183 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c362 (h : TenSystem T Q) :
    T {0, 4, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a25 n137 n158 n173 n187 n190 n192 n194
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 8} a25
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c370 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a187 n137 n158 n173 n190 n192 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 4, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c372 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a190 n137 n158 n173 n187 n192 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {0, 4, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c376 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → False := by
  intro a194 n137 n158 n173 n187 n190 n192
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 8, 9} {0, 4, 8} a194 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c380 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 4, 9} → False := by
  intro a159 n26
  exact n26 (h.down {0, 2, 4, 9} {0, 4, 9} a159 (by decide) (by decide))

theorem c382 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {0, 4, 9} → False := by
  intro a174 n26
  exact n26 (h.down {0, 3, 4, 9} {0, 4, 9} a174 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases005
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c407 (h : TenSystem T Q) :
    T {0, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a28 n140 n161 n176 n186 n195 n198 n199
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 7} a28
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c415 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a186 n140 n161 n176 n195 n198 n199
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 7} {0, 5, 7} a186 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c422 (h : TenSystem T Q) :
    T {0, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a29 n141 n162 n177 n187 n196 n198 n200
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 8} a29
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c430 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a187 n141 n162 n177 n196 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 5, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c434 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a198 n141 n162 n177 n187 n196 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 7, 8} {0, 5, 8} a198 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c467 (h : TenSystem T Q) :
    T {0, 6, 8} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 8, 9} → False := by
  intro a32 n144 n165 n180 n190 n196 n201 n203
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 6, 8} a32
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n144 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n196 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 8} = {0, 6, 8, 9} by decide)) hS)

theorem c469 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 8, 9} → False := by
  intro a144 n165 n180 n190 n196 n201 n203
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 6, 8} {0, 6, 8} a144 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n165 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n196 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 8} = {0, 6, 8, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases006
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c475 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 8, 9} → False := by
  intro a190 n144 n165 n180 n196 n201 n203
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {0, 6, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n144 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 8} = {0, 6, 8, 9} by decide)) hS)

theorem c495 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {0, 6, 9} → False := by
  intro a203 n33
  exact n33 (h.down {0, 6, 8, 9} {0, 6, 9} a203 (by decide) (by decide))

theorem c527 (h : TenSystem T Q) :
    T {0, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a36 n148 n169 n184 n194 n200 n203 n204
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 8, 9} a36
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n148 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 8, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n194 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n200 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n203 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n204 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c538 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a203 n36
  exact n36 (h.down {0, 6, 8, 9} {0, 8, 9} a203 (by decide) (by decide))

theorem c539 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a203 n148 n169 n184 n194 n200 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {0, 8, 9} a203 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n148 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 8, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n194 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n200 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c543 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {1, 2, 3} → False := by
  intro a121 n37
  exact n37 (h.down {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide))

theorem c558 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {1, 2, 4} → False := by
  intro a122 n38
  exact n38 (h.down {0, 1, 2, 4} {1, 2, 4} a122 (by decide) (by decide))

theorem c581 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {1, 2, 5} → False := by
  intro a217 n39
  exact n39 (h.down {1, 2, 5, 7} {1, 2, 5} a217 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases007
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c603 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {1, 2, 7} → False := by
  intro a125 n41
  exact n41 (h.down {0, 1, 2, 7} {1, 2, 7} a125 (by decide) (by decide))

theorem c609 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {1, 2, 7} → False := by
  intro a217 n41
  exact n41 (h.down {1, 2, 5, 7} {1, 2, 7} a217 (by decide) (by decide))

theorem c615 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 7} → False := by
  intro a224 n41
  exact n41 (h.down {1, 2, 7, 9} {1, 2, 7} a224 (by decide) (by decide))

theorem c632 (h : TenSystem T Q) :
    T {1, 2, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a43 n127 n210 n215 n219 n222 n224 n225
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 9} a43
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c633 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {1, 2, 9} → False := by
  intro a127 n43
  exact n43 (h.down {0, 1, 2, 9} {1, 2, 9} a127 (by decide) (by decide))

theorem c634 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a127 n210 n215 n219 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 9} {1, 2, 9} a127 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c640 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a219 n127 n210 n215 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 9} {1, 2, 9} a219 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases008
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c662 (h : TenSystem T Q) :
    T {1, 3, 5} → ¬ Q {0, 1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 3, 5, 9} → False := by
  intro a45 n129 n206 n226 n231 n232 n233 n234
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 5} a45
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n129 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 5} = {0, 1, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n231 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 5} = {1, 3, 5, 6} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 5} = {1, 3, 5, 7} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 5} = {1, 3, 5, 8} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 5} = {1, 3, 5, 9} by decide)) hS)

theorem c664 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 3, 5, 9} → False := by
  intro a129 n206 n226 n231 n232 n233 n234
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 5} {1, 3, 5} a129 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n231 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 5} = {1, 3, 5, 6} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 5} = {1, 3, 5, 7} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 5} = {1, 3, 5, 8} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 5} = {1, 3, 5, 9} by decide)) hS)

theorem c671 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {1, 3, 5} → False := by
  intro a232 n45
  exact n45 (h.down {1, 3, 5, 7} {1, 3, 5} a232 (by decide) (by decide))

theorem c674 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ Q {0, 1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 9} → False := by
  intro a233 n129 n206 n226 n231 n232 n234
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 8} {1, 3, 5} a233 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n129 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 5} = {0, 1, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n231 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 5} = {1, 3, 5, 6} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 5} = {1, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n234 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 5} = {1, 3, 5, 9} by decide)) hS)

theorem c692 (h : TenSystem T Q) :
    T {1, 3, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 7, 9} → False := by
  intro a47 n131 n208 n228 n232 n235 n238 n239
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 7} a47
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n131 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n238 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 7} = {1, 3, 7, 8} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 7} = {1, 3, 7, 9} by decide)) hS)

theorem c694 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 7, 9} → False := by
  intro a131 n208 n228 n232 n235 n238 n239
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 7} {1, 3, 7} a131 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n238 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 7} = {1, 3, 7, 8} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 7} = {1, 3, 7, 9} by decide)) hS)

theorem c723 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a133 n49
  exact n49 (h.down {0, 1, 3, 9} {1, 3, 9} a133 (by decide) (by decide))

theorem c725 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a210 n49
  exact n49 (h.down {1, 2, 3, 9} {1, 3, 9} a210 (by decide) (by decide))

theorem c727 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 3, 9} → False := by
  intro a230 n49
  exact n49 (h.down {1, 3, 4, 9} {1, 3, 9} a230 (by decide) (by decide))

theorem c729 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 3, 9} → False := by
  intro a234 n49
  exact n49 (h.down {1, 3, 5, 9} {1, 3, 9} a234 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases009
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c735 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 3, 9} → False := by
  intro a240 n49
  exact n49 (h.down {1, 3, 8, 9} {1, 3, 9} a240 (by decide) (by decide))

theorem c746 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {1, 4, 5} → False := by
  intro a242 n50
  exact n50 (h.down {1, 4, 5, 7} {1, 4, 5} a242 (by decide) (by decide))

theorem c763 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {1, 4, 6} → False := by
  intro a246 n51
  exact n51 (h.down {1, 4, 6, 8} {1, 4, 6} a246 (by decide) (by decide))

theorem c774 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {1, 4, 7} → False := by
  intro a242 n52
  exact n52 (h.down {1, 4, 5, 7} {1, 4, 7} a242 (by decide) (by decide))

theorem c775 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 4, 7, 9} → False := by
  intro a242 n136 n213 n228 n245 n248 n249
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {1, 4, 7} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n136 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n213 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n245 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n248 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 7} = {1, 4, 7, 8} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 7} = {1, 4, 7, 9} by decide)) hS)

theorem c827 (h : TenSystem T Q) :
    T {1, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a56 n140 n217 n232 n242 n251 n254 n255
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 7} a56
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c829 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a140 n217 n232 n242 n251 n254 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 7} {1, 5, 7} a140 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c831 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a217 n140 n232 n242 n251 n254 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 7} {1, 5, 7} a217 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c835 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a242 n140 n217 n232 n251 n254 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {1, 5, 7} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases010
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c841 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → False := by
  intro a255 n140 n217 n232 n242 n251 n254
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 9} {1, 5, 7} a255 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c868 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {1, 5, 9} → False := by
  intro a255 n58
  exact n58 (h.down {1, 5, 7, 9} {1, 5, 9} a255 (by decide) (by decide))

theorem c894 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {1, 6, 8} → False := by
  intro a246 n60
  exact n60 (h.down {1, 4, 6, 8} {1, 6, 8} a246 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases011
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c941 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a255 n63
  exact n63 (h.down {1, 5, 7, 9} {1, 7, 9} a255 (by decide) (by decide))

theorem c975 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 3, 4} → False := by
  intro a265 n65
  exact n65 (h.down {2, 3, 4, 9} {2, 3, 4} a265 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases012
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1035 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {2, 3, 8} → False := by
  intro a275 n69
  exact n69 (h.down {2, 3, 8, 9} {2, 3, 8} a275 (by decide) (by decide))

theorem c1038 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a154 n70
  exact n70 (h.down {0, 2, 3, 9} {2, 3, 9} a154 (by decide) (by decide))

theorem c1042 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 3, 9} → False := by
  intro a265 n70
  exact n70 (h.down {2, 3, 4, 9} {2, 3, 9} a265 (by decide) (by decide))

theorem c1050 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {2, 3, 9} → False := by
  intro a275 n70
  exact n70 (h.down {2, 3, 8, 9} {2, 3, 9} a275 (by decide) (by decide))

theorem c1078 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {2, 4, 6} → False := by
  intro a281 n72
  exact n72 (h.down {2, 4, 6, 8} {2, 4, 6} a281 (by decide) (by decide))

theorem c1113 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {2, 4, 9} → False := by
  intro a159 n75
  exact n75 (h.down {0, 2, 4, 9} {2, 4, 9} a159 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases013
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1117 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 4, 9} → False := by
  intro a265 n75
  exact n75 (h.down {2, 3, 4, 9} {2, 4, 9} a265 (by decide) (by decide))

theorem c1230 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ T {2, 6, 9} → False := by
  intro a294 n82
  exact n82 (h.down {2, 6, 8, 9} {2, 6, 9} a294 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases014
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1273 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ T {2, 8, 9} → False := by
  intro a294 n85
  exact n85 (h.down {2, 6, 8, 9} {2, 8, 9} a294 (by decide) (by decide))

theorem c1288 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 4, 5} → False := by
  intro a298 n86
  exact n86 (h.down {3, 4, 5, 8} {3, 4, 5} a298 (by decide) (by decide))

theorem c1320 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 4, 7} → False := by
  intro a304 n88
  exact n88 (h.down {3, 4, 7, 9} {3, 4, 7} a304 (by decide) (by decide))

theorem c1335 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 4, 8} → False := by
  intro a305 n89
  exact n89 (h.down {3, 4, 8, 9} {3, 4, 8} a305 (by decide) (by decide))

theorem c1348 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 4, 9} → False := by
  intro a304 n90
  exact n90 (h.down {3, 4, 7, 9} {3, 4, 9} a304 (by decide) (by decide))

theorem c1349 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a304 n174 n230 n265 n299 n302 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {3, 4, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases015
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1352 (h : TenSystem T Q) :
    T {3, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 6, 9} → False := by
  intro a91 n175 n231 n266 n296 n306 n307 n308
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 6} a91
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 6} = {3, 5, 6, 7} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 6} = {3, 5, 6, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases016
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1428 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {3, 6, 8} → False := by
  intro a180 n96
  exact n96 (h.down {0, 3, 6, 8} {3, 6, 8} a180 (by decide) (by decide))

theorem c1434 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {3, 6, 8} → False := by
  intro a301 n96
  exact n96 (h.down {3, 4, 6, 8} {3, 6, 8} a301 (by decide) (by decide))

theorem c1440 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {3, 6, 8} → False := by
  intro a314 n96
  exact n96 (h.down {3, 6, 8, 9} {3, 6, 8} a314 (by decide) (by decide))

theorem c1479 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a304 n99
  exact n99 (h.down {3, 4, 7, 9} {3, 7, 9} a304 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases017
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1495 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a305 n184 n240 n275 n311 n314 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 8, 9} {3, 8, 9} a305 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1502 (h : TenSystem T Q) :
    T {4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a101 n185 n241 n276 n296 n316 n317 n318
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 6} a101
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact n296 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1510 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a296 n185 n241 n276 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 6} {4, 5, 6} a296 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1532 (h : TenSystem T Q) :
    T {4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a103 n187 n243 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 8} a103
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1534 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a187 n243 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {4, 5, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1540 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a298 n187 n243 n278 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 8} {4, 5, 8} a298 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases018
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1577 (h : TenSystem T Q) :
    T {4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a106 n190 n246 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 6, 8} a106
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1578 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a190 n106
  exact n106 (h.down {0, 4, 6, 8} {4, 6, 8} a190 (by decide) (by decide))

theorem c1579 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a190 n246 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {4, 6, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1581 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a246 n190 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 8} {4, 6, 8} a246 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1583 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a281 n190 n246 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 8} {4, 6, 8} a281 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1608 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a192 n108
  exact n108 (h.down {0, 4, 7, 8} {4, 7, 8} a192 (by decide) (by decide))

theorem c1629 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a304 n109
  exact n109 (h.down {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide))

theorem c1630 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a304 n193 n249 n284 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases019
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1659 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a306 n111
  exact n111 (h.down {3, 5, 6, 7} {5, 6, 7} a306 (by decide) (by decide))

theorem c1712 (h : TenSystem T Q) :
    T {5, 7, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a115 n199 n255 n290 n310 n320 n327 n329
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 7, 9} a115
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n199 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 7, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1715 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {5, 7, 9} → False := by
  intro a255 n115
  exact n115 (h.down {1, 5, 7, 9} {5, 7, 9} a255 (by decide) (by decide))

theorem c1716 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a255 n199 n290 n310 n320 n327 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 9} {5, 7, 9} a255 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n199 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n290 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 7, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1728 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a200 n116
  exact n116 (h.down {0, 5, 8, 9} {5, 8, 9} a200 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases020
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1734 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a311 n116
  exact n116 (h.down {3, 5, 8, 9} {5, 8, 9} a311 (by decide) (by decide))

theorem c1743 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a201 n117
  exact n117 (h.down {0, 6, 7, 8} {6, 7, 8} a201 (by decide) (by decide))

theorem c1772 (h : TenSystem T Q) :
    T {6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a119 n203 n259 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {6, 8, 9} a119
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1774 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a203 n259 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {6, 8, 9} a203 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1776 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a259 n203 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 8, 9} {6, 8, 9} a259 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1778 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a294 n203 n259 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 8, 9} {6, 8, 9} a294 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1788 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a204 n120
  exact n120 (h.down {0, 7, 8, 9} {7, 8, 9} a204 (by decide) (by decide))

theorem c1794 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a315 n120
  exact n120 (h.down {3, 7, 8, 9} {7, 8, 9} a315 (by decide) (by decide))

theorem c1804 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  intro a121 n102 n119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n102 (hc.mpr n119)

theorem c1806 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n103 n118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n103 (hc.mpr n118)

theorem c1808 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {6, 7, 8} → False := by
  intro a121 n104 n117
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n104 (hc.mpr n117)

theorem c1809 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {6, 7, 8} → False := by
  intro a121 a104 a117
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a104 a117

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases021
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1810 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {5, 8, 9} → False := by
  intro a121 n105 n116
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n105 (hc.mpr n116)

theorem c1813 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {5, 7, 9} → False := by
  intro a121 a106 a115
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a106 a115

theorem c1815 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {5, 7, 8} → False := by
  intro a121 a107 a114
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a107 a114

theorem c1816 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {5, 6, 9} → False := by
  intro a121 n108 n113
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n108 (hc.mpr n113)

theorem c1819 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {5, 6, 8} → False := by
  intro a121 a109 a112
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a109 a112

theorem c1824 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → False := by
  intro a121 n101 n102 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1841 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a121 a102 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 7} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c1845 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a121 a105 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 7} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c1856 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {4, 6, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n104 n107 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases022
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1884 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n112 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1886 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {5, 6, 9} → ¬ T {5, 7, 9} → False := by
  intro a121 n104 n113 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) ht)

theorem c1887 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {5, 6, 9} → T {5, 7, 9} → False := by
  intro a121 a104 a113 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c1890 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {5, 7, 9} → ¬ T {5, 8, 9} → False := by
  intro a121 n104 n115 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 9} {4, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) ht)

theorem c1895 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a121 a105 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

theorem c1900 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n111 n117 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c1903 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {5, 6, 8} → T {6, 7, 8} → False := by
  intro a121 a106 a112 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 8} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)

theorem c1904 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a121 n106 n112 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c1906 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {6, 7, 8} → ¬ T {6, 8, 9} → False := by
  intro a121 n106 n117 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c1907 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a121 a106 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases023
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1925 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a121 a114 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c1950 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 6, 7} → ¬ T {5, 8, 9} → False := by
  intro a122 n95 n116
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 7} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n95 (hc.mpr n116)

theorem c1971 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {3, 6, 7} → T {3, 6, 8} → False := by
  intro a122 a91 a95 a96
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 6} {5, 7, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) a96)

theorem c1981 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 7} → T {3, 6, 7} → T {3, 7, 9} → False := by
  intro a122 a92 a95 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 7} {5, 6, 9} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 7} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c2002 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 6} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → False := by
  intro a122 n91 n111 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 4} {5, 6} {3, 7, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c2020 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a122 n93 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 4} {5, 8} {3, 6, 9} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases024
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c2153 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a123 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {4, 7} {3, 6, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c2239 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 7, 9} → T {4, 5, 8} → False := by
  intro a124 a99 a103
  have hc := h.complementary {0, 1, 2, 6} {3, 7, 9} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 7, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a99 a103

theorem c2367 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 8} → T {5, 6, 9} → False := by
  intro a125 a89 a113
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 8} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a89 a113

theorem c2441 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 8} → T {4, 5, 8} → T {4, 8, 9} → False := by
  intro a125 a89 a103 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 7} {4, 8} {3, 5, 9} a125 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 8} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c2583 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a126 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {4, 7} {3, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c2643 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {6, 7, 8} → False := by
  intro a127 a86 a117
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 5} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a86 a117

theorem c2645 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 6} → T {5, 7, 8} → False := by
  intro a127 a87 a114
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 6} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a87 a114

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases025
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c2657 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 6, 7} → T {4, 5, 8} → False := by
  intro a127 a95 a103
  have hc := h.complementary {0, 1, 2, 9} {3, 6, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a95 a103

theorem c2678 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 4, 6} → ¬ T {3, 5, 6} → ¬ T {3, 6, 7} → False := by
  intro a127 n87 n91 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 9} {3, 6} {4, 5, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n87 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c2747 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 7} → T {5, 6, 7} → T {5, 7, 8} → False := by
  intro a127 a92 a111 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {5, 7} {3, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) a114)

theorem c2790 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {2, 6, 7} → ¬ T {5, 8, 9} → False := by
  intro a128 n80 n116
  have hc := h.complementary {0, 1, 3, 4} {2, 6, 7} a128 (by decide) (by decide)
  have he : ( {0, 1, 3, 4} : Finset Labels)ᶜ \ {2, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n80 (hc.mpr n116)

theorem c2811 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 6} → T {2, 6, 7} → T {2, 6, 8} → False := by
  intro a128 a76 a80 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 4} {2, 6} {5, 7, 8} a128 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) a81)

theorem c2936 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ T {2, 7, 8} → ¬ T {4, 6, 9} → False := by
  intro a129 n83 n107
  have hc := h.complementary {0, 1, 3, 5} {2, 7, 8} a129 (by decide) (by decide)
  have he : ( {0, 1, 3, 5} : Finset Labels)ᶜ \ {2, 7, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n83 (hc.mpr n107)

theorem c3011 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → T {2, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a129 a75 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 5} {4, 9} {2, 7, 8} a129 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c3180 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 7, 8} → ¬ T {4, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a130 n83 n108 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 3, 6} {7, 8} {2, 4, 9} a130 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n83 (Eq.mp (congrArg T (show insert (2 : Labels) {7, 8} = {2, 7, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c3297 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 5, 6} → T {4, 5, 6} → T {5, 6, 9} → False := by
  intro a131 a76 a101 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {5, 6} {2, 4, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c3351 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 5, 6} → T {4, 7, 9} → False := by
  intro a132 a76 a109
  have hc := h.complementary {0, 1, 3, 8} {2, 5, 6} a132 (by decide) (by decide)
  have he : ( {0, 1, 3, 8} : Finset Labels)ᶜ \ {2, 5, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a76 a109

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases026
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c4024 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {3, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a136 n96 n112 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 7} {6, 8} {3, 5, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c4141 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {3, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a137 a91 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {5, 6} {3, 7, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases027
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c4164 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a137 n95 n111 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 8} {6, 7} {3, 5, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c4471 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 4, 6} → T {3, 8, 9} → False := by
  intro a140 a72 a100
  have hc := h.complementary {0, 1, 5, 7} {2, 4, 6} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a100

theorem c4521 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 4, 9} → T {2, 6, 9} → T {2, 8, 9} → False := by
  intro a140 a75 a82 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 7} {2, 9} {4, 6, 8} a140 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c4584 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a140 n96 n106 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 7} {6, 8} {3, 4, 9} a140 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c4709 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a141 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 7} {3, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c4865 (h : TenSystem T Q) :
    Q {0, 1, 5, 9} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 8} → False := by
  intro a142 a95 a105 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 9} {6, 7} {3, 4, 8} a142 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases028
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c5137 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {3, 4, 9} → T {4, 5, 9} → T {4, 7, 9} → False := by
  intro a144 a90 a104 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 8} {4, 9} {3, 5, 7} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c5293 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a145 a93 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 9} {5, 8} {3, 4, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c5580 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a147 n96 n106 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 7, 9} {6, 8} {3, 4, 5} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)

theorem c5712 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → ¬ T {3, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a148 n92 n102 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 8, 9} {5, 7} {3, 4, 6} a148 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c5728 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 5, 9} → ¬ T {6, 7, 8} → False := by
  intro a149 n58 n117
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n58 (hc.mpr n117)

theorem c5729 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 9} → T {6, 7, 8} → False := by
  intro a149 a58 a117
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a58 a117

theorem c5738 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 7, 9} → ¬ T {5, 6, 8} → False := by
  intro a149 n63 n112
  have hc := h.complementary {0, 2, 3, 4} {1, 7, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n63 (hc.mpr n112)

theorem c5746 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 5, 6} → ¬ T {1, 5, 8} → ¬ T {1, 5, 9} → False := by
  intro a149 n55 n57 n58
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 4} {1, 5} {6, 8, 9} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n55 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 5} = {1, 5, 8} by decide)) ht)
  · exact n58 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases029
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c5872 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 6, 8} → ¬ T {4, 7, 9} → False := by
  intro a150 n60 n109
  have hc := h.complementary {0, 2, 3, 5} {1, 6, 8} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n60 (hc.mpr n109)

theorem c5873 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 6, 8} → T {4, 7, 9} → False := by
  intro a150 a60 a109
  have hc := h.complementary {0, 2, 3, 5} {1, 6, 8} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a60 a109

theorem c6041 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a151 a52 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 6} {1, 7} {4, 5, 9} a151 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

theorem c6157 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 6, 8} → T {4, 5, 9} → False := by
  intro a152 a60 a104
  have hc := h.complementary {0, 2, 3, 7} {1, 6, 8} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a60 a104

theorem c6260 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 6, 8} → ¬ T {4, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a152 n60 n106 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 7} {6, 8} {1, 4, 9} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n60 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 8} = {1, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c6329 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a153 a52 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {1, 7} {4, 5, 9} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases030
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c6423 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 5} → T {6, 7, 8} → False := by
  intro a154 a50 a117
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 5} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a50 a117

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases031
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c6988 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 3, 9} → ¬ T {5, 6, 7} → False := by
  intro a158 n49 n111
  have hc := h.complementary {0, 2, 4, 8} {1, 3, 9} a158 (by decide) (by decide)
  have he : ( {0, 2, 4, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n111)

theorem c7081 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {3, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a158 a91 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 6} {3, 7, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c7122 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 3, 5} → ¬ T {6, 7, 8} → False := by
  intro a159 n45 n117
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 5} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n117)

theorem c7123 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 5} → T {6, 7, 8} → False := by
  intro a159 a45 a117
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 5} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a45 a117

theorem c7126 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 3, 7} → ¬ T {5, 6, 8} → False := by
  intro a159 n47 n112
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 7} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n47 (hc.mpr n112)

theorem c7132 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 5, 7} → ¬ T {3, 6, 8} → False := by
  intro a159 n56 n96
  have hc := h.complementary {0, 2, 4, 9} {1, 5, 7} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 5, 7} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n56 (hc.mpr n96)

theorem c7151 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 5} → T {1, 5, 6} → T {1, 5, 7} → False := by
  intro a159 a45 a55 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {1, 5} {3, 6, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

theorem c7155 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 5} → T {1, 5, 7} → T {1, 5, 8} → False := by
  intro a159 a45 a56 a57
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {1, 5} {3, 7, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 5} = {1, 5, 8} by decide)) a57)

theorem c7248 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 6, 8} → ¬ T {3, 6, 8} → ¬ T {6, 7, 8} → False := by
  intro a159 n60 n96 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {6, 8} {1, 3, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n60 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 8} = {1, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases032
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c7251 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 6, 8} → T {5, 6, 8} → T {6, 7, 8} → False := by
  intro a159 a60 a112 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {6, 8} {1, 5, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 8} = {1, 6, 8} by decide)) a60)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)

theorem c7411 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 4, 6} → T {3, 8, 9} → False := by
  intro a161 a51 a100
  have hc := h.complementary {0, 2, 5, 7} {1, 4, 6} a161 (by decide) (by decide)
  have he : ( {0, 2, 5, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a100

theorem c7649 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a162 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 7} {3, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c7805 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 8} → False := by
  intro a163 a95 a105 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 9} {6, 7} {3, 4, 8} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases033
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c7968 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ T {1, 3, 9} → ¬ T {4, 5, 7} → False := by
  intro a165 n49 n102
  have hc := h.complementary {0, 2, 6, 8} {1, 3, 9} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n102)

theorem c7979 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 5, 9} → T {3, 4, 7} → False := by
  intro a165 a58 a88
  have hc := h.complementary {0, 2, 6, 8} {1, 5, 9} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a58 a88

theorem c8233 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a166 a93 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 9} {5, 8} {3, 4, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases034
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c8520 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a168 n96 n106 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 9} {6, 8} {3, 4, 5} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)

theorem c8652 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {3, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a169 n92 n102 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {5, 7} {3, 4, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c8662 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {1, 2, 6} → ¬ T {7, 8, 9} → False := by
  intro a170 n40 n120
  have hc := h.complementary {0, 3, 4, 5} {1, 2, 6} a170 (by decide) (by decide)
  have he : ( {0, 3, 4, 5} : Finset Labels)ᶜ \ {1, 2, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n120)

theorem c9084 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {1, 2, 6} → ¬ T {5, 7, 9} → False := by
  intro a173 n40 n115
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 6} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n115)

theorem c9087 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 2, 7} → T {5, 6, 9} → False := by
  intro a173 a41 a113
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 7} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a113

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases035
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c9223 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 2, 5} → T {6, 7, 8} → False := by
  intro a174 a39 a117
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 5} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a39 a117

theorem c9226 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n41 n112
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 7} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n112)

theorem c9228 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 8} → ¬ T {5, 6, 7} → False := by
  intro a174 n42 n111
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 8} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n111)

theorem c9318 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 5, 6} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n55 n111 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {5, 6} {1, 7, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n55 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c9320 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {2, 5, 6} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n76 n111 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {5, 6} {2, 7, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c9361 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {2, 7, 8} → T {5, 7, 8} → T {6, 7, 8} → False := by
  intro a174 a83 a114 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {7, 8} {2, 5, 6} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 8} = {2, 7, 8} by decide)) a83)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)

theorem c9365 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 2, 7} → T {4, 8, 9} → False := by
  intro a175 a41 a110
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 7} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a110

theorem c9477 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {2, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a175 a75 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 6} {4, 9} {2, 7, 8} a175 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c9517 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 6, 8} → T {2, 4, 9} → False := by
  intro a176 a60 a75
  have hc := h.complementary {0, 3, 5, 7} {1, 6, 8} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 6, 8} = {2, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a60 a75

theorem c9646 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 7} → ¬ T {4, 6, 9} → False := by
  intro a177 n41 n107
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 7} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n107)

theorem c9649 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 9} → T {4, 6, 7} → False := by
  intro a177 a43 a105
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 9} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a43 a105

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases036
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c9784 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ T {1, 2, 6} → ¬ T {4, 7, 8} → False := by
  intro a178 n40 n108
  have hc := h.complementary {0, 3, 5, 9} {1, 2, 6} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n108)

theorem c10062 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {1, 2, 4} → ¬ T {5, 7, 9} → False := by
  intro a180 n38 n115
  have hc := h.complementary {0, 3, 6, 8} {1, 2, 4} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n115)

theorem c10203 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 2, 4} → T {5, 7, 8} → False := by
  intro a181 a38 a114
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 4} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a38 a114

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases037
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c10626 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 2, 6} → ¬ T {4, 5, 7} → False := by
  intro a184 n40 n102
  have hc := h.complementary {0, 3, 8, 9} {1, 2, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n102)

theorem c10827 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a185 a37 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {2, 3} {1, 8, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases038
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c11048 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 2, 9} → ¬ T {3, 6, 7} → False := by
  intro a187 n43 n95
  have hc := h.complementary {0, 4, 5, 8} {1, 2, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n95)

theorem c11067 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a187 a37 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 2} {3, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11068 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → ¬ T {1, 2, 9} → False := by
  intro a187 n40 n41 n43
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {1, 2} {6, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases039
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c11483 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a190 a37 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 2} {3, 5, 7} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c11505 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 3, 5} → T {1, 5, 7} → T {1, 5, 9} → False := by
  intro a190 a45 a56 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 5} {3, 7, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

theorem c11513 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 3, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a190 a47 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 7} {3, 5, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases040
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c11890 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 5} → ¬ T {2, 6, 8} → False := by
  intro a193 n45 n81
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 5} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n81)

theorem c12023 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {5, 6, 7} → False := by
  intro a194 a37 a111
  have hc := h.complementary {0, 4, 8, 9} {1, 2, 3} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a111

theorem c12026 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {1, 2, 6} → ¬ T {3, 5, 7} → False := by
  intro a194 n40 n92
  have hc := h.complementary {0, 4, 8, 9} {1, 2, 6} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n92)

theorem c12270 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a195 n49 n70 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 7} {3, 9} {1, 2, 4} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c12303 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {4, 7, 9} → False := by
  intro a196 a37 a109
  have hc := h.complementary {0, 5, 6, 8} {1, 2, 3} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a109

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases041
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c12396 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a196 n44 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {3, 4} {1, 2, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases042
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c12605 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a198 a37 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 2} {3, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c12645 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {2, 3, 4} → T {2, 3, 9} → False := by
  intro a198 a37 a65 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {2, 3} {1, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12690 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a198 n49 n70 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {3, 9} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c12723 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 2, 3} → T {4, 6, 8} → False := by
  intro a199 a37 a106
  have hc := h.complementary {0, 5, 7, 9} {1, 2, 3} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a106

theorem c12726 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ T {1, 2, 6} → ¬ T {3, 4, 8} → False := by
  intro a199 n40 n89
  have hc := h.complementary {0, 5, 7, 9} {1, 2, 6} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 4, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n89)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases043
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c13096 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → ¬ T {1, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a201 n44 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 6, 7, 8} {3, 4} {1, 2, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

theorem c13284 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 2, 4} → ¬ T {3, 5, 7} → False := by
  intro a203 n38 n92
  have hc := h.complementary {0, 6, 8, 9} {1, 2, 4} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n92)

theorem c13307 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a203 a37 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {1, 2} {3, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c13316 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 3, 4} → ¬ T {1, 3, 5} → ¬ T {1, 3, 7} → False := by
  intro a203 n44 n45 n47
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 6, 8, 9} {1, 3} {4, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n45 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)

theorem c13379 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 3, 4} → T {3, 4, 5} → T {3, 4, 7} → False := by
  intro a203 a44 a86 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {3, 4} {1, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases044
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c13757 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {0, 6, 9} → T {0, 8, 9} → False := by
  intro a206 a26 a33 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {0, 9} {4, 6, 8} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c13791 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a206 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {4, 9} {0, 7, 8} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases045
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c14039 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 9} → T {0, 6, 9} → T {0, 8, 9} → False := by
  intro a208 a26 a33 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {0, 9} {4, 6, 8} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases046
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c14804 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {3, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a213 n96 n112 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 4, 7} {6, 8} {3, 5, 9} a213 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c14975 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 5, 8} → T {3, 6, 7} → False := by
  intro a215 a29 a95
  have hc := h.complementary {1, 2, 4, 9} {0, 5, 8} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a95

theorem c15242 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 3, 4} → ¬ T {6, 8, 9} → False := by
  intro a217 n16 n119
  have hc := h.complementary {1, 2, 5, 7} {0, 3, 4} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 3, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n119)

theorem c15250 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 4, 6} → ¬ T {3, 8, 9} → False := by
  intro a217 n23 n100
  have hc := h.complementary {1, 2, 5, 7} {0, 4, 6} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n100)

theorem c15257 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 6, 8} → T {3, 4, 9} → False := by
  intro a217 a32 a90
  have hc := h.complementary {1, 2, 5, 7} {0, 6, 8} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a90

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases047
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c15273 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 3, 4} → T {0, 4, 6} → T {0, 4, 9} → False := by
  intro a217 a16 a23 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 7} {0, 4} {3, 6, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 4} = {0, 4, 9} by decide)) a26)

theorem c15360 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 6, 8} → ¬ T {3, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a217 n32 n96 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 7} {6, 8} {0, 3, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c15364 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a217 n96 n106 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 7} {6, 8} {3, 4, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases048
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c15959 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 5, 8} → T {3, 4, 7} → False := by
  intro a222 a29 a88
  have hc := h.complementary {1, 2, 6, 9} {0, 5, 8} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a88

theorem c16501 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {3, 6, 7} → T {4, 6, 7} → T {5, 6, 7} → False := by
  intro a225 a95 a105 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {6, 7} {3, 4, 5} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases049
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c16605 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 6, 8} → T {2, 6, 8} → T {6, 8, 9} → False := by
  intro a226 a32 a81 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {6, 8} {0, 2, 9} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 8} = {2, 6, 8} by decide)) a81)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c16607 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a226 a32 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {6, 8} {0, 7, 9} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c16782 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 2, 5} → ¬ T {6, 8, 9} → False := by
  intro a228 n11 n119
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 5} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n119)

theorem c16901 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 6, 8} → T {2, 6, 8} → T {6, 8, 9} → False := by
  intro a228 a32 a81 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {6, 8} {0, 2, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 8} = {2, 6, 8} by decide)) a81)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases050
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c17257 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 9} → T {0, 4, 9} → T {0, 8, 9} → False := by
  intro a231 a15 a26 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {0, 9} {2, 4, 8} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c17315 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a231 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {4, 9} {0, 7, 8} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c17346 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 8} → ¬ T {4, 6, 9} → False := by
  intro a232 n14 n107
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 8} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n107)

theorem c17357 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 6, 8} → T {2, 4, 9} → False := by
  intro a232 a32 a75
  have hc := h.complementary {1, 3, 5, 7} {0, 6, 8} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a75

theorem c17365 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 4} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a232 a10 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {0, 2} {4, 6, 9} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c17373 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 9} → False := by
  intro a232 a10 a23 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {0, 4} {2, 6, 9} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 4} = {0, 4, 9} by decide)) a26)

theorem c17378 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 6} → ¬ T {0, 4, 6} → ¬ T {0, 6, 8} → False := by
  intro a232 n12 n23 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 7} {0, 6} {2, 4, 8} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) ht)

theorem c17535 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a233 a15 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {0, 9} {2, 4, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases051
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c17626 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 7} → ¬ T {4, 6, 8} → False := by
  intro a234 n13 n106
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n106)

theorem c17817 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 2, 9} → T {0, 4, 9} → T {0, 8, 9} → False := by
  intro a235 a15 a26 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {0, 9} {2, 4, 8} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases052
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c18237 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a238 a15 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 8} {0, 9} {2, 4, 6} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

theorem c18324 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 8} → False := by
  intro a239 n11 n106
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 5} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n106)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases053
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c18667 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a241 a9 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {2, 3} {0, 8, 9} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c18743 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {6, 8, 9} → False := by
  intro a242 a9 a119
  have hc := h.complementary {1, 4, 5, 7} {0, 2, 3} a242 (by decide) (by decide)
  have he : ( {1, 4, 5, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a119

theorem c18757 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 6, 8} → T {2, 3, 9} → False := by
  intro a242 a32 a70
  have hc := h.complementary {1, 4, 5, 7} {0, 6, 8} a242 (by decide) (by decide)
  have he : ( {1, 4, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a70

theorem c18765 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a242 a9 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {0, 2} {3, 6, 9} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c18767 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {0, 2, 8} → T {0, 2, 9} → False := by
  intro a242 a9 a14 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {0, 2} {3, 8, 9} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases054
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c18862 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {0, 6, 8} → ¬ T {3, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a242 n32 n96 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 7} {6, 8} {0, 3, 9} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c19002 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n31 n95 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {0, 3, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c19163 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {5, 8, 9} → False := by
  intro a245 a9 a116
  have hc := h.complementary {1, 4, 6, 7} {0, 2, 3} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a116

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases055
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c19303 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {5, 7, 9} → False := by
  intro a246 a9 a115
  have hc := h.complementary {1, 4, 6, 8} {0, 2, 3} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a115

theorem c19309 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 9} → T {3, 5, 7} → False := by
  intro a246 a15 a92
  have hc := h.complementary {1, 4, 6, 8} {0, 2, 9} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a92

theorem c19317 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 5, 7} → T {2, 3, 9} → False := by
  intro a246 a28 a70
  have hc := h.complementary {1, 4, 6, 8} {0, 5, 7} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a70

theorem c19325 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 9} → False := by
  intro a246 a9 a11 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {0, 2} {3, 5, 9} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c19422 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a246 n28 n92 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 8} {5, 7} {0, 3, 9} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n28 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c19583 (h : TenSystem T Q) :
    Q {1, 4, 7, 8} → T {0, 2, 3} → T {5, 6, 9} → False := by
  intro a248 a9 a113
  have hc := h.complementary {1, 4, 7, 8} {0, 2, 3} a248 (by decide) (by decide)
  have he : ( {1, 4, 7, 8} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a113

theorem c19724 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 5} → ¬ T {3, 6, 8} → False := by
  intro a249 n11 n96
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n96)

theorem c19842 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 5, 6} → ¬ T {3, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a249 n27 n91 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {5, 6} {0, 3, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases056
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c20025 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a251 a9 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {0, 2} {3, 4, 9} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases057
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c20445 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a254 a9 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 2} {3, 4, 9} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c20563 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 2, 3} → T {4, 6, 8} → False := by
  intro a255 a9 a106
  have hc := h.complementary {1, 5, 7, 9} {0, 2, 3} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a106

theorem c20571 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 3, 4} → T {2, 6, 8} → False := by
  intro a255 a16 a81
  have hc := h.complementary {1, 5, 7, 9} {0, 3, 4} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a16 a81

theorem c20581 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 6, 8} → T {2, 3, 4} → False := by
  intro a255 a32 a65
  have hc := h.complementary {1, 5, 7, 9} {0, 6, 8} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a32 a65

theorem c20698 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {0, 6, 8} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a255 n32 n96 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 9} {6, 8} {0, 3, 4} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)

theorem c20700 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {2, 6, 8} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a255 n81 n96 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 9} {6, 8} {2, 3, 4} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n81 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 8} = {2, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases058
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c21126 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 5} → ¬ T {3, 4, 7} → False := by
  intro a259 n11 n88
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 5} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n88)

theorem c21128 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 7} → ¬ T {3, 4, 5} → False := by
  intro a259 n13 n86
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 7} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 4, 5} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n86)

theorem c21143 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 5} → False := by
  intro a259 a9 a10 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {0, 2} {3, 4, 5} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c21145 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a259 a9 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {0, 2} {3, 4, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c21214 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 5} → False := by
  intro a259 n16 n65 n86
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {3, 4} {0, 2, 5} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n86 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) ht)

theorem c21216 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 7} → False := by
  intro a259 n16 n65 n88
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {3, 4} {0, 2, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases059
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c21965 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 1, 6} → T {5, 7, 8} → False := by
  intro a265 a5 a114
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 6} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a5 a114

theorem c21975 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 5, 8} → T {1, 6, 7} → False := by
  intro a265 a29 a59
  have hc := h.complementary {2, 3, 4, 9} {0, 5, 8} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a59

theorem c22034 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 6} → ¬ T {1, 6, 7} → ¬ T {1, 6, 8} → False := by
  intro a265 n5 n59 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {1, 6} {0, 7, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 6} = {0, 1, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases060
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c22215 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a266 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {4, 9} {0, 7, 8} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases063
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c23556 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 8, 9} → False := by
  intro a276 n8 n21 n36
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 6} {0, 9} {1, 3, 8} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n36 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) ht)

theorem c23796 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {1, 3, 9} → False := by
  intro a278 n31 n49
  have hc := h.complementary {2, 4, 5, 8} {0, 6, 7} a278 (by decide) (by decide)
  have he : ( {2, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n49)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases064
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c24217 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 5, 7} → T {1, 3, 9} → False := by
  intro a281 a28 a49
  have hc := h.complementary {2, 4, 6, 8} {0, 5, 7} a281 (by decide) (by decide)
  have he : ( {2, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a49

theorem c24223 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 7} → False := by
  intro a281 a2 a4 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {0, 1} {3, 5, 7} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c24277 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {1, 3, 5} → T {1, 5, 7} → T {1, 5, 9} → False := by
  intro a281 a45 a56 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 5} {3, 7, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

theorem c24285 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {1, 3, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a281 a47 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 7} {3, 5, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases065
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c24742 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 5, 6} → ¬ T {3, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a284 n27 n91 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {5, 6} {0, 3, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases066
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c25590 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → ¬ T {0, 4, 8} → ¬ T {3, 4, 8} → ¬ T {4, 6, 8} → False := by
  intro a290 n25 n89 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 9} {4, 8} {0, 3, 6} a290 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n89 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 8} = {3, 4, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)

theorem c26047 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 7} → False := by
  intro a294 a2 a4 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {0, 1} {3, 5, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases067
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c26121 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {1, 3, 4} → T {3, 4, 5} → T {3, 4, 7} → False := by
  intro a294 a44 a86 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {3, 4} {1, 5, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)

theorem c26363 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 8} → False := by
  intro a296 a1 a41 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {1, 2} {0, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases068
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c26723 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {6, 7, 8} → False := by
  intro a299 a1 a117
  have hc := h.complementary {3, 4, 5, 9} {0, 1, 2} a299 (by decide) (by decide)
  have he : ( {3, 4, 5, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a117

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases069
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c27143 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {5, 7, 8} → False := by
  intro a302 a1 a114
  have hc := h.complementary {3, 4, 6, 9} {0, 1, 2} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a114

theorem c27423 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {5, 6, 8} → False := by
  intro a304 a1 a112
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 2} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a112

theorem c27435 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 2, 8} → T {1, 5, 6} → False := by
  intro a304 a14 a55
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a14 a55

theorem c27437 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 5, 6} → T {1, 2, 8} → False := by
  intro a304 a27 a42
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 2, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a42

theorem c27439 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 5, 8} → T {1, 2, 6} → False := by
  intro a304 a29 a40
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a40

theorem c27440 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 6, 8} → ¬ T {1, 2, 5} → False := by
  intro a304 n32 n39
  have hc := h.complementary {3, 4, 7, 9} {0, 6, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n39)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases070
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c27578 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 5, 7} → ¬ T {1, 2, 6} → False := by
  intro a305 n28 n40
  have hc := h.complementary {3, 4, 8, 9} {0, 5, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n40)

theorem c27581 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 6, 7} → T {1, 2, 5} → False := by
  intro a305 a31 a39
  have hc := h.complementary {3, 4, 8, 9} {0, 6, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 5} := by decide
  rw [he] at hc
  exact hc.mp a31 a39

theorem c27628 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {1, 2, 5} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → False := by
  intro a305 n39 n40 n41
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {1, 2} {5, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n39 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)

theorem c27843 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {4, 7, 9} → False := by
  intro a307 a1 a109
  have hc := h.complementary {3, 5, 6, 8} {0, 1, 2} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a109

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases071
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c28047 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 8} → False := by
  intro a308 a1 a41 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {1, 2} {0, 7, 8} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases072
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c28278 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {0, 4, 8} → ¬ T {1, 2, 6} → False := by
  intro a310 n25 n40
  have hc := h.complementary {3, 5, 7, 9} {0, 4, 8} a310 (by decide) (by decide)
  have he : ( {3, 5, 7, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n40)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases074
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c28841 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 5, 7} → T {1, 2, 4} → False := by
  intro a314 a28 a38
  have hc := h.complementary {3, 6, 8, 9} {0, 5, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a28 a38

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases075
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c29123 (h : TenSystem T Q) :
    Q {4, 5, 6, 7} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 8} → False := by
  intro a316 a1 a2 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 7} {0, 1} {2, 3, 8} a316 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c29131 (h : TenSystem T Q) :
    Q {4, 5, 6, 7} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 8} → False := by
  intro a316 a1 a9 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 7} {0, 2} {1, 3, 8} a316 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c29139 (h : TenSystem T Q) :
    Q {4, 5, 6, 7} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 8} → False := by
  intro a316 a2 a9 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 7} {0, 3} {1, 2, 8} a316 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c29146 (h : TenSystem T Q) :
    Q {4, 5, 6, 7} → ¬ T {0, 1, 8} → ¬ T {0, 2, 8} → ¬ T {0, 3, 8} → False := by
  intro a316 n7 n14 n20
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 5, 6, 7} {0, 8} {1, 2, 3} a316 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 8} = {0, 1, 8} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) ht)
  · exact n20 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 8} = {0, 3, 8} by decide)) ht)

theorem c29263 (h : TenSystem T Q) :
    Q {4, 5, 6, 8} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 7} → False := by
  intro a317 a1 a2 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 8} {0, 1} {2, 3, 7} a317 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c29271 (h : TenSystem T Q) :
    Q {4, 5, 6, 8} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 7} → False := by
  intro a317 a1 a9 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 8} {0, 2} {1, 3, 7} a317 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c29279 (h : TenSystem T Q) :
    Q {4, 5, 6, 8} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 7} → False := by
  intro a317 a2 a9 a19
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 8} {0, 3} {1, 2, 7} a317 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)

theorem c29286 (h : TenSystem T Q) :
    Q {4, 5, 6, 8} → ¬ T {0, 1, 7} → ¬ T {0, 2, 7} → ¬ T {0, 3, 7} → False := by
  intro a317 n6 n13 n19
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 5, 6, 8} {0, 7} {1, 2, 3} a317 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n6 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) ht)
  · exact n19 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 7} = {0, 3, 7} by decide)) ht)

theorem c29403 (h : TenSystem T Q) :
    Q {4, 5, 6, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 7} → False := by
  intro a318 a1 a2 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 9} {0, 1} {2, 3, 7} a318 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c29411 (h : TenSystem T Q) :
    Q {4, 5, 6, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 7} → False := by
  intro a318 a1 a9 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 9} {0, 2} {1, 3, 7} a318 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c29419 (h : TenSystem T Q) :
    Q {4, 5, 6, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 7} → False := by
  intro a318 a2 a9 a19
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 6, 9} {0, 3} {1, 2, 7} a318 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)

theorem c29426 (h : TenSystem T Q) :
    Q {4, 5, 6, 9} → ¬ T {0, 1, 7} → ¬ T {0, 2, 7} → ¬ T {0, 3, 7} → False := by
  intro a318 n6 n13 n19
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 5, 6, 9} {0, 7} {1, 2, 3} a318 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n6 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) ht)
  · exact n19 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 7} = {0, 3, 7} by decide)) ht)

theorem c29543 (h : TenSystem T Q) :
    Q {4, 5, 7, 8} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 6} → False := by
  intro a319 a1 a2 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 7, 8} {0, 1} {2, 3, 6} a319 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c29551 (h : TenSystem T Q) :
    Q {4, 5, 7, 8} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 6} → False := by
  intro a319 a1 a9 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 7, 8} {0, 2} {1, 3, 6} a319 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c29559 (h : TenSystem T Q) :
    Q {4, 5, 7, 8} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 6} → False := by
  intro a319 a2 a9 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 7, 8} {0, 3} {1, 2, 6} a319 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c29566 (h : TenSystem T Q) :
    Q {4, 5, 7, 8} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 3, 6} → False := by
  intro a319 n5 n12 n18
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 5, 7, 8} {0, 6} {1, 2, 3} a319 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)

theorem c29683 (h : TenSystem T Q) :
    Q {4, 5, 7, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 6} → False := by
  intro a320 a1 a2 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 7, 9} {0, 1} {2, 3, 6} a320 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c29691 (h : TenSystem T Q) :
    Q {4, 5, 7, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 6} → False := by
  intro a320 a1 a9 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 7, 9} {0, 2} {1, 3, 6} a320 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c29699 (h : TenSystem T Q) :
    Q {4, 5, 7, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 6} → False := by
  intro a320 a2 a9 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 7, 9} {0, 3} {1, 2, 6} a320 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c29706 (h : TenSystem T Q) :
    Q {4, 5, 7, 9} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 3, 6} → False := by
  intro a320 n5 n12 n18
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 5, 7, 9} {0, 6} {1, 2, 3} a320 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)

theorem c29823 (h : TenSystem T Q) :
    Q {4, 5, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 6} → False := by
  intro a321 a1 a2 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 8, 9} {0, 1} {2, 3, 6} a321 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c29831 (h : TenSystem T Q) :
    Q {4, 5, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 6} → False := by
  intro a321 a1 a9 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 8, 9} {0, 2} {1, 3, 6} a321 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c29839 (h : TenSystem T Q) :
    Q {4, 5, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 6} → False := by
  intro a321 a2 a9 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 5, 8, 9} {0, 3} {1, 2, 6} a321 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c29846 (h : TenSystem T Q) :
    Q {4, 5, 8, 9} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 3, 6} → False := by
  intro a321 n5 n12 n18
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 5, 8, 9} {0, 6} {1, 2, 3} a321 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)

theorem c29963 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a322 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 8} {0, 1} {2, 3, 5} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases076
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c29971 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a322 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 8} {0, 2} {1, 3, 5} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c29979 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a322 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 8} {0, 3} {1, 2, 5} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c29986 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a322 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 6, 7, 8} {0, 5} {1, 2, 3} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30103 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a323 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 9} {0, 1} {2, 3, 5} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c30111 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a323 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 9} {0, 2} {1, 3, 5} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c30119 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a323 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 9} {0, 3} {1, 2, 5} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c30126 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a323 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 6, 7, 9} {0, 5} {1, 2, 3} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30243 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a324 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 8, 9} {0, 1} {2, 3, 5} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c30251 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a324 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 8, 9} {0, 2} {1, 3, 5} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c30259 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a324 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 8, 9} {0, 3} {1, 2, 5} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c30266 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a324 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 6, 8, 9} {0, 5} {1, 2, 3} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30383 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a325 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 7, 8, 9} {0, 1} {2, 3, 5} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c30391 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a325 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 7, 8, 9} {0, 2} {1, 3, 5} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c30399 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a325 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 7, 8, 9} {0, 3} {1, 2, 5} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c30406 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a325 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 7, 8, 9} {0, 5} {1, 2, 3} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30663 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a327 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 9} {0, 1} {2, 3, 4} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

theorem c30671 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a327 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 9} {0, 2} {1, 3, 4} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

theorem c30679 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a327 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 9} {0, 3} {1, 2, 4} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

theorem c30686 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a327 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 6, 7, 9} {0, 4} {1, 2, 3} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

theorem c30803 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a328 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 8, 9} {0, 1} {2, 3, 4} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

theorem c30811 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a328 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 8, 9} {0, 2} {1, 3, 4} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

theorem c30819 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a328 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 8, 9} {0, 3} {1, 2, 4} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

theorem c30826 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a328 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 6, 8, 9} {0, 4} {1, 2, 3} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

private theorem c30943 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a329 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 7, 8, 9} {0, 1} {2, 3, 4} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

private theorem c30951 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a329 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 7, 8, 9} {0, 2} {1, 3, 4} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

private theorem c30959 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a329 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 7, 8, 9} {0, 3} {1, 2, 4} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

private theorem c30966 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a329 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 7, 8, 9} {0, 4} {1, 2, 3} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

private theorem c31083 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a330 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {6, 7, 8, 9} {0, 1} {2, 3, 4} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

private theorem c31091 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a330 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {6, 7, 8, 9} {0, 2} {1, 3, 4} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

private theorem c31099 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a330 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {6, 7, 8, 9} {0, 3} {1, 2, 4} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

private theorem c31106 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a330 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {6, 7, 8, 9} {0, 4} {1, 2, 3} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

theorem c31202 (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 3} → False := by
  intro n121
  exact n121 h0
theorem c31203 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 1, 2} → False := by
  classical
  intro n1
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c3 h u0_121 n1

theorem c31204 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 1, 3} → False := by
  classical
  intro n2
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c18 h u0_121 n2

theorem c31205 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 3} → False := by
  classical
  intro n9
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c123 h u0_121 n9

theorem c31206 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 3} → False := by
  classical
  intro n37
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c543 h u0_121 n37

theorem c31207 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {6, 7, 8, 9} → False := by
  classical
  intro a330
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c31083 h a330 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31091 h a330 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c31099 h a330 u1_2 u2_9 hv
  exact c31106 h a330 u3_3 u4_10 u5_16

theorem c31208 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 7, 8, 9} → False := by
  classical
  intro a329
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30943 h a329 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30951 h a329 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30959 h a329 u1_2 u2_9 hv
  exact c30966 h a329 u3_3 u4_10 u5_16

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases077
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31209 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 6, 8, 9} → False := by
  classical
  intro a328
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30803 h a328 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30811 h a328 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30819 h a328 u1_2 u2_9 hv
  exact c30826 h a328 u3_3 u4_10 u5_16

theorem c31210 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 6, 7, 9} → False := by
  classical
  intro a327
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30663 h a327 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30671 h a327 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30679 h a327 u1_2 u2_9 hv
  exact c30686 h a327 u3_3 u4_10 u5_16

theorem c31212 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 7, 8, 9} → False := by
  classical
  intro a325
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c30383 h a325 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c30391 h a325 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c30399 h a325 u1_2 u2_9 hv
  exact c30406 h a325 u3_4 u4_11 u5_17

theorem c31213 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 6, 8, 9} → False := by
  classical
  intro a324
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c30243 h a324 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c30251 h a324 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c30259 h a324 u1_2 u2_9 hv
  exact c30266 h a324 u3_4 u4_11 u5_17

theorem c31214 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 6, 7, 9} → False := by
  classical
  intro a323
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c30103 h a323 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c30111 h a323 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c30119 h a323 u1_2 u2_9 hv
  exact c30126 h a323 u3_4 u4_11 u5_17

theorem c31215 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 6, 7, 8} → False := by
  classical
  intro a322
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c29963 h a322 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c29971 h a322 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c29979 h a322 u1_2 u2_9 hv
  exact c29986 h a322 u3_4 u4_11 u5_17

theorem c31216 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 8, 9} → False := by
  classical
  intro a321
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c29823 h a321 u0_1 u1_2 hv
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29831 h a321 u0_1 u2_9 hv
  have u5_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c29839 h a321 u1_2 u2_9 hv
  exact c29846 h a321 u3_5 u4_12 u5_18

theorem c31217 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 7, 9} → False := by
  classical
  intro a320
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c29683 h a320 u0_1 u1_2 hv
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29691 h a320 u0_1 u2_9 hv
  have u5_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c29699 h a320 u1_2 u2_9 hv
  exact c29706 h a320 u3_5 u4_12 u5_18

theorem c31218 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 7, 8} → False := by
  classical
  intro a319
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c29543 h a319 u0_1 u1_2 hv
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29551 h a319 u0_1 u2_9 hv
  have u5_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c29559 h a319 u1_2 u2_9 hv
  exact c29566 h a319 u3_5 u4_12 u5_18

theorem c31219 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 6, 9} → False := by
  classical
  intro a318
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c29403 h a318 u0_1 u1_2 hv
  have u4_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c29411 h a318 u0_1 u2_9 hv
  have u5_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c29419 h a318 u1_2 u2_9 hv
  exact c29426 h a318 u3_6 u4_13 u5_19

theorem c31220 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 6, 8} → False := by
  classical
  intro a317
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c29263 h a317 u0_1 u1_2 hv
  have u4_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c29271 h a317 u0_1 u2_9 hv
  have u5_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c29279 h a317 u1_2 u2_9 hv
  exact c29286 h a317 u3_6 u4_13 u5_19

theorem c31221 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 6, 7} → False := by
  classical
  intro a316
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c29123 h a316 u0_1 u1_2 hv
  have u4_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c29131 h a316 u0_1 u2_9 hv
  have u5_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c29139 h a316 u1_2 u2_9 hv
  exact c29146 h a316 u3_7 u4_14 u5_20

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases082
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31261 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → T {4, 5, 6} → ¬ Q {2, 4, 5, 6} → False := by
  classical
  intro n185 n241 a101 n276
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1502 h a101 n185 n241 n276 hv u0_316 u1_317 u2_318
  exact c1510 h u3_296 n185 n241 n276 u0_316 u1_317 u2_318

theorem c31262 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 8, 9} → ¬ Q {2, 4, 5, 6} → T {4, 5, 6} → False := by
  classical
  intro a275 n276 a101
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_69 : T {2, 3, 8} := by
    by_contra hv
    exact c1035 h a275 hv
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1050 h a275 hv
  have u4_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10827 h hv u0_37 u2_69 u3_70
  have u5_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18667 h hv u1_9 u2_69 u3_70
  exact c31261 h h0 u4_185 u5_241 a101 n276

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases084
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31274 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → T {6, 8, 9} → False := by
  classical
  intro n203 n294 n314 a119
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c1776 h hv n203 n294 n314 u2_324 u1_328 u0_330
  exact c1772 h a119 n203 u3_259 n294 n314 u2_324 u1_328 u0_330

theorem c31297 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → Q {0, 2, 3, 4} → ¬ Q {1, 4, 6, 8} → T {1, 5, 7} → Q {0, 2, 4, 9} → ¬ Q {3, 4, 6, 8} → ¬ T {6, 8, 9} → False := by
  classical
  intro n117 a149 n246 a56 a159 n301 n119
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1906 h u0_121 hv n117 n119
  have u5_45 : T {1, 3, 5} := by
    by_contra hv
    exact c7122 h a159 hv n117
  have u6_58 : T {1, 5, 9} := by
    by_contra hv
    exact c5728 h a149 hv n117
  have u7_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11505 h hv u5_45 a56 u6_58
  have u8_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24277 h hv u5_45 a56 u6_58
  exact c1577 h u4_106 u7_190 n246 u8_281 n301 u3_317 u2_322 u1_324

private theorem c31298 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → T {6, 7, 8} → Q {0, 2, 3, 4} → ¬ Q {1, 4, 6, 8} → T {1, 5, 7} → Q {0, 2, 4, 9} → ¬ Q {3, 4, 6, 8} → False := by
  classical
  intro a106 a117 a149 n246 a56 a159 n301
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1903 h u0_121 a106 hv a117
  have u5_47 : T {1, 3, 7} := by
    by_contra hv
    exact c7126 h a159 hv u4_112
  have u6_63 : T {1, 7, 9} := by
    by_contra hv
    exact c5738 h a149 hv u4_112
  have u7_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11513 h hv u5_47 a56 u6_63
  have u8_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24285 h hv u5_47 a56 u6_63
  exact c1577 h a106 u7_190 n246 u8_281 n301 u3_317 u2_322 u1_324

private theorem c31299 (h : TenSystem T Q) :
    ¬ Q {1, 2, 5, 7} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 5, 6, 7} → T {1, 5, 7} → ¬ Q {0, 1, 5, 7} → False := by
  classical
  intro n217 n255 n254 n232 n251 a56 n140
  have u0_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c827 h a56 n140 n217 n232 hv n251 n254 n255
  exact c835 h u0_242 n140 n217 n232 n251 n254 n255

private theorem c31300 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 4} → ¬ Q {1, 4, 6, 8} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → ¬ T {6, 8, 9} → False := by
  classical
  intro a149 n246 a159 n96 n119
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u2_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u3_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u0_9 u1_10 u2_15
  have u4_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u0_9 u1_10 u2_15
  have u5_56 : T {1, 5, 7} := by
    by_contra hv
    exact c7132 h a159 hv n96
  have u6_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u7_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31297 h h0 hv a149 n246 u5_56 a159 u6_301 n119
  have u8_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c7123 h a159 hv u7_117
  have u9_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c5729 h a149 hv u7_117
  have u10_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c671 h hv u8_45
  have u11_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c868 h hv u9_58
  have u12_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31298 h h0 hv u7_117 a149 n246 u5_56 a159 u6_301
  have u13_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15364 h hv n96 u12_106 n119
  have u14_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4584 h hv n96 u12_106 n119
  exact c31299 h u13_217 u11_255 u3_254 u10_232 u4_251 u5_56 u14_140

theorem c31301 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → Q {0, 2, 4, 9} → False := by
  classical
  intro a232 a159
  have u0_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1113 h a159 hv
  have u1_26 : T {0, 4, 9} := by
    by_contra hv
    exact c380 h a159 hv
  have u2_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u3_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u4_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c17357 h a232 hv u0_75
  have u5_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17365 h a232 u3_10 hv u2_15
  have u6_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c17373 h a232 u3_10 hv u1_26
  exact c17378 h a232 u5_12 u6_23 u4_32

theorem c31302 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n140 n217 a159 n96
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u3_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u4_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u5_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u0_9 u3_10 u4_15
  have u6_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u0_9 u3_10 u4_15
  have u7_56 : T {1, 5, 7} := by
    by_contra hv
    exact c7132 h a159 hv n96
  have u8_255 : Q {1, 5, 7, 9} := by
    by_contra hv
    exact c31299 h n217 hv u5_254 u2_232 u6_251 u7_56 n140
  have u9_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c841 h u8_255 n140 n217 u2_232 hv u6_251 u5_254
  have u10_63 : T {1, 7, 9} := by
    by_contra hv
    exact c941 h u8_255 hv
  have u11_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1715 h u8_255 hv
  have u12_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c20563 h u8_255 u0_9 hv
  have u13_50 : T {1, 4, 5} := by
    by_contra hv
    exact c746 h u9_242 hv
  have u14_52 : T {1, 4, 7} := by
    by_contra hv
    exact c774 h u9_242 hv
  have u15_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h u9_242 u0_9 hv
  have u16_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6329 h hv u14_52 u7_56 u10_63
  have u17_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6041 h hv u14_52 u7_56 u10_63
  have u18_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19303 h hv u0_9 u11_115
  have u19_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1904 h u1_121 u12_106 hv u15_119
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1906 h u1_121 u12_106 hv u15_119
  have u21_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6423 h hv u13_50 u20_117
  have u22_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c31300 h h0 hv u18_246 a159 n96 u15_119
  have u23_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u1_121 hv u19_112
  have u24_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c7251 h a159 hv u19_112 u20_117
  have u25_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5872 h hv u24_60 u23_109
  have u26_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6260 h hv u24_60 u12_106 u15_119
  exact c124 h u1_121 u22_149 u25_150 u17_151 u26_152 u16_153 u21_154

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases085
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31303 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 7, 9} → Q {0, 1, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro a255 a140 a159 n96
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_4 : T {0, 1, 5} := by
    by_contra hv
    exact c56 h a140 hv
  have u6_6 : T {0, 1, 7} := by
    by_contra hv
    exact c84 h a140 hv
  have u7_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26047 h hv u0_2 u5_4 u6_6
  have u8_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u9_26 : T {0, 4, 9} := by
    by_contra hv
    exact c380 h a159 hv
  have u10_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u11_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u12_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1440 h hv n96
  have u13_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c20563 h a255 u4_9 hv
  have u14_32 : T {0, 6, 8} := by
    by_contra hv
    exact c20698 h a255 hv n96 u13_106
  have u15_81 : T {2, 6, 8} := by
    by_contra hv
    exact c20700 h a255 hv n96 u13_106
  have u16_119 : T {6, 8, 9} := by
    by_contra hv
    exact c4584 h a140 n96 u13_106 hv
  have u17_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20581 h a255 u14_32 hv
  have u18_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16605 h hv u14_32 u15_81 u16_119
  have u19_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16901 h hv u14_32 u15_81 u16_119
  have u20_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c20571 h a255 hv u15_81
  have u21_203 : Q {0, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 hv u7_294 u12_314 u16_119
  have u22_33 : T {0, 6, 9} := by
    by_contra hv
    exact c495 h u21_203 hv
  have u23_36 : T {0, 8, 9} := by
    by_contra hv
    exact c538 h u21_203 hv
  have u24_259 : Q {1, 6, 8, 9} := by
    by_contra hv
    exact c1774 h u21_203 hv u7_294 u12_314 u3_324 u2_328 u1_330
  have u25_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13757 h hv u9_26 u22_33 u23_36
  have u26_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14039 h hv u9_26 u22_33 u23_36
  have u27_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17535 h hv u10_15 u9_26 u22_33
  have u28_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18237 h hv u10_15 u9_26 u22_33
  have u29_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17257 h hv u10_15 u9_26 u23_36
  have u30_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17817 h hv u10_15 u9_26 u23_36
  have u31_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c21143 h u24_259 u4_9 u11_10 hv
  have u32_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c21145 h u24_259 u4_9 u11_10 hv
  have u33_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21214 h u24_259 u20_16 u17_65 hv
  have u34_88 : T {3, 4, 7} := by
    by_contra hv
    exact c21216 h u24_259 u20_16 u17_65 hv
  have u35_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18324 h hv u31_11 u13_106
  have u36_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u32_13 u13_106
  have u37_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c13379 h u21_203 hv u33_86 u34_88
  have u38_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c694 h hv u26_208 u19_228 u8_232 u30_235 u28_238 u35_239
  have u39_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c664 h hv u25_206 u18_226 u29_231 u8_232 u27_233 u36_234
  have u40_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c662 h hv u39_129 u25_206 u18_226 u29_231 u8_232 u27_233 u36_234
  have u41_47 : T {1, 3, 7} := by
    by_contra hv
    exact c13316 h u21_203 u37_44 u40_45 hv
  exact c692 h u41_47 u38_131 u26_208 u19_228 u8_232 u30_235 u28_238 u35_239

private theorem c31304 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → ¬ T {0, 2, 5} → T {4, 6, 8} → Q {1, 4, 5, 7} → ¬ T {3, 6, 8} → False := by
  classical
  intro a117 n11 a106 a242 n96
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19724 h hv n11 n96
  have u3_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h a242 u1_9 hv
  have u4_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16782 h hv n11 u3_119
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 a106 hv
  have u6_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1809 h u0_121 hv a117
  have u7_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1903 h u0_121 a106 hv a117
  have u8_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1890 h u0_121 u6_104 u5_115 hv
  have u9_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1886 h u0_121 u6_104 hv u5_115
  have u10_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14804 h hv n96 u7_112 u3_119
  have u11_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4024 h hv n96 u7_112 u3_119
  have u12_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19163 h hv u1_9 u8_116
  have u13_248 : ¬ Q {1, 4, 7, 8} := by
    intro hv
    exact c19583 h hv u1_9 u9_113
  exact c775 h a242 u11_136 u10_213 u4_228 u12_245 u13_248 u2_249

private theorem c31305 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 5} → ¬ Q {1, 2, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n11 n217 a159 n96
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_140 : Q {0, 1, 5, 7} := by
    by_contra hv
    exact c31302 h h0 hv n217 a159 n96
  have u7_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u8_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u9_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u1_9 u7_10 u8_15
  have u10_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u1_9 u7_10 u8_15
  have u11_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u12_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c31303 h h0 hv u6_140 a159 n96
  have u13_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c829 h u6_140 n217 u11_232 hv u10_251 u9_254 u12_255
  have u14_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h u13_242 u1_9 hv
  have u15_32 : T {0, 6, 8} := by
    by_contra hv
    exact c18862 h u13_242 hv n96 u14_119
  have u16_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c18757 h u13_242 u15_32 hv
  have u17_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c1038 h hv u16_70
  have u18_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c18767 h u13_242 u1_9 hv u8_15
  have u19_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c200 h hv u18_14
  have u20_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18765 h u13_242 u1_9 hv u8_15
  have u21_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c170 h hv u20_12
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c4584 h u6_140 n96 hv u14_119
  have u23_4 : T {0, 1, 5} := by
    by_contra hv
    exact c56 h u6_140 hv
  have u24_6 : T {0, 1, 7} := by
    by_contra hv
    exact c84 h u6_140 hv
  have u25_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24223 h hv u0_2 u23_4 u24_6
  have u26_56 : T {1, 5, 7} := by
    by_contra hv
    exact c7132 h a159 hv n96
  have u27_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u28_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c155 h hv n11
  have u29_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31304 h h0 hv n11 u22_106 u13_242 n96
  have u30_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1808 h u2_121 hv u29_117
  have u31_45 : T {1, 3, 5} := by
    by_contra hv
    exact c7122 h a159 hv u29_117
  have u32_60 : T {1, 6, 8} := by
    by_contra hv
    exact c7248 h a159 hv n96 u29_117
  have u33_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6157 h hv u32_60 u30_104
  have u34_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c7155 h a159 u31_45 u26_56 hv
  have u35_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c7151 h a159 u31_45 hv u26_56
  have u36_149 : Q {0, 2, 3, 4} := by
    by_contra hv
    exact c124 h u2_121 hv u28_150 u21_151 u33_152 u19_153 u17_154
  have u37_58 : T {1, 5, 9} := by
    by_contra hv
    exact c5746 h u36_149 u35_55 u34_57 hv
  have u38_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31297 h h0 u29_117 u36_149 hv u26_56 a159 u27_301 u14_119
  have u39_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11505 h hv u31_45 u26_56 u37_58
  exact c1581 h u38_246 u39_190 u25_281 u27_301 u5_317 u4_322 u3_324

theorem c31306 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n217 a159 n96
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u6_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u7_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u8_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u1_9 u6_10 u7_15
  have u9_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u1_9 u6_10 u7_15
  have u10_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u11_140 : Q {0, 1, 5, 7} := by
    by_contra hv
    exact c31302 h h0 hv n217 a159 n96
  have u12_4 : T {0, 1, 5} := by
    by_contra hv
    exact c56 h u11_140 hv
  have u13_6 : T {0, 1, 7} := by
    by_contra hv
    exact c84 h u11_140 hv
  have u14_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24223 h hv u0_2 u12_4 u13_6
  have u15_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c31303 h h0 hv u11_140 a159 n96
  have u16_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c829 h u11_140 n217 u5_232 hv u9_251 u8_254 u15_255
  have u17_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h u16_242 u1_9 hv
  have u18_106 : T {4, 6, 8} := by
    by_contra hv
    exact c4584 h u11_140 n96 hv u17_119
  have u19_11 : T {0, 2, 5} := by
    by_contra hv
    exact c31305 h h0 hv n217 a159 n96
  have u20_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19325 h hv u1_9 u19_11 u7_15
  have u21_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c1579 h hv u20_246 u14_281 u10_301 u4_317 u3_322 u2_324
  exact c1577 h u18_106 u21_190 u20_246 u14_281 u10_301 u4_317 u3_322 u2_324

theorem c31307 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 6, 8} → T {4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → False := by
  classical
  intro n246 a106 n301 n190
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c1577 h a106 n190 n246 hv n301 u0_317 u1_322 u2_324
  exact c1583 h u3_281 n190 n246 n301 u0_317 u1_322 u2_324

theorem c31308 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n119 a159 n96
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_217 : Q {1, 2, 5, 7} := by
    by_contra hv
    exact c31306 h h0 hv a159 n96
  have u6_41 : T {1, 2, 7} := by
    by_contra hv
    exact c609 h u5_217 hv
  have u7_39 : T {1, 2, 5} := by
    by_contra hv
    exact c581 h u5_217 hv
  have u8_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11483 h hv u1_37 u7_39 u6_41
  have u9_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1113 h a159 hv
  have u10_26 : T {0, 4, 9} := by
    by_contra hv
    exact c380 h a159 hv
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u12_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u13_16 : T {0, 3, 4} := by
    by_contra hv
    exact c15242 h u5_217 hv n119
  have u14_32 : T {0, 6, 8} := by
    by_contra hv
    exact c15360 h u5_217 hv n96 n119
  have u15_106 : T {4, 6, 8} := by
    by_contra hv
    exact c15364 h u5_217 n96 hv n119
  have u16_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c15273 h u5_217 u13_16 hv u10_26
  have u17_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c15257 h u5_217 u14_32 hv
  have u18_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 u15_106 hv
  have u19_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12723 h hv u1_37 u15_106
  have u20_100 : T {3, 8, 9} := by
    by_contra hv
    exact c15250 h u5_217 u16_23 hv
  have u21_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 hv u15_106 u12_301 u8_190
  have u22_51 : T {1, 4, 6} := by
    by_contra hv
    exact c763 h u21_246 hv
  have u23_60 : T {1, 6, 8} := by
    by_contra hv
    exact c894 h u21_246 hv
  have u24_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c1581 h u21_246 u8_190 hv u12_301 u4_317 u3_322 u2_324
  have u25_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c19309 h u21_246 u11_15 hv
  have u26_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7411 h hv u22_51 u20_100
  have u27_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9517 h hv u23_60 u9_75
  have u28_72 : T {2, 4, 6} := by
    by_contra hv
    exact c1078 h u24_281 hv
  have u29_28 : T {0, 5, 7} := by
    by_contra hv
    exact c19422 h u21_246 hv u25_92 u18_115
  have u30_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4471 h hv u28_72 u20_100
  have u31_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19317 h u21_246 u29_28 hv
  have u32_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c24217 h u24_281 u29_28 hv
  have u33_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12270 h hv u32_49 u31_70 u17_90
  have u34_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12690 h hv u32_49 u31_70 u17_90
  have u35_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c415 h hv u30_140 u26_161 u27_176 u33_195 u34_198 u19_199
  exact c407 h u29_28 u30_140 u26_161 u27_176 u35_186 u33_195 u34_198 u19_199

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases086
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31309 (h : TenSystem T Q) :
    ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 8, 9} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 3, 6, 8} → T {0, 6, 8} → False := by
  classical
  intro n196 n203 n165 n201 n190 n180 a32
  have u0_144 : Q {0, 1, 6, 8} := by
    by_contra hv
    exact c467 h a32 hv n165 n180 n190 n196 n201 n203
  exact c469 h u0_144 n165 n180 n190 n196 n201 n203

theorem c31310 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro a159 n96
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1440 h hv n96
  have u6_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c1428 h hv n96
  have u7_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u8_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u9_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1113 h a159 hv
  have u10_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u4_9 u7_10 u8_15
  have u11_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u4_9 u7_10 u8_15
  have u12_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u13_217 : Q {1, 2, 5, 7} := by
    by_contra hv
    exact c31306 h h0 hv a159 n96
  have u14_39 : T {1, 2, 5} := by
    by_contra hv
    exact c581 h u13_217 hv
  have u15_41 : T {1, 2, 7} := by
    by_contra hv
    exact c609 h u13_217 hv
  have u16_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11483 h hv u0_37 u14_39 u15_41
  have u17_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13307 h hv u0_37 u14_39 u15_41
  have u18_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31308 h h0 hv a159 n96
  have u19_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18743 h hv u4_9 u18_119
  have u20_294 : Q {2, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u17_203 hv u5_314 u18_119
  have u21_82 : T {2, 6, 9} := by
    by_contra hv
    exact c1230 h u20_294 hv
  have u22_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1273 h u20_294 hv
  have u23_259 : Q {1, 6, 8, 9} := by
    by_contra hv
    exact c1778 h u20_294 u17_203 hv u5_314 u3_324 u2_328 u1_330
  have u24_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4521 h hv u9_75 u21_82 u22_85
  have u25_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c21143 h u23_259 u4_9 u7_10 hv
  have u26_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c21145 h u23_259 u4_9 u7_10 hv
  have u27_255 : Q {1, 5, 7, 9} := by
    by_contra hv
    exact c831 h u13_217 u24_140 u12_232 u19_242 u10_251 u11_254 hv
  have u28_88 : T {3, 4, 7} := by
    by_contra hv
    exact c21126 h u23_259 u25_11 hv
  have u29_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21128 h u23_259 u26_13 hv
  have u30_58 : T {1, 5, 9} := by
    by_contra hv
    exact c868 h u27_255 hv
  have u31_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c20563 h u27_255 u4_9 hv
  have u32_32 : T {0, 6, 8} := by
    by_contra hv
    exact c20698 h u27_255 hv n96 u31_106
  have u33_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20581 h u27_255 u32_32 hv
  have u34_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7979 h hv u30_58 u28_88
  have u35_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c26121 h u20_294 hv u29_86 u28_88
  have u36_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c15257 h u13_217 u32_32 hv
  have u37_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12396 h hv u35_44 u33_65 u36_90
  have u38_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13096 h hv u35_44 u33_65 u36_90
  exact c31309 h u37_196 u17_203 u34_165 u38_201 u16_190 u6_180 u32_32

theorem c31320 (h : TenSystem T Q) :
    ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 9} → T {1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 3, 4, 5} → False := by
  classical
  intro n231 n232 n234 a45 n206 n233 n226
  have u0_129 : Q {0, 1, 3, 5} := by
    by_contra hv
    exact c662 h a45 hv n206 n226 n231 n232 n233 n234
  exact c664 h u0_129 n206 n226 n231 n232 n233 n234

theorem c31335 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {0, 5, 7, 9} → False := by
  classical
  intro a115 n310 n290 n199
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_255 : Q {1, 5, 7, 9} := by
    by_contra hv
    exact c1712 h a115 n199 hv n290 n310 u0_320 u1_327 u2_329
  exact c1716 h u3_255 n199 n290 n310 u0_320 u1_327 u2_329

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases087
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31390 (h : TenSystem T Q) :
    ¬ Q {1, 2, 6, 9} → T {1, 2, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 5, 9} → False := by
  classical
  intro n222 a43 n225 n224 n215 n210 n219
  have u0_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c632 h a43 hv n210 n215 n219 n222 n224 n225
  exact c634 h u0_127 n210 n215 n219 n222 n224 n225

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases089
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31421 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 5, 8} → T {4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → False := by
  classical
  intro n243 a103 n187 n278
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u2_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u3_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1540 h hv n187 n243 n278 u2_317 u1_319 u0_321
  exact c1532 h a103 n187 n243 n278 u3_298 u2_317 u1_319 u0_321

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases090
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31431 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 4, 7, 8} → T {0, 4, 8} → ¬ Q {0, 2, 4, 8} → False := by
  classical
  intro n173 n137 n187 n194 n192 a25 n158
  have u0_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c362 h a25 n137 n158 n173 n187 hv n192 n194
  exact c372 h u0_190 n137 n158 n173 n187 n192 n194

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases092
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31443 (h : TenSystem T Q) :
    ¬ Q {0, 3, 5, 8} → ¬ Q {0, 1, 5, 8} → T {0, 5, 8} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n177 n141 a29 n200 n162 n198 n196
  have u0_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c430 h hv n141 n162 n177 n196 n198 n200
  exact c422 h a29 n141 n162 n177 u0_187 n196 n198 n200

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases098
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31485 (h : TenSystem T Q) :
    ¬ Q {0, 3, 5, 9} → T {0, 3, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → False := by
  classical
  intro n178 a21 n183 n184 n133 n154 n174
  have u0_181 : Q {0, 3, 6, 9} := by
    by_contra hv
    exact c302 h a21 n133 n154 n174 n178 hv n183 n184
  exact c312 h u0_181 n133 n154 n174 n178 n183 n184

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases102
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31528 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 6, 7} → ¬ Q {3, 4, 5, 8} → ¬ T {3, 6, 7} → ¬ T {1, 3, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n31 n298 n95 n49 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv n118
  have u5_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23796 h hv n31 n49
  have u6_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c19002 h hv n31 n95 n118
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1534 h hv u6_243 u5_278 n298 u3_317 u2_319 u1_321
  exact c31421 h h0 u6_243 u4_103 u7_187 u5_278

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases103
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31532 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 4} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 1, 2, 8} → False := by
  classical
  intro n122 n125 n124 n127 n123 n126
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c4 h u0_121 n122 n123 n124 n125 n126 n127

theorem c31533 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 3, 5} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 1, 3, 6} → False := by
  classical
  intro n129 n132 n128 n133 n131 n130
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c19 h u0_121 n128 n129 n130 n131 n132 n133

theorem c31576 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → Q {3, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → False := by
  classical
  intro n249 n284 a304 n193
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1630 h a304 n193 n249 n284 u0_320 u1_323 u2_325

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases104
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31629 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  classical
  intro n102 n119
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1804 h u0_121 n102 n119

theorem c31631 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  classical
  intro n103 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1806 h u0_121 n103 n118

theorem c31633 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {6, 7, 8} → False := by
  classical
  intro n104 n117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1808 h u0_121 n104 n117

theorem c31634 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a104 a117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1809 h u0_121 a104 a117

theorem c31635 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ T {5, 8, 9} → False := by
  classical
  intro n105 n116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1810 h u0_121 n105 n116

theorem c31640 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a107 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1815 h u0_121 a107 a114

theorem c31641 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {5, 6, 9} → False := by
  classical
  intro n108 n113
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1816 h u0_121 n108 n113

theorem c31649 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → False := by
  classical
  intro n101 n102 n104
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1824 h u0_121 n101 n102 n104

theorem c31666 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  classical
  intro a102 a105 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1841 h u0_121 a102 a105 a109

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases105
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31670 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {4, 6, 7} → T {4, 7, 9} → False := by
  classical
  intro a108 a105 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1845 h u0_121 a105 a108 a109

theorem c31681 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {4, 8, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n104 n110 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1856 h u0_121 n104 n107 n110

theorem c31709 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n116 n114 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1884 h u0_121 n112 n114 n116

theorem c31712 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 9} → T {4, 5, 9} → T {5, 6, 9} → False := by
  classical
  intro a115 a104 a113
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1887 h u0_121 a104 a113 a115

theorem c31715 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {5, 7, 9} → ¬ T {5, 8, 9} → False := by
  classical
  intro n104 n115 n116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1890 h u0_121 n104 n115 n116

theorem c31720 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {5, 6, 7} → T {4, 6, 7} → False := by
  classical
  intro a117 a111 a105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1895 h u0_121 a105 a111 a117

theorem c31725 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {5, 6, 7} → ¬ T {6, 7, 9} → False := by
  classical
  intro n117 n111 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1900 h u0_121 n111 n117 n118

theorem c31732 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → T {6, 8, 9} → T {6, 7, 8} → False := by
  classical
  intro a106 a119 a117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1907 h u0_121 a106 a117 a119

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases106
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31750 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {7, 8, 9} → T {5, 7, 8} → False := by
  classical
  intro a117 a120 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1925 h u0_121 a114 a117 a120

theorem c31790 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 8} → T {1, 2, 7} → T {1, 2, 9} → False := by
  classical
  intro a187 a41 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11067 h a187 u0_37 a41 a43

theorem c31857 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 8, 9} → T {5, 6, 7} → False := by
  classical
  intro a194 a111
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12023 h a194 u0_37 a111

theorem c31877 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a196 a109
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12303 h a196 u0_37 a109

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases107
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31899 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a198 a38 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12605 h a198 u0_37 a38 a43

theorem c31905 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {2, 3, 4} → T {2, 3, 9} → False := by
  classical
  intro a198 a65 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12645 h a198 u0_37 a65 a70

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases108
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32374 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {3, 4, 5, 6} → T {1, 2, 8} → False := by
  classical
  intro a41 a296 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26363 h a296 u0_1 a41 a42

theorem c32397 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a299 a117
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26723 h a299 u0_1 a117

theorem c32427 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a302 a114
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27143 h a302 u0_1 a114

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases109
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32447 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a304 a112
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27423 h a304 u0_1 a112

theorem c32477 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a307 a109
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27843 h a307 u0_1 a109

theorem c32496 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 9} → T {1, 2, 7} → T {1, 2, 8} → False := by
  classical
  intro a308 a41 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28047 h a308 u0_1 a41 a42

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases110
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32572 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 4, 9} → ¬ Q {0, 3, 4, 5} → T {4, 8, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → T {5, 7, 8} → ¬ Q {0, 5, 8, 9} → T {0, 5, 8} → T {4, 7, 9} → False := by
  classical
  intro a265 n170 a110 n178 n162 n141 a114 n200 a29 a109
  have u0_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv a109
  have u1_65 : T {2, 3, 4} := by
    by_contra hv
    exact c975 h a265 hv
  have u2_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1042 h a265 hv
  have u3_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1117 h a265 hv
  have u4_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c21965 h a265 hv a114
  have u5_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c21975 h a265 a29 hv
  have u6_60 : T {1, 6, 8} := by
    by_contra hv
    exact c22034 h a265 u4_5 u5_59 hv
  have u7_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31905 h h0 hv u1_65 u2_70
  have u8_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c3011 h hv u3_75 a109 a110
  have u9_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9477 h hv u3_75 a109 a110
  have u10_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9517 h hv u6_60 u3_75
  have u11_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5873 h hv u6_60 a109
  have u12_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c31443 h hv n141 a29 n200 n162 u7_198 u0_196
  exact c254 h u12_177 u8_129 u11_150 n170 u9_175 u10_176 n178

theorem c32573 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 3, 4, 9} → T {6, 7, 8} → T {3, 6, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n174 a117 a95 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u2_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u2_116
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u5_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u2_116 hv u4_112
  have u6_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u7_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u2_116
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u6_88 u7_105 u0_109
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u6_88 u7_105 u0_109
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u1_29 hv
  have u11_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u7_105 u0_109
  have u12_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9784 h hv u10_40 u11_108
  have u13_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u5_114
  have u14_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv a117
  have u15_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u14_104 hv u13_107
  have u16_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31750 h h0 a117 hv u5_114
  have u17_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8662 h hv u10_40 u16_120
  have u18_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c32572 h h0 hv u17_170 u15_110 u12_178 u9_162 u8_141 u5_114 u3_200 u1_29 u0_109
  have u19_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u16_120
  have u20_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c1788 h hv u16_120
  have u21_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u7_105 u0_109
  have u22_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31649 h h0 hv u21_102 u14_104
  have u23_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7805 h hv a95 u7_105 a117
  have u24_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c4865 h hv a95 u7_105 a117
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31629 h h0 u21_102 hv
  have u26_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31732 h h0 hv u25_119 a117
  have u27_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31720 h h0 a117 hv u7_105
  have u28_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv a117
  have u29_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u30_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u29_118
  have u31_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2657 h hv a95 u30_103
  have u32_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10626 h hv u10_40 u21_102
  have u33_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u11_108 hv
  have u34_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u5_114
  have u35_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u6_88 u7_105 u0_109
  have u36_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u6_88 u7_105 u0_109
  have u37_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv u2_116
  have u38_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c735 h hv n49
  have u39_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u40_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c723 h hv n49
  have u41_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u42_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u41_99 u30_103
  have u43_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1349 h a304 n174 u39_230 u18_265 u28_299 u34_302 hv
  have u44_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u43_305 hv
  have u45_28 : T {0, 5, 7} := by
    by_contra hv
    exact c27578 h u43_305 hv u10_40
  have u46_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2367 h hv u44_89 u33_113
  have u47_122 : Q {0, 1, 2, 4} := by
    by_contra hv
    exact c31532 h h0 hv u46_125 u42_124 u31_127 u36_123 u35_126
  have u48_38 : T {1, 2, 4} := by
    by_contra hv
    exact c558 h u47_122 hv
  have u49_93 : T {3, 5, 8} := by
    by_contra hv
    exact c2020 h u47_122 hv u4_112 u2_116
  have u50_91 : T {3, 5, 6} := by
    by_contra hv
    exact c2002 h u47_122 hv u27_111 u4_112
  have u51_96 : ¬ T {3, 6, 8} := by
    intro hv
    exact c1971 h u47_122 u50_91 a95 hv
  have u52_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c1981 h u47_122 hv a95 u41_99
  have u53_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10203 h hv u48_38 u5_114
  have u54_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28841 h hv u45_28 u48_38
  have u55_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8233 h hv u49_93 u30_103 u5_114
  have u56_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5293 h hv u49_93 u30_103 u5_114
  have u57_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c31310 h h0 hv u51_96
  have u58_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5580 h hv u51_96 u26_106 u4_112
  have u59_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8520 h hv u51_96 u26_106 u4_112
  have u60_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12026 h hv u10_40 u52_92
  have u61_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8652 h hv u52_92 u21_102 u27_111
  have u62_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5712 h hv u52_92 u21_102 u27_111
  have u63_275 : Q {2, 3, 8, 9} := by
    by_contra hv
    exact c1495 h u43_305 u32_184 u38_240 hv u37_311 u54_314 u19_315
  have u64_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c216 h hv u31_127 u57_159 u23_163 u55_166 u59_168 u61_169
  have u65_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c539 h hv u62_148 u61_169 u32_184 u60_194 u3_200 u20_204
  have u66_138 : ¬ Q {0, 1, 4, 9} := by
    intro hv
    exact c113 h hv u31_127 u40_133 u24_142 u56_145 u58_147 u62_148
  have u67_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c527 h hv u62_148 u61_169 u32_184 u60_194 u3_200 u65_203 u20_204
  have u68_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c107 h hv u31_127 u40_133 u66_138 u24_142 u56_145 u58_147 u62_148
  have u69_276 : Q {2, 4, 5, 6} := by
    by_contra hv
    exact c31262 h h0 u63_275 hv u22_101
  have u70_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c314 h hv u40_133 u64_154 n174 u12_178 u53_181 u32_184
  have u71_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c31485 h u12_178 hv u70_183 u32_184 u40_133 u64_154 n174
  exact c23556 h u69_276 u68_8 u71_21 u67_36

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases111
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32574 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {3, 6, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a117 a95 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u1_116
  have u3_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u2_105 u0_109
  have u4_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31629 h h0 u3_102 hv
  have u5_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u2_105 u0_109
  have u6_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u5_108 hv
  have u7_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u8_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u1_116 hv u7_112
  have u9_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u8_114
  have u10_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c729 h hv n49
  have u11_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c723 h hv n49
  have u12_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u0_109
  have u13_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv a117
  have u14_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31720 h h0 a117 hv u2_105
  have u15_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31750 h h0 a117 hv u8_114
  have u16_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u13_104 hv u9_107
  have u17_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31649 h h0 hv u3_102 u13_104
  have u18_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1659 h hv u14_111
  have u19_174 : Q {0, 3, 4, 9} := by
    by_contra hv
    exact c32573 h h0 hv a117 a95 n49 a304
  have u20_26 : T {0, 4, 9} := by
    by_contra hv
    exact c382 h u19_174 hv
  have u21_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c9223 h u19_174 hv a117
  have u22_41 : T {1, 2, 7} := by
    by_contra hv
    exact c9226 h u19_174 hv u7_112
  have u23_42 : T {1, 2, 8} := by
    by_contra hv
    exact c9228 h u19_174 hv u14_111
  have u24_55 : T {1, 5, 6} := by
    by_contra hv
    exact c9318 h u19_174 hv u14_111 u7_112
  have u25_76 : T {2, 5, 6} := by
    by_contra hv
    exact c9320 h u19_174 hv u14_111 u7_112
  have u26_83 : ¬ T {2, 7, 8} := by
    intro hv
    exact c9361 h u19_174 hv u8_114 a117
  have u27_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22215 h hv u20_26 u0_109 u16_110
  have u28_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17315 h hv u20_26 u0_109 u16_110
  have u29_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13791 h hv u20_26 u0_109 u16_110
  have u30_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u21_39
  have u31_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9365 h hv u22_41 u16_110
  have u32_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c27437 h a304 hv u23_42
  have u33_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32374 h h0 u22_41 hv u23_42
  have u34_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32496 h h0 hv u22_41 u23_42
  have u35_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c27435 h a304 hv u24_55
  have u36_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3351 h hv u25_76 u0_109
  have u37_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3297 h hv u25_76 u17_101 u6_113
  have u38_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c2936 h hv u26_83 u9_107
  have u39_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3180 h hv u26_83 u5_108 u15_120
  have u40_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16607 h hv u30_32 a117 u4_119
  have u41_91 : ¬ T {3, 5, 6} := by
    intro hv
    exact c1352 h hv u31_175 u28_231 u27_266 u33_296 u18_306 u12_307 u34_308
  have u42_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17346 h hv u35_14 u9_107
  have u43_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c674 h hv u38_129 u29_206 u40_226 u28_231 u42_232 u10_234
  have u44_128 : Q {0, 1, 3, 4} := by
    by_contra hv
    exact c31533 h h0 u38_129 u36_132 hv u11_133 u37_131 u39_130
  have u45_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c31320 h u28_231 u42_232 u10_234 hv u29_206 u43_233 u40_226
  have u46_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19842 h hv u32_27 u41_91 u7_112
  have u47_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24742 h hv u32_27 u41_91 u7_112
  have u48_80 : T {2, 6, 7} := by
    by_contra hv
    exact c2790 h u44_128 hv u1_116
  have u49_81 : ¬ T {2, 6, 8} := by
    intro hv
    exact c2811 h u44_128 u25_76 u48_80 hv
  have u50_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11890 h hv u45_45 u49_81
  exact c31576 h h0 u46_249 u47_284 a304 u50_193

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases112
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32578 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 6, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a95 n49 a304
  have u0_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u2_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u1_116 hv u0_112
  have u3_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u2_114
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u1_116
  have u7_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u5_88 u6_105 u4_109
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u5_88 u6_105 u4_109
  have u9_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u1_116
  have u10_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u11_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u10_29 hv
  have u12_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15959 h hv u10_29 u5_88
  have u13_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c725 h hv n49
  have u14_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u15_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u14_118
  have u16_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u4_109
  have u17_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2657 h hv a95 u15_103
  have u18_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u10_29 a95
  have u19_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c32574 h h0 hv a95 n49 a304
  have u20_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31725 h h0 u19_117 hv u14_118
  have u21_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16501 h hv a95 u6_105 u20_111
  have u22_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32577 h h0 hv u19_117 n49 a304
  have u23_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c615 h hv u22_41
  have u24_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9646 h hv u22_41 u3_107
  have u25_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c640 h hv u17_127 u13_210 u18_215 u12_222 u23_224 u21_225
  have u26_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c31390 h u12_222 hv u21_225 u23_224 u18_215 u13_210 u25_219
  have u27_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u24_177 u8_141 u10_29 u9_200 u7_162 hv u16_196
  have u28_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11068 h hv u11_40 u22_41 u26_43
  exact c434 h u27_198 u8_141 u7_162 u24_177 u28_187 u16_196 u9_200

private theorem c32579 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n117 n49 a304
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u1_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32578 h h0 hv n49 a304
  have u2_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1950 h hv u1_95 u0_116
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u0_116
  have u5_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u4_105 u3_109
  have u6_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7968 h hv n49 u5_102
  have u7_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u4_105 u3_109
  have u8_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u7_108 hv
  have u9_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv u7_108
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u11_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u0_116 hv u10_112
  have u12_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u11_114
  have u13_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u14_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u13_88 u4_105 u3_109
  have u15_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u13_88 u4_105 u3_109
  have u16_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u13_88 u4_105 u3_109
  have u17_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u13_88 u4_105 u3_109
  have u18_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u0_116
  have u19_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u20_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u19_29 hv
  have u21_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u22_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u23_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u22_118
  have u24_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u21_99 u23_103
  have u25_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u3_109
  have u26_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u27_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c1743 h hv n117
  have u28_104 : T {4, 5, 9} := by
    by_contra hv
    exact c31633 h h0 hv n117
  have u29_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31725 h h0 n117 hv u22_118
  have u30_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32577 h h0 hv n117 n49 a304
  have u31_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31712 h h0 hv u28_104 u8_113
  have u32_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5137 h hv u26_90 u28_104 u3_109
  have u33_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c31857 h h0 hv u29_111
  have u34_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv u30_41
  have u35_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9646 h hv u30_41 u12_107
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9084 h hv u20_40 u31_115
  have u37_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c31532 h h0 u2_122 u34_125 u24_124 hv u17_123 u16_126
  have u38_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u35_177 u15_141 u19_29 u18_200 u14_162 hv u25_196
  have u39_43 : T {1, 2, 9} := by
    by_contra hv
    exact c633 h u37_127 hv
  have u40_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c2747 h u37_127 hv u29_111 u11_114
  have u41_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c2645 h u37_127 hv u11_114
  have u42_91 : T {3, 5, 6} := by
    by_contra hv
    exact c2678 h u37_127 u41_87 hv u1_95
  have u43_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c434 h u38_198 u15_141 u14_162 u35_177 hv u25_196 u18_200
  have u44_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31899 h h0 u38_198 hv u39_43
  have u45_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13284 h hv u44_38 u40_92
  have u46_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4141 h hv u42_91 u29_111 u8_113
  have u47_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7081 h hv u42_91 u29_111 u8_113
  have u48_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c370 h u43_187 u46_137 u47_158 u36_173 hv u9_192 u33_194
  have u49_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv u44_38 u31_115
  exact c475 h u48_190 u32_144 u6_165 u49_180 u25_196 u27_201 u45_203

private theorem c32580 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n41 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u2_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u2_116
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u5_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u2_116 hv u4_112
  have u6_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u7_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u2_116
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u6_88 u7_105 u0_109
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u6_88 u7_105 u0_109
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u1_29 hv
  have u11_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u7_105 u0_109
  have u12_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9784 h hv u10_40 u11_108
  have u13_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u5_114
  have u14_117 : T {6, 7, 8} := by
    by_contra hv
    exact c32579 h h0 hv n49 a304
  have u15_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u14_117
  have u16_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u15_104 hv u13_107
  have u17_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31750 h h0 u14_117 hv u5_114
  have u18_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8662 h hv u10_40 u17_120
  have u19_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c32572 h h0 hv u18_170 u16_110 u12_178 u9_162 u8_141 u5_114 u3_200 u1_29 u0_109
  have u20_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u14_117
  have u21_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32578 h h0 hv n49 a304
  have u22_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1950 h hv u21_95 u2_116
  have u23_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u5_114
  have u24_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u6_88 u7_105 u0_109
  have u25_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u6_88 u7_105 u0_109
  have u26_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u27_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u28_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u29_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u28_118
  have u30_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u27_99 u29_103
  have u31_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv n41
  have u32_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9226 h hv n41 u4_112
  have u33_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c31532 h h0 u22_122 u31_125 u30_124 hv u25_123 u24_126
  have u34_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1349 h a304 u32_174 u26_230 u19_265 u20_299 u23_302 hv
  have u35_86 : ¬ T {3, 4, 5} := by
    intro hv
    exact c2643 h u33_127 hv u14_117
  have u36_39 : T {1, 2, 5} := by
    by_contra hv
    exact c27628 h u34_305 hv u10_40 n41
  have u37_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1288 h hv u35_86
  have u38_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c27581 h u34_305 hv u36_39
  exact c31528 h h0 u38_31 u37_298 u21_95 n49 u28_118

private theorem c32581 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → T {1, 2, 7} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → T {4, 6, 7} → ¬ Q {0, 5, 8, 9} → T {0, 5, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro a43 a41 n162 n141 a105 n200 a29 n196
  have u0_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31790 h h0 hv a41 a43
  have u1_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9649 h hv a43 a105
  have u2_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c434 h hv n141 n162 u1_177 u0_187 n196 n200
  exact c31443 h u1_177 n141 a29 n200 n162 u2_198 n196

theorem c32582_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n49 a304
  have u0_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u2_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u1_118
  have u3_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u0_99 u2_103
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u4_109
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u7_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u8_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u9_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u8_29 hv
  have u10_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u11_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u10_116
  have u12_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u10_116
  have u13_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u10_116 hv u6_112
  have u14_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u7_88 u12_105 u4_109
  have u15_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u7_88 u12_105 u4_109
  have u16_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u7_88 u12_105 u4_109
  have u17_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u12_105 u4_109
  have u18_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u12_105 u4_109
  have u19_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u7_88 u12_105 u4_109
  have u20_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u13_114
  have u21_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv u17_108
  have u22_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u17_108 hv
  have u23_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31629 h h0 u18_102 hv
  have u24_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32578 h h0 hv n49 a304
  have u25_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1950 h hv u24_95 u10_116
  have u26_117 : T {6, 7, 8} := by
    by_contra hv
    exact c32579 h h0 hv n49 a304
  have u27_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u26_117
  have u28_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31720 h h0 u26_117 hv u12_105
  have u29_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31732 h h0 hv u23_119 u26_117
  have u30_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u27_104 hv u20_107
  have u31_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31715 h h0 u27_104 hv u10_116
  have u32_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c6988 h hv n49 u28_111
  have u33_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4164 h hv u24_95 u28_111 u1_118
  have u34_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c1578 h hv u29_106
  have u35_41 : T {1, 2, 7} := by
    by_contra hv
    exact c32580 h h0 hv n49 a304
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9087 h hv u35_41 u22_113
  have u37_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32581 h h0 hv u35_41 u19_162 u16_141 u12_105 u11_200 u8_29 u5_196
  have u38_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c633 h hv u37_43
  have u39_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11048 h hv u37_43 u24_95
  have u40_125 : Q {0, 1, 2, 7} := by
    by_contra hv
    exact c31532 h h0 u25_122 hv u3_124 u38_127 u14_123 u15_126
  have u41_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c376 h hv u33_137 u32_158 u36_173 u39_187 u34_190 u21_192
  have u42_89 : ¬ T {3, 4, 8} := by
    intro hv
    exact c2441 h u40_125 hv u2_103 u30_110
  have u43_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c31431 h u36_173 u33_137 u39_187 u41_194 u21_192 hv u32_158
  have u44_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12726 h hv u9_40 u42_89
  have u45_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28278 h hv u43_25 u9_40
  have u46_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25590 h hv u43_25 u42_89 u29_106
  exact c31335 h h0 u31_115 u45_310 u46_290 u44_199

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32582_oai := @OAI.BorsukNine.FiniteObstruction.c32582_oai
