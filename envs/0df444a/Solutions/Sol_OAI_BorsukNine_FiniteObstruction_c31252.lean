-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31252
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:07:07.653845+00:00
-- url     : https://prove2.me/submissions/a153fb76-8b23-4bfc-83bc-3eaa1661b146

import Mathlib
import Definitions.Def_OAIQ058B000

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

theorem c35 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {0, 1, 4} → False := by
  intro a128 n3
  exact n3 (h.down {0, 1, 3, 4} {0, 1, 4} a128 (by decide) (by decide))

theorem c50 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ T {0, 1, 5} → False := by
  intro a129 n4
  exact n4 (h.down {0, 1, 3, 5} {0, 1, 5} a129 (by decide) (by decide))

theorem c52 (h : TenSystem T Q) :
    Q {0, 1, 4, 5} → ¬ T {0, 1, 5} → False := by
  intro a134 n4
  exact n4 (h.down {0, 1, 4, 5} {0, 1, 5} a134 (by decide) (by decide))

theorem c56 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {0, 1, 5} → False := by
  intro a140 n4
  exact n4 (h.down {0, 1, 5, 7} {0, 1, 5} a140 (by decide) (by decide))

theorem c60 (h : TenSystem T Q) :
    Q {0, 1, 5, 9} → ¬ T {0, 1, 5} → False := by
  intro a142 n4
  exact n4 (h.down {0, 1, 5, 9} {0, 1, 5} a142 (by decide) (by decide))

theorem c63 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {0, 1, 6} → False := by
  intro a124 n5
  exact n5 (h.down {0, 1, 2, 6} {0, 1, 6} a124 (by decide) (by decide))

theorem c65 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {0, 1, 6} → False := by
  intro a130 n5
  exact n5 (h.down {0, 1, 3, 6} {0, 1, 6} a130 (by decide) (by decide))

theorem c80 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ T {0, 1, 7} → False := by
  intro a131 n6
  exact n6 (h.down {0, 1, 3, 7} {0, 1, 7} a131 (by decide) (by decide))

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

theorem c140 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {0, 2, 4} → False := by
  intro a149 n10
  exact n10 (h.down {0, 2, 3, 4} {0, 2, 4} a149 (by decide) (by decide))

theorem c142 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {0, 2, 4} → False := by
  intro a155 n10
  exact n10 (h.down {0, 2, 4, 5} {0, 2, 4} a155 (by decide) (by decide))

theorem c144 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {0, 2, 4} → False := by
  intro a156 n10
  exact n10 (h.down {0, 2, 4, 6} {0, 2, 4} a156 (by decide) (by decide))

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

theorem c228 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {0, 3, 4} → False := by
  intro a128 n16
  exact n16 (h.down {0, 1, 3, 4} {0, 3, 4} a128 (by decide) (by decide))

theorem c231 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 4, 9} → False := by
  intro a149 n128 n170 n171 n172 n173 n174
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 4} {0, 3, 4} a149 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 4} = {0, 3, 4, 5} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 4} = {0, 3, 4, 6} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 4} = {0, 3, 4, 7} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 4} = {0, 3, 4, 8} by decide)) hS)
  · exact n174 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 4} = {0, 3, 4, 9} by decide)) hS)

theorem c263 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 6, 9} → False := by
  intro a171 n130 n151 n175 n179 n180 n181
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 6} {0, 3, 6} a171 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n130 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n151 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n175 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n179 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 6} = {0, 3, 6, 7} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 6} = {0, 3, 6, 8} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 6} = {0, 3, 6, 9} by decide)) hS)

theorem c287 (h : TenSystem T Q) :
    T {0, 3, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a20 n132 n153 n173 n177 n180 n182 n184
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 8} a20
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n173 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c293 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a173 n132 n153 n177 n180 n182 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 8} {0, 3, 8} a173 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n177 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c300 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {0, 3, 8} → False := by
  intro a184 n20
  exact n20 (h.down {0, 3, 8, 9} {0, 3, 8} a184 (by decide) (by decide))

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

theorem c317 (h : TenSystem T Q) :
    T {0, 4, 5} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 9} → False := by
  intro a22 n134 n155 n170 n185 n186 n187 n188
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 5} a22
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n134 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact n170 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 5} = {0, 4, 5, 6} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 5} = {0, 4, 5, 7} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 5} = {0, 4, 5, 8} by decide)) hS)
  · exact n188 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 5} = {0, 4, 5, 9} by decide)) hS)

theorem c318 (h : TenSystem T Q) :
    Q {0, 1, 4, 5} → ¬ T {0, 4, 5} → False := by
  intro a134 n22
  exact n22 (h.down {0, 1, 4, 5} {0, 4, 5} a134 (by decide) (by decide))

theorem c322 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {0, 4, 5} → False := by
  intro a170 n22
  exact n22 (h.down {0, 3, 4, 5} {0, 4, 5} a170 (by decide) (by decide))

theorem c326 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ T {0, 4, 5} → False := by
  intro a186 n22
  exact n22 (h.down {0, 4, 5, 7} {0, 4, 5} a186 (by decide) (by decide))

theorem c329 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 5, 9} → False := by
  intro a187 n134 n155 n170 n185 n186 n188
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 4, 5} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n134 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact n170 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 5} = {0, 4, 5, 6} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 5} = {0, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n188 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 5} = {0, 4, 5, 9} by decide)) hS)

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

theorem c445 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {0, 5, 8, 9} → False := by
  intro a188 n142 n163 n178 n197 n199 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 9} {0, 5, 9} a188 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n142 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n197 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact n200 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c532 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a184 n36
  exact n36 (h.down {0, 3, 8, 9} {0, 8, 9} a184 (by decide) (by decide))

theorem c543 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {1, 2, 3} → False := by
  intro a121 n37
  exact n37 (h.down {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide))

theorem c544 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 2, 3, 9} → False := by
  intro a121 n205 n206 n207 n208 n209 n210
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 3} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 3} = {1, 2, 3, 4} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 3} = {1, 2, 3, 5} by decide)) hS)
  · exact n207 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 3} = {1, 2, 3, 6} by decide)) hS)
  · exact n208 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 3} = {1, 2, 3, 7} by decide)) hS)
  · exact n209 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 3} = {1, 2, 3, 8} by decide)) hS)
  · exact n210 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 3} = {1, 2, 3, 9} by decide)) hS)

theorem c560 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {1, 2, 4} → False := by
  intro a205 n38
  exact n38 (h.down {1, 2, 3, 4} {1, 2, 4} a205 (by decide) (by decide))

theorem c562 (h : TenSystem T Q) :
    Q {1, 2, 4, 5} → ¬ T {1, 2, 4} → False := by
  intro a211 n38
  exact n38 (h.down {1, 2, 4, 5} {1, 2, 4} a211 (by decide) (by decide))

theorem c564 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ T {1, 2, 4} → False := by
  intro a212 n38
  exact n38 (h.down {1, 2, 4, 6} {1, 2, 4} a212 (by decide) (by decide))

theorem c575 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {1, 2, 5} → False := by
  intro a206 n39
  exact n39 (h.down {1, 2, 3, 5} {1, 2, 5} a206 (by decide) (by decide))

theorem c579 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 5} → False := by
  intro a216 n39
  exact n39 (h.down {1, 2, 5, 6} {1, 2, 5} a216 (by decide) (by decide))

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

theorem c587 (h : TenSystem T Q) :
    T {1, 2, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a40 n124 n207 n212 n216 n220 n221 n222
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 6} a40
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

theorem c599 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 9} → False := by
  intro a221 n124 n207 n212 n216 n220 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 6, 8} {1, 2, 6} a221 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

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

theorem c720 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 3, 8} → False := by
  intro a240 n48
  exact n48 (h.down {1, 3, 8, 9} {1, 3, 8} a240 (by decide) (by decide))

theorem c725 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a210 n49
  exact n49 (h.down {1, 2, 3, 9} {1, 3, 9} a210 (by decide) (by decide))

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

theorem c737 (h : TenSystem T Q) :
    T {1, 4, 5} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 4, 5, 9} → False := by
  intro a50 n134 n211 n226 n241 n242 n243 n244
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 4, 5} a50
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n134 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact n226 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 5} = {1, 4, 5, 6} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 5} = {1, 4, 5, 7} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 5} = {1, 4, 5, 8} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 5} = {1, 4, 5, 9} by decide)) hS)

theorem c747 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 4, 5, 9} → False := by
  intro a242 n134 n211 n226 n241 n243 n244
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {1, 4, 5} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n134 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact n226 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 5} = {1, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n243 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 5} = {1, 4, 5, 8} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 5} = {1, 4, 5, 9} by decide)) hS)

theorem c749 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 4, 5, 9} → False := by
  intro a243 n134 n211 n226 n241 n242 n244
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 8} {1, 4, 5} a243 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n134 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact n226 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 5} = {1, 4, 5, 6} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 5} = {1, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n244 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 5} = {1, 4, 5, 9} by decide)) hS)

theorem c761 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  intro a245 n51
  exact n51 (h.down {1, 4, 6, 7} {1, 4, 6} a245 (by decide) (by decide))

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

theorem c850 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a243 n141 n218 n233 n252 n254 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 8} {1, 5, 8} a243 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c865 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 5, 8, 9} → False := by
  intro a244 n142 n219 n234 n253 n255 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 9} {1, 5, 9} a244 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n142 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n219 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c882 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 7, 9} → False := by
  intro a251 n143 n220 n235 n245 n257 n258
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 7} {1, 6, 7} a251 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n143 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 7} = {1, 6, 7, 8} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 7} = {1, 6, 7, 9} by decide)) hS)

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

theorem c947 (h : TenSystem T Q) :
    T {1, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a64 n148 n225 n240 n250 n256 n259 n260
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 8, 9} a64
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n148 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n225 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 8, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c952 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a240 n64
  exact n64 (h.down {1, 3, 8, 9} {1, 8, 9} a240 (by decide) (by decide))

theorem c962 (h : TenSystem T Q) :
    T {2, 3, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a65 n149 n205 n261 n262 n263 n264 n265
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 4} a65
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 4} = {2, 3, 4, 5} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 4} = {2, 3, 4, 6} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 4} = {2, 3, 4, 7} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c968 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a261 n149 n205 n262 n263 n264 n265
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 5} {2, 3, 4} a261 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 4} = {2, 3, 4, 6} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 4} = {2, 3, 4, 7} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c969 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {2, 3, 4} → False := by
  intro a262 n65
  exact n65 (h.down {2, 3, 4, 6} {2, 3, 4} a262 (by decide) (by decide))

theorem c970 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a262 n149 n205 n261 n263 n264 n265
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 6} {2, 3, 4} a262 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 4} = {2, 3, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 4} = {2, 3, 4, 7} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c977 (h : TenSystem T Q) :
    T {2, 3, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 5, 7} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 5, 9} → False := by
  intro a66 n150 n206 n261 n266 n267 n268 n269
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 5} a66
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n150 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 5} = {2, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 5} = {2, 3, 5, 6} by decide)) hS)
  · exact n267 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 5} = {2, 3, 5, 7} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 5} = {2, 3, 5, 8} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 5} = {2, 3, 5, 9} by decide)) hS)

theorem c983 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 5, 7} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 5, 9} → False := by
  intro a261 n150 n206 n266 n267 n268 n269
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 5} {2, 3, 5} a261 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n150 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 5} = {2, 3, 5, 6} by decide)) hS)
  · exact n267 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 5} = {2, 3, 5, 7} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 5} = {2, 3, 5, 8} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 5} = {2, 3, 5, 9} by decide)) hS)

theorem c985 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ Q {0, 2, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 5, 7} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 5, 9} → False := by
  intro a266 n150 n206 n261 n267 n268 n269
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 5, 6} {2, 3, 5} a266 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n150 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 5} = {2, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n267 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 5} = {2, 3, 5, 7} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 5} = {2, 3, 5, 8} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 5} = {2, 3, 5, 9} by decide)) hS)

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

theorem c995 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {2, 3, 6} → False := by
  intro a207 n67
  exact n67 (h.down {1, 2, 3, 6} {2, 3, 6} a207 (by decide) (by decide))

theorem c996 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 6, 9} → False := by
  intro a207 n151 n262 n266 n270 n271 n272
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 6} {2, 3, 6} a207 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n151 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 6} = {2, 3, 6, 7} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 6} = {2, 3, 6, 8} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 6} = {2, 3, 6, 9} by decide)) hS)

theorem c997 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {2, 3, 6} → False := by
  intro a262 n67
  exact n67 (h.down {2, 3, 4, 6} {2, 3, 6} a262 (by decide) (by decide))

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

theorem c1067 (h : TenSystem T Q) :
    T {2, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a72 n156 n212 n262 n276 n280 n281 n282
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 6} a72
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n280 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 6} = {2, 4, 6, 7} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

theorem c1077 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a280 n156 n212 n262 n276 n281 n282
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {2, 4, 6} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

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

theorem c1275 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {2, 8, 9} → False := by
  intro a295 n85
  exact n85 (h.down {2, 7, 8, 9} {2, 8, 9} a295 (by decide) (by decide))

theorem c1281 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {2, 3, 4, 5} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 4, 5, 9} → False := by
  intro a226 n170 n261 n296 n297 n298 n299
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 5} {3, 4, 5} a226 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n170 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 5} = {2, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 5} = {3, 4, 5, 6} by decide)) hS)
  · exact n297 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 5} = {3, 4, 5, 7} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 5} = {3, 4, 5, 8} by decide)) hS)
  · exact n299 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 5} = {3, 4, 5, 9} by decide)) hS)

theorem c1297 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {3, 4, 6} → False := by
  intro a262 n87
  exact n87 (h.down {2, 3, 4, 6} {3, 4, 6} a262 (by decide) (by decide))

theorem c1322 (h : TenSystem T Q) :
    T {3, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {1, 3, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 8, 9} → False := by
  intro a89 n173 n229 n264 n298 n301 n303 n305
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 8} a89
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n173 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 8} = {1, 3, 4, 8} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n303 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 8} = {3, 4, 8, 9} by decide)) hS)

theorem c1332 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {1, 3, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 8, 9} → False := by
  intro a301 n173 n229 n264 n298 n303 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 8} {3, 4, 8} a301 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n173 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 8} = {1, 3, 4, 8} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 8} = {3, 4, 8, 9} by decide)) hS)

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

theorem c1382 (h : TenSystem T Q) :
    T {3, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a93 n177 n233 n268 n298 n307 n309 n311
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 8} a93
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1384 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a177 n233 n268 n298 n307 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {3, 5, 8} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

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

theorem c1485 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {3, 7, 9} → False := by
  intro a315 n99
  exact n99 (h.down {3, 7, 8, 9} {3, 7, 9} a315 (by decide) (by decide))

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

theorem c1500 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a315 n100
  exact n100 (h.down {3, 7, 8, 9} {3, 8, 9} a315 (by decide) (by decide))

theorem c1501 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a315 n184 n240 n275 n305 n311 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 7, 8, 9} {3, 8, 9} a315 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1517 (h : TenSystem T Q) :
    T {4, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 7, 9} → False := by
  intro a102 n186 n242 n277 n297 n316 n319 n320
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 7} a102
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n186 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact n277 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n297 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 7} = {4, 5, 7, 8} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 7} = {4, 5, 7, 9} by decide)) hS)

theorem c1524 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a297 n102
  exact n102 (h.down {3, 4, 5, 7} {4, 5, 7} a297 (by decide) (by decide))

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

theorem c1637 (h : TenSystem T Q) :
    T {4, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {2, 4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a110 n194 n250 n285 n305 n321 n324 n325
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 8, 9} a110
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n194 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 8, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
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

theorem c1644 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a305 n110
  exact n110 (h.down {3, 4, 8, 9} {4, 8, 9} a305 (by decide) (by decide))

theorem c1671 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a252 n196 n287 n307 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 8} {5, 6, 8} a252 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1727 (h : TenSystem T Q) :
    T {5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a116 n200 n256 n291 n311 n321 n328 n329
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 8, 9} a116
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1728 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a200 n116
  exact n116 (h.down {0, 5, 8, 9} {5, 8, 9} a200 (by decide) (by decide))

theorem c1730 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a256 n116
  exact n116 (h.down {1, 5, 8, 9} {5, 8, 9} a256 (by decide) (by decide))

theorem c1731 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a256 n200 n291 n311 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 8, 9} {5, 8, 9} a256 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

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

theorem c1733 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a291 n200 n256 n311 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 8, 9} {5, 8, 9} a291 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1734 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a311 n116
  exact n116 (h.down {3, 5, 8, 9} {5, 8, 9} a311 (by decide) (by decide))

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

theorem c1779 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a314 n119
  exact n119 (h.down {3, 6, 8, 9} {6, 8, 9} a314 (by decide) (by decide))

theorem c1780 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a314 n203 n259 n294 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {6, 8, 9} a314 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1794 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a315 n120
  exact n120 (h.down {3, 7, 8, 9} {7, 8, 9} a315 (by decide) (by decide))

theorem c1795 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → ¬ Q {4, 7, 8, 9} → ¬ Q {5, 7, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a315 n204 n260 n295 n325 n329 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 7, 8, 9} {7, 8, 9} a315 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {7, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n204 (Eq.mp (congrArg Q (show insert (0 : Labels) {7, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (1 : Labels) {7, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact n295 (Eq.mp (congrArg Q (show insert (2 : Labels) {7, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (4 : Labels) {7, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (5 : Labels) {7, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact n330 (Eq.mp (congrArg Q (show insert (6 : Labels) {7, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1804 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  intro a121 n102 n119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n102 (hc.mpr n119)

theorem c1805 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {6, 8, 9} → False := by
  intro a121 a102 a119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a102 a119

theorem c1807 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {6, 7, 9} → False := by
  intro a121 a103 a118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a103 a118

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

theorem c1811 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {5, 8, 9} → False := by
  intro a121 a105 a116
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a105 a116

theorem c1814 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 7, 8} → False := by
  intro a121 n107 n114
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n107 (hc.mpr n114)

theorem c1816 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {5, 6, 9} → False := by
  intro a121 n108 n113
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n108 (hc.mpr n113)

theorem c1820 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {5, 6, 7} → False := by
  intro a121 n110 n111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n110 (hc.mpr n111)

theorem c1821 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 6, 7} → False := by
  intro a121 a110 a111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a110 a111

theorem c1822 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 8} → False := by
  intro a121 n101 n102 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c1824 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → False := by
  intro a121 n101 n102 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

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

theorem c1895 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a121 a105 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

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

theorem c1934 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {5, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n110 n116 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {8, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

theorem c1937 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a110 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c1939 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a110 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c1941 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a116 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c3063 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → T {2, 4, 5} → T {7, 8, 9} → False := by
  intro a130 a71 a120
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 5} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a120

theorem c3203 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 4, 5} → T {6, 8, 9} → False := by
  intro a131 a71 a119
  have hc := h.complementary {0, 1, 3, 7} {2, 4, 5} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a119

theorem c3343 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {6, 7, 9} → False := by
  intro a132 a71 a118
  have hc := h.complementary {0, 1, 3, 8} {2, 4, 5} a132 (by decide) (by decide)
  have he : ( {0, 1, 3, 8} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a118

theorem c3363 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {2, 4, 6} → T {2, 4, 7} → False := by
  intro a132 a71 a72 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 8} {2, 4} {5, 6, 7} a132 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

theorem c3371 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a132 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 8} {2, 5} {4, 6, 7} a132 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

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

theorem c3503 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 4, 6} → T {2, 4, 7} → False := by
  intro a133 a71 a72 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 4} {5, 6, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

theorem c3511 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a133 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 6, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

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

theorem c4611 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 4, 6} → T {3, 7, 9} → False := by
  intro a141 a72 a99
  have hc := h.complementary {0, 1, 5, 8} {2, 4, 6} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a99

theorem c4891 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {2, 4, 5} → T {3, 8, 9} → False := by
  intro a143 a71 a100
  have hc := h.complementary {0, 1, 6, 7} {2, 4, 5} a143 (by decide) (by decide)
  have he : ( {0, 1, 6, 7} : Finset Labels)ᶜ \ {2, 4, 5} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a100

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

theorem c5611 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → T {2, 3, 4} → T {2, 4, 5} → T {2, 4, 6} → False := by
  intro a148 a65 a71 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 8, 9} {2, 4} {3, 5, 6} a148 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c5723 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 6} → T {7, 8, 9} → False := by
  intro a149 a55 a120
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 6} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a55 a120

theorem c5863 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 4, 6} → T {7, 8, 9} → False := by
  intro a150 a51 a120
  have hc := h.complementary {0, 2, 3, 5} {1, 4, 6} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a120

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

theorem c5881 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 8, 9} → T {4, 6, 7} → False := by
  intro a150 a64 a105
  have hc := h.complementary {0, 2, 3, 5} {1, 8, 9} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 8, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a64 a105

theorem c6003 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 5} → T {7, 8, 9} → False := by
  intro a151 a50 a120
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 5} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a120

theorem c6144 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 4, 6} → ¬ T {5, 8, 9} → False := by
  intro a152 n51 n116
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n116)

theorem c6145 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 6} → T {5, 8, 9} → False := by
  intro a152 a51 a116
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a116

theorem c6283 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 5} → T {6, 7, 9} → False := by
  intro a153 a50 a118
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 5} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a118

theorem c6288 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 9} → ¬ T {5, 6, 7} → False := by
  intro a153 n54 n111
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 9} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n54 (hc.mpr n111)

theorem c6303 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 5} → T {1, 4, 6} → T {1, 4, 7} → False := by
  intro a153 a50 a51 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {1, 4} {5, 6, 7} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

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

theorem c6428 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 8} → ¬ T {5, 6, 7} → False := by
  intro a154 n53 n111
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n53 (hc.mpr n111)

theorem c6443 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 5} → T {1, 4, 6} → T {1, 4, 7} → False := by
  intro a154 a50 a51 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {1, 4} {5, 6, 7} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

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

theorem c7689 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 3, 8} → T {4, 6, 7} → False := by
  intro a163 a48 a105
  have hc := h.complementary {0, 2, 5, 9} {1, 3, 8} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a48 a105

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

theorem c8799 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → T {1, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a170 a64 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 5} {8, 9} {1, 6, 7} a170 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c8942 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 2, 5} → ¬ T {6, 8, 9} → False := by
  intro a172 n39 n119
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 5} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n119)

theorem c9151 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a173 a40 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {2, 6} {1, 5, 7} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

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

theorem c9291 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a174 a40 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {2, 6} {1, 5, 7} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c9364 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {1, 2, 7} → ¬ T {4, 8, 9} → False := by
  intro a175 n41 n110
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 7} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n110)

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

theorem c9782 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ T {1, 2, 4} → ¬ T {6, 7, 8} → False := by
  intro a178 n38 n117
  have hc := h.complementary {0, 3, 5, 9} {1, 2, 4} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n117)

theorem c9924 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {1, 2, 5} → ¬ T {4, 8, 9} → False := by
  intro a179 n39 n110
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 5} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n110)

theorem c10155 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 7} → False := by
  intro a180 a50 a71 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 8} {4, 5} {1, 2, 7} a180 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10295 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 7} → False := by
  intro a181 a50 a71 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 9} {4, 5} {1, 2, 7} a181 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10347 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 6} → T {4, 5, 9} → False := by
  intro a182 a40 a104
  have hc := h.complementary {0, 3, 7, 8} {1, 2, 6} a182 (by decide) (by decide)
  have he : ( {0, 3, 7, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a104

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

theorem c10627 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 6} → T {4, 5, 7} → False := by
  intro a184 a40 a102
  have hc := h.complementary {0, 3, 8, 9} {1, 2, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a40 a102

theorem c10635 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 7} → T {2, 5, 6} → False := by
  intro a184 a52 a76
  have hc := h.complementary {0, 3, 8, 9} {1, 4, 7} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a52 a76

theorem c10636 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 5, 6} → ¬ T {2, 4, 7} → False := by
  intro a184 n55 n73
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n55 (hc.mpr n73)

theorem c10637 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 6} → T {2, 4, 7} → False := by
  intro a184 a55 a73
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a55 a73

theorem c10638 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 5, 7} → ¬ T {2, 4, 6} → False := by
  intro a184 n56 n72
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 7} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n56 (hc.mpr n72)

theorem c10718 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 4, 5} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → False := by
  intro a184 n50 n101 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 8, 9} {4, 5} {1, 6, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)

theorem c10744 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a184 n76 n101 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 8, 9} {5, 6} {2, 4, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c10763 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {7, 8, 9} → False := by
  intro a185 a37 a120
  have hc := h.complementary {0, 4, 5, 6} {1, 2, 3} a185 (by decide) (by decide)
  have he : ( {0, 4, 5, 6} : Finset Labels)ᶜ \ {1, 2, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a120

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

theorem c10903 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {6, 8, 9} → False := by
  intro a186 a37 a119
  have hc := h.complementary {0, 4, 5, 7} {1, 2, 3} a186 (by decide) (by decide)
  have he : ( {0, 4, 5, 7} : Finset Labels)ᶜ \ {1, 2, 3} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a119

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

theorem c12092 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {1, 2, 5} → ¬ T {2, 3, 5} → ¬ T {2, 5, 7} → False := by
  intro a194 n39 n66 n77
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 8, 9} {2, 5} {1, 3, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n39 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 5} = {2, 3, 5} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) ht)

theorem c12103 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a194 a40 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {2, 6} {1, 5, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

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

theorem c12413 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 7, 9} → False := by
  intro a196 a49 a70 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {3, 9} {1, 2, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c12510 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → ¬ T {1, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a197 n38 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 9} {2, 4} {1, 3, 7} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

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

theorem c12735 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 3, 8} → T {2, 4, 6} → False := by
  intro a199 a48 a72
  have hc := h.complementary {0, 5, 7, 9} {1, 3, 8} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a48 a72

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

theorem c12911 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {1, 4, 6} → T {1, 6, 7} → False := by
  intro a200 a40 a51 a59
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 6} {2, 4, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) a59)

theorem c12932 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a200 n38 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {2, 4} {1, 3, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c12939 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {2, 3, 6} → T {2, 4, 6} → False := by
  intro a200 a40 a67 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {2, 6} {1, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)

theorem c13284 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 2, 4} → ¬ T {3, 5, 7} → False := by
  intro a203 n38 n92
  have hc := h.complementary {0, 6, 8, 9} {1, 2, 4} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n92)

theorem c13298 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 4, 7} → ¬ T {2, 3, 5} → False := by
  intro a203 n52 n66
  have hc := h.complementary {0, 6, 8, 9} {1, 4, 7} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n66)

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

theorem c13399 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 4, 5} → T {2, 4, 5} → T {3, 4, 5} → False := by
  intro a203 a50 a71 a86
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {4, 5} {1, 2, 3} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)

theorem c13497 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {2, 3, 4} → T {2, 4, 5} → T {2, 4, 6} → False := by
  intro a204 a65 a71 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 7, 8, 9} {2, 4} {3, 5, 6} a204 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c13563 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 6} → T {7, 8, 9} → False := by
  intro a205 a27 a120
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 6} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a120

theorem c13703 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 6} → T {7, 8, 9} → False := by
  intro a206 a23 a120
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 6} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a120

theorem c13844 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a207 n24 n116
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n116)

theorem c13982 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 4, 5} → ¬ T {6, 8, 9} → False := by
  intro a208 n22 n119
  have hc := h.complementary {1, 2, 3, 7} {0, 4, 5} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n119)

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

theorem c14122 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 5} → ¬ T {6, 7, 9} → False := by
  intro a209 n22 n118
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 5} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n118)

theorem c14125 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 6} → T {5, 7, 9} → False := by
  intro a209 a23 a115
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 6} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a115

theorem c14131 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 5, 6} → T {4, 7, 9} → False := by
  intro a209 a27 a109
  have hc := h.complementary {1, 2, 3, 8} {0, 5, 6} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a109

theorem c14139 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 6, 9} → T {4, 5, 7} → False := by
  intro a209 a33 a102
  have hc := h.complementary {1, 2, 3, 8} {0, 6, 9} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a33 a102

theorem c14159 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 6} → T {0, 5, 6} → T {0, 6, 7} → False := by
  intro a209 a23 a27 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 8} {0, 6} {4, 5, 7} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)

theorem c14184 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 5} → ¬ T {4, 5, 6} → ¬ T {4, 5, 9} → False := by
  intro a209 n22 n101 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 5} {0, 6, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c14262 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 5} → ¬ T {6, 7, 8} → False := by
  intro a210 n22 n117
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 5} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n117)

theorem c14265 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {5, 7, 8} → False := by
  intro a210 a23 a114
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a23 a114

theorem c14271 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 6} → T {4, 7, 8} → False := by
  intro a210 a27 a108
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a108

theorem c14279 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 6, 8} → T {4, 5, 7} → False := by
  intro a210 a32 a102
  have hc := h.complementary {1, 2, 3, 9} {0, 6, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a32 a102

theorem c14280 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 7, 8} → ¬ T {4, 5, 6} → False := by
  intro a210 n34 n101
  have hc := h.complementary {1, 2, 3, 9} {0, 7, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 7, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n34 (hc.mpr n101)

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

theorem c14299 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {0, 5, 6} → T {0, 6, 7} → False := by
  intro a210 a23 a27 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {0, 6} {4, 5, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)

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

theorem c15391 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 4, 6} → T {3, 7, 9} → False := by
  intro a218 a23 a99
  have hc := h.complementary {1, 2, 5, 8} {0, 4, 6} a218 (by decide) (by decide)
  have he : ( {1, 2, 5, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a99

theorem c15529 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 3, 8} → T {4, 6, 7} → False := by
  intro a219 a20 a105
  have hc := h.complementary {1, 2, 5, 9} {0, 3, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a20 a105

theorem c15662 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 3, 4} → ¬ T {5, 8, 9} → False := by
  intro a220 n16 n116
  have hc := h.complementary {1, 2, 6, 7} {0, 3, 4} a220 (by decide) (by decide)
  have he : ( {1, 2, 6, 7} : Finset Labels)ᶜ \ {0, 3, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n116)

theorem c15738 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 3, 8} → ¬ T {3, 4, 8} → ¬ T {3, 5, 8} → False := by
  intro a220 n20 n89 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 7} {3, 8} {0, 4, 5} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n20 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 8} = {0, 3, 8} by decide)) ht)
  · exact n89 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 8} = {3, 4, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 8} = {3, 5, 8} by decide)) ht)

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

theorem c16026 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {0, 3, 8} → ¬ T {3, 4, 8} → ¬ T {3, 5, 8} → False := by
  intro a222 n20 n89 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 9} {3, 8} {0, 4, 5} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n20 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 8} = {0, 3, 8} by decide)) ht)
  · exact n89 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 8} = {3, 4, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 8} = {3, 5, 8} by decide)) ht)

theorem c16465 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a225 a23 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {4, 6} {0, 3, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c16530 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ T {0, 2, 6} → ¬ T {0, 6, 7} → ¬ T {0, 6, 8} → False := by
  intro a226 n12 n31 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 5} {0, 6} {2, 7, 8} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n31 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) ht)

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

theorem c16639 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a226 a36 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {8, 9} {0, 6, 7} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c16923 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → T {0, 2, 5} → T {6, 7, 9} → False := by
  intro a229 a11 a118
  have hc := h.complementary {1, 3, 4, 8} {0, 2, 5} a229 (by decide) (by decide)
  have he : ( {1, 3, 4, 8} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a11 a118

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

theorem c17203 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 4} → T {7, 8, 9} → False := by
  intro a231 a10 a120
  have hc := h.complementary {1, 3, 5, 6} {0, 2, 4} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a120

theorem c17343 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 4} → T {6, 8, 9} → False := by
  intro a232 a10 a119
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 4} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a119

theorem c17351 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 4, 6} → T {2, 8, 9} → False := by
  intro a232 a23 a85
  have hc := h.complementary {1, 3, 5, 7} {0, 4, 6} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a85

theorem c17484 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 2, 6} → ¬ T {4, 7, 9} → False := by
  intro a233 n12 n109
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 6} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n109)

theorem c17511 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a233 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {0, 4} {2, 6, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c17577 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 9} → False := by
  intro a233 a23 a72 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 2, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

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

theorem c17622 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 4} → ¬ T {6, 7, 8} → False := by
  intro a234 n10 n117
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 4} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n117)

theorem c17651 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a234 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {0, 4} {2, 6, 7} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c17762 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 2, 4} → ¬ T {5, 8, 9} → False := by
  intro a235 n10 n116
  have hc := h.complementary {1, 3, 6, 7} {0, 2, 4} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n116)

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

theorem c18463 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {5, 6, 7} → False := by
  intro a240 a10 a111
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 4} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a10 a111

theorem c18465 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {4, 6, 7} → False := by
  intro a240 a11 a105
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a11 a105

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

theorem c18474 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 5, 6} → False := by
  intro a240 n24 n76
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n76)

theorem c18477 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 5, 6} → T {2, 4, 7} → False := by
  intro a240 a27 a73
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a27 a73

theorem c18478 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 5, 7} → ¬ T {2, 4, 6} → False := by
  intro a240 n28 n72
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n72)

theorem c18479 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 5, 7} → T {2, 4, 6} → False := by
  intro a240 a28 a72
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a28 a72

theorem c18481 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 6, 7} → T {2, 4, 5} → False := by
  intro a240 a31 a71
  have hc := h.complementary {1, 3, 8, 9} {0, 6, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a31 a71

theorem c18500 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 7} → False := by
  intro a240 n11 n22 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {0, 5} {2, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) ht)

theorem c18537 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a240 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 5} {4, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c18540 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → False := by
  intro a240 n12 n72 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 6} {0, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c18558 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → False := by
  intro a240 n22 n101 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 5} {0, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)

theorem c18565 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 7} → False := by
  intro a240 a23 a72 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 6} {0, 2, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c18568 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {2, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a240 n72 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 6} {2, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c18584 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a240 n76 n101 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {5, 6} {2, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c18603 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {7, 8, 9} → False := by
  intro a241 a9 a120
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 3} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a120

theorem c18743 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {6, 8, 9} → False := by
  intro a242 a9 a119
  have hc := h.complementary {1, 4, 5, 7} {0, 2, 3} a242 (by decide) (by decide)
  have he : ( {1, 4, 5, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a119

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

theorem c19023 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 3} → T {6, 7, 8} → False := by
  intro a244 a9 a117
  have hc := h.complementary {1, 4, 5, 9} {0, 2, 3} a244 (by decide) (by decide)
  have he : ( {1, 4, 5, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a117

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

theorem c19880 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {0, 6, 7} → ¬ T {2, 3, 5} → False := by
  intro a250 n31 n66
  have hc := h.complementary {1, 4, 8, 9} {0, 6, 7} a250 (by decide) (by decide)
  have he : ( {1, 4, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n66)

theorem c19899 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 5} → T {0, 3, 5} → T {0, 5, 6} → False := by
  intro a250 a11 a17 a27
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {0, 5} {2, 3, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 5} = {0, 5, 6} by decide)) a27)

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

theorem c20350 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a253 n10 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 9} {2, 4} {0, 3, 7} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

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

theorem c20437 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 4, 6} → T {2, 3, 9} → False := by
  intro a254 a23 a70
  have hc := h.complementary {1, 5, 7, 8} {0, 4, 6} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a70

theorem c20483 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 6} → False := by
  intro a254 a9 a65 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {2, 3} {0, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c20575 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 3, 8} → T {2, 4, 6} → False := by
  intro a255 a20 a72
  have hc := h.complementary {1, 5, 7, 9} {0, 3, 8} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a20 a72

theorem c20623 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 6} → False := by
  intro a255 a9 a65 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 9} {2, 3} {0, 4, 6} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c20720 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {2, 3, 4} → False := by
  intro a256 n31 n65
  have hc := h.complementary {1, 5, 8, 9} {0, 6, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 4} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n65)

theorem c20743 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a256 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {0, 4} {2, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c20763 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 6} → False := by
  intro a256 a9 a65 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {2, 3} {0, 4, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c20772 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a256 n10 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {2, 4} {0, 3, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

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

theorem c20878 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → ¬ T {0, 4, 5} → False := by
  intro a257 n10 n16 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 8} {0, 4} {2, 3, 5} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c21018 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → ¬ T {0, 4, 5} → False := by
  intro a258 n10 n16 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {0, 4} {2, 3, 5} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c21124 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {3, 5, 7} → False := by
  intro a259 n10 n92
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 4} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n92)

theorem c21158 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → ¬ T {0, 4, 5} → False := by
  intro a259 n10 n16 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {0, 4} {2, 3, 5} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c21195 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 4} → T {2, 4, 5} → T {2, 4, 7} → False := by
  intro a259 a10 a71 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {2, 4} {0, 5, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

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

theorem c21337 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {2, 3, 4} → T {2, 4, 5} → T {2, 4, 6} → False := by
  intro a260 a65 a71 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 7, 8, 9} {2, 4} {3, 5, 6} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c21404 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ T {0, 1, 7} → ¬ T {6, 8, 9} → False := by
  intro a261 n6 n119
  have hc := h.complementary {2, 3, 4, 5} {0, 1, 7} a261 (by decide) (by decide)
  have he : ( {2, 3, 4, 5} : Finset Labels)ᶜ \ {0, 1, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n119)

theorem c21405 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → T {0, 1, 7} → T {6, 8, 9} → False := by
  intro a261 a6 a119
  have hc := h.complementary {2, 3, 4, 5} {0, 1, 7} a261 (by decide) (by decide)
  have he : ( {2, 3, 4, 5} : Finset Labels)ᶜ \ {0, 1, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a119

theorem c21523 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → T {0, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a261 a34 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 5} {7, 8} {0, 6, 9} a261 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 8} = {0, 7, 8} by decide)) a34)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c21543 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 1, 5} → T {7, 8, 9} → False := by
  intro a262 a4 a120
  have hc := h.complementary {2, 3, 4, 6} {0, 1, 5} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 1, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a4 a120

theorem c21544 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {0, 1, 7} → ¬ T {5, 8, 9} → False := by
  intro a262 n6 n116
  have hc := h.complementary {2, 3, 4, 6} {0, 1, 7} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n116)

theorem c21545 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 1, 7} → T {5, 8, 9} → False := by
  intro a262 a6 a116
  have hc := h.complementary {2, 3, 4, 6} {0, 1, 7} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a116

theorem c21682 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 1, 5} → ¬ T {6, 8, 9} → False := by
  intro a263 n4 n119
  have hc := h.complementary {2, 3, 4, 7} {0, 1, 5} a263 (by decide) (by decide)
  have he : ( {2, 3, 4, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n119)

theorem c21684 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 1, 6} → ¬ T {5, 8, 9} → False := by
  intro a263 n5 n116
  have hc := h.complementary {2, 3, 4, 7} {0, 1, 6} a263 (by decide) (by decide)
  have he : ( {2, 3, 4, 7} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n116)

theorem c21822 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 5} → ¬ T {6, 7, 9} → False := by
  intro a264 n4 n118
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 5} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n118)

theorem c21824 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 6} → ¬ T {5, 7, 9} → False := by
  intro a264 n5 n115
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 6} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n115)

theorem c21827 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → T {0, 1, 7} → T {5, 6, 9} → False := by
  intro a264 a6 a113
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 7} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a113

theorem c21842 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a264 n4 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 8} {0, 1} {5, 6, 7} a264 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c21962 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 5} → ¬ T {6, 7, 8} → False := by
  intro a265 n4 n117
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 5} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n117)

theorem c21964 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 6} → ¬ T {5, 7, 8} → False := by
  intro a265 n5 n114
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 6} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n114)

theorem c21982 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a265 n4 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {0, 1} {5, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

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

theorem c22103 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 1, 4} → T {7, 8, 9} → False := by
  intro a266 a3 a120
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 4} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a120

theorem c22104 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 1, 7} → ¬ T {4, 8, 9} → False := by
  intro a266 n6 n110
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n110)

theorem c22105 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 1, 7} → T {4, 8, 9} → False := by
  intro a266 a6 a110
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a110

theorem c22242 (h : TenSystem T Q) :
    Q {2, 3, 5, 7} → ¬ T {0, 1, 4} → ¬ T {6, 8, 9} → False := by
  intro a267 n3 n119
  have hc := h.complementary {2, 3, 5, 7} {0, 1, 4} a267 (by decide) (by decide)
  have he : ( {2, 3, 5, 7} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n119)

theorem c22244 (h : TenSystem T Q) :
    Q {2, 3, 5, 7} → ¬ T {0, 1, 6} → ¬ T {4, 8, 9} → False := by
  intro a267 n5 n110
  have hc := h.complementary {2, 3, 5, 7} {0, 1, 6} a267 (by decide) (by decide)
  have he : ( {2, 3, 5, 7} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n110)

theorem c22382 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 4} → ¬ T {6, 7, 9} → False := by
  intro a268 n3 n118
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 4} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n118)

theorem c22383 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 1, 4} → T {6, 7, 9} → False := by
  intro a268 a3 a118
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 4} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a118

theorem c22402 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 4} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a268 n3 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {0, 1} {4, 6, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c22475 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 7} → False := by
  intro a268 a23 a51 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 6} {0, 1, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c22522 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 1, 4} → ¬ T {6, 7, 8} → False := by
  intro a269 n3 n117
  have hc := h.complementary {2, 3, 5, 9} {0, 1, 4} a269 (by decide) (by decide)
  have he : ( {2, 3, 5, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n117)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases061
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

theorem c22542 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 1, 4} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a269 n3 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 9} {0, 1} {4, 6, 7} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c22615 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 7} → False := by
  intro a269 a23 a51 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {4, 6} {0, 1, 7} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c22663 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 4} → T {5, 8, 9} → False := by
  intro a270 a3 a116
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 4} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a116

theorem c22664 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 5} → ¬ T {4, 8, 9} → False := by
  intro a270 n4 n110
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 5} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n110)

theorem c22665 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 5} → T {4, 8, 9} → False := by
  intro a270 a4 a110
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 5} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a4 a110

theorem c22670 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 4, 5} → ¬ T {1, 8, 9} → False := by
  intro a270 n22 n64
  have hc := h.complementary {2, 3, 6, 7} {0, 4, 5} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n64)

theorem c22723 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 8} → False := by
  intro a270 a3 a50 a53
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {1, 4} {0, 5, 8} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 4} = {1, 4, 8} by decide)) a53)

theorem c22725 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 9} → False := by
  intro a270 a3 a50 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {1, 4} {0, 5, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c22838 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 7} → False := by
  intro a271 n4 n22 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 8} {0, 5} {1, 4, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) ht)

theorem c22847 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 7} → T {0, 4, 7} → T {0, 5, 7} → False := by
  intro a271 a6 a24 a28
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {0, 7} {1, 4, 5} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) a6)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)

theorem c22863 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 7} → False := by
  intro a271 a3 a50 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {1, 4} {0, 5, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

theorem c22871 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 7} → False := by
  intro a271 a4 a50 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {1, 5} {0, 4, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases062
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

theorem c22978 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → ¬ T {0, 1, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 7} → False := by
  intro a272 n4 n22 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 9} {0, 5} {1, 4, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) ht)

theorem c22987 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 1, 7} → T {0, 4, 7} → T {0, 5, 7} → False := by
  intro a272 a6 a24 a28
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {0, 7} {1, 4, 5} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) a6)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)

theorem c23003 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 7} → False := by
  intro a272 a3 a50 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {1, 4} {0, 5, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

theorem c23011 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 7} → False := by
  intro a272 a4 a50 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {1, 5} {0, 4, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

theorem c23366 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 1, 6} → ¬ T {4, 5, 7} → False := by
  intro a275 n5 n102
  have hc := h.complementary {2, 3, 8, 9} {0, 1, 6} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n102)

theorem c23368 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 1, 7} → ¬ T {4, 5, 6} → False := by
  intro a275 n6 n101
  have hc := h.complementary {2, 3, 8, 9} {0, 1, 7} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n101)

theorem c23370 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 6, 7} → False := by
  intro a275 n22 n59
  have hc := h.complementary {2, 3, 8, 9} {0, 4, 5} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 6, 7} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n59)

theorem c23374 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 5, 6} → False := by
  intro a275 n24 n55
  have hc := h.complementary {2, 3, 8, 9} {0, 4, 7} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n55)

theorem c23465 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 7} → False := by
  intro a275 a23 a51 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {4, 6} {0, 1, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c23503 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {7, 8, 9} → False := by
  intro a276 a2 a120
  have hc := h.complementary {2, 4, 5, 6} {0, 1, 3} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 1, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a120

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

theorem c23650 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {0, 3, 6} → ¬ T {1, 8, 9} → False := by
  intro a277 n18 n64
  have hc := h.complementary {2, 4, 5, 7} {0, 3, 6} a277 (by decide) (by decide)
  have he : ( {2, 4, 5, 7} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n64)

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

theorem c24319 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 5, 7} → T {1, 5, 7} → T {3, 5, 7} → False := by
  intro a281 a28 a56 a92
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {5, 7} {0, 1, 3} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)

theorem c24459 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 5, 7} → T {1, 5, 7} → T {3, 5, 7} → False := by
  intro a282 a28 a56 a92
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {5, 7} {0, 1, 3} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)

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

theorem c24785 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 7} → False := by
  intro a285 a2 a4 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {0, 1} {3, 5, 7} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c24803 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 1, 5} → T {0, 5, 6} → T {0, 5, 7} → False := by
  intro a285 a4 a27 a28
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {0, 5} {1, 6, 7} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 5} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) a28)

theorem c25045 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 4} → T {3, 7, 9} → False := by
  intro a287 a3 a99
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 4} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a99

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

theorem c25625 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a291 a2 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {0, 1} {3, 4, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c25643 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a291 a3 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {0, 4} {1, 6, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c26031 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 3, 4} → T {1, 5, 7} → False := by
  intro a294 a16 a56
  have hc := h.complementary {2, 6, 8, 9} {0, 3, 4} a294 (by decide) (by decide)
  have he : ( {2, 6, 8, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {1, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a16 a56

theorem c26045 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a294 a2 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {0, 1} {3, 4, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

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

theorem c26103 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 7} → False := by
  intro a294 a4 a50 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {1, 5} {0, 4, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

theorem c26168 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {0, 1, 6} → ¬ T {3, 4, 5} → False := by
  intro a295 n5 n86
  have hc := h.complementary {2, 7, 8, 9} {0, 1, 6} a295 (by decide) (by decide)
  have he : ( {2, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {3, 4, 5} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n86)

theorem c26172 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {0, 3, 5} → ¬ T {1, 4, 6} → False := by
  intro a295 n17 n51
  have hc := h.complementary {2, 7, 8, 9} {0, 3, 5} a295 (by decide) (by decide)
  have he : ( {2, 7, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n51)

theorem c26175 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 3, 6} → T {1, 4, 5} → False := by
  intro a295 a18 a50
  have hc := h.complementary {2, 7, 8, 9} {0, 3, 6} a295 (by decide) (by decide)
  have he : ( {2, 7, 8, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a18 a50

theorem c26259 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 3, 4} → T {3, 4, 5} → T {3, 4, 6} → False := by
  intro a295 a16 a86 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 7, 8, 9} {3, 4} {0, 5, 6} a295 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)

theorem c26303 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {7, 8, 9} → False := by
  intro a296 a1 a120
  have hc := h.complementary {3, 4, 5, 6} {0, 1, 2} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 1, 2} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a120

theorem c26450 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {0, 2, 6} → ¬ T {1, 8, 9} → False := by
  intro a297 n12 n64
  have hc := h.complementary {3, 4, 5, 7} {0, 2, 6} a297 (by decide) (by decide)
  have he : ( {3, 4, 5, 7} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n64)

theorem c26583 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {6, 7, 9} → False := by
  intro a298 a1 a118
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 2} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a118

theorem c26643 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a298 a1 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 2} {0, 6, 7} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

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

theorem c26783 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a299 a1 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {1, 2} {0, 6, 7} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

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

theorem c27300 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {0, 6, 9} → ¬ T {1, 2, 5} → False := by
  intro a303 n33 n39
  have hc := h.complementary {3, 4, 7, 8} {0, 6, 9} a303 (by decide) (by decide)
  have he : ( {3, 4, 7, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n39)

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

theorem c27569 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 7} → T {2, 5, 6} → False := by
  intro a305 a6 a76
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a6 a76

theorem c27572 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 2, 6} → ¬ T {1, 5, 7} → False := by
  intro a305 n12 n56
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 6} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 7} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n56)

theorem c27580 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 6, 7} → ¬ T {1, 2, 5} → False := by
  intro a305 n31 n39
  have hc := h.complementary {3, 4, 8, 9} {0, 6, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n39)

theorem c27588 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a305 n4 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {0, 1} {5, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c27863 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a307 a1 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 1} {2, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

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

theorem c28140 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 6, 9} → ¬ T {1, 2, 4} → False := by
  intro a309 n33 n38
  have hc := h.complementary {3, 5, 7, 8} {0, 6, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n38)

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

theorem c28404 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 1, 4} → ¬ T {2, 6, 7} → False := by
  intro a311 n3 n80
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 4} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n80)

theorem c28412 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 6} → ¬ T {1, 4, 7} → False := by
  intro a311 n12 n52
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n52)

theorem c28417 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 4, 6} → T {1, 2, 7} → False := by
  intro a311 a23 a41
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a23 a41

theorem c28420 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {1, 2, 4} → False := by
  intro a311 n31 n38
  have hc := h.complementary {3, 5, 8, 9} {0, 6, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n38)

theorem c28425 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a311 a1 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 1} {2, 4, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c28428 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a311 n3 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {0, 1} {4, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

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

theorem c28823 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {4, 5, 7} → False := by
  intro a314 a1 a102
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 2} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a102

theorem c28826 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 1, 5} → ¬ T {2, 4, 7} → False := by
  intro a314 n4 n73
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 5} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n73)

theorem c28829 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 7} → T {2, 4, 5} → False := by
  intro a314 a6 a71
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a6 a71

theorem c28830 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {1, 5, 7} → False := by
  intro a314 n10 n56
  have hc := h.complementary {3, 6, 8, 9} {0, 2, 4} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n56)

theorem c28836 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 2, 7} → False := by
  intro a314 n22 n41
  have hc := h.complementary {3, 6, 8, 9} {0, 4, 5} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n41)

theorem c28838 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 2, 5} → False := by
  intro a314 n24 n39
  have hc := h.complementary {3, 6, 8, 9} {0, 4, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n39)

theorem c28840 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 5, 7} → ¬ T {1, 2, 4} → False := by
  intro a314 n28 n38
  have hc := h.complementary {3, 6, 8, 9} {0, 5, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n38)

theorem c28845 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a314 a1 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {0, 1} {2, 4, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c28924 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 2, 5} → ¬ T {1, 2, 5} → ¬ T {2, 5, 7} → False := by
  intro a314 n11 n39 n77
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 8, 9} {2, 5} {0, 1, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) ht)

theorem c28963 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {4, 5, 6} → False := by
  intro a315 a1 a101
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 2} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a1 a101

theorem c28964 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {2, 5, 6} → False := by
  intro a315 n3 n76
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 4} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n76)

theorem c28965 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 4} → T {2, 5, 6} → False := by
  intro a315 a3 a76
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 4} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a3 a76

theorem c28966 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 5} → ¬ T {2, 4, 6} → False := by
  intro a315 n4 n72
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 5} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n72)

theorem c28968 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 6} → ¬ T {2, 4, 5} → False := by
  intro a315 n5 n71
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 4, 5} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n71)

theorem c28969 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 6} → T {2, 4, 5} → False := by
  intro a315 a5 a71
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a5 a71

theorem c28971 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 4} → T {1, 5, 6} → False := by
  intro a315 a10 a55
  have hc := h.complementary {3, 7, 8, 9} {0, 2, 4} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a10 a55

theorem c28975 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 6} → T {1, 4, 5} → False := by
  intro a315 a12 a50
  have hc := h.complementary {3, 7, 8, 9} {0, 2, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a12 a50

theorem c28976 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 2, 6} → False := by
  intro a315 n22 n40
  have hc := h.complementary {3, 7, 8, 9} {0, 4, 5} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n40)

theorem c28978 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 6} → ¬ T {1, 2, 5} → False := by
  intro a315 n23 n39
  have hc := h.complementary {3, 7, 8, 9} {0, 4, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n39)

theorem c28980 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 5, 6} → ¬ T {1, 2, 4} → False := by
  intro a315 n27 n38
  have hc := h.complementary {3, 7, 8, 9} {0, 5, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n38)

theorem c28981 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 5, 6} → T {1, 2, 4} → False := by
  intro a315 a27 a38
  have hc := h.complementary {3, 7, 8, 9} {0, 5, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a27 a38

theorem c28983 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 5} → False := by
  intro a315 a1 a3 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 1} {2, 4, 5} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c28985 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 6} → False := by
  intro a315 a1 a3 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 1} {2, 4, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c28988 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → False := by
  intro a315 n3 n4 n5
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 1} {4, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)

theorem c28998 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 4, 5} → False := by
  intro a315 n3 n10 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 4} {1, 2, 5} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c29001 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 4} → T {0, 2, 4} → T {0, 4, 6} → False := by
  intro a315 a3 a10 a23
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 4} {1, 2, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)

theorem c29002 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 4, 5} → ¬ T {0, 4, 6} → False := by
  intro a315 n3 n22 n23
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 4} {1, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) ht)

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

theorem c29004 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 2, 4} → ¬ T {0, 4, 5} → ¬ T {0, 4, 6} → False := by
  intro a315 n10 n22 n23
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 4} {2, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) ht)

theorem c29025 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a315 a1 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {1, 2} {0, 4, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c29027 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a315 a1 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {1, 2} {0, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c29032 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {1, 2, 4} → ¬ T {1, 4, 6} → False := by
  intro a315 n3 n38 n51
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {1, 4} {0, 2, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) ht)
  · exact n38 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) ht)

theorem c29035 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 6} → False := by
  intro a315 a3 a50 a51
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {1, 4} {0, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)

theorem c29064 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 2, 5} → ¬ T {1, 2, 5} → ¬ T {2, 5, 6} → False := by
  intro a315 n11 n39 n76
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {2, 5} {0, 1, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) ht)

theorem c29067 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a315 a11 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {2, 5} {0, 4, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c29071 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 6} → T {1, 2, 6} → T {2, 4, 6} → False := by
  intro a315 a12 a40 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {2, 6} {0, 1, 4} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)

theorem c29074 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 5, 6} → False := by
  intro a315 n12 n72 n76
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {2, 6} {0, 4, 5} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) ht)

theorem c29077 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {1, 2, 6} → T {2, 4, 6} → T {2, 5, 6} → False := by
  intro a315 a40 a72 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {2, 6} {1, 4, 5} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)

theorem c29080 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 4, 5} → ¬ T {4, 5, 6} → False := by
  intro a315 n22 n50 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {4, 5} {0, 1, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)

theorem c29082 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 6} → False := by
  intro a315 n22 n71 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {4, 5} {0, 2, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)

theorem c29095 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 5, 6} → T {1, 5, 6} → T {2, 5, 6} → False := by
  intro a315 a27 a55 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {5, 6} {0, 1, 2} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)

theorem c29098 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → False := by
  intro a315 n27 n76 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {5, 6} {0, 2, 4} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)

theorem c29100 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {1, 5, 6} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → False := by
  intro a315 n55 n76 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {5, 6} {1, 2, 4} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n55 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)

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

theorem c30523 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a326 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 8} {0, 1} {2, 3, 4} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

theorem c30531 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a326 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 8} {0, 2} {1, 3, 4} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

theorem c30539 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a326 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 8} {0, 3} {1, 2, 4} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

theorem c30546 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a326 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 6, 7, 8} {0, 4} {1, 2, 3} a326 (by decide) (by decide) (by decide) (by decide)
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

theorem c31211 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 6, 7, 8} → False := by
  classical
  intro a326
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
    exact c30523 h a326 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30531 h a326 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30539 h a326 u1_2 u2_9 hv
  exact c30546 h a326 u3_3 u4_10 u5_16

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

theorem c31226 (h : TenSystem T Q) :
    ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → ¬ Q {0, 2, 4, 6} → T {2, 4, 6} →
      ¬ Q {2, 4, 5, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → False := by
  classical
  intro n281 n282 n156 a72 n276 n212 n262
  have u0_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c1067 h a72 n156 n212 n262 n276 hv n281 n282
  exact c1077 h u0_280 n156 n212 n262 n276 n281 n282

private theorem c31227 (h : TenSystem T Q) :
    T {3, 5, 7} → ¬ Q {2, 3, 4, 6} → T {1, 5, 7} → T {0, 5, 7} →
      ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → T {2, 4, 6} → ¬ Q {2, 4, 5, 6} → False := by
  classical
  intro a92 n262 a56 a28 n156 n212 a72 n276
  have u0_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24319 h hv a28 a56 a92
  have u1_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24459 h hv a28 a56 a92
  exact c31226 h u0_281 u1_282 n156 a72 n276 n212 n262

theorem c31228 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → Q {3, 7, 8, 9} → T {0, 1, 4} → False := by
  classical
  intro a314 a315 a3
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u4_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u5_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u6_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u1_1 hv
  have u7_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u8_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u7_76 u6_101
  have u9_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u8_55
  have u10_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c144 h hv u9_10
  have u11_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv u7_76 u6_101
  have u12_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u11_27 hv
  have u13_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv u12_38
  have u14_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28985 h a315 u1_1 a3 hv
  have u15_71 : T {2, 4, 5} := by
    by_contra hv
    exact c28968 h a315 u14_5 hv
  have u16_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c65 h hv u14_5
  have u17_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u1_1 a3 hv
  have u18_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28966 h a315 u17_4 hv
  have u19_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c50 h hv u17_4
  have u20_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u21_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23503 h hv u0_2 u20_120
  have u22_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1779 h a314 hv
  have u23_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c28845 h a314 u1_1 a3 hv
  have u24_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28826 h a314 u17_4 hv
  have u25_28 : T {0, 5, 7} := by
    by_contra hv
    exact c28840 h a314 hv u12_38
  have u26_56 : T {1, 5, 7} := by
    by_contra hv
    exact c28830 h a314 u9_10 hv
  have u27_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1941 h u2_121 hv u22_119 u20_120
  have u28_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3203 h hv u15_71 u22_119
  have u29_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21544 h hv u23_6 u27_116
  have u30_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3363 h hv u15_71 u18_72 u24_73
  have u31_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3503 h hv u15_71 u18_72 u24_73
  have u32_128 : Q {0, 1, 3, 4} := by
    by_contra hv
    exact c19 h u2_121 hv u19_129 u16_130 u28_131 u30_132 u31_133
  have u33_16 : T {0, 3, 4} := by
    by_contra hv
    exact c228 h u32_128 hv
  have u34_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26031 h hv u33_16 u26_56
  have u35_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c31227 h hv u29_262 u26_56 u25_28 u10_156 u13_212 u18_72 u21_276
  have u36_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21124 h hv u9_10 u35_92
  have u37_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13284 h hv u12_38 u35_92
  exact c1780 h a314 u37_203 u36_259 u34_294 u5_324 u4_328 u3_330

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases078
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

private theorem c31229 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 7} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ T {2, 5, 6} → Q {3, 7, 8, 9} → False := by
  classical
  intro n111 n311 n305 n275 n314 n76 a315
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u2_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10744 h hv n76 u1_101 n111
  have u3_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18584 h hv n76 u1_101 n111
  exact c1501 h a315 u2_184 u3_240 n275 n305 n311 n314

theorem c31230 (h : TenSystem T Q) :
    ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 9} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 7} → T {1, 4, 5} → False := by
  classical
  intro n226 n244 n134 n211 n241 n242 a50
  have u0_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c737 h a50 n134 n211 n226 n241 n242 hv n244
  exact c749 h u0_243 n134 n211 n226 n241 n242 n244

theorem c31231 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 8, 9} → ¬ Q {1, 3, 5, 9} → T {6, 8, 9} → ¬ T {2, 3, 4} → T {4, 6, 7} → ¬ Q {1, 5, 8, 9} → ¬ Q {1, 2, 4, 5} → ¬ T {0, 2, 4} → T {2, 4, 6} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 4, 5} → T {1, 5, 6} → ¬ T {4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a184 n234 a119 n65 a105 n256 n211 n10 a72 n142 n134 a55 n101 a120
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18743 h hv u1_9 a119
  have u3_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1805 h u0_121 hv a119
  have u4_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18603 h hv u1_9 a120
  have u5_20 : T {0, 3, 8} := by
    by_contra hv
    exact c300 h a184 hv
  have u6_36 : T {0, 8, 9} := by
    by_contra hv
    exact c532 h a184 hv
  have u7_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c10637 h a184 a55 hv
  have u8_50 : T {1, 4, 5} := by
    by_contra hv
    exact c10718 h a184 hv n101 u3_102
  have u9_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15529 h hv u5_20 a105
  have u10_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20575 h hv u5_20 a72
  have u11_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16639 h hv u6_36 a119 a120
  have u12_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20350 h hv n10 n65 u7_73
  have u13_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c865 h hv n142 u9_219 n234 u12_253 u10_255 n256
  exact c31230 h u11_226 u13_244 n134 n211 u4_241 u2_242 u8_50

private theorem c31232 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 9} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 7} → T {0, 4, 5} → False := by
  classical
  intro n170 n188 n134 n155 n185 n186 a22
  have u0_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c317 h a22 n134 n155 n170 n185 n186 hv n188
  exact c329 h u0_187 n134 n155 n170 n185 n186 n188

private theorem c31233 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 4, 8} → ¬ T {0, 1, 7} → ¬ Q {3, 6, 8, 9} → T {2, 4, 6} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 4, 5} → ¬ T {0, 1, 6} → ¬ T {2, 5, 6} → Q {3, 7, 8, 9} → False := by
  classical
  intro n116 n305 n265 n264 n6 n314 a72 n142 n134 n5 n76 a315
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u4_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv n6 u3_101
  have u5_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv n76 u3_101
  have u6_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u5_55
  have u7_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c142 h hv u6_10
  have u8_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv n76 u3_101
  have u9_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u8_27 hv
  have u10_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv u9_38
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u12_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5723 h hv u5_55 u11_120
  have u13_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u8_27 u11_120
  have u14_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10763 h hv u2_37 u11_120
  have u15_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv n116
  have u16_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv n116
  have u17_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv n116
  have u18_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv n116
  have u19_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21684 h hv n5 n116
  have u20_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21544 h hv n6 n116
  have u21_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31229 h h0 hv u17_311 n305 u4_275 n314 n76 a315
  have u22_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c968 h hv u12_149 u13_205 u20_262 u19_263 n264 n265
  have u23_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1821 h u1_121 hv u21_111
  have u24_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1895 h u1_121 u18_105 u21_111 hv
  have u25_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u12_149 u13_205 u22_261 u20_262 u19_263 n264 n265
  have u26_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1934 h u1_121 u23_110 n116 hv
  have u27_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9782 h hv u9_38 u24_117
  have u28_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17622 h hv u6_10 u24_117
  have u29_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10903 h hv u2_37 u26_119
  have u30_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c31231 h h0 hv u28_234 u26_119 u25_65 u18_105 u16_256 u10_211 u6_10 a72 n142 n134 u5_55 u3_101 u11_120
  have u31_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 u30_184 hv u4_275 n305 u17_311 n314
  have u32_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u31_240 hv
  have u33_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h u31_240 hv
  have u34_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u31_240 hv u18_105
  have u35_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c18477 h u31_240 u8_27 hv
  have u36_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c18479 h u31_240 hv a72
  have u37_22 : T {0, 4, 5} := by
    by_contra hv
    exact c18500 h u31_240 u34_11 hv u36_28
  have u38_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7689 h hv u32_48 u18_105
  have u39_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12735 h hv u32_48 a72
  have u40_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8799 h hv u33_64 u26_119 u11_120
  have u41_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12510 h hv u9_38 u25_65 u35_73
  have u42_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c445 h hv n142 u38_163 u27_178 u41_197 u39_199 u15_200
  exact c31232 h u40_170 u42_188 n134 u7_155 u14_185 u29_186 u37_22

private theorem c31234 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ T {0, 4, 5} → ¬ T {0, 1, 7} → Q {3, 7, 8, 9} → T {0, 1, 4} → False := by
  classical
  intro n311 n22 n6 a315 a3
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u6_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u7_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28985 h a315 u0_1 a3 hv
  have u8_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u9_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c52 h hv u8_4
  have u10_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c60 h hv u8_4
  have u11_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28966 h a315 u8_4 hv
  have u12_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u13_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21842 h hv u8_4 u7_5 n6
  have u14_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21982 h hv u8_4 u7_5 n6
  have u15_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27588 h hv u8_4 u7_5 n6
  have u16_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31233 h h0 hv u15_305 u14_265 u13_264 n6 u12_314 u11_72 u10_142 u9_134 u7_5 u6_76 a315
  have u17_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1941 h u1_121 u16_116 hv u5_120
  have u18_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u1_121 hv u17_119
  have u19_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u20_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv u19_40 u18_102
  have u21_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u22_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u6_76 u21_101
  have u23_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u22_55
  have u24_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29004 h a315 u23_10 n22 hv
  have u25_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21682 h hv u8_4 u17_119
  have u26_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21404 h hv n6 u17_119
  have u27_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv u6_76 u21_101
  have u28_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u27_27 u5_120
  have u29_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5723 h hv u22_55 u5_120
  have u30_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c970 h hv u29_149 u28_205 u26_261 u25_263 u13_264 u14_265
  have u31_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u29_149 u28_205 u26_261 u30_262 u25_263 u13_264 u14_265
  have u32_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv n6 u21_101
  have u33_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u27_27 hv
  have u34_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 u20_184 hv u32_275 u15_305 n311 u12_314
  have u35_24 : T {0, 4, 7} := by
    by_contra hv
    exact c18474 h u34_240 hv u6_76
  have u36_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c18477 h u34_240 u27_27 hv
  have u37_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25643 h hv a3 u24_23 u35_24
  have u38_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20772 h hv u23_10 u31_65 u36_73
  have u39_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12932 h hv u33_38 u31_65 u36_73
  exact c1727 h u16_116 u39_200 u38_256 u37_291 n311 u4_321 u3_328 u2_329

theorem c31235 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 5} → ¬ T {0, 1, 7} → Q {3, 7, 8, 9} → T {0, 1, 4} → False := by
  classical
  intro n22 n6 a315 a3
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28985 h a315 u0_1 a3 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u4_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21982 h hv u3_4 u2_5 n6
  have u5_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21842 h hv u3_4 u2_5 n6
  have u6_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u7_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u8_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c52 h hv u3_4
  have u9_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c60 h hv u3_4
  have u10_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28966 h a315 u3_4 hv
  have u11_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u12_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27588 h hv u3_4 u2_5 n6
  have u13_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31233 h h0 hv u12_305 u4_265 u5_264 n6 u11_314 u10_72 u9_142 u8_134 u2_5 u7_76 a315
  have u14_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1941 h u1_121 u13_116 hv u6_120
  have u15_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21682 h hv u3_4 u14_119
  have u16_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u17_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u7_76 u16_101
  have u18_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5723 h hv u17_55 u6_120
  have u19_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv u7_76 u16_101
  have u20_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u19_27 u6_120
  have u21_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21404 h hv n6 u14_119
  have u22_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c970 h hv u18_149 u20_205 u21_261 u15_263 u5_264 u4_265
  have u23_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22663 h hv a3 u13_116
  have u24_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u17_55
  have u25_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u19_27 hv
  have u26_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22103 h hv a3 u6_120
  have u27_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u28_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u16_101
  have u29_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13982 h hv n22 u14_119
  have u30_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29004 h a315 u24_10 n22 hv
  have u31_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29071 h a315 hv u27_40 u10_72
  have u32_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u28_50 u6_120
  have u33_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13703 h hv u30_23 u6_120
  have u34_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31234 h h0 hv n22 n6 a315 a3
  have u35_52 : T {1, 4, 7} := by
    by_contra hv
    exact c28412 h u34_311 u31_12 hv
  have u36_31 : T {0, 6, 7} := by
    by_contra hv
    exact c28420 h u34_311 hv u25_38
  have u37_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22863 h hv a3 u28_50 u35_52
  have u38_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23003 h hv a3 u28_50 u35_52
  have u39_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14159 h hv u30_23 u19_27 u36_31
  have u40_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c14299 h hv u30_23 u19_27 u36_31
  have u41_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c996 h hv u32_151 u22_262 u26_266 u23_270 u37_271 u38_272
  exact c544 h u1_121 u20_205 u33_206 u41_207 u29_208 u39_209 u40_210

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases079
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

private theorem c31236 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 8} → ¬ Q {1, 2, 3, 6} → T {4, 5, 7} → T {0, 2, 5} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 8, 9} → ¬ T {0, 2, 6} → ¬ T {0, 1, 6} → ¬ T {1, 2, 5} → T {0, 5, 6} → T {0, 1, 4} → T {0, 4, 6} → T {2, 4, 5} → T {1, 4, 5} → T {1, 2, 6} → ¬ T {4, 5, 6} → ¬ T {1, 2, 4} → ¬ T {0, 4, 5} → False := by
  classical
  intro a209 n207 a102 a11 n307 n311 n12 n5 n39 a27 a3 a23 a71 a50 a40 n101 n38 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10155 h hv a50 a71 a102
  have u2_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv a40 a102
  have u3_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c63 h hv n5
  have u4_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c579 h hv n39
  have u5_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv n38
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c14122 h a209 n22 hv
  have u7_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c14125 h a209 a23 hv
  have u8_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c14131 h a209 a27 hv
  have u9_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c14139 h a209 hv a102
  have u10_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14159 h a209 a23 a27 hv
  have u11_104 : T {4, 5, 9} := by
    by_contra hv
    exact c14184 h a209 n22 n101 hv
  have u12_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26583 h hv u0_1 u6_118
  have u13_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22383 h hv a3 u6_118
  have u14_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u6_118
  have u15_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6283 h hv a50 u6_118
  have u16_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16923 h hv a11 u6_118
  have u17_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21824 h hv n5 u7_115
  have u18_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17484 h hv n12 u8_109
  have u19_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27300 h hv u9_33 n39
  have u20_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28140 h hv u9_33 n38
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27580 h hv u10_31 n39
  have u22_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10347 h hv a40 u11_104
  have u23_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c1384 h hv u18_233 u13_268 u12_298 n307 u20_309 n311
  have u24_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c293 h hv u14_132 u15_153 u23_177 u1_180 u22_182 u2_184
  have u25_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c287 h hv u14_132 u15_153 u24_173 u23_177 u1_180 u22_182 u2_184
  have u26_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1332 h hv u24_173 u16_229 u17_264 u12_298 u19_303 u21_305
  have u27_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u23_177 u18_233 u13_268 u12_298 n307 u20_309 n311
  have u28_89 : ¬ T {3, 4, 8} := by
    intro hv
    exact c1322 h hv u24_173 u16_229 u17_264 u12_298 u26_301 u19_303 u21_305
  have u29_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15738 h hv u25_20 u28_89 u27_93
  have u30_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16026 h hv u25_20 u28_89 u27_93
  have u31_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c599 h hv u3_124 n207 u5_212 u4_216 u29_220 u30_222
  exact c587 h a40 u3_124 n207 u5_212 u4_216 u29_220 u31_221 u30_222

private theorem c31237 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 7} → T {4, 5, 7} → ¬ Q {3, 5, 6, 8} → ¬ T {0, 2, 6} → ¬ T {0, 1, 6} → ¬ Q {2, 5, 6, 8} → T {2, 4, 6} → T {0, 5, 6} → T {0, 1, 7} → T {0, 4, 6} → T {1, 4, 5} → ¬ T {4, 5, 6} → T {7, 8, 9} → T {3, 7, 9} → ¬ T {1, 2, 4} → ¬ T {0, 4, 5} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro a210 n262 n263 a102 n307 n12 n5 n287 a72 a27 a6 a23 a50 n101 a120 a99 n38 n22 n149 n134
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4611 h hv a72 a99
  have u6_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15391 h hv a23 a99
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18603 h hv u0_9 a120
  have u8_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv n38
  have u9_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv n38
  have u10_49 : T {1, 3, 9} := by
    by_contra hv
    exact c725 h a210 hv
  have u11_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h a210 hv
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c14262 h a210 n22 hv
  have u13_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c14265 h a210 a23 hv
  have u14_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c14271 h a210 a27 hv
  have u15_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c14279 h a210 hv a102
  have u16_34 : T {0, 7, 8} := by
    by_contra hv
    exact c14280 h a210 hv n101
  have u17_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14299 h a210 a23 a27 hv
  have u18_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12413 h hv u10_49 u11_70 a99
  have u19_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20437 h hv a23 u11_70
  have u20_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19023 h hv u0_9 u12_117
  have u21_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u1_121 hv u13_114
  have u22_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21964 h hv n5 u13_114
  have u23_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u1_121 u14_108 hv
  have u24_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16530 h hv n12 u17_31 u15_32
  have u25_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21523 h hv u16_34 u12_117 a120
  have u26_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1671 h hv u18_196 n287 n307 u4_317 u3_326 u2_328
  have u27_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31230 h u24_226 u20_244 n134 u8_211 u7_241 hv a50
  have u28_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17577 h hv a23 a72 u21_107
  have u29_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21827 h hv a6 u23_113
  have u30_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv n149 u9_205 u25_261 n262 n263 u29_264 u22_265
  have u31_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c747 h u27_242 n134 u8_211 u24_226 u7_241 hv u20_244
  have u32_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20720 h hv u17_31 u30_65
  exact c850 h u31_243 u5_141 u6_218 u28_233 u26_252 u19_254 u32_256

private theorem c31238 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 5} → ¬ Q {0, 2, 3, 6} → ¬ T {1, 4, 6} → T {0, 1, 4} → T {1, 4, 5} → ¬ T {0, 4, 5} → ¬ Q {0, 2, 3, 4} → False := by
  classical
  intro a270 n4 n151 n51 a3 a50 n22 n149
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c22663 h a270 a3 hv
  have u2_110 : T {4, 8, 9} := by
    by_contra hv
    exact c22664 h a270 n4 hv
  have u3_64 : T {1, 8, 9} := by
    by_contra hv
    exact c22670 h a270 n22 hv
  have u4_53 : ¬ T {1, 4, 8} := by
    intro hv
    exact c22723 h a270 a3 a50 hv
  have u5_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c22725 h a270 a3 a50 hv
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u0_121 hv u1_116
  have u7_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6144 h hv n51 u1_116
  have u8_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 u2_110 hv
  have u9_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5881 h hv u3_64 u6_105
  have u10_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6428 h hv u4_53 u8_111
  have u11_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6288 h hv u5_54 u8_111
  exact c124 h u0_121 n149 u9_150 n151 u7_152 u11_153 u10_154

private theorem c31239 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → ¬ T {0, 1, 5} → T {0, 1, 7} → ¬ T {0, 4, 5} → False := by
  classical
  intro a271 a24 n4 a6 n22
  have u0_28 : T {0, 5, 7} := by
    by_contra hv
    exact c22838 h a271 n4 n22 hv
  exact c22847 h a271 a6 a24 u0_28

private theorem c31240 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 6, 7} → T {2, 4, 6} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ T {0, 1, 5} → ¬ Q {0, 2, 3, 6} → ¬ Q {2, 3, 5, 6} → T {0, 1, 7} → T {1, 2, 6} → ¬ T {0, 4, 5} → False := by
  classical
  intro a207 n262 n270 a72 n291 n311 n4 n151 n266 a6 a40 n22
  have u0_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u3_67 : T {2, 3, 6} := by
    by_contra hv
    exact c995 h a207 hv
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12939 h hv a40 u3_67 a72
  have u5_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1731 h hv u4_200 n291 n311 u2_321 u1_328 u0_329
  have u6_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1727 h hv u4_200 u5_256 n291 n311 u2_321 u1_328 u0_329
  have u7_24 : T {0, 4, 7} := by
    by_contra hv
    exact c13844 h a207 hv u6_116
  have u8_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c31239 h hv u7_24 n4 a6 n22
  have u9_272 : Q {2, 3, 6, 9} := by
    by_contra hv
    exact c996 h a207 n151 n262 n266 n270 u8_271 hv
  have u10_28 : T {0, 5, 7} := by
    by_contra hv
    exact c22978 h u9_272 n4 n22 hv
  exact c22987 h u9_272 a6 u7_24 u10_28

private theorem c31242 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → ¬ Q {2, 3, 4, 6} → T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro a102 n262 a3 a315 n22 n134
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u4_6 : T {0, 1, 7} := by
    by_contra hv
    exact c31235 h h0 n22 hv a315 a3
  have u5_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u6_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22103 h hv a3 u5_120
  have u7_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u1_1 hv
  have u8_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u7_101
  have u9_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u8_50 u5_120
  have u10_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u1_1 a3 hv
  have u11_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28425 h hv u1_1 a3 u4_6
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25625 h hv u0_2 a3 u4_6
  have u13_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u8_50
  have u14_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u15_72 : T {2, 4, 6} := by
    by_contra hv
    exact c29074 h a315 u13_12 hv u14_76
  have u16_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c29035 h a315 a3 u8_50 hv
  have u17_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u1_1 hv u3_40
  have u18_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u17_39
  have u19_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c29001 h a315 a3 hv u18_23
  have u20_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c140 h hv u19_10
  have u21_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c31238 h h0 hv u10_4 u9_151 u16_51 a3 u8_50 n22 u20_149
  have u22_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c31240 h h0 hv n262 u21_270 u15_72 u12_291 u11_311 u10_4 u9_151 u6_266 u4_6 u3_40 n22
  have u23_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27863 h hv u1_1 a3 u4_6
  have u24_11 : T {0, 2, 5} := by
    by_contra hv
    exact c29064 h a315 hv u17_39 u14_76
  have u25_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1485 h a315 hv
  have u26_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25045 h hv a3 u25_99
  have u27_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u17_39
  have u28_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u1_1 hv u3_40
  have u29_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u28_38
  have u30_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u28_38
  have u31_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u7_101
  have u32_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u31_71
  have u33_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u2_121 a102 hv
  have u34_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c31236 h h0 hv u22_207 a102 u24_11 u23_307 u11_311 u13_12 u32_5 u17_39 u29_27 a3 u18_23 u31_71 u8_50 u3_40 u7_101 u28_38 n22
  have u35_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21682 h hv u10_4 u33_119
  have u36_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13982 h hv n22 u33_119
  have u37_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c544 h u2_121 u30_205 u27_206 u22_207 u36_208 u34_209 hv
  exact c31237 h h0 u37_210 n262 u35_263 a102 u23_307 u13_12 u32_5 u26_287 u15_72 u29_27 u4_6 u18_23 u8_50 u7_101 u5_120 u25_99 u28_38 n22 u20_149 n134

theorem c31243 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 3, 4, 6} → T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro n262 a3 a315 n22 n134
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u3_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u2_40
  have u4_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u3_39
  have u5_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c29001 h a315 a3 hv u4_23
  have u6_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c140 h hv u5_10
  have u7_6 : T {0, 1, 7} := by
    by_contra hv
    exact c31235 h h0 n22 hv a315 a3
  have u8_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28425 h hv u0_1 a3 u7_6
  have u9_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u10_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c60 h hv u9_4
  have u11_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u12_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u11_101
  have u13_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u12_50
  have u14_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u15_72 : T {2, 4, 6} := by
    by_contra hv
    exact c29074 h a315 u13_12 hv u14_76
  have u16_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u14_76 u11_101
  have u17_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u18_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u2_40
  have u19_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv u18_38
  have u20_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u18_38
  have u21_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u11_101
  have u22_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u21_71
  have u23_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u24_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31242 h h0 hv n262 a3 a315 n22 n134
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 u24_102 hv
  have u26_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1822 h u1_121 u11_101 u24_102 hv
  have u27_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1824 h u1_121 u11_101 u24_102 hv
  have u28_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23366 h hv u22_5 u24_102
  have u29_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18558 h hv n22 u11_101 u24_102
  have u30_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u1_121 hv u25_119 u23_120
  have u31_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1941 h u1_121 hv u25_119 u23_120
  have u32_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21405 h hv u7_6 u25_119
  have u33_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u1_121 u26_103 hv
  have u34_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1809 h u1_121 u27_104 hv
  have u35_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1644 h hv u30_110
  have u36_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv u31_116
  have u37_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv u31_116
  have u38_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21684 h hv u22_5 u31_116
  have u39_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21822 h hv u9_4 u33_118
  have u40_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21962 h hv u9_4 u34_117
  have u41_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17622 h hv u5_10 u34_117
  have u42_184 : Q {0, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 hv u29_240 u28_275 u35_305 u8_311 u17_314
  have u43_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u6_149 u20_205 u32_261 n262 u38_263 u39_264 u40_265
  exact c31231 h h0 u42_184 u41_234 u25_119 u43_65 u37_105 u36_256 u19_211 u5_10 u15_72 u10_142 n134 u16_55 u11_101 u23_120

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases080
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

theorem c31244 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 1, 4, 5} → False := by
  classical
  intro a3 a315 n22 n186 n134
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u4_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u5_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u6_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u7_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u8_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u9_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u10_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u11_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u12_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u13_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u12_40
  have u14_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u13_39
  have u15_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c581 h hv u13_39
  have u16_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u12_40
  have u17_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u16_38
  have u18_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u19_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u18_101
  have u20_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u19_71
  have u21_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1500 h a315 hv
  have u22_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4891 h hv u19_71 u21_100
  have u23_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u18_101
  have u24_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u23_50
  have u25_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u26_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u0_1 a3 hv
  have u27_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31228 h h0 hv a315 a3
  have u28_6 : T {0, 1, 7} := by
    by_contra hv
    exact c31235 h h0 n22 hv a315 a3
  have u29_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c29035 h a315 a3 u23_50 hv
  have u30_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c29001 h a315 a3 hv u14_23
  have u31_11 : T {0, 2, 5} := by
    by_contra hv
    exact c29064 h a315 hv u13_39 u25_76
  have u32_72 : T {2, 4, 6} := by
    by_contra hv
    exact c29074 h a315 u24_12 hv u25_76
  have u33_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c56 h hv u26_4
  have u34_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26045 h hv u1_2 a3 u28_6
  have u35_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv u29_51
  have u36_262 : Q {2, 3, 4, 6} := by
    by_contra hv
    exact c31243 h h0 hv a3 a315 n22 n134
  have u37_65 : T {2, 3, 4} := by
    by_contra hv
    exact c969 h u36_262 hv
  have u38_67 : T {2, 3, 6} := by
    by_contra hv
    exact c997 h u36_262 hv
  have u39_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1297 h u36_262 hv
  have u40_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c21545 h u36_262 u28_6 hv
  have u41_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5611 h hv u37_65 u19_71 u32_72
  have u42_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13497 h hv u37_65 u19_71 u32_72
  have u43_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21337 h hv u37_65 u19_71 u32_72
  have u44_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20483 h hv u2_9 u37_65 u38_67
  have u45_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20623 h hv u2_9 u37_65 u38_67
  have u46_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20763 h hv u2_9 u37_65 u38_67
  have u47_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u8_121 hv u40_116
  have u48_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17762 h hv u30_10 u40_116
  have u49_295 : Q {2, 7, 8, 9} := by
    by_contra hv
    exact c1795 h a315 u42_204 u43_260 hv u4_325 u3_329 u5_330
  have u50_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18565 h hv u14_23 u32_72 u47_105
  have u51_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16465 h hv u14_23 u39_87 u47_105
  have u52_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1275 h u49_295 hv
  have u53_86 : T {3, 4, 5} := by
    by_contra hv
    exact c26168 h u49_295 u20_5 hv
  have u54_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c26259 h u49_295 hv u53_86 u39_87
  have u55_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c26175 h u49_295 hv u23_50
  have u56_17 : T {0, 3, 5} := by
    by_contra hv
    exact c26172 h u49_295 hv u29_51
  have u57_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17351 h hv u14_23 u52_85
  have u58_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13399 h hv u23_50 u19_71 u53_86
  have u59_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15662 h hv u54_16 u40_116
  have u60_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20878 h hv u30_10 u54_16 n22
  have u61_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21018 h hv u30_10 u54_16 n22
  have u62_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21158 h hv u30_10 u54_16 n22
  have u63_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19899 h hv u31_11 u56_17 u17_27
  have u64_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c882 h hv u22_143 u59_220 u48_235 u35_245 u60_257 u61_258
  have u65_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1772 h hv u58_203 u62_259 u34_294 u27_314 u7_324 u6_328 u5_330
  have u66_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c947 h hv u41_148 u51_225 u50_240 u63_250 u46_256 u62_259 u43_260
  have u67_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c835 h hv u33_140 u15_217 u57_232 u64_251 u44_254 u45_255
  have u68_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u8_121 hv u65_119
  have u69_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26450 h hv u24_12 u66_64
  have u70_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23650 h hv u55_18 u66_64
  exact c1517 h u68_102 n186 u67_242 u70_277 u69_297 u11_316 u10_319 u9_320

private theorem c31245 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {2, 3, 5, 7} → ¬ Q {0, 3, 8, 9} → ¬ T {6, 8, 9} →
      ¬ Q {2, 4, 8, 9} → T {0, 1, 7} → T {1, 4, 6} → T {2, 5, 6} → ¬ T {0, 2, 6} →
      T {2, 4, 5} → T {1, 2, 6} → Q {3, 7, 8, 9} → False := by
  classical
  intro n116 n267 n184 n119 n285 a6 a51 a76 n12 a71 a40 a315
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28829 h hv a6 a71
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27569 h hv a6 a76
  have u7_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u8_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv a51 u7_120
  have u9_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 a40 hv a76
  have u10_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv a40
  have u11_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u10_39
  have u12_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u10_39
  have u13_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv n116
  have u14_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv n116
  have u15_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1934 h u1_121 hv n116 n119
  have u16_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22475 h hv u11_23 a51 u14_105
  have u17_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22615 h hv u11_23 a51 u14_105
  have u18_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23465 h hv u11_23 a51 u14_105
  have u19_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22105 h hv a6 u15_110
  have u20_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 n184 hv u18_275 u6_305 u13_311 u5_314
  have u21_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c983 h hv u8_150 u12_206 u19_266 n267 u16_268 u17_269
  have u22_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c18481 h u20_240 hv a71
  have u23_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18540 h u20_240 n12 u9_72 hv
  have u24_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u8_150 u12_206 u21_261 u19_266 n267 u16_268 u17_269
  have u25_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19880 h hv u22_31 u24_66
  have u26_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12103 h hv a40 a76 u23_80
  exact c1637 h u15_110 u26_194 u25_250 n285 u6_305 u4_321 u3_324 u2_325

private theorem c31246 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ Q {1, 3, 8, 9} → T {5, 8, 9} → ¬ Q {0, 3, 8, 9} →
      ¬ Q {3, 6, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ T {1, 5, 6} → T {1, 4, 6} →
      T {0, 2, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n311 n240 a116 n184 n314 n305 n55 a51 a10 a315 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u5_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u4_40
  have u6_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u5_39
  have u7_275 : Q {2, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 n184 n240 hv n305 n311 n314
  have u8_59 : T {1, 6, 7} := by
    by_contra hv
    exact c23370 h u7_275 n22 hv
  have u9_24 : T {0, 4, 7} := by
    by_contra hv
    exact c23374 h u7_275 hv n55
  have u10_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12911 h hv u4_40 a51 u8_59
  have u11_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20743 h hv a10 u6_23 u9_24
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1733 h hv u10_200 u11_256 n311 u3_321 u2_328 u1_329
  exact c1727 h a116 u10_200 u11_256 u12_291 n311 u3_321 u2_328 u1_329

theorem c31247 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {0, 1, 7} → ¬ T {0, 1, 4} → Q {3, 7, 8, 9} →
      ¬ T {0, 4, 5} → ¬ Q {0, 3, 4, 5} → False := by
  classical
  intro a102 a6 n3 a315 n22 n170
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u1_1 hv
  have u4_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u3_101
  have u5_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u4_71
  have u6_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 n3 hv u5_5
  have u7_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24785 h hv u0_2 u6_4 a6
  have u8_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28829 h hv a6 u4_71
  have u9_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 n3 hv
  have u10_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27569 h hv a6 u9_76
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u12_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u13_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u1_1 hv u12_40
  have u14_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 n3 u13_38 hv
  have u15_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u14_51 u11_120
  have u16_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 u12_40 hv u9_76
  have u17_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u13_38
  have u18_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c29095 h a315 u17_27 hv u9_76
  have u19_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 n3 hv n22
  have u20_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv n3
  have u21_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u1_1 hv u12_40
  have u22_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28978 h a315 hv u21_39
  have u23_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3063 h hv u4_71 u11_120
  have u24_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u3_101
  have u25_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u24_50
  have u26_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u24_50 u11_120
  have u27_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u2_121 a102 hv
  have u28_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv u12_40 a102
  have u29_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10155 h hv u24_50 u4_71 a102
  have u30_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10295 h hv u24_50 u4_71 a102
  have u31_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22242 h hv n3 u27_119
  have u32_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8942 h hv u21_39 u27_119
  have u33_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31245 h h0 hv u31_267 u28_184 u27_119 u7_285 a6 u14_51 u9_76 u25_12 u4_71 u12_40 a315
  have u34_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u33_116
  have u35_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1937 h u2_121 hv u33_116 u11_120
  have u36_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6145 h hv u14_51 u33_116
  have u37_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18568 h hv u16_72 u3_101 u34_105
  have u38_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9924 h hv u21_39 u35_110
  have u39_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31246 h h0 hv u37_240 u33_116 u28_184 u8_314 u10_305 u18_55 u14_51 u19_10 a315 n22
  have u40_80 : T {2, 6, 7} := by
    by_contra hv
    exact c28404 h u39_311 n3 hv
  have u41_52 : T {1, 4, 7} := by
    by_contra hv
    exact c28412 h u39_311 u25_12 hv
  have u42_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c28417 h u39_311 u22_23 hv
  have u43_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9151 h hv u12_40 u9_76 u40_80
  have u44_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9291 h hv u12_40 u9_76 u40_80
  have u45_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6303 h hv u24_50 u14_51 u41_52
  have u46_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6443 h hv u24_50 u14_51 u41_52
  have u47_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9364 h hv u42_41 u35_110
  have u48_149 : Q {0, 2, 3, 4} := by
    by_contra hv
    exact c124 h u2_121 hv u15_150 u26_151 u36_152 u45_153 u46_154
  have u49_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c263 h hv u23_130 u26_151 u47_175 u38_179 u29_180 u30_181
  exact c231 h u48_149 u20_128 n170 u49_171 u32_172 u43_173 u44_174

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases081
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

private theorem c31248 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 7} → ¬ T {0, 1, 4} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ Q {0, 3, 4, 5} → False := by
  classical
  intro a6 n3 a315 n22 n170
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := h0
  have u3_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u4_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u5_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u6_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u7_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u7_40
  have u9_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 n3 u8_38 hv
  have u10_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u9_51 u6_120
  have u11_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u8_38
  have u12_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 n3 hv
  have u13_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c29095 h a315 u11_27 hv u12_76
  have u14_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u15_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u14_101
  have u16_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u15_71
  have u17_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 n3 hv u16_5
  have u18_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 n3 hv n22
  have u19_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u7_40
  have u20_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u19_39
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27569 h hv a6 u12_76
  have u22_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28829 h hv a6 u15_71
  have u23_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26047 h hv u1_2 u17_4 a6
  have u24_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31247 h h0 hv a6 n3 a315 n22 n170
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u2_121 u24_102 hv
  have u26_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1822 h u2_121 u14_101 u24_102 hv
  have u27_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1824 h u2_121 u14_101 u24_102 hv
  have u28_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23366 h hv u16_5 u24_102
  have u29_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18558 h hv n22 u14_101 u24_102
  have u30_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u2_121 hv u25_119 u6_120
  have u31_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1941 h u2_121 hv u25_119 u6_120
  have u32_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21405 h hv a6 u25_119
  have u33_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 u26_103 hv
  have u34_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1809 h u2_121 u27_104 hv
  have u35_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22244 h hv u16_5 u30_110
  have u36_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv u31_116
  have u37_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22382 h hv n3 u33_118
  have u38_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22522 h hv n3 u34_117
  have u39_184 : Q {0, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 hv u29_240 u28_275 u21_305 u36_311 u22_314
  have u40_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c985 h hv u10_150 u20_206 u32_261 u35_267 u37_268 u38_269
  have u41_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c10635 h u39_184 hv u12_76
  have u42_73 : T {2, 4, 7} := by
    by_contra hv
    exact c10636 h u39_184 u13_55 hv
  have u43_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u10_150 u20_206 u32_261 u40_266 u35_267 u37_268 u38_269
  have u44_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13298 h hv u41_52 u43_66
  have u45_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21195 h hv u18_10 u15_71 u42_73
  exact c1772 h u25_119 u44_203 u45_259 u23_294 u22_314 u5_324 u4_328 u3_330

private theorem c31249 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 6, 8, 9} → ¬ T {2, 3, 5} → ¬ Q {1, 3, 8, 9} → T {6, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ T {2, 4, 6} → ¬ T {1, 5, 6} → T {0, 1, 5} → T {0, 2, 4} → T {2, 5, 6} → T {2, 4, 5} → T {1, 4, 5} → Q {3, 7, 8, 9} → False := by
  classical
  intro n314 n66 n240 a119 n311 n275 n72 n55 a4 a10 a76 a71 a50 a315
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u5_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u0_121 hv a119 u4_120
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1644 h hv u5_110
  have u7_184 : Q {0, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 hv n240 n275 u6_305 n311 n314
  have u8_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c10635 h u7_184 hv a76
  have u9_73 : T {2, 4, 7} := by
    by_contra hv
    exact c10636 h u7_184 n55 hv
  have u10_56 : T {1, 5, 7} := by
    by_contra hv
    exact c10638 h u7_184 hv n72
  have u11_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13298 h hv u8_52 n66
  have u12_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21195 h hv a10 a71 u9_73
  have u13_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26103 h hv a4 a50 u10_56
  exact c1772 h a119 u11_203 u12_259 u13_294 n314 u3_324 u2_328 u1_330

private theorem c31250 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n102 a315 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u3_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u2_101
  have u4_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u3_71
  have u5_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c318 h hv n22
  have u6_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u7_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c31244 h h0 hv a315 n22 u6_186 u5_134
  have u8_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c322 h hv n22
  have u9_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c31248 h h0 hv u7_3 a315 n22 u8_170
  have u10_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28428 h hv u7_3 u4_5 u9_6
  have u11_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22542 h hv u7_3 u4_5 u9_6
  have u12_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22402 h hv u7_3 u4_5 u9_6
  have u13_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv u9_6 u2_101
  have u14_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c80 h hv u9_6
  have u15_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u16_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u17_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u16_40
  have u18_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 u7_3 u17_38 hv
  have u19_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u18_51 u15_120
  have u20_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 u7_3 hv n22
  have u21_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17203 h hv u20_10 u15_120
  have u22_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 u7_3 hv
  have u23_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c29067 h a315 hv u3_71 u22_76
  have u24_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 u16_40 hv u22_76
  have u25_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u17_38
  have u26_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c29095 h a315 u25_27 hv u22_76
  have u27_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u16_40
  have u28_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u27_39
  have u29_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 u7_3 hv u4_5
  have u30_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29002 h a315 u7_3 n22 hv
  have u31_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv u7_3
  have u32_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3063 h hv u3_71 u15_120
  have u33_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26303 h hv u0_1 u15_120
  have u34_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u2_101
  have u35_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1524 h hv n102
  have u36_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 n102 hv
  have u37_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18558 h hv n22 u2_101 n102
  have u38_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1939 h u1_121 hv u36_119 u15_120
  have u39_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17343 h hv u20_10 u36_119
  have u40_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22244 h hv u4_5 u38_110
  have u41_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22104 h hv u9_6 u38_110
  have u42_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c983 h hv u19_150 u28_206 u41_266 u40_267 u12_268 u11_269
  have u43_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u19_150 u28_206 u42_261 u41_266 u40_267 u12_268 u11_269
  have u44_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31249 h h0 hv u43_66 u37_240 u36_119 u10_311 u13_275 u24_72 u26_55 u29_4 u20_10 u22_76 u3_71 u34_50 a315
  have u45_41 : T {1, 2, 7} := by
    by_contra hv
    exact c28836 h u44_314 n22 hv
  have u46_24 : T {0, 4, 7} := by
    by_contra hv
    exact c28838 h u44_314 hv u27_39
  have u47_77 : T {2, 5, 7} := by
    by_contra hv
    exact c28924 h u44_314 u23_11 u27_39 hv
  have u48_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26783 h hv u0_1 u16_40 u45_41
  have u49_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26643 h hv u0_1 u16_40 u45_41
  have u50_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17511 h hv u20_10 u30_23 u46_24
  have u51_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17651 h hv u20_10 u30_23 u46_24
  have u52_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3511 h hv u3_71 u22_76 u47_77
  have u53_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3371 h hv u3_71 u22_76 u47_77
  have u54_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c1281 h hv u8_170 u42_261 u33_296 u35_297 u49_298 u48_299
  have u55_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c664 h hv u28_206 u54_226 u21_231 u39_232 u50_233 u51_234
  exact c19 h u1_121 u31_128 u55_129 u32_130 u14_131 u53_132 u52_133

private theorem c31251 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 8, 9} → ¬ Q {2, 3, 5, 6} → ¬ Q {1, 2, 3, 7} → ¬ Q {2, 3, 4, 6} → T {0, 5, 6} → ¬ Q {1, 2, 3, 4} → T {0, 1, 5} → T {0, 4, 6} → ¬ T {0, 2, 6} → ¬ Q {0, 2, 3, 6} → ¬ T {1, 2, 5} → T {1, 4, 5} → False := by
  classical
  intro a305 n266 n208 n262 a27 n205 a4 a23 n12 n151 n39 a50
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv n39
  have u2_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1644 h a305 hv
  have u3_56 : T {1, 5, 7} := by
    by_contra hv
    exact c27572 h a305 n12 hv
  have u4_31 : T {0, 6, 7} := by
    by_contra hv
    exact c27580 h a305 hv n39
  have u5_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22665 h hv a4 u2_110
  have u6_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22871 h hv a4 a50 u3_56
  have u7_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23011 h hv a4 a50 u3_56
  have u8_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14159 h hv a23 a27 u4_31
  have u9_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c14299 h hv a23 a27 u4_31
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c996 h hv n151 n262 n266 u5_270 u6_271 u7_272
  exact c544 h u0_121 n205 u1_206 u10_207 n208 u8_209 u9_210

theorem c31252_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro a315 n22
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := h0
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u6_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c322 h hv n22
  have u7_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c318 h hv n22
  have u8_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u9_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u0_1 hv
  have u10_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28976 h a315 n22 hv
  have u11_50 : T {1, 4, 5} := by
    by_contra hv
    exact c29080 h a315 n22 hv u9_101
  have u12_71 : T {2, 4, 5} := by
    by_contra hv
    exact c29082 h a315 n22 hv u9_101
  have u13_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c31244 h h0 hv a315 n22 u5_186 u7_134
  have u14_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c29025 h a315 u0_1 hv u10_40
  have u15_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c29027 h a315 u0_1 hv u10_40
  have u16_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6003 h hv u11_50 u8_120
  have u17_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28975 h a315 hv u11_50
  have u18_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28969 h a315 hv u12_71
  have u19_76 : T {2, 5, 6} := by
    by_contra hv
    exact c28964 h a315 u13_3 hv
  have u20_10 : T {0, 2, 4} := by
    by_contra hv
    exact c28998 h a315 u13_3 hv n22
  have u21_23 : T {0, 4, 6} := by
    by_contra hv
    exact c29002 h a315 u13_3 n22 hv
  have u22_51 : T {1, 4, 6} := by
    by_contra hv
    exact c29032 h a315 u13_3 u14_38 hv
  have u23_4 : T {0, 1, 5} := by
    by_contra hv
    exact c28988 h a315 u13_3 hv u18_5
  have u24_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c31248 h h0 hv u13_3 a315 n22 u6_170
  have u25_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u14_38
  have u26_27 : T {0, 5, 6} := by
    by_contra hv
    exact c28980 h a315 hv u14_38
  have u27_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u15_39
  have u28_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c29077 h a315 u10_40 hv u19_76
  have u29_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv u22_51 u8_120
  have u30_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21543 h hv u23_4 u8_120
  have u31_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23368 h hv u24_6 u9_101
  have u32_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22402 h hv u13_3 u18_5 u24_6
  have u33_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22542 h hv u13_3 u18_5 u24_6
  have u34_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28428 h hv u13_3 u18_5 u24_6
  have u35_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31250 h h0 hv a315 n22
  have u36_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u1_121 u35_102 hv
  have u37_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28823 h hv u0_1 u35_102
  have u38_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10627 h hv u10_40 u35_102
  have u39_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22242 h hv u13_3 u36_119
  have u40_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21404 h hv u24_6 u36_119
  have u41_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13982 h hv n22 u36_119
  have u42_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c985 h hv u29_150 u27_206 u40_261 u39_267 u32_268 u33_269
  have u43_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c977 h hv u29_150 u27_206 u40_261 u42_266 u39_267 u32_268 u33_269
  have u44_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c31251 h h0 hv u42_266 u41_208 u30_262 u26_27 u25_205 u23_4 u21_23 u17_12 u16_151 u15_39 u11_50
  have u45_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1501 h a315 u38_184 hv u31_275 u44_305 u34_311 u37_314
  have u46_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c18463 h u45_240 u20_10 hv
  have u47_28 : T {0, 5, 7} := by
    by_contra hv
    exact c18478 h u45_240 hv u28_72
  have u48_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c18481 h u45_240 hv u12_71
  have u49_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c18537 h u45_240 u12_71 u19_76 hv
  have u50_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1820 h u1_121 hv u46_111
  have u51_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24803 h hv u23_4 u26_27 u47_28
  have u52_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19880 h hv u48_31 u43_66
  have u53_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12092 h hv u15_39 u43_66 u49_77
  exact c1637 h u50_110 u53_194 u52_250 u51_285 u44_305 u4_321 u3_324 u2_325

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31252_oai := @OAI.BorsukNine.FiniteObstruction.c31252_oai
