-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31469
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:08:55.803654+00:00
-- url     : https://prove2.me/submissions/84e98cc3-a6a5-47a3-b25b-45e0a1ef1676

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31437

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

theorem c35 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {0, 1, 4} → False := by
  intro a128 n3
  exact n3 (h.down {0, 1, 3, 4} {0, 1, 4} a128 (by decide) (by decide))

theorem c41 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {0, 1, 4} → False := by
  intro a136 n3
  exact n3 (h.down {0, 1, 4, 7} {0, 1, 4} a136 (by decide) (by decide))

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

theorem c137 (h : TenSystem T Q) :
    T {0, 2, 4} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 4, 9} → False := by
  intro a10 n122 n149 n155 n156 n157 n158 n159
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 4} a10
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n149 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n155 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 4} = {0, 2, 4, 5} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 4} = {0, 2, 4, 6} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 4} = {0, 2, 4, 7} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 4} = {0, 2, 4, 8} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 4} = {0, 2, 4, 9} by decide)) hS)

theorem c141 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 4, 9} → False := by
  intro a149 n122 n155 n156 n157 n158 n159
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 4} {0, 2, 4} a149 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n155 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 4} = {0, 2, 4, 5} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 4} = {0, 2, 4, 6} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 4} = {0, 2, 4, 7} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 4} = {0, 2, 4, 8} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 4} = {0, 2, 4, 9} by decide)) hS)

theorem c150 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 2, 4} → False := by
  intro a159 n10
  exact n10 (h.down {0, 2, 4, 9} {0, 2, 4} a159 (by decide) (by decide))

theorem c152 (h : TenSystem T Q) :
    T {0, 2, 5} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 9} → False := by
  intro a11 n123 n150 n155 n160 n161 n162 n163
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 5} a11
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n123 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n150 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n160 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 5} = {0, 2, 5, 6} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 5} = {0, 2, 5, 7} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 5} = {0, 2, 5, 8} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 5} = {0, 2, 5, 9} by decide)) hS)

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

theorem c157 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {0, 2, 5} → False := by
  intro a155 n11
  exact n11 (h.down {0, 2, 4, 5} {0, 2, 5} a155 (by decide) (by decide))

theorem c165 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {0, 2, 5} → False := by
  intro a163 n11
  exact n11 (h.down {0, 2, 5, 9} {0, 2, 5} a163 (by decide) (by decide))

theorem c166 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 5, 8} → False := by
  intro a163 n123 n150 n155 n160 n161 n162
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 9} {0, 2, 5} a163 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n123 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n150 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n160 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 5} = {0, 2, 5, 6} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 5} = {0, 2, 5, 7} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 5} = {0, 2, 5, 8} by decide)) hS)
  · exact hne (by decide)

theorem c171 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 6, 9} → False := by
  intro a151 n124 n156 n160 n164 n165 n166
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 6} {0, 2, 6} a151 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n156 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n160 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n164 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 6} = {0, 2, 6, 7} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 6} = {0, 2, 6, 8} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 6} = {0, 2, 6, 9} by decide)) hS)

theorem c172 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {0, 2, 6} → False := by
  intro a156 n12
  exact n12 (h.down {0, 2, 4, 6} {0, 2, 6} a156 (by decide) (by decide))

theorem c176 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {0, 2, 6} → False := by
  intro a164 n12
  exact n12 (h.down {0, 2, 6, 7} {0, 2, 6} a164 (by decide) (by decide))

theorem c180 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {0, 2, 6} → False := by
  intro a166 n12
  exact n12 (h.down {0, 2, 6, 9} {0, 2, 6} a166 (by decide) (by decide))

theorem c182 (h : TenSystem T Q) :
    T {0, 2, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a13 n125 n152 n157 n161 n164 n167 n168
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 7} a13
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c188 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a157 n125 n152 n161 n164 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 4, 7} {0, 2, 7} a157 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c197 (h : TenSystem T Q) :
    T {0, 2, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a14 n126 n153 n158 n162 n165 n167 n169
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 8} a14
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c199 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a126 n153 n158 n162 n165 n167 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 8} {0, 2, 8} a126 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c202 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {0, 2, 8} → False := by
  intro a158 n14
  exact n14 (h.down {0, 2, 4, 8} {0, 2, 8} a158 (by decide) (by decide))

theorem c210 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {0, 2, 8} → False := by
  intro a169 n14
  exact n14 (h.down {0, 2, 8, 9} {0, 2, 8} a169 (by decide) (by decide))

theorem c211 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → False := by
  intro a169 n126 n153 n158 n162 n165 n167
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 8, 9} {0, 2, 8} a169 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c212 (h : TenSystem T Q) :
    T {0, 2, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a15 n127 n154 n159 n163 n166 n168 n169
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 9} a15
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n154 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c226 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  intro a169 n127 n154 n159 n163 n166 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 8, 9} {0, 2, 9} a169 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n154 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c357 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 7, 9} → False := by
  intro a189 n136 n157 n172 n186 n192 n193
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 7} {0, 4, 7} a189 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n186 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 7} = {0, 4, 7, 8} by decide)) hS)
  · exact n193 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 7} = {0, 4, 7, 9} by decide)) hS)

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

theorem c543 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {1, 2, 3} → False := by
  intro a121 n37
  exact n37 (h.down {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide))

theorem c560 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {1, 2, 4} → False := by
  intro a205 n38
  exact n38 (h.down {1, 2, 3, 4} {1, 2, 4} a205 (by decide) (by decide))

theorem c566 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {1, 2, 4} → False := by
  intro a213 n38
  exact n38 (h.down {1, 2, 4, 7} {1, 2, 4} a213 (by decide) (by decide))

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

theorem c633 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {1, 2, 9} → False := by
  intro a127 n43
  exact n43 (h.down {0, 1, 2, 9} {1, 2, 9} a127 (by decide) (by decide))

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

theorem c660 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 3, 4} → False := by
  intro a230 n44
  exact n44 (h.down {1, 3, 4, 9} {1, 3, 4} a230 (by decide) (by decide))

theorem c661 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ Q {0, 1, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 4, 8} → False := by
  intro a230 n128 n205 n226 n227 n228 n229
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 9} {1, 3, 4} a230 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n128 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 4} = {1, 3, 4, 5} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 4} = {1, 3, 4, 6} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 4} = {1, 3, 4, 7} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 4} = {1, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)

theorem c675 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 3, 5} → False := by
  intro a234 n45
  exact n45 (h.down {1, 3, 5, 9} {1, 3, 5} a234 (by decide) (by decide))

theorem c682 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ T {1, 3, 6} → False := by
  intro a227 n46
  exact n46 (h.down {1, 3, 4, 6} {1, 3, 6} a227 (by decide) (by decide))

theorem c686 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {1, 3, 6} → False := by
  intro a235 n46
  exact n46 (h.down {1, 3, 6, 7} {1, 3, 6} a235 (by decide) (by decide))

theorem c690 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 3, 6} → False := by
  intro a237 n46
  exact n46 (h.down {1, 3, 6, 9} {1, 3, 6} a237 (by decide) (by decide))

theorem c705 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 7} → False := by
  intro a239 n47
  exact n47 (h.down {1, 3, 7, 9} {1, 3, 7} a239 (by decide) (by decide))

theorem c728 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a230 n133 n210 n234 n237 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 9} {1, 3, 9} a230 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c765 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ T {1, 4, 6} → False := by
  intro a247 n51
  exact n51 (h.down {1, 4, 6, 9} {1, 4, 6} a247 (by decide) (by decide))

theorem c802 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 4, 9} → False := by
  intro a230 n54
  exact n54 (h.down {1, 3, 4, 9} {1, 4, 9} a230 (by decide) (by decide))

theorem c832 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {1, 5, 7} → False := by
  intro a232 n56
  exact n56 (h.down {1, 3, 5, 7} {1, 5, 7} a232 (by decide) (by decide))

theorem c836 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {1, 5, 7} → False := by
  intro a251 n56
  exact n56 (h.down {1, 5, 6, 7} {1, 5, 7} a251 (by decide) (by decide))

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

theorem c838 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {1, 5, 7} → False := by
  intro a254 n56
  exact n56 (h.down {1, 5, 7, 8} {1, 5, 7} a254 (by decide) (by decide))

theorem c842 (h : TenSystem T Q) :
    T {1, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a57 n141 n218 n233 n243 n252 n254 n256
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 8} a57
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c853 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {1, 5, 8} → False := by
  intro a254 n57
  exact n57 (h.down {1, 5, 7, 8} {1, 5, 8} a254 (by decide) (by decide))

theorem c881 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {1, 6, 7} → False := by
  intro a251 n59
  exact n59 (h.down {1, 5, 6, 7} {1, 6, 7} a251 (by decide) (by decide))

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

theorem c883 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {1, 6, 7} → False := by
  intro a257 n59
  exact n59 (h.down {1, 6, 7, 8} {1, 6, 7} a257 (by decide) (by decide))

theorem c907 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 6, 9} → False := by
  intro a237 n61
  exact n61 (h.down {1, 3, 6, 9} {1, 6, 9} a237 (by decide) (by decide))

theorem c909 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ T {1, 6, 9} → False := by
  intro a247 n61
  exact n61 (h.down {1, 4, 6, 9} {1, 6, 9} a247 (by decide) (by decide))

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

theorem c922 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {1, 7, 8} → False := by
  intro a238 n62
  exact n62 (h.down {1, 3, 7, 8} {1, 7, 8} a238 (by decide) (by decide))

theorem c926 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {1, 7, 8} → False := by
  intro a254 n62
  exact n62 (h.down {1, 5, 7, 8} {1, 7, 8} a254 (by decide) (by decide))

theorem c928 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {1, 7, 8} → False := by
  intro a257 n62
  exact n62 (h.down {1, 6, 7, 8} {1, 7, 8} a257 (by decide) (by decide))

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

theorem c1038 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a154 n70
  exact n70 (h.down {0, 2, 3, 9} {2, 3, 9} a154 (by decide) (by decide))

theorem c1092 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {2, 4, 7, 8} → ¬ Q {2, 4, 7, 9} → False := by
  intro a280 n157 n213 n263 n277 n283 n284
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {2, 4, 7} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n157 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n283 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 7} = {2, 4, 7, 8} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 7} = {2, 4, 7, 9} by decide)) hS)

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

theorem c1340 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {3, 4, 9} → False := by
  intro a230 n90
  exact n90 (h.down {1, 3, 4, 9} {3, 4, 9} a230 (by decide) (by decide))

theorem c1341 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a230 n174 n265 n299 n302 n304 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 9} {3, 4, 9} a230 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
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

theorem c1367 (h : TenSystem T Q) :
    T {3, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {2, 3, 5, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 7, 9} → False := by
  intro a92 n176 n232 n267 n297 n306 n309 n310
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 7} a92
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n176 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n267 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 7} = {2, 3, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n309 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 7} = {3, 5, 7, 8} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 7} = {3, 5, 7, 9} by decide)) hS)

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

theorem c1393 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {3, 5, 8} → False := by
  intro a309 n93
  exact n93 (h.down {3, 5, 7, 8} {3, 5, 8} a309 (by decide) (by decide))

theorem c1410 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 9} → False := by
  intro a311 n94
  exact n94 (h.down {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide))

theorem c1412 (h : TenSystem T Q) :
    T {3, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 7, 9} → False := by
  intro a95 n179 n235 n270 n300 n306 n312 n313
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 6, 7} a95
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact n306 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 7} = {3, 6, 7, 8} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

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

theorem c1445 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {3, 6, 9} → False := by
  intro a237 n97
  exact n97 (h.down {1, 3, 6, 9} {3, 6, 9} a237 (by decide) (by decide))

theorem c1457 (h : TenSystem T Q) :
    T {3, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 7, 8, 9} → False := by
  intro a98 n182 n238 n273 n303 n309 n312 n315
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 7, 8} a98
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n182 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n312 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 7, 8} = {3, 7, 8, 9} by decide)) hS)

theorem c1487 (h : TenSystem T Q) :
    T {3, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a100 n184 n240 n275 n305 n311 n314 n315
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 8, 9} a100
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

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

theorem c1496 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a311 n100
  exact n100 (h.down {3, 5, 8, 9} {3, 8, 9} a311 (by decide) (by decide))

theorem c1497 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a311 n184 n240 n275 n305 n314 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {3, 8, 9} a311 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1539 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a298 n103
  exact n103 (h.down {3, 4, 5, 8} {4, 5, 8} a298 (by decide) (by decide))

theorem c1562 (h : TenSystem T Q) :
    T {4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a105 n189 n245 n280 n300 n316 n322 n323
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 6, 7} a105
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

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

theorem c1570 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a300 n189 n245 n280 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {4, 6, 7} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

theorem c1592 (h : TenSystem T Q) :
    T {4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a107 n191 n247 n282 n302 n318 n323 n324
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 6, 9} a107
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1600 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a302 n191 n247 n282 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 9} {4, 6, 9} a302 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
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

theorem c1652 (h : TenSystem T Q) :
    T {5, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 7, 9} → False := by
  intro a111 n195 n251 n286 n306 n316 n326 n327
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 6, 7} a111
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n195 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact n251 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact n306 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact n316 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 7} = {5, 6, 7, 8} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 7} = {5, 6, 7, 9} by decide)) hS)

theorem c1660 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 7, 9} → False := by
  intro a306 n195 n251 n286 n316 n326 n327
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 7} {5, 6, 7} a306 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n195 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact n251 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 7} = {5, 6, 7, 8} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 7} = {5, 6, 7, 9} by decide)) hS)

theorem c1670 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a252 n112
  exact n112 (h.down {1, 5, 6, 8} {5, 6, 8} a252 (by decide) (by decide))

theorem c1674 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a307 n112
  exact n112 (h.down {3, 5, 6, 8} {5, 6, 8} a307 (by decide) (by decide))

theorem c1682 (h : TenSystem T Q) :
    T {5, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 6, 8, 9} → False := by
  intro a113 n197 n253 n288 n308 n318 n327 n328
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 6, 9} a113
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n197 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1690 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 6, 8, 9} → False := by
  intro a308 n197 n253 n288 n318 n327 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 9} {5, 6, 9} a308 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n197 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1697 (h : TenSystem T Q) :
    T {5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a114 n198 n254 n289 n309 n319 n326 n329
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 7, 8} a114
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1700 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a254 n114
  exact n114 (h.down {1, 5, 7, 8} {5, 7, 8} a254 (by decide) (by decide))

theorem c1701 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a254 n198 n289 n309 n319 n326 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 8} {5, 7, 8} a254 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1704 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a309 n114
  exact n114 (h.down {3, 5, 7, 8} {5, 7, 8} a309 (by decide) (by decide))

theorem c1705 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a309 n198 n254 n289 n319 n326 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 8} {5, 7, 8} a309 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

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

theorem c1742 (h : TenSystem T Q) :
    T {6, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {6, 7, 8, 9} → False := by
  intro a117 n201 n257 n292 n312 n322 n326 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {6, 7, 8} a117
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n201 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact n292 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact n312 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact n322 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact n326 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (9 : Labels) {6, 7, 8} = {6, 7, 8, 9} by decide)) hS)

theorem c1750 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {6, 7, 8, 9} → False := by
  intro a312 n201 n257 n292 n322 n326 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {6, 7, 8} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n201 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact n292 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact n326 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (9 : Labels) {6, 7, 8} = {6, 7, 8, 9} by decide)) hS)

theorem c1779 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a314 n119
  exact n119 (h.down {3, 6, 8, 9} {6, 8, 9} a314 (by decide) (by decide))

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

theorem c1807 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {6, 7, 9} → False := by
  intro a121 a103 a118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a103 a118

theorem c1808 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {6, 7, 8} → False := by
  intro a121 n104 n117
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n104 (hc.mpr n117)

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

theorem c1813 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {5, 7, 9} → False := by
  intro a121 a106 a115
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a106 a115

theorem c1814 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 7, 8} → False := by
  intro a121 n107 n114
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n107 (hc.mpr n114)

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

theorem c1817 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {5, 6, 9} → False := by
  intro a121 a108 a113
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a108 a113

theorem c1818 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 9} → ¬ T {5, 6, 8} → False := by
  intro a121 n109 n112
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n109 (hc.mpr n112)

theorem c1819 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {5, 6, 8} → False := by
  intro a121 a109 a112
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a109 a112

theorem c1820 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {5, 6, 7} → False := by
  intro a121 n110 n111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n110 (hc.mpr n111)

theorem c1857 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {4, 6, 9} → T {4, 8, 9} → False := by
  intro a121 a104 a107 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

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

theorem c1861 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a121 a107 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c1878 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a121 n103 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c1879 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a121 a103 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c1880 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n103 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1881 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a121 a103 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1882 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n103 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1883 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a121 a103 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1884 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n112 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1885 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a121 a112 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1894 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a121 n105 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c1910 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a121 n107 n113 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c1911 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {5, 6, 9} → T {6, 7, 9} → False := by
  intro a121 a107 a113 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

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

theorem c1915 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {6, 7, 9} → T {6, 8, 9} → False := by
  intro a121 a107 a118 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 9} {4, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c1924 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 7, 8} → ¬ T {6, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n114 n117 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1926 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 9} → ¬ T {5, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a121 n109 n115 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n109 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)

theorem c1927 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {5, 7, 9} → T {6, 7, 9} → False := by
  intro a121 a109 a115 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c1946 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a122 n93 n118
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n118)

theorem c2034 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a122 n95 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 4} {6, 7} {3, 5, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c2137 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 9} → T {3, 6, 9} → T {3, 8, 9} → False := by
  intro a123 a90 a97 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {3, 9} {4, 6, 8} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

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

theorem c2270 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {3, 4, 8} → ¬ T {3, 7, 8} → ¬ T {3, 8, 9} → False := by
  intro a124 n89 n98 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 6} {3, 8} {4, 7, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n89 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 8} = {3, 4, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 8} = {3, 7, 8} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 8} = {3, 8, 9} by decide)) ht)

theorem c2378 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {3, 6, 9} → ¬ T {4, 5, 8} → False := by
  intro a125 n97 n103
  have hc := h.complementary {0, 1, 2, 7} {3, 6, 9} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n97 (hc.mpr n103)

theorem c2449 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a125 a90 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 7} {4, 9} {3, 5, 8} a125 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c2555 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 9} → T {3, 5, 9} → T {3, 6, 9} → False := by
  intro a126 a90 a94 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 9} {4, 5, 6} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c2654 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a127 n93 n105
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n105)

theorem c2656 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a127 n95 n103
  have hc := h.complementary {0, 1, 2, 9} {3, 6, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n95 (hc.mpr n103)

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

theorem c3484 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a133 n72 n114
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n72 (hc.mpr n114)

theorem c3485 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 6} → T {5, 7, 8} → False := by
  intro a133 a72 a114
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a72 a114

theorem c3497 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 6, 7} → T {4, 5, 8} → False := by
  intro a133 a80 a103
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a80 a103

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

theorem c4605 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 6} → T {4, 7, 9} → False := by
  intro a141 a67 a109
  have hc := h.complementary {0, 1, 5, 8} {2, 3, 6} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a67 a109

theorem c4638 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 3, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → False := by
  intro a141 n67 n72 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {2, 6} {3, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c4699 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a141 a72 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 6} {2, 7, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c4717 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a141 a90 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 9} {3, 6, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

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

theorem c5003 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {2, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a143 a78 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 7} {5, 8} {2, 4, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c5731 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 6, 7} → T {5, 8, 9} → False := by
  intro a149 a59 a116
  have hc := h.complementary {0, 2, 3, 4} {1, 6, 7} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a59 a116

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

theorem c5924 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a150 n51 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 5} {4, 6} {1, 7, 9} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c6145 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 6} → T {5, 8, 9} → False := by
  intro a152 a51 a116
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a116

theorem c6158 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 6, 9} → ¬ T {4, 5, 8} → False := by
  intro a152 n61 n103
  have hc := h.complementary {0, 2, 3, 7} {1, 6, 9} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n61 (hc.mpr n103)

theorem c6229 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a152 a54 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 7} {4, 9} {1, 5, 8} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c6284 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 6} → ¬ T {5, 7, 9} → False := by
  intro a153 n51 n115
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 6} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n115)

theorem c6293 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 5, 7} → T {4, 6, 9} → False := by
  intro a153 a56 a107
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 7} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a56 a107

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

theorem c6409 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a153 a61 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {6, 9} {1, 4, 7} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c6434 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a154 n57 n105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n105)

theorem c6436 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a154 n59 n103
  have hc := h.complementary {0, 2, 3, 9} {1, 6, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n59 (hc.mpr n103)

theorem c6473 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 7} → T {1, 6, 7} → T {1, 7, 8} → False := by
  intro a154 a56 a59 a62
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {1, 7} {5, 6, 8} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) a62)

theorem c6558 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 7, 8} → ¬ T {5, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a154 n62 n114 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 9} {7, 8} {1, 5, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) ht)

theorem c6654 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a155 n59 n95 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 5} {6, 7} {1, 3, 8} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c6671 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {1, 6, 9} → T {3, 6, 9} → T {6, 7, 9} → False := by
  intro a155 a61 a97 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {6, 9} {1, 3, 7} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c6802 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a156 n57 n93 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 6} {5, 8} {1, 3, 7} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c6818 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 7, 8} → ¬ T {3, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a156 n62 n98 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 6} {7, 8} {1, 3, 5} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)

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

theorem c6942 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a157 n57 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {5, 8} {1, 3, 6} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c7082 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a158 n56 n92 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 8} {5, 7} {1, 3, 6} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c7098 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a158 n59 n95 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 8} {6, 7} {1, 3, 5} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)

theorem c7109 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 6, 9} → T {3, 6, 9} → T {6, 7, 9} → False := by
  intro a158 a61 a97 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {6, 9} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c7234 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a159 n57 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {5, 8} {1, 6, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c7242 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a159 n59 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {6, 7} {1, 5, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

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

theorem c7269 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → T {1, 3, 9} → T {4, 7, 8} → False := by
  intro a160 a49 a108
  have hc := h.complementary {0, 2, 5, 6} {1, 3, 9} a160 (by decide) (by decide)
  have he : ( {0, 2, 5, 6} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a108

theorem c7371 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → T {1, 4, 9} → T {3, 4, 9} → T {4, 7, 9} → False := by
  intro a160 a54 a90 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 6} {4, 9} {1, 3, 7} a160 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c7425 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 3, 4} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a161 a44 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {1, 3} {4, 6, 9} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c7513 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 4, 9} → T {3, 4, 9} → T {4, 8, 9} → False := by
  intro a161 a54 a90 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {4, 9} {1, 3, 8} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c7557 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 6, 7} → T {3, 4, 9} → False := by
  intro a162 a59 a90
  have hc := h.complementary {0, 2, 5, 8} {1, 6, 7} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 6, 7} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a59 a90

theorem c7565 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 4} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a162 a44 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {1, 3} {4, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c7573 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a162 a44 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {1, 4} {3, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c7578 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → ¬ T {1, 6, 7} → False := by
  intro a162 n46 n51 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 8} {1, 6} {3, 4, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c7683 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 3, 4} → T {6, 7, 8} → False := by
  intro a163 a44 a117
  have hc := h.complementary {0, 2, 5, 9} {1, 3, 4} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 3, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a44 a117

theorem c7718 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → ¬ T {1, 6, 7} → False := by
  intro a163 n46 n51 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 9} {1, 6} {3, 4, 7} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c7823 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 3, 4} → T {5, 8, 9} → False := by
  intro a164 a44 a116
  have hc := h.complementary {0, 2, 6, 7} {1, 3, 4} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 3, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a44 a116

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

theorem c7933 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 4, 9} → T {3, 4, 9} → T {4, 8, 9} → False := by
  intro a164 a54 a90 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {4, 9} {1, 3, 8} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c7969 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 3, 9} → T {4, 5, 7} → False := by
  intro a165 a49 a102
  have hc := h.complementary {0, 2, 6, 8} {1, 3, 9} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a49 a102

theorem c8073 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 4, 9} → T {3, 4, 9} → T {4, 7, 9} → False := by
  intro a165 a54 a90 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {4, 9} {1, 3, 7} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c8103 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 3, 4} → T {5, 7, 8} → False := by
  intro a166 a44 a114
  have hc := h.complementary {0, 2, 6, 9} {1, 3, 4} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 3, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a44 a114

theorem c8228 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n57 n93 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {5, 8} {1, 3, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c8236 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {1, 7, 8} → ¬ T {3, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n62 n98 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {7, 8} {1, 3, 5} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)

theorem c8267 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 3, 4} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a167 a44 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {1, 3} {4, 6, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c8275 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 3, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a167 a44 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {1, 4} {3, 6, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c8351 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 4, 9} → T {3, 4, 9} → T {4, 5, 9} → False := by
  intro a167 a54 a90 a104
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {4, 9} {1, 3, 5} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)

theorem c8386 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {1, 3, 6} → ¬ T {4, 5, 8} → False := by
  intro a168 n46 n103
  have hc := h.complementary {0, 2, 7, 9} {1, 3, 6} a168 (by decide) (by decide)
  have he : ( {0, 2, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n46 (hc.mpr n103)

theorem c8393 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 6} → T {3, 5, 8} → False := by
  intro a168 a51 a93
  have hc := h.complementary {0, 2, 7, 9} {1, 4, 6} a168 (by decide) (by decide)
  have he : ( {0, 2, 7, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a51 a93

theorem c8403 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 3, 4} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a168 a44 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {1, 3} {4, 5, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c8508 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a168 n57 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 9} {5, 8} {1, 3, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

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

theorem c8568 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → ¬ T {1, 6, 7} → False := by
  intro a169 n46 n51 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {1, 6} {3, 4, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c8648 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a169 n56 n92 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {5, 7} {1, 3, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c8953 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 8} → T {2, 6, 9} → False := by
  intro a172 a57 a82
  have hc := h.complementary {0, 3, 4, 7} {1, 5, 8} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a82

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

theorem c9203 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a173 a59 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {6, 7} {1, 5, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c9273 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 5, 7} → T {1, 6, 7} → T {1, 7, 8} → False := by
  intro a174 a56 a59 a62
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {1, 7} {5, 6, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) a62)

theorem c9615 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 4, 9} → T {4, 6, 9} → T {4, 8, 9} → False := by
  intro a176 a54 a107 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 7} {4, 9} {1, 6, 8} a176 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c9645 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 6} → T {4, 7, 9} → False := by
  intro a177 a40 a109
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 6} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a109

theorem c9710 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → False := by
  intro a177 n40 n72 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 8} {2, 6} {1, 4, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

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

theorem c9741 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {2, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a177 a72 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 6} {2, 7, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c9755 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a177 a54 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 9} {1, 6, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c10035 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a179 a54 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 7} {4, 9} {1, 5, 8} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

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

theorem c10455 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 4, 9} → T {4, 5, 9} → T {4, 6, 9} → False := by
  intro a182 a54 a104 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {4, 9} {1, 5, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)

theorem c10751 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 7} → T {4, 5, 7} → T {5, 6, 7} → False := by
  intro a184 a56 a102 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {5, 7} {1, 4, 6} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)

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

theorem c10933 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a186 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {1, 3} {2, 6, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c11722 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 7, 8} → False := by
  intro a191 n56 n92 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 9} {5, 7} {1, 3, 8} a191 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) ht)

theorem c11775 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a192 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {1, 3} {2, 6, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c11883 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {5, 6, 8} → False := by
  intro a193 a37 a112
  have hc := h.complementary {0, 4, 7, 9} {1, 2, 3} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a112

theorem c12193 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a195 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 3} {2, 4, 9} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c12333 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a196 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 3} {2, 4, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12471 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 7} → False := by
  intro a197 a37 a44 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 9} {1, 3} {2, 4, 7} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

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

theorem c12613 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a198 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 3} {2, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12751 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a199 a37 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 9} {1, 3} {2, 4, 6} a199 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c12891 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a200 a37 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 3} {2, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

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

theorem c13033 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a201 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 3} {2, 4, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c15497 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a218 a90 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {4, 9} {3, 6, 7} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c15783 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a220 a29 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 7} {5, 8} {0, 4, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c16611 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 6, 9} → T {2, 6, 9} → T {6, 7, 9} → False := by
  intro a226 a33 a82 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {6, 9} {0, 2, 7} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c16784 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 2, 6} → ¬ T {5, 8, 9} → False := by
  intro a228 n12 n116
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 6} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n116)

theorem c16788 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 2, 9} → ¬ T {5, 6, 8} → False := by
  intro a228 n15 n112
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 9} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n112)

theorem c16926 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → ¬ T {0, 2, 7} → ¬ T {5, 6, 9} → False := by
  intro a229 n13 n113
  have hc := h.complementary {1, 3, 4, 8} {0, 2, 7} a229 (by decide) (by decide)
  have he : ( {1, 3, 4, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n113)

theorem c17049 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → T {0, 6, 9} → T {2, 6, 9} → T {6, 7, 9} → False := by
  intro a229 a33 a82 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 8} {6, 9} {0, 2, 7} a229 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c17062 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {6, 7, 8} → False := by
  intro a230 n11 n117
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 5} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n117)

theorem c17064 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {5, 7, 8} → False := by
  intro a230 n12 n114
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 6} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n114)

theorem c17065 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 6} → T {5, 7, 8} → False := by
  intro a230 a12 a114
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 6} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a114

theorem c17066 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 7} → ¬ T {5, 6, 8} → False := by
  intro a230 n13 n112
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 7} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n112)

theorem c17067 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 7} → T {5, 6, 8} → False := by
  intro a230 a13 a112
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 7} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a13 a112

theorem c17068 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 8} → ¬ T {5, 6, 7} → False := by
  intro a230 n14 n111
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 8} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n111)

theorem c17074 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 5, 8} → ¬ T {2, 6, 7} → False := by
  intro a230 n29 n80
  have hc := h.complementary {1, 3, 4, 9} {0, 5, 8} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n80)

theorem c17075 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 5, 8} → T {2, 6, 7} → False := by
  intro a230 a29 a80
  have hc := h.complementary {1, 3, 4, 9} {0, 5, 8} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a80

theorem c17082 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a230 n11 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {0, 2} {5, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

theorem c17083 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 5} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a230 a11 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 9} {0, 2} {5, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c17084 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 8} → False := by
  intro a230 n11 n12 n14
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {0, 2} {5, 6, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)

theorem c17085 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 5} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a230 a11 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 9} {0, 2} {5, 6, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c17088 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → ¬ T {0, 2, 8} → False := by
  intro a230 n12 n13 n14
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {0, 2} {6, 7, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)

theorem c17089 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 6} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a230 a12 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 9} {0, 2} {6, 7, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c17130 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {2, 5, 6} → ¬ T {2, 6, 7} → False := by
  intro a230 n12 n76 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {2, 6} {0, 5, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c17134 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {2, 6, 7} → ¬ T {2, 6, 8} → False := by
  intro a230 n12 n80 n81
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {2, 6} {0, 7, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)
  · exact n81 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) ht)

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

theorem c17174 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a230 n29 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {5, 8} {0, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c17176 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a230 n78 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {5, 8} {2, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c17487 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 7} → T {4, 6, 9} → False := by
  intro a233 a13 a107
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 7} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a107

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

theorem c17624 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 6} → ¬ T {4, 7, 8} → False := by
  intro a234 n12 n108
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 6} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n108)

theorem c17626 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 7} → ¬ T {4, 6, 8} → False := by
  intro a234 n13 n106
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n106)

theorem c17883 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a235 a29 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {5, 8} {0, 4, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c18042 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 4} → ¬ T {5, 7, 8} → False := by
  intro a237 n10 n114
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 4} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n114)

theorem c18046 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 7} → ¬ T {4, 5, 8} → False := by
  intro a237 n13 n103
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n103)

theorem c18047 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 7} → T {4, 5, 8} → False := by
  intro a237 a13 a103
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a13 a103

theorem c18322 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 4} → ¬ T {5, 6, 8} → False := by
  intro a239 n10 n112
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 4} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n112)

theorem c18326 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 6} → ¬ T {4, 5, 8} → False := by
  intro a239 n12 n103
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n103)

theorem c18327 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 6} → T {4, 5, 8} → False := by
  intro a239 a12 a103
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a103

theorem c18405 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {2, 4, 6} → T {2, 5, 6} → T {2, 6, 8} → False := by
  intro a239 a72 a76 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 9} {2, 6} {4, 5, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) a81)

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

theorem c18903 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a243 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 2} {3, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19163 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {5, 8, 9} → False := by
  intro a245 a9 a116
  have hc := h.complementary {1, 4, 6, 7} {0, 2, 3} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a116

theorem c19183 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 8} → False := by
  intro a245 a9 a11 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {0, 2} {3, 5, 8} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

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

theorem c19449 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 8} → T {3, 5, 7} → False := by
  intro a247 a14 a92
  have hc := h.complementary {1, 4, 6, 9} {0, 2, 8} a247 (by decide) (by decide)
  have he : ( {1, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a14 a92

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

theorem c20004 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 2, 4} → ¬ T {3, 8, 9} → False := by
  intro a251 n10 n100
  have hc := h.complementary {1, 5, 6, 7} {0, 2, 4} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n100)

theorem c20008 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 2, 9} → ¬ T {3, 4, 8} → False := by
  intro a251 n15 n89
  have hc := h.complementary {1, 5, 6, 7} {0, 2, 9} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 4, 8} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n89)

theorem c20025 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a251 a9 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {0, 2} {3, 4, 9} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c20303 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a253 a9 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 9} {0, 2} {3, 4, 7} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c20425 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 4} → T {3, 6, 9} → False := by
  intro a254 a10 a97
  have hc := h.complementary {1, 5, 7, 8} {0, 2, 4} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a97

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

theorem c20448 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 2, 6} → ¬ T {0, 2, 9} → False := by
  intro a254 n10 n12 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 8} {0, 2} {4, 6, 9} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c20727 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a256 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {0, 2} {3, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

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

theorem c20868 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 2, 5} → ¬ T {0, 2, 9} → False := by
  intro a257 n10 n11 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 8} {0, 2} {4, 5, 9} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c20983 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 2, 3} → T {4, 5, 8} → False := by
  intro a258 a9 a103
  have hc := h.complementary {1, 6, 7, 9} {0, 2, 3} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a103

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

theorem c21699 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 6, 9} → T {1, 5, 8} → False := by
  intro a263 a33 a57
  have hc := h.complementary {2, 3, 4, 7} {0, 6, 9} a263 (by decide) (by decide)
  have he : ( {2, 3, 4, 7} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a33 a57

theorem c21945 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → T {1, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a264 a59 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 8} {6, 7} {1, 5, 9} a264 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c22045 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {1, 5, 7} → T {1, 6, 7} → T {1, 7, 8} → False := by
  intro a265 a56 a59 a62
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {1, 7} {5, 6, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) a62)

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

theorem c22357 (h : TenSystem T Q) :
    Q {2, 3, 5, 7} → T {1, 4, 9} → T {4, 6, 9} → T {4, 8, 9} → False := by
  intro a267 a54 a107 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 7} {4, 9} {1, 6, 8} a267 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c22497 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a268 a54 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 9} {1, 6, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

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

theorem c22777 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {1, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a270 a54 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {4, 9} {1, 5, 8} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

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

theorem c23197 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → T {1, 4, 9} → T {4, 5, 9} → T {4, 6, 9} → False := by
  intro a273 a54 a104 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 8} {4, 9} {1, 5, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)

theorem c23493 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {1, 5, 7} → T {4, 5, 7} → T {5, 6, 7} → False := by
  intro a275 a56 a102 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {5, 7} {1, 4, 6} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)

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

theorem c23705 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a277 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {1, 3} {0, 6, 9} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c24464 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 7, 8} → False := by
  intro a282 n56 n92 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 9} {5, 7} {1, 3, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) ht)

theorem c24547 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a283 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {1, 3} {0, 6, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24623 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {5, 6, 8} → False := by
  intro a284 a2 a112
  have hc := h.complementary {2, 4, 7, 9} {0, 1, 3} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a112

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

theorem c24965 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a286 a2 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 7} {1, 3} {0, 4, 9} a286 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c25243 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 7} → False := by
  intro a288 a2 a44 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 9} {1, 3} {0, 4, 7} a288 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c25385 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a289 a2 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {1, 3} {0, 4, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c25523 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a290 a2 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 9} {1, 3} {0, 4, 6} a290 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c25663 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a291 a2 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {1, 3} {0, 4, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c25805 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a292 a2 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 7, 8} {1, 3} {0, 4, 9} a292 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c26471 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a297 a1 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {0, 2} {1, 6, 8} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c26611 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a298 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {0, 2} {1, 6, 7} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

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

theorem c26731 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 2, 6} → T {1, 7, 8} → False := by
  intro a299 a12 a62
  have hc := h.complementary {3, 4, 5, 9} {0, 2, 6} a299 (by decide) (by decide)
  have he : ( {3, 4, 5, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a62

theorem c26891 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 8} → False := by
  intro a300 a1 a11 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 2} {1, 5, 8} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

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

theorem c27151 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 2, 5} → T {1, 7, 8} → False := by
  intro a302 a11 a62
  have hc := h.complementary {3, 4, 6, 9} {0, 2, 5} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a62

theorem c27155 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 2, 8} → T {1, 5, 7} → False := by
  intro a302 a14 a56
  have hc := h.complementary {3, 4, 6, 9} {0, 2, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a14 a56

theorem c27176 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 7} → ¬ T {0, 2, 8} → False := by
  intro a302 n11 n13 n14
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 9} {0, 2} {5, 7, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)

theorem c27311 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 6} → False := by
  intro a303 a1 a11 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {0, 2} {1, 5, 6} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c27423 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {5, 6, 8} → False := by
  intro a304 a1 a112
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 2} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a112

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

theorem c27573 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 6} → T {1, 5, 7} → False := by
  intro a305 a12 a56
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 6} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a56

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

theorem c28124 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 1, 4} → ¬ T {2, 6, 9} → False := by
  intro a309 n3 n82
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 4} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 6, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n82)

theorem c28130 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 2, 4} → ¬ T {1, 6, 9} → False := by
  intro a309 n10 n61
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 4} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 6, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n61)

theorem c28131 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 2, 4} → T {1, 6, 9} → False := by
  intro a309 a10 a61
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 4} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a61

theorem c28134 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 2, 9} → ¬ T {1, 4, 6} → False := by
  intro a309 n15 n51
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n51)

theorem c28135 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 2, 9} → T {1, 4, 6} → False := by
  intro a309 a15 a51
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a15 a51

theorem c28140 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 6, 9} → ¬ T {1, 2, 4} → False := by
  intro a309 n33 n38
  have hc := h.complementary {3, 5, 7, 8} {0, 6, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n38)

theorem c28153 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a309 a1 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {0, 2} {1, 4, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c28156 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 2, 6} → ¬ T {0, 2, 9} → False := by
  intro a309 n10 n12 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {0, 2} {4, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c28195 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a309 a3 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 4} {0, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c28197 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {1, 2, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a309 a38 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 4} {2, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

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

theorem c28213 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {1, 2, 9} → T {1, 4, 9} → T {1, 6, 9} → False := by
  intro a309 a43 a54 a61
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 9} {2, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) a61)

theorem c28240 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {1, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a309 n23 n51 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {4, 6} {0, 1, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c28244 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {1, 4, 6} → ¬ T {2, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a309 n51 n72 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {4, 6} {1, 2, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c28291 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 6} → False := by
  intro a310 a1 a10 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {0, 2} {1, 4, 6} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c28295 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a310 a1 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {0, 2} {1, 6, 8} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c28414 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 7} → ¬ T {1, 4, 6} → False := by
  intro a311 n13 n51
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n51)

theorem c28415 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 7} → T {1, 4, 6} → False := by
  intro a311 a13 a51
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a51

theorem c28435 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a311 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 2} {1, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases073
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

theorem c28715 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 8} → False := by
  intro a313 a1 a11 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {0, 2} {1, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

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

theorem c28995 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 6} → False := by
  intro a315 a1 a11 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 2} {1, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

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

theorem c31281 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → T {4, 6, 7} → ¬ Q {0, 4, 6, 7} → False := by
  classical
  intro n280 n245 a105 n189
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1562 h a105 n189 n245 n280 hv u0_316 u1_322 u2_323
  exact c1570 h u3_300 n189 n245 n280 u0_316 u1_322 u2_323

theorem c31290 (h : TenSystem T Q) :
    ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 4, 9} → T {0, 2, 4} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 2, 4, 5} → False := by
  classical
  intro n157 n158 n159 a10 n156 n122 n155
  have u0_149 : Q {0, 2, 3, 4} := by
    by_contra hv
    exact c137 h a10 n122 hv n155 n156 n157 n158 n159
  exact c141 h u0_149 n122 n155 n156 n157 n158 n159

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

theorem c31353 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → False := by
  classical
  intro a116 n200 n311 n291
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c1727 h a116 n200 hv n291 n311 u0_321 u1_328 u2_329
  exact c1731 h u3_256 n200 n291 n311 u0_321 u1_328 u2_329

theorem c31376 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 6, 9} → T {5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → False := by
  classical
  intro n197 a113 n253 n288
  have u0_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c1690 h hv n197 n253 n288 u2_318 u1_327 u0_328
  exact c1682 h a113 n197 n253 n288 u3_308 u2_318 u1_327 u0_328

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

theorem c31378 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 5, 6, 7} → T {5, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {0, 5, 6, 7} → False := by
  classical
  intro n286 a111 n251 n195
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u3_306 : Q {3, 5, 6, 7} := by
    by_contra hv
    exact c1652 h a111 n195 n251 n286 hv u0_316 u1_326 u2_327
  exact c1660 h u3_306 n195 n251 n286 u0_316 u1_326 u2_327

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases091
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

private theorem c31438 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 7} → Q {1, 3, 6, 9} → Q {1, 3, 4, 9} → False := by
  classical
  intro n103 n167 n162 n161 a237 a230
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u4_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12891 h hv u1_37 u3_44 u4_46
  have u6_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25663 h hv u0_2 u3_44 u4_46
  have u7_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u8_61 : T {1, 6, 9} := by
    by_contra hv
    exact c907 h a237 hv
  have u9_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u10_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u2_121 n103 hv
  have u12_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv n103
  have u13_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7109 h hv u8_61 u7_97 u11_118
  have u14_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6671 h hv u8_61 u7_97 u11_118
  have u15_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c17067 h a230 u12_13 hv
  have u16_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u2_121 hv u15_112
  have u17_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1878 h u2_121 n103 u15_112 hv
  have u18_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1880 h u2_121 n103 u15_112 hv
  have u19_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u2_121 u16_109 hv u11_118
  have u20_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8073 h hv u10_54 u9_90 u16_109
  have u21_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7371 h hv u10_54 u9_90 u16_109
  have u22_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u2_121 hv u17_114
  have u23_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv u17_114
  have u24_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u18_116
  have u25_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u18_116 u5_200 hv u6_291
  have u26_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h u25_311 hv
  have u27_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1496 h u25_311 hv
  have u28_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c28415 h u25_311 u12_13 hv
  have u29_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2555 h hv u9_90 u26_94 u7_97
  have u30_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2137 h hv u9_90 u7_97 u27_100
  have u31_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6284 h hv u28_51 u19_115
  have u32_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5924 h hv u28_51 u24_105 u22_107
  have u33_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c211 h hv u29_126 u31_153 u13_158 n162 u20_165 n167
  have u34_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c166 h hv u30_123 u32_150 u14_155 u21_160 n161 n162
  have u35_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c152 h hv u30_123 u32_150 u14_155 u21_160 n161 n162 u34_163
  have u36_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c197 h hv u29_126 u31_153 u13_158 n162 u20_165 n167 u33_169
  exact c17084 h a230 u35_11 u23_12 u36_14

theorem c31440 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 6, 9} → Q {1, 3, 4, 9} → T {1, 3, 9} → False := by
  classical
  intro a237 a230 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u5_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u6_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25523 h hv u0_2 u4_44 u5_46
  have u7_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12751 h hv u1_37 u4_44 u5_46
  have u8_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7425 h hv u4_44 u5_46 a49
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7565 h hv u4_44 u5_46 a49
  have u10_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8267 h hv u4_44 u5_46 a49
  have u11_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31438 h h0 hv u10_167 u9_162 u8_161 a237 a230
  have u12_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 u11_103 hv
  have u13_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv u11_103
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c17066 h a230 u13_13 hv
  have u15_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u2_121 hv u14_112
  have u16_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1879 h u2_121 u11_103 u14_112 hv
  have u17_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1926 h u2_121 u15_109 hv u12_118
  have u18_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18042 h a237 hv u16_114
  have u19_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv u16_114
  have u20_310 : Q {3, 5, 7, 9} := by
    by_contra hv
    exact c31335 h h0 u17_115 hv u6_290 u7_199
  exact c28291 h u20_310 u3_1 u18_10 u19_12

theorem c31441 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {0, 2, 5, 8} → T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a112 n162 a103 n237 n198 n196 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u0_121 a103 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u0_121 hv a112
  have u3_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h a230 hv a112
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1881 h u0_121 a103 a112 hv
  have u5_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1879 h u0_121 a103 a112 hv
  have u6_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1926 h u0_121 u2_109 hv u1_118
  have u7_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u4_116
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u0_121 hv u4_116
  have u9_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u0_121 hv u5_114
  have u10_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv u5_114
  have u11_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1813 h u0_121 hv u6_115
  have u12_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18327 h hv u10_12 a103
  have u13_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u3_13 u11_106
  have u14_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c728 h a230 hv n210 u13_234 n237 u12_239 n240
  have u15_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c3497 h u14_133 hv a103
  have u16_72 : T {2, 4, 6} := by
    by_contra hv
    exact c3484 h u14_133 hv u5_114
  have u17_29 : T {0, 5, 8} := by
    by_contra hv
    exact c17074 h a230 hv u15_80
  have u18_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9741 h hv u16_72 u8_105 u9_107
  have u19_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4699 h hv u16_72 u8_105 u9_107
  have u20_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c430 h hv u19_141 n162 u18_177 n196 n198 u7_200
  exact c422 h u17_29 u19_141 n162 u18_177 u20_187 n196 n198 u7_200

theorem c31442 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 8} → ¬ T {5, 6, 8} → T {4, 5, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro n114 n112 a103 n195 n286 a230
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17066 h a230 hv n112
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u2_121 hv n112
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1674 h hv n112
  have u6_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1670 h hv n112
  have u7_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c20983 h hv u0_9 a103
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 a103 hv
  have u9_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u10_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u11_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c1700 h hv n114
  have u12_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u13_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u2_121 hv n114
  have u14_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1884 h u2_121 n112 n114 hv
  have u15_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv n114
  have u16_29 : T {0, 5, 8} := by
    by_contra hv
    exact c17174 h a230 hv n112 n114
  have u17_78 : T {2, 5, 8} := by
    by_contra hv
    exact c17176 h a230 hv n112 n114
  have u18_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1861 h u2_121 u13_107 u4_109 hv
  have u19_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17487 h hv u3_13 u13_107
  have u20_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9755 h hv u10_54 u13_107 u4_109
  have u21_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22497 h hv u10_54 u13_107 u4_109
  have u22_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u9_90 u13_107 u4_109
  have u23_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15497 h hv u9_90 u13_107 u4_109
  have u24_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u14_116
  have u25_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19163 h hv u0_9 u14_116
  have u26_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c17089 h a230 u15_12 u3_13 hv
  have u27_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18903 h hv u0_9 u15_12 u3_13
  have u28_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26611 h hv u1_1 u15_12 u3_13
  have u29_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20727 h hv u0_9 u15_12 u3_13
  have u30_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28435 h hv u1_1 u15_12 u3_13
  have u31_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c17083 h a230 hv u15_12 u3_13
  have u32_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17883 h hv u16_29 a103 u14_116
  have u33_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15783 h hv u16_29 a103 u14_116
  have u34_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5003 h hv u17_78 a103 u14_116
  have u35_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u2_121 u18_110 hv
  have u36_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c202 h hv u26_14
  have u37_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c210 h hv u26_14
  have u38_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c842 h hv u22_141 u23_218 u19_233 u27_243 u6_252 u11_254 u29_256
  have u39_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u20_177 u19_233 u21_268 u28_298 u5_307 u12_309 u30_311
  have u40_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c157 h hv u31_11
  have u41_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c165 h hv u31_11
  have u42_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u35_111 hv n195
  have u43_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6434 h hv u38_57 u24_105
  have u44_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6802 h hv u38_57 u39_93 n114
  have u45_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7234 h hv u38_57 n112 n114
  have u46_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8228 h hv u38_57 u39_93 n114
  have u47_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8508 h hv u38_57 u39_93 n112
  have u48_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1946 h hv u39_93 u8_118
  have u49_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2654 h hv u39_93 u24_105
  have u50_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6942 h hv u38_57 u39_93 n112
  have u51_257 : Q {1, 6, 7, 8} := by
    by_contra hv
    exact c882 h u42_251 u34_143 u33_220 u32_235 u25_245 hv u7_258
  have u52_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c212 h hv u49_127 u43_154 u45_159 u41_163 u46_166 u47_168 u37_169
  have u53_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u50_157 u36_158 u45_159 hv u44_156 u48_122 u40_155
  exact c20868 h u51_257 u53_10 u31_11 u52_15

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

private theorem c31444 (h : TenSystem T Q) :
    T {2, 4, 6} → ¬ T {2, 6, 7} → ¬ Q {1, 3, 5, 9} → T {5, 7, 8} → ¬ Q {1, 3, 6, 9} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a72 n80 n234 a114 n237 a230 n240 n210
  have u0_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv a114
  have u1_81 : T {2, 6, 8} := by
    by_contra hv
    exact c17134 h a230 u0_12 n80 hv
  have u2_76 : T {2, 5, 6} := by
    by_contra hv
    exact c17130 h a230 u0_12 hv n80
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18405 h hv a72 u2_76 u1_81
  have u4_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3485 h hv a72 a114
  exact c728 h a230 u4_133 n210 n234 n237 u3_239 n240

private theorem c31445 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → T {4, 7, 9} → False := by
  classical
  intro a177 n72 n80 a109
  have u0_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c9645 h a177 hv a109
  exact c9710 h a177 u0_40 n72 n80

private theorem c31446 (h : TenSystem T Q) :
    T {0, 5, 8} → ¬ Q {1, 3, 5, 9} → ¬ Q {0, 5, 8, 9} → T {5, 7, 8} → T {4, 7, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a29 n234 n200 a114 a109 n162 n237 n198 n196 a230 n240 n210
  have u0_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c17075 h a230 a29 hv
  have u1_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c31444 h hv u0_80 n234 a114 n237 a230 n240 n210
  have u2_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c31445 h hv u1_72 u0_80 a109
  have u3_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c31443 h u2_177 hv a29 n200 n162 n198 n196
  have u4_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c4605 h u3_141 hv a109
  exact c4638 h u3_141 u4_67 u1_72 u0_80

theorem c31447 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 2, 5, 8} → T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {0, 5, 6, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n162 a103 n237 n198 n195 n286 n196 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u4_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u0_121 a103 hv
  have u5_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31441 h h0 hv n162 a103 n237 n198 n196 a230 n240 n210
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u0_121 hv u6_112
  have u8_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17066 h a230 hv u6_112
  have u9_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31442 h h0 hv u6_112 a103 n195 n286 a230
  have u10_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u0_121 hv u9_114
  have u11_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1883 h u0_121 a103 u9_114 hv
  have u12_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv u9_114
  have u13_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1910 h u0_121 u10_107 hv u4_118
  have u14_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u11_116
  have u15_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u0_121 hv u13_113
  have u16_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17624 h hv u12_12 u15_108
  have u17_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c31446 h hv u16_234 u14_200 u9_114 u7_109 n162 n237 n198 n196 a230 n240 n210
  have u18_80 : T {2, 6, 7} := by
    by_contra hv
    exact c17074 h a230 u17_29 hv
  have u19_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3497 h hv u18_80 a103
  have u20_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c728 h a230 u19_133 n210 u16_234 n237 hv n240
  have u21_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u20_239 hv
  have u22_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18322 h u20_239 hv u6_112
  have u23_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25243 h hv u1_2 u5_44 u21_47
  have u24_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12471 h hv u2_37 u5_44 u21_47
  have u25_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20303 h hv u3_9 u22_10 u8_13
  exact c31376 h h0 u24_197 u13_113 u25_253 u23_288

theorem c31448 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → Q {1, 3, 4, 9} → T {1, 3, 9} → False := by
  classical
  intro a162 a230 a49
  have u0_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u1_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u2_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u3_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c7557 h a162 hv u0_90
  have u4_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c7565 h a162 u2_44 hv a49
  have u5_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c7573 h a162 u2_44 hv u1_54
  exact c7578 h a162 u4_46 u5_51 u3_59

theorem c31449 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 6, 7} → ¬ T {1, 4, 6} → ¬ T {1, 3, 6} → ¬ T {4, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro n59 n51 n46 n103 n198 n201 n195 n292 n289 n286 a230
  have u0_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u1_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u6_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u7_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u8_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u9_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8386 h hv n46 n103
  have u10_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c686 h hv n46
  have u11_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u12_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u13_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c881 h hv n59
  have u14_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c883 h hv n59
  have u15_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6436 h hv n59 n103
  have u16_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7718 h hv n46 n51 n59
  have u17_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8568 h hv n46 n51 n59
  have u18_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1660 h hv n195 u13_251 n286 u1_316 u7_326 u0_327
  have u19_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 n286 hv u13_251 n195
  have u20_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u14_257 n292 u3_322 u7_326 u2_330
  have u21_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1820 h u5_121 hv u19_111
  have u22_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17068 h a230 hv u19_111
  have u23_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u14_257 n292 u20_312 u3_322 u7_326 u2_330
  have u24_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7513 h hv u12_54 u11_90 u21_110
  have u25_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7933 h hv u12_54 u11_90 u21_110
  have u26_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1808 h u5_121 hv u23_117
  have u27_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u23_117
  have u28_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7242 h hv n59 u19_111 u23_117
  have u29_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10035 h hv u12_54 u26_104 u21_110
  have u30_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8351 h hv u12_54 u11_90 u26_104
  have u31_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1857 h u5_121 u26_104 hv u21_110
  have u32_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22777 h hv u12_54 u26_104 u21_110
  have u33_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6229 h hv u12_54 u26_104 u21_110
  have u34_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2449 h hv u11_90 u26_104 u21_110
  have u35_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28715 h hv u4_1 u27_11 u22_14
  have u36_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17085 h a230 u27_11 hv u22_14
  have u37_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26891 h hv u4_1 u27_11 u22_14
  have u38_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c1412 h hv u29_179 u10_235 u32_270 u37_300 u18_306 u20_312 u35_313
  have u39_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c188 h hv u34_125 u33_152 u24_161 u25_164 u30_167 u9_168
  have u40_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1814 h u5_121 u31_107 hv
  have u41_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c172 h hv u36_12
  have u42_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c180 h hv u36_12
  have u43_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7098 h hv n59 u38_95 u19_111
  have u44_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2656 h hv u38_95 n103
  have u45_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c2034 h hv u38_95 u19_111 u23_117
  have u46_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6654 h hv n59 u38_95 u23_117
  have u47_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c212 h hv u44_127 u15_154 u28_159 u16_163 u42_166 u9_168 u17_169
  have u48_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u39_157 u43_158 u28_159 hv u41_156 u45_122 u46_155
  have u49_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20448 h hv u48_10 u36_12 u47_15
  have u50_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28156 h hv u48_10 u36_12 u47_15
  exact c1697 h u40_114 n198 u49_254 n289 u50_309 u8_319 u7_326 u6_329

theorem c31450 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 7, 8} → T {5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → False := by
  classical
  intro n309 a114 n198 n289
  have u0_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c1701 h hv n198 n289 n309 u2_319 u1_326 u0_329
  exact c1697 h a114 n198 u3_254 n289 n309 u2_319 u1_326 u0_329

theorem c31451 (h : TenSystem T Q) :
    ¬ Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 3, 9} → T {0, 2, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  classical
  intro n163 n127 n159 n154 a15 n166 n168
  have u0_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c226 h hv n127 n154 n159 n163 n166 n168
  exact c212 h a15 n127 n154 n159 n163 n166 n168 u0_169

private theorem c31452 (h : TenSystem T Q) :
    ¬ T {0, 2, 4} → Q {1, 3, 5, 9} → ¬ Q {0, 2, 3, 9} → T {0, 2, 9} → Q {3, 5, 7, 8} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → Q {1, 3, 4, 9} → False := by
  classical
  intro n10 a234 n154 a15 a309 n166 n168 a230
  have u0_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u1_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u2_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c150 h hv n10
  have u3_61 : T {1, 6, 9} := by
    by_contra hv
    exact c28130 h a309 n10 hv
  have u4_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c28213 h a309 hv u0_54 u3_61
  have u5_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c633 h hv u4_43
  have u6_163 : Q {0, 2, 5, 9} := by
    by_contra hv
    exact c31451 h hv u5_127 u2_159 n154 a15 n166 n168
  have u7_117 : T {6, 7, 8} := by
    by_contra hv
    exact c17622 h a234 n10 hv
  exact c7683 h u6_163 u1_44 u7_117

theorem c31453 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 9} → ¬ Q {0, 2, 3, 9} → Q {1, 3, 4, 9} → T {0, 2, 9} → Q {3, 5, 7, 8} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  classical
  intro a234 n154 a230 a15 a309 n166 n168
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_10 : T {0, 2, 4} := by
    by_contra hv
    exact c31452 h hv a234 n154 a15 a309 n166 n168 a230
  exact c28153 h a309 u0_1 u1_10 a15

theorem c31454 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → T {1, 6, 7} → ¬ T {1, 4, 6} → ¬ Q {0, 2, 7, 9} → ¬ T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a114 a59 n51 n168 n103 n237 n198 n289 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u3_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u0_121 hv a114
  have u6_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv a114
  have u7_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8103 h hv u4_44 a114
  have u8_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18326 h hv u6_12 n103
  have u9_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv a114 n198 n289
  have u10_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c1705 h u9_309 n198 hv n289 u3_319 u2_326 u1_329
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c28134 h u9_309 hv n51
  have u12_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28244 h u9_309 n51 hv u5_107
  have u13_56 : T {1, 5, 7} := by
    by_contra hv
    exact c838 h u10_254 hv
  have u14_62 : T {1, 7, 8} := by
    by_contra hv
    exact c926 h u10_254 hv
  have u15_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3485 h hv u12_72 a114
  have u16_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6473 h hv u13_56 a59 u14_62
  have u17_234 : Q {1, 3, 5, 9} := by
    by_contra hv
    exact c728 h a230 u15_133 n210 hv n237 u8_239 n240
  exact c31453 h h0 u17_234 u16_154 a230 u11_15 u9_309 u7_166 n168

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases093
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

private theorem c31455 (h : TenSystem T Q) :
    T {1, 5, 7} → T {1, 7, 8} → ¬ T {0, 2, 7} → ¬ Q {3, 4, 7, 9} → T {0, 2, 6} → T {1, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro a56 a62 n13 n304 a12 a59 a230
  have u0_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26731 h hv a12 a62
  have u1_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv a12 a56
  have u2_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9273 h hv a56 a59 a62
  have u3_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22045 h hv a56 a59 a62
  have u4_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1341 h a230 u2_174 u3_265 u0_299 hv n304 u1_305
  have u5_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c27155 h u4_302 hv a56
  have u6_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c27151 h u4_302 hv a62
  exact c27176 h u4_302 u6_11 n13 u5_14

private theorem c31457 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 7} → T {0, 2, 9} → ¬ Q {3, 5, 8, 9} → T {4, 5, 7} → ¬ Q {3, 6, 8, 9} → ¬ T {0, 2, 7} → ¬ Q {3, 4, 7, 9} → ¬ T {4, 6, 7} → T {0, 2, 6} → T {1, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → False := by
  classical
  intro a56 a15 n311 a102 n314 n13 n304 n105 a12 a59 n201 n195 n292 n286 a230 n240
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv a12 a56
  have u7_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c31455 h a56 hv n13 n304 a12 a59 a230
  have u8_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c928 h hv u7_62
  have u9_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u8_257 n292 u2_322 u1_326 u0_330
  have u10_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u8_257 n292 u9_312 u2_322 u1_326 u0_330
  have u11_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u10_117
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1894 h u3_121 n105 hv u10_117
  have u13_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28995 h hv u4_1 u11_11 a12
  have u14_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u12_111 hv n195
  have u15_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10751 h hv a56 a102 u12_111
  have u16_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23493 h hv a56 a102 u12_111
  have u17_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c20025 h u14_251 u5_9 hv a15
  have u18_100 : T {3, 8, 9} := by
    by_contra hv
    exact c20004 h u14_251 u17_10 hv
  exact c1487 h u18_100 u15_184 n240 u16_275 u6_305 n311 n314 u13_315

theorem c31459 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → T {4, 6, 9} → False := by
  classical
  intro n282 n191 n247 a107
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1592 h a107 n191 n247 n282 hv u0_318 u1_323 u2_324
  exact c1600 h u3_302 n191 n247 n282 u0_318 u1_323 u2_324

theorem c31460 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 5, 7} → ¬ T {5, 7, 8} → ¬ Q {1, 4, 6, 9} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro n56 n114 n247 n195 n286 a230
  have u0_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv n114
  have u6_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u3_121 hv n114
  have u7_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u8_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u9_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c832 h hv n56
  have u10_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c836 h hv n56
  have u11_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1660 h hv n195 u10_251 n286 u2_316 u1_326 u0_327
  have u12_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 n286 hv u10_251 n195
  have u13_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1820 h u3_121 hv u12_111
  have u14_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17068 h a230 hv u12_111
  have u15_267 : ¬ Q {2, 3, 5, 7} := by
    intro hv
    exact c22357 h hv u8_54 u6_107 u13_110
  have u16_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9615 h hv u8_54 u6_107 u13_110
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28295 h hv u4_1 u5_12 u14_14
  have u18_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26471 h hv u4_1 u5_12 u14_14
  have u19_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c1367 h hv u16_176 u9_232 u15_267 u18_297 u11_306 u7_309 u17_310
  have u20_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24464 h hv n56 u19_92 n114
  have u21_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11722 h hv n56 u19_92 n114
  exact c31459 h h0 u20_282 u21_191 n247 u6_107

theorem c31461 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 6} → ¬ T {1, 3, 6} → ¬ T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n51 n46 n103 n237 n198 n201 n195 n292 n289 n286 a230 n240 n210
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8386 h hv n46 n103
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u3_121 n103 hv
  have u7_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u8_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c765 h hv n51
  have u9_59 : T {1, 6, 7} := by
    by_contra hv
    exact c31449 h h0 hv n51 n46 n103 n198 n201 n195 n292 n289 n286 a230
  have u10_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31454 h h0 hv u9_59 n51 u5_168 n103 n237 n198 n289 a230 n240 n210
  have u11_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u3_121 hv u10_114
  have u12_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1882 h u3_121 n103 u10_114 hv
  have u13_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1878 h u3_121 n103 hv u10_114
  have u14_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv u10_114
  have u15_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1911 h u3_121 u11_107 hv u6_118
  have u16_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1915 h u3_121 u11_107 u6_118 hv
  have u17_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u3_121 hv u12_116
  have u18_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c27423 h hv u4_1 u13_112
  have u19_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h a230 hv u13_112
  have u20_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv u19_13 u15_113
  have u21_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv u16_119
  have u22_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u3_121 hv u16_119
  have u23_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28414 h hv u19_13 n51
  have u24_56 : T {1, 5, 7} := by
    by_contra hv
    exact c31460 h h0 hv u10_114 u8_247 n195 n286 a230
  have u25_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv u14_12 u24_56
  have u26_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c31455 h u24_56 hv u19_13 u18_304 u14_12 u9_59 a230
  have u27_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c31457 h h0 u24_56 hv u23_311 u22_102 u21_314 u19_13 u18_304 u17_105 u14_12 u9_59 n201 n195 n292 n286 a230 n240
  have u28_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c928 h hv u26_62
  have u29_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u28_257 n292 u2_322 u1_326 u0_330
  have u30_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u28_257 n292 u29_312 u2_322 u1_326 u0_330
  have u31_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u30_117
  have u32_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1894 h u3_121 u17_105 hv u30_117
  have u33_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27311 h hv u4_1 u31_11 u14_12
  have u34_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u32_111 hv n195
  have u35_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21945 h hv u9_59 u32_111 u6_118
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9203 h hv u9_59 u32_111 u6_118
  have u37_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1332 h hv u36_173 u20_229 u35_264 u7_298 u33_303 u25_305
  have u38_89 : T {3, 4, 8} := by
    by_contra hv
    exact c20008 h u34_251 u27_15 hv
  exact c1322 h u38_89 u36_173 u20_229 u35_264 u7_298 u37_301 u33_303 u25_305

theorem c31462 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 6, 7} → T {1, 5, 7} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 5, 6} → ¬ T {0, 2, 7} → ¬ Q {3, 4, 7, 9} → T {5, 8, 9} → ¬ T {5, 7, 8} → T {1, 4, 6} → T {6, 7, 9} → ¬ Q {3, 4, 5, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {2, 6, 7, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → False := by
  classical
  intro a59 a56 n165 n160 n13 n304 a116 n114 a51 a118 n298 n201 n292 a230 n240
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u4_121 hv n114
  have u6_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6293 h hv a56 u5_107
  have u7_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17064 h a230 hv n114
  have u8_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27573 h hv u7_12 a56
  have u9_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1915 h u4_121 u5_107 a118 hv
  have u10_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u4_121 hv u9_119
  have u11_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv u9_119
  have u12_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1911 h u4_121 u5_107 hv a118
  have u13_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv n13 u12_113
  have u14_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6145 h hv a51 a116
  have u15_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u16_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7823 h hv u15_44 a116
  have u17_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u4_121 hv a116
  have u18_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u19_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u20_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5731 h hv a59 a116
  have u21_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c31455 h a56 hv n13 n304 u7_12 a59 a230
  have u22_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c922 h hv u21_62
  have u23_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c928 h hv u21_62
  have u24_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u23_257 n292 u2_322 u1_326 u0_330
  have u25_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u23_257 n292 u24_312 u2_322 u1_326 u0_330
  have u26_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1808 h u4_121 hv u25_117
  have u27_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u25_117
  have u28_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1924 h u4_121 n114 u25_117 hv
  have u29_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1894 h u4_121 u17_105 hv u25_117
  have u30_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6558 h hv u21_62 n114 u25_117
  have u31_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10455 h hv u19_54 u26_104 u5_107
  have u32_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23197 h hv u19_54 u26_104 u5_107
  have u33_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28995 h hv u3_1 u27_11 u7_12
  have u34_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27311 h hv u3_1 u27_11 u7_12
  have u35_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5863 h hv a51 u28_120
  have u36_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21945 h hv a59 u29_111 a118
  have u37_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9203 h hv a59 u29_111 a118
  have u38_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10751 h hv a56 u10_102 u29_111
  have u39_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23493 h hv a56 u10_102 u29_111
  have u40_98 : ¬ T {3, 7, 8} := by
    intro hv
    exact c1457 h hv u31_182 u22_238 u32_273 u34_303 u18_309 u24_312 u33_315
  have u41_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1497 h hv u38_184 n240 u39_275 u8_305 u11_314 u33_315
  have u42_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1332 h hv u37_173 u13_229 u36_264 n298 u34_303 u8_305
  have u43_151 : Q {0, 2, 3, 6} := by
    by_contra hv
    exact c124 h u4_121 u20_149 u35_150 hv u14_152 u6_153 u30_154
  have u44_89 : ¬ T {3, 4, 8} := by
    intro hv
    exact c1322 h hv u37_173 u13_229 u36_264 n298 u42_301 u34_303 u8_305
  have u45_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u38_184 n240 u39_275 u8_305 u41_311 u11_314 u33_315
  have u46_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2270 h hv u44_89 u40_98 u45_100
  have u47_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6818 h hv u21_62 u40_98 n114
  have u48_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8236 h hv u21_62 u40_98 n114
  exact c171 h u43_151 u46_124 u47_156 n160 u16_164 n165 u48_166

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases094
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

private theorem c31463 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 6, 7} → ¬ T {4, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 6, 7} → False := by
  classical
  intro n59 n105 n201 n195 n292 n286
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c881 h hv n59
  have u5_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c883 h hv n59
  have u6_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 n286 hv u4_251 n195
  have u7_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u5_257 n292 u3_322 u2_326 u1_330
  have u8_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1894 h u0_121 n105 u6_111 hv
  exact c1742 h u8_117 n201 u5_257 n292 u7_312 u3_322 u2_326 u1_330

theorem c31464 (h : TenSystem T Q) :
    ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 8, 9} → T {0, 2, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 5, 8} → False := by
  classical
  intro n158 n169 a14 n167 n153 n165 n162
  have u0_126 : Q {0, 1, 2, 8} := by
    by_contra hv
    exact c197 h a14 hv n153 n158 n162 n165 n167 n169
  exact c199 h u0_126 n153 n158 n162 n165 n167 n169

private theorem c31465 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 8} → T {1, 4, 6} → ¬ T {4, 5, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro n114 a51 n103 a230 n240 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u5_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u6_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8275 h hv u5_44 a51 u4_54
  have u7_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u3_121 n103 hv
  have u8_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c31448 h hv a230 a49
  have u10_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13033 h hv u1_37 u5_44 a49
  have u11_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12193 h hv u1_37 u5_44 a49
  have u12_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25805 h hv u0_2 u5_44 a49
  have u13_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24965 h hv u0_2 u5_44 a49
  have u14_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u3_121 hv n114
  have u15_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1882 h u3_121 n103 n114 hv
  have u16_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1878 h u3_121 n103 hv n114
  have u17_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1911 h u3_121 u14_107 hv u7_118
  have u18_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1915 h u3_121 u14_107 u7_118 hv
  have u19_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u3_121 hv u15_116
  have u20_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c27423 h hv u2_1 u16_112
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h a230 hv u16_112
  have u22_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1816 h u3_121 hv u17_113
  have u23_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u3_121 hv u18_119
  have u24_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7269 h hv a49 u22_108
  have u25_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7969 h hv a49 u23_102
  have u26_59 : T {1, 6, 7} := by
    by_contra hv
    exact c31463 h h0 hv u19_105 u10_201 u11_195 u12_292 u13_286
  have u27_56 : ¬ T {1, 5, 7} := by
    intro hv
    exact c31462 h h0 u26_59 hv u25_165 u24_160 u21_13 u20_304 u15_116 n114 a51 u7_118 u8_298 u10_201 u12_292 a230 n240
  have u28_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c836 h hv u27_56
  have u29_247 : Q {1, 4, 6, 9} := by
    by_contra hv
    exact c31460 h h0 u27_56 n114 hv u11_195 u13_286 a230
  have u30_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 u13_286 hv u28_251 u11_195
  have u31_61 : T {1, 6, 9} := by
    by_contra hv
    exact c909 h u29_247 hv
  have u32_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17068 h a230 hv u30_111
  have u33_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6409 h hv u31_61 u14_107 u7_118
  have u34_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c19449 h u29_247 u32_14 hv
  have u35_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8648 h hv u27_56 u34_92 u30_111
  have u36_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7082 h hv u27_56 u34_92 u30_111
  exact c31464 h u36_158 u35_169 u32_14 u6_167 u33_153 u25_165 u9_162

theorem c31466 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 6} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n46 n240 a49 n210
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_230 : Q {1, 3, 4, 9} := by
    by_contra hv
    exact c31437 h h0 hv n240 n210 a49
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h u3_230 hv
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12333 h hv u1_37 u4_44 a49
  have u6_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24965 h hv u0_2 u4_44 a49
  have u7_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12193 h hv u1_37 u4_44 a49
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12613 h hv u1_37 u4_44 a49
  have u9_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c31440 h h0 hv u3_230 a49
  have u10_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c31448 h hv u3_230 a49
  have u11_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31447 h h0 u10_162 hv u9_237 u8_198 u7_195 u6_286 u5_196 u3_230 n240 n210
  have u12_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u2_121 u11_103 hv
  have u13_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13033 h hv u1_37 u4_44 a49
  have u14_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25805 h hv u0_2 u4_44 a49
  have u15_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25385 h hv u0_2 u4_44 a49
  have u16_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h u3_230 hv
  have u17_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c682 h hv n46
  have u18_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31461 h h0 hv n46 u11_103 u9_237 u8_198 u13_201 u7_195 u14_292 u15_289 u6_286 u3_230 n240 n210
  have u19_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31465 h h0 hv u18_51 u11_103 u3_230 n240 a49
  have u20_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h u3_230 hv u19_114
  have u21_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv u19_114 u8_198 u15_289
  have u22_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c28135 h u21_309 hv u18_51
  have u23_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28195 h u21_309 hv u18_51 u16_54
  have u24_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28197 h u21_309 hv u18_51 u16_54
  have u25_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv u23_3
  have u26_82 : T {2, 6, 9} := by
    by_contra hv
    exact c28124 h u21_309 u23_3 hv
  have u27_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u24_38
  have u28_33 : T {0, 6, 9} := by
    by_contra hv
    exact c28140 h u21_309 hv u24_38
  have u29_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16611 h hv u28_33 u26_82 u12_118
  have u30_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c17049 h hv u28_33 u26_82 u12_118
  have u31_228 : Q {1, 3, 4, 7} := by
    by_contra hv
    exact c661 h u3_230 u25_128 u27_205 u29_226 u17_227 hv u30_229
  have u32_116 : T {5, 8, 9} := by
    by_contra hv
    exact c16784 h u31_228 u20_12 hv
  have u33_112 : T {5, 6, 8} := by
    by_contra hv
    exact c16788 h u31_228 u22_15 hv
  exact c1885 h u2_121 u33_112 u19_114 u32_116

theorem c31467 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 4, 6} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {2, 4, 7, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ T {4, 5, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro a51 n167 n161 n192 n283 n186 n277 n103 a230 n240 a49
  have u0_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u4_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12613 h hv u4_37 u7_44 a49
  have u9_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25385 h hv u3_2 u7_44 a49
  have u10_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u11_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31465 h h0 hv a51 n103 a230 n240 a49
  have u12_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv u11_114
  have u13_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv u11_114 u8_198 u9_289
  have u14_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c176 h hv u12_12
  have u15_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1393 h u13_309 hv
  have u16_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c1705 h u13_309 u8_198 hv u9_289 u2_319 u1_326 u0_329
  have u17_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c28135 h u13_309 hv a51
  have u18_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28195 h u13_309 hv a51 u10_54
  have u19_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28197 h u13_309 hv a51 u10_54
  have u20_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8393 h hv a51 u15_93
  have u21_57 : T {1, 5, 8} := by
    by_contra hv
    exact c853 h u16_254 hv
  have u22_10 : T {0, 2, 4} := by
    by_contra hv
    exact c20448 h u16_254 hv u12_12 u17_15
  have u23_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c41 h hv u18_3
  have u24_82 : T {2, 6, 9} := by
    by_contra hv
    exact c28124 h u13_309 u18_3 hv
  have u25_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c566 h hv u19_38
  have u26_33 : T {0, 6, 9} := by
    by_contra hv
    exact c28140 h u13_309 hv u19_38
  have u27_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c28131 h u13_309 u22_10 hv
  have u28_97 : ¬ T {3, 6, 9} := by
    intro hv
    exact c20425 h u16_254 u22_10 hv
  have u29_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8953 h hv u21_57 u24_82
  have u30_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21699 h hv u26_33 u21_57
  have u31_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6158 h hv u27_61 n103
  have u32_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2378 h hv u28_97 n103
  have u33_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c188 h hv u32_125 u31_152 n161 u14_164 n167 u20_168
  have u34_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c182 h hv u32_125 u31_152 u33_157 n161 u14_164 n167 u20_168
  have u35_112 : T {5, 6, 8} := by
    by_contra hv
    exact c17066 h a230 u34_13 hv
  have u36_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17082 h a230 hv u12_12 u34_13
  have u37_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17088 h a230 u12_12 u34_13 hv
  have u38_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24623 h hv u3_2 u35_112
  have u39_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11883 h hv u4_37 u35_112
  have u40_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1885 h u6_121 u35_112 u11_114 hv
  have u41_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19183 h hv u5_9 u36_11 u37_14
  have u42_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1092 h hv u33_157 u25_213 u30_263 n277 n283 u38_284
  have u43_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c357 h hv u23_136 u33_157 u29_172 n186 n192 u39_193
  have u44_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u6_121 hv u40_116
  exact c31281 h h0 u42_280 u41_245 u44_105 u43_189

theorem c31468 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → ¬ T {1, 4, 6} → T {1, 3, 6} → ¬ T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a114 n51 a46 n103 n237 n198 n289 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u3_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u0_121 hv a114
  have u6_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv a114
  have u7_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8103 h hv u4_44 a114
  have u8_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv a114 n198 n289
  have u9_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18326 h hv u6_12 n103
  have u10_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c1705 h u8_309 n198 hv n289 u3_319 u2_326 u1_329
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c28134 h u8_309 hv n51
  have u12_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28240 h u8_309 hv n51 u5_107
  have u13_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28244 h u8_309 n51 hv u5_107
  have u14_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c20437 h u10_254 u12_23 hv
  have u15_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3485 h hv u13_72 a114
  have u16_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c1038 h hv u14_70
  have u17_234 : Q {1, 3, 5, 9} := by
    by_contra hv
    exact c728 h a230 u15_133 n210 hv n237 u9_239 n240
  have u18_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h u17_234 hv
  have u19_168 : Q {0, 2, 7, 9} := by
    by_contra hv
    exact c31453 h h0 u17_234 u16_154 a230 u11_15 u8_309 u7_166 hv
  exact c8403 h u19_168 u4_44 u18_45 a46

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases095
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

theorem c31469_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n240 a49 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u3_230 : Q {1, 3, 4, 9} := by
    by_contra hv
    exact c31437 h h0 hv n240 n210 a49
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h u3_230 hv
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12333 h hv u1_37 u4_44 a49
  have u6_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24965 h hv u2_2 u4_44 a49
  have u7_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25385 h hv u2_2 u4_44 a49
  have u8_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12193 h hv u1_37 u4_44 a49
  have u9_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12613 h hv u1_37 u4_44 a49
  have u10_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c31440 h h0 hv u3_230 a49
  have u11_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c31448 h hv u3_230 a49
  have u12_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31447 h h0 u11_162 hv u10_237 u9_198 u8_195 u6_286 u5_196 u3_230 n240 n210
  have u13_46 : T {1, 3, 6} := by
    by_contra hv
    exact c31466 h h0 hv n240 a49 n210
  have u14_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23705 h hv u2_2 u13_46 a49
  have u15_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u1_37 u13_46 a49
  have u16_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24547 h hv u2_2 u13_46 a49
  have u17_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11775 h hv u1_37 u13_46 a49
  have u18_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7425 h hv u4_44 u13_46 a49
  have u19_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25663 h hv u2_2 u4_44 u13_46
  have u20_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12891 h hv u1_37 u4_44 u13_46
  have u21_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8267 h hv u4_44 u13_46 a49
  have u22_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c31467 h h0 hv u21_167 u18_161 u17_192 u16_283 u15_186 u14_277 u12_103 u3_230 n240 a49
  have u23_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31468 h h0 hv u22_51 u13_46 u12_103 u10_237 u9_198 u7_289 u3_230 n240 n210
  have u24_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1882 h u0_121 u12_103 u23_114 hv
  have u25_112 : T {5, 6, 8} := by
    by_contra hv
    exact c1878 h u0_121 u12_103 hv u23_114
  have u26_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u24_116 u20_200 hv u19_291
  have u27_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17067 h u3_230 hv u25_112
  exact c28414 h u26_311 u27_13 u22_51

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31469_oai := @OAI.BorsukNine.FiniteObstruction.c31469_oai
