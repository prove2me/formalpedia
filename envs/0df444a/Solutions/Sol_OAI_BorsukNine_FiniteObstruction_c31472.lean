-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31472
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:10:15.119494+00:00
-- url     : https://prove2.me/submissions/93edda3b-c6ab-485b-9066-8e2ba2756f57

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31264
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31469

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

theorem c33 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {0, 1, 4} → False := by
  intro a122 n3
  exact n3 (h.down {0, 1, 2, 4} {0, 1, 4} a122 (by decide) (by decide))

theorem c48 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {0, 1, 5} → False := by
  intro a123 n4
  exact n4 (h.down {0, 1, 2, 5} {0, 1, 5} a123 (by decide) (by decide))

theorem c123 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 2, 3} → False := by
  intro a121 n9
  exact n9 (h.down {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide))

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

theorem c148 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {0, 2, 4} → False := by
  intro a158 n10
  exact n10 (h.down {0, 2, 4, 8} {0, 2, 4} a158 (by decide) (by decide))

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

theorem c178 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ T {0, 2, 6} → False := by
  intro a165 n12
  exact n12 (h.down {0, 2, 6, 8} {0, 2, 6} a165 (by decide) (by decide))

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

theorem c190 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a161 n125 n152 n157 n164 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 7} {0, 2, 7} a161 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact hne (by decide)
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

theorem c573 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {1, 2, 5} → False := by
  intro a123 n39
  exact n39 (h.down {0, 1, 2, 5} {1, 2, 5} a123 (by decide) (by decide))

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

theorem c720 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 3, 8} → False := by
  intro a240 n48
  exact n48 (h.down {1, 3, 8, 9} {1, 3, 8} a240 (by decide) (by decide))

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

theorem c736 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → False := by
  intro a240 n133 n210 n230 n234 n237 n239
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 8, 9} {1, 3, 9} a240 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c744 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 5} → False := by
  intro a241 n50
  exact n50 (h.down {1, 4, 5, 6} {1, 4, 5} a241 (by decide) (by decide))

theorem c752 (h : TenSystem T Q) :
    T {1, 4, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 4, 6, 9} → False := by
  intro a51 n135 n212 n227 n241 n245 n246 n247
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 4, 6} a51
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n135 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n212 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 4, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n245 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 6} = {1, 4, 6, 7} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 6} = {1, 4, 6, 8} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 6} = {1, 4, 6, 9} by decide)) hS)

theorem c757 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ T {1, 4, 6} → False := by
  intro a227 n51
  exact n51 (h.down {1, 3, 4, 6} {1, 4, 6} a227 (by decide) (by decide))

theorem c759 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 6} → False := by
  intro a241 n51
  exact n51 (h.down {1, 4, 5, 6} {1, 4, 6} a241 (by decide) (by decide))

theorem c761 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  intro a245 n51
  exact n51 (h.down {1, 4, 6, 7} {1, 4, 6} a245 (by decide) (by decide))

theorem c819 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 5, 6} → False := by
  intro a241 n55
  exact n55 (h.down {1, 4, 5, 6} {1, 5, 6} a241 (by decide) (by decide))

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

theorem c917 (h : TenSystem T Q) :
    T {1, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 7, 8, 9} → False := by
  intro a62 n146 n223 n238 n248 n254 n257 n260
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 7, 8} a62
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n146 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 8} = {1, 2, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n248 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 8} = {1, 4, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 7, 8} = {1, 7, 8, 9} by decide)) hS)

theorem c929 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 7, 8, 9} → False := by
  intro a257 n146 n223 n238 n248 n254 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 8} {1, 7, 8} a257 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n146 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 8} = {1, 2, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n248 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 8} = {1, 4, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 7, 8} = {1, 7, 8, 9} by decide)) hS)

theorem c932 (h : TenSystem T Q) :
    T {1, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a63 n147 n224 n239 n249 n255 n258 n260
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 7, 9} a63
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c944 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a258 n147 n224 n239 n249 n255 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 9} {1, 7, 9} a258 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c952 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a240 n64
  exact n64 (h.down {1, 3, 8, 9} {1, 8, 9} a240 (by decide) (by decide))

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

theorem c1050 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {2, 3, 9} → False := by
  intro a275 n70
  exact n70 (h.down {2, 3, 8, 9} {2, 3, 9} a275 (by decide) (by decide))

theorem c1053 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {2, 4, 5} → False := by
  intro a155 n71
  exact n71 (h.down {0, 2, 4, 5} {2, 4, 5} a155 (by decide) (by decide))

theorem c1059 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {2, 4, 5} → False := by
  intro a276 n71
  exact n71 (h.down {2, 4, 5, 6} {2, 4, 5} a276 (by decide) (by decide))

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

theorem c1284 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 4, 5} → False := by
  intro a296 n86
  exact n86 (h.down {3, 4, 5, 6} {3, 4, 5} a296 (by decide) (by decide))

theorem c1292 (h : TenSystem T Q) :
    T {3, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a87 n171 n227 n262 n296 n300 n301 n302
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 6} a87
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1299 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 4, 6} → False := by
  intro a296 n87
  exact n87 (h.down {3, 4, 5, 6} {3, 4, 6} a296 (by decide) (by decide))

theorem c1335 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 4, 8} → False := by
  intro a305 n89
  exact n89 (h.down {3, 4, 8, 9} {3, 4, 8} a305 (by decide) (by decide))

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

theorem c1350 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 4, 9} → False := by
  intro a305 n90
  exact n90 (h.down {3, 4, 8, 9} {3, 4, 9} a305 (by decide) (by decide))

theorem c1359 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 5, 6} → False := by
  intro a296 n91
  exact n91 (h.down {3, 4, 5, 6} {3, 5, 6} a296 (by decide) (by decide))

theorem c1395 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 8} → False := by
  intro a311 n93
  exact n93 (h.down {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide))

theorem c1410 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 9} → False := by
  intro a311 n94
  exact n94 (h.down {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide))

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

theorem c1467 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 7, 8, 9} → False := by
  intro a309 n182 n238 n273 n303 n312 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 8} {3, 7, 8} a309 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n182 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 7, 8} = {3, 7, 8, 9} by decide)) hS)

theorem c1472 (h : TenSystem T Q) :
    T {3, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a99 n183 n239 n274 n304 n310 n313 n315
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 7, 9} a99
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1482 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a310 n183 n239 n274 n304 n313 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 9} {3, 7, 9} a310 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1490 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a240 n100
  exact n100 (h.down {1, 3, 8, 9} {3, 8, 9} a240 (by decide) (by decide))

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

theorem c1491 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a240 n184 n275 n305 n311 n314 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 8, 9} {3, 8, 9} a240 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1494 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a305 n100
  exact n100 (h.down {3, 4, 8, 9} {3, 8, 9} a305 (by decide) (by decide))

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

theorem c1496 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a311 n100
  exact n100 (h.down {3, 5, 8, 9} {3, 8, 9} a311 (by decide) (by decide))

theorem c1499 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a314 n184 n240 n275 n305 n311 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {3, 8, 9} a314 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c1506 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a241 n185 n276 n296 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 6} {4, 5, 6} a241 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
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

theorem c1788 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a204 n120
  exact n120 (h.down {0, 7, 8, 9} {7, 8, 9} a204 (by decide) (by decide))

theorem c1790 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a260 n120
  exact n120 (h.down {1, 7, 8, 9} {7, 8, 9} a260 (by decide) (by decide))

theorem c1794 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a315 n120
  exact n120 (h.down {3, 7, 8, 9} {7, 8, 9} a315 (by decide) (by decide))

theorem c1802 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {7, 8, 9} → False := by
  intro a121 n101 n120
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 6} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n101 (hc.mpr n120)

theorem c1803 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {7, 8, 9} → False := by
  intro a121 a101 a120
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 6} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a101 a120

theorem c1804 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  intro a121 n102 n119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n102 (hc.mpr n119)

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

theorem c1817 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {5, 6, 9} → False := by
  intro a121 a108 a113
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a108 a113

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

theorem c1828 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a121 n102 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1832 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a121 n101 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c1835 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 6, 8} → T {4, 6, 9} → False := by
  intro a121 a101 a106 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c1838 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → False := by
  intro a121 n102 n105 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)

theorem c1840 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a121 n102 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

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

theorem c1870 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → ¬ T {5, 7, 8} → False := by
  intro a121 n102 n111 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 7} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) ht)

theorem c1872 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → ¬ T {5, 7, 9} → False := by
  intro a121 n102 n111 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 7} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

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

theorem c1920 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {5, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n108 n114 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1924 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 7, 8} → ¬ T {6, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n114 n117 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1935 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a121 a110 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c1937 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a110 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c1953 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 8} → T {5, 7, 9} → False := by
  intro a122 a96 a115
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a96 a115

theorem c1955 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 9} → T {5, 7, 8} → False := by
  intro a122 a97 a114
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 9} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a97 a114

theorem c1967 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a122 a91 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 5} {6, 8, 9} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c2085 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 7} → T {6, 8, 9} → False := by
  intro a123 a88 a119
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 7} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a88 a119

theorem c2107 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 6} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a123 a87 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {3, 4} {6, 8, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c2122 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {3, 4, 7} → ¬ T {3, 7, 8} → ¬ T {3, 7, 9} → False := by
  intro a123 n88 n98 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 5} {3, 7} {4, 8, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n88 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 7} = {3, 7, 8} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) ht)

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

theorem c2247 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 4, 5} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a124 a86 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 6} {3, 4} {5, 8, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c2255 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 4, 5} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a124 a86 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 6} {3, 5} {4, 8, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c2363 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 5} → T {6, 8, 9} → False := by
  intro a125 a86 a119
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 5} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a86 a119

theorem c2525 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a126 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 4} {5, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c2533 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 5} → T {3, 5, 6} → T {3, 5, 9} → False := by
  intro a126 a86 a91 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 5} {4, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c2644 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a127 n87 n114
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 6} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n87 (hc.mpr n114)

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

theorem c2665 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a127 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {3, 4} {5, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c2673 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {3, 5, 6} → T {3, 5, 8} → False := by
  intro a127 a86 a91 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {3, 5} {4, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)

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

theorem c3483 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {6, 7, 8} → False := by
  intro a133 a71 a117
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 5} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a71 a117

theorem c3901 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → T {3, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a135 a100 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 6} {8, 9} {3, 5, 7} a135 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c5369 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a146 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 8} {3, 4} {5, 6, 9} a146 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c5509 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a147 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {3, 4} {5, 6, 8} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c5595 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → T {2, 4, 7} → T {3, 5, 6} → False := by
  intro a148 a73 a91
  have hc := h.complementary {0, 1, 8, 9} {2, 4, 7} a148 (by decide) (by decide)
  have he : ( {0, 1, 8, 9} : Finset Labels)ᶜ \ {2, 4, 7} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a73 a91

theorem c5855 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a149 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 4} {8, 9} {1, 5, 6} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c5995 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 8, 9} → T {4, 8, 9} → T {6, 8, 9} → False := by
  intro a150 a64 a110 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {8, 9} {1, 4, 6} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c6143 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 5} → T {6, 8, 9} → False := by
  intro a152 a50 a119
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 5} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a119

theorem c6350 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a153 n51 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 8} {4, 6} {1, 5, 7} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

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

theorem c6490 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a154 n51 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 9} {4, 6} {1, 5, 7} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c6835 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 8, 9} → T {3, 8, 9} → T {5, 8, 9} → False := by
  intro a156 a64 a100 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 6} {8, 9} {1, 3, 5} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

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

theorem c6909 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {3, 5, 6} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a157 a91 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {3, 5} {6, 8, 9} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c6974 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a157 n64 n100 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {8, 9} {1, 3, 5} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c7075 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 6} → T {3, 5, 6} → T {5, 6, 7} → False := by
  intro a158 a55 a91 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 6} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c7215 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 5, 6} → T {3, 5, 6} → T {5, 6, 7} → False := by
  intro a159 a55 a91 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {5, 6} {1, 3, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

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

theorem c7395 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → T {1, 8, 9} → T {3, 8, 9} → T {4, 8, 9} → False := by
  intro a160 a64 a100 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 6} {8, 9} {1, 3, 4} a160 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)

theorem c7469 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {3, 4, 6} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a161 a87 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {3, 4} {6, 8, 9} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c7534 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a161 n64 n100 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 7} {8, 9} {1, 3, 4} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)

theorem c7634 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a162 n51 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 8} {4, 6} {1, 3, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c7635 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a162 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 6} {1, 3, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c7774 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a163 n51 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 9} {4, 6} {1, 3, 7} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c7775 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a163 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 9} {4, 6} {1, 3, 7} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

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

theorem c7954 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a164 n64 n100 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {8, 9} {1, 3, 4} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)

theorem c7956 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a164 n64 n100 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {8, 9} {1, 3, 5} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c8335 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a167 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {4, 5} {1, 3, 6} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8342 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 5, 6} → False := by
  intro a167 n51 n87 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 8} {4, 6} {1, 3, 5} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)

theorem c8475 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a168 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 5} {1, 3, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8482 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 5, 6} → False := by
  intro a168 n51 n87 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 9} {4, 6} {1, 3, 5} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)

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

theorem c8615 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a169 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 5} {1, 3, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8626 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a169 n51 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {4, 6} {1, 5, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c8939 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a171 a64 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {8, 9} {1, 5, 7} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c10379 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a182 a39 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {1, 5} {2, 4, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c10519 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 2, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a183 a39 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 9} {1, 5} {2, 4, 6} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c10637 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 6} → T {2, 4, 7} → False := by
  intro a184 a55 a73
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a55 a73

theorem c10727 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a184 a51 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 6} {1, 5, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c10743 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 6} → T {4, 5, 6} → T {5, 6, 7} → False := by
  intro a184 a55 a101 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {5, 6} {1, 4, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c10795 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a185 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 3} {2, 8, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c11355 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a189 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 3} {2, 8, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
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

theorem c12108 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 6, 7} → False := by
  intro a194 n41 n68 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 8, 9} {2, 7} {1, 3, 6} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c12195 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a195 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 3} {2, 8, 9} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c12948 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 6, 7} → False := by
  intro a200 n41 n68 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {2, 7} {1, 3, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

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

theorem c14681 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {3, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a212 a100 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 6} {8, 9} {3, 5, 7} a212 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c16149 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a223 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 8} {3, 4} {5, 6, 9} a223 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c16289 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a224 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {3, 4} {5, 6, 8} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

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

theorem c16645 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 2, 7} → T {5, 8, 9} → False := by
  intro a227 a13 a116
  have hc := h.complementary {1, 3, 4, 6} {0, 2, 7} a227 (by decide) (by decide)
  have he : ( {1, 3, 4, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a116

theorem c17063 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 5} → T {6, 7, 8} → False := by
  intro a230 a11 a117
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 5} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a117

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

theorem c18045 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 5} → T {4, 7, 8} → False := by
  intro a237 a11 a108
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 5} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a108

theorem c18182 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 4} → ¬ T {5, 6, 9} → False := by
  intro a238 n10 n113
  have hc := h.complementary {1, 3, 7, 8} {0, 2, 4} a238 (by decide) (by decide)
  have he : ( {1, 3, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n113)

theorem c18184 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 5} → ¬ T {4, 6, 9} → False := by
  intro a238 n11 n107
  have hc := h.complementary {1, 3, 7, 8} {0, 2, 5} a238 (by decide) (by decide)
  have he : ( {1, 3, 7, 8} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n107)

theorem c18322 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 4} → ¬ T {5, 6, 8} → False := by
  intro a239 n10 n112
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 4} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n112)

theorem c18324 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 8} → False := by
  intro a239 n11 n106
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 5} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n106)

theorem c18327 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 6} → T {4, 5, 8} → False := by
  intro a239 a12 a103
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a103

theorem c18464 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 7} → False := by
  intro a240 n11 n105
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n105)

theorem c18466 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 6} → ¬ T {4, 5, 7} → False := by
  intro a240 n12 n102
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n102)

theorem c18468 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 7} → ¬ T {4, 5, 6} → False := by
  intro a240 n13 n101
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n101)

theorem c18469 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 7} → T {4, 5, 6} → False := by
  intro a240 a13 a101
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a101

theorem c18471 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 5} → T {2, 6, 7} → False := by
  intro a240 a22 a80
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a22 a80

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

theorem c18485 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a240 a10 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {4, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18488 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a240 n11 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {0, 2} {5, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

theorem c18489 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a240 a11 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {5, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18530 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {2, 4, 5} → ¬ T {2, 5, 6} → False := by
  intro a240 n11 n71 n76
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 5} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) ht)

theorem c18548 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 7} → ¬ T {2, 4, 7} → ¬ T {2, 6, 7} → False := by
  intro a240 n13 n73 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 7} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c18556 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 7} → False := by
  intro a240 n22 n71 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 5} {0, 2, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)

theorem c18561 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {2, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a240 a71 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 5} {2, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c18604 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 2, 7} → ¬ T {3, 8, 9} → False := by
  intro a241 n13 n100
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 7} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n100)

theorem c18605 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 7} → T {3, 8, 9} → False := by
  intro a241 a13 a100
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 7} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a100

theorem c18621 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 8, 9} → T {2, 3, 7} → False := by
  intro a241 a36 a68
  have hc := h.complementary {1, 4, 5, 6} {0, 8, 9} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 8, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a36 a68

theorem c18667 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a241 a9 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {2, 3} {0, 8, 9} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

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

theorem c19323 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a246 a9 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {0, 2} {3, 5, 7} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19463 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a247 a9 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 9} {0, 2} {3, 5, 7} a247 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19584 (h : TenSystem T Q) :
    Q {1, 4, 7, 8} → ¬ T {0, 2, 5} → ¬ T {3, 6, 9} → False := by
  intro a248 n11 n97
  have hc := h.complementary {1, 4, 7, 8} {0, 2, 5} a248 (by decide) (by decide)
  have he : ( {1, 4, 7, 8} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n97)

theorem c19724 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 5} → ¬ T {3, 6, 8} → False := by
  intro a249 n11 n96
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n96)

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

theorem c20028 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 2, 4} → ¬ T {0, 2, 8} → ¬ T {0, 2, 9} → False := by
  intro a251 n10 n14 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 7} {0, 2} {4, 8, 9} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

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

theorem c20427 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 6} → T {3, 4, 9} → False := by
  intro a254 a12 a90
  have hc := h.complementary {1, 5, 7, 8} {0, 2, 6} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a12 a90

theorem c20567 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 2, 6} → T {3, 4, 8} → False := by
  intro a255 a12 a89
  have hc := h.complementary {1, 5, 7, 9} {0, 2, 6} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a89

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

theorem c21681 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {1, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a262 a64 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {8, 9} {1, 5, 7} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c23151 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a273 a4 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 8} {1, 5} {0, 4, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c23291 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a274 a4 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 9} {1, 5} {0, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

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

theorem c23567 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a276 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {1, 3} {0, 8, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24127 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a280 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 3} {0, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c24967 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a286 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 7} {1, 3} {0, 8, 9} a286 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
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

theorem c26310 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 2, 7} → ¬ T {1, 8, 9} → False := by
  intro a296 n13 n64
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 7} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n64)

theorem c26311 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 2, 7} → T {1, 8, 9} → False := by
  intro a296 a13 a64
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 7} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a64

theorem c26320 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 8, 9} → ¬ T {1, 2, 7} → False := by
  intro a296 n36 n41
  have hc := h.complementary {3, 4, 5, 6} {0, 8, 9} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n36 (hc.mpr n41)

theorem c26374 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 1, 7} → ¬ T {1, 7, 8} → ¬ T {1, 7, 9} → False := by
  intro a296 n6 n62 n63
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 6} {1, 7} {0, 8, 9} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n6 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 7} = {0, 1, 7} by decide)) ht)
  · exact n62 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) ht)
  · exact n63 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) ht)

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

theorem c27031 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a301 a1 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {0, 2} {1, 5, 7} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

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

theorem c27171 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a302 a1 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {0, 2} {1, 5, 7} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c27351 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 5} → T {1, 2, 5} → T {1, 5, 6} → False := by
  intro a303 a4 a39 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {1, 5} {0, 2, 6} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c27491 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 5} → T {1, 2, 5} → T {1, 5, 6} → False := by
  intro a304 a4 a39 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 5} {0, 2, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

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

theorem c27563 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {5, 6, 7} → False := by
  intro a305 a1 a111
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 2} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a111

theorem c27569 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 7} → T {2, 5, 6} → False := by
  intro a305 a6 a76
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a6 a76

theorem c27575 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 7} → T {1, 5, 6} → False := by
  intro a305 a13 a55
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a55

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

theorem c28403 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {4, 6, 7} → False := by
  intro a311 a1 a105
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 2} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a105

theorem c28415 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 7} → T {1, 4, 6} → False := by
  intro a311 a13 a51
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a51

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

theorem c28619 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 5} → T {1, 2, 5} → T {1, 4, 5} → False := by
  intro a312 a4 a39 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 5} {0, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)

theorem c28759 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 5} → T {1, 2, 5} → T {1, 4, 5} → False := by
  intro a313 a4 a39 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 5} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)

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

theorem c28837 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 4, 5} → T {1, 2, 7} → False := by
  intro a314 a22 a41
  have hc := h.complementary {3, 6, 8, 9} {0, 4, 5} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a22 a41

theorem c28891 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 4} → T {1, 2, 4} → T {1, 4, 5} → False := by
  intro a314 a3 a38 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {1, 4} {0, 2, 5} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)

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
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases083
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

private theorem c31265 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → Q {3, 4, 5, 6} → Q {1, 4, 5, 6} → ¬ Q {2, 3, 8, 9} → ¬ T {7, 8, 9} → False := by
  classical
  intro n116 n240 n305 n311 n125 n152 a296 a241 n275 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv n120
  have u2_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h a241 hv
  have u3_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h a296 hv
  have u4_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8475 h hv u2_50 u3_86 u1_101
  have u5_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8335 h hv u2_50 u3_86 u1_101
  have u6_51 : T {1, 4, 6} := by
    by_contra hv
    exact c759 h a241 hv
  have u7_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u0_121 hv n116
  have u9_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10727 h hv u6_51 u1_101 u8_105
  have u10_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1499 h hv u9_184 n240 n275 n305 n311 u7_315
  have u11_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u9_184 n240 n275 n305 n311 u10_314 u7_315
  have u12_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18604 h a241 hv u11_100
  have u13_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c26311 h a296 u12_13 hv
  have u14_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6974 h hv u13_64 u11_100 n116
  have u15_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7956 h hv u13_64 u11_100 n116
  have u16_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c190 h hv n125 n152 u14_157 u15_164 u5_167 u4_168
  exact c182 h u12_13 n125 n152 u14_157 u16_161 u15_164 u5_167 u4_168

private theorem c31266 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → T {6, 8, 9} → Q {3, 4, 5, 6} → Q {1, 4, 5, 6} → ¬ Q {2, 3, 8, 9} → ¬ T {7, 8, 9} → False := by
  classical
  intro n240 n305 n311 a119 a296 a241 n275 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h a296 hv
  have u2_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2363 h hv u1_86 a119
  have u3_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h a241 hv
  have u4_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6143 h hv u3_50 a119
  have u5_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv n120
  have u6_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8475 h hv u3_50 u1_86 u5_101
  have u7_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8335 h hv u3_50 u1_86 u5_101
  have u8_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h a241 hv
  have u9_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31265 h h0 hv n240 n305 n311 u2_125 u4_152 a296 a241 n275 n120
  have u11_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1935 h u0_121 hv u10_116 a119
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u0_121 u11_110 hv
  have u13_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10743 h hv u8_55 u5_101 u12_111
  have u14_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1499 h hv u13_184 n240 n275 n305 n311 u9_315
  have u15_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u13_184 n240 n275 n305 n311 u14_314 u9_315
  have u16_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18604 h a241 hv u15_100
  have u17_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c26311 h a296 u16_13 hv
  have u18_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7534 h hv u17_64 u15_100 u11_110
  have u19_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7954 h hv u17_64 u15_100 u11_110
  have u20_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c188 h hv u2_125 u4_152 u18_161 u19_164 u7_167 u6_168
  exact c182 h u16_13 u2_125 u4_152 u20_157 u18_161 u19_164 u7_167 u6_168

private theorem c31267 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro n305 n311 n185 n71 n120
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u4_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31264 h h0 hv n185 n71 n120
  have u5_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u3_121 u4_102 hv
  have u6_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u3_121 hv n120
  have u7_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u8_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u6_101 u7_276
  have u9_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u8_241 hv
  have u10_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u8_241 n185 u7_276 hv u0_316 u1_317 u2_318
  have u11_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u10_296 hv
  have u12_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8615 h hv u9_50 u11_86 u6_101
  have u13_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u10_296 hv
  have u14_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u8_241 hv
  have u15_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u7_276 u6_101
  have u16_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u17_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c1788 h hv n120
  have u18_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31266 h h0 hv n305 n311 u5_119 u10_296 u8_241 u15_275 n120
  have u19_22 : T {0, 4, 5} := by
    by_contra hv
    exact c18556 h u18_240 hv n71 u4_102
  have u20_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c18471 h u18_240 u19_22 hv
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18469 h u18_240 hv u6_101
  have u22_73 : T {2, 4, 7} := by
    by_contra hv
    exact c18548 h u18_240 u21_13 hv u20_80
  have u23_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10637 h hv u14_55 u22_73
  have u24_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5595 h hv u22_73 u13_91
  have u25_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c1491 h u18_240 u23_184 u15_275 n305 n311 hv u16_315
  have u26_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c28837 h u25_314 u19_22 hv
  have u27_36 : T {0, 8, 9} := by
    by_contra hv
    exact c26320 h u10_296 hv u26_41
  have u28_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c18621 h u8_241 u27_36 hv
  have u29_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12948 h hv u26_41 u28_68 u20_80
  have u30_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12108 h hv u26_41 u28_68 u20_80
  have u31_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c539 h hv u24_148 u12_169 u23_184 u30_194 u29_200 u17_204
  exact c527 h u27_36 u24_148 u12_169 u23_184 u30_194 u29_200 u31_203 u17_204

theorem c31268 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro n311 n185 n71 n120
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u6_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u4_121 hv n120
  have u7_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u6_101 u5_276
  have u8_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u7_241 n185 u5_276 hv u0_316 u1_317 u2_318
  have u9_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u8_296 hv
  have u10_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31264 h h0 hv n185 n71 n120
  have u11_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u4_121 u10_102 hv
  have u12_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2363 h hv u9_86 u11_119
  have u13_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1299 h u8_296 hv
  have u14_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u7_241 hv
  have u15_51 : T {1, 4, 6} := by
    by_contra hv
    exact c759 h u7_241 hv
  have u16_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u7_241 hv
  have u17_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u5_276 u6_101
  have u18_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c1053 h hv n71
  have u19_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u20_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv n120
  have u21_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c31267 h h0 hv n311 n185 n71 n120
  have u22_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u21_305 hv
  have u23_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h u21_305 hv
  have u24_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1494 h u21_305 hv
  have u25_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1644 h u21_305 hv
  have u26_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c27563 h u21_305 u3_1 hv
  have u27_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c27575 h u21_305 hv u14_55
  have u28_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7469 h hv u13_87 u22_89 u23_90
  have u29_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5509 h hv u9_86 u13_87 u22_89
  have u30_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2665 h hv u9_86 u13_87 u22_89
  have u31_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16289 h hv u9_86 u13_87 u22_89
  have u32_146 : ¬ Q {0, 1, 7, 8} := by
    intro hv
    exact c5369 h hv u9_86 u13_87 u23_90
  have u33_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2525 h hv u9_86 u13_87 u23_90
  have u34_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16149 h hv u9_86 u13_87 u23_90
  have u35_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2247 h hv u9_86 u22_89 u23_90
  have u36_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2107 h hv u13_87 u22_89 u23_90
  have u37_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1935 h u4_121 u25_110 hv u11_119
  have u38_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1872 h u4_121 u10_102 u26_111 hv
  have u39_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1870 h u4_121 u10_102 u26_111 hv
  have u40_64 : T {1, 8, 9} := by
    by_contra hv
    exact c26310 h u8_296 u27_13 hv
  have u41_122 : Q {0, 1, 2, 4} := by
    by_contra hv
    exact c4 h u4_121 hv u36_123 u35_124 u12_125 u33_126 u30_127
  have u42_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u4_121 hv u37_116
  have u43_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1813 h u4_121 hv u38_115
  have u44_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u4_121 hv u39_114
  have u45_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7395 h hv u40_64 u24_100 u25_110
  have u46_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5995 h hv u40_64 u25_110 u11_119
  have u47_3 : T {0, 1, 4} := by
    by_contra hv
    exact c33 h u41_122 hv
  have u48_38 : T {1, 2, 4} := by
    by_contra hv
    exact c558 h u41_122 hv
  have u49_96 : ¬ T {3, 6, 8} := by
    intro hv
    exact c1953 h u41_122 hv u38_115
  have u50_97 : ¬ T {3, 6, 9} := by
    intro hv
    exact c1955 h u41_122 hv u39_114
  have u51_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10727 h hv u15_51 u6_101 u42_105
  have u52_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7635 h hv u15_51 u13_87 u42_105
  have u53_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7775 h hv u15_51 u13_87 u42_105
  have u54_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28891 h hv u47_3 u48_38 u16_50
  have u55_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c152 h hv u36_123 u46_150 u18_155 u45_160 u28_161 u52_162 u53_163
  have u56_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c1495 h u21_305 u51_184 hv u17_275 n311 u54_314 u19_315
  have u57_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18488 h u56_240 u55_11 hv u27_13
  have u58_76 : T {2, 5, 6} := by
    by_contra hv
    exact c18530 h u56_240 u55_11 n71 hv
  have u59_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18324 h hv u55_11 u43_106
  have u60_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18184 h hv u55_11 u44_107
  have u61_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19724 h hv u55_11 u49_96
  have u62_248 : ¬ Q {1, 4, 7, 8} := by
    intro hv
    exact c19584 h hv u55_11 u50_97
  have u63_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20567 h hv u57_12 u22_89
  have u64_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20427 h hv u57_12 u23_90
  have u65_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c27569 h u21_305 hv u58_76
  have u66_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c944 h hv u29_147 u31_224 u59_239 u61_249 u63_255 u20_260
  have u67_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c929 h hv u32_146 u34_223 u60_238 u62_248 u64_254 u20_260
  have u68_62 : ¬ T {1, 7, 8} := by
    intro hv
    exact c917 h hv u32_146 u34_223 u60_238 u62_248 u64_254 u67_257 u20_260
  have u69_63 : ¬ T {1, 7, 9} := by
    intro hv
    exact c932 h hv u29_147 u31_224 u59_239 u61_249 u63_255 u66_258 u20_260
  exact c26374 h u8_296 u65_6 u68_62 u69_63

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

theorem c31269 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro n185 n71 n120
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u6_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c1053 h hv n71
  have u7_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u4_121 hv n120
  have u8_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u9_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u7_101 u5_276
  have u10_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u9_241 hv
  have u11_51 : T {1, 4, 6} := by
    by_contra hv
    exact c759 h u9_241 hv
  have u12_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u9_241 hv
  have u13_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u9_241 n185 u5_276 hv u2_316 u1_317 u0_318
  have u14_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u13_296 hv
  have u15_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u13_296 hv
  have u16_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31264 h h0 hv n185 n71 n120
  have u17_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u4_121 u16_102 hv
  have u18_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2363 h hv u14_86 u17_119
  have u19_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31268 h h0 hv n185 n71 n120
  have u20_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h u19_311 hv
  have u21_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h u19_311 hv
  have u22_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1496 h u19_311 hv
  have u23_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1734 h u19_311 hv
  have u24_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c28403 h u19_311 u3_1 hv
  have u25_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c28415 h u19_311 hv u11_51
  have u26_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6909 h hv u15_91 u20_93 u21_94
  have u27_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2673 h hv u14_86 u15_91 u20_93
  have u28_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2533 h hv u14_86 u15_91 u21_94
  have u29_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2255 h hv u14_86 u20_93 u21_94
  have u30_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1967 h hv u15_91 u20_93 u21_94
  have u31_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1935 h u4_121 hv u23_116 u17_119
  have u32_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1838 h u4_121 u16_102 u24_105 hv
  have u33_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1840 h u4_121 u16_102 u24_105 hv
  have u34_64 : T {1, 8, 9} := by
    by_contra hv
    exact c26310 h u13_296 u25_13 hv
  have u35_123 : Q {0, 1, 2, 5} := by
    by_contra hv
    exact c4 h u4_121 u30_122 hv u29_124 u18_125 u28_126 u27_127
  have u36_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u4_121 u31_110 hv
  have u37_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1817 h u4_121 u32_108 hv
  have u38_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1819 h u4_121 u33_109 hv
  have u39_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6835 h hv u34_64 u22_100 u23_116
  have u40_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5855 h hv u34_64 u23_116 u17_119
  have u41_4 : T {0, 1, 5} := by
    by_contra hv
    exact c48 h u35_123 hv
  have u42_39 : T {1, 2, 5} := by
    by_contra hv
    exact c573 h u35_123 hv
  have u43_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c2085 h u35_123 hv u17_119
  have u44_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7075 h hv u12_55 u15_91 u36_111
  have u45_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7215 h hv u12_55 u15_91 u36_111
  have u46_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23151 h hv u41_4 u10_50 u12_55
  have u47_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23291 h hv u41_4 u10_50 u12_55
  have u48_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28619 h hv u41_4 u42_39 u10_50
  have u49_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28759 h hv u41_4 u42_39 u10_50
  have u50_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10379 h hv u42_39 u10_50 u12_55
  have u51_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10519 h hv u42_39 u10_50 u12_55
  have u52_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27351 h hv u41_4 u42_39 u12_55
  have u53_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c27491 h hv u41_4 u42_39 u12_55
  have u54_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c137 h hv u30_122 u40_149 u6_155 u39_156 u26_157 u44_158 u45_159
  have u55_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18182 h hv u54_10 u37_113
  have u56_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18322 h hv u54_10 u38_112
  have u57_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1467 h hv u50_182 u55_238 u46_273 u52_303 u48_312 u8_315
  have u58_98 : ¬ T {3, 7, 8} := by
    intro hv
    exact c1457 h hv u50_182 u55_238 u46_273 u52_303 u57_309 u48_312 u8_315
  have u59_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1482 h hv u51_183 u56_239 u47_274 u53_304 u49_313 u8_315
  have u60_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c1472 h hv u51_183 u56_239 u47_274 u53_304 u59_310 u49_313 u8_315
  exact c2122 h u35_123 u43_88 u58_98 u60_99

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

theorem c31451 (h : TenSystem T Q) :
    ¬ Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 3, 9} → T {0, 2, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  classical
  intro n163 n127 n159 n154 a15 n166 n168
  have u0_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c226 h hv n127 n154 n159 n163 n166 n168
  exact c212 h a15 n127 n154 n159 n163 n166 n168 u0_169

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

theorem c31464 (h : TenSystem T Q) :
    ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 8, 9} → T {0, 2, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 5, 8} → False := by
  classical
  intro n158 n169 a14 n167 n153 n165 n162
  have u0_126 : Q {0, 1, 2, 8} := by
    by_contra hv
    exact c197 h a14 hv n153 n158 n162 n165 n167 n169
  exact c199 h u0_126 n153 n158 n162 n165 n167 n169

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

theorem c31470 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 8, 9} → False := by
  classical
  intro n51 n185 n276 n189 n280 n195 n286 a240
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u5_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h a240 hv
  have u8_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c757 h hv n51
  have u9_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c759 h hv n51
  have u10_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u11_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31261 h h0 n185 u9_241 hv n276
  have u12_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c1510 h hv n185 u9_241 n276 u4_316 u1_317 u0_318
  have u13_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31281 h h0 n280 u10_245 hv n189
  have u14_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1570 h hv n189 u10_245 n280 u4_316 u3_322 u2_323
  have u15_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1802 h u6_121 u11_101 hv
  have u16_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8626 h hv n51 u11_101 u13_105
  have u17_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6490 h hv n51 u11_101 u13_105
  have u18_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6350 h hv n51 u11_101 u13_105
  have u19_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18468 h a240 hv u11_101
  have u20_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1810 h u6_121 u13_105 hv
  have u21_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h a240 hv u13_105
  have u22_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1832 h u6_121 u11_101 u13_105 hv
  have u23_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1937 h u6_121 hv u20_116 u15_120
  have u24_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21681 h hv u7_64 u20_116 u15_120
  have u25_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8939 h hv u7_64 u20_116 u15_120
  have u26_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27031 h hv u5_1 u21_11 u19_13
  have u27_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18489 h a240 u21_11 hv u19_13
  have u28_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27171 h hv u5_1 u21_11 u19_13
  have u29_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c18485 h a240 hv u21_11 u19_13
  have u30_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1815 h u6_121 u22_107 hv
  have u31_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u6_121 u23_110 hv
  have u32_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c1292 h hv u25_171 u8_227 u24_262 u12_296 u14_300 u26_301 u28_302
  have u33_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c178 h hv u27_12
  have u34_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c180 h hv u27_12
  have u35_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c148 h hv u29_10
  have u36_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c150 h hv u29_10
  have u37_251 : Q {1, 5, 6, 7} := by
    by_contra hv
    exact c31378 h h0 n286 u31_111 hv n195
  have u38_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2644 h hv u32_87 u30_114
  have u39_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8342 h hv n51 u32_87 u11_101
  have u40_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7774 h hv n51 u32_87 u13_105
  have u41_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8482 h hv n51 u32_87 u11_101
  have u42_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7634 h hv n51 u32_87 u13_105
  have u43_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u35_158 u16_169 hv u39_167 u18_153 u33_165 u42_162
  have u44_15 : T {0, 2, 9} := by
    by_contra hv
    exact c20028 h u37_251 u29_10 u43_14 hv
  exact c31451 h u40_163 u38_127 u36_159 u17_154 u44_15 u34_166 u41_168

private theorem c31471 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 7} → T {5, 8, 9} → T {1, 4, 6} → Q {1, 3, 8, 9} → False := by
  classical
  intro a13 a116 a51 a240
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv a116
  have u3_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h a240 hv u2_105
  have u4_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19163 h hv u0_9 a116
  have u5_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u6_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c18469 h a240 a13 hv
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18605 h hv a13 u5_100
  have u8_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16645 h hv a13 a116
  have u9_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19323 h hv u0_9 u3_11 a13
  have u10_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c19463 h hv u0_9 u3_11 a13
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1802 h u1_121 u6_101 hv
  have u12_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14681 h hv u5_100 a116 u11_120
  have u13_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3901 h hv u5_100 a116 u11_120
  exact c752 h a51 u13_135 u12_212 u8_227 u7_241 u4_245 u9_246 u10_247

theorem c31472_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ T {5, 7, 8} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a116 n114 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u2_121 hv n114
  have u4_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u5_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u4_240 hv
  have u6_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u1_2 u5_48 a49
  have u7_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u5_48 a49
  have u8_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u1_2 u5_48 a49
  have u9_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u5_48 a49
  have u10_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u1_2 u5_48 a49
  have u11_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u5_48 a49
  have u12_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u11_185 u10_276 u9_189 u8_280 u7_195 u6_286 u4_240
  have u13_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv a116
  have u14_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h u4_240 hv u13_105
  have u15_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c31471 h h0 hv a116 u12_51 u4_240
  have u16_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18468 h u4_240 u15_13 hv
  have u17_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u2_121 u16_101 hv
  have u18_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1835 h u2_121 u16_101 hv u3_107
  have u19_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1920 h u2_121 hv n114 u17_120
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1924 h u2_121 n114 hv u17_120
  have u21_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u11_185 hv u17_120
  have u22_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u15_13 u18_106
  have u23_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c18045 h hv u14_11 u19_108
  have u24_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1809 h u2_121 hv u20_117
  have u25_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c17063 h hv u14_11 u20_117
  have u26_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c18561 h u4_240 u21_71 u16_101 hv
  have u27_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3483 h hv u21_71 u20_117
  have u28_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18466 h u4_240 hv u26_102
  have u29_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1828 h u2_121 u26_102 hv u24_104
  have u30_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c736 h u4_240 u27_133 n210 u25_230 u22_234 u23_237 hv
  exact c18327 h u30_239 u28_12 u29_103

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31472_oai := @OAI.BorsukNine.FiniteObstruction.c31472_oai
