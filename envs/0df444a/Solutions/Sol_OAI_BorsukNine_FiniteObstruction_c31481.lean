-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31481
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:12:26.853813+00:00
-- url     : https://prove2.me/submissions/0cd5bcd9-c160-4116-8f0e-230f9e221edb

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31264
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31469
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31476

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

theorem c184 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a125 n152 n157 n161 n164 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 7} {0, 2, 7} a125 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
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

theorem c193 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {0, 2, 7} → False := by
  intro a167 n13
  exact n13 (h.down {0, 2, 7, 8} {0, 2, 7} a167 (by decide) (by decide))

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

theorem c207 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a165 n126 n153 n158 n162 n167 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 6, 8} {0, 2, 8} a165 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c209 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a167 n126 n153 n158 n162 n165 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 7, 8} {0, 2, 8} a167 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact hne (by decide)
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

theorem c347 (h : TenSystem T Q) :
    T {0, 4, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 7, 9} → False := by
  intro a24 n136 n157 n172 n186 n189 n192 n193
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 7} a24
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n186 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 7} = {0, 4, 7, 8} by decide)) hS)
  · exact n193 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 7} = {0, 4, 7, 9} by decide)) hS)

theorem c374 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a192 n137 n158 n173 n187 n190 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 8} {0, 4, 8} a192 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

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

theorem c520 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a193 n147 n168 n183 n199 n202 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 9} {0, 7, 9} a193 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n147 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n199 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 7, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c776 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 4, 7} → False := by
  intro a245 n52
  exact n52 (h.down {1, 4, 6, 7} {1, 4, 7} a245 (by decide) (by decide))

theorem c819 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 5, 6} → False := by
  intro a241 n55
  exact n55 (h.down {1, 4, 5, 6} {1, 5, 6} a241 (by decide) (by decide))

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

theorem c854 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a254 n141 n218 n233 n243 n252 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 8} {1, 5, 8} a254 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c879 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 6, 7} → False := by
  intro a245 n59
  exact n59 (h.down {1, 4, 6, 7} {1, 6, 7} a245 (by decide) (by decide))

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

theorem c1301 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 4, 6} → False := by
  intro a300 n87
  exact n87 (h.down {3, 4, 6, 7} {3, 4, 6} a300 (by decide) (by decide))

theorem c1316 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 4, 7} → False := by
  intro a300 n88
  exact n88 (h.down {3, 4, 6, 7} {3, 4, 7} a300 (by decide) (by decide))

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

theorem c1394 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a309 n177 n233 n268 n298 n307 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 8} {3, 5, 8} a309 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1395 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 8} → False := by
  intro a311 n93
  exact n93 (h.down {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide))

theorem c1410 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 9} → False := by
  intro a311 n94
  exact n94 (h.down {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide))

theorem c1419 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 6, 7} → False := by
  intro a300 n95
  exact n95 (h.down {3, 4, 6, 7} {3, 6, 7} a300 (by decide) (by decide))

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

theorem c1533 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a187 n103
  exact n103 (h.down {0, 4, 5, 8} {4, 5, 8} a187 (by decide) (by decide))

theorem c1535 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a243 n103
  exact n103 (h.down {1, 4, 5, 8} {4, 5, 8} a243 (by decide) (by decide))

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

theorem c1566 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a245 n189 n280 n300 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 7} {4, 6, 7} a245 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

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

theorem c1668 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a196 n112
  exact n112 (h.down {0, 5, 6, 8} {5, 6, 8} a196 (by decide) (by decide))

theorem c1670 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a252 n112
  exact n112 (h.down {1, 5, 6, 8} {5, 6, 8} a252 (by decide) (by decide))

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

theorem c1806 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n103 n118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n103 (hc.mpr n118)

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

theorem c1821 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 6, 7} → False := by
  intro a121 a110 a111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a110 a111

theorem c1828 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a121 n102 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1831 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 6, 7} → T {4, 6, 8} → False := by
  intro a121 a101 a105 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c1832 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a121 n101 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c1834 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 8} → ¬ T {4, 6, 9} → False := by
  intro a121 n101 n106 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c1836 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {4, 6, 8} → ¬ T {4, 6, 9} → False := by
  intro a121 n105 n106 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

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

theorem c1854 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → False := by
  intro a121 n104 n107 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

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

theorem c1860 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n107 n109 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

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

theorem c1883 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a121 a103 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1885 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a121 a112 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c1922 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {6, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n108 n117 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
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

theorem c2372 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {3, 5, 8} → ¬ T {4, 6, 9} → False := by
  intro a125 n93 n107
  have hc := h.complementary {0, 1, 2, 7} {3, 5, 8} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n107)

theorem c2517 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 6, 7} → T {4, 5, 9} → False := by
  intro a126 a95 a104
  have hc := h.complementary {0, 1, 2, 8} {3, 6, 7} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 6, 7} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a95 a104

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

theorem c2583 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a126 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {4, 7} {3, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c3515 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 7} → T {2, 5, 8} → False := by
  intro a133 a71 a77 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 7, 8} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c4041 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {3, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a136 a100 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {8, 9} {3, 5, 6} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c4163 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a137 a80 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {6, 7} {2, 5, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c4709 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a141 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 7} {3, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c4725 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a141 a95 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {6, 7} {3, 4, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

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

theorem c5142 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {2, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a144 n77 n102 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 8} {5, 7} {2, 4, 9} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

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

theorem c5535 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a147 a71 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {4, 5} {2, 3, 6} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

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

theorem c6152 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 5, 8} → ¬ T {4, 6, 9} → False := by
  intro a152 n57 n107
  have hc := h.complementary {0, 2, 3, 7} {1, 5, 8} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n107)

theorem c6297 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 6, 7} → T {4, 5, 9} → False := by
  intro a153 a59 a104
  have hc := h.complementary {0, 2, 3, 8} {1, 6, 7} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 6, 7} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a59 a104

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

theorem c6363 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a153 a52 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {4, 7} {1, 6, 9} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c6847 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 8} → T {5, 6, 9} → False := by
  intro a157 a48 a113
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 8} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a48 a113

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

theorem c6849 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 9} → T {5, 6, 8} → False := by
  intro a157 a49 a112
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 9} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a112

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

theorem c6975 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 8, 9} → T {3, 8, 9} → T {5, 8, 9} → False := by
  intro a157 a64 a100 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {8, 9} {1, 3, 5} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c7075 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 6} → T {3, 5, 6} → T {5, 6, 7} → False := by
  intro a158 a55 a91 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 6} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c7101 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 6, 7} → T {3, 6, 7} → T {6, 7, 9} → False := by
  intro a158 a59 a95 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {6, 7} {1, 3, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

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

theorem c7411 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 4, 6} → T {3, 8, 9} → False := by
  intro a161 a51 a100
  have hc := h.complementary {0, 2, 5, 7} {1, 4, 6} a161 (by decide) (by decide)
  have he : ( {0, 2, 5, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a100

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

theorem c7549 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 9} → T {4, 6, 7} → False := by
  intro a162 a49 a105
  have hc := h.complementary {0, 2, 5, 8} {1, 3, 9} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a49 a105

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

theorem c7829 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 3, 9} → T {4, 5, 8} → False := by
  intro a164 a49 a103
  have hc := h.complementary {0, 2, 6, 7} {1, 3, 9} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a103

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

theorem c7955 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 8, 9} → T {3, 8, 9} → T {4, 8, 9} → False := by
  intro a164 a64 a100 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {8, 9} {1, 3, 4} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)

theorem c7956 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a164 n64 n100 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {8, 9} {1, 3, 5} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c8057 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 9} → False := by
  intro a165 a50 a86 a104
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {4, 5} {1, 3, 9} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) a104)

theorem c8065 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 4, 7} → T {3, 4, 7} → T {4, 7, 9} → False := by
  intro a165 a52 a88 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {4, 7} {1, 3, 9} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c8485 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 8} → False := by
  intro a168 a51 a87 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 6} {1, 3, 8} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c8487 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a168 a51 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 6} {1, 5, 8} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

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

theorem c8625 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a169 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 6} {1, 3, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

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

theorem c9079 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a172 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {8, 9} {1, 5, 6} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c9205 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a173 a80 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {6, 7} {2, 5, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

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

theorem c9763 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a177 a59 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {6, 7} {1, 4, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c10184 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {2, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a180 n77 n102 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 6, 8} {5, 7} {2, 4, 9} a180 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

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

theorem c10587 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a183 a51 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 9} {4, 6} {1, 5, 8} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

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

theorem c10935 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a186 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {1, 3} {2, 8, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
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

theorem c12023 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {5, 6, 7} → False := by
  intro a194 a37 a111
  have hc := h.complementary {0, 4, 8, 9} {1, 2, 3} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a111

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

theorem c12723 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 2, 3} → T {4, 6, 8} → False := by
  intro a199 a37 a106
  have hc := h.complementary {0, 5, 7, 9} {1, 2, 3} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a106

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

theorem c13015 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 3, 9} → T {2, 4, 5} → False := by
  intro a201 a49 a71
  have hc := h.complementary {0, 6, 7, 8} {1, 3, 9} a201 (by decide) (by decide)
  have he : ( {0, 6, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a49 a71

theorem c13155 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → T {1, 3, 8} → T {2, 4, 5} → False := by
  intro a202 a48 a71
  have hc := h.complementary {0, 6, 7, 9} {1, 3, 8} a202 (by decide) (by decide)
  have he : ( {0, 6, 7, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a48 a71

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

theorem c13423 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 2, 3} → T {4, 5, 6} → False := by
  intro a204 a37 a101
  have hc := h.complementary {0, 7, 8, 9} {1, 2, 3} a204 (by decide) (by decide)
  have he : ( {0, 7, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a37 a101

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

theorem c15489 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a218 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {4, 7} {3, 6, 9} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c15505 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a218 a95 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {6, 7} {3, 4, 9} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

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

theorem c17062 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {6, 7, 8} → False := by
  intro a230 n11 n117
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 5} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n117)

theorem c17065 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 6} → T {5, 7, 8} → False := by
  intro a230 a12 a114
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 6} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a114

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

theorem c17483 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 4} → T {6, 7, 9} → False := by
  intro a233 a10 a118
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 4} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a118

theorem c17485 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 6} → T {4, 7, 9} → False := by
  intro a233 a12 a109
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 6} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a12 a109

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

theorem c18043 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 4} → T {5, 7, 8} → False := by
  intro a237 a10 a114
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 4} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a10 a114

theorem c18044 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 5} → ¬ T {4, 7, 8} → False := by
  intro a237 n11 n108
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 5} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n108)

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

theorem c18323 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 4} → T {5, 6, 8} → False := by
  intro a239 a10 a112
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 4} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a10 a112

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

theorem c18462 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 4} → ¬ T {5, 6, 7} → False := by
  intro a240 n10 n111
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 4} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n111)

theorem c18464 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 7} → False := by
  intro a240 n11 n105
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n105)

theorem c18465 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {4, 6, 7} → False := by
  intro a240 a11 a105
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a11 a105

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

theorem c18470 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 6, 7} → False := by
  intro a240 n22 n80
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n80)

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

theorem c18472 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 6} → ¬ T {2, 5, 7} → False := by
  intro a240 n23 n77
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 5, 7} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n77)

theorem c18474 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 5, 6} → False := by
  intro a240 n24 n76
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n76)

theorem c18485 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a240 a10 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {4, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18487 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a240 a10 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {4, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
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

theorem c18531 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a240 a11 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 5} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c18533 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {2, 4, 5} → T {2, 5, 7} → False := by
  intro a240 a11 a71 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 5} {0, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c18548 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 7} → ¬ T {2, 4, 7} → ¬ T {2, 6, 7} → False := by
  intro a240 n13 n73 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 7} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c18555 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a240 a22 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 5} {0, 2, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

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

theorem c18567 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a240 a23 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 6} {0, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c18604 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 2, 7} → ¬ T {3, 8, 9} → False := by
  intro a241 n13 n100
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 7} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n100)

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

theorem c18903 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a243 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 2} {3, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

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

theorem c20163 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a252 a9 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {0, 2} {3, 4, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

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

theorem c20703 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {4, 6, 7} → False := by
  intro a256 a9 a105
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 3} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a9 a105

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

theorem c22505 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a268 a59 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {6, 7} {1, 4, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

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

theorem c26875 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 2, 9} → T {1, 5, 8} → False := by
  intro a300 a15 a57
  have hc := h.complementary {3, 4, 6, 7} {0, 2, 9} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a15 a57

theorem c26896 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 2, 5} → ¬ T {0, 2, 8} → ¬ T {0, 2, 9} → False := by
  intro a300 n11 n14 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {0, 2} {5, 8, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c26984 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {1, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a300 n57 n78 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {5, 8} {1, 2, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c27871 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a307 a1 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 2} {1, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

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

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases096
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31477 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 7} → ¬ Q {1, 3, 5, 8} → T {0, 2, 4} → ¬ Q {0, 2, 4, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 6, 7} → ¬ Q {3, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 8, 9} → T {3, 4, 6} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ T {4, 6, 9} → T {1, 4, 6} → Q {1, 3, 8, 9} → False := by
  classical
  intro a13 n233 a10 n158 n218 n177 n268 n141 n126 n153 n164 n298 n243 n157 n169 a87 n162 n256 n311 n107 a51 a240
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u4_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7411 h hv a51 u3_100
  have u5_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c18469 h a240 a13 hv
  have u6_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27871 h hv u0_1 a10 a13
  have u7_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20163 h hv u1_9 a10 a13
  have u8_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18487 h a240 a10 hv a13
  have u9_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1834 h u2_121 u5_101 hv n107
  have u10_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1394 h hv n177 n233 n268 n298 u6_307 n311
  have u11_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv n177 n233 n268 n298 u6_307 u10_309 n311
  have u12_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c854 h hv n141 n218 n233 n243 u7_252 n256
  have u13_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c842 h hv n141 n218 n233 n243 u7_252 u12_254 n256
  have u14_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c178 h hv u8_12
  have u15_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8485 h hv a51 a87 u9_106
  have u16_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2372 h hv u11_93 n107
  have u17_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6152 h hv u13_57 n107
  have u18_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c209 h hv n126 n153 n158 n162 u14_165 n169
  exact c182 h a13 u16_125 u17_152 n157 u4_161 n164 u18_167 u15_168

theorem c31478 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 6, 7} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a112 a105 a49 n210
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u5_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u6_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u7_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u8_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u9_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u8_240 hv
  have u10_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u6_2 u9_48 a49
  have u11_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u5_37 u9_48 a49
  have u12_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u6_2 u9_48 a49
  have u13_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u5_37 u9_48 a49
  have u14_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u6_2 u9_48 a49
  have u15_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u5_37 u9_48 a49
  have u16_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u15_185 u14_276 u13_189 u12_280 u11_195 u10_286 u8_240
  have u17_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u12_280 hv a105 u13_189
  have u18_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1566 h u17_245 u13_189 u12_280 hv u2_316 u3_322 u4_323
  have u19_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u18_300 hv
  have u20_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8625 h hv u16_51 u19_87 a105
  have u21_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h u18_300 hv
  have u22_59 : T {1, 6, 7} := by
    by_contra hv
    exact c879 h u17_245 hv
  have u23_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u8_240 hv a105
  have u24_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7549 h hv a49 a105
  have u25_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20703 h hv u1_9 a105
  have u26_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28403 h hv u0_1 a105
  have u27_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u7_121 a105 hv
  have u28_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u29_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u7_121 hv u28_114
  have u30_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h u8_240 hv
  have u31_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h u8_240 hv
  have u32_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u7_121 hv a112
  have u33_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6849 h hv a49 a112
  have u34_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1879 h u7_121 hv a112 u28_114
  have u35_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1860 h u7_121 u29_107 u32_109 hv
  have u36_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1854 h u7_121 hv u29_107 u32_109
  have u37_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c1535 h hv u34_103
  have u38_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u34_103
  have u39_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u7_121 u34_103 hv
  have u40_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u7_121 u35_110 hv
  have u41_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7955 h hv u31_64 u30_100 u35_110
  have u42_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1809 h u7_121 u36_104 hv
  have u43_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6297 h hv u22_59 u36_104
  have u44_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2517 h hv u21_95 u36_104
  have u45_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4725 h hv u21_95 a105 u39_118
  have u46_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22505 h hv u22_59 a105 u39_118
  have u47_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9763 h hv u22_59 a105 u39_118
  have u48_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15505 h hv u21_95 a105 u39_118
  have u49_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7101 h hv u22_59 u21_95 u39_118
  have u50_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18462 h u8_240 hv u40_111
  have u51_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c17062 h hv u23_11 u42_117
  have u52_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18323 h hv u50_10 a112
  have u53_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17483 h hv u50_10 u39_118
  have u54_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c18043 h hv u50_10 u28_114
  have u55_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c31477 h h0 hv u53_233 u50_10 u49_158 u48_218 u47_177 u46_268 u45_141 u44_126 u43_153 u41_164 u38_298 u37_243 u33_157 u20_169 u19_87 u24_162 u25_256 u26_311 u29_107 u16_51 u8_240
  have u56_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c193 h hv u55_13
  have u57_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18468 h u8_240 u55_13 hv
  have u58_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c207 h hv u44_126 u43_153 u49_158 u24_162 u56_167 u20_169
  have u59_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c31464 h u49_158 u20_169 hv u56_167 u43_153 u58_165 u24_162
  have u60_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u7_121 u57_101 hv
  have u61_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1831 h u7_121 u57_101 a105 hv
  have u62_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c18567 h u8_240 hv u57_101 a105
  have u63_15 : T {0, 2, 9} := by
    by_contra hv
    exact c26896 h u18_300 u23_11 u59_14 hv
  have u64_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u15_185 hv u60_120
  have u65_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u55_13 u61_106
  have u66_77 : T {2, 5, 7} := by
    by_contra hv
    exact c18472 h u8_240 u62_23 hv
  have u67_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c26875 h u18_300 u63_15 hv
  have u68_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c736 h u8_240 hv n210 u51_230 u65_234 u54_237 u52_239
  have u69_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c3515 h u68_133 u64_71 u66_77 hv
  exact c26984 h u18_300 u67_57 u69_78 u27_116

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases097
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31479 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 7} → T {4, 6, 7} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n13 a105 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u3_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31478 h h0 hv a105 a49 n210
  have u5_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u1_121 hv u4_112
  have u6_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1841 h u1_121 hv a105 u5_109
  have u7_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18466 h u3_240 hv u6_102
  have u8_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c17065 h hv u7_12 u2_114
  have u9_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u1_121 a105 hv
  have u10_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1880 h u1_121 hv u4_112 u9_116
  have u11_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18327 h hv u7_12 u10_103
  have u12_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c18465 h u3_240 hv a105
  have u13_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1845 h u1_121 a105 hv u5_109
  have u14_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c18044 h hv u12_11 u13_108
  have u15_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u3_240 hv
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u15_48 a49
  have u17_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18468 h u3_240 n13 hv
  have u18_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u1_121 u17_101 hv
  have u19_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1831 h u1_121 u17_101 a105 hv
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1922 h u1_121 u13_108 hv u18_120
  have u21_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u16_185 hv u18_120
  have u22_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv n13 u19_106
  have u23_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3483 h hv u21_71 u20_117
  exact c736 h u3_240 u23_133 n210 u8_230 u22_234 u14_237 u11_239

private theorem c31480 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a105 a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u8_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u6_121 hv u7_114
  have u9_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u10_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h u9_240 hv
  have u11_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u9_240 hv
  have u12_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u1_2 u11_48 a49
  have u13_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u11_48 a49
  have u14_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u1_2 u11_48 a49
  have u15_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u11_48 a49
  have u16_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u1_2 u11_48 a49
  have u17_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u11_48 a49
  have u18_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u17_185 u16_276 u15_189 u14_280 u13_195 u12_286 u9_240
  have u19_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7411 h hv u18_51 u10_100
  have u20_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1811 h u6_121 a105 hv
  have u21_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20703 h hv u5_9 a105
  have u22_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7549 h hv a49 a105
  have u23_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u14_280 hv a105 u15_189
  have u24_52 : T {1, 4, 7} := by
    by_contra hv
    exact c776 h u23_245 hv
  have u25_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c1566 h u23_245 u15_189 u14_280 hv u4_316 u3_322 u2_323
  have u26_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u25_300 hv
  have u27_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u25_300 hv
  have u28_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8625 h hv u18_51 u26_87 a105
  have u29_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31478 h h0 hv a105 a49 n210
  have u30_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1670 h hv u29_112
  have u31_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u6_121 hv u29_112
  have u32_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1880 h u6_121 hv u29_112 u20_116
  have u33_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1845 h u6_121 a105 hv u31_109
  have u34_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1841 h u6_121 hv a105 u31_109
  have u35_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6363 h hv u24_52 a105 u31_109
  have u36_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15489 h hv u27_88 a105 u31_109
  have u37_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u27_88 a105 u31_109
  have u38_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u27_88 a105 u31_109
  have u39_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8065 h hv u24_52 u27_88 u31_109
  have u40_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7829 h hv a49 u32_103
  have u41_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u6_121 u33_108 hv
  have u42_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18466 h u9_240 hv u34_102
  have u43_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6847 h hv u11_48 u41_113
  have u44_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17485 h hv u42_12 u31_109
  have u45_13 : T {0, 2, 7} := by
    by_contra hv
    exact c31479 h h0 hv a105 a49 n210
  have u46_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c18469 h u9_240 u45_13 hv
  have u47_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c18487 h u9_240 hv u42_12 u45_13
  have u48_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18903 h hv u5_9 u42_12 u45_13
  have u49_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1834 h u6_121 u46_101 hv u8_107
  have u50_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c148 h hv u47_10
  have u51_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c854 h hv u38_141 u36_218 u44_233 u48_243 u30_252 u21_256
  have u52_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c842 h hv u38_141 u36_218 u44_233 u48_243 u30_252 u51_254 u21_256
  have u53_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8485 h hv u18_51 u26_87 u49_106
  have u54_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c209 h hv u37_126 u35_153 u50_158 u22_162 u39_165 u28_169
  have u55_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6152 h hv u52_57 u8_107
  have u56_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c184 h hv u55_152 u43_157 u19_161 u40_164 u54_167 u53_168
  exact c182 h u45_13 u56_125 u55_152 u43_157 u19_161 u40_164 u54_167 u53_168

theorem c31481_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a49 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u5_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u6_240 : Q {1, 3, 8, 9} := by
    by_contra hv
    exact c31469 h h0 hv a49 n210
  have u7_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h u6_240 hv
  have u8_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h u6_240 hv
  have u9_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h u6_240 hv
  have u10_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24967 h hv u5_2 u7_48 a49
  have u11_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12195 h hv u0_37 u7_48 a49
  have u12_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24127 h hv u5_2 u7_48 a49
  have u13_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10935 h hv u0_37 u7_48 a49
  have u14_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11355 h hv u0_37 u7_48 a49
  have u15_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23567 h hv u5_2 u7_48 a49
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10795 h hv u0_37 u7_48 a49
  have u17_51 : T {1, 4, 6} := by
    by_contra hv
    exact c31470 h h0 hv u16_185 u15_276 u14_189 u12_280 u11_195 u10_286 u6_240
  have u18_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31476 h h0 hv a49 n210
  have u19_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u1_121 hv u18_114
  have u20_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31480 h h0 hv a49 n210
  have u21_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1810 h u1_121 u20_105 hv
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1836 h u1_121 u20_105 hv u19_107
  have u23_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18464 h u6_240 hv u20_105
  have u24_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1832 h u1_121 hv u20_105 u19_107
  have u25_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6975 h hv u8_64 u9_100 u21_116
  have u26_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1883 h u1_121 hv u18_114 u21_116
  have u27_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1885 h u1_121 hv u18_114 u21_116
  have u28_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u1_121 u22_106 hv
  have u29_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12723 h hv u0_37 u22_106
  have u30_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10587 h hv u17_51 u24_101 u22_106
  have u31_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8487 h hv u17_51 u24_101 u22_106
  have u32_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u1_121 u24_101 hv
  have u33_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13423 h hv u0_37 u24_101
  have u34_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 u16_185 hv u24_101 u15_276
  have u35_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1533 h hv u26_103
  have u36_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u1_121 u26_103 hv
  have u37_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c1668 h hv u27_112
  have u38_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u16_185 hv u32_120
  have u39_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u34_241 hv
  have u40_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u34_241 hv
  have u41_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u34_241 u16_185 u15_276 hv u2_316 u3_317 u4_318
  have u42_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c18531 h u6_240 u23_11 u38_71 hv
  have u43_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c18555 h u6_240 hv u38_71 u24_101
  have u44_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c18561 h u6_240 u38_71 u24_101 hv
  have u45_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c18533 h u6_240 u23_11 u38_71 hv
  have u46_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13015 h hv a49 u38_71
  have u47_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13155 h hv u7_48 u38_71
  have u48_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u41_296 hv
  have u49_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u41_296 hv
  have u50_24 : T {0, 4, 7} := by
    by_contra hv
    exact c18474 h u6_240 hv u42_76
  have u51_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18470 h u6_240 u43_22 hv
  have u52_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 u44_102 hv
  have u53_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1828 h u1_121 u44_102 u26_103 hv
  have u54_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1872 h u1_121 u44_102 hv u28_115
  have u55_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5142 h hv u45_77 u44_102 u28_115
  have u56_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10184 h hv u45_77 u44_102 u28_115
  have u57_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5535 h hv u38_71 u48_86 u24_101
  have u58_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8057 h hv u39_50 u48_86 u53_104
  have u59_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13399 h hv u39_50 u38_71 u48_86
  have u60_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7075 h hv u40_55 u49_91 u54_111
  have u61_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4163 h hv u51_80 u54_111 u36_118
  have u62_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9205 h hv u51_80 u54_111 u36_118
  have u63_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9079 h hv u8_64 u21_116 u52_119
  have u64_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4041 h hv u9_100 u21_116 u52_119
  have u65_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12023 h hv u0_37 u54_111
  have u66_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c475 h hv u55_144 u58_165 u56_180 u37_196 u46_201 u59_203
  have u67_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c520 h hv u57_147 u31_168 u30_183 u29_199 u47_202 u33_204
  have u68_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c374 h hv u61_137 u60_158 u62_173 u35_187 u66_190 u65_194
  exact c347 h u50_24 u64_136 u25_157 u63_172 u13_186 u14_189 u68_192 u67_193

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31481_oai := @OAI.BorsukNine.FiniteObstruction.c31481_oai
