-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31520
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:12:53.835803+00:00
-- url     : https://prove2.me/submissions/4f79e58a-ab2d-4d1a-b06e-473e3a95c350

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31264
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31481

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

theorem c33 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {0, 1, 4} → False := by
  intro a122 n3
  exact n3 (h.down {0, 1, 2, 4} {0, 1, 4} a122 (by decide) (by decide))

theorem c35 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {0, 1, 4} → False := by
  intro a128 n3
  exact n3 (h.down {0, 1, 3, 4} {0, 1, 4} a128 (by decide) (by decide))

theorem c48 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {0, 1, 5} → False := by
  intro a123 n4
  exact n4 (h.down {0, 1, 2, 5} {0, 1, 5} a123 (by decide) (by decide))

theorem c97 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → ¬ T {0, 1, 8} → False := by
  intro a137 n7
  exact n7 (h.down {0, 1, 4, 8} {0, 1, 8} a137 (by decide) (by decide))

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

theorem c291 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a153 n132 n173 n177 n180 n182 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 8} {0, 3, 8} a153 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n173 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c292 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {0, 3, 8} → False := by
  intro a173 n20
  exact n20 (h.down {0, 3, 4, 8} {0, 3, 8} a173 (by decide) (by decide))

theorem c295 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a177 n132 n153 n173 n180 n182 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {0, 3, 8} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n173 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

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

theorem c324 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {0, 4, 5} → False := by
  intro a185 n22
  exact n22 (h.down {0, 4, 5, 6} {0, 4, 5} a185 (by decide) (by decide))

theorem c339 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {0, 4, 6} → False := by
  intro a185 n23
  exact n23 (h.down {0, 4, 5, 6} {0, 4, 6} a185 (by decide) (by decide))

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

theorem c517 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 7, 9} → False := by
  intro a183 n35
  exact n35 (h.down {0, 3, 7, 9} {0, 7, 9} a183 (by decide) (by decide))

theorem c523 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {0, 7, 9} → False := by
  intro a202 n35
  exact n35 (h.down {0, 6, 7, 9} {0, 7, 9} a202 (by decide) (by decide))

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

theorem c558 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {1, 2, 4} → False := by
  intro a122 n38
  exact n38 (h.down {0, 1, 2, 4} {1, 2, 4} a122 (by decide) (by decide))

theorem c562 (h : TenSystem T Q) :
    Q {1, 2, 4, 5} → ¬ T {1, 2, 4} → False := by
  intro a211 n38
  exact n38 (h.down {1, 2, 4, 5} {1, 2, 4} a211 (by decide) (by decide))

theorem c572 (h : TenSystem T Q) :
    T {1, 2, 5} → ¬ Q {0, 1, 2, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 2, 5, 9} → False := by
  intro a39 n123 n206 n211 n216 n217 n218 n219
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 5} a39
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n123 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact n211 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 5} = {1, 2, 5, 6} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 5} = {1, 2, 5, 7} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 5} = {1, 2, 5, 8} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 5} = {1, 2, 5, 9} by decide)) hS)

theorem c573 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {1, 2, 5} → False := by
  intro a123 n39
  exact n39 (h.down {0, 1, 2, 5} {1, 2, 5} a123 (by decide) (by decide))

theorem c575 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {1, 2, 5} → False := by
  intro a206 n39
  exact n39 (h.down {1, 2, 3, 5} {1, 2, 5} a206 (by decide) (by decide))

theorem c576 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ Q {0, 1, 2, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 2, 5, 9} → False := by
  intro a206 n123 n211 n216 n217 n218 n219
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 5} {1, 2, 5} a206 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n123 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 5} = {1, 2, 5, 6} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 5} = {1, 2, 5, 7} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 5} = {1, 2, 5, 8} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 5} = {1, 2, 5, 9} by decide)) hS)

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

theorem c594 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 6} → False := by
  intro a216 n40
  exact n40 (h.down {1, 2, 5, 6} {1, 2, 6} a216 (by decide) (by decide))

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

theorem c705 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 7} → False := by
  intro a239 n47
  exact n47 (h.down {1, 3, 7, 9} {1, 3, 7} a239 (by decide) (by decide))

theorem c715 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 3, 4, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 8, 9} → False := by
  intro a233 n132 n209 n229 n236 n238 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 8} {1, 3, 8} a233 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n132 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n209 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n229 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 8} = {1, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n236 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n240 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 8} = {1, 3, 8, 9} by decide)) hS)

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

theorem c733 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 9} → False := by
  intro a239 n49
  exact n49 (h.down {1, 3, 7, 9} {1, 3, 9} a239 (by decide) (by decide))

theorem c742 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ T {1, 4, 5} → False := by
  intro a226 n50
  exact n50 (h.down {1, 3, 4, 5} {1, 4, 5} a226 (by decide) (by decide))

theorem c744 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 5} → False := by
  intro a241 n50
  exact n50 (h.down {1, 4, 5, 6} {1, 4, 5} a241 (by decide) (by decide))

theorem c759 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 6} → False := by
  intro a241 n51
  exact n51 (h.down {1, 4, 5, 6} {1, 4, 6} a241 (by decide) (by decide))

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

theorem c885 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {1, 6, 7} → False := by
  intro a258 n59
  exact n59 (h.down {1, 6, 7, 9} {1, 6, 7} a258 (by decide) (by decide))

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

theorem c937 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a239 n63
  exact n63 (h.down {1, 3, 7, 9} {1, 7, 9} a239 (by decide) (by decide))

theorem c940 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a249 n147 n224 n239 n255 n258 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 7, 9} {1, 7, 9} a249 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c943 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a258 n63
  exact n63 (h.down {1, 6, 7, 9} {1, 7, 9} a258 (by decide) (by decide))

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

theorem c1022 (h : TenSystem T Q) :
    T {2, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {2, 3, 8, 9} → False := by
  intro a69 n153 n209 n264 n268 n271 n273 n275
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 8} a69
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n153 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n209 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 8} = {2, 3, 8, 9} by decide)) hS)

theorem c1025 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {2, 3, 8} → False := by
  intro a209 n69
  exact n69 (h.down {1, 2, 3, 8} {2, 3, 8} a209 (by decide) (by decide))

theorem c1030 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {2, 3, 8, 9} → False := by
  intro a268 n153 n209 n264 n271 n273 n275
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 5, 8} {2, 3, 8} a268 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n153 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n209 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 8} = {2, 3, 8, 9} by decide)) hS)

theorem c1035 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {2, 3, 8} → False := by
  intro a275 n69
  exact n69 (h.down {2, 3, 8, 9} {2, 3, 8} a275 (by decide) (by decide))

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

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

theorem c1202 (h : TenSystem T Q) :
    T {2, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 6, 8, 9} → False := by
  intro a81 n165 n221 n271 n281 n287 n292 n294
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 6, 8} a81
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n165 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 6, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 6, 8} = {2, 6, 8, 9} by decide)) hS)

theorem c1210 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 6, 8, 9} → False := by
  intro a281 n165 n221 n271 n287 n292 n294
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 8} {2, 6, 8} a281 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n165 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 6, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 6, 8} = {2, 6, 8, 9} by decide)) hS)

theorem c1252 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a274 n84
  exact n84 (h.down {2, 3, 7, 9} {2, 7, 9} a274 (by decide) (by decide))

theorem c1258 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a293 n84
  exact n84 (h.down {2, 6, 7, 9} {2, 7, 9} a293 (by decide) (by decide))

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

theorem c1299 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 4, 6} → False := by
  intro a296 n87
  exact n87 (h.down {3, 4, 5, 6} {3, 4, 6} a296 (by decide) (by decide))

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

theorem c1395 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 8} → False := by
  intro a311 n93
  exact n93 (h.down {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide))

theorem c1410 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 9} → False := by
  intro a311 n94
  exact n94 (h.down {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide))

theorem c1425 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {3, 6, 7} → False := by
  intro a313 n95
  exact n95 (h.down {3, 6, 7, 9} {3, 6, 7} a313 (by decide) (by decide))

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

theorem c1453 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {3, 6, 9} → False := by
  intro a313 n97
  exact n97 (h.down {3, 6, 7, 9} {3, 6, 9} a313 (by decide) (by decide))

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

theorem c1479 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a304 n99
  exact n99 (h.down {3, 4, 7, 9} {3, 7, 9} a304 (by decide) (by decide))

theorem c1480 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a304 n183 n239 n274 n310 n313 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {3, 7, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
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

theorem c1629 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a304 n109
  exact n109 (h.down {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide))

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

theorem c1715 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {5, 7, 9} → False := by
  intro a255 n115
  exact n115 (h.down {1, 5, 7, 9} {5, 7, 9} a255 (by decide) (by decide))

theorem c1719 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {5, 7, 9} → False := by
  intro a310 n115
  exact n115 (h.down {3, 5, 7, 9} {5, 7, 9} a310 (by decide) (by decide))

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

theorem c1757 (h : TenSystem T Q) :
    T {6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a118 n202 n258 n293 n313 n323 n327 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {6, 7, 9} a118
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n202 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1759 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a202 n258 n293 n313 n323 n327 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 7, 9} {6, 7, 9} a202 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n258 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1760 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a258 n118
  exact n118 (h.down {1, 6, 7, 9} {6, 7, 9} a258 (by decide) (by decide))

theorem c1763 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a293 n202 n258 n313 n323 n327 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 7, 9} {6, 7, 9} a293 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n202 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1764 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a313 n118
  exact n118 (h.down {3, 6, 7, 9} {6, 7, 9} a313 (by decide) (by decide))

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

theorem c1804 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  intro a121 n102 n119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n102 (hc.mpr n119)

theorem c1807 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {6, 7, 9} → False := by
  intro a121 a103 a118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a103 a118

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

theorem c1812 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {5, 7, 9} → False := by
  intro a121 n106 n115
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n106 (hc.mpr n115)

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

theorem c1878 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a121 n103 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c1880 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n103 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c1927 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {5, 7, 9} → T {6, 7, 9} → False := by
  intro a121 a109 a115 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c1931 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {6, 7, 9} → T {7, 8, 9} → False := by
  intro a121 a109 a118 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 9} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c1935 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a121 a110 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c2207 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a123 a99 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {7, 9} {3, 4, 6} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

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

theorem c2927 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → T {2, 4, 8} → T {6, 7, 9} → False := by
  intro a129 a74 a118
  have hc := h.complementary {0, 1, 3, 5} {2, 4, 8} a129 (by decide) (by decide)
  have he : ( {0, 1, 3, 5} : Finset Labels)ᶜ \ {2, 4, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a74 a118

theorem c3066 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 4, 8} → ¬ T {5, 7, 9} → False := by
  intro a130 n74 n115
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 8} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n74 (hc.mpr n115)

theorem c3231 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a131 a71 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {2, 5} {4, 6, 8} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c3343 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {6, 7, 9} → False := by
  intro a132 a71 a118
  have hc := h.complementary {0, 1, 3, 8} {2, 4, 5} a132 (by decide) (by decide)
  have he : ( {0, 1, 3, 8} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a118

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

theorem c3513 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a133 a71 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 6, 8} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

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

theorem c4685 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 7} → T {3, 6, 7} → T {3, 7, 9} → False := by
  intro a141 a88 a95 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {3, 7} {4, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

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

theorem c5031 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {2, 4, 5} → T {3, 7, 9} → False := by
  intro a144 a71 a99
  have hc := h.complementary {0, 1, 6, 8} {2, 4, 5} a144 (by decide) (by decide)
  have he : ( {0, 1, 6, 8} : Finset Labels)ᶜ \ {2, 4, 5} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a99

theorem c5369 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a146 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 8} {3, 4} {5, 6, 9} a146 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c5442 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ T {2, 3, 4} → ¬ T {5, 6, 8} → False := by
  intro a147 n65 n112
  have hc := h.complementary {0, 1, 7, 9} {2, 3, 4} a147 (by decide) (by decide)
  have he : ( {0, 1, 7, 9} : Finset Labels)ᶜ \ {2, 3, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n65 (hc.mpr n112)

theorem c5449 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 3, 8} → T {4, 5, 6} → False := by
  intro a147 a69 a101
  have hc := h.complementary {0, 1, 7, 9} {2, 3, 8} a147 (by decide) (by decide)
  have he : ( {0, 1, 7, 9} : Finset Labels)ᶜ \ {2, 3, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a69 a101

theorem c5501 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 4, 8} → T {2, 5, 8} → T {2, 6, 8} → False := by
  intro a147 a74 a78 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {2, 8} {4, 5, 6} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 8} = {2, 6, 8} by decide)) a81)

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

theorem c5727 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 8} → T {6, 7, 9} → False := by
  intro a149 a57 a118
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 8} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a118

theorem c5848 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 7, 9} → ¬ T {5, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a149 n63 n115 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 4} {7, 9} {1, 5, 8} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n63 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

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

theorem c5867 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 4, 8} → T {6, 7, 9} → False := by
  intro a150 a53 a118
  have hc := h.complementary {0, 2, 3, 5} {1, 4, 8} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 4, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a53 a118

theorem c5987 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a150 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {7, 9} {1, 4, 6} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c5995 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 8, 9} → T {4, 8, 9} → T {6, 8, 9} → False := by
  intro a150 a64 a110 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {8, 9} {1, 4, 6} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c6002 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 4, 5} → ¬ T {7, 8, 9} → False := by
  intro a151 n50 n120
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 5} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n50 (hc.mpr n120)

theorem c6130 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 7, 9} → ¬ T {5, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a151 n63 n115 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 6} {7, 9} {1, 5, 8} a151 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n63 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c6143 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 5} → T {6, 8, 9} → False := by
  intro a152 a50 a119
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 5} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a119

theorem c6187 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 8} → T {1, 5, 8} → T {1, 6, 8} → False := by
  intro a152 a53 a57 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 7} {1, 8} {4, 5, 6} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 8} = {1, 4, 8} by decide)) a53)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 8} = {1, 6, 8} by decide)) a60)

theorem c6283 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 5} → T {6, 7, 9} → False := by
  intro a153 a50 a118
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 5} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a118

theorem c6292 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 5, 7} → ¬ T {4, 6, 9} → False := by
  intro a153 n56 n107
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 7} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n56 (hc.mpr n107)

theorem c6294 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 5, 9} → ¬ T {4, 6, 7} → False := by
  intro a153 n58 n105
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 9} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n58 (hc.mpr n105)

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

theorem c6417 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a153 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {7, 9} {1, 4, 6} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c6475 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 8} → T {1, 5, 8} → T {1, 6, 8} → False := by
  intro a154 a53 a57 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {1, 8} {4, 5, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 8} = {1, 4, 8} by decide)) a53)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 8} = {1, 6, 8} by decide)) a60)

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

theorem c7625 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {3, 4, 7} → T {3, 6, 7} → T {3, 7, 9} → False := by
  intro a162 a88 a95 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {3, 7} {4, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c7635 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a162 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 6} {1, 3, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

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

theorem c8095 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 7, 9} → T {3, 7, 9} → T {4, 7, 9} → False := by
  intro a165 a63 a99 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {7, 9} {1, 3, 4} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)

theorem c8335 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a167 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {4, 5} {1, 3, 6} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8475 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a168 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 5} {1, 3, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

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

theorem c9115 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 2, 5} → T {1, 5, 7} → T {1, 5, 9} → False := by
  intro a173 a39 a56 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {1, 5} {2, 7, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

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

theorem c9362 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {1, 2, 4} → ¬ T {7, 8, 9} → False := by
  intro a175 n38 n120
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 4} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n120)

theorem c9506 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {1, 2, 8} → ¬ T {4, 6, 9} → False := by
  intro a176 n42 n107
  have hc := h.complementary {0, 3, 5, 7} {1, 2, 8} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 2, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n107)

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

theorem c9779 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a177 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {7, 9} {1, 4, 6} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c9788 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ T {1, 2, 8} → ¬ T {4, 6, 7} → False := by
  intro a178 n42 n105
  have hc := h.complementary {0, 3, 5, 9} {1, 2, 8} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 2, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n105)

theorem c10062 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {1, 2, 4} → ¬ T {5, 7, 9} → False := by
  intro a180 n38 n115
  have hc := h.complementary {0, 3, 6, 8} {1, 2, 4} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n115)

theorem c10081 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 7, 9} → T {2, 4, 5} → False := by
  intro a180 a63 a71
  have hc := h.complementary {0, 3, 6, 8} {1, 7, 9} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a63 a71

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

theorem c10411 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a182 a39 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {2, 5} {1, 4, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c10435 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a182 a50 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {4, 5} {1, 2, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c10482 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 4} → ¬ T {5, 6, 8} → False := by
  intro a183 n38 n112
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 4} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n112)

theorem c10486 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 6} → ¬ T {4, 5, 8} → False := by
  intro a183 n40 n103
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 6} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n103)

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

theorem c10691 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a184 a39 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {2, 5} {1, 4, 6} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c10715 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a184 a50 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 5} {1, 2, 6} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

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

theorem c10778 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {1, 7, 9} → ¬ T {2, 3, 8} → False := by
  intro a185 n63 n69
  have hc := h.complementary {0, 4, 5, 6} {1, 7, 9} a185 (by decide) (by decide)
  have he : ( {0, 4, 5, 6} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 3, 8} := by decide
  rw [he] at hc
  exact n63 (hc.mpr n69)

theorem c10793 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a185 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 3} {2, 7, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
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

theorem c11043 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {6, 7, 9} → False := by
  intro a187 a37 a118
  have hc := h.complementary {0, 4, 5, 8} {1, 2, 3} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a118

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

theorem c11495 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a190 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 3} {2, 7, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11859 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 5, 6} → T {2, 5, 6} → T {3, 5, 6} → False := by
  intro a192 a55 a76 a91
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {5, 6} {1, 2, 3} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)

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

theorem c12139 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 5, 6} → T {2, 5, 6} → T {3, 5, 6} → False := by
  intro a194 a55 a76 a91
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {5, 6} {1, 2, 3} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)

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

theorem c12695 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → T {3, 4, 9} → T {3, 6, 9} → False := by
  intro a198 a49 a90 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {3, 9} {1, 4, 6} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

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

theorem c12975 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 7} → T {3, 4, 7} → T {3, 6, 7} → False := by
  intro a200 a47 a88 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {3, 7} {1, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)

theorem c13071 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 4} → T {2, 3, 4} → T {2, 4, 5} → False := by
  intro a201 a38 a65 a71
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {2, 4} {1, 3, 5} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)

theorem c13145 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → T {1, 2, 4} → T {3, 5, 8} → False := by
  intro a202 a38 a93
  have hc := h.complementary {0, 6, 7, 9} {1, 2, 4} a202 (by decide) (by decide)
  have he : ( {0, 6, 7, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a38 a93

theorem c13280 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {2, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a202 n78 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 6, 7, 9} {5, 8} {2, 3, 4} a202 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c13351 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 4} → T {2, 3, 4} → T {2, 4, 5} → False := by
  intro a203 a38 a65 a71
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {2, 4} {1, 3, 5} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)

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

theorem c13562 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 6} → ¬ T {7, 8, 9} → False := by
  intro a205 n27 n120
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 6} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n120)

theorem c13842 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 4, 5} → ¬ T {7, 8, 9} → False := by
  intro a207 n22 n120
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 5} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n120)

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

theorem c14027 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a208 a25 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {0, 8} {4, 5, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c14123 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 5} → T {6, 7, 9} → False := by
  intro a209 a22 a118
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 5} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a118

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

theorem c14315 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a210 a25 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {0, 8} {4, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c15246 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 3, 8} → ¬ T {4, 6, 9} → False := by
  intro a217 n20 n107
  have hc := h.complementary {1, 2, 5, 7} {0, 3, 8} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n107)

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

theorem c15521 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a218 a99 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {7, 9} {3, 4, 6} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c15528 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 3, 8} → ¬ T {4, 6, 7} → False := by
  intro a219 n20 n105
  have hc := h.complementary {1, 2, 5, 9} {0, 3, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n105)

theorem c15811 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {0, 4, 5} → T {3, 7, 9} → False := by
  intro a221 a22 a99
  have hc := h.complementary {1, 2, 6, 8} {0, 4, 5} a221 (by decide) (by decide)
  have he : ( {1, 2, 6, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a99

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

theorem c16281 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 4, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a224 a25 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {0, 8} {4, 5, 6} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c16289 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a224 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {3, 4} {5, 6, 8} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c16327 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a224 a23 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {4, 6} {0, 5, 8} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

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

theorem c16924 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → ¬ T {0, 2, 6} → ¬ T {5, 7, 9} → False := by
  intro a229 n12 n115
  have hc := h.complementary {1, 3, 4, 8} {0, 2, 6} a229 (by decide) (by decide)
  have he : ( {1, 3, 4, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n115)

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

theorem c17207 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 8} → T {4, 7, 9} → False := by
  intro a231 a14 a109
  have hc := h.complementary {1, 3, 5, 6} {0, 2, 8} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a14 a109

theorem c17387 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 8} → T {0, 4, 8} → T {0, 6, 8} → False := by
  intro a232 a14 a25 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {0, 8} {2, 4, 6} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

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

theorem c17619 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a233 a35 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {7, 9} {0, 4, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c17621 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {2, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a233 a84 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {7, 9} {2, 4, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c17675 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 8} → T {0, 4, 8} → T {0, 6, 8} → False := by
  intro a234 a14 a25 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {0, 8} {2, 4, 6} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c17902 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {0, 2, 4} → ¬ T {5, 7, 9} → False := by
  intro a236 n10 n115
  have hc := h.complementary {1, 3, 6, 8} {0, 2, 4} a236 (by decide) (by decide)
  have he : ( {1, 3, 6, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n115)

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

theorem c18275 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → T {0, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a238 a22 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 8} {4, 5} {0, 2, 6} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

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

theorem c18397 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a239 a71 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 9} {2, 5} {4, 6, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c18427 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a239 a23 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 9} {4, 6} {0, 5, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c18450 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a239 n29 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 8} {0, 4, 6} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c18452 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {2, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a239 n78 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 8} {2, 4, 6} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

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

theorem c18488 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a240 n11 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {0, 2} {5, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

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

theorem c18604 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 2, 7} → ¬ T {3, 8, 9} → False := by
  intro a241 n13 n100
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 7} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n100)

theorem c18612 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 3, 8} → ¬ T {2, 7, 9} → False := by
  intro a241 n20 n84
  have hc := h.complementary {1, 4, 5, 6} {0, 3, 8} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 7, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n84)

theorem c18618 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 7, 9} → ¬ T {2, 3, 8} → False := by
  intro a241 n35 n69
  have hc := h.complementary {1, 4, 5, 6} {0, 7, 9} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {2, 3, 8} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n69)

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

theorem c18727 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 7, 9} → T {2, 7, 9} → T {3, 7, 9} → False := by
  intro a241 a35 a84 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {7, 9} {0, 2, 3} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)

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

theorem c19435 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 7, 9} → T {2, 7, 9} → T {3, 7, 9} → False := by
  intro a246 a35 a84 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {7, 9} {0, 2, 3} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)

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

theorem c19728 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 8} → ¬ T {3, 5, 6} → False := by
  intro a249 n14 n91
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n91)

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

theorem c20983 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 2, 3} → T {4, 5, 8} → False := by
  intro a258 a9 a103
  have hc := h.complementary {1, 6, 7, 9} {0, 2, 3} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a103

theorem c20995 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 3, 8} → T {2, 4, 5} → False := by
  intro a258 a20 a71
  have hc := h.complementary {1, 6, 7, 9} {0, 3, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a20 a71

theorem c21000 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 3, 4} → False := by
  intro a258 n29 n65
  have hc := h.complementary {1, 6, 7, 9} {0, 5, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n65)

theorem c21001 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 5, 8} → T {2, 3, 4} → False := by
  intro a258 a29 a65
  have hc := h.complementary {1, 6, 7, 9} {0, 5, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a29 a65

theorem c21039 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 2, 8} → T {0, 4, 8} → T {0, 5, 8} → False := by
  intro a258 a14 a25 a29
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 9} {0, 8} {2, 4, 5} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)

theorem c21100 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a258 n22 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {4, 5} {0, 2, 8} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c21104 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {2, 4, 5} → ¬ T {3, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a258 n71 n86 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {4, 5} {2, 3, 8} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n86 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c21118 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a258 n29 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {5, 8} {0, 3, 4} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c21120 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {2, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a258 n78 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {5, 8} {2, 3, 4} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

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

theorem c21824 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 6} → ¬ T {5, 7, 9} → False := by
  intro a264 n5 n115
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 6} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n115)

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

theorem c22521 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a268 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {7, 9} {1, 4, 6} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

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

theorem c22802 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 4} → ¬ T {5, 7, 9} → False := by
  intro a271 n3 n115
  have hc := h.complementary {2, 3, 6, 8} {0, 1, 4} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n115)

theorem c22811 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 5} → T {1, 7, 9} → False := by
  intro a271 a22 a63
  have hc := h.complementary {2, 3, 6, 8} {0, 4, 5} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a63

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

theorem c23175 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → T {0, 4, 5} → T {1, 4, 5} → T {4, 5, 6} → False := by
  intro a273 a22 a50 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 8} {4, 5} {0, 1, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c23222 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {0, 1, 4} → ¬ T {5, 6, 8} → False := by
  intro a274 n3 n112
  have hc := h.complementary {2, 3, 7, 9} {0, 1, 4} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n112)

theorem c23226 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {0, 1, 6} → ¬ T {4, 5, 8} → False := by
  intro a274 n5 n103
  have hc := h.complementary {2, 3, 7, 9} {0, 1, 6} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n103)

theorem c23291 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a274 a4 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 9} {1, 5} {0, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c23512 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 3, 8} → ¬ T {1, 7, 9} → False := by
  intro a276 n20 n63
  have hc := h.complementary {2, 4, 5, 6} {0, 3, 8} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 3, 8} = {1, 7, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n63)

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

theorem c23565 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a276 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {1, 3} {0, 7, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
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

theorem c25043 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {4, 7, 9} → False := by
  intro a287 a2 a109
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 3} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a109

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

theorem c25859 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → T {0, 4, 5} → T {1, 4, 5} → T {3, 4, 5} → False := by
  intro a292 a22 a50 a86
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 7, 8} {4, 5} {0, 1, 3} a292 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)

theorem c25885 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → T {0, 1, 4} → T {3, 5, 8} → False := by
  intro a293 a3 a93
  have hc := h.complementary {2, 6, 7, 9} {0, 1, 4} a293 (by decide) (by decide)
  have he : ( {2, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a3 a93

theorem c26018 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a293 n29 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 6, 7, 9} {5, 8} {0, 3, 4} a293 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

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

theorem c26139 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 4, 5} → T {1, 4, 5} → T {3, 4, 5} → False := by
  intro a294 a22 a50 a86
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {4, 5} {0, 1, 3} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)

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

theorem c26312 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 2, 8} → ¬ T {1, 7, 9} → False := by
  intro a296 n14 n63
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 8} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 7, 9} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n63)

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

theorem c26583 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {6, 7, 9} → False := by
  intro a298 a1 a118
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 2} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a118

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

theorem c27135 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 7, 9} → T {1, 7, 9} → T {2, 7, 9} → False := by
  intro a301 a35 a63 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {7, 9} {0, 1, 2} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)

theorem c27351 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 5} → T {1, 2, 5} → T {1, 5, 6} → False := by
  intro a303 a4 a39 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {1, 5} {0, 2, 6} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c27423 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {5, 6, 8} → False := by
  intro a304 a1 a112
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 2} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a112

theorem c27424 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 5} → ¬ T {2, 6, 8} → False := by
  intro a304 n4 n81
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 5} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n81)

theorem c27426 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {2, 5, 8} → False := by
  intro a304 n5 n78
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n78)

theorem c27427 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 6} → T {2, 5, 8} → False := by
  intro a304 a5 a78
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a5 a78

theorem c27428 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 8} → ¬ T {2, 5, 6} → False := by
  intro a304 n7 n76
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n76)

theorem c27433 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 2, 6} → T {1, 5, 8} → False := by
  intro a304 a12 a57
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a57

theorem c27434 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 2, 8} → ¬ T {1, 5, 6} → False := by
  intro a304 n14 n55
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 5, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n55)

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

theorem c27447 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {0, 1, 6} → T {0, 1, 8} → False := by
  intro a304 a1 a5 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {0, 1} {2, 6, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c27478 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 8} → ¬ T {0, 5, 8} → ¬ T {0, 6, 8} → False := by
  intro a304 n7 n29 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {0, 8} {1, 5, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 8} = {0, 1, 8} by decide)) ht)
  · exact n29 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) ht)

theorem c27487 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a304 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 2} {0, 6, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

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

theorem c27508 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 8} → ¬ T {1, 2, 8} → ¬ T {1, 6, 8} → False := by
  intro a304 n7 n42 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {1, 8} {0, 2, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 8} = {0, 1, 8} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 8} = {1, 2, 8} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 8} = {1, 6, 8} by decide)) ht)

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

theorem c28143 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 6} → False := by
  intro a309 a1 a3 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {0, 1} {2, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c28183 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a309 a1 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 2} {0, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

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

theorem c28423 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 6} → False := by
  intro a311 a1 a3 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 1} {2, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c28463 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a311 a1 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {1, 2} {0, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

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

theorem c28683 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {4, 5, 8} → False := by
  intro a313 a1 a103
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 2} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a103

theorem c28686 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 5} → ¬ T {2, 4, 8} → False := by
  intro a313 n4 n74
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 5} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n74)

theorem c28688 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {2, 4, 5} → False := by
  intro a313 n7 n71
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n71)

theorem c28689 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 8} → T {2, 4, 5} → False := by
  intro a313 a7 a71
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a7 a71

theorem c28691 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 2, 4} → T {1, 5, 8} → False := by
  intro a313 a10 a57
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 4} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a10 a57

theorem c28694 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 2, 8} → ¬ T {1, 4, 5} → False := by
  intro a313 n14 n50
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 4, 5} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n50)

theorem c28695 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 2, 8} → T {1, 4, 5} → False := by
  intro a313 a14 a50
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a14 a50

theorem c28696 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {1, 2, 8} → False := by
  intro a313 n22 n42
  have hc := h.complementary {3, 6, 7, 9} {0, 4, 5} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n42)

theorem c28697 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 4, 5} → T {1, 2, 8} → False := by
  intro a313 a22 a42
  have hc := h.complementary {3, 6, 7, 9} {0, 4, 5} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 8} := by decide
  rw [he] at hc
  exact hc.mp a22 a42

theorem c28698 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 8} → ¬ T {1, 2, 5} → False := by
  intro a313 n25 n39
  have hc := h.complementary {3, 6, 7, 9} {0, 4, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n39)

theorem c28700 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 4} → False := by
  intro a313 n29 n38
  have hc := h.complementary {3, 6, 7, 9} {0, 5, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n38)

theorem c28701 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 5, 8} → T {1, 2, 4} → False := by
  intro a313 a29 a38
  have hc := h.complementary {3, 6, 7, 9} {0, 5, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a29 a38

theorem c28705 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 8} → False := by
  intro a313 a1 a3 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {0, 1} {2, 4, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c28707 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 5} → T {0, 1, 8} → False := by
  intro a313 a1 a4 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {0, 1} {2, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c28738 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {0, 4, 8} → ¬ T {0, 5, 8} → False := by
  intro a313 n7 n25 n29
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {0, 8} {1, 4, 5} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 8} = {0, 1, 8} by decide)) ht)
  · exact n25 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) ht)
  · exact n29 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) ht)

theorem c28743 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 5} → False := by
  intro a313 a1 a38 a39
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 4, 5} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)

theorem c28745 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 8} → False := by
  intro a313 a1 a38 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 4, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28747 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 8} → False := by
  intro a313 a1 a39 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28748 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {1, 2, 4} → ¬ T {1, 2, 5} → ¬ T {1, 2, 8} → False := by
  intro a313 n38 n39 n42
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {1, 2} {4, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) ht)

theorem c28753 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 4} → T {1, 2, 4} → T {1, 4, 8} → False := by
  intro a313 a3 a38 a53
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 4} {0, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 4} = {1, 4, 8} by decide)) a53)

theorem c28759 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 5} → T {1, 2, 5} → T {1, 4, 5} → False := by
  intro a313 a4 a39 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 5} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)

theorem c28766 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {1, 2, 8} → ¬ T {1, 4, 8} → False := by
  intro a313 n7 n42 n53
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {1, 8} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 8} = {0, 1, 8} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 8} = {1, 2, 8} by decide)) ht)
  · exact n53 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 8} = {1, 4, 8} by decide)) ht)

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

theorem c28768 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {1, 2, 8} → ¬ T {1, 5, 8} → False := by
  intro a313 n7 n42 n57
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {1, 8} {0, 2, 5} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 8} = {0, 1, 8} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 8} = {1, 2, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 8} = {1, 5, 8} by decide)) ht)

theorem c28776 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 2, 4} → ¬ T {1, 2, 4} → ¬ T {2, 4, 8} → False := by
  intro a313 n10 n38 n74
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {2, 4} {0, 1, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 4} = {2, 4, 8} by decide)) ht)

theorem c28781 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {1, 2, 4} → T {2, 4, 5} → T {2, 4, 8} → False := by
  intro a313 a38 a71 a74
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {2, 4} {1, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 4} = {2, 4, 8} by decide)) a74)

theorem c28799 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 4, 5} → T {1, 4, 5} → T {2, 4, 5} → False := by
  intro a313 a22 a50 a71
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {4, 5} {0, 1, 2} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)

theorem c28800 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {1, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n22 n50 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {0, 1, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28802 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n22 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {0, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28804 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {1, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n50 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {1, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28818 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a313 n29 n78 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {5, 8} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

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

theorem c31288 (h : TenSystem T Q) :
    ¬ Q {3, 5, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 6, 7, 9} → T {3, 7, 9} → ¬ Q {1, 3, 7, 9} → False := by
  classical
  intro n310 n183 n315 n274 n313 a99 n239
  have u0_304 : Q {3, 4, 7, 9} := by
    by_contra hv
    exact c1472 h a99 n183 n239 n274 hv n310 n313 n315
  exact c1480 h u0_304 n183 n239 n274 n310 n313 n315

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

theorem c31500 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → T {6, 7, 9} → ¬ Q {0, 6, 7, 9} → False := by
  classical
  intro n258 n313 a118 n202
  have u0_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u3_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1757 h a118 n202 n258 hv n313 u0_323 u1_327 u2_330
  exact c1763 h u3_293 n202 n258 n313 u0_323 u1_327 u2_330

private theorem c31503 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → T {2, 4, 5} → Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n29 a71 a258 a313 a304
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u2_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5031 h hv a71 u1_99
  have u3_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u4_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u5_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10081 h hv u4_63 a71
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u7_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8095 h hv u4_63 u1_99 u6_109
  have u8_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u0_37 u6_109
  have u9_38 : T {1, 2, 4} := by
    by_contra hv
    exact c28700 h a313 n29 hv
  have u10_65 : T {2, 3, 4} := by
    by_contra hv
    exact c21000 h a258 n29 hv
  have u11_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27478 h a304 u3_7 n29 hv
  have u12_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13351 h hv u9_38 u10_65 a71
  have u13_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13071 h hv u9_38 u10_65 a71
  have u14_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c31309 h u8_196 u12_203 u7_165 u13_201 hv u5_180 u11_32
  exact c475 h u14_190 u2_144 u7_165 u5_180 u8_196 u13_201 u12_203

private theorem c31504 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 4, 5} → ¬ Q {0, 2, 4, 8} → Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {1, 2, 5, 8} → ¬ Q {0, 1, 2, 5} → Q {3, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {0, 4, 5, 8} → False := by
  classical
  intro a71 n158 a258 a313 n105 n107 n260 n218 n123 a304 n255 n239 n187
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u2_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c20995 h a258 hv a71
  have u3_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u4_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c292 h hv u2_20
  have u5_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15528 h hv u2_20 n105
  have u6_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15246 h hv u2_20 n107
  have u7_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c97 h hv u3_7
  have u8_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u3_7 hv
  have u9_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31503 h h0 hv a71 a258 a313 a304
  have u10_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h a313 u9_29 hv
  have u11_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u9_29 hv
  have u12_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c21001 h a258 u9_29 hv
  have u13_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c562 h hv u10_38
  have u14_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c594 h hv u11_40
  have u15_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5442 h hv u12_65 u1_112
  have u16_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c576 h hv n123 u13_211 u14_216 u6_217 n218 u5_219
  have u17_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c572 h hv n123 u16_206 u13_211 u14_216 u6_217 n218 u5_219
  have u18_25 : T {0, 4, 8} := by
    by_contra hv
    exact c28698 h a313 hv u17_39
  have u19_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u17_39
  have u20_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16281 h hv u18_25 u9_29 u19_32
  have u21_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c21039 h a258 hv u18_25 u9_29
  have u22_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c944 h a258 u15_147 u20_224 n239 hv n255 n260
  have u23_55 : T {1, 5, 6} := by
    by_contra hv
    exact c27434 h a304 u21_14 hv
  have u24_91 : T {3, 5, 6} := by
    by_contra hv
    exact c19728 h u22_249 u21_14 hv
  have u25_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11859 h hv u23_55 u8_76 u24_91
  have u26_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12139 h hv u23_55 u8_76 u24_91
  exact c31431 h u4_173 u7_137 n187 u26_194 u25_192 u18_25 n158

theorem c31505 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 3, 7, 9} → T {6, 7, 9} → False := by
  classical
  intro a258 a313 a304 n255 n239 a118
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1425 h a313 hv
  have u5_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1807 h u2_121 hv a118
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u3_1 hv
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1880 h u2_121 u5_103 u6_112 hv
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u2_121 hv u7_116
  have u9_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1878 h u2_121 u5_103 u6_112 hv
  have u10_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u2_121 hv u9_114
  have u11_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u12_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u2_121 u11_109 a118 hv
  have u13_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv u12_120
  have u14_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25043 h hv u1_2 u11_109
  have u15_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u16_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15521 h hv u15_99 u11_109 a118
  have u17_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2207 h hv u15_99 u11_109 a118
  have u18_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11043 h hv u0_37 a118
  have u19_59 : T {1, 6, 7} := by
    by_contra hv
    exact c885 h a258 hv
  have u20_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u21_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7101 h hv u19_59 u4_95 a118
  have u22_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c8095 h hv u20_63 u15_99 u11_109
  have u23_71 : ¬ T {2, 4, 5} := by
    intro hv
    exact c31504 h h0 hv u21_158 a258 a313 u8_105 u10_107 u13_260 u16_218 u17_123 a304 n255 n239 u18_187
  have u24_7 : T {0, 1, 8} := by
    by_contra hv
    exact c28688 h a313 hv u23_71
  have u25_50 : T {1, 4, 5} := by
    by_contra hv
    exact c28804 h a313 hv u23_71 u5_103
  have u26_22 : T {0, 4, 5} := by
    by_contra hv
    exact c21100 h a258 hv u23_71 u5_103
  have u27_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21104 h a258 u23_71 hv u5_103
  have u28_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28707 h a313 u3_1 hv u24_7
  have u29_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15811 h hv u26_22 u15_99
  have u30_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22811 h hv u26_22 u20_63
  have u31_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26139 h hv u26_22 u25_50 u27_86
  have u32_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25859 h hv u26_22 u25_50 u27_86
  have u33_81 : T {2, 6, 8} := by
    by_contra hv
    exact c27424 h a304 u28_4 hv
  have u34_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c1210 h hv u22_165 u29_221 u30_271 u14_287 u32_292 u31_294
  exact c1202 h u33_81 u22_165 u29_221 u30_271 u34_281 u14_287 u32_292 u31_294

theorem c31506 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 4, 5} → ¬ Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n71 n258 a313 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u3_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u4_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u0_121 u2_109 hv u3_118
  have u5_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1812 h u0_121 hv u4_115
  have u6_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c1715 h hv u4_115
  have u7_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u2_109 u3_118 hv
  have u8_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv u7_120
  have u9_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv u7_120
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u1_1 hv
  have u11_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u12_7 : T {0, 1, 8} := by
    by_contra hv
    exact c28688 h a313 hv n71
  have u13_50 : T {1, 4, 5} := by
    by_contra hv
    exact c28804 h a313 hv n71 u10_103
  have u14_22 : T {0, 4, 5} := by
    by_contra hv
    exact c28802 h a313 hv n71 u10_103
  have u15_185 : Q {0, 4, 5, 6} := by
    by_contra hv
    exact c31269 h h0 hv n71 u7_120
  have u16_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u11_276 u8_101
  have u17_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c27447 h a304 u1_1 hv u12_7
  have u18_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28707 h a313 u1_1 hv u12_7
  have u19_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28705 h a313 u1_1 hv u12_7
  have u20_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6283 h hv u13_50 u3_118
  have u21_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23175 h hv u14_22 u13_50 u8_101
  have u22_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14123 h hv u14_22 u3_118
  have u23_23 : T {0, 4, 6} := by
    by_contra hv
    exact c339 h u15_185 hv
  have u24_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21824 h hv u17_5 u4_115
  have u25_78 : T {2, 5, 8} := by
    by_contra hv
    exact c27426 h a304 u17_5 hv
  have u26_81 : T {2, 6, 8} := by
    by_contra hv
    exact c27424 h a304 u18_4 hv
  have u27_74 : T {2, 4, 8} := by
    by_contra hv
    exact c28686 h a313 u18_4 hv
  have u28_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22802 h hv u19_3 u4_115
  have u29_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18427 h hv u23_23 u8_101 u5_106
  have u30_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16327 h hv u23_23 u8_101 u5_106
  have u31_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c1030 h hv u20_153 u22_209 u24_264 u28_271 u21_273 u16_275
  have u32_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5501 h hv u27_74 u25_78 u26_81
  have u33_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c1022 h hv u20_153 u22_209 u24_264 u31_268 u28_271 u21_273 u16_275
  have u34_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c940 h hv u32_147 u30_224 u29_239 u6_255 n258 u9_260
  have u35_63 : T {1, 7, 9} := by
    by_contra hv
    exact c10778 h u15_185 hv u33_69
  exact c932 h u35_63 u32_147 u30_224 u29_239 u34_249 u6_255 n258 u9_260

theorem c31507 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 5} → T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a22 a63 a71 a313 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u3_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5987 h hv a63 u2_109 u1_118
  have u4_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6417 h hv a63 u2_109 u1_118
  have u5_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u6_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u2_109 u1_118 hv
  have u7_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c28697 h a313 a22 hv
  have u8_50 : ¬ T {1, 4, 5} := by
    intro hv
    exact c28799 h a313 a22 hv a71
  have u9_53 : T {1, 4, 8} := by
    by_contra hv
    exact c28766 h a313 u5_7 u7_42 hv
  have u10_57 : T {1, 5, 8} := by
    by_contra hv
    exact c28768 h a313 u5_7 u7_42 hv
  have u11_60 : T {1, 6, 8} := by
    by_contra hv
    exact c27508 h a304 u5_7 u7_42 hv
  have u12_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6002 h hv u8_50 u6_120
  have u13_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5727 h hv u10_57 u1_118
  have u14_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6187 h hv u9_53 u10_57 u11_60
  have u15_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6475 h hv u9_53 u10_57 u11_60
  exact c124 h u0_121 u13_149 u3_150 u12_151 u14_152 u4_153 u15_154

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases099
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31508 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a63 n239 n258 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31506 h h0 hv n258 a313 a304
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u3_109 hv u4_118
  have u6_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c1715 h hv u5_115
  have u7_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u3_109 u4_118 hv
  have u8_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u1_121 hv u7_120
  have u9_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c1790 h hv u7_120
  have u10_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c31507 h h0 hv a63 u2_71 a313 a304
  have u11_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13842 h hv u10_22 u7_120
  have u12_42 : T {1, 2, 8} := by
    by_contra hv
    exact c28696 h a313 u10_22 hv
  have u13_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c27437 h a304 hv u12_42
  have u14_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28745 h a313 u0_1 hv u12_42
  have u15_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c28747 h a313 u0_1 hv u12_42
  have u16_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13562 h hv u13_27 u7_120
  have u17_29 : T {0, 5, 8} := by
    by_contra hv
    exact c28700 h a313 hv u14_38
  have u18_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u15_39
  have u19_25 : T {0, 4, 8} := by
    by_contra hv
    exact c28698 h a313 hv u15_39
  have u20_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u15_39
  have u21_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c14315 h hv u19_25 u17_29 u20_32
  have u22_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16281 h hv u19_25 u17_29 u20_32
  have u23_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14027 h hv u19_25 u17_29 u20_32
  have u24_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c544 h u1_121 u16_205 u18_206 u11_207 u23_208 hv u21_210
  have u25_69 : T {2, 3, 8} := by
    by_contra hv
    exact c1025 h u24_209 hv
  have u26_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5449 h hv u25_69 u8_101
  have u27_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c940 h hv u26_147 u22_224 n239 u6_255 n258 u9_260
  exact c932 h a63 u26_147 u22_224 n239 u27_249 u6_255 n258 u9_260

private theorem c31509 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 5} → ¬ T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n22 n63 a71 a313 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u5_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u6_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u5_118
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u8_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u7_109 u5_118 hv
  have u9_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv u8_120
  have u10_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u0_121 u7_109 hv u5_118
  have u11_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u1_1 hv
  have u12_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c324 h hv n22
  have u13_42 : T {1, 2, 8} := by
    by_contra hv
    exact c28696 h a313 n22 hv
  have u14_50 : T {1, 4, 5} := by
    by_contra hv
    exact c28800 h a313 n22 hv u11_103
  have u15_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28745 h a313 u1_1 hv u13_42
  have u16_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27487 h a304 u1_1 hv u13_42
  have u17_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6283 h hv u14_50 u5_118
  have u18_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10435 h hv u14_50 a71 u9_101
  have u19_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10715 h hv u14_50 a71 u9_101
  have u20_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c28695 h a313 hv u14_50
  have u21_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv u15_38 u10_115
  have u22_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9084 h hv u16_40 u10_115
  have u23_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26312 h hv u20_14 n63
  have u24_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c295 h hv u6_132 u17_153 u22_173 u21_180 u18_182 u19_184
  have u25_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c287 h hv u6_132 u17_153 u22_173 u24_177 u21_180 u18_182 u19_184
  have u26_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23512 h hv u25_20 n63
  have u27_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 u12_185 hv u9_101 u26_276
  exact c1506 h u27_241 u12_185 u26_276 u23_296 u4_316 u3_317 u2_318

private theorem c31510 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 4} → ¬ T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n38 n63 a71 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u3_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1880 h u1_121 u3_103 u2_112 hv
  have u5_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv u4_116
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u7_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u8_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u6_109 u7_118 hv
  have u9_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u6_109 hv u7_118
  have u10_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6130 h hv n63 u9_115 u8_120
  have u11_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5848 h hv n63 u9_115 u8_120
  have u12_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u13_22 : T {0, 4, 5} := by
    by_contra hv
    exact c31509 h h0 hv n63 a71 a313 a304
  have u14_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c28697 h a313 u13_22 hv
  have u15_57 : T {1, 5, 8} := by
    by_contra hv
    exact c28768 h a313 u12_7 u14_42 hv
  have u16_53 : T {1, 4, 8} := by
    by_contra hv
    exact c28766 h a313 u12_7 u14_42 hv
  have u17_60 : T {1, 6, 8} := by
    by_contra hv
    exact c27508 h a304 u12_7 u14_42 hv
  have u18_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6187 h hv u16_53 u15_57 u17_60
  have u19_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5867 h hv u16_53 u7_118
  have u20_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6475 h hv u16_53 u15_57 u17_60
  have u21_153 : Q {0, 2, 3, 8} := by
    by_contra hv
    exact c124 h u1_121 u11_149 u19_150 u10_151 u18_152 hv u20_154
  have u22_58 : T {1, 5, 9} := by
    by_contra hv
    exact c6294 h u21_153 hv u5_105
  have u23_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1878 h u1_121 u3_103 u2_112 hv
  have u24_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u1_121 hv u23_114
  have u25_56 : T {1, 5, 7} := by
    by_contra hv
    exact c6292 h u21_153 hv u24_107
  have u26_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28691 h a313 hv u15_57
  have u27_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9788 h hv u14_42 u5_105
  have u28_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9506 h hv u14_42 u24_107
  have u29_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u12_7 hv
  have u30_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u7_118
  have u31_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv n38 u9_115
  have u32_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9362 h hv n38 u8_120
  have u33_29 : T {0, 5, 8} := by
    by_contra hv
    exact c28700 h a313 hv n38
  have u34_39 : T {1, 2, 5} := by
    by_contra hv
    exact c28748 h a313 n38 hv u14_42
  have u35_74 : T {2, 4, 8} := by
    by_contra hv
    exact c28776 h a313 u26_10 n38 hv
  have u36_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u33_29 hv
  have u37_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9115 h hv u34_39 u25_56 u22_58
  have u38_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10411 h hv u34_39 a71 u29_76
  have u39_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10691 h hv u34_39 a71 u29_76
  have u40_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c2927 h hv u35_74 u7_118
  have u41_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8662 h hv u36_40 u8_120
  have u42_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c291 h u21_153 u30_132 u37_173 hv u31_180 u38_182 u39_184
  exact c254 h u42_177 u40_129 u19_150 u41_170 u32_175 u28_176 u27_178

theorem c31511 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 7, 9} → T {2, 4, 5} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n63 a71 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv a71
  have u3_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u2_7 hv
  have u4_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u5_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3343 h hv a71 u4_118
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u7_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u6_109 u4_118 hv
  have u8_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u1_121 hv u7_120
  have u9_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u6_109 hv u4_118
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u11_22 : T {0, 4, 5} := by
    by_contra hv
    exact c31509 h h0 hv n63 a71 a313 a304
  have u12_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14123 h hv u11_22 u4_118
  have u13_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c18555 h hv u11_22 a71 u8_101
  have u14_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18275 h hv u11_22 a71 u8_101
  have u15_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c28697 h a313 u11_22 hv
  have u16_50 : ¬ T {1, 4, 5} := by
    intro hv
    exact c28799 h a313 u11_22 hv a71
  have u17_53 : T {1, 4, 8} := by
    by_contra hv
    exact c28766 h a313 u2_7 u15_42 hv
  have u18_57 : T {1, 5, 8} := by
    by_contra hv
    exact c28768 h a313 u2_7 u15_42 hv
  have u19_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c742 h hv u16_50
  have u20_14 : T {0, 2, 8} := by
    by_contra hv
    exact c28694 h a313 hv u16_50
  have u21_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28691 h a313 hv u18_57
  have u22_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c27433 h a304 hv u18_57
  have u23_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17207 h hv u20_14 u6_109
  have u24_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c17902 h hv u21_10 u9_115
  have u25_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16924 h hv u22_12 u9_115
  have u26_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c715 h hv u5_132 u12_209 u25_229 u24_236 u14_238 u13_240
  have u27_38 : T {1, 2, 4} := by
    by_contra hv
    exact c31510 h h0 hv n63 a71 a313 a304
  have u28_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c28701 h a313 hv u27_38
  have u29_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c28781 h a313 u27_38 a71 hv
  have u30_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c28743 h a313 u0_1 u27_38 hv
  have u31_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28753 h a313 hv u27_38 u17_53
  have u32_78 : T {2, 5, 8} := by
    by_contra hv
    exact c28818 h a313 u28_29 hv u10_103
  have u33_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27478 h a304 u2_7 u28_29 hv
  have u34_25 : T {0, 4, 8} := by
    by_contra hv
    exact c28738 h a313 u2_7 hv u28_29
  have u35_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3066 h hv u29_74 u9_115
  have u36_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u30_39
  have u37_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c35 h hv u31_3
  have u38_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3513 h hv a71 u3_76 u32_78
  have u39_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3231 h hv a71 u3_76 u32_78
  have u40_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17387 h hv u20_14 u34_25 u33_32
  have u41_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17675 h hv u20_14 u34_25 u33_32
  have u42_129 : Q {0, 1, 3, 5} := by
    by_contra hv
    exact c19 h u1_121 u37_128 hv u35_130 u39_131 u5_132 u38_133
  exact c664 h u42_129 u36_206 u19_226 u23_231 u40_232 u26_233 u41_234

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases100
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31512 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 6, 7, 9} → Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n258 a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u3_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31506 h h0 hv n258 a313 a304
  have u4_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c28689 h a313 hv u3_71
  have u5_76 : T {2, 5, 6} := by
    by_contra hv
    exact c27428 h a304 u4_7 hv
  have u6_63 : T {1, 7, 9} := by
    by_contra hv
    exact c31511 h h0 hv u3_71 a313 a304
  have u7_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31508 h h0 u6_63 hv n258 a313 a304
  have u8_78 : T {2, 5, 8} := by
    by_contra hv
    exact c18452 h u7_239 hv u1_103 u2_112
  exact c18397 h u7_239 u3_71 u5_76 u8_78

theorem c31513 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a313 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u1_37 u3_109
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u6_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u7_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u8_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u9_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1425 h a313 hv
  have u10_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1453 h a313 hv
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u12_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c28683 h a313 u0_1 hv
  have u13_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7625 h hv u8_88 u9_95 u6_99
  have u14_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4685 h hv u8_88 u9_95 u6_99
  have u15_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11043 h hv u1_37 u11_118
  have u16_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u2_121 u3_109 hv u11_118
  have u17_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c1715 h hv u16_115
  have u18_258 : Q {1, 6, 7, 9} := by
    by_contra hv
    exact c31512 h h0 hv a313 a304
  have u19_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h u18_258 hv
  have u20_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31505 h h0 u18_258 a313 a304 u17_255 hv u11_118
  have u21_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9779 h hv u19_63 u3_109 u11_118
  have u22_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u20_239 hv
  have u23_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h u20_239 hv
  have u24_29 : T {0, 5, 8} := by
    by_contra hv
    exact c18450 h u20_239 hv u12_103 u5_112
  have u25_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12975 h hv u22_47 u8_88 u9_95
  have u26_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12695 h hv u23_49 u7_90 u10_97
  exact c422 h u24_29 u14_141 u13_162 u21_177 u15_187 u4_196 u26_198 u25_200

private theorem c31514 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → ¬ T {7, 8, 9} → Q {1, 6, 7, 9} → T {3, 7, 9} → False := by
  classical
  intro a239 n120 a258 a99
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
  have u4_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv n120
  have u5_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u6_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h a239 hv
  have u7_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23565 h hv u1_2 u5_47 u6_49
  have u8_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 u6_49 hv
  have u9_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10793 h hv u2_37 u5_47 u6_49
  have u10_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u8_210 hv
  have u11_71 : T {2, 4, 5} := by
    by_contra hv
    exact c31269 h h0 u9_185 hv n120
  have u12_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 u9_185 hv u4_101 u7_276
  have u13_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c20995 h a258 hv u11_71
  have u14_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c18667 h u12_241 u3_9 hv u10_70
  have u15_84 : T {2, 7, 9} := by
    by_contra hv
    exact c18612 h u12_241 u13_20 hv
  have u16_35 : T {0, 7, 9} := by
    by_contra hv
    exact c18618 h u12_241 hv u14_69
  exact c18727 h u12_241 u16_35 u15_84 a99

private theorem c31516 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 7, 9} → Q {1, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a274 a258 a304
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1760 h a258 hv
  have u3_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26583 h hv u1_1 u2_118
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u6_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22521 h hv u5_63 u4_109 u2_118
  have u7_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9779 h hv u5_63 u4_109 u2_118
  have u8_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c20983 h a258 u0_9 hv
  have u9_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u1_1 u4_109
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u1_1 hv
  have u11_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1252 h a274 hv
  have u12_3 : T {0, 1, 4} := by
    by_contra hv
    exact c23222 h a274 hv u10_112
  have u13_5 : T {0, 1, 6} := by
    by_contra hv
    exact c23226 h a274 hv u8_103
  have u14_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17621 h hv u11_84 u4_109 u2_118
  have u15_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28423 h hv u1_1 u12_3 u13_5
  have u16_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c27427 h a304 u13_5 hv
  have u17_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28143 h hv u1_1 u12_3 u13_5
  have u18_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u7_177 u14_233 u6_268 u3_298 u9_307 u17_309 u15_311
  exact c21120 h a258 u16_78 u18_93 u8_103

theorem c31517 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a258 a304
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u3_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u2_1 u4_109
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u2_1 hv
  have u7_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u8_63 : T {1, 7, 9} := by
    by_contra hv
    exact c943 h a258 hv
  have u9_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1760 h a258 hv
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c20983 h a258 u0_9 hv
  have u11_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9779 h hv u8_63 u4_109 u9_118
  have u12_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22521 h hv u8_63 u4_109 u9_118
  have u13_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26583 h hv u2_1 u9_118
  have u14_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u1_121 u4_109 u9_118 hv
  have u15_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u1_121 u4_109 hv u9_118
  have u16_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u14_120
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1719 h hv u15_115
  have u18_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31514 h h0 hv u14_120 a258 u7_99
  have u19_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c31516 h h0 hv a258 a304
  have u20_183 : Q {0, 3, 7, 9} := by
    by_contra hv
    exact c31288 h u17_310 hv u16_315 u19_274 u3_313 u7_99 u18_239
  have u21_35 : T {0, 7, 9} := by
    by_contra hv
    exact c517 h u20_183 hv
  have u22_38 : T {1, 2, 4} := by
    by_contra hv
    exact c10482 h u20_183 hv u6_112
  have u23_40 : T {1, 2, 6} := by
    by_contra hv
    exact c10486 h u20_183 hv u10_103
  have u24_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17619 h hv u21_35 u4_109 u9_118
  have u25_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28463 h hv u2_1 u22_38 u23_40
  have u26_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c27439 h a304 hv u23_40
  have u27_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28183 h hv u2_1 u22_38 u23_40
  have u28_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv u11_177 u24_233 u12_268 u13_298 u5_307 u27_309 u25_311
  exact c21118 h a258 u26_29 u28_93 u10_103

theorem c31518 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 7, 9} → T {6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a183 a118 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u4_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u5_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u6_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31517 h h0 hv a304
  have u7_202 : Q {0, 6, 7, 9} := by
    by_contra hv
    exact c31500 h h0 u6_258 u5_313 a118 hv
  have u8_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1759 h u7_202 u6_258 hv u5_313 u2_323 u3_327 u4_330
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1807 h u1_121 hv a118
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u11_38 : T {1, 2, 4} := by
    by_contra hv
    exact c10482 h a183 hv u10_112
  have u12_40 : T {1, 2, 6} := by
    by_contra hv
    exact c10486 h a183 hv u9_103
  have u13_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c13145 h u7_202 u11_38 hv
  have u14_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c27439 h a304 hv u12_40
  exact c26018 h u8_293 u14_29 u13_93 u9_103

theorem c31519 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 7, 9} → T {6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a274 a118 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u3_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u4_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u5_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u6_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31517 h h0 hv a304
  have u7_202 : Q {0, 6, 7, 9} := by
    by_contra hv
    exact c31500 h h0 u6_258 u5_313 a118 hv
  have u8_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1759 h u7_202 u6_258 hv u5_313 u2_323 u3_327 u4_330
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1807 h u1_121 hv a118
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u11_3 : T {0, 1, 4} := by
    by_contra hv
    exact c23222 h a274 hv u10_112
  have u12_5 : T {0, 1, 6} := by
    by_contra hv
    exact c23226 h a274 hv u9_103
  have u13_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c25885 h u8_293 u11_3 hv
  have u14_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c27427 h a304 u12_5 hv
  exact c13280 h u7_202 u14_78 u13_93 u9_103

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases101
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31520_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a118 a304
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u3_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u4_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u5_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31517 h h0 hv a304
  have u6_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u8_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u9_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1931 h u0_121 u7_109 a118 hv
  have u10_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1927 h u0_121 u7_109 hv a118
  have u11_202 : Q {0, 6, 7, 9} := by
    by_contra hv
    exact c31500 h h0 u5_258 u6_313 a118 hv
  have u12_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u9_120
  have u13_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1719 h hv u10_115
  have u14_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1812 h u0_121 hv u10_115
  have u15_35 : T {0, 7, 9} := by
    by_contra hv
    exact c523 h u11_202 hv
  have u16_293 : Q {2, 6, 7, 9} := by
    by_contra hv
    exact c1759 h u11_202 u5_258 hv u6_313 u3_323 u2_327 u1_330
  have u17_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1258 h u16_293 hv
  have u18_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19435 h hv u15_35 u17_84 u8_99
  have u19_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c31518 h h0 hv a118 a304
  have u20_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c31519 h h0 hv a118 a304
  have u21_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31288 h u13_310 u19_183 u12_315 u20_274 u6_313 u8_99 hv
  have u22_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u21_239 hv
  have u23_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h u21_239 hv
  have u24_63 : T {1, 7, 9} := by
    by_contra hv
    exact c937 h u21_239 hv
  have u25_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11495 h hv u4_37 u22_47 u23_49
  have u26_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27135 h hv u15_35 u24_63 u17_84
  exact c31307 h h0 u18_246 u14_106 u26_301 u25_190

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31520_oai := @OAI.BorsukNine.FiniteObstruction.c31520_oai
