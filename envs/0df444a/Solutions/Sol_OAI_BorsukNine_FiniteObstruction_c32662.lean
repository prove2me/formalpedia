-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32662
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:22:46.077518+00:00
-- url     : https://prove2.me/submissions/318e7dd9-3f63-4bdc-8409-8e1889f47483

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c1390
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31481
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31520
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31524
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32582
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32601
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32606
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32611
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32621
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32629
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32630

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

theorem c50 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ T {0, 1, 5} → False := by
  intro a129 n4
  exact n4 (h.down {0, 1, 3, 5} {0, 1, 5} a129 (by decide) (by decide))

theorem c67 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ T {0, 1, 6} → False := by
  intro a135 n5
  exact n5 (h.down {0, 1, 4, 6} {0, 1, 6} a135 (by decide) (by decide))

theorem c81 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 1, 7, 9} → False := by
  intro a131 n125 n136 n140 n143 n146 n147
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 7} {0, 1, 7} a131 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n140 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n143 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 7} = {0, 1, 7, 8} by decide)) hS)
  · exact n147 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 7} = {0, 1, 7, 9} by decide)) hS)

theorem c95 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → ¬ T {0, 1, 8} → False := by
  intro a132 n7
  exact n7 (h.down {0, 1, 3, 8} {0, 1, 8} a132 (by decide) (by decide))

theorem c108 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {0, 1, 9} → False := by
  intro a127 n8
  exact n8 (h.down {0, 1, 2, 9} {0, 1, 9} a127 (by decide) (by decide))

theorem c123 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 2, 3} → False := by
  intro a121 n9
  exact n9 (h.down {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide))

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

theorem c172 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {0, 2, 6} → False := by
  intro a156 n12
  exact n12 (h.down {0, 2, 4, 6} {0, 2, 6} a156 (by decide) (by decide))

theorem c213 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {0, 2, 9} → False := by
  intro a127 n15
  exact n15 (h.down {0, 1, 2, 9} {0, 2, 9} a127 (by decide) (by decide))

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

theorem c227 (h : TenSystem T Q) :
    T {0, 3, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 4, 9} → False := by
  intro a16 n128 n149 n170 n171 n172 n173 n174
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 4} a16
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact n149 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 4} = {0, 3, 4, 5} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 4} = {0, 3, 4, 6} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 4} = {0, 3, 4, 7} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 4} = {0, 3, 4, 8} by decide)) hS)
  · exact n174 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 4} = {0, 3, 4, 9} by decide)) hS)

theorem c253 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {0, 3, 5} → False := by
  intro a177 n17
  exact n17 (h.down {0, 3, 5, 8} {0, 3, 5} a177 (by decide) (by decide))

theorem c285 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 7} → False := by
  intro a183 n19
  exact n19 (h.down {0, 3, 7, 9} {0, 3, 7} a183 (by decide) (by decide))

theorem c294 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {0, 3, 8} → False := by
  intro a177 n20
  exact n20 (h.down {0, 3, 5, 8} {0, 3, 8} a177 (by decide) (by decide))

theorem c296 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {0, 3, 8} → False := by
  intro a180 n20
  exact n20 (h.down {0, 3, 6, 8} {0, 3, 8} a180 (by decide) (by decide))

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

theorem c313 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 9} → False := by
  intro a183 n21
  exact n21 (h.down {0, 3, 7, 9} {0, 3, 9} a183 (by decide) (by decide))

theorem c332 (h : TenSystem T Q) :
    T {0, 4, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a23 n135 n156 n171 n185 n189 n190 n191
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 6} a23
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c340 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a185 n135 n156 n171 n189 n190 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 6} {0, 4, 6} a185 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c344 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 9} → False := by
  intro a190 n135 n156 n171 n185 n189 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {0, 4, 6} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c348 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {0, 4, 7} → False := by
  intro a136 n24
  exact n24 (h.down {0, 1, 4, 7} {0, 4, 7} a136 (by decide) (by decide))

theorem c350 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {0, 4, 7} → False := by
  intro a157 n24
  exact n24 (h.down {0, 2, 4, 7} {0, 4, 7} a157 (by decide) (by decide))

theorem c352 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {0, 4, 7} → False := by
  intro a172 n24
  exact n24 (h.down {0, 3, 4, 7} {0, 4, 7} a172 (by decide) (by decide))

theorem c356 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {0, 4, 7} → False := by
  intro a189 n24
  exact n24 (h.down {0, 4, 6, 7} {0, 4, 7} a189 (by decide) (by decide))

theorem c360 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {0, 4, 7} → False := by
  intro a193 n24
  exact n24 (h.down {0, 4, 7, 9} {0, 4, 7} a193 (by decide) (by decide))

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

theorem c403 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {0, 5, 6} → False := by
  intro a196 n27
  exact n27 (h.down {0, 5, 6, 8} {0, 5, 6} a196 (by decide) (by decide))

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

theorem c427 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {0, 5, 8} → False := by
  intro a177 n29
  exact n29 (h.down {0, 3, 5, 8} {0, 5, 8} a177 (by decide) (by decide))

theorem c431 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {0, 5, 8} → False := by
  intro a196 n29
  exact n29 (h.down {0, 5, 6, 8} {0, 5, 8} a196 (by decide) (by decide))

theorem c432 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a196 n141 n162 n177 n187 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 8} {0, 5, 8} a196 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c435 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {0, 5, 8} → False := by
  intro a200 n29
  exact n29 (h.down {0, 5, 8, 9} {0, 5, 8} a200 (by decide) (by decide))

theorem c436 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → False := by
  intro a200 n141 n162 n177 n187 n196 n198
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 8, 9} {0, 5, 8} a200 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c450 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {0, 5, 9} → False := by
  intro a200 n30
  exact n30 (h.down {0, 5, 8, 9} {0, 5, 9} a200 (by decide) (by decide))

theorem c459 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {0, 6, 7} → False := by
  intro a189 n31
  exact n31 (h.down {0, 4, 6, 7} {0, 6, 7} a189 (by decide) (by decide))

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

theorem c476 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {0, 6, 8} → False := by
  intro a196 n32
  exact n32 (h.down {0, 5, 6, 8} {0, 6, 8} a196 (by decide) (by decide))

theorem c481 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → False := by
  intro a203 n144 n165 n180 n190 n196 n201
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {0, 6, 8} a203 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c482 (h : TenSystem T Q) :
    T {0, 6, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {0, 6, 8, 9} → False := by
  intro a33 n145 n166 n181 n191 n197 n202 n203
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 6, 9} a33
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n145 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n202 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact n203 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c485 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {0, 6, 9} → False := by
  intro a166 n33
  exact n33 (h.down {0, 2, 6, 9} {0, 6, 9} a166 (by decide) (by decide))

theorem c494 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 6, 8, 9} → False := by
  intro a202 n145 n166 n181 n191 n197 n203
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 7, 9} {0, 6, 9} a202 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n145 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 9} = {0, 6, 8, 9} by decide)) hS)
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

theorem c560 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {1, 2, 4} → False := by
  intro a205 n38
  exact n38 (h.down {1, 2, 3, 4} {1, 2, 4} a205 (by decide) (by decide))

theorem c570 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ T {1, 2, 4} → False := by
  intro a215 n38
  exact n38 (h.down {1, 2, 4, 9} {1, 2, 4} a215 (by decide) (by decide))

theorem c579 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 5} → False := by
  intro a216 n39
  exact n39 (h.down {1, 2, 5, 6} {1, 2, 5} a216 (by decide) (by decide))

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

theorem c585 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {1, 2, 5} → False := by
  intro a219 n39
  exact n39 (h.down {1, 2, 5, 9} {1, 2, 5} a219 (by decide) (by decide))

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

theorem c588 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {1, 2, 6} → False := by
  intro a124 n40
  exact n40 (h.down {0, 1, 2, 6} {1, 2, 6} a124 (by decide) (by decide))

theorem c590 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {1, 2, 6} → False := by
  intro a207 n40
  exact n40 (h.down {1, 2, 3, 6} {1, 2, 6} a207 (by decide) (by decide))

theorem c592 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ T {1, 2, 6} → False := by
  intro a212 n40
  exact n40 (h.down {1, 2, 4, 6} {1, 2, 6} a212 (by decide) (by decide))

theorem c594 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 6} → False := by
  intro a216 n40
  exact n40 (h.down {1, 2, 5, 6} {1, 2, 6} a216 (by decide) (by decide))

theorem c595 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a216 n124 n207 n212 n220 n221 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 6} {1, 2, 6} a216 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hne (by decide)
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

theorem c600 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {1, 2, 6} → False := by
  intro a222 n40
  exact n40 (h.down {1, 2, 6, 9} {1, 2, 6} a222 (by decide) (by decide))

theorem c603 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {1, 2, 7} → False := by
  intro a125 n41
  exact n41 (h.down {0, 1, 2, 7} {1, 2, 7} a125 (by decide) (by decide))

theorem c605 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {1, 2, 7} → False := by
  intro a208 n41
  exact n41 (h.down {1, 2, 3, 7} {1, 2, 7} a208 (by decide) (by decide))

theorem c607 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {1, 2, 7} → False := by
  intro a213 n41
  exact n41 (h.down {1, 2, 4, 7} {1, 2, 7} a213 (by decide) (by decide))

theorem c615 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 7} → False := by
  intro a224 n41
  exact n41 (h.down {1, 2, 7, 9} {1, 2, 7} a224 (by decide) (by decide))

theorem c626 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ T {1, 2, 8} → False := by
  intro a221 n42
  exact n42 (h.down {1, 2, 6, 8} {1, 2, 8} a221 (by decide) (by decide))

theorem c630 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {1, 2, 8} → False := by
  intro a225 n42
  exact n42 (h.down {1, 2, 8, 9} {1, 2, 8} a225 (by decide) (by decide))

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

theorem c635 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 2, 9} → False := by
  intro a210 n43
  exact n43 (h.down {1, 2, 3, 9} {1, 2, 9} a210 (by decide) (by decide))

theorem c636 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a210 n127 n215 n219 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 9} {1, 2, 9} a210 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c641 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {1, 2, 9} → False := by
  intro a222 n43
  exact n43 (h.down {1, 2, 6, 9} {1, 2, 9} a222 (by decide) (by decide))

theorem c643 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 9} → False := by
  intro a224 n43
  exact n43 (h.down {1, 2, 7, 9} {1, 2, 9} a224 (by decide) (by decide))

theorem c648 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {1, 3, 4} → False := by
  intro a128 n44
  exact n44 (h.down {0, 1, 3, 4} {1, 3, 4} a128 (by decide) (by decide))

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

theorem c656 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {1, 3, 4} → False := by
  intro a228 n44
  exact n44 (h.down {1, 3, 4, 7} {1, 3, 4} a228 (by decide) (by decide))

theorem c701 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {1, 3, 7} → False := by
  intro a235 n47
  exact n47 (h.down {1, 3, 6, 7} {1, 3, 7} a235 (by decide) (by decide))

theorem c716 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {1, 3, 8} → False := by
  intro a236 n48
  exact n48 (h.down {1, 3, 6, 8} {1, 3, 8} a236 (by decide) (by decide))

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

theorem c731 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 3, 9} → False := by
  intro a237 n49
  exact n49 (h.down {1, 3, 6, 9} {1, 3, 9} a237 (by decide) (by decide))

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

theorem c780 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {1, 4, 7} → False := by
  intro a249 n52
  exact n52 (h.down {1, 4, 7, 9} {1, 4, 7} a249 (by decide) (by decide))

theorem c824 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 9} → False := by
  intro a252 n139 n216 n231 n241 n251 n253
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 8} {1, 5, 6} a252 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n139 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 6} = {1, 5, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 6} = {1, 5, 6, 9} by decide)) hS)

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

theorem c843 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {1, 5, 8} → False := by
  intro a141 n57
  exact n57 (h.down {0, 1, 5, 8} {1, 5, 8} a141 (by decide) (by decide))

theorem c851 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {1, 5, 8} → False := by
  intro a252 n57
  exact n57 (h.down {1, 5, 6, 8} {1, 5, 8} a252 (by decide) (by decide))

theorem c855 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {1, 5, 8} → False := by
  intro a256 n57
  exact n57 (h.down {1, 5, 8, 9} {1, 5, 8} a256 (by decide) (by decide))

theorem c860 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {1, 5, 9} → False := by
  intro a219 n58
  exact n58 (h.down {1, 2, 5, 9} {1, 5, 9} a219 (by decide) (by decide))

theorem c866 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {1, 5, 9} → False := by
  intro a253 n58
  exact n58 (h.down {1, 5, 6, 9} {1, 5, 9} a253 (by decide) (by decide))

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

theorem c931 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ Q {0, 1, 7, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 6, 7, 8} → False := by
  intro a260 n146 n223 n238 n248 n254 n257
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 7, 8, 9} {1, 7, 8} a260 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c934 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a147 n224 n239 n249 n255 n258 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 7, 9} {1, 7, 9} a147 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c939 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a249 n63
  exact n63 (h.down {1, 4, 7, 9} {1, 7, 9} a249 (by decide) (by decide))

theorem c950 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a225 n64
  exact n64 (h.down {1, 2, 8, 9} {1, 8, 9} a225 (by decide) (by decide))

theorem c958 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a259 n64
  exact n64 (h.down {1, 6, 8, 9} {1, 8, 9} a259 (by decide) (by decide))

theorem c969 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {2, 3, 4} → False := by
  intro a262 n65
  exact n65 (h.down {2, 3, 4, 6} {2, 3, 4} a262 (by decide) (by decide))

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

theorem c1006 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → ¬ Q {0, 2, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 3, 6, 8} → False := by
  intro a272 n151 n207 n262 n266 n270 n271
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 6, 9} {2, 3, 6} a272 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n151 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact n207 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 6} = {2, 3, 6, 7} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 6} = {2, 3, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1012 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {2, 3, 7} → False := by
  intro a263 n68
  exact n68 (h.down {2, 3, 4, 7} {2, 3, 7} a263 (by decide) (by decide))

theorem c1016 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {2, 3, 7} → False := by
  intro a270 n68
  exact n68 (h.down {2, 3, 6, 7} {2, 3, 7} a270 (by decide) (by decide))

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

theorem c1076 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {2, 4, 6} → False := by
  intro a280 n72
  exact n72 (h.down {2, 4, 6, 7} {2, 4, 6} a280 (by decide) (by decide))

theorem c1082 (h : TenSystem T Q) :
    T {2, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 7, 8} → ¬ Q {2, 4, 7, 9} → False := by
  intro a73 n157 n213 n263 n277 n280 n283 n284
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 7} a73
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n157 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n283 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 7} = {2, 4, 7, 8} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 7} = {2, 4, 7, 9} by decide)) hS)

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

theorem c1139 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ Q {0, 2, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 5, 6, 9} → False := by
  intro a287 n160 n216 n266 n276 n286 n288
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 8} {2, 5, 6} a287 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n160 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n286 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 6} = {2, 5, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 6} = {2, 5, 6, 9} by decide)) hS)

theorem c1166 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {2, 5, 8} → False := by
  intro a287 n78
  exact n78 (h.down {2, 5, 6, 8} {2, 5, 8} a287 (by decide) (by decide))

theorem c1170 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {2, 5, 8} → False := by
  intro a291 n78
  exact n78 (h.down {2, 5, 8, 9} {2, 5, 8} a291 (by decide) (by decide))

theorem c1171 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 7, 8} → False := by
  intro a291 n162 n218 n268 n278 n287 n289
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 8, 9} {2, 5, 8} a291 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n162 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n268 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c1218 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {2, 6, 9} → False := by
  intro a166 n82
  exact n82 (h.down {0, 2, 6, 9} {2, 6, 9} a166 (by decide) (by decide))

theorem c1254 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a284 n84
  exact n84 (h.down {2, 4, 7, 9} {2, 7, 9} a284 (by decide) (by decide))

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

theorem c1307 (h : TenSystem T Q) :
    T {3, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 7, 9} → False := by
  intro a88 n172 n228 n263 n297 n300 n303 n304
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 7} a88
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n172 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 7} = {3, 4, 7, 8} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

theorem c1317 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 7, 9} → False := by
  intro a300 n172 n228 n263 n297 n303 n304
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {3, 4, 7} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n172 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 7} = {3, 4, 7, 8} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

theorem c1337 (h : TenSystem T Q) :
    T {3, 4, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a90 n174 n230 n265 n299 n302 n304 n305
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 9} a90
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1343 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a265 n174 n230 n299 n302 n304 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 9} {3, 4, 9} a265 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1346 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 4, 9} → False := by
  intro a302 n90
  exact n90 (h.down {3, 4, 6, 9} {3, 4, 9} a302 (by decide) (by decide))

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

theorem c1383 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {3, 5, 8} → False := by
  intro a177 n93
  exact n93 (h.down {0, 3, 5, 8} {3, 5, 8} a177 (by decide) (by decide))

theorem c1388 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a268 n177 n233 n298 n307 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 5, 8} {3, 5, 8} a268 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1389 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 5, 8} → False := by
  intro a298 n93
  exact n93 (h.down {3, 4, 5, 8} {3, 5, 8} a298 (by decide) (by decide))

theorem c1391 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {3, 5, 8} → False := by
  intro a307 n93
  exact n93 (h.down {3, 5, 6, 8} {3, 5, 8} a307 (by decide) (by decide))

theorem c1392 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a307 n177 n233 n268 n298 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 8} {3, 5, 8} a307 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1393 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {3, 5, 8} → False := by
  intro a309 n93
  exact n93 (h.down {3, 5, 7, 8} {3, 5, 8} a309 (by decide) (by decide))

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

theorem c1396 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → False := by
  intro a311 n177 n233 n268 n298 n307 n309
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c1420 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 7, 9} → False := by
  intro a300 n179 n235 n270 n306 n312 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {3, 6, 7} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
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

theorem c1427 (h : TenSystem T Q) :
    T {3, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a96 n180 n236 n271 n301 n307 n312 n314
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 6, 8} a96
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1435 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a301 n180 n236 n271 n307 n312 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 8} {3, 6, 8} a301 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1437 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a307 n180 n236 n271 n301 n312 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 8} {3, 6, 8} a307 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1454 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a313 n181 n237 n272 n302 n308 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 9} {3, 6, 9} a313 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1478 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a274 n183 n239 n304 n310 n313 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 7, 9} {3, 7, 9} a274 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c1524 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a297 n102
  exact n102 (h.down {3, 4, 5, 7} {4, 5, 7} a297 (by decide) (by decide))

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

theorem c1539 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a298 n103
  exact n103 (h.down {3, 4, 5, 8} {4, 5, 8} a298 (by decide) (by decide))

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

theorem c1567 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a280 n105
  exact n105 (h.down {2, 4, 6, 7} {4, 6, 7} a280 (by decide) (by decide))

theorem c1568 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a280 n189 n245 n300 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {4, 6, 7} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

theorem c1569 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a300 n105
  exact n105 (h.down {3, 4, 6, 7} {4, 6, 7} a300 (by decide) (by decide))

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

theorem c1596 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a247 n191 n282 n302 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 9} {4, 6, 9} a247 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c1614 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a303 n108
  exact n108 (h.down {3, 4, 7, 8} {4, 7, 8} a303 (by decide) (by decide))

theorem c1622 (h : TenSystem T Q) :
    T {4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a109 n193 n249 n284 n304 n320 n323 n325
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 7, 9} a109
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1624 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a193 n249 n284 n304 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 9} {4, 7, 9} a193 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1625 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a249 n109
  exact n109 (h.down {1, 4, 7, 9} {4, 7, 9} a249 (by decide) (by decide))

theorem c1626 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a249 n193 n284 n304 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 7, 9} {4, 7, 9} a249 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1628 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a284 n193 n249 n304 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 7, 9} {4, 7, 9} a284 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
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

theorem c1655 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a251 n111
  exact n111 (h.down {1, 5, 6, 7} {5, 6, 7} a251 (by decide) (by decide))

theorem c1657 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a286 n111
  exact n111 (h.down {2, 5, 6, 7} {5, 6, 7} a286 (by decide) (by decide))

theorem c1667 (h : TenSystem T Q) :
    T {5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a112 n196 n252 n287 n307 n317 n326 n328
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 6, 8} a112
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1668 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a196 n112
  exact n112 (h.down {0, 5, 6, 8} {5, 6, 8} a196 (by decide) (by decide))

theorem c1669 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a196 n252 n287 n307 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 8} {5, 6, 8} a196 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

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

theorem c1673 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a287 n196 n252 n307 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 8} {5, 6, 8} a287 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1675 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a307 n196 n252 n287 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 8} {5, 6, 8} a307 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

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

theorem c1729 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a200 n256 n291 n311 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 8, 9} {5, 8, 9} a200 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

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

theorem c1735 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a311 n200 n256 n291 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {5, 8, 9} a311 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

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

theorem c1761 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a258 n202 n293 n313 n323 n327 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 9} {6, 7, 9} a258 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n202 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n293 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1802 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {7, 8, 9} → False := by
  intro a121 n101 n120
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 6} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n101 (hc.mpr n120)

theorem c1805 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {6, 8, 9} → False := by
  intro a121 a102 a119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a102 a119

theorem c1806 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n103 n118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n103 (hc.mpr n118)

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

theorem c1840 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a121 n102 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c1844 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a121 n105 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
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

theorem c1860 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n107 n109 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

theorem c1869 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 7} → T {5, 6, 8} → T {5, 6, 9} → False := by
  intro a121 a111 a112 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 6} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c1881 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a121 a103 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
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

theorem c1912 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 6, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n107 n113 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

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

theorem c1932 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 7, 9} → ¬ T {6, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n115 n118 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c1943 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {7, 8, 9} → False := by
  intro a122 a91 a120
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 6} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a91 a120

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

theorem c2221 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {4, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a123 a110 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {8, 9} {4, 6, 7} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c2233 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 5, 8} → T {4, 7, 9} → False := by
  intro a124 a93 a109
  have hc := h.complementary {0, 1, 2, 6} {3, 5, 8} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a109

theorem c2369 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 9} → T {5, 6, 8} → False := by
  intro a125 a90 a112
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 9} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a90 a112

theorem c2515 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 5, 9} → T {4, 6, 7} → False := by
  intro a126 a94 a105
  have hc := h.complementary {0, 1, 2, 8} {3, 5, 9} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a94 a105

theorem c2647 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 7} → T {5, 6, 8} → False := by
  intro a127 a88 a112
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a88 a112

theorem c2654 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a127 n93 n105
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n105)

theorem c2655 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 8} → T {4, 6, 7} → False := by
  intro a127 a93 a105
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a93 a105

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

theorem c2861 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a128 a78 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 4} {5, 8} {2, 6, 9} a128 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c3072 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a130 n78 n109
  have hc := h.complementary {0, 1, 3, 6} {2, 5, 8} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n78 (hc.mpr n109)

theorem c3219 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 6, 9} → T {4, 5, 8} → False := by
  intro a131 a82 a103
  have hc := h.complementary {0, 1, 3, 7} {2, 6, 9} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a82 a103

theorem c3304 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ T {2, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a131 n78 n103 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 3, 7} {5, 8} {2, 4, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c4326 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {2, 3, 8} → ¬ T {4, 7, 9} → False := by
  intro a139 n69 n109
  have hc := h.complementary {0, 1, 5, 6} {2, 3, 8} a139 (by decide) (by decide)
  have he : ( {0, 1, 5, 6} : Finset Labels)ᶜ \ {2, 3, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n69 (hc.mpr n109)

theorem c4471 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 4, 6} → T {3, 8, 9} → False := by
  intro a140 a72 a100
  have hc := h.complementary {0, 1, 5, 7} {2, 4, 6} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a100

theorem c4708 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a141 n88 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {4, 7} {3, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c4882 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → ¬ T {2, 3, 4} → ¬ T {5, 8, 9} → False := by
  intro a143 n65 n116
  have hc := h.complementary {0, 1, 6, 7} {2, 3, 4} a143 (by decide) (by decide)
  have he : ( {0, 1, 6, 7} : Finset Labels)ᶜ \ {2, 3, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n65 (hc.mpr n116)

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

theorem c5024 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {2, 3, 5} → ¬ T {4, 7, 9} → False := by
  intro a144 n66 n109
  have hc := h.complementary {0, 1, 6, 8} {2, 3, 5} a144 (by decide) (by decide)
  have he : ( {0, 1, 6, 8} : Finset Labels)ᶜ \ {2, 3, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n66 (hc.mpr n109)

theorem c5173 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 4, 7} → T {3, 5, 8} → False := by
  intro a145 a73 a93
  have hc := h.complementary {0, 1, 6, 9} {2, 4, 7} a145 (by decide) (by decide)
  have he : ( {0, 1, 6, 9} : Finset Labels)ᶜ \ {2, 4, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a73 a93

theorem c5179 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 5, 8} → T {3, 4, 7} → False := by
  intro a145 a78 a88
  have hc := h.complementary {0, 1, 6, 9} {2, 5, 8} a145 (by decide) (by decide)
  have he : ( {0, 1, 6, 9} : Finset Labels)ᶜ \ {2, 5, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a78 a88

theorem c5292 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a145 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 9} {5, 8} {3, 4, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c5313 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → T {2, 4, 6} → T {3, 5, 9} → False := by
  intro a146 a72 a94
  have hc := h.complementary {0, 1, 7, 8} {2, 4, 6} a146 (by decide) (by decide)
  have he : ( {0, 1, 7, 8} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a94

theorem c5801 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a149 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 4} {5, 8} {1, 6, 9} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c6004 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a151 n52 n116
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 7} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n116)

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

theorem c6434 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a154 n57 n105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n105)

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

theorem c7266 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {1, 3, 8} → ¬ T {4, 7, 9} → False := by
  intro a160 n48 n109
  have hc := h.complementary {0, 2, 5, 6} {1, 3, 8} a160 (by decide) (by decide)
  have he : ( {0, 2, 5, 6} : Finset Labels)ᶜ \ {1, 3, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n48 (hc.mpr n109)

theorem c7548 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 3, 9} → ¬ T {4, 6, 7} → False := by
  intro a162 n49 n105
  have hc := h.complementary {0, 2, 5, 8} {1, 3, 9} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n105)

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

theorem c7964 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ T {1, 3, 5} → ¬ T {4, 7, 9} → False := by
  intro a165 n45 n109
  have hc := h.complementary {0, 2, 6, 8} {1, 3, 5} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 3, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n109)

theorem c8113 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 4, 7} → T {3, 5, 8} → False := by
  intro a166 a52 a93
  have hc := h.complementary {0, 2, 6, 9} {1, 4, 7} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a93

theorem c8232 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {5, 8} {3, 4, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

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

theorem c8664 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {1, 2, 7} → ¬ T {6, 8, 9} → False := by
  intro a170 n41 n119
  have hc := h.complementary {0, 3, 4, 5} {1, 2, 7} a170 (by decide) (by decide)
  have he : ( {0, 3, 4, 5} : Finset Labels)ᶜ \ {1, 2, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n119)

theorem c8905 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a171 a57 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {5, 8} {1, 2, 9} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c8944 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 2, 6} → ¬ T {5, 8, 9} → False := by
  intro a172 n40 n116
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 6} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n116)

theorem c8945 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 2, 6} → T {5, 8, 9} → False := by
  intro a172 a40 a116
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 6} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a116

theorem c9086 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {1, 2, 7} → ¬ T {5, 6, 9} → False := by
  intro a173 n41 n113
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 7} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n113)

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

theorem c9224 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 6} → ¬ T {5, 7, 8} → False := by
  intro a174 n40 n114
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 6} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n114)

theorem c9330 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a174 n57 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {5, 8} {1, 2, 6} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c9644 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 6} → ¬ T {4, 7, 9} → False := by
  intro a177 n40 n109
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 6} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n109)

theorem c9645 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 6} → T {4, 7, 9} → False := by
  intro a177 a40 a109
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 6} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a109

theorem c9648 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 9} → ¬ T {4, 6, 7} → False := by
  intro a177 n43 n105
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 9} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n105)

theorem c9649 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 9} → T {4, 6, 7} → False := by
  intro a177 a43 a105
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 9} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a43 a105

theorem c9665 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 4} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a177 a38 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {1, 2} {4, 6, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c9773 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {2, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a177 a82 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {6, 9} {2, 4, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c9793 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → T {1, 4, 7} → T {2, 6, 8} → False := by
  intro a178 a52 a81
  have hc := h.complementary {0, 3, 5, 9} {1, 4, 7} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a81

theorem c9922 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {1, 2, 4} → ¬ T {5, 8, 9} → False := by
  intro a179 n38 n116
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 4} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n116)

theorem c10206 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 7} → ¬ T {4, 5, 8} → False := by
  intro a181 n41 n103
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n103)

theorem c10213 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 4, 7} → T {2, 5, 8} → False := by
  intro a181 a52 a78
  have hc := h.complementary {0, 3, 6, 9} {1, 4, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a78

theorem c10219 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 5, 8} → T {2, 4, 7} → False := by
  intro a181 a57 a73
  have hc := h.complementary {0, 3, 6, 9} {1, 5, 8} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a73

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

theorem c10608 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a183 n57 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 7, 9} {5, 8} {1, 2, 6} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c10635 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 7} → T {2, 5, 6} → False := by
  intro a184 a52 a76
  have hc := h.complementary {0, 3, 8, 9} {1, 4, 7} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a52 a76

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

theorem c11065 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a187 a37 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 2} {3, 6, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11153 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 7, 9} → False := by
  intro a187 a49 a70 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {3, 9} {1, 2, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

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

theorem c11463 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {5, 7, 9} → False := by
  intro a190 a37 a115
  have hc := h.complementary {0, 4, 6, 8} {1, 2, 3} a190 (by decide) (by decide)
  have he : ( {0, 4, 6, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a115

theorem c11485 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a190 a37 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 2} {3, 5, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11606 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {1, 2, 7} → ¬ T {3, 5, 8} → False := by
  intro a191 n41 n93
  have hc := h.complementary {0, 4, 6, 9} {1, 2, 7} a191 (by decide) (by decide)
  have he : ( {0, 4, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n93)

theorem c11727 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a191 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 9} {5, 8} {1, 2, 3} a191 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

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

theorem c12007 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a193 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {5, 8} {1, 2, 3} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c12309 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 9} → T {3, 4, 7} → False := by
  intro a196 a43 a88
  have hc := h.complementary {0, 5, 6, 8} {1, 2, 9} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a43 a88

theorem c12310 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {2, 7, 9} → False := by
  intro a196 n44 n84
  have hc := h.complementary {0, 5, 6, 8} {1, 3, 4} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 3, 4} = {2, 7, 9} := by decide
  rw [he] at hc
  exact n44 (hc.mpr n84)

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

theorem c12311 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 4} → T {2, 7, 9} → False := by
  intro a196 a44 a84
  have hc := h.complementary {0, 5, 6, 8} {1, 3, 4} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 3, 4} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a44 a84

theorem c12317 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 4, 7} → T {2, 3, 9} → False := by
  intro a196 a52 a70
  have hc := h.complementary {0, 5, 6, 8} {1, 4, 7} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a52 a70

theorem c12331 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 7} → False := by
  intro a196 a37 a44 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 3} {2, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12336 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {1, 3, 7} → ¬ T {1, 3, 9} → False := by
  intro a196 n44 n47 n49
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 3} {4, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) ht)

theorem c12338 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → ¬ T {1, 3, 4} → ¬ T {1, 4, 7} → False := by
  intro a196 n38 n44 n52
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 4} {2, 3, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) ht)
  · exact n44 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) ht)

theorem c12341 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 4} → T {1, 3, 4} → T {1, 4, 9} → False := by
  intro a196 a38 a44 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 4} {2, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c12354 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 4, 9} → False := by
  intro a196 n43 n49 n54
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 9} {2, 3, 4} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n54 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) ht)

theorem c12375 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 4} → T {2, 4, 7} → T {2, 4, 9} → False := by
  intro a196 a38 a73 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 4} {1, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) a75)

theorem c12380 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 7, 9} → False := by
  intro a196 n41 n68 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 7} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c12390 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 7, 9} → False := by
  intro a196 n43 n75 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 9} {1, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) ht)

theorem c12396 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a196 n44 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {3, 4} {1, 2, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

theorem c12399 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 4} → T {3, 4, 7} → T {3, 4, 9} → False := by
  intro a196 a44 a88 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {3, 4} {1, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c12443 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 2, 3} → T {4, 7, 8} → False := by
  intro a197 a37 a108
  have hc := h.complementary {0, 5, 6, 9} {1, 2, 3} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a108

theorem c12559 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a197 a52 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 9} {4, 7} {1, 2, 3} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c12583 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {4, 6, 9} → False := by
  intro a198 a37 a107
  have hc := h.complementary {0, 5, 7, 8} {1, 2, 3} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a107

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

theorem c12607 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a198 a37 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 2} {3, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c12635 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 9} → T {1, 3, 9} → T {1, 4, 9} → False := by
  intro a198 a43 a49 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 9} {2, 3, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)

theorem c12691 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 4, 9} → False := by
  intro a198 a49 a70 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {3, 9} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)

theorem c12710 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 4, 9} → ¬ T {3, 4, 9} → ¬ T {4, 6, 9} → False := by
  intro a198 n54 n90 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {4, 9} {1, 3, 6} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n54 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)

theorem c12867 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {3, 4, 7} → False := by
  intro a200 a40 a88
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 6} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a40 a88

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

theorem c13027 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a201 a37 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 2} {3, 5, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c13275 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a202 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 9} {5, 8} {1, 2, 3} a202 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c13283 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 3} → T {4, 5, 7} → False := by
  intro a203 a37 a102
  have hc := h.complementary {0, 6, 8, 9} {1, 2, 3} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a102

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

theorem c13407 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a203 a52 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {4, 7} {1, 2, 3} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c13641 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a205 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 4} {5, 8} {0, 6, 9} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c13772 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a206 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 5} {4, 7} {0, 6, 9} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c13844 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a207 n24 n116
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n116)

theorem c13852 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a207 n29 n109
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 8} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n109)

theorem c13853 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 5, 8} → T {4, 7, 9} → False := by
  intro a207 a29 a109
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 8} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a109

theorem c13855 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 5, 9} → T {4, 7, 8} → False := by
  intro a207 a30 a108
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 9} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a30 a108

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

theorem c14087 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a208 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {5, 8} {0, 6, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c14202 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a209 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 7} {0, 6, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c14264 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a210 n23 n114
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n114)

theorem c14266 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 7} → ¬ T {5, 6, 8} → False := by
  intro a210 n24 n112
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n112)

theorem c14267 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {5, 6, 8} → False := by
  intro a210 a24 a112
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a112

theorem c14271 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 6} → T {4, 7, 8} → False := by
  intro a210 a27 a108
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a108

theorem c14274 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a210 n29 n105
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n105)

theorem c14275 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 8} → T {4, 6, 7} → False := by
  intro a210 a29 a105
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a105

theorem c14277 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 6, 7} → T {4, 5, 8} → False := by
  intro a210 a31 a103
  have hc := h.complementary {1, 2, 3, 9} {0, 6, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a31 a103

theorem c14279 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 6, 8} → T {4, 5, 7} → False := by
  intro a210 a32 a102
  have hc := h.complementary {1, 2, 3, 9} {0, 6, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a32 a102

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

theorem c14331 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a210 a23 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 6} {0, 5, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c14338 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 7} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → False := by
  intro a210 n24 n102 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {4, 7} {0, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c14339 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 6, 7} → False := by
  intro a210 a24 a102 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 7} {0, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c14342 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → False := by
  intro a210 n24 n105 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {4, 7} {0, 6, 8} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)

theorem c14343 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 8} → False := by
  intro a210 a24 a105 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 7} {0, 6, 8} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c14370 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a210 n29 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {5, 8} {0, 4, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c14373 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a210 a29 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {5, 8} {0, 4, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c14645 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {0, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → False := by
  intro a212 a29 a93 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 6} {5, 8} {0, 3, 9} a212 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c15071 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 5, 8} → T {3, 5, 8} → T {5, 6, 8} → False := by
  intro a215 a29 a93 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 9} {5, 8} {0, 3, 6} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c15077 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {3, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a215 a93 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 9} {5, 8} {3, 6, 7} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

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

theorem c15510 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → ¬ T {0, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a218 n33 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 8} {6, 9} {0, 4, 7} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n33 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c15529 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 3, 8} → T {4, 6, 7} → False := by
  intro a219 a20 a105
  have hc := h.complementary {1, 2, 5, 9} {0, 3, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a20 a105

theorem c15532 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 7} → ¬ T {3, 6, 8} → False := by
  intro a219 n24 n96
  have hc := h.complementary {1, 2, 5, 9} {0, 4, 7} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n96)

theorem c15538 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 6, 8} → ¬ T {3, 4, 7} → False := by
  intro a219 n32 n88
  have hc := h.complementary {1, 2, 5, 9} {0, 6, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n88)

theorem c15622 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a219 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 9} {4, 7} {0, 3, 6} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c15781 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → False := by
  intro a220 a29 a93 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 7} {5, 8} {0, 3, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c15888 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ T {0, 3, 9} → ¬ T {3, 4, 9} → ¬ T {3, 7, 9} → False := by
  intro a221 n21 n90 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 8} {3, 9} {0, 4, 7} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c15945 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 3, 5} → T {4, 7, 8} → False := by
  intro a222 a17 a108
  have hc := h.complementary {1, 2, 6, 9} {0, 3, 5} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a17 a108

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

theorem c16097 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → T {0, 5, 6} → T {3, 4, 9} → False := by
  intro a223 a27 a90
  have hc := h.complementary {1, 2, 7, 8} {0, 5, 6} a223 (by decide) (by decide)
  have he : ( {1, 2, 7, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a90

theorem c16349 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 5, 8} → T {3, 5, 8} → T {5, 6, 8} → False := by
  intro a224 a29 a93 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {5, 8} {0, 3, 6} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c16365 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 3, 5} → T {4, 6, 7} → False := by
  intro a225 a17 a105
  have hc := h.complementary {1, 2, 8, 9} {0, 3, 5} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a17 a105

theorem c16368 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 3, 7} → ¬ T {4, 5, 6} → False := by
  intro a225 n19 n101
  have hc := h.complementary {1, 2, 8, 9} {0, 3, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n101)

theorem c16369 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 3, 7} → T {4, 5, 6} → False := by
  intro a225 a19 a101
  have hc := h.complementary {1, 2, 8, 9} {0, 3, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a19 a101

theorem c16374 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 5, 6} → False := by
  intro a225 n24 n91
  have hc := h.complementary {1, 2, 8, 9} {0, 4, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n91)

theorem c16376 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 5, 6} → ¬ T {3, 4, 7} → False := by
  intro a225 n27 n88
  have hc := h.complementary {1, 2, 8, 9} {0, 5, 6} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n88)

theorem c16384 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 3, 4} → ¬ T {0, 3, 5} → ¬ T {0, 3, 7} → False := by
  intro a225 n16 n17 n19
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {0, 3} {4, 5, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) ht)
  · exact n19 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) ht)

theorem c16388 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 3, 5} → ¬ T {0, 3, 6} → ¬ T {0, 3, 7} → False := by
  intro a225 n17 n18 n19
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {0, 3} {5, 6, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) ht)
  · exact n19 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) ht)

theorem c16472 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a225 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {4, 7} {0, 3, 6} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

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

theorem c16886 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a228 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 7} {5, 8} {0, 6, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c16887 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a228 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {5, 8} {0, 6, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c17298 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a231 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 6} {4, 7} {0, 8, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c17426 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 6, 9} → False := by
  intro a232 n15 n75 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 7} {2, 9} {0, 4, 6} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c17579 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a233 a23 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 7, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c17586 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a233 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {4, 7} {0, 6, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

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

theorem c17587 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a233 a24 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 7} {0, 6, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c17602 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a233 n31 n105 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {6, 7} {0, 4, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c17611 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a233 a33 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {6, 9} {0, 4, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

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

theorem c18268 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 6, 9} → False := by
  intro a238 n15 n75 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 8} {2, 9} {0, 4, 6} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

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

theorem c18603 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {7, 8, 9} → False := by
  intro a241 a9 a120
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 3} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a120

theorem c18757 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 6, 8} → T {2, 3, 9} → False := by
  intro a242 a32 a70
  have hc := h.complementary {1, 4, 5, 7} {0, 6, 8} a242 (by decide) (by decide)
  have he : ( {1, 4, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a70

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

theorem c18915 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a243 a9 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 3} {2, 7, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c19177 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 5, 8} → T {2, 3, 9} → False := by
  intro a245 a29 a70
  have hc := h.complementary {1, 4, 6, 7} {0, 5, 8} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a70

theorem c19191 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a245 a9 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {0, 3} {2, 5, 8} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19225 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {2, 3, 5} → T {2, 3, 9} → False := by
  intro a245 a9 a66 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {2, 3} {0, 5, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c19227 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a245 a9 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {2, 3} {0, 8, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c19280 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a245 n29 n78 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {5, 8} {0, 2, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c19282 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a245 n29 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {5, 8} {0, 3, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c19475 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a247 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 9} {0, 3} {2, 7, 8} a247 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19597 (h : TenSystem T Q) :
    Q {1, 4, 7, 8} → T {0, 5, 6} → T {2, 3, 9} → False := by
  intro a248 a27 a70
  have hc := h.complementary {1, 4, 7, 8} {0, 5, 6} a248 (by decide) (by decide)
  have he : ( {1, 4, 7, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a70

theorem c19727 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 6} → T {3, 5, 8} → False := by
  intro a249 a12 a93
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a93

theorem c19732 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {2, 5, 8} → False := by
  intro a249 n18 n78
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n78)

theorem c19739 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 5, 8} → T {2, 3, 6} → False := by
  intro a249 a29 a67
  have hc := h.complementary {1, 4, 7, 9} {0, 5, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a67

theorem c19753 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a249 a9 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {0, 3} {2, 5, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19798 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 6} → ¬ T {2, 3, 6} → ¬ T {2, 5, 6} → False := by
  intro a249 n12 n67 n76
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {2, 6} {0, 3, 5} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) ht)

theorem c19800 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 6} → ¬ T {2, 3, 6} → ¬ T {2, 6, 8} → False := by
  intro a249 n12 n67 n81
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {2, 6} {0, 3, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n81 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) ht)

theorem c19847 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a249 a29 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {5, 8} {0, 2, 3} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c19850 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a249 n29 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {5, 8} {0, 3, 6} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

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

theorem c20117 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {2, 3, 9} → T {3, 4, 9} → T {3, 8, 9} → False := by
  intro a251 a70 a90 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {3, 9} {2, 4, 8} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c20149 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 9} → T {3, 4, 7} → False := by
  intro a252 a15 a88
  have hc := h.complementary {1, 5, 6, 8} {0, 2, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a88

theorem c20151 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 4} → T {2, 7, 9} → False := by
  intro a252 a16 a84
  have hc := h.complementary {1, 5, 6, 8} {0, 3, 4} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a16 a84

theorem c20155 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 9} → T {2, 4, 7} → False := by
  intro a252 a21 a73
  have hc := h.complementary {1, 5, 6, 8} {0, 3, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a21 a73

theorem c20156 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {2, 3, 9} → False := by
  intro a252 n24 n70
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 7} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n70)

theorem c20158 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 9} → ¬ T {2, 3, 7} → False := by
  intro a252 n26 n68
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n68)

theorem c20205 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 9} → False := by
  intro a252 a9 a65 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {2, 3} {0, 4, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c20207 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {2, 3, 7} → T {2, 3, 9} → False := by
  intro a252 a9 a68 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {2, 3} {0, 7, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c20220 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 7, 9} → False := by
  intro a252 n13 n68 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {2, 7} {0, 3, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c20234 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 7} → False := by
  intro a252 n16 n65 n88
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {3, 4} {0, 2, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) ht)

theorem c20236 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a252 n16 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {3, 4} {0, 2, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

theorem c20251 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 9} → T {2, 3, 9} → T {3, 4, 9} → False := by
  intro a252 a21 a70 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {3, 9} {0, 2, 4} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)

theorem c20260 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a252 n24 n73 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {4, 7} {0, 2, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c20262 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a252 n24 n88 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {4, 7} {0, 3, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

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

theorem c20451 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a254 a9 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 3} {2, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c20510 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 6, 9} → False := by
  intro a254 n15 n75 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 8} {2, 9} {0, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c20707 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 6} → T {3, 4, 7} → False := by
  intro a256 a12 a88
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 6} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a88

theorem c20713 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 3, 6} → T {2, 4, 7} → False := by
  intro a256 a18 a73
  have hc := h.complementary {1, 5, 8, 9} {0, 3, 6} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a18 a73

theorem c20718 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 3, 6} → False := by
  intro a256 n24 n67
  have hc := h.complementary {1, 5, 8, 9} {0, 4, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n67)

theorem c20721 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 6, 7} → T {2, 3, 4} → False := by
  intro a256 a31 a65
  have hc := h.complementary {1, 5, 8, 9} {0, 6, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a31 a65

theorem c20767 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {2, 3, 6} → T {2, 3, 7} → False := by
  intro a256 a9 a67 a68
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {2, 3} {0, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)

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

theorem c20828 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n24 n73 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {4, 7} {0, 2, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c20830 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {4, 7} {0, 3, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c20957 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → T {2, 3, 9} → T {3, 4, 9} → T {3, 5, 9} → False := by
  intro a257 a70 a90 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 8} {3, 9} {2, 4, 5} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)

theorem c20990 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 3, 4} → ¬ T {2, 5, 8} → False := by
  intro a258 n16 n78
  have hc := h.complementary {1, 6, 7, 9} {0, 3, 4} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n78)

theorem c21000 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 3, 4} → False := by
  intro a258 n29 n65
  have hc := h.complementary {1, 6, 7, 9} {0, 5, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n65)

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

theorem c21786 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a263 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 7} {5, 8} {0, 6, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c21787 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a263 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {5, 8} {0, 6, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c22196 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a266 n24 n52 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 6} {4, 7} {0, 1, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22198 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a266 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 6} {4, 7} {0, 8, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22388 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 9} → ¬ T {4, 6, 7} → False := by
  intro a268 n8 n105
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 9} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n105)

theorem c22479 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a268 a23 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 6} {0, 7, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c22486 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a268 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {4, 7} {0, 6, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22487 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a268 a24 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 7} {0, 6, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22502 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a268 n31 n105 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {6, 7} {0, 4, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c22510 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a268 n33 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {6, 9} {0, 4, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n33 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c22511 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a268 a33 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {6, 9} {0, 4, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

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

theorem c22804 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 5} → ¬ T {4, 7, 9} → False := by
  intro a271 n4 n109
  have hc := h.complementary {2, 3, 6, 8} {0, 1, 5} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n109)

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

theorem c22904 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a271 n24 n52 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 8} {4, 7} {0, 1, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

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

theorem c23694 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 6, 9} → False := by
  intro a277 n8 n21 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 7} {0, 9} {1, 3, 6} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) ht)

theorem c23815 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a278 a2 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {0, 3} {1, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c23820 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {0, 1, 6} → ¬ T {0, 3, 6} → ¬ T {0, 6, 9} → False := by
  intro a278 n5 n18 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 8} {0, 6} {1, 3, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c24068 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {3, 5, 8} → False := by
  intro a280 n8 n93
  have hc := h.complementary {2, 4, 6, 7} {0, 1, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n93)

theorem c24075 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 3, 9} → T {1, 5, 8} → False := by
  intro a280 a21 a57
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a57

theorem c24085 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 9} → False := by
  intro a280 a2 a4 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 1} {3, 5, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c24087 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 1, 8} → T {0, 1, 9} → False := by
  intro a280 a2 a7 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 1} {3, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c24091 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a280 a2 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 3} {1, 5, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24096 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 5} → ¬ T {0, 3, 8} → ¬ T {0, 3, 9} → False := by
  intro a280 n17 n20 n21
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {0, 3} {5, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) ht)
  · exact n20 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) ht)

theorem c24125 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a280 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 3} {0, 5, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
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

theorem c24135 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 5} → T {1, 5, 8} → T {1, 5, 9} → False := by
  intro a280 a4 a57 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 5} {0, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 5} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

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

theorem c24153 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {1, 3, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a280 a49 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 9} {3, 5, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c24156 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 5} → ¬ T {1, 3, 5} → ¬ T {3, 5, 9} → False := by
  intro a280 n17 n45 n94
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 5} {0, 1, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) ht)

theorem c24170 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 9} → ¬ T {1, 3, 9} → ¬ T {3, 5, 9} → False := by
  intro a280 n21 n49 n94
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 9} {0, 1, 5} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)

theorem c24172 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 9} → ¬ T {1, 3, 9} → ¬ T {3, 8, 9} → False := by
  intro a280 n21 n49 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 9} {0, 1, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c24180 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a280 n29 n57 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {5, 8} {0, 1, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c24182 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a280 n29 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {5, 8} {0, 3, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c24353 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 3, 7} → T {1, 5, 8} → False := by
  intro a282 a19 a57
  have hc := h.complementary {2, 4, 6, 9} {0, 3, 7} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a19 a57

theorem c24358 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 7} → False := by
  intro a282 n29 n47
  have hc := h.complementary {2, 4, 6, 9} {0, 5, 8} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n47)

theorem c24536 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 6, 9} → False := by
  intro a283 n8 n21 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 8} {0, 9} {1, 3, 6} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) ht)

theorem c24623 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {5, 6, 8} → False := by
  intro a284 a2 a112
  have hc := h.complementary {2, 4, 7, 9} {0, 1, 3} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a112

theorem c24626 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {3, 5, 8} → False := by
  intro a284 n5 n93
  have hc := h.complementary {2, 4, 7, 9} {0, 1, 6} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n93)

theorem c24632 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {1, 5, 8} → False := by
  intro a284 n18 n57
  have hc := h.complementary {2, 4, 7, 9} {0, 3, 6} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n57)

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

theorem c24653 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a284 a2 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 3} {1, 5, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24747 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 5, 8} → T {1, 5, 8} → T {3, 5, 8} → False := by
  intro a284 a29 a57 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {5, 8} {0, 1, 3} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c24750 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a284 n29 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {5, 8} {0, 3, 6} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c25049 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 9} → T {3, 4, 7} → False := by
  intro a287 a8 a88
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 9} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a8 a88

theorem c25056 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 3, 9} → False := by
  intro a287 n24 n49
  have hc := h.complementary {2, 5, 6, 8} {0, 4, 7} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n49)

theorem c25162 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a287 n24 n88 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 6, 8} {4, 7} {0, 3, 9} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c25196 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → ¬ T {0, 4, 7} → ¬ T {1, 3, 8} → False := by
  intro a288 n24 n48
  have hc := h.complementary {2, 5, 6, 9} {0, 4, 7} a288 (by decide) (by decide)
  have he : ( {2, 5, 6, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 8} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n48)

theorem c25351 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a289 a2 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {0, 3} {1, 4, 6} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c25368 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {0, 1, 6} → ¬ T {0, 3, 6} → ¬ T {0, 6, 9} → False := by
  intro a289 n5 n18 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 8} {0, 6} {1, 3, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

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

theorem c25607 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 6} → T {3, 4, 7} → False := by
  intro a291 a5 a88
  have hc := h.complementary {2, 5, 8, 9} {0, 1, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a5 a88

theorem c25613 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 3, 6} → T {1, 4, 7} → False := by
  intro a291 a18 a52
  have hc := h.complementary {2, 5, 8, 9} {0, 3, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a18 a52

theorem c25617 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 4, 6} → T {1, 3, 7} → False := by
  intro a291 a23 a47
  have hc := h.complementary {2, 5, 8, 9} {0, 4, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a23 a47

theorem c25618 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 3, 6} → False := by
  intro a291 n24 n46
  have hc := h.complementary {2, 5, 8, 9} {0, 4, 7} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n46)

theorem c25621 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 6, 7} → T {1, 3, 4} → False := by
  intro a291 a31 a44
  have hc := h.complementary {2, 5, 8, 9} {0, 6, 7} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a31 a44

theorem c25663 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a291 a2 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {1, 3} {0, 4, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c25667 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a291 a2 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {1, 3} {0, 6, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c25728 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n24 n52 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {4, 7} {0, 1, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c25730 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {4, 7} {0, 3, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c25900 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 4} → False := by
  intro a293 n29 n44
  have hc := h.complementary {2, 6, 7, 9} {0, 5, 8} a293 (by decide) (by decide)
  have he : ( {2, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n44)

theorem c26038 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 3, 5} → False := by
  intro a294 n24 n45
  have hc := h.complementary {2, 6, 8, 9} {0, 4, 7} a294 (by decide) (by decide)
  have he : ( {2, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 5} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n45)

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

theorem c26480 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 6, 9} → False := by
  intro a297 n5 n12 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 7} {0, 6} {1, 2, 9} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c26505 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a297 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {1, 2} {0, 6, 9} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26583 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {6, 7, 9} → False := by
  intro a298 a1 a118
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 2} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a118

theorem c26597 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 6, 7} → T {1, 2, 9} → False := by
  intro a298 a31 a43
  have hc := h.complementary {3, 4, 5, 8} {0, 6, 7} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a31 a43

theorem c26600 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {0, 7, 9} → ¬ T {1, 2, 6} → False := by
  intro a298 n35 n40
  have hc := h.complementary {3, 4, 5, 8} {0, 7, 9} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n40)

theorem c26715 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 7, 9} → T {1, 7, 9} → T {2, 7, 9} → False := by
  intro a298 a35 a63 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {7, 9} {0, 1, 2} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)

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

theorem c26785 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a299 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {1, 2} {0, 6, 8} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c26877 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 5, 8} → T {1, 2, 9} → False := by
  intro a300 a29 a43
  have hc := h.complementary {3, 4, 6, 7} {0, 5, 8} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a43

theorem c26925 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a300 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {1, 2} {0, 5, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26927 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {1, 2, 8} → T {1, 2, 9} → False := by
  intro a300 a1 a42 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {1, 2} {0, 8, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26979 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 5, 8} → T {1, 5, 8} → T {2, 5, 8} → False := by
  intro a300 a29 a57 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {5, 8} {0, 1, 2} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)

theorem c27065 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a301 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {1, 2} {0, 5, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c27158 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 7} → False := by
  intro a302 n29 n41
  have hc := h.complementary {3, 4, 6, 9} {0, 5, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n41)

theorem c27205 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 8} → False := by
  intro a302 a1 a39 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {1, 2} {0, 5, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c27328 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 6, 9} → False := by
  intro a303 n5 n12 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 8} {0, 6} {1, 2, 9} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c27347 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a303 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {1, 2} {0, 6, 9} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c27623 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a305 a1 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {1, 2} {0, 5, 6} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c27827 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 4, 9} → T {1, 4, 9} → T {2, 4, 9} → False := by
  intro a306 a26 a54 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 7} {4, 9} {0, 1, 2} a306 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)

theorem c27856 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 2, 9} → False := by
  intro a307 n24 n43
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 7} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n43)

theorem c27857 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 7} → T {1, 2, 9} → False := by
  intro a307 a24 a43
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 7} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a43

theorem c27865 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 9} → False := by
  intro a307 a1 a3 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 1} {2, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

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

theorem c27873 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a307 a1 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 2} {1, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c27878 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 4, 7} → False := by
  intro a307 n3 n10 n24
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {0, 4} {1, 2, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n24 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) ht)

theorem c27905 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a307 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 2} {0, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28083 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 2, 7} → T {1, 2, 7} → T {2, 4, 7} → False := by
  intro a308 a13 a41 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {2, 7} {0, 1, 4} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)

theorem c28123 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {4, 6, 9} → False := by
  intro a309 a1 a107
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 2} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a107

theorem c28129 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 9} → T {2, 4, 6} → False := by
  intro a309 a8 a72
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a8 a72

theorem c28137 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 4, 6} → T {1, 2, 9} → False := by
  intro a309 a23 a43
  have hc := h.complementary {3, 5, 7, 8} {0, 4, 6} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a43

theorem c28185 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a309 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 2} {0, 4, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c28242 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {2, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a309 n23 n72 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {4, 6} {0, 2, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c28327 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a310 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {1, 2} {0, 6, 8} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28407 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 6} → T {2, 4, 7} → False := by
  intro a311 a5 a73
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a5 a73

theorem c28413 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 6} → T {1, 4, 7} → False := by
  intro a311 a12 a52
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a52

theorem c28416 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 6} → ¬ T {1, 2, 7} → False := by
  intro a311 n23 n41
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n41)

theorem c28418 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 2, 6} → False := by
  intro a311 n24 n40
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n40)

theorem c28420 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {1, 2, 4} → False := by
  intro a311 n31 n38
  have hc := h.complementary {3, 5, 8, 9} {0, 6, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n38)

theorem c28463 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a311 a1 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {1, 2} {0, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c28467 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a311 a1 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {1, 2} {0, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

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

theorem c28528 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a311 n24 n52 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {4, 7} {0, 1, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c28530 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a311 n24 n73 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {4, 7} {0, 2, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c28607 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a312 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 5, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28667 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 4, 9} → T {1, 4, 9} → T {2, 4, 9} → False := by
  intro a312 a26 a54 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {4, 9} {0, 1, 2} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)

theorem c28700 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 4} → False := by
  intro a313 n29 n38
  have hc := h.complementary {3, 6, 7, 9} {0, 5, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n38)

theorem c28747 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 8} → False := by
  intro a313 a1 a39 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

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

theorem c28931 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 2, 7} → T {1, 2, 7} → T {2, 4, 7} → False := by
  intro a314 a13 a41 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {2, 7} {0, 1, 4} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)

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

theorem c29027 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a315 a1 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {1, 2} {0, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

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

theorem c31322 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 7, 9} → T {4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → False := by
  classical
  intro n193 a109 n249 n304
  have u0_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u3_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c1628 h hv n193 n249 n304 u2_320 u1_323 u0_325
  exact c1622 h a109 n193 n249 u3_284 n304 u2_320 u1_323 u0_325

theorem c31327 (h : TenSystem T Q) :
    ¬ Q {3, 6, 8, 9} → ¬ Q {0, 3, 6, 8} → ¬ Q {3, 6, 7, 8} → T {3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {1, 3, 6, 8} → False := by
  classical
  intro n314 n180 n312 a96 n271 n307 n236
  have u0_301 : Q {3, 4, 6, 8} := by
    by_contra hv
    exact c1427 h a96 n180 n236 n271 hv n307 n312 n314
  exact c1435 h u0_301 n180 n236 n271 n307 n312 n314

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

theorem c31365 (h : TenSystem T Q) :
    ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 3, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 4, 6} → T {1, 2, 6} → False := by
  classical
  intro n222 n220 n207 n124 n221 n212 a40
  have u0_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c595 h hv n124 n207 n212 n220 n221 n222
  exact c587 h a40 n124 n207 n212 u0_216 n220 n221 n222

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

theorem c31377 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 6} → Q {1, 2, 3, 9} → T {5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {1, 2, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a112 n160 n196 n139 a210 a113 n253 n288 n216 a120
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := h0
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u2_121 hv a113
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18603 h hv u1_9 a120
  have u8_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23503 h hv u0_2 a120
  have u9_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u2_121 hv a112
  have u10_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1869 h u2_121 hv a112 a113
  have u11_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c14267 h a210 hv a112
  have u12_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22198 h hv u11_24 u6_108 u9_109
  have u13_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17298 h hv u11_24 u6_108 u9_109
  have u14_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c1655 h hv u10_111
  have u15_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1657 h hv u10_111
  have u16_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c824 h hv n139 n216 u13_231 u7_241 u14_251 n253
  have u17_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1139 h hv n160 n216 u12_266 u8_276 u15_286 n288
  have u18_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1675 h hv n196 u16_252 u17_287 u5_317 u4_326 u3_328
  exact c1667 h a112 n196 u16_252 u17_287 u18_307 u5_317 u4_326 u3_328

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

theorem c31458 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 6, 9} → ¬ Q {3, 5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro a166 n311 n114 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u0_121 hv n114
  have u2_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv n114
  have u3_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 n103 hv
  have u4_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u5_33 : T {0, 6, 9} := by
    by_contra hv
    exact c485 h a166 hv
  have u6_82 : T {2, 6, 9} := by
    by_contra hv
    exact c1218 h a166 hv
  have u7_93 : T {3, 5, 8} := by
    by_contra hv
    exact c8232 h a166 hv n103 n114
  have u8_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17611 h hv u5_33 u1_107 u3_118
  have u9_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22511 h hv u5_33 u1_107 u3_118
  have u10_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9773 h hv u6_82 u1_107 u3_118
  have u11_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1392 h hv u10_177 u8_233 u9_268 u4_298 u2_309 n311
  exact c1382 h u7_93 u10_177 u8_233 u9_268 u4_298 u11_307 u2_309 n311

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

theorem c31487 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → T {0, 4, 6} → ¬ Q {0, 4, 6, 9} → False := by
  classical
  intro n171 n185 n189 n135 n156 a23 n191
  have u0_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c332 h a23 n135 n156 n171 n185 n189 hv n191
  exact c344 h u0_190 n135 n156 n171 n185 n189 n191

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

theorem c31535 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 3, 5} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 3, 4} → False := by
  classical
  intro n206 n209 n210 n207 n208 n205
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c544 h u0_121 n205 n206 n207 n208 n209 n210

theorem c31556 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → False := by
  classical
  intro a245 n300 n280 n189
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1566 h a245 n189 n280 n300 u0_316 u1_322 u2_323

theorem c31557 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → False := by
  classical
  intro a280 n245 n189 n300
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1568 h a280 n189 n245 n300 u0_316 u1_322 u2_323

theorem c31558 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → False := by
  classical
  intro a300 n245 n189 n280
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1570 h a300 n189 n245 n280 u0_316 u1_322 u2_323

theorem c31564 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 6, 9} → Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → False := by
  classical
  intro n302 a247 n282 n191
  have u0_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  exact c1596 h a247 n191 n282 n302 u0_318 u1_323 u2_324

theorem c31572 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → T {4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → False := by
  classical
  intro n249 n193 a109 n304 n284
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1622 h a109 n193 n249 n284 n304 u0_320 u1_323 u2_325

theorem c31573 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → False := by
  classical
  intro a193 n284 n249 n304
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1624 h a193 n249 n284 n304 u0_320 u1_323 u2_325

theorem c31574 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → False := by
  classical
  intro a249 n284 n193 n304
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  exact c1626 h a249 n193 n284 n304 u0_320 u1_323 u2_325

theorem c31585 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → T {5, 6, 8} → False := by
  classical
  intro n196 n287 n252 n307 a112
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1667 h a112 n196 n252 n287 n307 u0_317 u1_326 u2_328

theorem c31586 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → False := by
  classical
  intro a196 n287 n252 n307
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1669 h a196 n252 n287 n307 u0_317 u1_326 u2_328

theorem c31587 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → False := by
  classical
  intro a252 n307 n196 n287
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1671 h a252 n196 n287 n307 u0_317 u1_326 u2_328

theorem c31588 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → False := by
  classical
  intro a287 n196 n252 n307
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1673 h a287 n196 n252 n307 u0_317 u1_326 u2_328

theorem c31589 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → False := by
  classical
  intro a307 n252 n196 n287
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  exact c1675 h a307 n196 n252 n287 u0_317 u1_326 u2_328

theorem c31595 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → T {5, 7, 8} → False := by
  classical
  intro n254 n289 n309 n198 a114
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1697 h a114 n198 n254 n289 n309 u0_319 u1_326 u2_329

theorem c31599 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → False := by
  classical
  intro a309 n254 n289 n198
  have u0_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1705 h a309 n198 n254 n289 u0_319 u1_326 u2_329

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

theorem c31604 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → False := by
  classical
  intro a200 n291 n256 n311
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1729 h a200 n256 n291 n311 u0_321 u1_328 u2_329

theorem c31606 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → False := by
  classical
  intro a291 n256 n200 n311
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1733 h a291 n200 n256 n311 u0_321 u1_328 u2_329

theorem c31607 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → Q {3, 5, 8, 9} → False := by
  classical
  intro n291 n200 n256 a311
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1735 h a311 n200 n256 n291 u0_321 u1_328 u2_329

theorem c31614 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → Q {1, 6, 7, 9} → False := by
  classical
  intro n293 n202 n313 a258
  have u0_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1761 h a258 n202 n293 n313 u0_323 u1_327 u2_330

theorem c31621 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → False := by
  classical
  intro a314 n259 n203 n294
  have u0_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1780 h a314 n203 n259 n294 u0_324 u1_328 u2_330

theorem c31627 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ T {7, 8, 9} → False := by
  classical
  intro n101 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1802 h u0_121 n101 n120

theorem c31630 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {6, 8, 9} → False := by
  classical
  intro a102 a119
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1805 h u0_121 a102 a119

theorem c31631 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  classical
  intro n103 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1806 h u0_121 n103 n118

theorem c31635 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ T {5, 8, 9} → False := by
  classical
  intro n105 n116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1810 h u0_121 n105 n116

theorem c31636 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a105 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1811 h u0_121 a105 a116

theorem c31639 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 9} → ¬ T {5, 7, 8} → False := by
  classical
  intro n107 n114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1814 h u0_121 n107 n114

theorem c31642 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {5, 6, 9} → False := by
  classical
  intro a108 a113
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1817 h u0_121 a108 a113

theorem c31643 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 9} → ¬ T {5, 6, 8} → False := by
  classical
  intro n109 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1818 h u0_121 n109 n112

theorem c31644 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a109 a112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1819 h u0_121 a109 a112

theorem c31665 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n102 n109 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1840 h u0_121 n102 n105 n109

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

theorem c31669 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n108 n109 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1844 h u0_121 n105 n108 n109

theorem c31685 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n110 n109 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1860 h u0_121 n107 n109 n110

theorem c31706 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  classical
  intro a112 a103 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1881 h u0_121 a103 a112 a116

theorem c31710 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  classical
  intro a112 a114 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1885 h u0_121 a112 a114 a116

theorem c31737 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {5, 6, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n119 n113 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1912 h u0_121 n107 n113 n119

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

theorem c31757 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 9} → ¬ T {7, 8, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n115 n120 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1932 h u0_121 n115 n118 n120

theorem c31767 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a185 a120
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10763 h a185 u0_37 a120

theorem c31789 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 8} → T {1, 2, 6} → T {1, 2, 9} → False := by
  classical
  intro a187 a40 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11065 h a187 u0_37 a40 a43

theorem c31817 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 8} → T {5, 7, 9} → False := by
  classical
  intro a190 a115
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11463 h a190 u0_37 a115

theorem c31819 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {0, 4, 6, 8} → T {1, 2, 9} → False := by
  classical
  intro a39 a190 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11485 h a190 u0_37 a39 a43

theorem c31881 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 4} → T {1, 3, 7} → Q {0, 5, 6, 8} → False := by
  classical
  intro a44 a47 a196
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12331 h a196 u0_37 a44 a47

theorem c31887 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 9} → T {4, 7, 8} → False := by
  classical
  intro a197 a108
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12443 h a197 u0_37 a108

theorem c31897 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {4, 6, 9} → False := by
  classical
  intro a198 a107
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12583 h a198 u0_37 a107

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

theorem c31900 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {1, 2, 6} → T {1, 2, 9} → False := by
  classical
  intro a198 a40 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12607 h a198 u0_37 a40 a43

theorem c31930 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a201 a39 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13027 h a201 u0_37 a39 a43

theorem c31947 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 6, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a203 a102
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13283 h a203 u0_37 a102

theorem c31993 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 7} → T {0, 3, 9} → Q {1, 4, 5, 8} → False := by
  classical
  intro a19 a21 a243
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c18915 h a243 u0_9 a19 a21

theorem c32011 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 8} → T {0, 3, 5} → Q {1, 4, 6, 7} → False := by
  classical
  intro a20 a17 a245
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19191 h a245 u0_9 a17 a20

theorem c32015 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 5} → Q {1, 4, 6, 7} → T {2, 3, 9} → False := by
  classical
  intro a66 a245 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19225 h a245 u0_9 a66 a70

theorem c32016 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 8} → Q {1, 4, 6, 7} → T {2, 3, 9} → False := by
  classical
  intro a69 a245 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19227 h a245 u0_9 a69 a70

theorem c32033 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 8} → T {0, 3, 7} → Q {1, 4, 6, 9} → False := by
  classical
  intro a20 a19 a247
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19475 h a247 u0_9 a19 a20

theorem c32052 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 5} → T {0, 3, 8} → Q {1, 4, 7, 9} → False := by
  classical
  intro a17 a20 a249
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19753 h a249 u0_9 a17 a20

theorem c32085 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 8} → T {2, 3, 4} → T {2, 3, 9} → False := by
  classical
  intro a252 a65 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20205 h a252 u0_9 a65 a70

theorem c32086 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 8} → T {2, 3, 9} → T {2, 3, 7} → False := by
  classical
  intro a252 a70 a68
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20207 h a252 u0_9 a68 a70

theorem c32101 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → Q {1, 5, 7, 8} → T {0, 3, 6} → False := by
  classical
  intro a16 a254 a18
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20451 h a254 u0_9 a16 a18

theorem c32126 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 6} → T {2, 3, 7} → Q {1, 5, 8, 9} → False := by
  classical
  intro a67 a68 a256
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20767 h a256 u0_9 a67 a68

theorem c32193 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → T {0, 3, 7} → T {0, 3, 9} → False := by
  classical
  intro a278 a19 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23815 h a278 u0_2 a19 a21

theorem c32209 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 1, 5} → T {0, 1, 9} → False := by
  classical
  intro a280 a4 a8
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24085 h a280 u0_2 a4 a8

theorem c32210 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 1, 8} → T {0, 1, 9} → False := by
  classical
  intro a280 a7 a8
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24087 h a280 u0_2 a7 a8

theorem c32211 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 3, 8} → T {0, 3, 5} → False := by
  classical
  intro a280 a20 a17
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24091 h a280 u0_2 a17 a20

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

theorem c32215 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 5} → Q {2, 4, 6, 7} → T {1, 3, 9} → False := by
  classical
  intro a45 a280 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24125 h a280 u0_2 a45 a49

theorem c32216 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {1, 3, 8} → T {1, 3, 9} → False := by
  classical
  intro a280 a48 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24127 h a280 u0_2 a48 a49

theorem c32247 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a284 a112
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24623 h a284 u0_2 a112

theorem c32252 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {0, 3, 5} → T {0, 3, 8} → False := by
  classical
  intro a284 a17 a20
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24653 h a284 u0_2 a17 a20

theorem c32301 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → T {0, 3, 6} → Q {2, 5, 7, 8} → False := by
  classical
  intro a16 a18 a289
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25351 h a289 u0_2 a16 a18

theorem c32324 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 6} → T {1, 3, 4} → Q {2, 5, 8, 9} → False := by
  classical
  intro a46 a44 a291
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25663 h a291 u0_2 a44 a46

theorem c32326 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 6} → T {1, 3, 7} → Q {2, 5, 8, 9} → False := by
  classical
  intro a46 a47 a291
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25667 h a291 u0_2 a46 a47

theorem c32385 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 7} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a297 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26505 h a297 u0_1 a40 a43

theorem c32387 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 8} → T {6, 7, 9} → False := by
  classical
  intro a298 a118
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26583 h a298 u0_1 a118

theorem c32405 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {1, 2, 6} → T {1, 2, 8} → False := by
  classical
  intro a299 a40 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26785 h a299 u0_1 a40 a42

theorem c32415 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {3, 4, 6, 7} → T {1, 2, 9} → False := by
  classical
  intro a39 a300 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26925 h a300 u0_1 a39 a43

theorem c32416 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 8} → Q {3, 4, 6, 7} → T {1, 2, 9} → False := by
  classical
  intro a42 a300 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26927 h a300 u0_1 a42 a43

theorem c32425 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a301 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27065 h a301 u0_1 a39 a43

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

theorem c32435 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → T {1, 2, 8} → Q {3, 4, 6, 9} → False := by
  classical
  intro a39 a42 a302
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27205 h a302 u0_1 a39 a42

theorem c32446 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 8} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a303 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27347 h a303 u0_1 a40 a43

theorem c32464 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {3, 4, 8, 9} → T {1, 2, 6} → False := by
  classical
  intro a39 a305 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27623 h a305 u0_1 a39 a40

theorem c32479 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {0, 1, 4} → T {0, 1, 9} → False := by
  classical
  intro a307 a3 a8
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27865 h a307 u0_1 a3 a8

theorem c32482 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {0, 2, 4} → False := by
  classical
  intro a307 a15 a10
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27873 h a307 u0_1 a10 a15

theorem c32485 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a307 a38 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27905 h a307 u0_1 a38 a43

theorem c32497 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → T {4, 6, 9} → False := by
  classical
  intro a309 a107
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28123 h a309 u0_1 a107

theorem c32505 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a309 a38 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28185 h a309 u0_1 a38 a43

theorem c32516 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 9} → T {1, 2, 8} → T {1, 2, 6} → False := by
  classical
  intro a310 a42 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28327 h a310 u0_1 a40 a42

theorem c32524 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {1, 2, 4} → T {1, 2, 6} → False := by
  classical
  intro a311 a38 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28463 h a311 u0_1 a38 a40

theorem c32526 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {3, 5, 8, 9} → T {1, 2, 6} → False := by
  classical
  intro a41 a311 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28467 h a311 u0_1 a40 a41

theorem c32536 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a312 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28607 h a312 u0_1 a39 a43

theorem c32546 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → T {1, 2, 8} → Q {3, 6, 7, 9} → False := by
  classical
  intro a39 a42 a313
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28747 h a313 u0_1 a39 a42

theorem c32566 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {3, 7, 8, 9} → T {1, 2, 6} → False := by
  classical
  intro a39 a315 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c29027 h a315 u0_1 a39 a40

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases113
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32583 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 9} → False := by
  classical
  intro a304
  have u0_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u2_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u1_118
  have u3_49 : T {1, 3, 9} := by
    by_contra hv
    exact c32582 h h0 hv a304
  have u4_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 u3_49 hv
  have u5_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u4_210 hv
  have u6_183 : Q {0, 3, 7, 9} := by
    by_contra hv
    exact c31524 h h0 u4_210 hv a304
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11153 h hv u3_49 u5_70 u0_99
  have u8_19 : T {0, 3, 7} := by
    by_contra hv
    exact c285 h u6_183 hv
  have u9_21 : T {0, 3, 9} := by
    by_contra hv
    exact c313 h u6_183 hv
  have u10_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c32193 h h0 hv u8_19 u9_21
  have u11_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c31993 h h0 u8_19 u9_21 hv
  exact c31421 h h0 u11_243 u2_103 u7_187 u10_278

theorem c32586 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → False := by
  classical
  intro a198 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u2_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u3_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31897 h h0 a198 hv
  have u4_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c12635 h a198 u2_43 a49 hv
  have u5_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c12691 h a198 a49 u1_70 hv
  exact c12710 h a198 u4_54 u5_90 u3_107

theorem c32590 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 5, 8} → ¬ Q {0, 4, 6, 7} → T {4, 6, 7} → ¬ T {0, 5, 8} → False := by
  classical
  intro n93 n189 a105 n29
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u1_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24182 h hv n29 n93 u0_116
  have u2_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19282 h hv n29 n93 u0_116
  exact c31281 h h0 u1_280 u2_245 a105 n189

theorem c32591 (h : TenSystem T Q) :
    ¬ Q {2, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → T {3, 5, 8} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 4, 5, 8} → False := by
  classical
  intro n268 n233 a93 n311 n177 n307 n298
  have u0_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1394 h hv n177 n233 n268 n298 n307 n311
  exact c1382 h a93 n177 n233 n268 n298 n307 u0_309 n311

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases114
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32599 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 6} → False := by
  classical
  intro a177 n40
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h a177 hv
  have u2_20 : T {0, 3, 8} := by
    by_contra hv
    exact c294 h a177 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c9644 h a177 n40 hv
  have u4_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32252 h h0 hv u1_17 u2_20
  have u5_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c32052 h h0 u1_17 u2_20 hv
  have u6_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31573 h h0 hv u4_284 u5_249 u0_304
  exact c31572 h h0 u5_249 u6_193 u3_109 u0_304 u4_284

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases116
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32612 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 7} → T {3, 5, 8} → T {4, 6, 7} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a24 a93 a105 n309 n298 n311 n177 a210
  have u0_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u1_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h a210 a24 hv
  have u2_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv a24 u0_43
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u1_112
  have u4_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22487 h hv a24 a105 u3_109
  have u5_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17587 h hv a24 a105 u3_109
  exact c1382 h a93 n177 u5_233 u4_268 n298 u2_307 n309 n311

theorem c32615 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 7} → T {4, 6, 7} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a24 a105 n309 n298 n311 n177 a210
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h a210 hv a105
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h a210 a24 hv
  have u3_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32612 h h0 a24 hv a105 n309 n298 n311 n177 a210
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u2_112
  have u5_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24750 h hv u1_29 u3_93 u2_112
  have u6_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19850 h hv u1_29 u3_93 u2_112
  have u7_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31573 h h0 hv u5_284 u6_249 u0_304
  exact c31572 h h0 u6_249 u7_193 u4_109 u0_304 u5_284

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases117
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32616 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → T {4, 6, 7} → False := by
  classical
  intro n280 n300 n189 a105
  have u0_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 hv a105 n189
  exact c31556 h h0 u0_245 n300 n280 n189

theorem c32622 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 8, 9} → T {0, 3, 7} → ¬ T {0, 4, 7} → T {4, 6, 7} → ¬ Q {1, 2, 5, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 2, 9} → T {1, 3, 9} → False := by
  classical
  intro a225 a19 n24 a105 n216 n124 n127 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u0_210 n24 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u1_112
  have u3_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u0_210 hv a105
  have u4_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u5_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u4_189 a105 u3_29
  have u6_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u3_29
  have u7_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u8_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u9_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv u8_41
  have u10_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u11_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u12_42 : T {1, 2, 8} := by
    by_contra hv
    exact c630 h a225 hv
  have u13_64 : T {1, 8, 9} := by
    by_contra hv
    exact c950 h a225 hv
  have u14_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c16365 h a225 hv a105
  have u15_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c16369 h a225 a19 hv
  have u16_91 : T {3, 5, 6} := by
    by_contra hv
    exact c16374 h a225 n24 hv
  have u17_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32416 h h0 u12_42 hv u11_43
  have u18_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31627 h h0 u15_101 hv
  have u19_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1943 h hv u16_91 u18_120
  have u20_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u17_300 u4_189 a105
  have u21_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u20_280 hv u4_189 u17_300
  have u22_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c32216 h h0 u20_280 hv a49
  have u23_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c32215 h h0 hv u20_280 a49
  have u24_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24180 h u20_280 u3_29 hv u7_116
  have u25_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c24075 h u20_280 hv u24_57
  have u26_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c24153 h u20_280 a49 hv u13_64
  have u27_94 : T {3, 5, 9} := by
    by_contra hv
    exact c24156 h u20_280 u14_17 u23_45 hv
  have u28_20 : T {0, 3, 8} := by
    by_contra hv
    exact c24096 h u20_280 u14_17 hv u25_21
  have u29_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c32016 h h0 hv u21_245 u10_70
  have u30_78 : T {2, 5, 8} := by
    by_contra hv
    exact c19280 h u21_245 u3_29 hv u7_116
  have u31_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25196 h hv n24 u22_48
  have u32_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7266 h hv u22_48 u2_109
  have u33_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24353 h hv a19 u24_57
  have u34_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c866 h hv u26_58
  have u35_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2515 h hv u27_94 a105
  have u36_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c32033 h h0 u28_20 a19 hv
  have u37_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4326 h hv u29_69 u2_109
  have u38_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u24_57 u30_78 u5_93
  have u39_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31459 h h0 u33_282 u38_191 u36_247 hv
  have u40_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31377 h h0 u1_112 u32_160 u6_196 u37_139 u0_210 hv u34_253 u31_288 n216 u18_120
  have u41_123 : Q {0, 1, 2, 5} := by
    by_contra hv
    exact c31532 h h0 u19_122 u9_125 n124 n127 hv u35_126
  have u42_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31685 h h0 hv u2_109 u39_107
  have u43_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31737 h h0 hv u40_113 u39_107
  exact c2221 h u41_123 u42_110 u43_119 u18_120

theorem c32623 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 7} → T {4, 6, 7} → T {1, 3, 9} → False := by
  classical
  intro a219 n24 a105 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u0_210 n24 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u1_112
  have u3_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u4_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u0_210 hv a105
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u4_29
  have u6_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u7_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u8_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u9_39 : T {1, 2, 5} := by
    by_contra hv
    exact c585 h a219 hv
  have u10_58 : T {1, 5, 9} := by
    by_contra hv
    exact c860 h a219 hv
  have u11_96 : T {3, 6, 8} := by
    by_contra hv
    exact c15532 h a219 n24 hv
  have u12_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c15529 h a219 hv a105
  have u13_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c31819 h h0 u9_39 hv u8_43
  have u14_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c32536 h h0 hv u9_39 u8_43
  have u15_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c31930 h h0 hv u9_39 u8_43
  have u16_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32425 h h0 hv u9_39 u8_43
  have u17_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32415 h h0 u9_39 hv u8_43
  have u18_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c296 h hv u12_20
  have u19_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u17_300 u3_189 a105
  have u20_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u19_280 hv u3_189 u17_300
  have u21_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c32216 h h0 u19_280 hv a49
  have u22_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c32215 h h0 hv u19_280 a49
  have u23_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24180 h u19_280 u4_29 hv u6_116
  have u24_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c24153 h u19_280 a49 u10_58 hv
  have u25_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c24135 h u19_280 hv u23_57 u10_58
  have u26_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c32015 h h0 hv u20_245 u7_70
  have u27_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c716 h hv u21_48
  have u28_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7964 h hv u22_45 u2_109
  have u29_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26038 h hv n24 u22_45
  have u30_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c958 h hv u24_64
  have u31_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22804 h hv u25_4 u2_109
  have u32_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5024 h hv u26_66 u2_109
  have u33_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c481 h hv u32_144 u28_165 u18_180 u13_190 u5_196 u15_201
  have u34_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31621 h h0 hv u30_259 u33_203 u29_294
  have u35_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c31327 h u34_314 u18_180 u14_312 u11_96 u31_271 hv u27_236
  exact c1437 h u35_307 u18_180 u27_236 u31_271 u16_301 u14_312 u34_314

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases118
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32624 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 4, 9} → ¬ T {0, 4, 7} → T {4, 6, 7} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a215 n24 a105 n311 n177 a210
  have u0_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h a210 hv a105
  have u1_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u2_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u1_189 a105 u0_29
  have u3_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h a210 n24 hv
  have u4_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u5_38 : T {1, 2, 4} := by
    by_contra hv
    exact c570 h a215 hv
  have u6_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c15077 h a215 u2_93 u3_112 hv
  have u7_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32485 h h0 hv u5_38 u4_43
  have u8_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32505 h h0 hv u5_38 u4_43
  have u9_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u6_114
  have u10_23 : T {0, 4, 6} := by
    by_contra hv
    exact c14264 h a210 hv u6_114
  have u11_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22479 h hv u10_23 a105 u9_107
  have u12_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17579 h hv u10_23 a105 u9_107
  have u13_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c32591 h u11_268 u12_233 u2_93 n311 n177 u7_307 hv
  exact c1390 h u13_298 n177 u12_233 u11_268 u7_307 u8_309 n311

private theorem c32625 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 7} → T {4, 6, 7} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n24 a105 n127 n177 a49
  have u0_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32621 h h0 hv n127 n177 a49
  have u1_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c600 h hv u0_40
  have u2_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c594 h hv u0_40
  have u3_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c588 h hv u0_40
  have u4_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u5_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u6_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c615 h hv u5_41
  have u7_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c32586 h h0 hv a49
  have u8_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u9_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c32623 h h0 hv n24 a105 a49
  have u10_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c32624 h h0 hv n24 a105 u4_311 n177 u8_210
  have u11_225 : Q {1, 2, 8, 9} := by
    by_contra hv
    exact c636 h u8_210 n127 u10_215 u9_219 u1_222 u6_224 hv
  have u12_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c16365 h u11_225 hv a105
  have u13_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c32622 h h0 u11_225 hv n24 a105 u2_216 u3_124 n127 a49
  have u14_101 : T {4, 5, 6} := by
    by_contra hv
    exact c16368 h u11_225 u13_19 hv
  have u15_16 : T {0, 3, 4} := by
    by_contra hv
    exact c16384 h u11_225 hv u12_17 u13_19
  have u16_18 : T {0, 3, 6} := by
    by_contra hv
    exact c16388 h u11_225 u12_17 hv u13_19
  have u17_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c14331 h u8_210 hv u14_101 a105
  have u18_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c32301 h h0 u15_16 u16_18 hv
  have u19_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c32101 h h0 u15_16 hv u16_18
  have u20_114 : T {5, 7, 8} := by
    by_contra hv
    exact c14264 h u8_210 u17_23 hv
  have u21_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c31599 h h0 hv u19_254 u18_289 u7_198
  exact c31595 h h0 u19_254 u18_289 u21_309 u7_198 u20_114

theorem c32626 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro a105 n127 n177 a49
  have u0_304 : ¬ Q {3, 4, 7, 9} := c32583 h h0
  have u1_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32621 h h0 hv n127 n177 a49
  have u2_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u3_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u4_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u3_210 hv
  have u5_116 : ¬ T {5, 8, 9} := c31636 h h0 a105
  have u6_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u3_210 hv a105
  have u7_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8944 h hv u1_40 u5_116
  have u8_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32625 h h0 hv a105 n127 n177 a49
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h u3_210 u8_24 hv
  have u10_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv u8_24 u4_43
  have u11_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c14343 h u3_210 u8_24 a105 hv
  have u12_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c14339 h u3_210 u8_24 hv a105
  have u13_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u9_112
  have u14_103 : T {4, 5, 8} := by
    by_contra hv
    exact c14370 h u3_210 u6_29 hv u9_112
  have u15_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21786 h hv u6_29 u9_112 u5_116
  have u16_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16886 h hv u6_29 u9_112 u5_116
  have u17_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c1614 h hv u11_108
  have u18_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1524 h hv u12_102
  have u19_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22487 h hv u8_24 a105 u13_109
  have u20_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17587 h hv u8_24 a105 u13_109
  have u21_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14277 h u3_210 hv u14_103
  have u22_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1317 h hv u7_172 u16_228 u15_263 u18_297 u17_303 u0_304
  have u23_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c459 h hv u21_31
  have u24_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u22_300 u23_189 a105
  have u25_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u23_189 a105 u6_29
  have u26_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u24_280 hv u23_189 u22_300
  have u27_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24180 h u24_280 u6_29 hv u5_116
  have u28_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c32591 h u19_268 u20_233 u25_93 u2_311 n177 u10_307 hv
  have u29_78 : T {2, 5, 8} := by
    by_contra hv
    exact c19280 h u26_245 u6_29 hv u5_116
  have u30_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c12007 h hv u27_57 u29_78 u25_93
  have u31_35 : T {0, 7, 9} := by
    by_contra hv
    exact c26600 h u28_298 hv u1_40
  have u32_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u30_193 u13_109 hv u0_304
  have u33_63 : T {1, 7, 9} := by
    by_contra hv
    exact c939 h u32_249 hv
  have u34_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u32_249 hv u30_193 u0_304
  have u35_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c26715 h u28_298 u31_35 u33_63 hv
  exact c1254 h u34_284 u35_84

theorem c32627 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ T {4, 6, 7} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → Q {1, 2, 3, 9} → False := by
  classical
  intro a298 n307 n105 n311 n177 a210
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h a210 hv n105
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h a210 hv
  have u2_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1539 h a298 hv
  have u3_118 : ¬ T {6, 7, 9} := c32387 h h0 a298
  have u4_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c26597 h a298 hv u1_43
  have u5_114 : ¬ T {5, 7, 8} := c14373 h a210 u0_29 u2_103
  have u6_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17602 h hv u4_31 n105 u3_118
  have u7_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22502 h hv u4_31 n105 u3_118
  have u8_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv u5_114
  exact c1390 h a298 n177 u6_233 u7_268 n307 u8_309 n311

theorem c32628 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 5, 8} → T {3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ T {4, 6, 7} → ¬ Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → T {1, 2, 9} → False := by
  classical
  intro n233 a93 n298 n307 n105 n311 n177 a43
  have u0_268 : Q {2, 3, 5, 8} := by
    by_contra hv
    exact c32591 h hv n233 a93 n311 n177 n307 n298
  have u1_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c1388 h u0_268 n177 n233 n298 n307 hv n311
  have u2_8 : T {0, 1, 9} := by
    by_contra hv
    exact c22388 h u0_268 hv n105
  have u3_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c32497 h h0 u1_309 hv
  have u4_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28137 h u1_309 hv a43
  have u5_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28242 h u1_309 u4_23 hv u3_107
  exact c28129 h u1_309 u2_8 u5_72

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases119
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32631 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → T {5, 6, 8} → False := by
  classical
  intro n252 n307 n196 a112
  have u0_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c31588 h h0 hv n196 n252 n307
  exact c31585 h h0 n196 u0_287 n252 n307 a112

private theorem c32632 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 3, 4} → T {2, 4, 7} → Q {2, 5, 6, 8} → Q {1, 5, 6, 8} → ¬ T {0, 6, 9} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 7, 9} → ¬ Q {0, 2, 4, 7} → ¬ Q {2, 4, 6, 7} → T {1, 3, 9} → False := by
  classical
  intro n16 a73 a287 a252 n33 n263 n284 n157 n280 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u2_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 a252 hv u1_70
  have u3_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u4_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c607 h hv u3_41
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c20234 h a252 n16 u2_65 hv
  have u6_90 : T {3, 4, 9} := by
    by_contra hv
    exact c20236 h a252 n16 u2_65 hv
  have u7_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c20251 h a252 hv u1_70 u6_90
  have u8_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c25049 h a287 hv u5_88
  have u9_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24536 h hv u8_8 u7_21 n33
  have u10_277 : Q {2, 4, 5, 7} := by
    by_contra hv
    exact c1082 h a73 n157 u4_213 n263 hv n280 u9_283 n284
  exact c23694 h u10_277 u8_8 u7_21 n33

private theorem c32633 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n127 n177 a49
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u1_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u2_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32621 h h0 hv n127 n177 a49
  have u4_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32626 h h0 hv n127 n177 a49
  have u5_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1567 h hv u4_105
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u4_105 hv
  have u7_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u2_210 hv u4_105
  have u8_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c32630 h h0 hv n127 n177 a49
  have u9_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c350 h hv u8_24
  have u10_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv u8_24
  have u11_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u2_210 u8_24 hv
  have u12_108 : T {4, 7, 8} := by
    by_contra hv
    exact c14342 h u2_210 u8_24 u4_105 hv
  have u13_102 : T {4, 5, 7} := by
    by_contra hv
    exact c14338 h u2_210 u8_24 hv u4_105
  have u14_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u11_112
  have u15_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32247 h h0 hv u11_112
  have u16_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31706 h h0 u11_112 hv u6_116
  have u17_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u11_112 hv u6_116
  have u18_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u7_29 u11_112 u6_116
  have u19_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u12_108 hv
  have u20_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c31887 h h0 hv u12_108
  have u21_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c14271 h u2_210 hv u12_108
  have u22_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u13_102 hv
  have u23_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c31947 h h0 hv u13_102
  have u24_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17586 h hv u8_24 u4_105 u14_109
  have u25_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22486 h hv u8_24 u4_105 u14_109
  have u26_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u16_103
  have u27_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c31458 h h0 hv u0_311 u17_114 u16_103
  have u28_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10206 h hv u1_41 u16_103
  have u29_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv u17_114
  have u30_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u3_40 u17_114
  have u31_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9086 h hv u1_41 u19_113
  have u32_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c403 h hv u21_27
  have u33_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8664 h hv u1_41 u22_119
  have u34_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1392 h hv n177 u24_233 u25_268 u26_298 u29_309 u0_311
  have u35_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c1382 h hv n177 u24_233 u25_268 u26_298 u34_307 u29_309 u0_311
  have u36_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11606 h hv u1_41 u35_93
  have u37_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5292 h hv u35_93 u16_103 u17_114
  have u38_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c494 h hv u37_145 u27_166 u28_181 u36_191 u20_197 u23_203
  have u39_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv u37_145 u27_166 u28_181 u36_191 u20_197 u38_202 u23_203
  have u40_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 hv u34_307 u32_196 u11_112
  have u41_57 : T {1, 5, 8} := by
    by_contra hv
    exact c851 h u40_252 hv
  have u42_287 : Q {2, 5, 6, 8} := by
    by_contra hv
    exact c31587 h h0 u40_252 u34_307 u32_196 hv
  have u43_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20260 h u40_252 u8_24 hv u14_109
  have u44_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5801 h hv u41_57 u11_112 u6_116
  have u45_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1166 h u42_287 hv
  have u46_16 : T {0, 3, 4} := by
    by_contra hv
    exact c32632 h h0 hv u43_73 u42_287 u40_252 u39_33 u18_263 u15_284 u9_157 u5_280 a49
  have u47_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2861 h hv u45_78 u11_112 u6_116
  have u48_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8905 h hv u41_57 u45_78 u6_116
  exact c227 h u46_16 u47_128 u44_149 u33_170 u48_171 u10_172 u31_173 u30_174

theorem c32634 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → T {5, 6, 8} → False := by
  classical
  intro n307 n252 n287 a112
  have u0_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 n252 n307 hv a112
  exact c31586 h h0 u0_196 n287 n252 n307

private theorem c32635 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 7} → Q {0, 1, 2, 9} → Q {1, 2, 3, 9} → False := by
  classical
  intro n24 a127 a210
  have u0_15 : T {0, 2, 9} := by
    by_contra hv
    exact c213 h a127 hv
  have u1_8 : T {0, 1, 9} := by
    by_contra hv
    exact c108 h a127 hv
  have u2_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h a210 n24 hv
  have u3_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u2_112
  have u4_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c2647 h a127 hv u2_112
  have u5_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25162 h hv n24 u4_88 u3_109
  have u6_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20262 h hv n24 u4_88 u3_109
  have u7_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32634 h h0 hv u6_252 u5_287 u2_112
  have u8_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c32479 h h0 u7_307 hv u1_8
  have u9_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c32482 h h0 u7_307 u0_15 hv
  exact c27878 h u7_307 u8_3 u9_10 n24

private theorem c32636 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n105 n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u2_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c32633 h h0 hv n177 a49
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32635 h h0 hv u2_127 u0_210
  have u4_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv u3_24 u1_43
  have u5_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u7_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u0_210 hv n105
  have u8_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32611 h h0 n105 hv n177 a49
  have u9_93 : T {3, 5, 8} := by
    by_contra hv
    exact c2654 h u2_127 hv n105
  have u10_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32627 h h0 hv u4_307 n105 u5_311 n177 u0_210
  have u11_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c592 h hv u8_40
  have u12_233 : Q {1, 3, 5, 8} := by
    by_contra hv
    exact c32628 h h0 hv u9_93 u10_298 u4_307 n105 u5_311 n177 u1_43
  exact c32629 h h0 u12_233 u3_24 u7_29 u6_116 u11_212 a49

private theorem c32637 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u2_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c32633 h h0 hv n177 a49
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32635 h h0 hv u2_127 u0_210
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32636 h h0 hv n177 a49
  have u5_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c2655 h u2_127 hv u4_105
  have u6_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1389 h hv u5_93
  have u7_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1393 h hv u5_93
  exact c32615 h h0 u3_24 u4_105 u7_309 u6_298 u1_311 n177 u0_210

theorem c32638 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 9} → False := by
  classical
  intro a49
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u2_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u1_210 hv
  have u3_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u4_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c615 h hv u3_41
  have u5_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c32637 h h0 hv a49
  have u6_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h u5_177 hv
  have u7_29 : T {0, 5, 8} := by
    by_contra hv
    exact c427 h u5_177 hv
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c9649 h u5_177 u2_43 hv
  have u9_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32599 h h0 u5_177 hv
  have u10_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26877 h hv u7_29 u2_43
  have u11_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u8_105 hv
  have u12_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c9645 h u5_177 u9_40 hv
  have u13_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c9665 h u5_177 hv u9_40 u2_43
  have u14_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u2_43 u9_40
  have u15_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u2_43 u9_40
  have u16_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv u9_40 u11_116
  have u17_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u12_109 hv
  have u18_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u12_109 u8_105
  have u19_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u12_109 u8_105
  have u20_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c570 h hv u13_38
  have u21_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c14267 h u1_210 hv u17_112
  have u22_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u7_29 u17_112 u11_116
  have u23_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u7_29 u17_112 u11_116
  have u24_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c14271 h u1_210 hv u18_108
  have u25_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15945 h hv u6_17 u18_108
  have u26_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c14279 h u1_210 hv u19_102
  have u27_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c32635 h h0 u21_24 hv u1_210
  have u28_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u16_172 u23_228 u22_263 u15_297 u10_300 u14_303 u0_304
  have u29_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16376 h hv u24_27 u28_88
  have u30_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15538 h hv u26_32 u28_88
  exact c636 h u1_210 u27_127 u20_215 u30_219 u25_222 u4_224 u29_225

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases120
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32639 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 3, 9} → False := by
  classical
  intro a133
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c723 h a133 u0_49

theorem c32640 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → False := by
  classical
  intro a210
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c725 h a210 u0_49

theorem c32641 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 4, 9} → False := by
  classical
  intro a230
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c727 h a230 u0_49

theorem c32643 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 6, 9} → False := by
  classical
  intro a237
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c731 h a237 u0_49

theorem c32644 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → False := by
  classical
  intro a239
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c733 h a239 u0_49

theorem c32646 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 8} → ¬ T {0, 4, 7} → False := by
  classical
  intro a177 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u3_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u4_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h a177 hv
  have u5_20 : T {0, 3, 8} := by
    by_contra hv
    exact c294 h a177 hv
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c427 h a177 hv
  have u7_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1383 h a177 hv
  have u8_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32599 h h0 a177 hv
  have u9_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32211 h h0 hv u5_20 u4_17
  have u10_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c32011 h h0 u5_20 u4_17 hv
  have u11_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c9645 h a177 u8_40 hv
  have u12_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31281 h h0 u9_280 u10_245 hv u2_189
  have u13_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c31558 h h0 hv u10_245 u2_189 u9_280
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u11_109 hv
  have u15_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u11_109 u12_105
  have u16_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u12_105 hv
  have u17_43 : T {1, 2, 9} := by
    by_contra hv
    exact c9648 h a177 hv u12_105
  have u18_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16349 h hv u6_29 u7_93 u14_112
  have u19_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u6_29 u14_112 u16_116
  have u20_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u6_29 u14_112 u16_116
  have u21_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c15071 h hv u6_29 u7_93 u14_112
  have u22_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15945 h hv u4_17 u15_108
  have u23_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u17_43 u8_40
  have u24_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u17_43 u8_40
  have u25_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u3_172 u20_228 u19_263 u24_297 u13_300 u23_303 u0_304
  have u26_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16472 h hv n24 u25_88 u12_105
  have u27_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15622 h hv n24 u25_88 u12_105
  exact c31390 h u22_222 u17_43 u26_225 u18_224 u21_215 u1_210 u27_219

private theorem c32647 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 5, 8} → T {0, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a112 n297 n303 n198 n187 a29 n105 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u5_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u6_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u7_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u8_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u9_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14087 h hv a29 a112 u4_116
  have u10_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13641 h hv a29 a112 u4_116
  have u11_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv a29 a112 u4_116
  have u12_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv a29 a112 u4_116
  have u13_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u8_109 n105
  have u14_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13772 h hv n24 n105 u8_109
  have u15_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14202 h hv n24 n105 u8_109
  have u16_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c31535 h h0 u14_206 u15_209 u1_210 hv u9_208 u10_205
  have u17_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u7_172 u12_228 u11_263 n297 u5_300 n303 u2_304
  have u18_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c13855 h u16_207 hv u13_108
  have u19_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4708 h hv u17_88 n105 u8_109
  have u20_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c450 h hv u18_30
  have u21_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c432 h hv u19_141 u3_162 u6_177 n187 n198 u20_200
  exact c422 h a29 u19_141 u3_162 u6_177 n187 u21_196 n198 u20_200

theorem c32648 (h : TenSystem T Q) :
    ¬ Q {0, 1, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → T {0, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 2, 5, 8} → False := by
  classical
  intro n141 n187 n196 n198 a29 n177 n162
  have u0_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c422 h a29 n141 n162 n177 n187 n196 n198 hv
  exact c436 h u0_200 n141 n162 n177 n187 n196 n198

private theorem c32649 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → T {1, 2, 6} → T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a43 a40 a29 a93 n105 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u3_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u4_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u5_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31789 h h0 hv a40 a43
  have u6_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31900 h h0 hv a40 a43
  have u7_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv a43 a40
  have u8_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv a43 a40
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32647 h h0 hv u8_297 u7_303 u6_198 u5_187 a29 n105 n24
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c1668 h hv u9_112
  have u11_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u9_112
  have u12_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u4_193 u11_109 hv u1_304
  have u13_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u12_249 hv u4_193 u1_304
  have u14_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24747 h u13_284 a29 hv a93
  have u15_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c843 h hv u14_57
  exact c32648 h u15_141 u5_187 u10_196 u6_198 a29 u3_177 u2_162

private theorem c32650 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 8} → ¬ Q {1, 2, 6, 9} → T {1, 2, 6} → T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ Q {0, 4, 7, 9} → False := by
  classical
  intro n112 n222 a40 a29 a93 n105 n193
  have u0_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u1_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u5_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15781 h hv a29 a93 u4_116
  have u6_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14645 h hv a29 a93 u4_116
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u8_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13853 h hv a29 u7_109
  have u9_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2233 h hv a93 u7_109
  have u10_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 n193 u7_109 hv u2_304
  have u11_221 : Q {1, 2, 6, 8} := by
    by_contra hv
    exact c31365 h n222 u5_220 u8_207 u9_124 hv u6_212 a40
  have u12_52 : T {1, 4, 7} := by
    by_contra hv
    exact c780 h u10_249 hv
  have u13_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u10_249 hv n193 u2_304
  have u14_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u10_249 a29 hv
  have u15_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c19847 h u10_249 a29 hv a93
  have u16_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c19727 h u10_249 hv a93
  have u17_81 : T {2, 6, 8} := by
    by_contra hv
    exact c19800 h u10_249 u16_12 u14_67 hv
  have u18_42 : T {1, 2, 8} := by
    by_contra hv
    exact c626 h u11_221 hv
  have u19_216 : Q {1, 2, 5, 6} := by
    by_contra hv
    exact c599 h u11_221 u9_124 u8_207 u6_212 hv u5_220 n222
  have u20_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24747 h u13_284 a29 hv a93
  have u21_76 : T {2, 5, 6} := by
    by_contra hv
    exact c19798 h u10_249 u16_12 u14_67 hv
  have u22_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9793 h hv u12_52 u17_81
  have u23_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32516 h h0 hv u18_42 a40
  have u24_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32405 h h0 hv a40 u18_42
  have u25_39 : T {1, 2, 5} := by
    by_contra hv
    exact c579 h u19_216 hv
  have u26_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6434 h hv u20_57 n105
  have u27_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9330 h hv u20_57 u15_78 n112
  have u28_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10608 h hv u20_57 u15_78 n112
  have u29_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10635 h hv u12_52 u21_76
  have u30_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32464 h h0 u25_39 hv a40
  have u31_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c32566 h h0 u25_39 hv a40
  have u32_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32435 h h0 u25_39 u18_42 hv
  have u33_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c32546 h h0 u25_39 u18_42 hv
  have u34_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c31485 h u22_178 hv u28_183 u29_184 u0_133 u26_154 u27_174
  have u35_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c1343 h hv u27_174 u1_230 u24_299 u32_302 u2_304 u30_305
  have u36_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c1337 h hv u27_174 u1_230 u35_265 u24_299 u32_302 u2_304 u30_305
  have u37_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c1478 h hv u28_183 u3_239 u2_304 u23_310 u33_313 u31_315
  have u38_99 : T {3, 7, 9} := by
    by_contra hv
    exact c15888 h u11_221 u34_21 u36_90 hv
  exact c31288 h u23_310 u28_183 u31_315 u37_274 u33_313 u38_99 u3_239

theorem c32651 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 6} → T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a40 a29 a93 n105 n24
  have u0_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u1_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u2_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u3_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32649 h h0 hv a40 a29 a93 n105 n24
  have u4_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c641 h hv u3_43
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27856 h hv n24 u3_43
  have u6_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32650 h h0 hv u4_222 a40 a29 a93 n105 u2_193
  have u7_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u6_112
  have u8_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31706 h h0 u6_112 hv u0_116
  have u9_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u6_112 hv u0_116
  have u10_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17586 h hv n24 n105 u7_109
  have u11_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22486 h hv n24 n105 u7_109
  have u12_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u8_103
  have u13_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1704 h hv u9_114
  have u14_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32591 h u11_268 u10_233 a93 hv u1_177 u5_307 u12_298
  exact c1396 h u14_311 u1_177 u10_233 u11_268 u12_298 u5_307 u13_309

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases121
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32652 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {1, 2, 3, 6} → T {0, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a112 n207 a29 n105 n24
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u3_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14087 h hv a29 a112 u1_116
  have u4_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13641 h hv a29 a112 u1_116
  have u5_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13772 h hv n24 n105 u2_109
  have u6_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14202 h hv n24 n105 u2_109
  exact c31535 h h0 u5_206 u6_209 u0_210 n207 u3_208 u4_205

private theorem c32653 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a29 a93 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u2_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32651 h h0 hv a29 a93 n105 n24
  have u4_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c590 h hv u3_40
  have u5_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28418 h hv n24 u3_40
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32652 h h0 hv u4_207 a29 n105 n24
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u6_112
  have u8_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u2_193 u7_109 hv u0_304
  have u9_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u8_249 a29 hv
  have u10_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c19847 h u8_249 a29 hv a93
  have u11_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20718 h hv n24 u9_67
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1170 h hv u10_78
  have u13_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u1_116 hv u5_311 u12_291
  exact c31604 h h0 u13_200 u12_291 u11_256 u5_311

private theorem c32654 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro n311 a93 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32653 h h0 hv a93 n105 n24
  have u2_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u1_29
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u4_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u5_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u6_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u3_116 u2_200 n311 hv
  have u7_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1170 h u6_291 hv
  have u8_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31606 h h0 u6_291 hv u2_200 n311
  have u9_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25730 h u6_291 n24 hv n105
  have u10_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c25607 h u6_291 hv u9_88
  have u11_46 : T {1, 3, 6} := by
    by_contra hv
    exact c25618 h u6_291 n24 hv
  have u12_52 : T {1, 4, 7} := by
    by_contra hv
    exact c25728 h u6_291 n24 hv n105
  have u13_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10213 h hv u12_52 u7_78
  have u14_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5179 h hv u7_78 u9_88
  have u15_57 : T {1, 5, 8} := by
    by_contra hv
    exact c855 h u8_256 hv
  have u16_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c20707 h u8_256 hv u9_88
  have u17_67 : T {2, 3, 6} := by
    by_contra hv
    exact c20718 h u8_256 n24 hv
  have u18_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20828 h u8_256 n24 hv n105
  have u19_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12559 h hv u12_52 u18_73 u9_88
  have u20_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13407 h hv u12_52 u18_73 u9_88
  have u21_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c32324 h h0 u11_46 hv u6_291
  have u22_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8113 h hv u12_52 a93
  have u23_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv u15_57 u7_78 a93
  have u24_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u15_57 u7_78 a93
  have u25_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c32126 h h0 u17_67 hv u8_256
  have u26_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv u14_145 u22_166 u13_181 u24_191 u19_197 u23_202 u20_203
  have u27_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c656 h hv u21_44
  have u28_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c1012 h hv u25_68
  have u29_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27328 h hv u10_5 u16_12 u26_33
  have u30_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26480 h hv u10_5 u16_12 u26_33
  exact c1307 h u9_88 u5_172 u27_228 u28_263 u30_297 u4_300 u29_303 u0_304

private theorem c32655 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 8, 9} → T {2, 5, 8} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 1, 4, 6} → T {0, 4, 6} → T {0, 6, 7} → ¬ Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → ¬ Q {0, 4, 6, 7} → False := by
  classical
  intro a256 a78 n156 n135 a23 a31 n313 n29 a93 a116 n189
  have u0_57 : T {1, 5, 8} := by
    by_contra hv
    exact c855 h a256 hv
  have u1_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20721 h a256 a31 hv
  have u2_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv u0_57 a78 a93
  have u3_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u0_57 a78 a93
  have u4_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8905 h hv u0_57 a78 a116
  have u5_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21000 h hv n29 u1_65
  have u6_185 : Q {0, 4, 5, 6} := by
    by_contra hv
    exact c31487 h u4_171 hv n189 n135 n156 a23 u3_191
  have u7_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31500 h h0 u5_258 n313 hv u2_202
  have u8_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31767 h h0 u6_185 hv
  have u9_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c340 h u6_185 n135 n156 u4_171 n189 hv u3_191
  have u10_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31757 h h0 hv u8_120 u7_118
  exact c31817 h h0 u9_190 u10_115

private theorem c32656 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 8} → ¬ Q {2, 4, 6, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {0, 5, 6, 9} → ¬ T {0, 3, 6} → Q {2, 5, 8, 9} → ¬ Q {0, 3, 6, 9} → T {2, 5, 8} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {0, 2, 6, 9} → ¬ T {0, 1, 6} → ¬ Q {0, 1, 6, 9} → T {3, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {2, 5, 6, 8} → False := by
  classical
  intro a57 n282 n293 n203 n197 n18 a291 n181 a78 n302 n313 n166 n5 n145 a93 n162 n287
  have u0_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv a57 a78 a93
  have u1_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv a57 a78 a93
  have u2_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv n145 n166 n181 u1_191 n197 u0_202 n203
  have u3_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c31614 h h0 n293 u0_202 n313 hv
  have u4_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c31564 h h0 n302 hv n282 u1_191
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31459 h h0 n282 u1_191 u4_247 hv
  have u6_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23820 h hv n5 n18 u2_33
  have u7_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25368 h hv n5 n18 u2_33
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31500 h h0 u3_258 n313 hv u0_202
  have u9_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15510 h hv u2_33 u5_107 u8_118
  have u10_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22510 h hv u2_33 u5_107 u8_118
  exact c1171 h a291 n162 u9_218 u10_268 u6_278 n287 u7_289

private theorem c32657 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 5, 8} → T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a78 a93 n105 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32654 h h0 hv a93 n105 n24
  have u3_52 : T {1, 4, 7} := by
    by_contra hv
    exact c28528 h u2_311 n24 hv n105
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28413 h u2_311 hv u3_52
  have u5_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c172 h hv u4_12
  have u6_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28530 h u2_311 n24 hv n105
  have u7_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28407 h u2_311 hv u6_73
  have u8_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c67 h hv u7_5
  have u9_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28418 h u2_311 n24 hv
  have u10_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32526 h h0 hv u2_311 u9_40
  have u11_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28416 h u2_311 hv u10_41
  have u12_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32653 h h0 hv a93 n105 n24
  have u13_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27158 h hv u12_29 u10_41
  have u14_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32524 h h0 u2_311 hv u9_40
  have u15_31 : T {0, 6, 7} := by
    by_contra hv
    exact c28420 h u2_311 hv u14_38
  have u16_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28700 h hv u12_29 u14_38
  have u17_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8113 h hv u3_52 a93
  have u18_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5173 h hv u6_73 a93
  have u19_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u12_29
  have u20_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u12_29
  have u21_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u22_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u23_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u24_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u25_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u26_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10213 h hv u3_52 a78
  have u27_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32655 h h0 hv a78 u5_156 u8_135 u11_23 u15_31 u16_313 u12_29 a93 u22_116 u25_189
  have u28_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 hv u19_200 u27_256 u2_311
  have u29_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25730 h u28_291 n24 hv n105
  have u30_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c25613 h u28_291 hv u3_52
  have u31_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c25621 h u28_291 u15_31 hv
  have u32_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c25617 h u28_291 u11_23 hv
  have u33_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12559 h hv u3_52 u6_73 u29_88
  have u34_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13407 h hv u3_52 u6_73 u29_88
  have u35_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c25900 h hv u12_29 u31_44
  have u36_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24358 h hv u12_29 u32_47
  have u37_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32656 h h0 hv u36_282 u35_293 u34_203 u33_197 u30_18 u28_291 u26_181 a78 u13_302 u16_313 u17_166 u7_5 u18_145 a93 u21_162 u23_287
  have u38_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c851 h hv u37_57
  have u39_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24632 h hv u30_18 u37_57
  have u40_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c31589 h h0 hv u38_252 u20_196 u23_287
  have u41_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c31574 h h0 hv u39_284 u24_193 u1_304
  have u42_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32634 h h0 u40_307 u38_252 u23_287 hv
  have u43_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31572 h h0 u41_249 u24_193 hv u1_304 u39_284
  exact c31643 h h0 u43_109 u42_112

theorem c32658 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 5, 8} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro a93 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u3_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32653 h h0 hv a93 n105 n24
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u3_29
  have u5_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32654 h h0 hv a93 n105 n24
  have u6_40 : T {1, 2, 6} := by
    by_contra hv
    exact c28418 h u5_311 n24 hv
  have u7_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28530 h u5_311 n24 hv n105
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32524 h h0 u5_311 hv u6_40
  have u9_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32526 h h0 hv u5_311 u6_40
  have u10_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u8_38
  have u11_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c605 h hv u9_41
  have u12_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c32657 h h0 hv a93 n105 n24
  have u13_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1170 h hv u12_78
  have u14_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 u13_291 u4_200 hv u5_311
  have u15_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c20713 h u14_256 hv u7_73
  have u16_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19732 h hv u15_18 u12_78
  have u17_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31322 h h0 u2_193 hv u16_249 u0_304
  have u18_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13772 h hv n24 n105 u17_109
  have u19_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14202 h hv n24 n105 u17_109
  have u20_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13852 h hv u3_29 u17_109
  exact c31535 h h0 u18_206 u19_209 u1_210 u20_207 u11_208 u10_205

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases122
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32659 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 5, 8, 9} → ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro n291 n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32658 h h0 hv n105 n24
  have u2_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1395 h hv u1_93
  have u3_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u4_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u3_116 hv u2_311 n291
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c435 h u5_200 hv
  have u7_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c31604 h h0 u5_200 n291 hv u2_311
  have u8_88 : T {3, 4, 7} := by
    by_contra hv
    exact c20830 h u7_256 n24 hv n105
  have u9_67 : T {2, 3, 6} := by
    by_contra hv
    exact c20718 h u7_256 n24 hv
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c12867 h u5_200 hv u8_88
  have u11_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19739 h hv u6_29 u9_67
  have u12_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c590 h hv u10_40
  have u13_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31322 h h0 u4_193 hv u11_249 u0_304
  have u14_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32652 h h0 hv u12_207 u6_29 n105 n24
  exact c31643 h h0 u13_109 u14_112

theorem c32660 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ T {0, 4, 7} → False := by
  classical
  intro n105 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u1_49
  have u3_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u4_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32658 h h0 hv n105 n24
  have u5_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1391 h hv u4_93
  have u6_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c32659 h h0 hv n105 n24
  have u7_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25730 h u6_291 n24 hv n105
  have u8_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c25607 h u6_291 hv u7_88
  have u9_46 : T {1, 3, 6} := by
    by_contra hv
    exact c25618 h u6_291 n24 hv
  have u10_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24626 h hv u8_5 u4_93
  have u11_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c32324 h h0 u9_46 hv u6_291
  have u12_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c32326 h h0 u9_46 hv u6_291
  have u13_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c31574 h h0 hv u10_284 u3_193 u0_304
  have u14_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31572 h h0 u13_249 u3_193 hv u0_304 u10_284
  have u15_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12336 h hv u11_44 u12_47 u1_49
  have u16_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u14_109 hv
  have u17_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c31587 h h0 hv u5_307 u15_196 u2_287
  exact c32634 h h0 u5_307 u17_252 u2_287 u16_112

private theorem c32661 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 4} → ¬ Q {0, 1, 3, 5} → ¬ Q {0, 1, 3, 8} → ¬ T {2, 5, 8} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 1, 7, 8} → T {3, 5, 9} → T {3, 8, 9} → ¬ Q {1, 2, 7, 9} → ¬ T {0, 2, 9} → Q {0, 5, 6, 8} → Q {1, 5, 6, 8} → ¬ T {4, 7, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro n44 n129 n132 n78 n140 n146 a94 a100 n224 n15 a196 a252 n109 n24
  have u0_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u1_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u2_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3072 h hv n78 n109
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c20156 h a252 n24 hv
  have u4_32 : T {0, 6, 8} := by
    by_contra hv
    exact c476 h a196 hv
  have u5_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18757 h hv u4_32 u3_70
  have u6_27 : T {0, 5, 6} := by
    by_contra hv
    exact c403 h a196 hv
  have u7_248 : ¬ Q {1, 4, 7, 8} := by
    intro hv
    exact c19597 h hv u6_27 u3_70
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u9_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u8_105 hv
  have u10_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 a252 hv u3_70
  have u11_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4882 h hv u10_65 u9_116
  have u12_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12317 h a196 hv u3_70
  have u13_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20260 h a252 n24 hv n109
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 n109 hv
  have u15_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c1625 h hv n109
  have u16_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c348 h hv n24
  have u17_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c648 h hv n44
  have u18_38 : T {1, 2, 4} := by
    by_contra hv
    exact c12338 h a196 hv n44 u12_52
  have u19_84 : T {2, 7, 9} := by
    by_contra hv
    exact c12310 h a196 n44 hv
  have u20_90 : T {3, 4, 9} := by
    by_contra hv
    exact c12396 h a196 n44 u10_65 hv
  have u21_131 : Q {0, 1, 3, 7} := by
    by_contra hv
    exact c31533 h h0 n129 n132 u17_128 u0_133 hv u2_130
  have u22_75 : ¬ T {2, 4, 9} := by
    intro hv
    exact c12375 h a196 u18_38 u13_73 hv
  have u23_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c20151 h a252 hv u19_84
  have u24_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2369 h hv u20_90 u14_112
  have u25_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20957 h hv u3_70 u20_90 a94
  have u26_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20117 h hv u3_70 u20_90 a100
  have u27_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16097 h hv u6_27 u20_90
  have u28_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15257 h hv u4_32 u20_90
  have u29_147 : Q {0, 1, 7, 9} := by
    by_contra hv
    exact c81 h u21_131 u24_125 u16_136 n140 u11_143 n146 hv
  have u30_103 : T {4, 5, 8} := by
    by_contra hv
    exact c3304 h u21_131 n78 hv u9_116
  have u31_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c3219 h u21_131 hv u30_103
  have u32_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20510 h hv n15 u22_75 u31_82
  have u33_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18268 h hv n15 u22_75 u31_82
  have u34_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17426 h hv n15 u22_75 u31_82
  have u35_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c20990 h hv u23_16 n78
  have u36_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c931 h hv n146 u27_223 u33_238 u7_248 u32_254 u25_257
  have u37_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c841 h hv n140 u28_217 u34_232 u5_242 u26_251 u32_254
  exact c934 h u29_147 n224 u1_239 u15_249 u37_255 u35_258 u36_260

theorem c32662_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 5, 8} → T {3, 4, 7} → ¬ T {4, 7, 9} → ¬ T {0, 4, 7} → False := by
  classical
  intro n93 a88 n109 n24
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u2_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 n109 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u3_105 hv
  have u5_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13844 h hv n24 u4_116
  have u6_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25056 h hv n24 u0_49
  have u7_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u8_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1391 h hv n93
  have u9_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32590 h h0 n93 u7_189 u3_105 hv
  have u10_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c32634 h h0 u8_307 hv u6_287 u2_112
  have u11_57 : T {1, 5, 8} := by
    by_contra hv
    exact c851 h u10_252 hv
  have u12_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31587 h h0 u10_252 u8_307 hv u6_287
  have u13_70 : T {2, 3, 9} := by
    by_contra hv
    exact c20156 h u10_252 n24 hv
  have u14_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32085 h h0 u10_252 hv u13_70
  have u15_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c32086 h h0 u10_252 u13_70 hv
  have u16_73 : T {2, 4, 7} := by
    by_contra hv
    exact c20260 h u10_252 n24 hv n109
  have u17_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c20155 h u10_252 hv u16_73
  have u18_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c20149 h u10_252 hv a88
  have u19_26 : T {0, 4, 9} := by
    by_contra hv
    exact c20158 h u10_252 hv u15_68
  have u20_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10219 h hv u11_57 u16_73
  have u21_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c12309 h u12_196 hv a88
  have u22_54 : T {1, 4, 9} := by
    by_contra hv
    exact c12354 h u12_196 u21_43 u0_49 hv
  have u23_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12317 h u12_196 hv u13_70
  have u24_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv u9_29 u13_70
  have u25_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c969 h hv u14_65
  have u26_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c1016 h hv u15_68
  have u27_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c643 h hv u21_43
  have u28_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6004 h hv u23_52 u4_116
  have u29_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22904 h hv n24 u23_52 n109
  have u30_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22196 h hv n24 u23_52 n109
  have u31_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 hv u24_245 u3_105 u7_189
  have u32_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c1006 h hv u28_151 u5_207 u25_262 u30_266 u26_270 u29_271
  have u33_72 : T {2, 4, 6} := by
    by_contra hv
    exact c1076 h u31_280 hv
  have u34_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u31_280 u24_245 u7_189 hv
  have u35_100 : T {3, 8, 9} := by
    by_contra hv
    exact c24172 h u31_280 u17_21 u0_49 hv
  have u36_8 : T {0, 1, 9} := by
    by_contra hv
    exact c24068 h u31_280 hv n93
  have u37_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c32210 h h0 u31_280 hv u36_8
  have u38_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c32209 h h0 u31_280 hv u36_8
  have u39_94 : T {3, 5, 9} := by
    by_contra hv
    exact c24170 h u31_280 u17_21 u0_49 hv
  have u40_146 : ¬ Q {0, 1, 7, 8} := by
    intro hv
    exact c5313 h hv u33_72 u39_94
  have u41_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4471 h hv u33_72 u35_100
  have u42_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c26979 h u34_300 u9_29 u11_57 hv
  have u43_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c95 h hv u37_7
  have u44_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c50 h hv u38_4
  have u45_44 : T {1, 3, 4} := by
    by_contra hv
    exact c32661 h h0 hv u44_129 u43_132 u42_78 u41_140 u40_146 u39_94 u35_100 u27_224 u18_15 u12_196 u10_252 n109 n24
  have u46_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c12311 h u12_196 u45_44 hv
  have u47_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c31881 h h0 u45_44 hv u12_196
  have u48_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c12399 h u12_196 u45_44 a88 hv
  have u49_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c12341 h u12_196 hv u45_44 u22_54
  have u50_41 : T {1, 2, 7} := by
    by_contra hv
    exact c12380 h u12_196 hv u15_68 u46_84
  have u51_75 : T {2, 4, 9} := by
    by_contra hv
    exact c12390 h u12_196 u21_43 hv u46_84
  have u52_13 : T {0, 2, 7} := by
    by_contra hv
    exact c20220 h u10_252 hv u15_68 u46_84
  have u53_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c701 h hv u47_47
  have u54_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1346 h hv u48_90
  have u55_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9922 h hv u49_38 u4_116
  have u56_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28083 h hv u52_13 u50_41 u16_73
  have u57_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28931 h hv u52_13 u50_41 u16_73
  have u58_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27827 h hv u19_26 u22_54 u51_75
  have u59_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28667 h hv u19_26 u22_54 u51_75
  have u60_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1454 h hv u20_181 u1_237 u32_272 u54_302 u56_308 u57_314
  exact c1420 h u34_300 u55_179 u53_235 u26_270 u58_306 u59_312 u60_313

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32662_oai := @OAI.BorsukNine.FiniteObstruction.c32662_oai
