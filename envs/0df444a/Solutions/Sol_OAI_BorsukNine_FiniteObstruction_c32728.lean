-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32728
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:33:41.930512+00:00
-- url     : https://prove2.me/submissions/ada14d57-e8b6-4434-bf60-7a871a4bbf4c

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
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32671
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32720

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

theorem c108 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {0, 1, 9} → False := by
  intro a127 n8
  exact n8 (h.down {0, 1, 2, 9} {0, 1, 9} a127 (by decide) (by decide))

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

theorem c193 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {0, 2, 7} → False := by
  intro a167 n13
  exact n13 (h.down {0, 2, 7, 8} {0, 2, 7} a167 (by decide) (by decide))

theorem c208 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {0, 2, 8} → False := by
  intro a167 n14
  exact n14 (h.down {0, 2, 7, 8} {0, 2, 8} a167 (by decide) (by decide))

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

theorem c283 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ T {0, 3, 7} → False := by
  intro a182 n19
  exact n19 (h.down {0, 3, 7, 8} {0, 3, 7} a182 (by decide) (by decide))

theorem c284 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 7, 9} → False := by
  intro a182 n131 n152 n172 n176 n179 n183
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 8} {0, 3, 7} a182 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n131 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n172 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n183 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 7} = {0, 3, 7, 9} by decide)) hS)

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

theorem c298 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ T {0, 3, 8} → False := by
  intro a182 n20
  exact n20 (h.down {0, 3, 7, 8} {0, 3, 8} a182 (by decide) (by decide))

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

theorem c313 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 9} → False := by
  intro a183 n21
  exact n21 (h.down {0, 3, 7, 9} {0, 3, 9} a183 (by decide) (by decide))

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

theorem c497 (h : TenSystem T Q) :
    T {0, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a34 n146 n167 n182 n192 n198 n201 n204
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 7, 8} a34
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n201 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c501 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a167 n146 n182 n192 n198 n201 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 7, 8} {0, 7, 8} a167 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n182 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n201 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c503 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a182 n146 n167 n192 n198 n201 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 8} {0, 7, 8} a182 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n201 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c509 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a201 n146 n167 n182 n192 n198 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 7, 8} {0, 7, 8} a201 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

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

theorem c575 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {1, 2, 5} → False := by
  intro a206 n39
  exact n39 (h.down {1, 2, 3, 5} {1, 2, 5} a206 (by decide) (by decide))

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

theorem c588 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {1, 2, 6} → False := by
  intro a124 n40
  exact n40 (h.down {0, 1, 2, 6} {1, 2, 6} a124 (by decide) (by decide))

theorem c592 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ T {1, 2, 6} → False := by
  intro a212 n40
  exact n40 (h.down {1, 2, 4, 6} {1, 2, 6} a212 (by decide) (by decide))

theorem c594 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 6} → False := by
  intro a216 n40
  exact n40 (h.down {1, 2, 5, 6} {1, 2, 6} a216 (by decide) (by decide))

theorem c600 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {1, 2, 6} → False := by
  intro a222 n40
  exact n40 (h.down {1, 2, 6, 9} {1, 2, 6} a222 (by decide) (by decide))

theorem c603 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {1, 2, 7} → False := by
  intro a125 n41
  exact n41 (h.down {0, 1, 2, 7} {1, 2, 7} a125 (by decide) (by decide))

theorem c607 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {1, 2, 7} → False := by
  intro a213 n41
  exact n41 (h.down {1, 2, 4, 7} {1, 2, 7} a213 (by decide) (by decide))

theorem c615 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 7} → False := by
  intro a224 n41
  exact n41 (h.down {1, 2, 7, 9} {1, 2, 7} a224 (by decide) (by decide))

theorem c620 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {1, 2, 8} → False := by
  intro a209 n42
  exact n42 (h.down {1, 2, 3, 8} {1, 2, 8} a209 (by decide) (by decide))

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

theorem c638 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a215 n127 n210 n219 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 4, 9} {1, 2, 9} a215 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c646 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → False := by
  intro a225 n127 n210 n215 n219 n222 n224
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 8, 9} {1, 2, 9} a225 (by decide) (by decide)
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
  · exact hne (by decide)
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

theorem c716 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {1, 3, 8} → False := by
  intro a236 n48
  exact n48 (h.down {1, 3, 6, 8} {1, 3, 8} a236 (by decide) (by decide))

theorem c725 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a210 n49
  exact n49 (h.down {1, 2, 3, 9} {1, 3, 9} a210 (by decide) (by decide))

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

theorem c851 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {1, 5, 8} → False := by
  intro a252 n57
  exact n57 (h.down {1, 5, 6, 8} {1, 5, 8} a252 (by decide) (by decide))

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

theorem c992 (h : TenSystem T Q) :
    T {2, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 6, 9} → False := by
  intro a67 n151 n207 n262 n266 n270 n271 n272
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 6} a67
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
  · exact n272 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 6} = {2, 3, 6, 9} by decide)) hS)

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

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

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

theorem c1300 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a296 n171 n227 n262 n300 n301 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 6} {3, 4, 6} a296 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1304 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 9} → False := by
  intro a301 n171 n227 n262 n296 n300 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 8} {3, 4, 6} a301 (by decide) (by decide)
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
  · exact hne (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1305 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 4, 6} → False := by
  intro a302 n87
  exact n87 (h.down {3, 4, 6, 9} {3, 4, 6} a302 (by decide) (by decide))

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

theorem c1319 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 7, 9} → False := by
  intro a303 n172 n228 n263 n297 n300 n304
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 8} {3, 4, 7} a303 (by decide) (by decide)
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
  · exact hne (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

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

theorem c1361 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {3, 5, 6} → False := by
  intro a306 n91
  exact n91 (h.down {3, 5, 6, 7} {3, 5, 6} a306 (by decide) (by decide))

theorem c1362 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 6, 9} → False := by
  intro a306 n175 n231 n266 n296 n307 n308
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 7} {3, 5, 6} a306 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 6} = {3, 5, 6, 9} by decide)) hS)

theorem c1376 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {3, 5, 7} → False := by
  intro a306 n92
  exact n92 (h.down {3, 5, 6, 7} {3, 5, 7} a306 (by decide) (by decide))

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

theorem c1422 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 7, 9} → False := by
  intro a306 n179 n235 n270 n300 n312 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 7} {3, 6, 7} a306 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 7} = {3, 6, 7, 8} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

theorem c1424 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 9} → False := by
  intro a312 n179 n235 n270 n300 n306 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {3, 6, 7} a312 (by decide) (by decide)
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
  · exact hne (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

theorem c1426 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 8} → False := by
  intro a313 n179 n235 n270 n300 n306 n312
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 9} {3, 6, 7} a313 (by decide) (by decide)
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
  · exact hne (by decide)

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

theorem c1438 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {3, 6, 8} → False := by
  intro a312 n96
  exact n96 (h.down {3, 6, 7, 8} {3, 6, 8} a312 (by decide) (by decide))

theorem c1439 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a312 n180 n236 n271 n301 n307 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {3, 6, 8} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1452 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a308 n181 n237 n272 n302 n313 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 9} {3, 6, 9} a308 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1453 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {3, 6, 9} → False := by
  intro a313 n97
  exact n97 (h.down {3, 6, 7, 9} {3, 6, 9} a313 (by decide) (by decide))

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

theorem c1468 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {3, 7, 8} → False := by
  intro a312 n98
  exact n98 (h.down {3, 6, 7, 8} {3, 7, 8} a312 (by decide) (by decide))

theorem c1469 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 7, 8, 9} → False := by
  intro a312 n182 n238 n273 n303 n309 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {3, 7, 8} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n182 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 7, 8} = {3, 7, 8, 9} by decide)) hS)

theorem c1479 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a304 n99
  exact n99 (h.down {3, 4, 7, 9} {3, 7, 9} a304 (by decide) (by decide))

theorem c1484 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a313 n183 n239 n274 n304 n310 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 9} {3, 7, 9} a313 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c1504 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a185 n241 n276 n296 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 6} {4, 5, 6} a185 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
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

theorem c1547 (h : TenSystem T Q) :
    T {4, 5, 9} → ¬ Q {0, 4, 5, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 5, 8, 9} → False := by
  intro a104 n188 n244 n279 n299 n318 n320 n321
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 9} a104
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n188 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 9} = {0, 4, 5, 9} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact n299 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1549 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 5, 8, 9} → False := by
  intro a188 n244 n279 n299 n318 n320 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 9} {4, 5, 9} a188 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n244 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact n299 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1584 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a301 n106
  exact n106 (h.down {3, 4, 6, 8} {4, 6, 8} a301 (by decide) (by decide))

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

theorem c1594 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a191 n247 n282 n302 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 9} {4, 6, 9} a191 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
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

theorem c1608 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a192 n108
  exact n108 (h.down {0, 4, 7, 8} {4, 7, 8} a192 (by decide) (by decide))

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

theorem c1659 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a306 n111
  exact n111 (h.down {3, 5, 6, 7} {5, 6, 7} a306 (by decide) (by decide))

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

theorem c1684 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 6, 8, 9} → False := by
  intro a197 n253 n288 n308 n318 n327 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 9} {5, 6, 9} a197 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 9} = {3, 5, 6, 9} by decide)) hS)
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

theorem c1698 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a198 n114
  exact n114 (h.down {0, 5, 7, 8} {5, 7, 8} a198 (by decide) (by decide))

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

theorem c1749 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a312 n117
  exact n117 (h.down {3, 6, 7, 8} {6, 7, 8} a312 (by decide) (by decide))

theorem c1764 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a313 n118
  exact n118 (h.down {3, 6, 7, 9} {6, 7, 9} a313 (by decide) (by decide))

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

theorem c1826 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a121 n101 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1828 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a121 n102 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1834 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 8} → ¬ T {4, 6, 9} → False := by
  intro a121 n101 n106 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
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

theorem c1843 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a121 a102 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c1844 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a121 n105 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c1846 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → False := by
  intro a121 n103 n106 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)

theorem c1847 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {4, 6, 8} → T {4, 7, 8} → False := by
  intro a121 a103 a106 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c1848 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 6, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n103 n106 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1850 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n103 n108 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1855 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a121 a104 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

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

theorem c1858 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {4, 7, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n104 n109 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

theorem c1860 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n107 n109 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

theorem c1865 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a121 a101 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 6} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c1866 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {5, 6, 8} → ¬ T {5, 6, 9} → False := by
  intro a121 n101 n112 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 6} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) ht)

theorem c1867 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {5, 6, 8} → T {5, 6, 9} → False := by
  intro a121 a101 a112 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 6} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

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

theorem c1886 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {5, 6, 9} → ¬ T {5, 7, 9} → False := by
  intro a121 n104 n113 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) ht)

theorem c1893 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a121 a113 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c1901 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 7} → T {6, 7, 8} → T {6, 7, 9} → False := by
  intro a121 a111 a117 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c1907 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a121 a106 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c1908 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 8} → ¬ T {6, 7, 8} → ¬ T {6, 8, 9} → False := by
  intro a121 n112 n117 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

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

theorem c1916 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n113 n118 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

theorem c1919 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {5, 7, 8} → T {6, 7, 8} → False := by
  intro a121 a108 a114 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)

theorem c1920 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {5, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n108 n114 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1923 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a121 a108 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c1931 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {6, 7, 9} → T {7, 8, 9} → False := by
  intro a121 a109 a118 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 9} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c1943 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {7, 8, 9} → False := by
  intro a122 a91 a120
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 6} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a91 a120

theorem c1951 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 7} → T {5, 8, 9} → False := by
  intro a122 a95 a116
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 7} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a95 a116

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

theorem c2653 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 7} → T {4, 6, 8} → False := by
  intro a127 a92 a106
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a92 a106

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

theorem c2661 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 7, 8} → T {4, 5, 6} → False := by
  intro a127 a98 a101
  have hc := h.complementary {0, 1, 2, 9} {3, 7, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 7, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a98 a101

theorem c2861 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a128 a78 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 4} {5, 8} {2, 6, 9} a128 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c3221 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 8, 9} → T {4, 5, 6} → False := by
  intro a131 a85 a101
  have hc := h.complementary {0, 1, 3, 7} {2, 8, 9} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 8, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a85 a101

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

theorem c4733 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a141 a97 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {6, 9} {3, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

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

theorem c5292 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a145 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 9} {5, 8} {3, 4, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c5306 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → ¬ T {2, 3, 6} → ¬ T {4, 5, 9} → False := by
  intro a146 n67 n104
  have hc := h.complementary {0, 1, 7, 8} {2, 3, 6} a146 (by decide) (by decide)
  have he : ( {0, 1, 7, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {4, 5, 9} := by decide
  rw [he] at hc
  exact n67 (hc.mpr n104)

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

theorem c6021 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 8, 9} → T {4, 5, 7} → False := by
  intro a151 a64 a102
  have hc := h.complementary {0, 2, 3, 6} {1, 8, 9} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 8, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a64 a102

theorem c6161 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 8, 9} → T {4, 5, 6} → False := by
  intro a152 a64 a101
  have hc := h.complementary {0, 2, 3, 7} {1, 8, 9} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 8, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a64 a101

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

theorem c6669 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {3, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a155 a96 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {6, 8} {3, 7, 9} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) a96)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c6685 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {3, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a155 a98 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {7, 8} {3, 6, 9} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) a98)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c6708 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 3, 9} → ¬ T {5, 7, 8} → False := by
  intro a156 n49 n114
  have hc := h.complementary {0, 2, 4, 6} {1, 3, 9} a156 (by decide) (by decide)
  have he : ( {0, 2, 4, 6} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n114)

theorem c6848 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 3, 9} → ¬ T {5, 6, 8} → False := by
  intro a157 n49 n112
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 9} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n112)

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

theorem c7081 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {3, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a158 a91 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 6} {3, 7, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c7089 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {3, 5, 7} → T {5, 6, 7} → T {5, 7, 9} → False := by
  intro a158 a92 a111 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 7} {3, 6, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) a115)

theorem c7197 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {3, 5, 6} → T {3, 6, 7} → T {3, 6, 8} → False := by
  intro a159 a91 a95 a96
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {3, 6} {5, 7, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) a96)

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

theorem c8232 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {5, 8} {3, 4, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c8248 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {1, 3, 9} → ¬ T {4, 5, 6} → False := by
  intro a167 n49 n101
  have hc := h.complementary {0, 2, 7, 8} {1, 3, 9} a167 (by decide) (by decide)
  have he : ( {0, 2, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n101)

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

theorem c8915 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a171 a58 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {5, 9} {1, 7, 8} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c8939 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a171 a64 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {8, 9} {1, 5, 7} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c9079 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a172 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {8, 9} {1, 5, 6} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c9362 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {1, 2, 4} → ¬ T {7, 8, 9} → False := by
  intro a175 n38 n120
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 4} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n120)

theorem c9363 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 2, 4} → T {7, 8, 9} → False := by
  intro a175 a38 a120
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 4} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a120

theorem c9503 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 2, 4} → T {6, 8, 9} → False := by
  intro a176 a38 a119
  have hc := h.complementary {0, 3, 5, 7} {1, 2, 4} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 2, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a119

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

theorem c10062 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {1, 2, 4} → ¬ T {5, 7, 9} → False := by
  intro a180 n38 n115
  have hc := h.complementary {0, 3, 6, 8} {1, 2, 4} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n115)

theorem c10202 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 4} → ¬ T {5, 7, 8} → False := by
  intro a181 n38 n114
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 4} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n114)

theorem c10204 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 5} → ¬ T {4, 7, 8} → False := by
  intro a181 n39 n108
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 5} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n108)

theorem c10206 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 7} → ¬ T {4, 5, 8} → False := by
  intro a181 n41 n103
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n103)

theorem c10343 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 4} → T {5, 6, 9} → False := by
  intro a182 a38 a113
  have hc := h.complementary {0, 3, 7, 8} {1, 2, 4} a182 (by decide) (by decide)
  have he : ( {0, 3, 7, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a113

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

theorem c10482 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 4} → ¬ T {5, 6, 8} → False := by
  intro a183 n38 n112
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 4} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n112)

theorem c10484 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 5} → ¬ T {4, 6, 8} → False := by
  intro a183 n39 n106
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 5} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n106)

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

theorem c12328 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → ¬ T {1, 2, 7} → ¬ T {1, 2, 9} → False := by
  intro a196 n38 n41 n43
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 2} {4, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) ht)

theorem c12443 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 2, 3} → T {4, 7, 8} → False := by
  intro a197 a37 a108
  have hc := h.complementary {0, 5, 6, 9} {1, 2, 3} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a108

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

theorem c13425 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 2, 4} → T {3, 5, 6} → False := by
  intro a204 a38 a91
  have hc := h.complementary {0, 7, 8, 9} {1, 2, 4} a204 (by decide) (by decide)
  have he : ( {0, 7, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a38 a91

theorem c13567 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 8} → T {6, 7, 9} → False := by
  intro a205 a29 a118
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a118

theorem c13702 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {0, 4, 6} → ¬ T {7, 8, 9} → False := by
  intro a206 n23 n120
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 6} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n120)

theorem c13709 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {6, 7, 8} → False := by
  intro a206 a26 a117
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 9} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a26 a117

theorem c13775 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a206 a24 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {4, 7} {0, 8, 9} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c13845 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 4, 7} → T {5, 8, 9} → False := by
  intro a207 a24 a116
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a116

theorem c13993 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 8} → T {4, 6, 9} → False := by
  intro a208 a29 a107
  have hc := h.complementary {1, 2, 3, 7} {0, 5, 8} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a107

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

theorem c14095 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 9} → T {5, 6, 9} → T {5, 8, 9} → False := by
  intro a208 a30 a113 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {5, 9} {0, 6, 8} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c14119 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a208 a36 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {8, 9} {0, 5, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c14127 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 7} → T {5, 6, 9} → False := by
  intro a209 a24 a113
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 7} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a113

theorem c14194 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a209 n23 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 6} {0, 7, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c14211 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a209 a26 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 8} {4, 9} {0, 6, 7} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

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

theorem c14975 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 5, 8} → T {3, 6, 7} → False := by
  intro a215 a29 a95
  have hc := h.complementary {1, 2, 4, 9} {0, 5, 8} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a95

theorem c15077 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {3, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a215 a93 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 9} {5, 8} {3, 6, 7} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

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

theorem c15533 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 4, 7} → T {3, 6, 8} → False := by
  intro a219 a24 a96
  have hc := h.complementary {1, 2, 5, 9} {0, 4, 7} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a96

theorem c15538 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 6, 8} → ¬ T {3, 4, 7} → False := by
  intro a219 n32 n88
  have hc := h.complementary {1, 2, 5, 9} {0, 6, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n88)

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

theorem c16047 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 8} → False := by
  intro a222 a24 a102 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 9} {4, 7} {0, 5, 8} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c16239 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 5, 8} → T {3, 4, 6} → False := by
  intro a224 a29 a87
  have hc := h.complementary {1, 2, 7, 9} {0, 5, 8} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a87

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

theorem c16375 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 4, 7} → T {3, 5, 6} → False := by
  intro a225 a24 a91
  have hc := h.complementary {1, 2, 8, 9} {0, 4, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a24 a91

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

theorem c16755 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 5, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a227 a30 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 6} {5, 9} {0, 7, 8} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c16779 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a227 a36 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 6} {8, 9} {0, 5, 7} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c16921 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {2, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a228 a85 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {8, 9} {2, 5, 6} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) a85)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c17211 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 7} → T {2, 8, 9} → False := by
  intro a231 a24 a85
  have hc := h.complementary {1, 3, 5, 6} {0, 4, 7} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a85

theorem c17298 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a231 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 6} {4, 7} {0, 8, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c17299 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a231 a24 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {4, 7} {0, 8, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c18007 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 9} → False := by
  intro a236 a24 a102 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {4, 7} {0, 5, 9} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c18631 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a241 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {0, 3} {2, 7, 8} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

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

theorem c19055 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a244 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {0, 3} {2, 7, 8} a244 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
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

theorem c19753 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a249 a9 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {0, 3} {2, 5, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

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

theorem c20205 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 9} → False := by
  intro a252 a9 a65 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {2, 3} {0, 4, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

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

theorem c20315 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a253 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 9} {0, 3} {2, 7, 8} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

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

theorem c21657 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {1, 5, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a262 a58 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {5, 9} {1, 7, 8} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c21681 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {1, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a262 a64 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {8, 9} {1, 5, 7} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

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

theorem c21821 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a263 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {8, 9} {1, 5, 6} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

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

theorem c22111 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 7} → T {1, 8, 9} → False := by
  intro a266 a24 a64
  have hc := h.complementary {2, 3, 5, 6} {0, 4, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a64

theorem c22198 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a266 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 6} {4, 7} {0, 8, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22199 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a266 a24 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {4, 7} {0, 8, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c22907 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 9} → False := by
  intro a271 a24 a102 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {4, 7} {0, 5, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c23047 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 8} → False := by
  intro a272 a24 a102 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {4, 7} {0, 5, 8} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c23210 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → ¬ T {0, 5, 9} → ¬ T {4, 5, 9} → ¬ T {5, 6, 9} → False := by
  intro a273 n30 n104 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 7, 8} {5, 9} {0, 4, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n30 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) ht)

theorem c23233 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 4, 6} → T {1, 5, 8} → False := by
  intro a274 a23 a57
  have hc := h.complementary {2, 3, 7, 9} {0, 4, 6} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a23 a57

theorem c23352 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a274 n57 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 7, 9} {5, 8} {1, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

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

theorem c23531 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a276 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {0, 3} {1, 7, 8} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

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

theorem c23955 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a279 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {0, 3} {1, 7, 8} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24075 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 3, 9} → T {1, 5, 8} → False := by
  intro a280 a21 a57
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a57

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

theorem c24375 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a282 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {0, 3} {1, 7, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

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

theorem c25215 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a288 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 9} {0, 3} {1, 7, 8} a288 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c25351 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a289 a2 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {0, 3} {1, 4, 6} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

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

theorem c26303 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {7, 8, 9} → False := by
  intro a296 a1 a120
  have hc := h.complementary {3, 4, 5, 6} {0, 1, 2} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 1, 2} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a120

theorem c26331 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a296 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {0, 2} {1, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

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

theorem c26755 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a299 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {0, 2} {1, 7, 8} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

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

theorem c27159 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 5, 8} → T {1, 2, 7} → False := by
  intro a302 a29 a41
  have hc := h.complementary {3, 4, 6, 9} {0, 5, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a41

theorem c27160 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 7, 8} → ¬ T {1, 2, 5} → False := by
  intro a302 n34 n39
  have hc := h.complementary {3, 4, 6, 9} {0, 7, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 7, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n34 (hc.mpr n39)

theorem c27175 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a302 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {0, 2} {1, 7, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c27205 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 8} → False := by
  intro a302 a1 a39 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {1, 2} {0, 5, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

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

theorem c27703 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 1, 2} → T {4, 8, 9} → False := by
  intro a306 a1 a110
  have hc := h.complementary {3, 5, 6, 7} {0, 1, 2} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a110

theorem c27710 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 2, 4} → ¬ T {1, 8, 9} → False := by
  intro a306 n10 n64
  have hc := h.complementary {3, 5, 6, 7} {0, 2, 4} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n64)

theorem c27718 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 4, 9} → ¬ T {1, 2, 8} → False := by
  intro a306 n26 n42
  have hc := h.complementary {3, 5, 6, 7} {0, 4, 9} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n42)

theorem c27720 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 8, 9} → ¬ T {1, 2, 4} → False := by
  intro a306 n36 n38
  have hc := h.complementary {3, 5, 6, 7} {0, 8, 9} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n36 (hc.mpr n38)

theorem c27721 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 8, 9} → T {1, 2, 4} → False := by
  intro a306 a36 a38
  have hc := h.complementary {3, 5, 6, 7} {0, 8, 9} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a36 a38

theorem c27838 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 8, 9} → ¬ T {2, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a306 n36 n85 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 7} {8, 9} {0, 2, 4} a306 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n36 (Eq.mp (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) ht)
  · exact n85 (Eq.mp (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)

theorem c27843 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {4, 7, 9} → False := by
  intro a307 a1 a109
  have hc := h.complementary {3, 5, 6, 8} {0, 1, 2} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a109

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

theorem c27983 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 1, 2} → T {4, 7, 8} → False := by
  intro a308 a1 a108
  have hc := h.complementary {3, 5, 6, 9} {0, 1, 2} a308 (by decide) (by decide)
  have he : ( {3, 5, 6, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a108

theorem c28015 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a308 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {0, 2} {1, 7, 8} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

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

theorem c28263 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {4, 6, 8} → False := by
  intro a310 a1 a106
  have hc := h.complementary {3, 5, 7, 9} {0, 1, 2} a310 (by decide) (by decide)
  have he : ( {3, 5, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a106

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

theorem c28543 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {4, 5, 9} → False := by
  intro a312 a1 a104
  have hc := h.complementary {3, 6, 7, 8} {0, 1, 2} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a104

theorem c28550 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 2, 4} → ¬ T {1, 5, 9} → False := by
  intro a312 n10 n58
  have hc := h.complementary {3, 6, 7, 8} {0, 2, 4} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n58)

theorem c28558 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 4, 9} → ¬ T {1, 2, 5} → False := by
  intro a312 n26 n39
  have hc := h.complementary {3, 6, 7, 8} {0, 4, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n39)

theorem c28560 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 5, 9} → ¬ T {1, 2, 4} → False := by
  intro a312 n30 n38
  have hc := h.complementary {3, 6, 7, 8} {0, 5, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 5, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n30 (hc.mpr n38)

theorem c28561 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 5, 9} → T {1, 2, 4} → False := by
  intro a312 a30 a38
  have hc := h.complementary {3, 6, 7, 8} {0, 5, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 5, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a30 a38

theorem c28603 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 5} → False := by
  intro a312 a1 a38 a39
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 4, 5} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)

theorem c28607 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a312 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 5, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28683 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {4, 5, 8} → False := by
  intro a313 a1 a103
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 2} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a103

theorem c28701 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 5, 8} → T {1, 2, 4} → False := by
  intro a313 a29 a38
  have hc := h.complementary {3, 6, 7, 9} {0, 5, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a29 a38

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

theorem c28963 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {4, 5, 6} → False := by
  intro a315 a1 a101
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 2} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a1 a101

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

private theorem c31370 (h : TenSystem T Q) :
    ¬ Q {0, 3, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 7, 8} → T {0, 7, 8} → ¬ Q {0, 7, 8, 9} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 6, 7, 8} → False := by
  classical
  intro n182 n198 n192 a34 n204 n146 n201
  have u0_167 : Q {0, 2, 7, 8} := by
    by_contra hv
    exact c497 h a34 n146 hv n182 n192 n198 n201 n204
  exact c501 h u0_167 n146 n182 n192 n198 n201 n204

theorem c31373 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 7, 8, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 7, 8} → T {0, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 1, 7, 8} → False := by
  classical
  intro n204 n198 n192 a34 n201 n146
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u2_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u5_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u6_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u7_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u8_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u9_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u10_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u11_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u12_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u13_182 : Q {0, 3, 7, 8} := by
    by_contra hv
    exact c31370 h hv n198 n192 a34 n204 n146 n201
  have u14_19 : T {0, 3, 7} := by
    by_contra hv
    exact c283 h u13_182 hv
  have u15_20 : T {0, 3, 8} := by
    by_contra hv
    exact c298 h u13_182 hv
  have u16_167 : Q {0, 2, 7, 8} := by
    by_contra hv
    exact c503 h u13_182 n146 hv n192 n198 n201 n204
  have u17_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19055 h hv u11_9 u14_19 u15_20
  have u18_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23531 h hv u12_2 u14_19 u15_20
  have u19_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c23955 h hv u12_2 u14_19 u15_20
  have u20_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24375 h hv u12_2 u14_19 u15_20
  have u21_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25215 h hv u12_2 u14_19 u15_20
  have u22_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c19475 h hv u11_9 u14_19 u15_20
  have u23_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20315 h hv u11_9 u14_19 u15_20
  have u24_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18631 h hv u11_9 u14_19 u15_20
  have u25_13 : T {0, 2, 7} := by
    by_contra hv
    exact c193 h u16_167 hv
  have u26_14 : T {0, 2, 8} := by
    by_contra hv
    exact c208 h u16_167 hv
  have u27_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26755 h hv u10_1 u25_13 u26_14
  have u28_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26331 h hv u10_1 u25_13 u26_14
  have u29_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27175 h hv u10_1 u25_13 u26_14
  have u30_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28015 h hv u10_1 u25_13 u26_14
  have u31_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c1549 h hv u17_244 u19_279 u27_299 u1_318 u6_320 u7_321
  have u32_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c1504 h hv u24_241 u18_276 u28_296 u8_316 u9_317 u1_318
  have u33_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c1594 h hv u22_247 u20_282 u29_302 u1_318 u4_323 u5_324
  have u34_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c1684 h hv u23_253 u21_288 u30_308 u1_318 u2_327 u3_328
  have u35_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1547 h hv u31_188 u17_244 u19_279 u27_299 u1_318 u6_320 u7_321
  have u36_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31261 h h0 u32_185 u24_241 hv u18_276
  have u37_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1592 h hv u33_191 u22_247 u20_282 u29_302 u1_318 u4_323 u5_324
  have u38_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1682 h hv u34_197 u23_253 u21_288 u30_308 u1_318 u2_327 u3_328
  have u39_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1808 h u0_121 u35_104 hv
  have u40_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1912 h u0_121 u37_107 u38_113 hv
  have u41_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1834 h u0_121 u36_101 hv u37_107
  exact c1907 h u0_121 u41_106 u39_117 u40_119

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

theorem c31628 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a101 a120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1803 h u0_121 a101 a120

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

theorem c31633 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {6, 7, 8} → False := by
  classical
  intro n104 n117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1808 h u0_121 n104 n117

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

theorem c31651 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {4, 5, 6} → ¬ T {4, 5, 8} → False := by
  classical
  intro n104 n101 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1826 h u0_121 n101 n103 n104

theorem c31653 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → ¬ T {4, 5, 8} → False := by
  classical
  intro n102 n104 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1828 h u0_121 n102 n103 n104

theorem c31663 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 7, 8} → ¬ T {4, 6, 7} → False := by
  classical
  intro n102 n108 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1838 h u0_121 n102 n105 n108

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

theorem c31668 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  classical
  intro a102 a108 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1843 h u0_121 a102 a108 a109

theorem c31669 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n108 n109 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1844 h u0_121 n105 n108 n109

theorem c31671 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro n106 n108 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1846 h u0_121 n103 n106 n108

theorem c31672 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {4, 6, 8} → T {4, 5, 8} → False := by
  classical
  intro a108 a106 a103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1847 h u0_121 a103 a106 a108

theorem c31673 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 6, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro n110 n106 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1848 h u0_121 n103 n106 n110

theorem c31675 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → ¬ T {4, 5, 8} → False := by
  classical
  intro n108 n110 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1850 h u0_121 n103 n108 n110

theorem c31680 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  classical
  intro a104 a107 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1855 h u0_121 a104 a107 a109

theorem c31681 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {4, 8, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n104 n110 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1856 h u0_121 n104 n107 n110

theorem c31683 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 5, 9} → ¬ T {4, 7, 9} → False := by
  classical
  intro n110 n104 n109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1858 h u0_121 n104 n109 n110

theorem c31685 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n110 n109 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1860 h u0_121 n107 n109 n110

theorem c31690 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 6} → T {5, 6, 9} → T {5, 6, 7} → False := by
  classical
  intro a101 a113 a111
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1865 h u0_121 a101 a111 a113

theorem c31691 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 9} → ¬ T {4, 5, 6} → ¬ T {5, 6, 8} → False := by
  classical
  intro n113 n101 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1866 h u0_121 n101 n112 n113

theorem c31692 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → T {5, 6, 8} → T {4, 5, 6} → False := by
  classical
  intro a113 a112 a101
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1867 h u0_121 a101 a112 a113

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

theorem c31711 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 9} → ¬ T {5, 7, 9} → ¬ T {4, 5, 9} → False := by
  classical
  intro n113 n115 n104
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1886 h u0_121 n104 n113 n115

theorem c31718 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  classical
  intro a113 a115 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1893 h u0_121 a113 a115 a116

theorem c31726 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 7} → T {6, 7, 8} → T {6, 7, 9} → False := by
  classical
  intro a111 a117 a118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1901 h u0_121 a111 a117 a118

theorem c31733 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {6, 8, 9} → ¬ T {5, 6, 8} → False := by
  classical
  intro n117 n119 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1908 h u0_121 n112 n117 n119

theorem c31737 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {5, 6, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n119 n113 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1912 h u0_121 n107 n113 n119

theorem c31741 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n119 n113 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1916 h u0_121 n113 n118 n119

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

theorem c31744 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {4, 7, 8} → T {5, 7, 8} → False := by
  classical
  intro a117 a108 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1919 h u0_121 a108 a114 a117

theorem c31745 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {7, 8, 9} → ¬ T {5, 7, 8} → False := by
  classical
  intro n108 n120 n114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1920 h u0_121 n108 n114 n120

theorem c31748 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {7, 8, 9} → T {6, 7, 8} → False := by
  classical
  intro a108 a120 a117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1923 h u0_121 a108 a117 a120

theorem c31756 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {7, 8, 9} → T {6, 7, 9} → T {4, 7, 9} → False := by
  classical
  intro a120 a118 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1931 h u0_121 a109 a118 a120

theorem c31787 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 8} → T {6, 7, 9} → False := by
  classical
  intro a187 a118
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11043 h a187 u0_37 a118

theorem c31819 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {0, 4, 6, 8} → T {1, 2, 9} → False := by
  classical
  intro a39 a190 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11485 h a190 u0_37 a39 a43

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

theorem c32101 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → Q {1, 5, 7, 8} → T {0, 3, 6} → False := by
  classical
  intro a16 a254 a18
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20451 h a254 u0_9 a16 a18

theorem c32193 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → T {0, 3, 7} → T {0, 3, 9} → False := by
  classical
  intro a278 a19 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23815 h a278 u0_2 a19 a21

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

theorem c32367 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a296 a120
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26303 h a296 u0_1 a120

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

theorem c32467 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 7} → T {4, 8, 9} → False := by
  classical
  intro a306 a110
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27703 h a306 u0_1 a110

theorem c32477 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a307 a109
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27843 h a307 u0_1 a109

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

theorem c32487 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 9} → T {4, 7, 8} → False := by
  classical
  intro a308 a108
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27983 h a308 u0_1 a108

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

theorem c32507 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 9} → T {4, 6, 8} → False := by
  classical
  intro a310 a106
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28263 h a310 u0_1 a106

theorem c32527 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {4, 5, 9} → False := by
  classical
  intro a312 a104
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28543 h a312 u0_1 a104

theorem c32534 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 4} → False := by
  classical
  intro a312 a39 a38
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28603 h a312 u0_1 a38 a39

theorem c32536 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a312 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28607 h a312 u0_1 a39 a43

theorem c32537 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 9} → T {4, 5, 8} → False := by
  classical
  intro a313 a103
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28683 h a313 u0_1 a103

theorem c32547 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a314 a102
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28823 h a314 u0_1 a102

theorem c32557 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 7, 8, 9} → T {4, 5, 6} → False := by
  classical
  intro a315 a101
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28963 h a315 u0_1 a101

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

theorem c32640 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 3, 9} → False := by
  classical
  intro a210
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c725 h a210 u0_49

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

theorem c32648 (h : TenSystem T Q) :
    ¬ Q {0, 1, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → T {0, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 2, 5, 8} → False := by
  classical
  intro n141 n187 n196 n198 a29 n177 n162
  have u0_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c422 h a29 n141 n162 n177 n187 n196 n198 hv
  exact c436 h u0_200 n141 n162 n177 n187 n196 n198

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases129
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32708 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → T {1, 2, 9} → False := by
  classical
  intro n224 n222 n225 n219 n127 a43
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c638 h hv n127 u0_210 n219 n222 n224 n225
  exact c31390 h n222 a43 n225 n224 u1_215 u0_210 n219

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases131
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32718 (h : TenSystem T Q) :
    ¬ Q {1, 3, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {0, 3, 6, 7} → False := by
  classical
  intro n235 n312 n270 a95 n306 n300 n179
  have u0_313 : Q {3, 6, 7, 9} := by
    by_contra hv
    exact c1412 h a95 n179 n235 n270 n300 n306 n312 hv
  exact c1426 h u0_313 n179 n235 n270 n300 n306 n312

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases132
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32721 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 9} → ¬ Q {3, 5, 7, 9} → T {0, 8, 9} → T {4, 7, 8} → ¬ T {6, 7, 8} → Q {3, 6, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro a109 n310 a36 a108 n117 a313 n105
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u4_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u5_104 : T {4, 5, 9} := by
    by_contra hv
    exact c31633 h h0 hv n117
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u7_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv u0_29 u6_118
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h a313 u0_29 hv
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 a313 hv
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u11_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u1_24 u10_116
  have u12_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 a109 hv
  have u13_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31756 h h0 hv u6_118 a109
  have u14_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13775 h hv u1_24 a108 a109
  have u15_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31680 h h0 u5_104 hv a109
  have u16_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10482 h hv u8_38 u12_112
  have u17_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31733 h h0 n117 hv u12_112
  have u18_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u13_120
  have u19_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14119 h hv a36 u10_116 u17_119
  have u20_274 : Q {2, 3, 7, 9} := by
    by_contra hv
    exact c1484 h a313 u16_183 u3_239 hv u2_304 n310 u18_315
  have u21_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c31535 h h0 u14_206 hv u4_210 u11_207 u19_208 u7_205
  have u22_57 : T {1, 5, 8} := by
    by_contra hv
    exact c23352 h u20_274 hv u9_103 u12_112
  have u23_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c23233 h u20_274 hv u22_57
  exact c14194 h u21_209 u23_23 n105 u15_107

theorem c32722 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 6, 7, 8} → ¬ Q {1, 3, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro n312 n235 n179 n270 a95 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u3_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u4_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u5_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u4_29 a95
  have u6_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u9_306 : Q {3, 5, 6, 7} := by
    by_contra hv
    exact c32718 h n235 n312 n270 a95 hv u8_300 n179
  have u10_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1361 h u9_306 hv
  have u11_92 : T {3, 5, 7} := by
    by_contra hv
    exact c1376 h u9_306 hv
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h u9_306 hv
  have u13_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 u9_306 hv
  have u14_313 : Q {3, 6, 7, 9} := by
    by_contra hv
    exact c1422 h u9_306 n179 n235 n270 u8_300 n312 hv
  have u15_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16375 h hv u1_24 u10_91
  have u16_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1453 h u14_313 hv
  have u17_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h u14_313 hv
  have u18_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 u14_313 hv
  have u19_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h u14_313 u4_29 hv
  have u20_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31787 h h0 hv u17_118
  have u21_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31726 h h0 u12_111 hv u17_118
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31673 h h0 u13_110 hv u18_103
  have u23_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31675 h h0 hv u13_110 u18_103
  have u24_36 : T {0, 8, 9} := by
    by_contra hv
    exact c27720 h u9_306 hv u19_38
  have u25_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u22_106
  have u26_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2653 h hv u11_92 u22_106
  have u27_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv u23_108
  have u28_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c32721 h h0 hv u25_310 u24_36 u23_108 u21_117 u14_313 n105
  have u29_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u28_109 hv
  have u30_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u28_109 n105
  have u31_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31685 h h0 u13_110 u28_109 hv
  have u32_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u29_112 hv u7_116
  have u33_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u30_102
  have u34_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16047 h hv u1_24 u30_102 u23_108
  have u35_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23047 h hv u1_24 u30_102 u23_108
  have u36_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31897 h h0 hv u31_107
  have u37_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4733 h hv u16_97 u31_107 u17_118
  have u38_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10202 h hv u19_38 u32_114
  have u39_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1454 h u14_313 u38_181 u2_237 u35_272 hv u27_308 u33_314
  have u40_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1305 h u39_302 hv
  have u41_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c27159 h u39_302 u4_29 hv
  have u42_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16239 h hv u4_29 u40_87
  have u43_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c640 h hv u26_127 u3_210 u5_215 u34_222 u42_224 u15_225
  have u44_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32708 h h0 u42_224 u34_222 u15_225 u43_219 u26_127 hv
  have u45_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9648 h hv u44_43 n105
  have u46_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12328 h hv u19_38 u41_41 u44_43
  exact c32648 h u37_141 u20_187 u46_196 u36_198 u4_29 u45_177 u6_162

private theorem c32723 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 4} → ¬ Q {0, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 6, 8} → T {5, 7, 9} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ T {7, 8, 9} → ¬ Q {3, 5, 6, 9} → Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → ¬ T {4, 6, 7} → False := by
  classical
  intro n38 n171 n262 n301 a115 n206 n266 n231 n120 n308 a306 a312 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u4_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u5_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u3_104 u4_110 hv
  have u6_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13993 h hv u1_29 u5_107
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u4_110 u3_104 hv
  have u8_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u7_109
  have u9_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u9_116
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u12_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv n38
  have u13_30 : T {0, 5, 9} := by
    by_contra hv
    exact c28560 h a312 hv n38
  have u14_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9362 h hv n38 n120
  have u15_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c31535 h h0 n206 hv u2_210 u10_207 u6_208 u12_205
  have u16_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16755 h hv u13_30 a115 u9_116
  have u17_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1362 h a306 u14_175 n231 n266 hv u8_307 n308
  have u18_42 : T {1, 2, 8} := by
    by_contra hv
    exact c620 h u15_209 hv
  have u19_26 : ¬ T {0, 4, 9} := by
    intro hv
    exact c14211 h u15_209 hv u5_107 u7_109
  have u20_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1300 h u17_296 n171 u16_227 n262 u11_300 n301 hv
  have u21_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32435 h h0 hv u18_42 u20_302
  exact c28558 h a312 u19_26 u21_39

theorem c32724 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → ¬ Q {0, 2, 4, 9} → Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 1, 2, 4} → ¬ T {4, 6, 7} → False := by
  classical
  intro a108 n159 a306 a312 n179 n122 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u4_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u5_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u3_104 u4_110 hv
  have u6_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 u5_107 hv
  have u7_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6708 h hv u0_49 u6_114
  have u8_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u4_110 u3_104 hv
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u8_109 hv
  have u10_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 u9_112
  have u11_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32497 h h0 hv u5_107
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h a312 hv
  have u13_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h a306 hv
  have u14_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31726 h h0 u13_111 u12_117 hv
  have u15_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u14_118
  have u16_92 : T {3, 5, 7} := by
    by_contra hv
    exact c1376 h a306 hv
  have u17_96 : T {3, 6, 8} := by
    by_contra hv
    exact c1438 h a312 hv
  have u18_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u19_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u20_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 a108 hv
  have u21_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv a108
  have u22_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31672 h h0 a108 hv u15_103
  have u23_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31748 h h0 a108 hv u12_117
  have u24_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31668 h h0 hv a108 u8_109
  have u25_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17299 h hv u1_24 a108 u8_109
  have u26_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22199 h hv u1_24 a108 u8_109
  have u27_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13775 h hv u1_24 a108 u8_109
  have u28_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31741 h h0 hv u20_113 u14_118
  have u29_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31711 h h0 u20_113 hv u3_104
  have u30_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31691 h h0 u20_113 hv u9_112
  have u31_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1584 h hv u22_106
  have u32_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u23_120
  have u33_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1524 h hv u24_102
  have u34_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6669 h hv u17_96 u12_117 u28_119
  have u35_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7089 h hv u16_92 u13_111 u29_115
  have u36_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u10_157 u35_158 n159 hv u7_156 n122 u34_155
  have u37_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18182 h hv u36_10 u20_113
  have u38_64 : T {1, 8, 9} := by
    by_contra hv
    exact c27710 h a306 u36_10 hv
  have u39_58 : T {1, 5, 9} := by
    by_contra hv
    exact c28550 h a312 u36_10 hv
  have u40_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9079 h hv u38_64 u18_116 u28_119
  have u41_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21821 h hv u38_64 u18_116 u28_119
  have u42_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6161 h hv u38_64 u30_101
  have u43_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21657 h hv u39_58 u29_115 u18_116
  have u44_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8915 h hv u39_58 u29_115 u18_116
  have u45_38 : T {1, 2, 4} := by
    by_contra hv
    exact c32723 h h0 hv u44_171 u43_262 u31_301 u29_115 u27_206 u26_266 u25_231 u23_120 u21_308 a306 a312 n105
  have u46_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c27721 h a306 hv u45_38
  have u47_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32534 h h0 a312 hv u45_38
  have u48_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c28561 h a312 hv u45_38
  have u49_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9503 h hv u45_38 u28_119
  have u50_85 : T {2, 8, 9} := by
    by_contra hv
    exact c27838 h a306 u46_36 hv u4_110
  have u51_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10484 h hv u47_39 u22_106
  have u52_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23210 h hv u48_30 u3_104 u20_113
  have u53_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16921 h hv u50_85 u18_116 u28_119
  have u54_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3221 h hv u50_85 u30_101
  have u55_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c284 h hv u54_131 u42_152 u40_172 u49_176 n179 u51_183
  have u56_303 : Q {3, 4, 7, 8} := by
    by_contra hv
    exact c1469 h a312 u55_182 u37_238 u52_273 hv u11_309 u32_315
  exact c1319 h u56_303 u40_172 u53_228 u41_263 u33_297 u19_300 u2_304

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases133
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32725 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 4} → ¬ Q {0, 1, 7, 8} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 6, 8, 9} → ¬ T {4, 7, 8} → Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → False := by
  classical
  intro a38 n146 n272 n266 n314 n108 a306 a312
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u3_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h a306 hv
  have u4_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 n108 hv
  have u5_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31690 h h0 hv u4_113 u3_111
  have u6_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8248 h hv u0_49 u5_101
  have u7_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u8_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u9_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u7_104 u8_110 hv
  have u10_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 u9_107 hv
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31745 h h0 n108 hv u10_114
  have u12_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32367 h h0 hv u11_120
  have u13_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv n108
  have u14_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31897 h h0 hv u9_107
  have u15_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u8_110 u7_104 hv
  have u16_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u15_109
  have u17_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h a312 hv
  have u18_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31726 h h0 u3_111 u17_117 hv
  have u19_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1764 h hv u18_118
  have u20_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1361 h a306 hv
  have u21_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13425 h hv a38 u20_91
  have u22_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9363 h hv a38 u11_120
  have u23_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c27721 h a306 hv a38
  have u24_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32534 h h0 a312 hv a38
  have u25_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10343 h hv a38 u4_113
  have u26_85 : T {2, 8, 9} := by
    by_contra hv
    exact c27838 h a306 u23_36 hv u8_110
  have u27_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10204 h hv u24_39 n108
  have u28_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c509 h hv n146 u6_167 u25_182 u13_192 u14_198 u21_204
  have u29_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17211 h hv u1_24 u26_85
  have u30_34 : ¬ T {0, 7, 8} := by
    intro hv
    exact c31373 h h0 u21_204 u14_198 u13_192 hv u28_201 n146
  have u31_308 : Q {3, 5, 6, 9} := by
    by_contra hv
    exact c1362 h a306 u22_175 u29_231 n266 u12_296 u16_307 hv
  have u32_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27160 h hv u30_34 u24_39
  exact c1452 h u31_308 u27_181 u2_237 n272 u32_302 u19_313 n314

private theorem c32726 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a306 a312 n179 n270 a95 n105
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u4_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u5_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h a312 hv
  have u6_98 : T {3, 7, 8} := by
    by_contra hv
    exact c1468 h a312 hv
  have u7_96 : T {3, 6, 8} := by
    by_contra hv
    exact c1438 h a312 hv
  have u8_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u9_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1951 h hv a95 u8_116
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u2_24 u8_116
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u12_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1361 h a306 hv
  have u13_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h a306 hv
  have u14_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u15_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7197 h hv u12_91 a95 u7_96
  have u16_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u14_110 u4_104 hv
  have u17_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u4_104 u14_110 hv
  have u18_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u16_109 hv
  have u19_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u16_109
  have u20_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 u17_107 hv
  have u21_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13993 h hv u0_29 u17_107
  have u22_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u1_49 u18_112
  have u23_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6708 h hv u1_49 u20_114
  have u24_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c32724 h h0 hv u15_159 a306 a312 n179 u9_122 n105
  have u25_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u24_108 hv
  have u26_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31663 h h0 hv u24_108 n105
  have u27_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31745 h h0 u24_108 hv u20_114
  have u28_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31718 h h0 u25_113 hv u8_116
  have u29_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14127 h hv u2_24 u25_113
  have u30_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7081 h hv u12_91 u13_111 u25_113
  have u31_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u26_102
  have u32_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22907 h hv u2_24 u26_102 u16_109
  have u33_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18007 h hv u2_24 u26_102 u16_109
  have u34_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32367 h h0 hv u27_120
  have u35_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6685 h hv u6_98 u5_117 u27_120
  have u36_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u22_157 u30_158 u15_159 hv u23_156 u9_122 u35_155
  have u37_64 : T {1, 8, 9} := by
    by_contra hv
    exact c27710 h a306 u36_10 hv
  have u38_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22111 h hv u2_24 u37_64
  have u39_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6021 h hv u37_64 u26_102
  have u40_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21681 h hv u37_64 u8_116 u27_120
  have u41_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8939 h hv u37_64 u8_116 u27_120
  have u42_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c1006 h hv u39_151 u10_207 u40_262 u38_266 n270 u32_271
  have u43_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c992 h hv u39_151 u10_207 u40_262 u38_266 n270 u32_271 u42_272
  have u44_146 : ¬ Q {0, 1, 7, 8} := by
    intro hv
    exact c5306 h hv u43_67 u4_104
  have u45_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32725 h h0 hv u44_146 u42_272 u38_266 u31_314 u24_108 a306 a312
  have u46_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u45_38
  have u47_36 : T {0, 8, 9} := by
    by_contra hv
    exact c27720 h a306 hv u45_38
  have u48_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv u45_38 u28_115
  have u49_206 : Q {1, 2, 3, 5} := by
    by_contra hv
    exact c31535 h h0 hv u29_209 u3_210 u10_207 u21_208 u46_205
  have u50_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16779 h hv u47_36 u8_116 u27_120
  have u51_301 : Q {3, 4, 6, 8} := by
    by_contra hv
    exact c1439 h a312 u48_180 u33_236 u32_271 hv u19_307 u31_314
  have u52_39 : T {1, 2, 5} := by
    by_contra hv
    exact c575 h u49_206 hv
  have u53_26 : ¬ T {0, 4, 9} := by
    intro hv
    exact c13709 h u49_206 hv u5_117
  have u54_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1304 h u51_301 u41_171 u50_227 u40_262 u34_296 u11_300 hv
  have u55_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c32435 h h0 u52_39 hv u54_302
  exact c27718 h a306 u53_26 u55_42

private theorem c32727 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → T {0, 5, 9} → T {4, 5, 6} → Q {3, 6, 7, 9} → T {5, 8, 9} → False := by
  classical
  intro n108 a30 a101 a313 a116
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u4_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u5_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c32557 h h0 hv a101
  have u6_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31628 h h0 a101 hv
  have u7_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u8_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv u0_29 u7_118
  have u9_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h a313 u0_29 hv
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 a313 hv
  have u11_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u1_24 a116
  have u12_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 n108 hv
  have u13_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31671 h h0 hv n108 u10_103
  have u14_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31692 h h0 u12_113 hv a101
  have u15_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14127 h hv u1_24 u12_113
  have u16_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14095 h hv a30 u12_113 a116
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u13_106
  have u18_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10482 h hv u9_38 u14_112
  have u19_206 : Q {1, 2, 3, 5} := by
    by_contra hv
    exact c31535 h h0 hv u15_209 u2_210 u11_207 u16_208 u8_205
  have u20_274 : Q {2, 3, 7, 9} := by
    by_contra hv
    exact c1484 h a313 u18_183 u4_239 hv u3_304 u17_310 u5_315
  have u21_23 : T {0, 4, 6} := by
    by_contra hv
    exact c13702 h u19_206 hv u6_120
  have u22_57 : T {1, 5, 8} := by
    by_contra hv
    exact c23352 h u20_274 hv u10_103 u14_112
  exact c23233 h u20_274 u21_23 u22_57

theorem c32728_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro n235 n179 n270 a95 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u3_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u4_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u5_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u4_29 a95
  have u6_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u9_312 : Q {3, 6, 7, 8} := by
    by_contra hv
    exact c32722 h h0 hv n235 n179 n270 a95 n105
  have u10_96 : T {3, 6, 8} := by
    by_contra hv
    exact c1438 h u9_312 hv
  have u11_98 : T {3, 7, 8} := by
    by_contra hv
    exact c1468 h u9_312 hv
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h u9_312 hv
  have u13_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 u9_312 hv
  have u14_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15533 h hv u1_24 u10_96
  have u15_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c32726 h h0 hv u9_312 n179 n270 a95 n105
  have u16_313 : Q {3, 6, 7, 9} := by
    by_contra hv
    exact c1424 h u9_312 n179 n235 n270 u8_300 u15_306 hv
  have u17_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1453 h u16_313 hv
  have u18_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h u16_313 hv
  have u19_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 u16_313 hv
  have u20_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h u16_313 u4_29 hv
  have u21_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31787 h h0 hv u18_118
  have u22_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31651 h h0 u13_104 hv u19_103
  have u23_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31653 h h0 hv u13_104 u19_103
  have u24_30 : T {0, 5, 9} := by
    by_contra hv
    exact c28560 h u9_312 hv u20_38
  have u25_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2661 h hv u11_98 u22_101
  have u26_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u23_102 hv
  have u27_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u23_102
  have u28_108 : T {4, 7, 8} := by
    by_contra hv
    exact c32727 h h0 hv u24_30 u22_101 u16_313 u7_116
  have u29_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u28_108 hv
  have u30_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv u28_108
  have u31_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31744 h h0 u12_117 u28_108 hv
  have u32_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16047 h hv u1_24 u23_102 u28_108
  have u33_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23047 h hv u1_24 u23_102 u28_108
  have u34_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31737 h h0 u26_119 u29_113 hv
  have u35_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u31_114
  have u36_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10202 h hv u20_38 u31_114
  have u37_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1454 h u16_313 u36_181 u2_237 u33_272 hv u30_308 u27_314
  have u38_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4733 h hv u17_97 u34_107 u18_118
  have u39_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1305 h u37_302 hv
  have u40_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c27159 h u37_302 u4_29 hv
  have u41_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16239 h hv u4_29 u39_87
  have u42_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c646 h hv u25_127 u3_210 u5_215 u14_219 u32_222 u41_224
  have u43_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c31390 h u32_222 hv u42_225 u41_224 u5_215 u3_210 u14_219
  have u44_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9648 h hv u43_43 n105
  have u45_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12328 h hv u20_38 u40_41 u43_43
  exact c32648 h u38_141 u21_187 u45_196 u35_198 u4_29 u44_177 u6_162

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32728_oai := @OAI.BorsukNine.FiniteObstruction.c32728_oai
