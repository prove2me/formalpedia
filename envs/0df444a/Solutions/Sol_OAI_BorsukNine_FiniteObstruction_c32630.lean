-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32630
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:21:55.095116+00:00
-- url     : https://prove2.me/submissions/ad58447b-bae2-42fc-95e5-e0507c4ca100

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c1390
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31481
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31520
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31524
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32582
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32601
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32606
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32621
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c32629

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

theorem c123 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 2, 3} → False := by
  intro a121 n9
  exact n9 (h.down {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide))

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

theorem c285 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 7} → False := by
  intro a183 n19
  exact n19 (h.down {0, 3, 7, 9} {0, 3, 7} a183 (by decide) (by decide))

theorem c296 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {0, 3, 8} → False := by
  intro a180 n20
  exact n20 (h.down {0, 3, 6, 8} {0, 3, 8} a180 (by decide) (by decide))

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

theorem c428 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a177 n141 n162 n187 n196 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {0, 5, 8} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact hne (by decide)
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

theorem c543 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {1, 2, 3} → False := by
  intro a121 n37
  exact n37 (h.down {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide))

theorem c570 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ T {1, 2, 4} → False := by
  intro a215 n38
  exact n38 (h.down {1, 2, 4, 9} {1, 2, 4} a215 (by decide) (by decide))

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

theorem c615 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 7} → False := by
  intro a224 n41
  exact n41 (h.down {1, 2, 7, 9} {1, 2, 7} a224 (by decide) (by decide))

theorem c630 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {1, 2, 8} → False := by
  intro a225 n42
  exact n42 (h.down {1, 2, 8, 9} {1, 2, 8} a225 (by decide) (by decide))

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

theorem c808 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {1, 4, 9} → False := by
  intro a249 n54
  exact n54 (h.down {1, 4, 7, 9} {1, 4, 9} a249 (by decide) (by decide))

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

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

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

theorem c1123 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {2, 4, 9} → False := by
  intro a284 n75
  exact n75 (h.down {2, 4, 7, 9} {2, 4, 9} a284 (by decide) (by decide))

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

theorem c2515 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 5, 9} → T {4, 6, 7} → False := by
  intro a126 a94 a105
  have hc := h.complementary {0, 1, 2, 8} {3, 5, 9} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a94 a105

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

theorem c4657 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 9} → T {2, 4, 9} → T {2, 7, 9} → False := by
  intro a141 a70 a75 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {2, 9} {3, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

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

theorem c7597 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 9} → T {1, 4, 9} → T {1, 7, 9} → False := by
  intro a162 a49 a54 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {1, 9} {3, 4, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

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

theorem c8944 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 2, 6} → ¬ T {5, 8, 9} → False := by
  intro a172 n40 n116
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 6} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n116)

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

theorem c11097 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 9} → T {1, 3, 9} → T {1, 7, 9} → False := by
  intro a187 a43 a49 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 9} {2, 3, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

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

theorem c11886 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 2, 6} → ¬ T {3, 5, 8} → False := by
  intro a193 n40 n93
  have hc := h.complementary {0, 4, 7, 9} {1, 2, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n93)

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

theorem c14339 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 6, 7} → False := by
  intro a210 a24 a102 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 7} {0, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

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

theorem c16886 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a228 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 7} {5, 8} {0, 6, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c17579 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a233 a23 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 7, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
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

theorem c20157 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 4, 7} → T {2, 3, 9} → False := by
  intro a252 a24 a70
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 7} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a70

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

theorem c21786 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a263 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 7} {5, 8} {0, 6, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c23815 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a278 a2 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {0, 3} {1, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

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

theorem c25057 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 4, 7} → T {1, 3, 9} → False := by
  intro a287 a24 a49
  have hc := h.complementary {2, 5, 6, 8} {0, 4, 7} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a49

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

theorem c27857 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 7} → T {1, 2, 9} → False := by
  intro a307 a24 a43
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 7} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a43

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

theorem c27905 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a307 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 2} {0, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c28607 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a312 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 5, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c31685 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n110 n109 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1860 h u0_121 n107 n109 n110

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

theorem c31819 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {0, 4, 6, 8} → T {1, 2, 9} → False := by
  classical
  intro a39 a190 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11485 h a190 u0_37 a39 a43

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

theorem c32301 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → T {0, 3, 6} → Q {2, 5, 7, 8} → False := by
  classical
  intro a16 a18 a289
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25351 h a289 u0_2 a16 a18

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

theorem c32536 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a312 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28607 h a312 u0_1 a39 a43

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

theorem c32585 (h : TenSystem T Q) :
    ¬ Q {0, 5, 7, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → T {0, 5, 8} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n198 n162 n141 a29 n200 n187 n196
  have u0_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c428 h hv n141 n162 n187 n196 n198 n200
  exact c31443 h u0_177 n141 a29 n200 n162 n198 n196

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

theorem c32630_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 4, 7} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro a24 n127 n177 a49
  have u0_304 : ¬ Q {3, 4, 7, 9} := c32583 h h0
  have u1_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u2_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32626 h h0 hv n127 n177 a49
  have u3_29 : T {0, 5, 8} := by
    by_contra hv
    exact c14274 h u1_210 hv u2_105
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u2_105 hv
  have u5_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c32621 h h0 hv n127 n177 a49
  have u6_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c592 h hv u5_40
  have u7_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c32586 h h0 hv a49
  have u9_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u1_210 hv
  have u10_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u1_210 hv
  have u11_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25057 h hv a24 a49
  have u12_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h u1_210 a24 hv
  have u13_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv a24 u10_43
  have u14_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv a24 u9_70
  have u15_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31586 h h0 hv u11_287 u14_252 u13_307
  have u16_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u12_112
  have u17_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32627 h h0 hv u13_307 u2_105 u7_311 n177 u1_210
  have u18_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c32629 h h0 hv a24 u3_29 u4_116 u6_212 a49
  have u19_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32628 h h0 u18_233 hv u17_298 u13_307 u2_105 u7_311 n177 u10_43
  have u20_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11886 h hv u5_40 u19_93
  have u21_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u20_193 u16_109 hv u0_304
  have u22_54 : T {1, 4, 9} := by
    by_contra hv
    exact c808 h u21_249 hv
  have u23_63 : T {1, 7, 9} := by
    by_contra hv
    exact c939 h u21_249 hv
  have u24_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u21_249 hv u20_193 u0_304
  have u25_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7597 h hv a49 u22_54 u23_63
  have u26_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11097 h hv u10_43 a49 u23_63
  have u27_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h u24_284 hv
  have u28_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h u24_284 hv
  have u29_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4657 h hv u9_70 u27_75 u28_84
  have u30_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32585 h u8_198 u25_162 u29_141 u3_29 hv u26_187 u15_196
  exact c436 h u30_200 u29_141 u25_162 n177 u26_187 u15_196 u8_198

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32630_oai := @OAI.BorsukNine.FiniteObstruction.c32630_oai
