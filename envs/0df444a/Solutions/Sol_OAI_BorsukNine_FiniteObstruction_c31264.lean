-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31264
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:07:34.864361+00:00
-- url     : https://prove2.me/submissions/bb729926-6346-4ff6-bfd2-ce29b634a199

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31252

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

theorem c62 (h : TenSystem T Q) :
    T {0, 1, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 9} → False := by
  intro a5 n124 n130 n135 n139 n143 n144 n145
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 1, 6} a5
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n135 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n139 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 6} = {0, 1, 6, 7} by decide)) hS)
  · exact n144 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 6} = {0, 1, 6, 8} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 6} = {0, 1, 6, 9} by decide)) hS)

theorem c68 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 9} → False := by
  intro a135 n124 n130 n139 n143 n144 n145
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 4, 6} {0, 1, 6} a135 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n139 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 6} = {0, 1, 6, 7} by decide)) hS)
  · exact n144 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 6} = {0, 1, 6, 8} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 6} = {0, 1, 6, 9} by decide)) hS)

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

theorem c192 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a164 n125 n152 n157 n161 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 6, 7} {0, 2, 7} a164 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

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

theorem c326 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ T {0, 4, 5} → False := by
  intro a186 n22
  exact n22 (h.down {0, 4, 5, 7} {0, 4, 5} a186 (by decide) (by decide))

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

theorem c593 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a212 n124 n207 n216 n220 n221 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 4, 6} {1, 2, 6} a212 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
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

theorem c735 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 3, 9} → False := by
  intro a240 n49
  exact n49 (h.down {1, 3, 8, 9} {1, 3, 9} a240 (by decide) (by decide))

theorem c744 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 5} → False := by
  intro a241 n50
  exact n50 (h.down {1, 4, 5, 6} {1, 4, 5} a241 (by decide) (by decide))

theorem c746 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {1, 4, 5} → False := by
  intro a242 n50
  exact n50 (h.down {1, 4, 5, 7} {1, 4, 5} a242 (by decide) (by decide))

theorem c774 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {1, 4, 7} → False := by
  intro a242 n52
  exact n52 (h.down {1, 4, 5, 7} {1, 4, 7} a242 (by decide) (by decide))

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

theorem c1286 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {3, 4, 5} → False := by
  intro a297 n86
  exact n86 (h.down {3, 4, 5, 7} {3, 4, 5} a297 (by decide) (by decide))

theorem c1314 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {3, 4, 7} → False := by
  intro a297 n88
  exact n88 (h.down {3, 4, 5, 7} {3, 4, 7} a297 (by decide) (by decide))

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

theorem c1521 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 7, 9} → False := by
  intro a242 n186 n277 n297 n316 n319 n320
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {4, 5, 7} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n186 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n297 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 7} = {4, 5, 7, 8} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 7} = {4, 5, 7, 9} by decide)) hS)

theorem c1525 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 7, 9} → False := by
  intro a297 n186 n242 n277 n316 n319 n320
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 7} {4, 5, 7} a297 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n186 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact n277 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 7} = {4, 5, 7, 8} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 7} = {4, 5, 7, 9} by decide)) hS)

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

theorem c1779 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a314 n119
  exact n119 (h.down {3, 6, 8, 9} {6, 8, 9} a314 (by decide) (by decide))

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

theorem c1821 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 6, 7} → False := by
  intro a121 a110 a111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a110 a111

theorem c1823 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 5, 7} → T {4, 5, 8} → False := by
  intro a121 a101 a102 a103
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 5} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) a103)

theorem c1825 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 5, 7} → T {4, 5, 9} → False := by
  intro a121 a101 a102 a104
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 5} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) a104)

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

theorem c1938 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {6, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n110 n119 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {8, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) ht)

theorem c1940 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 8, 9} → ¬ T {6, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n116 n119 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {8, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) ht)

theorem c1947 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 8} → T {6, 7, 9} → False := by
  intro a122 a93 a118
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a118

theorem c2087 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 8} → T {6, 7, 9} → False := by
  intro a123 a89 a118
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 8} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a89 a118

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

theorem c2241 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 8, 9} → T {4, 5, 7} → False := by
  intro a124 a100 a102
  have hc := h.complementary {0, 1, 2, 6} {3, 8, 9} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 8, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a100 a102

theorem c2255 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 4, 5} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a124 a86 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 6} {3, 5} {4, 8, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c2371 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 5, 6} → T {4, 8, 9} → False := by
  intro a125 a91 a110
  have hc := h.complementary {0, 1, 2, 7} {3, 5, 6} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 5, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a91 a110

theorem c2563 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a126 a86 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {4, 5} {3, 6, 7} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

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

theorem c2703 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a127 a86 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {4, 5} {3, 6, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c3062 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  intro a130 n71 n120
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 5} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n71 (hc.mpr n120)

theorem c3063 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → T {2, 4, 5} → T {7, 8, 9} → False := by
  intro a130 a71 a120
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 5} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a120

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

theorem c4389 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → T {3, 4, 7} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a139 a88 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 6} {3, 4} {7, 8, 9} a139 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

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

theorem c4978 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a143 n71 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 7} {4, 5} {2, 8, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c5089 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 9} → False := by
  intro a144 a86 a88 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 8} {3, 4} {5, 7, 9} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c5115 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {2, 4, 5} → T {3, 4, 5} → T {4, 5, 7} → False := by
  intro a144 a71 a86 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 8} {4, 5} {2, 3, 7} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c5229 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 8} → False := by
  intro a145 a86 a88 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 9} {3, 4} {5, 7, 8} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c5255 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 4, 5} → T {3, 4, 5} → T {4, 5, 7} → False := by
  intro a145 a71 a86 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 9} {4, 5} {2, 3, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

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

theorem c6151 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 5, 6} → T {4, 8, 9} → False := by
  intro a152 a55 a110
  have hc := h.complementary {0, 2, 3, 7} {1, 5, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 5, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a55 a110

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

theorem c6975 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 8, 9} → T {3, 8, 9} → T {5, 8, 9} → False := by
  intro a157 a64 a100 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {8, 9} {1, 3, 5} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c6976 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a157 n64 n100 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {8, 9} {1, 3, 6} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

theorem c7098 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a158 n59 n95 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 8} {6, 7} {1, 3, 5} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)

theorem c7238 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a159 n59 n95 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {6, 7} {1, 3, 5} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)

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

theorem c7536 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a161 n64 n100 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 7} {8, 9} {1, 3, 6} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

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

theorem c10020 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a179 n71 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 6, 7} {4, 5} {2, 8, 9} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

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

theorem c10717 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 7} → False := by
  intro a184 a50 a71 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 5} {1, 2, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10719 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a184 a50 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 5} {1, 6, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

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

theorem c15169 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {3, 4, 7} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a216 a88 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {3, 4} {7, 8, 9} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

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

theorem c15758 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a220 n22 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 7} {4, 5} {0, 8, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c15869 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 9} → False := by
  intro a221 a86 a88 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 8} {3, 4} {5, 7, 9} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

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

theorem c16009 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 8} → False := by
  intro a222 a86 a88 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 9} {3, 4} {5, 7, 8} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

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

theorem c17860 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a235 n71 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 7} {4, 5} {2, 8, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

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

theorem c18462 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 4} → ¬ T {5, 6, 7} → False := by
  intro a240 n10 n111
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 4} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n111)

theorem c18467 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 6} → T {4, 5, 7} → False := by
  intro a240 a12 a102
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a102

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

theorem c18476 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 4, 7} → False := by
  intro a240 n27 n73
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n73)

theorem c18488 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a240 n11 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {0, 2} {5, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

theorem c18549 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 7} → T {2, 4, 7} → T {2, 6, 7} → False := by
  intro a240 a13 a73 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 7} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c18551 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 7} → T {2, 5, 7} → T {2, 6, 7} → False := by
  intro a240 a13 a77 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 7} {0, 5, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c18554 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 6} → False := by
  intro a240 n22 n71 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 5} {0, 2, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)

theorem c18559 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a240 a22 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 5} {0, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

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

theorem c22801 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {1, 8, 9} → T {4, 8, 9} → T {5, 8, 9} → False := by
  intro a270 a64 a110 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {8, 9} {1, 4, 5} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

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

theorem c23377 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 5, 6} → T {1, 4, 7} → False := by
  intro a275 a27 a52
  have hc := h.complementary {2, 3, 8, 9} {0, 5, 6} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a27 a52

theorem c23461 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {1, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a275 a50 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {4, 5} {1, 6, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

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

theorem c23707 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a277 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {1, 3} {0, 8, 9} a277 (by decide) (by decide) (by decide) (by decide)
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

theorem c26311 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 2, 7} → T {1, 8, 9} → False := by
  intro a296 a13 a64
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 7} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a64

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

theorem c26863 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {5, 8, 9} → False := by
  intro a300 a1 a116
  have hc := h.complementary {3, 4, 6, 7} {0, 1, 2} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a116

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

theorem c27566 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 1, 6} → ¬ T {2, 5, 7} → False := by
  intro a305 n5 n77
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 6} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 7} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n77)

theorem c27571 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 5} → T {1, 6, 7} → False := by
  intro a305 a11 a59
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 5} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a11 a59

theorem c27640 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 1, 6} → ¬ T {1, 2, 6} → ¬ T {1, 6, 7} → False := by
  intro a305 n5 n40 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {1, 6} {0, 2, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 6} = {0, 1, 6} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c27703 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 1, 2} → T {4, 8, 9} → False := by
  intro a306 a1 a110
  have hc := h.complementary {3, 5, 6, 7} {0, 1, 2} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a110

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

theorem c28411 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 4} → T {1, 6, 7} → False := by
  intro a311 a10 a59
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 4} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a10 a59

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

theorem c28662 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 9} → False := by
  intro a312 n22 n71 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {4, 5} {0, 2, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

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

theorem c28802 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n22 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {0, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28823 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {4, 5, 7} → False := by
  intro a314 a1 a102
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 2} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a102

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

theorem c31253 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → T {4, 5, 7} → ¬ Q {0, 4, 5, 7} → False := by
  classical
  intro n242 n277 a102 n186
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u2_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u3_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1525 h hv n186 n242 n277 u2_316 u1_319 u0_320
  exact c1517 h a102 n186 n242 n277 u3_297 u2_316 u1_319 u0_320

theorem c31254 (h : TenSystem T Q) :
    T {0, 1, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → False := by
  classical
  intro a5 n139 n124 n130 n145 n143 n144
  have u0_135 : Q {0, 1, 4, 6} := by
    by_contra hv
    exact c62 h a5 n124 n130 hv n139 n143 n144 n145
  exact c68 h u0_135 n124 n130 n139 n143 n144 n145

private theorem c31255 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 3, 6} → ¬ T {2, 5, 7} → T {3, 4, 7} → ¬ Q {0, 1, 2, 6} → False := by
  classical
  intro a305 n145 n144 n143 n130 n77 a88 n124
  have u0_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h a305 hv
  have u1_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h a305 hv
  have u2_5 : T {0, 1, 6} := by
    by_contra hv
    exact c27566 h a305 hv n77
  have u3_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4389 h hv a88 u0_89 u1_90
  exact c31254 h u2_5 u3_139 n124 n130 n145 n143 n144

private theorem c31256 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ Q {3, 5, 8, 9} → Q {1, 3, 8, 9} → ¬ T {6, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n101 n311 a240 n119 n22
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_49 : T {1, 3, 9} := by
    by_contra hv
    exact c735 h a240 hv
  have u6_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h a240 hv
  have u7_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23707 h hv u0_2 u6_48 u5_49
  have u8_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u9_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u4_121 hv n119
  have u10_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31253 h h0 hv u7_277 u9_102 u8_186
  have u11_297 : Q {3, 4, 5, 7} := by
    by_contra hv
    exact c1521 h u10_242 u8_186 u7_277 hv u1_316 u2_319 u3_320
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1314 h u11_297 hv
  have u13_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1286 h u11_297 hv
  have u14_52 : T {1, 4, 7} := by
    by_contra hv
    exact c774 h u10_242 hv
  have u15_50 : T {1, 4, 5} := by
    by_contra hv
    exact c746 h u10_242 hv
  have u16_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u17_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2241 h hv u16_100 u9_102
  have u18_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18470 h a240 n22 hv
  have u19_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv n119
  have u20_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c31252 h h0 hv n22
  have u21_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1802 h u4_121 n101 hv
  have u22_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18468 h a240 hv n101
  have u23_71 : T {2, 4, 5} := by
    by_contra hv
    exact c18554 h a240 n22 hv n101
  have u24_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c18549 h a240 u22_13 hv u18_80
  have u25_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c18551 h a240 u22_13 hv u18_80
  have u26_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3063 h hv u23_71 u21_120
  have u27_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4891 h hv u23_71 u16_100
  have u28_27 : T {0, 5, 6} := by
    by_contra hv
    exact c18476 h a240 hv u24_73
  have u29_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10717 h hv u15_50 u23_71 u9_102
  have u30_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5115 h hv u23_71 u13_86 u9_102
  have u31_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5255 h hv u23_71 u13_86 u9_102
  have u32_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c31255 h hv u31_145 u30_144 u27_143 u26_130 u25_77 u12_88 u17_124
  have u33_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23377 h hv u28_27 u14_52
  exact c1491 h a240 u29_184 u33_275 u32_305 n311 u19_314 u20_315

private theorem c31257 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → Q {1, 3, 8, 9} → ¬ T {6, 8, 9} → ¬ T {0, 4, 5} → False := by
  classical
  intro n311 a240 n119 n22
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_49 : T {1, 3, 9} := by
    by_contra hv
    exact c735 h a240 hv
  have u6_48 : T {1, 3, 8} := by
    by_contra hv
    exact c720 h a240 hv
  have u7_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23707 h hv u0_2 u6_48 u5_49
  have u8_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c326 h hv n22
  have u9_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1804 h u4_121 hv n119
  have u10_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31253 h h0 hv u7_277 u9_102 u8_186
  have u11_297 : Q {3, 4, 5, 7} := by
    by_contra hv
    exact c1521 h u10_242 u8_186 u7_277 hv u1_316 u2_319 u3_320
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1314 h u11_297 hv
  have u13_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1286 h u11_297 hv
  have u14_50 : T {1, 4, 5} := by
    by_contra hv
    exact c746 h u10_242 hv
  have u15_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u16_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2241 h hv u15_100 u9_102
  have u17_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18467 h a240 hv u9_102
  have u18_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1779 h hv n119
  have u19_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c31252 h h0 hv n22
  have u20_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31256 h h0 hv n311 a240 n119 n22
  have u21_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10719 h hv u14_50 u20_101 u9_102
  have u22_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23461 h hv u14_50 u20_101 u9_102
  have u23_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u4_121 u20_101 hv
  have u24_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1823 h u4_121 u20_101 u9_102 hv
  have u25_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1825 h u4_121 u20_101 u9_102 hv
  have u26_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18469 h a240 hv u20_101
  have u27_71 : ¬ T {2, 4, 5} := by
    intro hv
    exact c18561 h a240 hv u20_101 u9_102
  have u28_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1491 h a240 u21_184 u22_275 hv n311 u18_314 u19_315
  have u29_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13842 h hv n22 u23_120
  have u30_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15758 h hv n22 u24_103 u25_104
  have u31_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18488 h a240 hv u17_12 u26_13
  have u32_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3062 h hv u27_71 u23_120
  have u33_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4978 h hv u27_71 u24_103 u25_104
  have u34_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u28_305 hv
  have u35_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h u28_305 hv
  have u36_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c27571 h u28_305 u31_11 hv
  have u37_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5229 h hv u13_86 u12_88 u34_89
  have u38_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4389 h hv u12_88 u34_89 u35_90
  have u39_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15169 h hv u12_88 u34_89 u35_90
  have u40_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16009 h hv u13_86 u12_88 u34_89
  have u41_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5089 h hv u13_86 u12_88 u35_90
  have u42_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15869 h hv u13_86 u12_88 u35_90
  have u43_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c31254 h hv u38_139 u16_124 u32_130 u37_145 u33_143 u41_144
  have u44_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c593 h hv u16_124 u29_207 u39_216 u30_220 u42_221 u40_222
  have u45_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c587 h hv u16_124 u29_207 u44_212 u39_216 u30_220 u42_221 u40_222
  exact c27640 h u28_305 u43_5 u45_40 u36_59

theorem c31258 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 8, 9} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a240 n71 n120 a102
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u1_121 hv n120
  have u3_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1825 h u1_121 u2_101 a102 hv
  have u4_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1823 h u1_121 u2_101 a102 hv
  have u5_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17860 h hv n71 u4_103 u3_104
  have u6_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10020 h hv n71 u4_103 u3_104
  have u7_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c1053 h hv n71
  have u8_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u1_121 u4_103 hv
  have u9_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u1_121 a102 hv
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1940 h u1_121 hv u9_119 n120
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26863 h hv u0_1 u10_116
  have u12_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1938 h u1_121 hv u9_119 n120
  have u13_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27703 h hv u0_1 u12_110
  have u14_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u1_121 u12_110 hv
  have u15_64 : T {1, 8, 9} := by
    by_contra hv
    exact c952 h a240 hv
  have u16_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1490 h a240 hv
  have u17_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c18559 h a240 hv u2_101 a102
  have u18_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31257 h h0 hv a240 u9_119 u17_22
  have u19_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18462 h a240 hv u14_111
  have u20_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22801 h hv u15_64 u12_110 u10_116
  have u21_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6975 h hv u15_64 u16_100 u10_116
  have u22_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6835 h hv u15_64 u16_100 u10_116
  have u23_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28662 h hv u17_22 n71 u3_104
  have u24_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28802 h hv u17_22 n71 u4_103
  have u25_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h u18_311 hv
  have u26_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c28411 h u18_311 u19_10 hv
  have u27_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c1412 h hv u6_179 u5_235 u20_270 u11_300 u13_306 u23_312 u24_313
  have u28_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1947 h hv u25_93 u8_118
  have u29_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7098 h hv u26_59 u27_95 u14_111
  have u30_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7238 h hv u26_59 u27_95 u14_111
  have u31_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c141 h hv u28_122 u7_155 u22_156 u21_157 u29_158 u30_159
  exact c137 h u19_10 u28_122 u31_149 u7_155 u22_156 u21_157 u29_158 u30_159

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

private theorem c31263 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → ¬ Q {0, 1, 2, 7} → T {6, 7, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {3, 6, 8, 9} → T {3, 4, 5} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  classical
  intro a311 n125 a118 n127 n126 n184 n240 n314 a86 n275 n315
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h a311 hv
  have u2_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h a311 hv
  have u3_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1497 h a311 n184 n240 n275 hv n314 n315
  have u4_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1947 h hv u1_93 a118
  have u5_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2255 h hv a86 u1_93 u2_94
  have u6_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u3_305 hv
  have u7_123 : Q {0, 1, 2, 5} := by
    by_contra hv
    exact c4 h u0_121 u4_122 hv u5_124 n125 n126 n127
  exact c2087 h u7_123 u6_89 a118

theorem c31264_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → ¬ Q {0, 4, 5, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  classical
  intro a102 n185 n71 n120
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
  have u4_121 : Q {0, 1, 2, 3} := h0
  have u5_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u4_121 hv n120
  have u6_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c1059 h hv n71
  have u7_241 : Q {1, 4, 5, 6} := by
    by_contra hv
    exact c31261 h h0 n185 hv u5_101 u6_276
  have u8_50 : T {1, 4, 5} := by
    by_contra hv
    exact c744 h u7_241 hv
  have u9_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1506 h u7_241 n185 u6_276 hv u0_316 u1_317 u2_318
  have u10_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1284 h u9_296 hv
  have u11_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8475 h hv u8_50 u10_86 u5_101
  have u12_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8335 h hv u8_50 u10_86 u5_101
  have u13_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1359 h u9_296 hv
  have u14_55 : T {1, 5, 6} := by
    by_contra hv
    exact c819 h u7_241 hv
  have u15_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c31262 h h0 hv u6_276 u5_101
  have u16_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv n120
  have u17_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c1805 h u4_121 a102 hv
  have u18_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28823 h hv u3_1 a102
  have u19_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1823 h u4_121 u5_101 a102 hv
  have u20_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c31258 h h0 hv n71 n120 a102
  have u21_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10719 h hv u8_50 u5_101 a102
  have u22_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2563 h hv u10_86 u5_101 a102
  have u23_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2703 h hv u10_86 u5_101 a102
  have u24_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1938 h u4_121 hv u17_119 n120
  have u25_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u4_121 u19_103 hv
  have u26_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6151 h hv u14_55 u24_110
  have u27_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2371 h hv u13_91 u24_110
  have u28_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c31263 h h0 hv u27_125 u25_118 u23_127 u22_126 u21_184 u20_240 u18_314 u10_86 u15_275 u16_315
  have u29_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c1495 h hv u21_184 u20_240 u15_275 u28_311 u18_314 u16_315
  have u30_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c1487 h hv u21_184 u20_240 u15_275 u29_305 u28_311 u18_314 u16_315
  have u31_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18604 h u7_241 hv u30_100
  have u32_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c26311 h u9_296 u31_13 hv
  have u33_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6976 h hv u32_64 u30_100 u17_119
  have u34_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7536 h hv u32_64 u30_100 u17_119
  have u35_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c192 h hv u27_125 u26_152 u33_157 u34_161 u12_167 u11_168
  exact c182 h u31_13 u27_125 u26_152 u33_157 u34_161 u35_164 u12_167 u11_168

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31264_oai := @OAI.BorsukNine.FiniteObstruction.c31264_oai
