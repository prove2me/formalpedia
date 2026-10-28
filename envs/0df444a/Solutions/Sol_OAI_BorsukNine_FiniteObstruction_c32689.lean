-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32689
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:24:52.572461+00:00
-- url     : https://prove2.me/submissions/1c25a993-c3a5-4778-a781-85060c020055

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

theorem c163 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {0, 2, 5} → False := by
  intro a162 n11
  exact n11 (h.down {0, 2, 5, 8} {0, 2, 5} a162 (by decide) (by decide))

theorem c213 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {0, 2, 9} → False := by
  intro a127 n15
  exact n15 (h.down {0, 1, 2, 9} {0, 2, 9} a127 (by decide) (by decide))

theorem c215 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {0, 2, 9} → False := by
  intro a154 n15
  exact n15 (h.down {0, 2, 3, 9} {0, 2, 9} a154 (by decide) (by decide))

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

theorem c305 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {0, 3, 9} → False := by
  intro a154 n21
  exact n21 (h.down {0, 2, 3, 9} {0, 3, 9} a154 (by decide) (by decide))

theorem c306 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a154 n133 n174 n178 n181 n183 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 9} {0, 3, 9} a154 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c313 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 9} → False := by
  intro a183 n21
  exact n21 (h.down {0, 3, 7, 9} {0, 3, 9} a183 (by decide) (by decide))

theorem c341 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {0, 4, 6} → False := by
  intro a189 n23
  exact n23 (h.down {0, 4, 6, 7} {0, 4, 6} a189 (by decide) (by decide))

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

theorem c388 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {0, 4, 9} → False := by
  intro a193 n26
  exact n26 (h.down {0, 4, 7, 9} {0, 4, 9} a193 (by decide) (by decide))

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

theorem c519 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {0, 7, 9} → False := by
  intro a193 n35
  exact n35 (h.down {0, 4, 7, 9} {0, 7, 9} a193 (by decide) (by decide))

theorem c543 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {1, 2, 3} → False := by
  intro a121 n37
  exact n37 (h.down {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide))

theorem c557 (h : TenSystem T Q) :
    T {1, 2, 4} → ¬ Q {0, 1, 2, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 2, 4, 8} → ¬ Q {1, 2, 4, 9} → False := by
  intro a38 n122 n205 n211 n212 n213 n214 n215
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 4} a38
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n122 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 4} = {1, 2, 4, 5} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 4} = {1, 2, 4, 6} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 4} = {1, 2, 4, 7} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 4} = {1, 2, 4, 8} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 4} = {1, 2, 4, 9} by decide)) hS)

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

theorem c602 (h : TenSystem T Q) :
    T {1, 2, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 2, 7, 9} → False := by
  intro a41 n125 n208 n213 n217 n220 n223 n224
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 7} a41
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n125 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 7} = {1, 2, 7, 8} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 7} = {1, 2, 7, 9} by decide)) hS)

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

theorem c684 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 3, 6} → False := by
  intro a231 n46
  exact n46 (h.down {1, 3, 5, 6} {1, 3, 6} a231 (by decide) (by decide))

theorem c688 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {1, 3, 6} → False := by
  intro a236 n46
  exact n46 (h.down {1, 3, 6, 8} {1, 3, 6} a236 (by decide) (by decide))

theorem c716 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {1, 3, 8} → False := by
  intro a236 n48
  exact n48 (h.down {1, 3, 6, 8} {1, 3, 8} a236 (by decide) (by decide))

theorem c723 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a133 n49
  exact n49 (h.down {0, 1, 3, 9} {1, 3, 9} a133 (by decide) (by decide))

theorem c729 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 3, 9} → False := by
  intro a234 n49
  exact n49 (h.down {1, 3, 5, 9} {1, 3, 9} a234 (by decide) (by decide))

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

theorem c812 (h : TenSystem T Q) :
    T {1, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 6, 9} → False := by
  intro a55 n139 n216 n231 n241 n251 n252 n253
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 6} a55
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
  · exact n252 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 6} = {1, 5, 6, 8} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 6} = {1, 5, 6, 9} by decide)) hS)

theorem c814 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 6, 9} → False := by
  intro a139 n216 n231 n241 n251 n252 n253
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 6} {1, 5, 6} a139 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 6} = {1, 5, 6, 7} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 6} = {1, 5, 6, 8} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 6} = {1, 5, 6, 9} by decide)) hS)

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

theorem c843 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {1, 5, 8} → False := by
  intro a141 n57
  exact n57 (h.down {0, 1, 5, 8} {1, 5, 8} a141 (by decide) (by decide))

theorem c844 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a141 n218 n233 n243 n252 n254 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 8} {1, 5, 8} a141 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c846 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a218 n141 n233 n243 n252 n254 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 8} {1, 5, 8} a218 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c847 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 5, 8} → False := by
  intro a233 n57
  exact n57 (h.down {1, 3, 5, 8} {1, 5, 8} a233 (by decide) (by decide))

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

theorem c887 (h : TenSystem T Q) :
    T {1, 6, 8} → ¬ Q {0, 1, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 8, 9} → False := by
  intro a60 n144 n221 n236 n246 n252 n257 n259
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 6, 8} a60
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n144 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n221 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n259 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 8} = {1, 6, 8, 9} by decide)) hS)

theorem c889 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 8, 9} → False := by
  intro a144 n221 n236 n246 n252 n257 n259
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 6, 8} {1, 6, 8} a144 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n221 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n259 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 8} = {1, 6, 8, 9} by decide)) hS)

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

theorem c988 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {2, 3, 5} → False := by
  intro a268 n66
  exact n66 (h.down {2, 3, 5, 8} {2, 3, 5} a268 (by decide) (by decide))

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

theorem c1038 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a154 n70
  exact n70 (h.down {0, 2, 3, 9} {2, 3, 9} a154 (by decide) (by decide))

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

theorem c1095 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {2, 4, 7} → False := by
  intro a284 n73
  exact n73 (h.down {2, 4, 7, 9} {2, 4, 7} a284 (by decide) (by decide))

theorem c1112 (h : TenSystem T Q) :
    T {2, 4, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {2, 4, 8, 9} → False := by
  intro a75 n159 n215 n265 n279 n282 n284 n285
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 9} a75
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n159 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n279 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1157 (h : TenSystem T Q) :
    T {2, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 8, 9} → False := by
  intro a78 n162 n218 n268 n278 n287 n289 n291
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 5, 8} a78
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
  · exact n291 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 8} = {2, 5, 8, 9} by decide)) hS)

theorem c1166 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {2, 5, 8} → False := by
  intro a287 n78
  exact n78 (h.down {2, 5, 6, 8} {2, 5, 8} a287 (by decide) (by decide))

theorem c1218 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {2, 6, 9} → False := by
  intro a166 n82
  exact n82 (h.down {0, 2, 6, 9} {2, 6, 9} a166 (by decide) (by decide))

theorem c1247 (h : TenSystem T Q) :
    T {2, 7, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {2, 7, 8, 9} → False := by
  intro a84 n168 n224 n274 n284 n290 n293 n295
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 7, 9} a84
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n168 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 7, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n274 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 7, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n295 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 7, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1301 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 4, 6} → False := by
  intro a300 n87
  exact n87 (h.down {3, 4, 6, 7} {3, 4, 6} a300 (by decide) (by decide))

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

theorem c1399 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 5, 8, 9} → False := by
  intro a178 n234 n269 n299 n308 n310 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 9} {3, 5, 9} a178 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n234 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n308 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1442 (h : TenSystem T Q) :
    T {3, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a97 n181 n237 n272 n302 n308 n313 n314
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 6, 9} a97
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1444 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a181 n237 n272 n302 n308 n313 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 6, 9} {3, 6, 9} a181 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1533 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a187 n103
  exact n103 (h.down {0, 4, 5, 8} {4, 5, 8} a187 (by decide) (by decide))

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

theorem c1564 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a189 n245 n280 n300 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 7} {4, 6, 7} a189 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
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

theorem c1627 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a284 n109
  exact n109 (h.down {2, 4, 7, 9} {4, 7, 9} a284 (by decide) (by decide))

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

theorem c1730 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a256 n116
  exact n116 (h.down {1, 5, 8, 9} {5, 8, 9} a256 (by decide) (by decide))

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

theorem c1732 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a291 n116
  exact n116 (h.down {2, 5, 8, 9} {5, 8, 9} a291 (by decide) (by decide))

theorem c1749 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a312 n117
  exact n117 (h.down {3, 6, 7, 8} {6, 7, 8} a312 (by decide) (by decide))

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

theorem c1947 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 8} → T {6, 7, 9} → False := by
  intro a122 a93 a118
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a118

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

theorem c2463 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a125 a93 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 7} {5, 8} {3, 4, 6} a125 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

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

theorem c3909 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 3, 9} → T {5, 6, 8} → False := by
  intro a136 a70 a112
  have hc := h.complementary {0, 1, 4, 7} {2, 3, 9} a136 (by decide) (by decide)
  have he : ( {0, 1, 4, 7} : Finset Labels)ᶜ \ {2, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a70 a112

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

theorem c4604 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 3, 6} → ¬ T {4, 7, 9} → False := by
  intro a141 n67 n109
  have hc := h.complementary {0, 1, 5, 8} {2, 3, 6} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n67 (hc.mpr n109)

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

theorem c5292 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a145 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 9} {5, 8} {3, 4, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

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

theorem c6005 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 7} → T {5, 8, 9} → False := by
  intro a151 a52 a116
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 7} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a52 a116

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

theorem c6424 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a154 n51 n114
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 6} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n114)

theorem c6426 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 7} → ¬ T {5, 6, 8} → False := by
  intro a154 n52 n112
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n112)

theorem c6427 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 7} → T {5, 6, 8} → False := by
  intro a154 a52 a112
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a112

theorem c6434 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a154 n57 n105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n105)

theorem c6435 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {4, 6, 7} → False := by
  intro a154 a57 a105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a105

theorem c6436 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a154 n59 n103
  have hc := h.complementary {0, 2, 3, 9} {1, 6, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n59 (hc.mpr n103)

theorem c6531 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a154 a57 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {5, 8} {1, 4, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c6535 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a154 a57 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {5, 8} {1, 6, 7} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

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

theorem c6947 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a157 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {5, 8} {1, 6, 9} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c7237 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {3, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a159 a93 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {5, 8} {3, 6, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

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

theorem c7647 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a162 a52 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 7} {1, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c8513 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a168 a93 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {5, 8} {3, 4, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

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

theorem c9045 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a172 a57 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {5, 8} {1, 2, 9} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c9047 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a172 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {5, 8} {1, 6, 9} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c9223 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 2, 5} → T {6, 7, 8} → False := by
  intro a174 a39 a117
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 5} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a39 a117

theorem c9224 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 6} → ¬ T {5, 7, 8} → False := by
  intro a174 n40 n114
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 6} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n114)

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

theorem c9739 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a177 a51 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 6} {1, 7, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c9745 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a177 a52 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 7} {1, 2, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c9746 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a177 n52 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 8} {4, 7} {1, 6, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c9763 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a177 a59 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {6, 7} {1, 4, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c9773 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {2, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a177 a82 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {6, 9} {2, 4, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c10165 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a180 a52 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 8} {4, 7} {1, 2, 9} a180 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c10206 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 7} → ¬ T {4, 5, 8} → False := by
  intro a181 n41 n103
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n103)

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

theorem c10485 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 2, 5} → T {4, 6, 8} → False := by
  intro a183 a39 a106
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 5} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a39 a106

theorem c10693 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 5} → T {2, 4, 5} → T {2, 5, 7} → False := by
  intro a184 a39 a71 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {2, 5} {1, 4, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

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

theorem c10965 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 9} → False := by
  intro a186 a37 a67 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {2, 3} {1, 6, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c11153 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 7, 9} → False := by
  intro a187 a49 a70 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {3, 9} {1, 2, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c11334 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 3, 9} → ¬ T {2, 5, 8} → False := by
  intro a189 n49 n78
  have hc := h.complementary {0, 4, 6, 7} {1, 3, 9} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n78)

theorem c11337 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 5, 8} → T {2, 3, 9} → False := by
  intro a189 a57 a70
  have hc := h.complementary {0, 4, 6, 7} {1, 5, 8} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a70

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

theorem c11385 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {2, 3, 5} → T {2, 3, 9} → False := by
  intro a189 a37 a66 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {2, 3} {1, 5, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c11442 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a189 n57 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {5, 8} {1, 3, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c11807 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 9} → False := by
  intro a192 a37 a67 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {2, 3} {1, 6, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

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

theorem c11890 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 5} → ¬ T {2, 6, 8} → False := by
  intro a193 n45 n81
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 5} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n81)

theorem c11892 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {2, 5, 8} → False := by
  intro a193 n46 n78
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n46 (hc.mpr n78)

theorem c11893 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 3, 6} → T {2, 5, 8} → False := by
  intro a193 a46 a78
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a46 a78

theorem c11894 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 8} → ¬ T {2, 5, 6} → False := by
  intro a193 n48 n76
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 8} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n48 (hc.mpr n76)

theorem c11898 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 5, 8} → ¬ T {2, 3, 6} → False := by
  intro a193 n57 n67
  have hc := h.complementary {0, 4, 7, 9} {1, 5, 8} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n67)

theorem c11911 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a193 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 3} {2, 5, 6} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c11915 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 8} → False := by
  intro a193 a37 a46 a48
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 3} {2, 6, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)

theorem c11930 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 2, 6} → ¬ T {1, 5, 6} → ¬ T {1, 6, 8} → False := by
  intro a193 n40 n55 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {1, 6} {2, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) ht)

theorem c11932 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {1, 5, 6} → ¬ T {1, 6, 8} → False := by
  intro a193 n46 n55 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {1, 6} {3, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) ht)

theorem c11963 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 8} → False := by
  intro a193 a40 a76 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {2, 6} {1, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) a81)

theorem c11982 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 5, 6} → False := by
  intro a193 n46 n67 n91
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {3, 6} {1, 2, 5} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) ht)

theorem c11984 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 8} → False := by
  intro a193 n46 n67 n96
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {3, 6} {1, 2, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) ht)

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

theorem c12367 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {2, 3, 7} → T {2, 3, 9} → False := by
  intro a196 a37 a68 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 3} {1, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12380 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 7, 9} → False := by
  intro a196 n41 n68 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 7} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c12393 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {2, 3, 9} → T {2, 4, 9} → T {2, 7, 9} → False := by
  intro a196 a70 a75 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 9} {3, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

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

theorem c12647 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 9} → False := by
  intro a198 a37 a67 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {2, 3} {1, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12684 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 9} → False := by
  intro a198 n46 n67 n97
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {3, 6} {1, 2, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n97 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) ht)

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

theorem c12863 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {4, 6, 7} → False := by
  intro a200 a37 a105
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 3} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a105

theorem c12878 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 4, 7} → ¬ T {2, 3, 6} → False := by
  intro a200 n52 n67
  have hc := h.complementary {0, 5, 8, 9} {1, 4, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n67)

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

theorem c13567 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 8} → T {6, 7, 9} → False := by
  intro a205 a29 a118
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a118

theorem c13853 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 5, 8} → T {4, 7, 9} → False := by
  intro a207 a29 a109
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 8} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a109

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

theorem c14083 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a208 a29 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {5, 8} {0, 4, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

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

theorem c14497 (h : TenSystem T Q) :
    Q {1, 2, 4, 5} → T {0, 6, 7} → T {3, 6, 7} → T {6, 7, 9} → False := by
  intro a211 a31 a95 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 5} {6, 7} {0, 3, 9} a211 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c14549 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {0, 3, 9} → T {5, 7, 8} → False := by
  intro a212 a21 a114
  have hc := h.complementary {1, 2, 4, 6} {0, 3, 9} a212 (by decide) (by decide)
  have he : ( {1, 2, 4, 6} : Finset Labels)ᶜ \ {0, 3, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a114

theorem c14685 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → T {0, 3, 6} → T {5, 8, 9} → False := by
  intro a213 a18 a116
  have hc := h.complementary {1, 2, 4, 7} {0, 3, 6} a213 (by decide) (by decide)
  have he : ( {1, 2, 4, 7} : Finset Labels)ᶜ \ {0, 3, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a18 a116

theorem c14689 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → T {0, 3, 9} → T {5, 6, 8} → False := by
  intro a213 a21 a112
  have hc := h.complementary {1, 2, 4, 7} {0, 3, 9} a213 (by decide) (by decide)
  have he : ( {1, 2, 4, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a112

theorem c14941 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → T {0, 6, 7} → T {3, 6, 7} → T {6, 7, 9} → False := by
  intro a214 a31 a95 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 8} {6, 7} {0, 3, 9} a214 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c14977 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 6, 7} → T {3, 5, 8} → False := by
  intro a215 a31 a93
  have hc := h.complementary {1, 2, 4, 9} {0, 6, 7} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a31 a93

theorem c15077 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {3, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a215 a93 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 9} {5, 8} {3, 6, 7} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c15155 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 3, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a216 a21 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {0, 9} {3, 4, 7} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

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

theorem c15337 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 4, 6} → T {3, 4, 6} → T {4, 6, 9} → False := by
  intro a217 a23 a87 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 7} {4, 6} {0, 3, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c15437 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 3, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a218 a21 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {0, 9} {3, 4, 7} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

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

theorem c15669 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 3, 9} → T {4, 5, 8} → False := by
  intro a220 a21 a103
  have hc := h.complementary {1, 2, 6, 7} {0, 3, 9} a220 (by decide) (by decide)
  have he : ( {1, 2, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a103

theorem c15857 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {0, 3, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a221 a21 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 8} {0, 9} {3, 4, 7} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

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

theorem c16185 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → T {0, 4, 6} → T {3, 4, 6} → T {4, 6, 9} → False := by
  intro a223 a23 a87 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 8} {4, 6} {0, 3, 9} a223 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c16233 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 4, 6} → T {3, 5, 8} → False := by
  intro a224 a23 a93
  have hc := h.complementary {1, 2, 7, 9} {0, 4, 6} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a23 a93

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

theorem c16885 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a228 a29 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {5, 8} {0, 2, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c17255 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a231 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {0, 9} {2, 4, 7} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c17298 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a231 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 6} {4, 7} {0, 8, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c17537 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a233 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {0, 9} {2, 4, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c17579 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a233 a23 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 7, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c17585 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a233 a24 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 7} {0, 2, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c17957 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a236 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {0, 9} {2, 4, 7} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c18005 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a236 a24 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {4, 7} {0, 2, 9} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c18655 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a241 a15 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {0, 9} {2, 3, 7} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

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

theorem c18937 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a243 a15 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 9} {2, 3, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c18969 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 9} → T {2, 3, 9} → T {2, 7, 9} → False := by
  intro a243 a15 a70 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {2, 9} {0, 3, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c19177 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 5, 8} → T {2, 3, 9} → False := by
  intro a245 a29 a70
  have hc := h.complementary {1, 4, 6, 7} {0, 5, 8} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a70

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

theorem c19357 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a246 a15 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {0, 9} {2, 3, 7} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c19475 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a247 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 9} {0, 3} {2, 7, 8} a247 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19725 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 5} → T {3, 6, 8} → False := by
  intro a249 a11 a96
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a96

theorem c19726 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 6} → ¬ T {3, 5, 8} → False := by
  intro a249 n12 n93
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n93)

theorem c19729 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 8} → T {3, 5, 6} → False := by
  intro a249 a14 a91
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a14 a91

theorem c19731 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 3, 5} → T {2, 6, 8} → False := by
  intro a249 a17 a81
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a17 a81

theorem c19732 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {2, 5, 8} → False := by
  intro a249 n18 n78
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n78)

theorem c19735 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 3, 8} → T {2, 5, 6} → False := by
  intro a249 a20 a76
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a20 a76

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

theorem c20055 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 9} → T {0, 3, 9} → T {0, 4, 9} → False := by
  intro a251 a15 a21 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {0, 9} {2, 3, 4} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)

theorem c20157 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 4, 7} → T {2, 3, 9} → False := by
  intro a252 a24 a70
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 7} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a70

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

theorem c20288 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {0, 2, 8} → ¬ T {3, 4, 7} → False := by
  intro a253 n14 n88
  have hc := h.complementary {1, 5, 6, 9} {0, 2, 8} a253 (by decide) (by decide)
  have he : ( {1, 5, 6, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n88)

theorem c20294 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {0, 3, 8} → ¬ T {2, 4, 7} → False := by
  intro a253 n20 n73
  have hc := h.complementary {1, 5, 6, 9} {0, 3, 8} a253 (by decide) (by decide)
  have he : ( {1, 5, 6, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n73)

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

theorem c20475 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 4, 9} → False := by
  intro a254 a15 a21 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 9} {2, 3, 4} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)

theorem c20507 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 9} → T {2, 3, 9} → T {2, 4, 9} → False := by
  intro a254 a15 a70 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {2, 9} {0, 3, 4} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)

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

theorem c20895 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 4, 9} → False := by
  intro a257 a15 a21 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 8} {0, 9} {2, 3, 4} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)

theorem c21126 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 5} → ¬ T {3, 4, 7} → False := by
  intro a259 n11 n88
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 5} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n88)

theorem c21132 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 5} → ¬ T {2, 4, 7} → False := by
  intro a259 n17 n73
  have hc := h.complementary {1, 6, 8, 9} {0, 3, 5} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n73)

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

theorem c21645 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 5, 8} → T {1, 5, 8} → T {5, 8, 9} → False := by
  intro a262 a29 a57 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {5, 8} {0, 1, 9} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c21785 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 5, 8} → T {1, 5, 8} → T {5, 8, 9} → False := by
  intro a263 a29 a57 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {5, 8} {0, 1, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c22075 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a265 a29 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {5, 8} {0, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

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

theorem c22197 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 7} → T {1, 4, 7} → T {4, 7, 9} → False := by
  intro a266 a24 a52 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {4, 7} {0, 1, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c22485 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 7} → T {1, 4, 7} → T {4, 7, 9} → False := by
  intro a268 a24 a52 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 7} {0, 1, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

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

theorem c22528 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 1, 8} → ¬ T {4, 6, 7} → False := by
  intro a269 n7 n105
  have hc := h.complementary {2, 3, 5, 9} {0, 1, 8} a269 (by decide) (by decide)
  have he : ( {2, 3, 5, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n105)

theorem c22781 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 5, 8} → T {1, 5, 8} → T {5, 8, 9} → False := by
  intro a270 a29 a57 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {5, 8} {0, 1, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c22905 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → T {1, 4, 7} → T {4, 7, 9} → False := by
  intro a271 a24 a52 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {4, 7} {0, 1, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22959 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 5, 8} → T {1, 4, 7} → False := by
  intro a272 a29 a52
  have hc := h.complementary {2, 3, 6, 9} {0, 5, 8} a272 (by decide) (by decide)
  have he : ( {2, 3, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a52

theorem c23351 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a274 a29 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 9} {5, 8} {0, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

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

theorem c23673 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a277 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {0, 3} {1, 6, 9} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c23694 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 6, 9} → False := by
  intro a277 n8 n21 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 7} {0, 9} {1, 3, 6} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) ht)

theorem c23813 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a278 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {0, 3} {1, 6, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c23815 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a278 a2 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {0, 3} {1, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c24039 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a279 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {6, 7} {0, 1, 3} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c24063 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {5, 8, 9} → False := by
  intro a280 a2 a116
  have hc := h.complementary {2, 4, 6, 7} {0, 1, 3} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a116

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

theorem c24343 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {5, 7, 8} → False := by
  intro a282 a2 a114
  have hc := h.complementary {2, 4, 6, 9} {0, 1, 3} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a114

theorem c24353 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 3, 7} → T {1, 5, 8} → False := by
  intro a282 a19 a57
  have hc := h.complementary {2, 4, 6, 9} {0, 3, 7} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a19 a57

theorem c24515 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a283 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {0, 3} {1, 6, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

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

theorem c24633 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 3, 6} → T {1, 5, 8} → False := by
  intro a284 a18 a57
  have hc := h.complementary {2, 4, 7, 9} {0, 3, 6} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a18 a57

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

theorem c24639 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 5, 8} → T {1, 3, 6} → False := by
  intro a284 a29 a46
  have hc := h.complementary {2, 4, 7, 9} {0, 5, 8} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a46

theorem c24643 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 6} → False := by
  intro a284 a2 a4 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 1} {3, 5, 6} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c24647 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 1, 6} → T {0, 1, 8} → False := by
  intro a284 a2 a5 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 1} {3, 6, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c24653 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a284 a2 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 3} {1, 5, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24724 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {1, 3, 6} → ¬ T {3, 6, 8} → False := by
  intro a284 n18 n46 n96
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {3, 6} {0, 1, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 6} = {0, 3, 6} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) ht)

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

theorem c24895 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a285 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {6, 7} {0, 1, 3} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c25043 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {4, 7, 9} → False := by
  intro a287 a2 a109
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 3} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a109

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

theorem c25351 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a289 a2 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {0, 3} {1, 4, 6} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c25355 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a289 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {0, 3} {1, 6, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

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

theorem c25579 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → T {0, 4, 6} → T {1, 4, 6} → T {3, 4, 6} → False := by
  intro a290 a23 a51 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 9} {4, 6} {0, 1, 3} a290 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c25883 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → T {0, 1, 3} → T {4, 5, 8} → False := by
  intro a293 a2 a103
  have hc := h.complementary {2, 6, 7, 9} {0, 1, 3} a293 (by decide) (by decide)
  have he : ( {2, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a103

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

theorem c26287 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 4, 6} → T {1, 4, 6} → T {3, 4, 6} → False := by
  intro a295 a23 a51 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 7, 8, 9} {4, 6} {0, 1, 3} a295 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c26473 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a297 a1 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {0, 2} {1, 6, 9} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

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

theorem c26723 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {6, 7, 8} → False := by
  intro a299 a1 a117
  have hc := h.complementary {3, 4, 5, 9} {0, 1, 2} a299 (by decide) (by decide)
  have he : ( {3, 4, 5, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a117

theorem c26863 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {5, 8, 9} → False := by
  intro a300 a1 a116
  have hc := h.complementary {3, 4, 6, 7} {0, 1, 2} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a116

theorem c26877 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 5, 8} → T {1, 2, 9} → False := by
  intro a300 a29 a43
  have hc := h.complementary {3, 4, 6, 7} {0, 5, 8} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a43

theorem c26893 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 9} → False := by
  intro a300 a1 a11 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 2} {1, 5, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

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

theorem c27013 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 2, 7} → T {1, 5, 9} → False := by
  intro a301 a13 a58
  have hc := h.complementary {3, 4, 6, 8} {0, 2, 7} a301 (by decide) (by decide)
  have he : ( {3, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a58

theorem c27063 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a301 a1 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {1, 2} {0, 5, 7} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c27065 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a301 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {1, 2} {0, 5, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27102 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 2, 7} → ¬ T {1, 2, 7} → ¬ T {2, 5, 7} → False := by
  intro a301 n13 n41 n77
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 8} {2, 7} {0, 1, 5} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) ht)

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

theorem c27315 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a303 a1 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {0, 2} {1, 6, 9} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

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

theorem c27857 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 7} → T {1, 2, 9} → False := by
  intro a307 a24 a43
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 7} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a43

theorem c27860 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 7, 9} → ¬ T {1, 2, 4} → False := by
  intro a307 n35 n38
  have hc := h.complementary {3, 5, 6, 8} {0, 7, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n38)

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

theorem c27901 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a307 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 9} {2, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c27905 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a307 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 2} {0, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27955 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {2, 4, 9} → T {2, 7, 9} → False := by
  intro a307 a15 a75 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {2, 9} {0, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c27970 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 4, 9} → ¬ T {2, 4, 9} → ¬ T {4, 7, 9} → False := by
  intro a307 n26 n75 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {4, 9} {0, 2, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n26 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

theorem c28099 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a308 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {4, 7} {0, 1, 2} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

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

theorem c28403 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {4, 6, 7} → False := by
  intro a311 a1 a105
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 2} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a105

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

theorem c28527 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a311 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {4, 7} {0, 1, 2} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

theorem c28543 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {4, 5, 9} → False := by
  intro a312 a1 a104
  have hc := h.complementary {3, 6, 7, 8} {0, 1, 2} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a104

theorem c28555 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 2, 9} → T {1, 4, 5} → False := by
  intro a312 a15 a50
  have hc := h.complementary {3, 6, 7, 8} {0, 2, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a15 a50

theorem c28607 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a312 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 5, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28618 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 1, 5} → ¬ T {1, 2, 5} → ¬ T {1, 4, 5} → False := by
  intro a312 n4 n39 n50
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {1, 5} {0, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) ht)
  · exact n50 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) ht)

theorem c28655 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 2, 9} → T {2, 4, 9} → T {2, 5, 9} → False := by
  intro a312 a15 a75 a79
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {2, 9} {0, 4, 5} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)

theorem c28664 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {1, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 9} → False := by
  intro a312 n50 n71 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {4, 5} {1, 2, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c28680 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {1, 5, 9} → ¬ T {2, 5, 9} → ¬ T {4, 5, 9} → False := by
  intro a312 n58 n79 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {5, 9} {1, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n58 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) ht)
  · exact n79 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 9} = {2, 5, 9} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)

theorem c28683 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {4, 5, 8} → False := by
  intro a313 a1 a103
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 2} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a103

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

theorem c28947 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a314 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {4, 7} {0, 1, 2} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

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

theorem c31555 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → False := by
  classical
  intro a189 n300 n280 n245
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  exact c1564 h a189 n245 n280 n300 u0_316 u1_322 u2_323

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

theorem c31704 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  classical
  intro a112 a103 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1879 h u0_121 a103 a112 a114

theorem c31705 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n116 n103 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1880 h u0_121 n103 n112 n116

theorem c31706 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  classical
  intro a112 a103 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1881 h u0_121 a103 a112 a116

theorem c31707 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro n116 n114 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1882 h u0_121 n103 n114 n116

theorem c31709 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n116 n114 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1884 h u0_121 n112 n114 n116

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

theorem c31785 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 7} → T {2, 3, 6} → T {2, 3, 9} → False := by
  classical
  intro a186 a67 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10965 h a186 u0_37 a67 a70

theorem c31815 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {2, 3, 5} → T {2, 3, 9} → False := by
  classical
  intro a189 a66 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11385 h a189 u0_37 a66 a70

theorem c31819 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {0, 4, 6, 8} → T {1, 2, 9} → False := by
  classical
  intro a39 a190 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11485 h a190 u0_37 a39 a43

theorem c31846 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 8} → T {2, 3, 6} → T {2, 3, 9} → False := by
  classical
  intro a192 a67 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11807 h a192 u0_37 a67 a70

theorem c31847 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a193 a112
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11883 h a193 u0_37 a112

theorem c31851 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → T {1, 3, 5} → T {1, 3, 6} → False := by
  classical
  intro a193 a45 a46
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11911 h a193 u0_37 a45 a46

theorem c31853 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → T {1, 3, 8} → T {1, 3, 6} → False := by
  classical
  intro a193 a48 a46
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11915 h a193 u0_37 a46 a48

theorem c31886 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 7} → T {2, 3, 9} → Q {0, 5, 6, 8} → False := by
  classical
  intro a68 a70 a196
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12367 h a196 u0_37 a68 a70

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

theorem c31906 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {2, 3, 6} → T {2, 3, 9} → False := by
  classical
  intro a198 a67 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12647 h a198 u0_37 a67 a70

theorem c31917 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a200 a105
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12863 h a200 u0_37 a105

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

theorem c32182 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 7} → T {0, 3, 6} → T {0, 3, 9} → False := by
  classical
  intro a277 a18 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23673 h a277 u0_2 a18 a21

theorem c32192 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → T {0, 3, 6} → T {0, 3, 9} → False := by
  classical
  intro a278 a18 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23813 h a278 u0_2 a18 a21

theorem c32193 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → T {0, 3, 7} → T {0, 3, 9} → False := by
  classical
  intro a278 a19 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23815 h a278 u0_2 a19 a21

theorem c32207 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a280 a116
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24063 h a280 u0_2 a116

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

theorem c32227 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a282 a114
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24343 h a282 u0_2 a114

theorem c32243 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 8} → T {0, 3, 6} → T {0, 3, 9} → False := by
  classical
  intro a283 a18 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24515 h a283 u0_2 a18 a21

theorem c32247 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a284 a112
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24623 h a284 u0_2 a112

theorem c32248 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 5} → Q {2, 4, 7, 9} → T {0, 1, 6} → False := by
  classical
  intro a4 a284 a5
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24643 h a284 u0_2 a4 a5

theorem c32250 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 8} → Q {2, 4, 7, 9} → T {0, 1, 6} → False := by
  classical
  intro a7 a284 a5
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24647 h a284 u0_2 a5 a7

theorem c32252 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {0, 3, 5} → T {0, 3, 8} → False := by
  classical
  intro a284 a17 a20
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24653 h a284 u0_2 a17 a20

theorem c32277 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a287 a109
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25043 h a287 u0_2 a109

theorem c32301 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → T {0, 3, 6} → Q {2, 5, 7, 8} → False := by
  classical
  intro a16 a18 a289
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25351 h a289 u0_2 a16 a18

theorem c32303 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 6} → T {0, 3, 9} → Q {2, 5, 7, 8} → False := by
  classical
  intro a18 a21 a289
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25355 h a289 u0_2 a18 a21

theorem c32337 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 6, 7, 9} → T {4, 5, 8} → False := by
  classical
  intro a293 a103
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25883 h a293 u0_2 a103

theorem c32382 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 7} → T {0, 2, 6} → T {0, 2, 9} → False := by
  classical
  intro a297 a12 a15
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26473 h a297 u0_1 a12 a15

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

theorem c32397 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a299 a117
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26723 h a299 u0_1 a117

theorem c32407 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a300 a116
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26863 h a300 u0_1 a116

theorem c32412 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → T {0, 2, 9} → T {0, 2, 5} → False := by
  classical
  intro a300 a15 a11
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26893 h a300 u0_1 a11 a15

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

theorem c32424 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 8} → T {1, 2, 5} → T {1, 2, 7} → False := by
  classical
  intro a301 a39 a41
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27063 h a301 u0_1 a39 a41

theorem c32425 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a301 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27065 h a301 u0_1 a39 a43

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

theorem c32443 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 8} → T {0, 2, 6} → T {0, 2, 9} → False := by
  classical
  intro a303 a12 a15
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27315 h a303 u0_1 a12 a15

theorem c32446 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 8} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a303 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27347 h a303 u0_1 a40 a43

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

theorem c32507 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 9} → T {4, 6, 8} → False := by
  classical
  intro a310 a106
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28263 h a310 u0_1 a106

theorem c32517 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a311 a105
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28403 h a311 u0_1 a105

theorem c32527 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {4, 5, 9} → False := by
  classical
  intro a312 a104
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28543 h a312 u0_1 a104

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

theorem c32642 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 9} → False := by
  classical
  intro a234
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c729 h a234 u0_49

theorem c32643 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 6, 9} → False := by
  classical
  intro a237
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  exact c731 h a237 u0_49

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
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases124
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32672 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {0, 3, 5, 8} → T {1, 4, 7} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 8} → ¬ T {1, 3, 6} → ¬ T {5, 6, 8} → T {4, 7, 9} → T {0, 5, 8} → T {2, 3, 9} → False := by
  classical
  intro a280 n314 n308 n177 a52 n196 n141 n46 n112 a109 a29 a70
  have u0_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u1_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c22959 h hv a29 a52
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1567 h a280 hv
  have u3_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32207 h h0 a280 hv
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u2_105
  have u5_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7647 h hv a52 u2_105 a109
  have u6_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u3_116 hv n112
  have u7_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31705 h h0 u3_116 hv n112
  have u8_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h n177 n141 a29 u4_200 u5_162 hv n196
  have u9_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u6_114
  have u10_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c32537 h h0 hv u7_103
  have u11_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c31906 h h0 u8_198 hv a70
  have u12_97 : T {3, 6, 9} := by
    by_contra hv
    exact c12684 h u8_198 n46 u11_67 hv
  have u13_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c1444 h hv u0_237 u1_272 u9_302 n308 u10_313 n314
  exact c1442 h u12_97 u13_181 u0_237 u1_272 u9_302 n308 u10_313 n314

private theorem c32673 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {2, 4, 6, 7} → Q {2, 4, 7, 9} → ¬ Q {1, 4, 6, 7} → Q {0, 2, 3, 9} → False := by
  classical
  intro n116 n280 a284 n245 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1627 h a284 hv
  have u3_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32247 h h0 a284 hv
  have u4_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv u3_112
  have u5_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22485 h hv u0_24 u4_52 u2_109
  have u6_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c32277 h h0 hv u2_109
  have u7_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u8_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u9_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h a284 hv
  have u10_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18969 h hv u7_15 u8_70 u9_84
  have u11_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h a284 hv
  have u12_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20507 h hv u7_15 u8_70 u11_75
  have u13_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4657 h hv u8_70 u11_75 u9_84
  have u14_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h a284 hv
  have u15_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17585 h hv u0_24 u14_73 u2_109
  have u16_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u0_24 u8_70
  have u17_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u18_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv n116
  have u19_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1732 h hv n116
  have u20_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv n116
  have u21_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c846 h hv u13_141 u15_233 u10_243 u16_252 u12_254 u18_256
  have u22_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c6435 h a154 hv u20_105
  have u23_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 n245 u20_105 hv
  have u24_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7647 h hv u4_52 u20_105 u2_109
  have u25_18 : T {0, 3, 6} := by
    by_contra hv
    exact c24632 h a284 hv u22_57
  have u26_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u23_189 u1_49 hv
  have u27_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c32303 h h0 u25_18 u17_21 hv
  have u28_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c32192 h h0 hv u25_18 u17_21
  exact c1157 h u26_78 u24_162 u21_218 u5_268 u28_278 u6_287 u27_289 u19_291

theorem c32674 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a284 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c32642 h h0 hv
  have u2_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u4_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u3_70
  have u5_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u6_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h a284 hv
  have u7_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h a284 hv
  have u8_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h a284 hv
  have u9_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1627 h a284 hv
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32247 h h0 a284 hv
  have u11_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c24639 h a284 a29 hv
  have u12_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18005 h hv u0_24 u6_73 u9_109
  have u13_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27955 h hv u5_15 u7_75 u8_84
  have u14_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4657 h hv u3_70 u7_75 u8_84
  have u15_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12393 h hv u3_70 u7_75 u8_84
  have u16_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv u10_112
  have u17_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9745 h hv u16_52 u6_73 u9_109
  have u18_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22905 h hv u0_24 u16_52 u9_109
  have u19_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28527 h hv u0_24 u16_52 u6_73
  have u20_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28099 h hv u0_24 u16_52 u6_73
  have u21_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28947 h hv u0_24 u16_52 u6_73
  have u22_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10165 h hv u16_52 u6_73 u9_109
  have u23_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32672 h h0 hv u21_314 u20_308 u17_177 u16_52 u15_196 u14_141 u11_46 u10_112 u9_109 a29 u3_70
  have u24_116 : T {5, 8, 9} := by
    by_contra hv
    exact c32673 h h0 hv u23_280 a284 u4_245 a154
  have u25_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv u24_116
  have u26_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u25_105
  have u27_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c24747 h a284 a29 u26_57 hv
  have u28_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10219 h hv u26_57 u6_73
  have u29_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c24633 h a284 hv u26_57
  have u30_5 : T {0, 1, 6} := by
    by_contra hv
    exact c24626 h a284 hv u27_93
  have u31_96 : T {3, 6, 8} := by
    by_contra hv
    exact c24724 h a284 u29_18 u11_46 hv
  have u32_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c32248 h h0 hv a284 u30_5
  have u33_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c32250 h h0 hv a284 u30_5
  have u34_312 : Q {3, 6, 7, 8} := by
    by_contra hv
    exact c31327 h u21_314 u22_180 hv u31_96 u18_271 u13_307 u12_236
  have u35_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22528 h hv u33_7 u25_105
  have u36_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h u34_312 hv
  have u37_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 u34_312 hv
  have u38_301 : Q {3, 4, 6, 8} := by
    by_contra hv
    exact c1439 h u34_312 u22_180 u12_236 u18_271 hv u13_307 u21_314
  have u39_50 : ¬ T {1, 4, 5} := by
    intro hv
    exact c28555 h u34_312 u5_15 hv
  have u40_39 : T {1, 2, 5} := by
    by_contra hv
    exact c28618 h u34_312 u32_4 hv u39_50
  have u41_79 : ¬ T {2, 5, 9} := by
    intro hv
    exact c28655 h u34_312 u5_15 u7_75 hv
  have u42_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u36_117
  have u43_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9223 h hv u40_39 u36_117
  have u44_58 : T {1, 5, 9} := by
    by_contra hv
    exact c28680 h u34_312 hv u41_79 u37_104
  have u45_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1584 h u38_301 hv
  have u46_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c27013 h u38_301 hv u44_58
  have u47_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32424 h h0 u38_301 u40_39 hv
  have u48_77 : T {2, 5, 7} := by
    by_contra hv
    exact c27102 h u38_301 u46_13 u47_41 hv
  have u49_71 : T {2, 4, 5} := by
    by_contra hv
    exact c28664 h u34_312 u39_50 hv u37_104
  have u50_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10485 h hv u40_39 u45_106
  have u51_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u45_106
  have u52_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10693 h hv u40_39 u49_71 u48_77
  have u53_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c1399 h hv u1_234 u35_269 u42_299 u20_308 u51_310 u19_311
  exact c306 h a154 u2_133 u43_174 u53_178 u28_181 u50_183 u52_184

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases125
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32680 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 7, 9} → T {4, 7, 9} → ¬ Q {2, 4, 7, 9} → False := by
  classical
  intro n193 a109 n284
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 n193 a109 hv u0_304
  exact c31574 h h0 u1_249 n284 n193 u0_304

private theorem c32681 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → T {5, 8, 9} → Q {0, 4, 7, 9} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n46 n67 a116 a193 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u3_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u2_105
  have u4_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21785 h hv a29 u3_57 a116
  have u5_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32407 h h0 hv a116
  have u6_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h a193 hv
  have u7_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u8_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h a193 hv
  have u9_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15857 h hv u7_21 u6_26 u8_35
  have u10_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15155 h hv u7_21 u6_26 u8_35
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u12_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19357 h hv u11_15 u7_21 u8_35
  have u13_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18655 h hv u11_15 u7_21 u8_35
  have u14_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20055 h hv u11_15 u7_21 u6_26
  have u15_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20895 h hv u11_15 u7_21 u6_26
  have u16_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u17_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 a193 u16_284 hv u1_304
  have u18_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u19_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u0_24 u18_70
  have u20_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c684 h hv n46
  have u21_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c688 h hv n46
  have u22_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11892 h a193 n46 hv
  have u23_91 : T {3, 5, 6} := by
    by_contra hv
    exact c11982 h a193 n46 n67 hv
  have u24_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c12007 h a193 u3_57 u22_78 hv
  have u25_96 : T {3, 6, 8} := by
    by_contra hv
    exact c11984 h a193 n46 n67 hv
  have u26_12 : T {0, 2, 6} := by
    by_contra hv
    exact c19726 h u17_249 hv u24_93
  have u27_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c19725 h u17_249 hv u25_96
  have u28_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c19729 h u17_249 hv u23_91
  have u29_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9045 h hv u3_57 u22_78 a116
  have u30_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16885 h hv a29 u22_78 a116
  have u31_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32382 h h0 hv u26_12 u11_15
  have u32_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32443 h h0 hv u26_12 u11_15
  have u33_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u29_172 u30_228 u4_263 u31_297 u5_300 u32_303 u1_304
  have u34_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21126 h hv u27_11 u33_88
  have u35_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20288 h hv u28_14 u33_88
  have u36_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c889 h hv u9_221 u21_236 u12_246 u19_252 u15_257 u34_259
  have u37_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c814 h hv u10_216 u20_231 u13_241 u14_251 u19_252 u35_253
  have u38_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c887 h hv u36_144 u9_221 u21_236 u12_246 u19_252 u15_257 u34_259
  have u39_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c812 h hv u37_139 u10_216 u20_231 u13_241 u14_251 u19_252 u35_253
  exact c11932 h a193 n46 u39_55 u38_60

private theorem c32682 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ T {5, 6, 8} → ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a116 n112 n280 a29 a154
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u5_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv u4_109 u3_284
  have u6_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h u5_193 hv
  have u7_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u8_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h u5_193 hv
  have u9_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c17957 h hv u7_15 u8_26 u6_35
  have u10_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17255 h hv u7_15 u8_26 u6_35
  have u11_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u12_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15857 h hv u11_21 u8_26 u6_35
  have u13_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15155 h hv u11_21 u8_26 u6_35
  have u14_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19357 h hv u7_15 u11_21 u6_35
  have u15_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18655 h hv u7_15 u11_21 u6_35
  have u16_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20055 h hv u7_15 u11_21 u8_26
  have u17_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20895 h hv u7_15 u11_21 u8_26
  have u18_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 u5_193 u3_284 hv u2_304
  have u19_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv n112
  have u20_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c22959 h hv a29 u19_52
  have u21_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22197 h hv u1_24 u19_52 u4_109
  have u22_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22905 h hv u1_24 u19_52 u4_109
  have u23_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13853 h hv a29 u4_109
  have u24_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 n112
  have u25_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u26_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u1_24 u25_70
  have u27_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u28_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6005 h hv u19_52 a116
  have u29_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u27_105
  have u30_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21645 h hv a29 u29_57 a116
  have u31_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21785 h hv a29 u29_57 a116
  have u32_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22781 h hv a29 u29_57 a116
  have u33_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c992 h hv u28_151 u23_207 u30_262 u21_266 u32_270 u22_271 u20_272
  have u34_46 : T {1, 3, 6} := by
    by_contra hv
    exact c32681 h h0 hv u33_67 a116 u5_193 a29 a154
  have u35_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c31853 h h0 u5_193 hv u34_46
  have u36_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c31851 h h0 u5_193 hv u34_46
  have u37_78 : ¬ T {2, 5, 8} := by
    intro hv
    exact c11893 h u5_193 u34_46 hv
  have u38_76 : T {2, 5, 6} := by
    by_contra hv
    exact c11894 h u5_193 u35_48 hv
  have u39_81 : T {2, 6, 8} := by
    by_contra hv
    exact c11890 h u5_193 u36_45 hv
  have u40_18 : T {0, 3, 6} := by
    by_contra hv
    exact c19732 h u18_249 hv u37_78
  have u41_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c19735 h u18_249 hv u38_76
  have u42_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c11963 h u5_193 hv u38_76 u39_81
  have u43_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c19731 h u18_249 hv u39_81
  have u44_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14685 h hv u40_18 a116
  have u45_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c32182 h h0 hv u40_18 u11_21
  have u46_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c32243 h h0 hv u40_18 u11_21
  have u47_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c1082 h hv u24_157 u44_213 u31_263 u45_277 n280 u46_283 u3_284
  have u48_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20294 h hv u41_20 u47_73
  have u49_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21132 h hv u43_17 u47_73
  have u50_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c814 h hv u13_216 u10_231 u15_241 u16_251 u26_252 u48_253
  have u51_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c889 h hv u12_221 u9_236 u14_246 u26_252 u17_257 u49_259
  have u52_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c812 h hv u50_139 u13_216 u10_231 u15_241 u16_251 u26_252 u48_253
  have u53_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c887 h hv u51_144 u12_221 u9_236 u14_246 u26_252 u17_257 u49_259
  exact c11930 h u5_193 u42_40 u52_55 u53_60

private theorem c32683 (h : TenSystem T Q) :
    ¬ Q {1, 5, 8, 9} → ¬ Q {1, 5, 7, 8} → T {1, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 2, 5, 8} → False := by
  classical
  intro n256 n254 a57 n243 n252 n233 n218
  have u0_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c842 h a57 hv n218 n233 n243 n252 n254 n256
  exact c844 h u0_141 n218 n233 n243 n252 n254 n256

theorem c32684 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 8} → ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n112 n280 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u4_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u0_24 u3_70
  have u5_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u6_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u8_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv u7_109 u2_284
  have u9_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h u8_193 hv
  have u10_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h u8_193 hv
  have u11_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 u8_193 u2_284 hv u1_304
  have u12_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20475 h hv u6_15 u5_21 u9_26
  have u13_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18937 h hv u6_15 u5_21 u10_35
  have u14_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17537 h hv u6_15 u9_26 u10_35
  have u15_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15437 h hv u5_21 u9_26 u10_35
  have u16_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32682 h h0 hv n112 n280 a29 a154
  have u17_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u11_249 a29 hv
  have u18_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv u16_116
  have u19_57 : T {1, 5, 8} := by
    by_contra hv
    exact c11898 h u8_193 hv u17_67
  exact c32683 h u18_256 u12_254 u19_57 u13_243 u4_252 u14_233 u15_218

private theorem c32686 (h : TenSystem T Q) :
    ¬ T {2, 3, 6} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → T {0, 5, 8} → False := by
  classical
  intro n67 n187 n198 n177 n162 n52 n109 a29
  have u0_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4604 h hv n67 n109
  have u1_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12878 h hv n52 n67
  have u2_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32648 h u0_141 n187 hv n198 a29 n177 n162
  exact c432 h u2_196 u0_141 n162 n177 n187 n198 u1_200

theorem c32687 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 8} → T {5, 6, 8} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a57 a112 a29 a154
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c6427 h a154 hv a112
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u4_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c3909 h hv u3_70 a112
  have u5_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31847 h h0 hv a112
  have u6_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c6435 h a154 a57 hv
  have u8_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11337 h hv a57 u3_70
  have u9_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c6535 h a154 a57 a112 hv
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c6531 h a154 a57 hv a112
  have u11_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u7_105 hv
  have u12_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 u7_105
  have u13_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9746 h hv u2_52 u7_105 u6_109
  have u14_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u9_114
  have u15_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1533 h hv u10_103
  have u16_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6947 h hv a57 a112 u11_116
  have u17_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9047 h hv a57 a112 u11_116
  have u18_67 : T {2, 3, 6} := by
    by_contra hv
    exact c32686 h hv u15_187 u14_198 u13_177 u12_162 u2_52 u6_109 a29
  have u19_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c31785 h h0 hv u18_67 u3_70
  have u20_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c31846 h h0 hv u18_67 u3_70
  exact c347 h u1_24 u4_136 u16_157 u17_172 u19_186 u8_189 u20_192 u5_193

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases126
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32688 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n103 n280 a29 a154
  have u0_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u1_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u0_70
  have u2_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32684 h h0 hv n280 a29 a154
  have u3_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32687 h h0 hv u2_112 a29 a154
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c6434 h a154 u3_57 hv
  have u5_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 u1_245 u4_105 hv
  have u6_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c31815 h h0 u5_189 hv u0_70
  have u7_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c988 h hv u6_66
  have u8_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c31555 h h0 u5_189 hv n280 u1_245
  have u9_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h u8_300 hv
  have u10_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u4_105 hv
  have u11_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11442 h u5_189 u3_57 hv u10_116
  have u12_31 : T {0, 6, 7} := by
    by_contra hv
    exact c459 h u5_189 hv
  have u13_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14977 h hv u12_31 u11_93
  have u14_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32517 h h0 hv u4_105
  have u15_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c847 h hv u3_57
  have u16_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u17_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14689 h hv u16_21 u2_112
  have u18_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u2_112
  have u19_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u20_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u21_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u22_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 n103 hv
  have u23_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31707 h h0 u10_116 hv n103
  have u24_59 : T {1, 6, 7} := by
    by_contra hv
    exact c6436 h a154 hv n103
  have u25_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv a29 u22_118
  have u26_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1947 h hv u11_93 u22_118
  have u27_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14941 h hv u12_31 u9_95 u22_118
  have u28_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c14497 h hv u12_31 u9_95 u22_118
  have u29_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c32227 h h0 hv u23_114
  have u30_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv a29 u2_112 u23_114
  have u31_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7237 h hv u11_93 u2_112 u23_114
  have u32_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14549 h hv u16_21 u23_114
  have u33_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9763 h hv u24_59 u4_105 u22_118
  have u34_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24895 h hv u12_31 u24_59 u9_95
  have u35_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c24039 h hv u12_31 u24_59 u9_95
  have u36_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c557 h hv u26_122 u25_205 u28_211 u32_212 u17_213 u27_214 u13_215
  have u37_75 : ¬ T {2, 4, 9} := by
    intro hv
    exact c1112 h hv u31_159 u13_215 u30_265 u35_279 u29_282 u19_284 u34_285
  have u38_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32591 h u7_268 u15_233 u11_93 u14_311 u33_177 hv u21_298
  have u39_26 : T {0, 4, 9} := by
    by_contra hv
    exact c27970 h u38_307 hv u37_75 u18_109
  have u40_35 : T {0, 7, 9} := by
    by_contra hv
    exact c27860 h u38_307 hv u36_38
  exact c27901 h u38_307 u20_15 u39_26 u40_35

theorem c32689_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n280 a29 a154
  have u0_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u1_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u2_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u1_70
  have u3_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u4_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u5_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32684 h h0 hv n280 a29 a154
  have u6_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14689 h hv u3_21 u5_112
  have u7_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32687 h h0 hv u5_112 a29 a154
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c843 h hv u7_57
  have u9_105 : T {4, 6, 7} := by
    by_contra hv
    exact c6434 h a154 u7_57 hv
  have u10_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u9_105 hv
  have u11_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u9_105
  have u12_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 u2_245 u9_105 hv
  have u13_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u12_189 hv
  have u14_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c31555 h h0 u12_189 hv n280 u2_245
  have u15_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11442 h u12_189 u7_57 hv u10_116
  have u16_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16233 h hv u13_23 u15_93
  have u17_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u14_300 hv
  have u18_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c32412 h h0 u14_300 u4_15 hv
  have u19_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c163 h hv u18_11
  have u20_103 : T {4, 5, 8} := by
    by_contra hv
    exact c32688 h h0 hv n280 a29 a154
  have u21_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c32337 h h0 hv u20_103
  have u22_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31704 h h0 u5_112 u20_103 hv
  have u23_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23351 h hv a29 u20_103 u5_112
  have u24_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8513 h hv u15_93 u20_103 u5_112
  have u25_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14083 h hv a29 u20_103 u5_112
  have u26_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15669 h hv u3_21 u20_103
  have u27_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2463 h hv u15_93 u20_103 u5_112
  have u28_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u22_114
  have u29_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u22_114
  have u30_51 : T {1, 4, 6} := by
    by_contra hv
    exact c6424 h a154 hv u22_114
  have u31_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9739 h hv u30_51 u9_105 u29_107
  have u32_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16185 h hv u13_23 u17_87 u29_107
  have u33_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15337 h hv u13_23 u17_87 u29_107
  have u34_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25579 h hv u13_23 u30_51 u17_87
  have u35_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c26287 h hv u13_23 u30_51 u17_87
  have u36_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31443 h u31_177 u8_141 a29 u11_200 u19_162 u28_198 hv
  have u37_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c602 h hv u27_125 u25_208 u6_213 u33_217 u26_220 u32_223 u16_224
  have u38_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c1247 h hv u24_168 u16_224 u23_274 u0_284 u34_290 u21_293 u35_295
  have u39_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c31886 h h0 hv u1_70 u36_196
  exact c12380 h u36_196 u37_41 u39_68 u38_84

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32689_oai := @OAI.BorsukNine.FiniteObstruction.c32689_oai
