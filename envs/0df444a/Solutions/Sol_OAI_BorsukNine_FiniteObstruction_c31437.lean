-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31437
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:08:28.561954+00:00
-- url     : https://prove2.me/submissions/a1df9388-f373-4d71-a516-4ced07727402

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

theorem c54 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {0, 1, 5} → False := by
  intro a139 n4
  exact n4 (h.down {0, 1, 5, 6} {0, 1, 5} a139 (by decide) (by decide))

theorem c69 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {0, 1, 6} → False := by
  intro a139 n5
  exact n5 (h.down {0, 1, 5, 6} {0, 1, 6} a139 (by decide) (by decide))

theorem c110 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {0, 1, 9} → False := by
  intro a133 n8
  exact n8 (h.down {0, 1, 3, 9} {0, 1, 9} a133 (by decide) (by decide))

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

theorem c160 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 9} → False := by
  intro a160 n123 n150 n155 n161 n162 n163
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 6} {0, 2, 5} a160 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n123 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n150 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n161 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 5} = {0, 2, 5, 7} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 5} = {0, 2, 5, 8} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 5} = {0, 2, 5, 9} by decide)) hS)

theorem c174 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {0, 2, 6} → False := by
  intro a160 n12
  exact n12 (h.down {0, 2, 5, 6} {0, 2, 6} a160 (by decide) (by decide))

theorem c176 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {0, 2, 6} → False := by
  intro a164 n12
  exact n12 (h.down {0, 2, 6, 7} {0, 2, 6} a164 (by decide) (by decide))

theorem c189 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ T {0, 2, 7} → False := by
  intro a161 n13
  exact n13 (h.down {0, 2, 5, 7} {0, 2, 7} a161 (by decide) (by decide))

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

theorem c264 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {0, 3, 6} → False := by
  intro a175 n18
  exact n18 (h.down {0, 3, 5, 6} {0, 3, 6} a175 (by decide) (by decide))

theorem c279 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {0, 3, 7} → False := by
  intro a176 n19
  exact n19 (h.down {0, 3, 5, 7} {0, 3, 7} a176 (by decide) (by decide))

theorem c303 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {0, 3, 9} → False := by
  intro a133 n21
  exact n21 (h.down {0, 1, 3, 9} {0, 3, 9} a133 (by decide) (by decide))

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

theorem c370 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a187 n137 n158 n173 n190 n192 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 4, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
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

theorem c392 (h : TenSystem T Q) :
    T {0, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 6, 9} → False := by
  intro a27 n139 n160 n175 n185 n195 n196 n197
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 6} a27
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n139 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact n160 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n175 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n185 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 6} = {0, 5, 6, 7} by decide)) hS)
  · exact n196 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 6} = {0, 5, 6, 8} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 6} = {0, 5, 6, 9} by decide)) hS)

theorem c402 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 6, 9} → False := by
  intro a195 n139 n160 n175 n185 n196 n197
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 7} {0, 5, 6} a195 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n139 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact n160 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n175 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n185 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 6} = {0, 5, 6, 8} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 6} = {0, 5, 6, 9} by decide)) hS)

theorem c407 (h : TenSystem T Q) :
    T {0, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a28 n140 n161 n176 n186 n195 n198 n199
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 7} a28
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c417 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a195 n140 n161 n176 n186 n198 n199
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 7} {0, 5, 7} a195 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c421 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → False := by
  intro a199 n140 n161 n176 n186 n195 n198
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 7, 9} {0, 5, 7} a199 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)

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

theorem c534 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a194 n36
  exact n36 (h.down {0, 4, 8, 9} {0, 8, 9} a194 (by decide) (by decide))

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

theorem c665 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {1, 3, 5} → False := by
  intro a206 n45
  exact n45 (h.down {1, 2, 3, 5} {1, 3, 5} a206 (by decide) (by decide))

theorem c669 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 3, 5} → False := by
  intro a231 n45
  exact n45 (h.down {1, 3, 5, 6} {1, 3, 5} a231 (by decide) (by decide))

theorem c675 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 3, 5} → False := by
  intro a234 n45
  exact n45 (h.down {1, 3, 5, 9} {1, 3, 5} a234 (by decide) (by decide))

theorem c680 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {1, 3, 6} → False := by
  intro a207 n46
  exact n46 (h.down {1, 2, 3, 6} {1, 3, 6} a207 (by decide) (by decide))

theorem c684 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 3, 6} → False := by
  intro a231 n46
  exact n46 (h.down {1, 3, 5, 6} {1, 3, 6} a231 (by decide) (by decide))

theorem c690 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 3, 6} → False := by
  intro a237 n46
  exact n46 (h.down {1, 3, 6, 9} {1, 3, 6} a237 (by decide) (by decide))

theorem c705 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 7} → False := by
  intro a239 n47
  exact n47 (h.down {1, 3, 7, 9} {1, 3, 7} a239 (by decide) (by decide))

theorem c722 (h : TenSystem T Q) :
    T {1, 3, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a49 n133 n210 n230 n234 n237 n239 n240
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 9} a49
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
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c724 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a133 n210 n230 n234 n237 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 9} {1, 3, 9} a133 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c730 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a234 n133 n210 n230 n237 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 9} {1, 3, 9} a234 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c732 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a237 n133 n210 n230 n234 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 6, 9} {1, 3, 9} a237 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c734 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a239 n133 n210 n230 n234 n237 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 7, 9} {1, 3, 9} a239 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c748 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {1, 4, 5} → False := by
  intro a243 n50
  exact n50 (h.down {1, 4, 5, 8} {1, 4, 5} a243 (by decide) (by decide))

theorem c789 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {1, 4, 8} → False := by
  intro a243 n53
  exact n53 (h.down {1, 4, 5, 8} {1, 4, 8} a243 (by decide) (by decide))

theorem c810 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {1, 4, 9} → False := by
  intro a250 n54
  exact n54 (h.down {1, 4, 8, 9} {1, 4, 9} a250 (by decide) (by decide))

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

theorem c817 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 5, 6} → False := by
  intro a231 n55
  exact n55 (h.down {1, 3, 5, 6} {1, 5, 6} a231 (by decide) (by decide))

theorem c826 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 8} → False := by
  intro a253 n139 n216 n231 n241 n251 n252
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 9} {1, 5, 6} a253 (by decide) (by decide)
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
  · exact hne (by decide)

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

theorem c862 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 5, 9} → False := by
  intro a234 n58
  exact n58 (h.down {1, 3, 5, 9} {1, 5, 9} a234 (by decide) (by decide))

theorem c907 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 6, 9} → False := by
  intro a237 n61
  exact n61 (h.down {1, 3, 6, 9} {1, 6, 9} a237 (by decide) (by decide))

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

theorem c937 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a239 n63
  exact n63 (h.down {1, 3, 7, 9} {1, 7, 9} a239 (by decide) (by decide))

theorem c954 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a250 n64
  exact n64 (h.down {1, 4, 8, 9} {1, 8, 9} a250 (by decide) (by decide))

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

theorem c999 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {2, 3, 6} → False := by
  intro a266 n67
  exact n67 (h.down {2, 3, 5, 6} {2, 3, 6} a266 (by decide) (by decide))

theorem c1044 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {2, 3, 9} → False := by
  intro a269 n70
  exact n70 (h.down {2, 3, 5, 9} {2, 3, 9} a269 (by decide) (by decide))

theorem c1063 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {2, 4, 5} → False := by
  intro a278 n71
  exact n71 (h.down {2, 4, 5, 8} {2, 4, 5} a278 (by decide) (by decide))

theorem c1097 (h : TenSystem T Q) :
    T {2, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {1, 2, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 7, 8} → ¬ Q {2, 4, 8, 9} → False := by
  intro a74 n158 n214 n264 n278 n281 n283 n285
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 8} a74
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n158 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 8} = {1, 2, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n278 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n283 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 8} = {2, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n285 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 8} = {2, 4, 8, 9} by decide)) hS)

theorem c1111 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → ¬ Q {0, 2, 4, 8} → ¬ Q {1, 2, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 7, 8} → False := by
  intro a285 n158 n214 n264 n278 n281 n283
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 8, 9} {2, 4, 8} a285 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n158 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 8} = {1, 2, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n278 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n283 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 8} = {2, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

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

theorem c1127 (h : TenSystem T Q) :
    T {2, 5, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 6, 9} → False := by
  intro a76 n160 n216 n266 n276 n286 n287 n288
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 5, 6} a76
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
  · exact n287 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 6} = {2, 5, 6, 8} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 6} = {2, 5, 6, 9} by decide)) hS)

theorem c1128 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {2, 5, 6} → False := by
  intro a160 n76
  exact n76 (h.down {0, 2, 5, 6} {2, 5, 6} a160 (by decide) (by decide))

theorem c1136 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {2, 5, 6} → False := by
  intro a286 n76
  exact n76 (h.down {2, 5, 6, 7} {2, 5, 6} a286 (by decide) (by decide))

theorem c1141 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → ¬ Q {0, 2, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 5, 6, 8} → False := by
  intro a288 n160 n216 n266 n276 n286 n287
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 9} {2, 5, 6} a288 (by decide) (by decide)
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
  · exact n287 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 6} = {2, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1184 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {2, 5, 8, 9} → False := by
  intro a290 n163 n219 n269 n279 n288 n291
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 7, 9} {2, 5, 9} a290 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n163 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n269 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1187 (h : TenSystem T Q) :
    T {2, 6, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 6, 7, 9} → False := by
  intro a80 n164 n220 n270 n280 n286 n292 n293
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 6, 7} a80
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n164 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 6, 7} = {2, 6, 7, 8} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 6, 7} = {2, 6, 7, 9} by decide)) hS)

theorem c1196 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {2, 6, 7} → False := by
  intro a286 n80
  exact n80 (h.down {2, 5, 6, 7} {2, 6, 7} a286 (by decide) (by decide))

theorem c1201 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ Q {0, 2, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → False := by
  intro a293 n164 n220 n270 n280 n286 n292
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 7, 9} {2, 6, 7} a293 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n164 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 6, 7} = {2, 6, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1209 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {2, 6, 8} → False := by
  intro a281 n81
  exact n81 (h.down {2, 4, 6, 8} {2, 6, 8} a281 (by decide) (by decide))

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

theorem c1288 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 4, 5} → False := by
  intro a298 n86
  exact n86 (h.down {3, 4, 5, 8} {3, 4, 5} a298 (by decide) (by decide))

theorem c1329 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 4, 8} → False := by
  intro a298 n89
  exact n89 (h.down {3, 4, 5, 8} {3, 4, 8} a298 (by decide) (by decide))

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

theorem c1352 (h : TenSystem T Q) :
    T {3, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 6, 9} → False := by
  intro a91 n175 n231 n266 n296 n306 n307 n308
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 6} a91
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 6} = {3, 5, 6, 7} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 6} = {3, 5, 6, 9} by decide)) hS)

theorem c1355 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {3, 5, 6} → False := by
  intro a231 n91
  exact n91 (h.down {1, 3, 5, 6} {3, 5, 6} a231 (by decide) (by decide))

theorem c1366 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 6, 8} → False := by
  intro a308 n175 n231 n266 n296 n306 n307
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 9} {3, 5, 6} a308 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 6} = {3, 5, 6, 7} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1400 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {3, 5, 9} → False := by
  intro a234 n94
  exact n94 (h.down {1, 3, 5, 9} {3, 5, 9} a234 (by decide) (by decide))

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

theorem c1475 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a239 n99
  exact n99 (h.down {1, 3, 7, 9} {3, 7, 9} a239 (by decide) (by decide))

theorem c1481 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a310 n99
  exact n99 (h.down {3, 5, 7, 9} {3, 7, 9} a310 (by decide) (by decide))

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

theorem c1494 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a305 n100
  exact n100 (h.down {3, 4, 8, 9} {3, 8, 9} a305 (by decide) (by decide))

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

theorem c1536 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a243 n187 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 8} {4, 5, 8} a243 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

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

theorem c1579 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a190 n246 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {4, 6, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1581 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a246 n190 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 8} {4, 6, 8} a246 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
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

theorem c1638 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a194 n110
  exact n110 (h.down {0, 4, 8, 9} {4, 8, 9} a194 (by decide) (by decide))

theorem c1639 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {2, 4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a194 n250 n285 n305 n321 n324 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 8, 9} {4, 8, 9} a194 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n250 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 8, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1643 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a285 n194 n250 n305 n321 n324 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 8, 9} {4, 8, 9} a285 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n194 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c1776 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a259 n203 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 8, 9} {6, 8, 9} a259 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1787 (h : TenSystem T Q) :
    T {7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {4, 7, 8, 9} → ¬ Q {5, 7, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a120 n204 n260 n295 n315 n325 n329 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {7, 8, 9} a120
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {7, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n204 (Eq.mp (congrArg Q (show insert (0 : Labels) {7, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (1 : Labels) {7, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact n295 (Eq.mp (congrArg Q (show insert (2 : Labels) {7, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (3 : Labels) {7, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (4 : Labels) {7, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (5 : Labels) {7, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact n330 (Eq.mp (congrArg Q (show insert (6 : Labels) {7, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

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

theorem c1821 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 6, 7} → False := by
  intro a121 a110 a111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a110 a111

theorem c1831 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 6, 7} → T {4, 6, 8} → False := by
  intro a121 a101 a105 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

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

theorem c1849 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {4, 6, 8} → T {4, 8, 9} → False := by
  intro a121 a103 a106 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c1850 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n103 n108 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1851 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {4, 7, 8} → T {4, 8, 9} → False := by
  intro a121 a103 a108 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c1852 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n106 n108 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1853 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {4, 7, 8} → T {4, 8, 9} → False := by
  intro a121 a106 a108 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

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

theorem c1872 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → ¬ T {5, 7, 9} → False := by
  intro a121 n102 n111 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 7} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c1901 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 7} → T {6, 7, 8} → T {6, 7, 9} → False := by
  intro a121 a111 a117 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

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

theorem c1916 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n113 n118 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

theorem c1925 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a121 a114 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c1932 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 7, 9} → ¬ T {6, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n115 n118 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c2098 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {3, 7, 9} → ¬ T {4, 6, 8} → False := by
  intro a123 n99 n106
  have hc := h.complementary {0, 1, 2, 5} {3, 7, 9} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 7, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n99 (hc.mpr n106)

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

theorem c3488 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 4, 8} → ¬ T {5, 6, 7} → False := by
  intro a133 n74 n111
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 8} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n74 (hc.mpr n111)

theorem c3489 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 8} → T {5, 6, 7} → False := by
  intro a133 a74 a111
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 8} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a74 a111

theorem c3490 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 5, 6} → ¬ T {4, 7, 8} → False := by
  intro a133 n76 n108
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n76 (hc.mpr n108)

theorem c3491 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 5, 6} → T {4, 7, 8} → False := by
  intro a133 a76 a108
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a76 a108

theorem c3492 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 5, 7} → ¬ T {4, 6, 8} → False := by
  intro a133 n77 n106
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n77 (hc.mpr n106)

theorem c3493 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 5, 7} → T {4, 6, 8} → False := by
  intro a133 a77 a106
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a77 a106

theorem c3496 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a133 n80 n103
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n80 (hc.mpr n103)

theorem c3497 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 6, 7} → T {4, 5, 8} → False := by
  intro a133 a80 a103
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a80 a103

theorem c3499 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 6, 8} → T {4, 5, 7} → False := by
  intro a133 a81 a102
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 8} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a81 a102

theorem c3511 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a133 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 6, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c3567 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 8} → T {4, 5, 8} → T {4, 6, 8} → False := by
  intro a133 a74 a103 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {4, 8} {2, 5, 6} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)

theorem c3569 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 8} → T {4, 5, 8} → T {4, 7, 8} → False := by
  intro a133 a74 a103 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {4, 8} {2, 5, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c3997 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 5, 6} → T {3, 5, 6} → T {5, 6, 9} → False := by
  intro a136 a76 a91 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {5, 6} {2, 3, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c4139 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a137 a76 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {5, 6} {2, 7, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

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

theorem c4147 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 5, 7} → T {5, 6, 7} → T {5, 7, 9} → False := by
  intro a137 a77 a111 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {5, 7} {2, 6, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) a115)

theorem c4163 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a137 a80 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {6, 7} {2, 5, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c4333 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → T {2, 4, 8} → T {3, 7, 9} → False := by
  intro a139 a74 a99
  have hc := h.complementary {0, 1, 5, 6} {2, 4, 8} a139 (by decide) (by decide)
  have he : ( {0, 1, 5, 6} : Finset Labels)ᶜ \ {2, 4, 8} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a74 a99

theorem c4468 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {2, 3, 9} → ¬ T {4, 6, 8} → False := by
  intro a140 n70 n106
  have hc := h.complementary {0, 1, 5, 7} {2, 3, 9} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 3, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n70 (hc.mpr n106)

theorem c4479 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 6, 9} → T {3, 4, 8} → False := by
  intro a140 a82 a89
  have hc := h.complementary {0, 1, 5, 7} {2, 6, 9} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 6, 9} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a82 a89

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

theorem c5878 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 7, 9} → ¬ T {4, 6, 8} → False := by
  intro a150 n63 n106
  have hc := h.complementary {0, 2, 3, 5} {1, 7, 9} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 7, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n63 (hc.mpr n106)

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

theorem c6625 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {1, 3, 6} → T {3, 6, 7} → T {3, 6, 9} → False := by
  intro a155 a46 a95 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {3, 6} {1, 7, 9} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) a97)

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

theorem c6865 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 5} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a157 a45 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {1, 3} {5, 6, 9} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c6989 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 3, 9} → T {5, 6, 7} → False := by
  intro a158 a49 a111
  have hc := h.complementary {0, 2, 4, 8} {1, 3, 9} a158 (by decide) (by decide)
  have he : ( {0, 2, 4, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a49 a111

theorem c7009 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 3, 6} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a158 a46 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {1, 3} {6, 7, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c7091 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 9} → T {3, 5, 9} → T {5, 6, 9} → False := by
  intro a158 a58 a94 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 9} {1, 3, 6} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)

theorem c7093 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 9} → T {3, 5, 9} → T {5, 7, 9} → False := by
  intro a158 a58 a94 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 9} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c7109 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 6, 9} → T {3, 6, 9} → T {6, 7, 9} → False := by
  intro a158 a61 a97 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {6, 9} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

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

theorem c7615 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 6} → T {3, 6, 7} → T {3, 6, 9} → False := by
  intro a162 a46 a95 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {3, 6} {1, 7, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) a97)

theorem c7695 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 4, 8} → T {3, 6, 7} → False := by
  intro a163 a53 a95
  have hc := h.complementary {0, 2, 5, 9} {1, 4, 8} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 4, 8} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a53 a95

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

theorem c9037 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 6} → T {2, 5, 6} → T {5, 6, 9} → False := by
  intro a172 a55 a76 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {5, 6} {1, 2, 9} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

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

theorem c9181 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a173 a76 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {5, 6} {2, 7, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c9189 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 5, 7} → T {5, 6, 7} → T {5, 7, 9} → False := by
  intro a173 a77 a111 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {5, 7} {2, 6, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) a115)

theorem c9205 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a173 a80 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {6, 7} {2, 5, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c9373 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 4, 8} → T {2, 7, 9} → False := by
  intro a175 a53 a84
  have hc := h.complementary {0, 3, 5, 6} {1, 4, 8} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 4, 8} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a53 a84

theorem c9379 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 7, 9} → T {2, 4, 8} → False := by
  intro a175 a63 a74
  have hc := h.complementary {0, 3, 5, 6} {1, 7, 9} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a63 a74

theorem c9508 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {1, 2, 9} → ¬ T {4, 6, 8} → False := by
  intro a176 n43 n106
  have hc := h.complementary {0, 3, 5, 7} {1, 2, 9} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n106)

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

theorem c10793 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a185 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 3} {2, 7, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c10833 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 7} → T {2, 3, 7} → T {2, 7, 9} → False := by
  intro a185 a41 a68 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {2, 7} {1, 3, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) a84)

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

theorem c11073 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a187 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 3} {2, 6, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11075 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a187 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 3} {2, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11211 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a188 a37 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 9} {1, 3} {2, 6, 7} a188 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

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

theorem c11353 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a189 a37 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 3} {2, 5, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11493 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a190 a37 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 3} {2, 5, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11495 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a190 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 3} {2, 7, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11755 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 3, 9} → T {2, 5, 6} → False := by
  intro a192 a49 a76
  have hc := h.complementary {0, 4, 7, 8} {1, 3, 9} a192 (by decide) (by decide)
  have he : ( {0, 4, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a49 a76

theorem c11773 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a192 a37 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {1, 3} {2, 5, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c11911 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a193 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 3} {2, 5, 6} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c12023 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {5, 6, 7} → False := by
  intro a194 a37 a111
  have hc := h.complementary {0, 4, 8, 9} {1, 2, 3} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a111

theorem c12031 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 3, 5} → T {2, 6, 7} → False := by
  intro a194 a45 a80
  have hc := h.complementary {0, 4, 8, 9} {1, 3, 5} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a45 a80

theorem c12033 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 3, 6} → T {2, 5, 7} → False := by
  intro a194 a46 a77
  have hc := h.complementary {0, 4, 8, 9} {1, 3, 6} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a46 a77

theorem c12035 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 3, 7} → T {2, 5, 6} → False := by
  intro a194 a47 a76
  have hc := h.complementary {0, 4, 8, 9} {1, 3, 7} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a47 a76

theorem c12051 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a194 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {1, 3} {2, 5, 6} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c12053 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 7} → False := by
  intro a194 a37 a45 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {1, 3} {2, 5, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12055 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a194 a37 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {1, 3} {2, 6, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12163 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {4, 8, 9} → False := by
  intro a195 a37 a110
  have hc := h.complementary {0, 5, 6, 7} {1, 2, 3} a195 (by decide) (by decide)
  have he : ( {0, 5, 6, 7} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a110

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

theorem c12335 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a196 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 3} {2, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12381 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 7} → T {2, 3, 7} → T {2, 7, 9} → False := by
  intro a196 a41 a68 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 7} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) a84)

theorem c12443 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 2, 3} → T {4, 7, 8} → False := by
  intro a197 a37 a108
  have hc := h.complementary {0, 5, 6, 9} {1, 2, 3} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a108

theorem c12459 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 4, 8} → T {2, 3, 7} → False := by
  intro a197 a53 a68
  have hc := h.complementary {0, 5, 6, 9} {1, 4, 8} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 4, 8} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a53 a68

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

theorem c12615 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a198 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 3} {2, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c13315 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 7} → False := by
  intro a203 a37 a45 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {1, 3} {2, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

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

theorem c13455 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a204 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 7, 8, 9} {1, 3} {2, 5, 6} a204 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c13562 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 6} → ¬ T {7, 8, 9} → False := by
  intro a205 n27 n120
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 6} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n120)

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

theorem c14001 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 8, 9} → T {4, 5, 6} → False := by
  intro a208 a36 a101
  have hc := h.complementary {1, 2, 3, 7} {0, 8, 9} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a36 a101

theorem c14130 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 5, 6} → ¬ T {4, 7, 9} → False := by
  intro a209 n27 n109
  have hc := h.complementary {1, 2, 3, 8} {0, 5, 6} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n109)

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

theorem c14828 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → ¬ T {0, 3, 9} → ¬ T {5, 6, 7} → False := by
  intro a214 n21 n111
  have hc := h.complementary {1, 2, 4, 8} {0, 3, 9} a214 (by decide) (by decide)
  have he : ( {1, 2, 4, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n111)

theorem c14937 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → T {3, 5, 9} → T {5, 6, 9} → T {5, 7, 9} → False := by
  intro a214 a94 a113 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 8} {5, 9} {3, 6, 7} a214 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c15104 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {0, 3, 7} → ¬ T {4, 8, 9} → False := by
  intro a216 n19 n110
  have hc := h.complementary {1, 2, 5, 6} {0, 3, 7} a216 (by decide) (by decide)
  have he : ( {1, 2, 5, 6} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n110)

theorem c15119 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 7, 9} → T {3, 4, 8} → False := by
  intro a216 a35 a89
  have hc := h.complementary {1, 2, 5, 6} {0, 7, 9} a216 (by decide) (by decide)
  have he : ( {1, 2, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a89

theorem c15187 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 3, 9} → T {3, 4, 9} → T {3, 7, 9} → False := by
  intro a216 a21 a90 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {3, 9} {0, 4, 7} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

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

theorem c15537 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 6, 7} → T {3, 4, 8} → False := by
  intro a219 a31 a89
  have hc := h.complementary {1, 2, 5, 9} {0, 6, 7} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a31 a89

theorem c15766 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 4, 8} → ¬ T {4, 5, 8} → ¬ T {4, 8, 9} → False := by
  intro a220 n25 n103 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 7} {4, 8} {0, 5, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

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

theorem c17205 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 7} → T {4, 8, 9} → False := by
  intro a231 a13 a110
  have hc := h.complementary {1, 3, 5, 6} {0, 2, 7} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a110

theorem c17219 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 7, 9} → T {2, 4, 8} → False := by
  intro a231 a35 a74
  have hc := h.complementary {1, 3, 5, 6} {0, 7, 9} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a74

theorem c17240 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {0, 2, 7} → ¬ T {0, 4, 7} → ¬ T {0, 7, 9} → False := by
  intro a231 n13 n24 n35
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 6} {0, 7} {2, 4, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) ht)
  · exact n24 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) ht)
  · exact n35 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 7} = {0, 7, 9} by decide)) ht)

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

theorem c17625 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 6} → T {4, 7, 8} → False := by
  intro a234 a12 a108
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 6} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a108

theorem c17626 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 7} → ¬ T {4, 6, 8} → False := by
  intro a234 n13 n106
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n106)

theorem c17627 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 7} → T {4, 6, 8} → False := by
  intro a234 a13 a106
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a13 a106

theorem c17628 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 8} → ¬ T {4, 6, 7} → False := by
  intro a234 n14 n105
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 8} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n105)

theorem c17634 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 4, 8} → ¬ T {2, 6, 7} → False := by
  intro a234 n25 n80
  have hc := h.complementary {1, 3, 5, 9} {0, 4, 8} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n80)

theorem c17636 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 6, 7} → ¬ T {2, 4, 8} → False := by
  intro a234 n31 n74
  have hc := h.complementary {1, 3, 5, 9} {0, 6, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n74)

theorem c17645 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 4} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a234 a10 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {0, 2} {4, 6, 8} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c17730 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 4, 8} → ¬ T {2, 4, 8} → ¬ T {4, 6, 8} → False := by
  intro a234 n25 n74 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 9} {4, 8} {0, 2, 6} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)

theorem c17732 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 4, 8} → ¬ T {2, 4, 8} → ¬ T {4, 7, 8} → False := by
  intro a234 n25 n74 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 9} {4, 8} {0, 2, 7} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)

theorem c17735 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 4, 8} → T {4, 6, 8} → T {4, 7, 8} → False := by
  intro a234 a25 a106 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {4, 8} {0, 6, 7} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

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

theorem c18044 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 5} → ¬ T {4, 7, 8} → False := by
  intro a237 n11 n108
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 5} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n108)

theorem c18045 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 5} → T {4, 7, 8} → False := by
  intro a237 a11 a108
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 5} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a108

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

theorem c18054 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 4, 8} → ¬ T {2, 5, 7} → False := by
  intro a237 n25 n77
  have hc := h.complementary {1, 3, 6, 9} {0, 4, 8} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 5, 7} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n77)

theorem c18055 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 4, 8} → T {2, 5, 7} → False := by
  intro a237 a25 a77
  have hc := h.complementary {1, 3, 6, 9} {0, 4, 8} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a25 a77

theorem c18056 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 5, 7} → ¬ T {2, 4, 8} → False := by
  intro a237 n28 n74
  have hc := h.complementary {1, 3, 6, 9} {0, 5, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n74)

theorem c18057 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 5, 7} → T {2, 4, 8} → False := by
  intro a237 a28 a74
  have hc := h.complementary {1, 3, 6, 9} {0, 5, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a28 a74

theorem c18153 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 4, 8} → T {2, 4, 8} → T {4, 7, 8} → False := by
  intro a237 a25 a74 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 9} {4, 8} {0, 2, 7} a237 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c18158 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 5, 7} → ¬ T {2, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a237 n28 n77 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 9} {5, 7} {0, 2, 4} a237 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n28 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)

theorem c18324 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 8} → False := by
  intro a239 n11 n106
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 5} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n106)

theorem c18325 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 5} → T {4, 6, 8} → False := by
  intro a239 a11 a106
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 5} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a106

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

theorem c18328 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 8} → ¬ T {4, 5, 6} → False := by
  intro a239 n14 n101
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 8} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n101)

theorem c18329 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 8} → T {4, 5, 6} → False := by
  intro a239 a14 a101
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 8} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a14 a101

theorem c18336 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 6} → ¬ T {2, 4, 8} → False := by
  intro a239 n27 n74
  have hc := h.complementary {1, 3, 7, 9} {0, 5, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n74)

theorem c18337 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 5, 6} → T {2, 4, 8} → False := by
  intro a239 a27 a74
  have hc := h.complementary {1, 3, 7, 9} {0, 5, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a74

theorem c18430 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 4, 8} → ¬ T {2, 4, 8} → ¬ T {4, 5, 8} → False := by
  intro a239 n25 n74 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {4, 8} {0, 2, 5} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)

theorem c18438 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → False := by
  intro a239 n27 n76 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 6} {0, 2, 4} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)

theorem c18440 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a239 n27 n76 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 6} {0, 2, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

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

theorem c18715 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 3, 9} → T {3, 7, 9} → T {3, 8, 9} → False := by
  intro a241 a21 a99 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {3, 9} {0, 7, 8} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

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

theorem c18851 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 3, 9} → T {2, 3, 9} → T {3, 6, 9} → False := by
  intro a242 a21 a70 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {3, 9} {0, 2, 6} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c18889 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 9} → T {3, 6, 7} → False := by
  intro a243 a15 a95
  have hc := h.complementary {1, 4, 5, 8} {0, 2, 9} a243 (by decide) (by decide)
  have he : ( {1, 4, 5, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a95

theorem c18894 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 3, 9} → ¬ T {2, 6, 7} → False := by
  intro a243 n21 n80
  have hc := h.complementary {1, 4, 5, 8} {0, 3, 9} a243 (by decide) (by decide)
  have he : ( {1, 4, 5, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n80)

theorem c18896 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {2, 3, 9} → False := by
  intro a243 n31 n70
  have hc := h.complementary {1, 4, 5, 8} {0, 6, 7} a243 (by decide) (by decide)
  have he : ( {1, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n70)

theorem c18913 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a243 a9 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 3} {2, 6, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c18915 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a243 a9 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 3} {2, 7, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c18943 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {2, 3, 6} → T {2, 3, 7} → False := by
  intro a243 a9 a67 a68
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {2, 3} {0, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)

theorem c18954 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 6} → ¬ T {2, 6, 7} → ¬ T {2, 6, 9} → False := by
  intro a243 n12 n80 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 6} {0, 7, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) ht)

theorem c18958 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 6, 7} → False := by
  intro a243 n13 n68 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 7} {0, 3, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c18962 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 7} → ¬ T {2, 6, 7} → ¬ T {2, 7, 9} → False := by
  intro a243 n13 n80 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 7} {0, 6, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c18966 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 9} → ¬ T {2, 3, 9} → ¬ T {2, 6, 9} → False := by
  intro a243 n15 n70 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 9} {0, 3, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c18991 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 3, 9} → T {2, 3, 9} → T {3, 6, 9} → False := by
  intro a243 a21 a70 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {3, 9} {0, 2, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c18995 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 3, 9} → T {3, 6, 9} → T {3, 7, 9} → False := by
  intro a243 a21 a97 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {3, 9} {0, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c18997 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {2, 3, 9} → T {3, 6, 9} → T {3, 7, 9} → False := by
  intro a243 a70 a97 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {3, 9} {2, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c19000 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {2, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n31 n80 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {0, 2, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c19004 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {2, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n80 n95 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {2, 3, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c19018 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 7, 9} → ¬ T {3, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a243 n35 n99 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {7, 9} {0, 3, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n35 (Eq.mp (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)

theorem c19043 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a244 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {0, 2} {3, 6, 7} a244 (by decide) (by decide) (by decide) (by decide)
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

theorem c19316 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {2, 3, 9} → False := by
  intro a246 n28 n70
  have hc := h.complementary {1, 4, 6, 8} {0, 5, 7} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n70)

theorem c19887 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a250 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {0, 2} {3, 6, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19919 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 7} → T {0, 5, 7} → T {0, 6, 7} → False := by
  intro a250 a13 a28 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {0, 7} {2, 5, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

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

theorem c19943 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a250 a12 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {2, 6} {0, 5, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c19951 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 7} → T {2, 5, 7} → T {2, 6, 7} → False := by
  intro a250 a13 a77 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {2, 7} {0, 5, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c19980 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a250 n27 n76 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 8, 9} {5, 6} {0, 2, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c19982 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {3, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a250 n27 n91 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 8, 9} {5, 6} {0, 3, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c20003 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 3} → T {4, 8, 9} → False := by
  intro a251 a9 a110
  have hc := h.complementary {1, 5, 6, 7} {0, 2, 3} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a110

theorem c20255 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 9} → T {3, 4, 9} → T {3, 7, 9} → False := by
  intro a252 a21 a90 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {3, 9} {0, 4, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

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

theorem c21269 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {0, 2, 6} → T {3, 4, 5} → False := by
  intro a260 a12 a86
  have hc := h.complementary {1, 7, 8, 9} {0, 2, 6} a260 (by decide) (by decide)
  have he : ( {1, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a12 a86

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

theorem c21828 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 9} → ¬ T {5, 6, 7} → False := by
  intro a264 n8 n111
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 9} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n111)

theorem c21937 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → T {1, 5, 9} → T {5, 6, 9} → T {5, 7, 9} → False := by
  intro a264 a58 a113 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 8} {5, 9} {1, 6, 7} a264 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

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

theorem c22104 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 1, 7} → ¬ T {4, 8, 9} → False := by
  intro a266 n6 n110
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n110)

theorem c22193 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {1, 4, 9} → T {1, 7, 9} → T {1, 8, 9} → False := by
  intro a266 a54 a63 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {1, 9} {4, 7, 8} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

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

theorem c22766 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 4, 8} → ¬ T {4, 5, 8} → ¬ T {4, 8, 9} → False := by
  intro a270 n25 n103 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {4, 8} {0, 5, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

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

theorem c23555 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a276 a8 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {0, 9} {1, 3, 7} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c23565 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a276 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {1, 3} {0, 7, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23705 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a277 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {1, 3} {0, 6, 9} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23845 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a278 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {1, 3} {0, 6, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23847 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a278 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {1, 3} {0, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23983 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a279 a2 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {1, 3} {0, 6, 7} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c24039 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a279 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {6, 7} {0, 1, 3} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c24125 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a280 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 3} {0, 5, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
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

theorem c24265 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a281 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 3} {0, 5, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24267 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a281 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 3} {0, 7, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24545 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a283 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {1, 3} {0, 5, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24547 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a283 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {1, 3} {0, 6, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
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

theorem c24827 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a285 a2 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {1, 3} {0, 6, 7} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c25097 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a287 a8 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {0, 9} {1, 3, 7} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c25107 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a287 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {1, 3} {0, 7, 9} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
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

theorem c25735 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a291 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {6, 7} {0, 1, 3} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c25807 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a292 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 7, 8} {1, 3} {0, 5, 9} a292 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
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

theorem c26087 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 7} → False := by
  intro a294 a2 a45 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {1, 3} {0, 5, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c26227 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a295 a2 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 7, 8, 9} {1, 3} {0, 5, 6} a295 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c26391 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 9} → T {1, 7, 9} → T {1, 8, 9} → False := by
  intro a296 a8 a63 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {1, 9} {0, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c26585 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 6} → T {2, 7, 9} → False := by
  intro a298 a5 a84
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 6} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a5 a84

theorem c26587 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 7} → T {2, 6, 9} → False := by
  intro a298 a6 a82
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 7} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a82

theorem c26589 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 9} → T {2, 6, 7} → False := by
  intro a298 a8 a80
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 9} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a8 a80

theorem c26597 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 6, 7} → T {1, 2, 9} → False := by
  intro a298 a31 a43
  have hc := h.complementary {3, 4, 5, 8} {0, 6, 7} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a31 a43

theorem c26605 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {0, 1, 6} → T {0, 1, 9} → False := by
  intro a298 a1 a5 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {0, 1} {2, 6, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c26671 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 9} → T {1, 6, 9} → T {1, 7, 9} → False := by
  intro a298 a8 a61 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 9} {0, 6, 7} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

theorem c26682 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {0, 2, 7} → ¬ T {1, 2, 7} → ¬ T {2, 6, 7} → False := by
  intro a298 n13 n41 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 8} {2, 7} {0, 1, 6} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c26704 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {1, 6, 7} → ¬ T {2, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a298 n59 n80 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 8} {6, 7} {1, 2, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

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

theorem c26751 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a299 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {0, 2} {1, 6, 7} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c27025 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {0, 1, 5} → T {0, 1, 9} → False := by
  intro a301 a1 a4 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {0, 1} {2, 5, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

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

theorem c27122 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {2, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a301 n28 n77 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 8} {5, 7} {0, 2, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n28 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

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

theorem c27595 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a305 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {0, 2} {1, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c27621 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 7} → T {0, 5, 7} → T {0, 6, 7} → False := by
  intro a305 a13 a28 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {0, 7} {2, 5, 6} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c27667 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a305 a12 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {2, 6} {0, 5, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c27675 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 7} → T {2, 5, 7} → T {2, 6, 7} → False := by
  intro a305 a13 a77 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {2, 7} {0, 5, 6} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c27680 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {1, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a305 n27 n55 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {5, 6} {0, 1, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c27682 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a305 n27 n76 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {5, 6} {0, 2, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

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

theorem c27931 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 9} → T {1, 4, 9} → T {1, 7, 9} → False := by
  intro a307 a8 a54 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 9} {0, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

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

theorem c28855 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a314 a1 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {0, 2} {1, 5, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c28975 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 6} → T {1, 4, 5} → False := by
  intro a315 a12 a50
  have hc := h.complementary {3, 7, 8, 9} {0, 2, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a12 a50

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

theorem c31274 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → T {6, 8, 9} → False := by
  classical
  intro n203 n294 n314 a119
  have u0_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c1776 h hv n203 n294 n314 u2_324 u1_328 u0_330
  exact c1772 h a119 n203 u3_259 n294 n314 u2_324 u1_328 u0_330

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

theorem c31392 (h : TenSystem T Q) :
    ¬ Q {1, 3, 6, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → T {1, 3, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 3, 7, 9} → False := by
  classical
  intro n237 n210 n230 n234 a49 n240 n239
  have u0_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c722 h a49 hv n210 n230 n234 n237 n239 n240
  exact c724 h u0_133 n210 n230 n234 n237 n239 n240

private theorem c31396 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {7, 8, 9} → T {5, 6, 9} → Q {1, 3, 7, 9} → Q {1, 3, 5, 9} → False := by
  classical
  intro a120 a113 a239 a234
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u0_121 hv a113
  have u2_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u1_108
  have u3_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c18327 h a239 u2_12 hv
  have u4_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 u3_103 hv
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1911 h u0_121 hv a113 u4_118
  have u6_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1814 h u0_121 u5_107 hv
  have u7_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c1803 h u0_121 hv a120
  have u8_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1925 h u0_121 u6_114 hv a120
  have u9_14 : T {0, 2, 8} := by
    by_contra hv
    exact c18328 h a239 hv u7_101
  have u10_10 : T {0, 2, 4} := by
    by_contra hv
    exact c17622 h a234 hv u8_117
  exact c17645 h a234 u10_10 u2_12 u9_14

private theorem c31397 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → Q {1, 3, 7, 9} → Q {1, 3, 5, 9} → False := by
  classical
  intro a113 a239 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u0_121 hv a113
  have u2_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u1_108
  have u3_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c18327 h a239 u2_12 hv
  have u4_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1846 h u0_121 u3_103 hv u1_108
  have u5_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31396 h h0 hv a113 a239 a234
  have u6_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv u5_120
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1831 h u0_121 u6_101 hv u4_106
  have u8_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c18329 h a239 hv u6_101
  exact c17628 h a234 u8_14 u7_105

theorem c31398 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → Q {1, 3, 5, 9} → False := by
  classical
  intro a239 a234
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
  have u4_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u5_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u6_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13315 h hv u0_37 u4_45 u5_47
  have u7_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26087 h hv u1_2 u4_45 u5_47
  have u8_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31397 h h0 hv a239 a234
  have u9_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1816 h u2_121 hv u8_113
  have u10_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17625 h a234 hv u9_108
  have u11_103 : T {4, 5, 8} := by
    by_contra hv
    exact c18326 h a239 u10_12 hv
  have u12_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 u11_103 hv
  have u13_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1847 h u2_121 u11_103 hv u9_108
  have u14_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1916 h u2_121 u8_113 u12_118 hv
  have u15_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18324 h a239 hv u13_106
  have u16_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17626 h a234 hv u13_106
  have u17_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u6_203 u7_294 hv u14_119
  exact c28855 h u17_314 u3_1 u15_11 u16_13

private theorem c31399 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → ¬ T {4, 6, 8} → T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro a103 n106 a108 a133 n192 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_58 : T {1, 5, 9} := by
    by_contra hv
    exact c862 h a234 hv
  have u2_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1400 h a234 hv
  have u3_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u0_121 n106 hv
  have u4_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7093 h hv u1_58 u2_94 u3_115
  have u5_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h a133 hv n106
  have u6_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1851 h u0_121 a103 a108 hv
  have u7_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3569 h a133 hv a103 a108
  have u8_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c1638 h hv u6_110
  have u9_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u0_121 u6_110 hv
  have u10_25 : T {0, 4, 8} := by
    by_contra hv
    exact c17730 h a234 hv u7_74 n106
  have u11_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4147 h hv u5_77 u9_111 u3_115
  have u12_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9189 h hv u5_77 u9_111 u3_115
  have u13_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c370 h hv u11_137 u4_158 u12_173 n190 n192 u8_194
  exact c362 h u10_25 u11_137 u4_158 u12_173 u13_187 n190 n192 u8_194

private theorem c31400 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro n106 a108 a133 n192 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u5_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17626 h a234 hv n106
  have u6_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h a133 hv n106
  have u7_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31399 h h0 hv n106 a108 a133 n192 n190 a234
  have u8_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u0_121 u7_103 n106 hv
  have u9_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv u7_103
  have u10_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12031 h hv u4_45 u9_80
  have u11_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19951 h hv u5_13 u6_77 u9_80
  have u12_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27675 h hv u5_13 u6_77 u9_80
  have u13_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c1643 h hv u10_194 u11_250 u12_305 u3_321 u2_324 u1_325
  exact c1637 h u8_110 u10_194 u11_250 u13_285 u12_305 u3_321 u2_324 u1_325

theorem c31401 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro a108 a133 n192 n292 n280 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17625 h a234 hv a108
  have u2_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c3491 h a133 hv a108
  have u3_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c176 h hv u1_12
  have u4_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1136 h hv u2_76
  have u5_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31400 h h0 hv a108 a133 n192 n190 a234
  have u6_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1847 h u0_121 hv u5_106 a108
  have u7_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1853 h u0_121 u5_106 a108 hv
  have u8_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c17735 h a234 hv u5_106 a108
  have u9_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv u6_103
  have u10_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15766 h hv u8_25 u6_103 u7_110
  have u11_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22766 h hv u8_25 u6_103 u7_110
  have u12_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c1201 h hv u3_164 u10_220 u11_270 n280 u4_286 n292
  exact c1187 h u9_80 u3_164 u10_220 u11_270 n280 u4_286 n292 u12_293

theorem c31402 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 8, 9} → T {4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {0, 4, 8, 9} → False := by
  classical
  intro n250 a110 n305 n194
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_285 : Q {2, 4, 8, 9} := by
    by_contra hv
    exact c1637 h a110 n194 n250 hv n305 u0_321 u1_324 u2_325
  exact c1643 h u3_285 n194 n250 n305 u0_321 u1_324 u2_325

private theorem c31403 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → T {0, 2, 6} → ¬ T {4, 7, 8} → Q {0, 1, 3, 9} → T {1, 3, 5} → False := by
  classical
  intro n103 a12 n108 a133 a45
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_76 : T {2, 5, 6} := by
    by_contra hv
    exact c3490 h a133 hv n108
  have u2_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1850 h u0_121 n103 n108 hv
  have u3_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv n103
  have u4_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27667 h hv a12 u1_76 u3_80
  have u5_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19943 h hv a12 u1_76 u3_80
  have u6_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12031 h hv a45 u3_80
  exact c31402 h h0 u5_250 u2_110 u4_305 u6_194

theorem c31404 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → ¬ T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro a106 n108 a133 n192 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u2_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv n108
  have u3_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31403 h h0 hv u2_12 n108 a133 u1_45
  have u4_58 : T {1, 5, 9} := by
    by_contra hv
    exact c862 h a234 hv
  have u5_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1400 h a234 hv
  have u6_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u0_121 n108 hv
  have u7_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7091 h hv u4_58 u5_94 u6_113
  have u8_76 : T {2, 5, 6} := by
    by_contra hv
    exact c3490 h a133 hv n108
  have u9_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1849 h u0_121 u3_103 a106 hv
  have u10_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3567 h a133 hv u3_103 a106
  have u11_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c1638 h hv u9_110
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u0_121 u9_110 hv
  have u13_25 : T {0, 4, 8} := by
    by_contra hv
    exact c17732 h a234 hv u10_74 n108
  have u14_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4139 h hv u8_76 u12_111 u6_113
  have u15_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9181 h hv u8_76 u12_111 u6_113
  have u16_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c370 h hv u14_137 u7_158 u15_173 n190 n192 u11_194
  exact c362 h u13_25 u14_137 u7_158 u15_173 u16_187 n190 n192 u11_194

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases088
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31405 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a234 n237 n230 n240 a49 n210
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
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u6_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u7_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u8_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u9_58 : T {1, 5, 9} := by
    by_contra hv
    exact c862 h a234 hv
  have u10_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1400 h a234 hv
  have u11_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11493 h hv u1_37 u8_45 a49
  have u12_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24125 h hv u0_2 u8_45 a49
  have u13_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24265 h hv u0_2 u8_45 a49
  have u14_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25807 h hv u0_2 u8_45 a49
  have u15_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24545 h hv u0_2 u8_45 a49
  have u16_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11773 h hv u1_37 u8_45 a49
  have u17_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31398 h h0 hv a234
  have u18_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c730 h a234 hv n210 n230 n237 u17_239 n240
  have u19_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31401 h h0 hv u18_133 u16_192 u14_292 u12_280 u11_190 a234
  have u20_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u2_121 u19_108 hv
  have u21_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u19_108
  have u22_76 : T {2, 5, 6} := by
    by_contra hv
    exact c3490 h u18_133 hv u19_108
  have u23_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7091 h hv u9_58 u10_94 u20_113
  have u24_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31404 h h0 hv u19_108 u18_133 u16_192 u11_190 a234
  have u25_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u2_121 u24_106 hv
  have u26_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1852 h u2_121 u24_106 u19_108 hv
  have u27_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17626 h a234 hv u24_106
  have u28_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h u18_133 hv u24_106
  have u29_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21937 h hv u9_58 u20_113 u25_115
  have u30_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14937 h hv u10_94 u20_113 u25_115
  have u31_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27595 h hv u3_1 u21_12 u27_13
  have u32_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19887 h hv u4_9 u21_12 u27_13
  have u33_71 : ¬ T {2, 4, 5} := by
    intro hv
    exact c3511 h u18_133 hv u22_76 u28_77
  have u34_194 : Q {0, 4, 8, 9} := by
    by_contra hv
    exact c31402 h h0 u32_250 u26_110 u31_305 hv
  have u35_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c1063 h hv u33_71
  have u36_285 : Q {2, 4, 8, 9} := by
    by_contra hv
    exact c1639 h u34_194 u32_250 hv u31_305 u7_321 u6_324 u5_325
  exact c1111 h u36_285 u23_158 u30_214 u29_264 u35_278 u13_281 u15_283

private theorem c31406 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 8, 9} → ¬ T {0, 5, 6} → Q {1, 3, 7, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a194 n27 a239 n210
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u3_36 : T {0, 8, 9} := by
    by_contra hv
    exact c534 h a194 hv
  have u4_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c12053 h a194 u0_37 hv u2_47
  have u5_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c12055 h a194 u0_37 hv u2_47
  have u6_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c12035 h a194 u2_47 hv
  have u7_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c665 h hv u4_45
  have u8_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c680 h hv u5_46
  have u9_101 : T {4, 5, 6} := by
    by_contra hv
    exact c18438 h a239 n27 u6_76 hv
  have u10_112 : T {5, 6, 8} := by
    by_contra hv
    exact c18440 h a239 n27 u6_76 hv
  have u11_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c1803 h u1_121 u9_101 hv
  have u12_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14001 h hv u3_36 u9_101
  have u13_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u1_121 hv u10_112
  have u14_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13562 h hv n27 u11_120
  have u15_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c544 h u1_121 u14_205 u7_206 u8_207 u12_208 hv n210
  exact c14130 h u15_209 n27 u13_109

private theorem c31407 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 5, 6} → ¬ Q {0, 4, 8, 9} → ¬ T {0, 5, 6} → T {4, 8, 9} → False := by
  classical
  intro n76 n194 n27 a110
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 a110 hv
  have u2_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27682 h hv n27 n76 u1_111
  have u3_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19980 h hv n27 n76 u1_111
  exact c31402 h h0 u3_250 a110 u2_305 n194

private theorem c31408 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ Q {1, 3, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ T {0, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ T {5, 6, 7} → T {0, 3, 9} → T {3, 7, 9} → False := by
  classical
  intro a305 n231 n139 n27 n251 n111 a21 a99
  have u0_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1350 h a305 hv
  have u1_100 : T {3, 8, 9} := by
    by_contra hv
    exact c1494 h a305 hv
  have u2_55 : T {1, 5, 6} := by
    by_contra hv
    exact c27680 h a305 n27 hv n111
  have u3_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15187 h hv a21 u0_90 a99
  have u4_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20255 h hv a21 u0_90 a99
  have u5_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18715 h hv a21 a99 u1_100
  have u6_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c826 h hv n139 u3_216 n231 u5_241 n251 u4_252
  exact c812 h u2_55 n139 u3_216 n231 u5_241 n251 u4_252 u6_253

private theorem c31409 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 5, 6} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ T {0, 5, 6} → T {4, 8, 9} → T {0, 3, 9} → T {0, 1, 9} → T {3, 7, 9} → T {1, 7, 9} → False := by
  classical
  intro n231 n194 n139 n175 n27 a110 a21 a8 a99 a63
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20003 h hv u2_9 a110
  have u4_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c27703 h hv u1_1 a110
  have u5_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 a110 hv
  have u6_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c31408 h hv n231 n139 n27 u3_251 u5_111 a21 a99
  have u7_250 : Q {1, 4, 8, 9} := by
    by_contra hv
    exact c31402 h h0 hv a110 u6_305 n194
  have u8_54 : T {1, 4, 9} := by
    by_contra hv
    exact c810 h u7_250 hv
  have u9_64 : T {1, 8, 9} := by
    by_contra hv
    exact c954 h u7_250 hv
  have u10_91 : T {3, 5, 6} := by
    by_contra hv
    exact c19982 h u7_250 n27 hv u5_111
  have u11_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22193 h hv u8_54 a63 u9_64
  have u12_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27931 h hv a8 u8_54 a63
  have u13_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26391 h hv a8 a63 u9_64
  have u14_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c1366 h hv n175 n231 u11_266 u13_296 u4_306 u12_307
  exact c1352 h u10_91 n175 n231 u11_266 u13_296 u4_306 u12_307 u14_308

theorem c31410 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 8, 9} → Q {0, 1, 3, 9} → Q {1, 3, 7, 9} → T {1, 3, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a110 a133 a239 a49 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h a133 hv
  have u3_8 : T {0, 1, 9} := by
    by_contra hv
    exact c110 h a133 hv
  have u4_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1475 h a239 hv
  have u5_63 : T {1, 7, 9} := by
    by_contra hv
    exact c937 h a239 hv
  have u6_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u0_121 a110 hv
  have u7_74 : T {2, 4, 8} := by
    by_contra hv
    exact c3488 h a133 hv u6_111
  have u8_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c18337 h a239 hv u7_74
  have u9_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9379 h hv u5_63 u7_74
  have u10_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4333 h hv u7_74 u4_99
  have u11_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c31406 h h0 hv u8_27 a239 n210
  have u12_76 : T {2, 5, 6} := by
    by_contra hv
    exact c31407 h h0 hv u11_194 u8_27 a110
  have u13_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11755 h hv a49 u12_76
  have u14_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c3491 h a133 u12_76 hv
  have u15_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u0_121 u14_108 hv
  have u16_231 : Q {1, 3, 5, 6} := by
    by_contra hv
    exact c31409 h h0 hv u11_194 u10_139 u9_175 u8_27 a110 u2_21 u3_8 u4_99 u5_63
  have u17_45 : T {1, 3, 5} := by
    by_contra hv
    exact c669 h u16_231 hv
  have u18_46 : T {1, 3, 6} := by
    by_contra hv
    exact c684 h u16_231 hv
  have u19_55 : T {1, 5, 6} := by
    by_contra hv
    exact c817 h u16_231 hv
  have u20_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1355 h u16_231 hv
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c17205 h u16_231 hv a110
  have u22_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c17219 h u16_231 hv u7_74
  have u23_24 : T {0, 4, 7} := by
    by_contra hv
    exact c17240 h u16_231 u21_13 hv u22_35
  have u24_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11353 h hv u1_37 u17_45 a49
  have u25_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u1_37 u18_46 a49
  have u26_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11911 h hv u1_37 u17_45 u18_46
  have u27_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6865 h hv u17_45 u18_46 a49
  have u28_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9037 h hv u19_55 u12_76 u15_113
  have u29_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c3997 h hv u12_76 u20_91 u15_113
  exact c347 h u23_24 u29_136 u27_157 u28_172 u25_186 u24_189 u13_192 u26_193

theorem c31412 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 1, 5, 6} → T {0, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 8} → Q {0, 1, 3, 9} → False := by
  classical
  intro n76 n175 n139 a27 n185 n196 a133
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c1128 h hv n76
  have u2_108 : T {4, 7, 8} := by
    by_contra hv
    exact c3490 h a133 n76 hv
  have u3_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12443 h hv u0_37 u2_108
  have u4_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c402 h hv n139 u1_160 n175 n185 n196 u3_197
  exact c392 h a27 n139 u1_160 n175 n185 u4_195 n196 u3_197

theorem c31419 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 5, 6} → ¬ T {4, 8, 9} → T {0, 1, 9} → ¬ Q {2, 4, 6, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → False := by
  classical
  intro a139 n110 a8 n281 n187 n278 n190
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u7_4 : T {0, 1, 5} := by
    by_contra hv
    exact c54 h a139 hv
  have u8_5 : T {0, 1, 6} := by
    by_contra hv
    exact c69 h a139 hv
  have u9_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27025 h hv u0_1 u7_4 a8
  have u10_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c26605 h hv u0_1 u8_5 a8
  have u11_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c1581 h hv n190 n281 u9_301 u5_317 u2_322 u1_324
  have u12_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c1536 h hv n187 n278 u10_298 u5_317 u4_319 u3_321
  have u13_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31307 h h0 u11_246 hv u9_301 n190
  have u14_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1532 h hv n187 u12_243 n278 u10_298 u5_317 u4_319 u3_321
  exact c1848 h u6_121 u14_103 u13_106 n110

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

private theorem c31420 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ Q {0, 2, 4, 8} → T {5, 6, 7} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → Q {0, 1, 3, 9} → Q {1, 3, 7, 9} → False := by
  classical
  intro n103 n158 a111 n194 n187 n190 a133 a239
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3489 h a133 hv a111
  have u2_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 n103 hv
  have u3_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv n103
  have u4_25 : T {0, 4, 8} := by
    by_contra hv
    exact c18430 h a239 hv u1_74 n103
  have u5_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9205 h hv u3_80 a111 u2_118
  have u6_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4163 h hv u3_80 a111 u2_118
  have u7_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c374 h hv u6_137 n158 u5_173 n187 n190 n194
  exact c362 h u4_25 u6_137 n158 u5_173 n187 n190 u7_192 n194

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

private theorem c31422 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 2, 3, 9} → T {1, 3, 9} → ¬ Q {1, 3, 8, 9} → False := by
  classical
  intro n234 n237 n230 n210 a49 n240
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u1_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u6_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u7_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c31392 h n237 n210 n230 n234 a49 n240 hv
  have u8_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u7_239 hv
  have u9_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c734 h u7_239 hv n210 n230 n234 n237 n240
  have u10_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11495 h hv u6_37 u8_47 a49
  have u11_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12335 h hv u6_37 u8_47 a49
  have u12_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23847 h hv u5_2 u8_47 a49
  have u13_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11075 h hv u6_37 u8_47 a49
  have u14_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24267 h hv u5_2 u8_47 a49
  have u15_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25107 h hv u5_2 u8_47 a49
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10793 h hv u6_37 u8_47 a49
  have u17_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23565 h hv u5_2 u8_47 a49
  have u18_8 : T {0, 1, 9} := by
    by_contra hv
    exact c110 h u9_133 hv
  have u19_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h u9_133 hv
  have u20_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31410 h h0 hv u9_133 u7_239 a49 n210
  have u21_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c1638 h hv u20_110
  have u22_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u4_121 u20_110 hv
  have u23_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c6989 h hv a49 u22_111
  have u24_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3489 h u9_133 hv u22_111
  have u25_27 : T {0, 5, 6} := by
    by_contra hv
    exact c18336 h u7_239 hv u24_74
  have u26_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c31419 h h0 hv u20_110 u18_8 u14_281 u13_187 u12_278 u10_190
  have u27_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31420 h h0 hv u23_158 u22_111 u21_194 u13_187 u10_190 u9_133 u7_239
  have u28_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18327 h u7_239 hv u27_103
  have u29_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c3497 h u9_133 hv u27_103
  have u30_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c174 h hv u28_12
  have u31_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1196 h hv u29_80
  have u32_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv u27_103 u13_187 u12_278
  have u33_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c18915 h u32_243 u0_9 hv u19_21
  have u34_82 : T {2, 6, 9} := by
    by_contra hv
    exact c18954 h u32_243 u28_12 u29_80 hv
  have u35_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u32_243 u13_187 u12_278 hv u1_317 u2_319 u3_321
  have u36_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c18913 h u32_243 u0_9 hv u19_21
  have u37_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15104 h hv u33_19 u20_110
  have u38_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c26587 h u35_298 hv u34_82
  have u39_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c264 h hv u36_18
  have u40_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22104 h hv u38_6 u20_110
  have u41_76 : T {2, 5, 6} := by
    by_contra hv
    exact c31412 h h0 hv u39_175 u26_139 u25_27 u16_185 u11_196 u9_133
  have u42_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c1141 h hv u30_160 u37_216 u40_266 u17_276 u31_286 u15_287
  exact c1127 h u41_76 u30_160 u37_216 u40_266 u17_276 u31_286 u15_287 u42_288

theorem c31423 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 8, 9} → T {1, 3, 9} → False := by
  classical
  intro n237 n230 n210 n240 a49
  have u0_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c31405 h h0 hv n237 n230 n240 a49 n210
  exact c31422 h h0 u0_234 n237 n230 n210 a49 n240

private theorem c31425 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → Q {1, 3, 7, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n103 a239 a237
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u3_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u4_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u5_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u6_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u7_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u8_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u9_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u10_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12055 h hv u1_37 u8_46 u9_47
  have u11_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c11211 h hv u1_37 u8_46 u9_47
  have u12_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c23983 h hv u0_2 u8_46 u9_47
  have u13_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u7_121 n103 hv
  have u14_12 : T {0, 2, 6} := by
    by_contra hv
    exact c18326 h a239 hv n103
  have u15_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv n103
  have u16_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27595 h hv u2_1 u14_12 u15_13
  have u17_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19887 h hv u3_9 u14_12 u15_13
  have u18_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26751 h hv u2_1 u14_12 u15_13
  have u19_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19043 h hv u3_9 u14_12 u15_13
  have u20_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31402 h h0 u17_250 hv u16_305 u10_194
  have u21_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1547 h hv u11_188 u19_244 u12_279 u18_299 u6_318 u5_320 u4_321
  have u22_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u7_121 u20_110 hv
  have u23_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1808 h u7_121 u21_104 hv
  exact c1901 h u7_121 u22_111 u23_117 u13_118

private theorem c31426 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 5} → Q {1, 3, 7, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n11 a239 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31425 h h0 hv a239 a237
  have u2_108 : T {4, 7, 8} := by
    by_contra hv
    exact c18044 h a237 n11 hv
  have u3_106 : T {4, 6, 8} := by
    by_contra hv
    exact c18324 h a239 n11 hv
  exact c1847 h u0_121 u1_103 u3_106 u2_108

theorem c31427 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → Q {1, 3, 6, 9} → T {1, 3, 9} → False := by
  classical
  intro a239 a237 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u6_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u7_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12615 h hv u5_37 u6_46 a49
  have u8_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c24547 h hv u0_2 u6_46 a49
  have u9_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23845 h hv u0_2 u6_46 a49
  have u10_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11073 h hv u5_37 u6_46 a49
  have u11_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u5_37 u6_46 a49
  have u12_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u13_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u14_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1475 h a239 hv
  have u15_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24267 h hv u0_2 u13_47 a49
  have u16_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7009 h hv u6_46 u13_47 a49
  have u17_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24827 h hv u0_2 u6_46 u13_47
  have u18_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31425 h h0 hv a239 a237
  have u19_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv u18_103
  have u20_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv u18_103 u10_187 u9_278
  have u21_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c189 h hv u19_13
  have u22_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c18995 h u20_243 hv u12_97 u14_99
  have u23_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c18997 h u20_243 hv u12_97 u14_99
  have u24_80 : T {2, 6, 7} := by
    by_contra hv
    exact c18894 h u20_243 u22_21 hv
  have u25_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u20_243 u10_187 u9_278 hv u3_317 u2_319 u1_321
  have u26_31 : T {0, 6, 7} := by
    by_contra hv
    exact c18896 h u20_243 hv u23_70
  have u27_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c26589 h u25_298 hv u24_80
  have u28_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26597 h u25_298 u26_31 hv
  have u29_11 : T {0, 2, 5} := by
    by_contra hv
    exact c31426 h h0 hv a239 a237
  have u30_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c18045 h a237 u29_11 hv
  have u31_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c18325 h a239 u29_11 hv
  have u32_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1852 h u4_121 u31_106 u30_108 hv
  have u33_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4468 h hv u23_70 u31_106
  have u34_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9508 h hv u28_43 u31_106
  have u35_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1821 h u4_121 u32_110 hv
  have u36_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12163 h hv u5_37 u32_110
  have u37_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c421 h hv u33_140 u21_161 u34_176 u11_186 u36_195 u7_198
  have u38_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c407 h hv u33_140 u21_161 u34_176 u11_186 u36_195 u7_198 u37_199
  have u39_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14828 h hv u22_21 u35_111
  have u40_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21828 h hv u27_8 u35_111
  have u41_74 : T {2, 4, 8} := by
    by_contra hv
    exact c18056 h a237 u38_28 hv
  exact c1097 h u41_74 u16_158 u39_214 u40_264 u9_278 u15_281 u8_283 u17_285

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

private theorem c31428 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ Q {2, 5, 8, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 4, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {0, 3, 5, 7} → ¬ Q {1, 2, 5, 9} → ¬ T {1, 7, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 5, 6, 9} → ¬ T {3, 7, 9} → ¬ Q {2, 5, 6, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 5, 7} → False := by
  classical
  intro n106 n291 n279 n185 n196 n140 n216 n287 n276 n139 n266 n176 n219 n63 n269 n155 n162 n163 n175 n197 n99 n286 n161 n198 n186
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c1481 h hv n99
  have u2_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u0_121 n106 hv
  have u3_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2098 h hv n99 n106
  have u4_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5878 h hv n63 n106
  have u5_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c160 h hv u3_123 u4_150 n155 n161 n162 n163
  have u6_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c1141 h hv u5_160 n216 n266 n276 n286 n287
  have u7_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c402 h hv n139 u5_160 n175 n185 n196 n197
  have u8_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c1184 h hv n163 n219 n269 n279 u6_288 n291
  have u9_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c421 h hv n140 n161 n176 n186 u7_195 n198
  exact c31335 h h0 u2_115 u1_310 u8_290 u9_199

private theorem c31429 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 7} → Q {1, 3, 6, 9} → False := by
  classical
  intro a103 a133 n198 n278 n187 n186 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u6_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h a133 hv
  have u7_8 : T {0, 1, 9} := by
    by_contra hv
    exact c110 h a133 hv
  have u8_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u9_61 : T {1, 6, 9} := by
    by_contra hv
    exact c907 h a237 hv
  have u10_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u11_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u0_121 a103 hv
  have u12_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv a103
  have u13_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c3497 h a133 hv a103
  have u14_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv a103 n187 n278
  have u15_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c189 h hv u12_13
  have u16_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1196 h hv u13_80
  have u17_68 : T {2, 3, 7} := by
    by_contra hv
    exact c18958 h u14_243 u12_13 hv u13_80
  have u18_84 : T {2, 7, 9} := by
    by_contra hv
    exact c18962 h u14_243 u12_13 u13_80 hv
  have u19_95 : T {3, 6, 7} := by
    by_contra hv
    exact c19004 h u14_243 u13_80 hv u11_118
  have u20_53 : T {1, 4, 8} := by
    by_contra hv
    exact c789 h u14_243 hv
  have u21_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c18995 h u14_243 u6_21 u8_97 hv
  have u22_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c18991 h u14_243 u6_21 hv u8_97
  have u23_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u14_243 n187 n278 hv u3_317 u2_319 u1_321
  have u24_31 : T {0, 6, 7} := by
    by_contra hv
    exact c19000 h u14_243 hv u13_80 u11_118
  have u25_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c18915 h u14_243 u4_9 hv u6_21
  have u26_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c18943 h u14_243 u4_9 hv u17_68
  have u27_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12459 h hv u20_53 u17_68
  have u28_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9373 h hv u20_53 u18_84
  have u29_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c26585 h u23_298 hv u18_84
  have u30_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7695 h hv u20_53 u19_95
  have u31_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7615 h hv u10_46 u19_95 u8_97
  have u32_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6625 h hv u10_46 u19_95 u8_97
  have u33_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c18889 h u14_243 hv u19_95
  have u34_35 : T {0, 7, 9} := by
    by_contra hv
    exact c19018 h u14_243 hv u21_99 u11_118
  have u35_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c1044 h hv u22_70
  have u36_82 : T {2, 6, 9} := by
    by_contra hv
    exact c18966 h u14_243 u33_15 u22_70 hv
  have u37_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1329 h u23_298 hv
  have u38_63 : ¬ T {1, 7, 9} := by
    intro hv
    exact c26671 h u23_298 u7_8 u9_61 hv
  have u39_41 : T {1, 2, 7} := by
    by_contra hv
    exact c26682 h u23_298 u12_13 hv u13_80
  have u40_59 : T {1, 6, 7} := by
    by_contra hv
    exact c26704 h u23_298 hv u13_80 u11_118
  have u41_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15537 h hv u24_31 u37_89
  have u42_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c279 h hv u25_19
  have u43_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c999 h hv u26_67
  have u44_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c69 h hv u29_5
  have u45_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23555 h hv u7_8 u6_21 u34_35
  have u46_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25097 h hv u7_8 u6_21 u34_35
  have u47_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15119 h hv u34_35 u37_89
  have u48_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4479 h hv u36_82 u37_89
  have u49_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12381 h hv u39_41 u17_68 u18_84
  have u50_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10833 h hv u39_41 u17_68 u18_84
  have u51_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c24039 h hv u24_31 u40_59 u19_95
  have u52_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25735 h hv u24_31 u40_59 u19_95
  have u53_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31428 h h0 hv u52_291 u51_279 u50_185 u49_196 u48_140 u47_216 u46_287 u45_276 u44_139 u43_266 u42_176 u41_219 u38_63 u35_269 u32_155 u31_162 u30_163 u28_175 u27_197 u21_99 u16_286 u15_161 n198 n186
  have u54_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12723 h hv u5_37 u53_106
  have u55_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3567 h a133 hv a103 u53_106
  have u56_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c417 h hv u48_140 u15_161 u42_176 n186 n198 u54_199
  have u57_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c407 h hv u48_140 u15_161 u42_176 n186 u56_195 n198 u54_199
  exact c18056 h a237 u57_28 u55_74

private theorem c31430 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 7} → ¬ T {2, 3, 9} → T {4, 6, 8} → Q {0, 1, 3, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n28 n70 a106 a133 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u3_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u4_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c3493 h a133 hv a106
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 a106 hv
  have u6_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19316 h hv n28 n70
  have u7_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27122 h hv n28 u4_77 u5_115
  have u8_102 : T {4, 5, 7} := by
    by_contra hv
    exact c18158 h a237 n28 u4_77 hv
  have u9_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 u6_246 a106 u7_301 hv
  have u10_81 : ¬ T {2, 6, 8} := by
    intro hv
    exact c3499 h a133 hv u8_102
  have u11_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c1579 h u9_190 u6_246 hv u7_301 u3_317 u2_322 u1_324
  exact c1209 h u11_281 u10_81

theorem c31431 (h : TenSystem T Q) :
    ¬ Q {0, 3, 4, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 4, 7, 8} → T {0, 4, 8} → ¬ Q {0, 2, 4, 8} → False := by
  classical
  intro n173 n137 n187 n194 n192 a25 n158
  have u0_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c362 h a25 n137 n158 n173 n187 hv n192 n194
  exact c372 h u0_190 n137 n158 n173 n187 n192 n194

private theorem c31432 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 7} → T {0, 4, 8} → ¬ Q {0, 2, 4, 8} → T {2, 6, 7} → T {6, 7, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 5, 8} → False := by
  classical
  intro a111 a25 n158 a80 a118 n192 n187
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12023 h hv u0_37 a111
  have u2_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4163 h hv a80 a111 a118
  have u3_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9205 h hv a80 a111 a118
  exact c31431 h u3_173 u2_137 n187 u1_194 n192 a25 n158

private theorem c31433 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → T {2, 6, 7} → T {6, 7, 9} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → Q {1, 3, 6, 9} → False := by
  classical
  intro a106 a80 a118 a133 n192 n187 n186 n277 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_61 : T {1, 6, 9} := by
    by_contra hv
    exact c907 h a237 hv
  have u2_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1445 h a237 hv
  have u3_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7109 h hv u1_61 u2_97 a118
  have u4_21 : T {0, 3, 9} := by
    by_contra hv
    exact c303 h a133 hv
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 a106 hv
  have u6_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c3493 h a133 hv a106
  have u7_25 : T {0, 4, 8} := by
    by_contra hv
    exact c18054 h a237 hv u6_77
  have u8_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31432 h h0 hv u7_25 u3_158 a80 a118 n192 n187
  have u9_74 : T {2, 4, 8} := by
    by_contra hv
    exact c3488 h a133 hv u8_111
  have u10_102 : T {4, 5, 7} := by
    by_contra hv
    exact c1872 h u0_121 hv u8_111 u5_115
  have u11_28 : ¬ T {0, 5, 7} := by
    intro hv
    exact c18057 h a237 hv u9_74
  have u12_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c31253 h h0 hv n277 u10_102 n186
  have u13_70 : T {2, 3, 9} := by
    by_contra hv
    exact c31430 h h0 u11_28 hv a106 a133 a237
  exact c18851 h u12_242 u4_21 u13_70 u2_97

theorem c31434 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → Q {1, 3, 6, 9} → False := by
  classical
  intro a133 n192 n198 n278 n187 n186 n277 a237
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u2_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31429 h h0 hv a133 n198 n278 n187 n186 a237
  have u3_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 u2_103 hv
  have u4_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv u2_103
  have u5_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv u2_103
  have u6_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31433 h h0 hv u5_80 u3_118 a133 n192 n187 n186 n277 a237
  have u7_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h a133 hv u6_106
  have u8_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u0_121 u2_103 u6_106 hv
  have u9_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12033 h hv u1_46 u7_77
  have u10_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27675 h hv u4_13 u7_77 u5_80
  have u11_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19951 h hv u4_13 u7_77 u5_80
  exact c31402 h h0 u11_250 u8_110 u10_305 u9_194

theorem c31435 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → T {2, 5, 7} → Q {1, 3, 5, 9} → Q {1, 3, 6, 9} → False := by
  classical
  intro n103 a77 a234 a237
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c18055 h a237 hv a77
  have u3_80 : T {2, 6, 7} := by
    by_contra hv
    exact c17634 h a234 u2_25 hv
  have u4_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u5_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u6_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12051 h hv u0_37 u5_45 u4_46
  have u7_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h a237 hv n103
  have u8_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c17627 h a234 u7_13 hv
  have u9_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27675 h hv u7_13 a77 u3_80
  have u10_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19951 h hv u7_13 a77 u3_80
  have u11_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u1_121 n103 u8_106 hv
  exact c31402 h h0 u10_250 u11_110 u9_305 u6_194

theorem c31436 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → Q {1, 3, 5, 9} → ¬ Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → Q {1, 3, 6, 9} → False := by
  classical
  intro a103 a234 n278 n187 a237
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u3_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u6_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u7_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u8_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u9_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h a237 hv
  have u10_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u11_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c26227 h hv u1_2 u10_45 u9_46
  have u12_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13455 h hv u0_37 u10_45 u9_46
  have u13_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u5_121 a103 hv
  have u14_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c18047 h a237 hv a103
  have u15_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv a103 n187 n278
  have u16_106 : T {4, 6, 8} := by
    by_contra hv
    exact c17626 h a234 u14_13 hv
  have u17_50 : T {1, 4, 5} := by
    by_contra hv
    exact c748 h u15_243 hv
  have u18_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u15_243 n187 n278 hv u4_317 u3_319 u2_321
  have u19_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u5_121 u16_106 hv
  have u20_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1847 h u5_121 a103 u16_106 hv
  have u21_86 : T {3, 4, 5} := by
    by_contra hv
    exact c1288 h u18_298 hv
  have u22_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1932 h u5_121 u19_115 u13_118 hv
  have u23_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u20_108
  have u24_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21269 h hv u23_12 u21_86
  have u25_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28975 h hv u23_12 u17_50
  exact c1787 h u22_120 u12_204 u24_260 u11_295 u25_315 u8_325 u7_329 u6_330

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

theorem c31437_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → T {1, 3, 9} → False := by
  classical
  intro n230 n240 n210 a49
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u3_237 : Q {1, 3, 6, 9} := by
    by_contra hv
    exact c31423 h h0 hv n230 n210 n240 a49
  have u4_46 : T {1, 3, 6} := by
    by_contra hv
    exact c690 h u3_237 hv
  have u5_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c23705 h hv u2_2 u4_46 a49
  have u6_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c10933 h hv u1_37 u4_46 a49
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11073 h hv u1_37 u4_46 a49
  have u8_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23845 h hv u2_2 u4_46 a49
  have u9_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12615 h hv u1_37 u4_46 a49
  have u10_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c11775 h hv u1_37 u4_46 a49
  have u11_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31427 h h0 hv u3_237 a49
  have u12_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c31434 h h0 hv u10_192 u9_198 u8_278 u7_187 u6_186 u5_277 u3_237
  have u13_234 : Q {1, 3, 5, 9} := by
    by_contra hv
    exact c732 h u3_237 u12_133 n210 n230 hv u11_239 n240
  have u14_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h u13_234 hv
  have u15_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12051 h hv u1_37 u14_45 u4_46
  have u16_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31436 h h0 hv u13_234 u8_278 u7_187 u3_237
  have u17_13 : T {0, 2, 7} := by
    by_contra hv
    exact c18046 h u3_237 hv u16_103
  have u18_77 : ¬ T {2, 5, 7} := by
    intro hv
    exact c31435 h h0 u16_103 hv u13_234 u3_237
  have u19_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c17627 h u13_234 u17_13 hv
  have u20_25 : T {0, 4, 8} := by
    by_contra hv
    exact c18054 h u3_237 hv u18_77
  have u21_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1846 h u0_121 u16_103 u19_106 hv
  have u22_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u0_121 u16_103 u19_106 hv
  have u23_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c18153 h u3_237 u20_25 hv u21_108
  have u24_28 : T {0, 5, 7} := by
    by_contra hv
    exact c18056 h u3_237 hv u23_74
  have u25_31 : T {0, 6, 7} := by
    by_contra hv
    exact c17636 h u13_234 hv u23_74
  have u26_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27621 h hv u17_13 u24_28 u25_31
  have u27_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19919 h hv u17_13 u24_28 u25_31
  exact c31402 h h0 u27_250 u22_110 u26_305 u15_194

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31437_oai := @OAI.BorsukNine.FiniteObstruction.c31437_oai
