-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c31527
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:14:13.273964+00:00
-- url     : https://prove2.me/submissions/4842d33c-3ddb-4a68-b9bb-022b0c11da5c

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31481
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31520

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

theorem c73 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {0, 1, 6} → False := by
  intro a144 n5
  exact n5 (h.down {0, 1, 6, 8} {0, 1, 6} a144 (by decide) (by decide))

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

theorem c224 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a168 n127 n154 n159 n163 n166 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 7, 9} {0, 2, 9} a168 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n154 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c241 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 4, 8} → False := by
  intro a174 n128 n149 n170 n171 n172 n173
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 9} {0, 3, 4} a174 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c268 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {0, 3, 6} → False := by
  intro a180 n18
  exact n18 (h.down {0, 3, 6, 8} {0, 3, 6} a180 (by decide) (by decide))

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

theorem c435 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {0, 5, 8} → False := by
  intro a200 n29
  exact n29 (h.down {0, 5, 8, 9} {0, 5, 8} a200 (by decide) (by decide))

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

theorem c620 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {1, 2, 8} → False := by
  intro a209 n42
  exact n42 (h.down {1, 2, 3, 8} {1, 2, 8} a209 (by decide) (by decide))

theorem c626 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ T {1, 2, 8} → False := by
  intro a221 n42
  exact n42 (h.down {1, 2, 6, 8} {1, 2, 8} a221 (by decide) (by decide))

theorem c635 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 2, 9} → False := by
  intro a210 n43
  exact n43 (h.down {1, 2, 3, 9} {1, 2, 9} a210 (by decide) (by decide))

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

theorem c680 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {1, 3, 6} → False := by
  intro a207 n46
  exact n46 (h.down {1, 2, 3, 6} {1, 3, 6} a207 (by decide) (by decide))

theorem c696 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 7, 9} → False := by
  intro a208 n131 n228 n232 n235 n238 n239
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 7} {1, 3, 7} a208 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n131 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n238 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 7} = {1, 3, 7, 8} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 7} = {1, 3, 7, 9} by decide)) hS)

theorem c705 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 7} → False := by
  intro a239 n47
  exact n47 (h.down {1, 3, 7, 9} {1, 3, 7} a239 (by decide) (by decide))

theorem c725 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a210 n49
  exact n49 (h.down {1, 2, 3, 9} {1, 3, 9} a210 (by decide) (by decide))

theorem c727 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 3, 9} → False := by
  intro a230 n49
  exact n49 (h.down {1, 3, 4, 9} {1, 3, 9} a230 (by decide) (by decide))

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

theorem c870 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {1, 5, 9} → False := by
  intro a256 n58
  exact n58 (h.down {1, 5, 8, 9} {1, 5, 9} a256 (by decide) (by decide))

theorem c901 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ Q {0, 1, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 6, 7, 8} → False := by
  intro a259 n144 n221 n236 n246 n252 n257
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 8, 9} {1, 6, 8} a259 (by decide) (by decide)
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
  · exact hne (by decide)

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

theorem c956 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a256 n64
  exact n64 (h.down {1, 5, 8, 9} {1, 8, 9} a256 (by decide) (by decide))

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

theorem c995 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {2, 3, 6} → False := by
  intro a207 n67
  exact n67 (h.down {1, 2, 3, 6} {2, 3, 6} a207 (by decide) (by decide))

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

theorem c1096 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ Q {0, 2, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 7, 8} → False := by
  intro a284 n157 n213 n263 n277 n280 n283
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 7, 9} {2, 4, 7} a284 (by decide) (by decide)
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

theorem c1185 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {2, 5, 9} → False := by
  intro a291 n79
  exact n79 (h.down {2, 5, 8, 9} {2, 5, 9} a291 (by decide) (by decide))

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

theorem c1271 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {2, 8, 9} → False := by
  intro a291 n85
  exact n85 (h.down {2, 5, 8, 9} {2, 8, 9} a291 (by decide) (by decide))

theorem c1306 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → False := by
  intro a302 n171 n227 n262 n296 n300 n301
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 9} {3, 4, 6} a302 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c1320 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 4, 7} → False := by
  intro a304 n88
  exact n88 (h.down {3, 4, 7, 9} {3, 4, 7} a304 (by decide) (by decide))

theorem c1348 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 4, 9} → False := by
  intro a304 n90
  exact n90 (h.down {3, 4, 7, 9} {3, 4, 9} a304 (by decide) (by decide))

theorem c1349 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a304 n174 n230 n265 n299 n302 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {3, 4, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

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

theorem c1441 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 7, 8} → False := by
  intro a314 n180 n236 n271 n301 n307 n312
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {3, 6, 8} a314 (by decide) (by decide)
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
  · exact hne (by decide)

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

theorem c1522 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a277 n102
  exact n102 (h.down {2, 4, 5, 7} {4, 5, 7} a277 (by decide) (by decide))

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

theorem c1612 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a283 n108
  exact n108 (h.down {2, 4, 7, 8} {4, 7, 8} a283 (by decide) (by decide))

theorem c1629 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a304 n109
  exact n109 (h.down {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide))

theorem c1630 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a304 n193 n249 n284 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
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

theorem c1774 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a203 n259 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {6, 8, 9} a203 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
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

theorem c1821 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 6, 7} → False := by
  intro a121 a110 a111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a110 a111

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

theorem c1896 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a121 n105 n111 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c1898 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {6, 7, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n105 n117 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

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

theorem c2753 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a127 a93 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {5, 8} {3, 4, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c2789 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 9} → T {6, 7, 8} → False := by
  intro a128 a79 a117
  have hc := h.complementary {0, 1, 3, 4} {2, 5, 9} a128 (by decide) (by decide)
  have he : ( {0, 1, 3, 4} : Finset Labels)ᶜ \ {2, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a79 a117

theorem c3305 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a131 a78 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {5, 8} {2, 4, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c4689 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 9} → T {3, 4, 9} → T {3, 7, 9} → False := by
  intro a141 a70 a90 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {3, 9} {2, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

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

theorem c5729 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 9} → T {6, 7, 8} → False := by
  intro a149 a58 a117
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a58 a117

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

theorem c6435 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {4, 6, 7} → False := by
  intro a154 a57 a105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a105

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

theorem c7125 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 6} → T {5, 7, 8} → False := by
  intro a159 a46 a114
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 6} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a46 a114

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

theorem c7621 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 7} → T {3, 4, 7} → T {3, 7, 9} → False := by
  intro a162 a47 a88 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {3, 7} {1, 4, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c7783 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a163 a52 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 9} {4, 7} {1, 3, 6} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

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

theorem c8119 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 5, 8} → T {3, 4, 7} → False := by
  intro a166 a57 a88
  have hc := h.complementary {0, 2, 6, 9} {1, 5, 8} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a88

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

theorem c8633 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a169 a52 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 7} {1, 3, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c8666 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {1, 2, 8} → ¬ T {6, 7, 9} → False := by
  intro a170 n42 n118
  have hc := h.complementary {0, 3, 4, 5} {1, 2, 8} a170 (by decide) (by decide)
  have he : ( {0, 3, 4, 5} : Finset Labels)ᶜ \ {1, 2, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n118)

theorem c8905 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a171 a57 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {5, 8} {1, 2, 9} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c8945 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 2, 6} → T {5, 8, 9} → False := by
  intro a172 a40 a116
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 6} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a116

theorem c9082 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {1, 2, 5} → ¬ T {6, 7, 9} → False := by
  intro a173 n39 n118
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 5} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n118)

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

theorem c9226 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n41 n112
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 7} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n112)

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

theorem c11075 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a187 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 3} {2, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
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

theorem c11893 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 3, 6} → T {2, 5, 8} → False := by
  intro a193 a46 a78
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a46 a78

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

theorem c12691 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 4, 9} → False := by
  intro a198 a49 a70 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {3, 9} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)

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

theorem c12975 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 7} → T {3, 4, 7} → T {3, 6, 7} → False := by
  intro a200 a47 a88 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {3, 7} {1, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)

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

theorem c13566 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a205 n29 n118
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n118)

theorem c13844 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a207 n24 n116
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n116)

theorem c13849 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 4, 9} → T {5, 7, 8} → False := by
  intro a207 a26 a114
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 9} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a26 a114

theorem c13850 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 5, 7} → ¬ T {4, 8, 9} → False := by
  intro a207 n28 n110
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n110)

theorem c13859 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 7, 9} → T {4, 5, 8} → False := by
  intro a207 a35 a103
  have hc := h.complementary {1, 2, 3, 6} {0, 7, 9} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a103

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

theorem c14086 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a208 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 7} {5, 8} {0, 6, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c14786 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a213 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 4, 7} {5, 8} {0, 6, 9} a213 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

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

theorem c16651 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 5, 7} → T {2, 8, 9} → False := by
  intro a227 a28 a85
  have hc := h.complementary {1, 3, 4, 6} {0, 5, 7} a227 (by decide) (by decide)
  have he : ( {1, 3, 4, 6} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a85

theorem c16797 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 6, 8} → T {2, 5, 9} → False := by
  intro a228 a32 a79
  have hc := h.complementary {1, 3, 4, 7} {0, 6, 8} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a79

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

theorem c17344 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 6} → ¬ T {4, 8, 9} → False := by
  intro a232 n12 n110
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 6} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n110)

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

theorem c17885 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {2, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a235 a78 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {5, 8} {2, 4, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c17908 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {0, 2, 9} → ¬ T {4, 5, 7} → False := by
  intro a236 n15 n102
  have hc := h.complementary {1, 3, 6, 8} {0, 2, 9} a236 (by decide) (by decide)
  have he : ( {1, 3, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n102)

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

theorem c18186 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 6} → ¬ T {4, 5, 9} → False := by
  intro a238 n12 n104
  have hc := h.complementary {1, 3, 7, 8} {0, 2, 6} a238 (by decide) (by decide)
  have he : ( {1, 3, 7, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n104)

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

theorem c19002 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n31 n95 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {0, 3, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

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

theorem c19320 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {0, 7, 9} → ¬ T {2, 3, 5} → False := by
  intro a246 n35 n66
  have hc := h.complementary {1, 4, 6, 8} {0, 7, 9} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n66)

theorem c19773 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 3, 6} → T {0, 5, 6} → T {0, 6, 8} → False := by
  intro a249 a18 a27 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {0, 6} {3, 5, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) a32)

theorem c19783 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 3} → T {2, 3, 5} → T {2, 3, 6} → False := by
  intro a249 a9 a66 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {2, 3} {0, 5, 6} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

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

theorem c20143 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {4, 7, 9} → False := by
  intro a252 a9 a109
  have hc := h.complementary {1, 5, 6, 8} {0, 2, 3} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a109

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

theorem c20858 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 4, 9} → ¬ T {2, 3, 5} → False := by
  intro a257 n26 n66
  have hc := h.complementary {1, 6, 7, 8} {0, 4, 9} a257 (by decide) (by decide)
  have he : ( {1, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n66)

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

theorem c21551 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 5, 7} → T {1, 8, 9} → False := by
  intro a262 a28 a64
  have hc := h.complementary {2, 3, 4, 6} {0, 5, 7} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a64

theorem c21786 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a263 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 7} {5, 8} {0, 6, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c22074 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a265 n29 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {5, 8} {0, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

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

theorem c23847 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a278 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {1, 3} {0, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24076 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → False := by
  intro a280 n29 n49
  have hc := h.complementary {2, 4, 6, 7} {0, 5, 8} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n49)

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

theorem c26147 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 4, 7} → T {1, 4, 7} → T {3, 4, 7} → False := by
  intro a294 a24 a52 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {4, 7} {0, 1, 3} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c26318 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 7, 9} → ¬ T {1, 2, 8} → False := by
  intro a296 n35 n42
  have hc := h.complementary {3, 4, 5, 6} {0, 7, 9} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n42)

theorem c26645 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a298 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 2} {0, 6, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c27020 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 7, 9} → ¬ T {1, 2, 5} → False := by
  intro a301 n35 n39
  have hc := h.complementary {3, 4, 6, 8} {0, 7, 9} a301 (by decide) (by decide)
  have he : ( {3, 4, 6, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n39)

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

theorem c27423 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {5, 6, 8} → False := by
  intro a304 a1 a112
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 2} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a112

theorem c27427 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 6} → T {2, 5, 8} → False := by
  intro a304 a5 a78
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a5 a78

theorem c27433 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 2, 6} → T {1, 5, 8} → False := by
  intro a304 a12 a57
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a57

theorem c27438 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 6} → False := by
  intro a304 n29 n40
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n40)

theorem c27466 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 5, 6} → False := by
  intro a304 n5 n12 n27
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {0, 6} {1, 2, 5} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n27 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) ht)

theorem c27468 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 6, 8} → False := by
  intro a304 n5 n12 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {0, 6} {1, 2, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) ht)

theorem c27483 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a304 a1 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 2} {0, 5, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c27487 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a304 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 2} {0, 6, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

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

theorem c27548 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a304 n29 n57 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {5, 8} {0, 1, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c27550 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a304 n29 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {5, 8} {0, 2, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c27563 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {5, 6, 7} → False := by
  intro a305 a1 a111
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 2} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a111

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

theorem c28558 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 4, 9} → ¬ T {1, 2, 5} → False := by
  intro a312 n26 n39
  have hc := h.complementary {3, 6, 7, 8} {0, 4, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n39)

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

theorem c31473 (h : TenSystem T Q) :
    ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 8, 9} → T {0, 2, 9} → False := by
  classical
  intro n166 n159 n163 n127 n154 n169 a15
  have u0_168 : Q {0, 2, 7, 9} := by
    by_contra hv
    exact c212 h a15 n127 n154 n159 n163 n166 hv n169
  exact c224 h u0_168 n127 n154 n159 n163 n166 n169

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

theorem c31521 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a239 a304
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u7_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u8_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv u7_118
  have u9_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u2_37 u9_109
  have u11_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u12_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u13_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u14_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u15_49 : T {1, 3, 9} := by
    by_contra hv
    exact c733 h a239 hv
  have u16_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23847 h hv u1_2 u14_47 u15_49
  have u17_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11075 h hv u2_37 u14_47 u15_49
  have u18_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7621 h hv u14_47 u13_88 u11_99
  have u19_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 u15_49 hv
  have u20_243 : Q {1, 4, 5, 8} := by
    by_contra hv
    exact c31421 h h0 hv u8_103 u17_187 u16_278
  have u21_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u19_210 hv
  have u22_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u19_210 hv
  have u23_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c14277 h u19_210 hv u8_103
  have u24_298 : Q {3, 4, 5, 8} := by
    by_contra hv
    exact c1536 h u20_243 u17_187 u16_278 hv u5_317 u4_319 u3_321
  have u25_95 : T {3, 6, 7} := by
    by_contra hv
    exact c19002 h u20_243 u23_31 hv u7_118
  have u26_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c26645 h u24_298 u6_1 hv u21_43
  have u27_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4689 h hv u22_70 u12_90 u11_99
  have u28_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12691 h hv u15_49 u22_70 u12_90
  have u29_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12975 h hv u14_47 u13_88 u25_95
  have u30_29 : T {0, 5, 8} := by
    by_contra hv
    exact c27438 h a304 hv u26_40
  have u31_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c428 h hv u27_141 u18_162 u17_187 u10_196 u28_198 u29_200
  exact c422 h u30_29 u27_141 u18_162 u31_177 u17_187 u10_196 u28_198 u29_200

theorem c31525 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n116 n29 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u4_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u5_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u6_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u7_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u8_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u10_78 : T {2, 5, 8} := by
    by_contra hv
    exact c27550 h a304 n29 hv u9_112
  have u11_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c27427 h a304 hv u10_78
  have u12_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c73 h hv u11_5
  have u13_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 n29 hv
  have u14_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c27483 h a304 u0_1 hv u13_40
  have u15_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u14_39
  have u16_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c27487 h a304 u0_1 u13_40 hv
  have u17_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c626 h hv u16_42
  have u18_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c620 h hv u16_42
  have u19_57 : T {1, 5, 8} := by
    by_contra hv
    exact c27548 h a304 n29 hv u9_112
  have u20_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c27433 h a304 hv u19_57
  have u21_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27468 h a304 u11_5 u20_12 hv
  have u22_27 : T {0, 5, 6} := by
    by_contra hv
    exact c27466 h a304 u11_5 u20_12 hv
  have u23_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u24_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8119 h hv u19_57 u23_88
  have u25_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 n49
  have u26_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u27_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13566 h hv n29 u26_118
  have u28_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv n49 u9_112
  have u29_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c725 h hv n49
  have u30_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u26_118
  have u31_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u32_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20143 h hv u5_9 u31_109
  have u33_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27843 h hv u0_1 u31_109
  have u34_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1810 h u1_121 hv n116
  have u35_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1884 h u1_121 u9_112 hv n116
  have u36_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14786 h hv n29 u9_112 n116
  have u37_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21786 h hv n29 u9_112 n116
  have u38_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14086 h hv n29 u9_112 n116
  have u39_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1845 h u1_121 u34_105 hv u31_109
  have u40_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c1841 h u1_121 hv u34_105 u31_109
  have u41_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6435 h hv u19_57 u34_105
  have u42_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c544 h u1_121 u27_205 u15_206 hv u38_208 u18_209 u29_210
  have u43_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c1612 h hv u39_108
  have u44_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c1522 h hv u40_102
  have u45_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1804 h u1_121 u40_102 hv
  have u46_46 : T {1, 3, 6} := by
    by_contra hv
    exact c680 h u42_207 hv
  have u47_67 : T {2, 3, 6} := by
    by_contra hv
    exact c995 h u42_207 hv
  have u48_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c13859 h u42_207 hv u30_103
  have u49_26 : ¬ T {0, 4, 9} := by
    intro hv
    exact c13849 h u42_207 hv u35_114
  have u50_24 : T {0, 4, 7} := by
    by_contra hv
    exact c13844 h u42_207 hv n116
  have u51_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c1096 h hv u28_157 u36_213 u37_263 u44_277 u25_280 u43_283
  have u52_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7125 h hv u46_46 u35_114
  have u53_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11893 h hv u46_46 u10_78
  have u54_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27020 h hv u48_35 u14_39
  have u55_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c28558 h hv u49_26 u14_39
  have u56_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c1630 h a304 u53_193 hv u51_284 u4_320 u3_323 u2_325
  have u57_52 : T {1, 4, 7} := by
    by_contra hv
    exact c780 h u56_249 hv
  have u58_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c19773 h u56_249 hv u22_27 u21_32
  have u59_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c19783 h u56_249 u5_9 hv u47_67
  have u60_93 : T {3, 5, 8} := by
    by_contra hv
    exact c19850 h u56_249 n29 hv u9_112
  have u61_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22905 h hv u50_24 u57_52 u31_109
  have u62_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7783 h hv u57_52 u23_88 u34_105
  have u63_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8633 h hv u57_52 u23_88 u34_105
  have u64_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26147 h hv u50_24 u57_52 u23_88
  have u65_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c268 h hv u58_18
  have u66_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19320 h hv u48_35 u59_66
  have u67_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20858 h hv u49_26 u59_66
  have u68_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2753 h hv u60_93 u30_103 u35_114
  have u69_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c31473 h u24_166 u52_159 u62_163 u68_127 u41_154 u63_169 hv
  have u70_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c17908 h hv u69_15 u40_102
  have u71_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1441 h hv u65_180 u70_236 u61_271 u54_301 u33_307 u55_312
  have u72_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c901 h hv u12_144 u17_221 u70_236 u66_246 u32_252 u67_257
  have u73_203 : Q {0, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 hv u64_294 u71_314 u45_119
  exact c1774 h u73_203 u72_259 u64_294 u71_314 u8_324 u7_328 u6_330

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases102
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31526 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n311 n29 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u6_57 : T {1, 5, 8} := by
    by_contra hv
    exact c27548 h a304 n29 hv u5_112
  have u7_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c27433 h a304 hv u6_57
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u9_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31525 h h0 hv n29 n49 a304
  have u10_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u4_121 hv u9_116
  have u11_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u4_121 u10_105 hv u8_118
  have u12_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1809 h u4_121 hv u11_117
  have u13_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18186 h hv u7_12 u12_104
  have u14_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u4_121 u10_105 hv u8_118
  have u15_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1821 h u4_121 hv u14_111
  have u16_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17344 h hv u7_12 u15_110
  have u17_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26723 h hv u0_1 u11_117
  have u18_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27563 h hv u0_1 u14_111
  have u19_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u4_121 hv u8_118
  have u20_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u4_121 u19_103 hv u9_116
  have u21_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22074 h hv n29 u5_112 u20_114
  have u22_78 : T {2, 5, 8} := by
    by_contra hv
    exact c27550 h a304 n29 hv u5_112
  have u23_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8905 h hv u6_57 u22_78 u9_116
  have u24_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17885 h hv u22_78 u19_103 u9_116
  have u25_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3305 h hv u22_78 u19_103 u9_116
  have u26_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 n29 hv
  have u27_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c8945 h hv u26_40 u9_116
  have u28_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26863 h hv u0_1 u9_116
  have u29_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c27483 h a304 u0_1 hv u26_40
  have u30_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9082 h hv u29_39 u8_118
  have u31_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c575 h hv u29_39
  have u32_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c27487 h a304 u0_1 u26_40 hv
  have u33_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8666 h hv u32_42 u8_118
  have u34_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c620 h hv u32_42
  have u35_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c27427 h a304 hv u22_78
  have u36_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27468 h a304 u35_5 u7_12 hv
  have u37_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13566 h hv n29 u8_118
  have u38_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv n29
  have u39_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u40_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c725 h hv n49
  have u41_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c31521 h h0 hv a304
  have u42_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u9_116 u38_200 n311 hv
  have u43_79 : T {2, 5, 9} := by
    by_contra hv
    exact c1185 h u42_291 hv
  have u44_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1271 h u42_291 hv
  have u45_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c1733 h u42_291 u38_200 hv n311 u3_321 u2_328 u1_329
  have u46_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2789 h hv u43_79 u11_117
  have u47_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16797 h hv u36_32 u43_79
  have u48_58 : T {1, 5, 9} := by
    by_contra hv
    exact c870 h u45_256 hv
  have u49_64 : T {1, 8, 9} := by
    by_contra hv
    exact c956 h u45_256 hv
  have u50_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c696 h hv u25_131 u47_228 u16_232 u24_235 u13_238 u41_239
  have u51_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5729 h hv u48_58 u11_117
  have u52_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c544 h u4_121 u37_205 u31_206 hv u50_208 u34_209 u40_210
  have u53_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c241 h hv u46_128 u51_149 u33_170 u23_171 u27_172 u30_173
  have u54_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c13859 h u52_207 hv u19_103
  have u55_28 : T {0, 5, 7} := by
    by_contra hv
    exact c13850 h u52_207 hv u15_110
  have u56_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1349 h a304 u53_174 u39_230 u21_265 u17_299 hv u18_305
  have u57_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27020 h hv u54_35 u29_39
  have u58_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26318 h hv u54_35 u32_42
  have u59_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21551 h hv u55_28 u49_64
  have u60_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16651 h hv u55_28 u44_85
  exact c1306 h u56_302 u23_171 u60_227 u59_262 u58_296 u28_300 u57_301

theorem c31527_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n29 n49 a304
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u3_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u4_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv u3_118
  have u5_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u1_1 hv
  have u6_40 : T {1, 2, 6} := by
    by_contra hv
    exact c27438 h a304 n29 hv
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31525 h h0 hv n29 n49 a304
  have u8_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u0_121 hv u7_116
  have u9_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u0_121 u4_103 hv u7_116
  have u10_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u0_121 u8_105 hv u3_118
  have u11_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u0_121 u8_105 hv u3_118
  have u12_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22074 h hv n29 u5_112 u9_114
  have u13_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27563 h hv u1_1 u10_111
  have u14_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26723 h hv u1_1 u11_117
  have u15_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c31526 h h0 hv n29 n49 a304
  have u16_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c28467 h u15_311 u1_1 u6_40 hv
  have u17_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9226 h hv u16_41 u5_112
  have u18_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27158 h hv n29 u16_41
  exact c1349 h a304 u17_174 u2_230 u12_265 u14_299 u18_302 u13_305

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c31527_oai := @OAI.BorsukNine.FiniteObstruction.c31527_oai
