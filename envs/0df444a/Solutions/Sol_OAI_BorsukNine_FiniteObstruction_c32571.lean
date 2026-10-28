-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32571
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:16:46.803319+00:00
-- url     : https://prove2.me/submissions/fc325996-86d3-46f4-8eeb-07e166518649

import Mathlib
import Definitions.Def_OAIQ058B000
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31520
import Theorems.Thm_OAI_BorsukNine_FiniteObstruction_c31527

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

theorem c452 (h : TenSystem T Q) :
    T {0, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 7, 9} → False := by
  intro a31 n143 n164 n179 n189 n195 n201 n202
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 6, 7} a31
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n195 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 7} = {0, 6, 7, 8} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 7} = {0, 6, 7, 9} by decide)) hS)

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

theorem c603 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {1, 2, 7} → False := by
  intro a125 n41
  exact n41 (h.down {0, 1, 2, 7} {1, 2, 7} a125 (by decide) (by decide))

theorem c633 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {1, 2, 9} → False := by
  intro a127 n43
  exact n43 (h.down {0, 1, 2, 9} {1, 2, 9} a127 (by decide) (by decide))

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

theorem c727 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 3, 9} → False := by
  intro a230 n49
  exact n49 (h.down {1, 3, 4, 9} {1, 3, 9} a230 (by decide) (by decide))

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

theorem c1008 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {2, 3, 7} → False := by
  intro a152 n68
  exact n68 (h.down {0, 2, 3, 7} {2, 3, 7} a152 (by decide) (by decide))

theorem c1042 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 3, 9} → False := by
  intro a265 n70
  exact n70 (h.down {2, 3, 4, 9} {2, 3, 9} a265 (by decide) (by decide))

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

theorem c1248 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a168 n84
  exact n84 (h.down {0, 2, 7, 9} {2, 7, 9} a168 (by decide) (by decide))

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

theorem c1305 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 4, 6} → False := by
  intro a302 n87
  exact n87 (h.down {3, 4, 6, 9} {3, 4, 6} a302 (by decide) (by decide))

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

theorem c1395 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 8} → False := by
  intro a311 n93
  exact n93 (h.down {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide))

theorem c1410 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 9} → False := by
  intro a311 n94
  exact n94 (h.down {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide))

theorem c1413 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {3, 6, 7} → False := by
  intro a179 n95
  exact n95 (h.down {0, 3, 6, 7} {3, 6, 7} a179 (by decide) (by decide))

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

theorem c1449 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 6, 9} → False := by
  intro a302 n97
  exact n97 (h.down {3, 4, 6, 9} {3, 6, 9} a302 (by decide) (by decide))

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

theorem c1534 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a187 n243 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {4, 5, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
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

theorem c1698 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a198 n114
  exact n114 (h.down {0, 5, 7, 8} {5, 7, 8} a198 (by decide) (by decide))

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

theorem c1758 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a202 n118
  exact n118 (h.down {0, 6, 7, 9} {6, 7, 9} a202 (by decide) (by decide))

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

theorem c1946 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a122 n93 n118
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n118)

theorem c1949 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 9} → T {6, 7, 8} → False := by
  intro a122 a94 a117
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 9} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a94 a117

theorem c1951 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 7} → T {5, 8, 9} → False := by
  intro a122 a95 a116
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 7} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a95 a116

theorem c2001 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 9} → T {3, 7, 9} → T {3, 8, 9} → False := by
  intro a122 a97 a99 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 9} {6, 7, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c2089 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 9} → T {6, 7, 8} → False := by
  intro a123 a90 a117
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 9} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a90 a117

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

theorem c2239 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 7, 9} → T {4, 5, 8} → False := by
  intro a124 a99 a103
  have hc := h.complementary {0, 1, 2, 6} {3, 7, 9} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 7, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a99 a103

theorem c2365 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 6} → T {5, 8, 9} → False := by
  intro a125 a87 a116
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 6} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a87 a116

theorem c2373 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 5, 8} → T {4, 6, 9} → False := by
  intro a125 a93 a107
  have hc := h.complementary {0, 1, 2, 7} {3, 5, 8} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a107

theorem c2509 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 9} → T {5, 6, 7} → False := by
  intro a126 a90 a111
  have hc := h.complementary {0, 1, 2, 8} {3, 4, 9} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 4, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a90 a111

theorem c2643 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {6, 7, 8} → False := by
  intro a127 a86 a117
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 5} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a86 a117

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

theorem c2754 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a127 n93 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 9} {5, 8} {3, 6, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c2763 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a127 a95 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {6, 7} {3, 5, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

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

theorem c4717 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a141 a90 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 9} {3, 6, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

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

theorem c5005 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {3, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a143 a93 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 7} {5, 8} {3, 4, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

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

theorem c7441 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 3, 6} → T {1, 4, 6} → T {1, 6, 9} → False := by
  intro a161 a46 a51 a61
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {1, 6} {3, 4, 9} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 6} = {1, 6, 9} by decide)) a61)

theorem c7548 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 3, 9} → ¬ T {4, 6, 7} → False := by
  intro a162 n49 n105
  have hc := h.complementary {0, 2, 5, 8} {1, 3, 9} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n105)

theorem c7837 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 5, 8} → T {3, 4, 9} → False := by
  intro a164 a57 a90
  have hc := h.complementary {0, 2, 6, 7} {1, 5, 8} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a90

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

theorem c7910 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 3, 9} → ¬ T {3, 5, 9} → ¬ T {3, 8, 9} → False := by
  intro a164 n49 n94 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {3, 9} {1, 5, 8} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c7945 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {3, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a164 a93 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {5, 8} {3, 4, 9} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c8289 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 3, 6} → T {1, 4, 6} → T {1, 6, 9} → False := by
  intro a167 a46 a51 a61
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {1, 6} {3, 4, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 6} = {1, 6, 9} by decide)) a61)

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

theorem c9642 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 4} → ¬ T {6, 7, 9} → False := by
  intro a177 n38 n118
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 4} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n118)

theorem c9647 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 7} → T {4, 6, 9} → False := by
  intro a177 a41 a107
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 7} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a107

theorem c9648 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 9} → ¬ T {4, 6, 7} → False := by
  intro a177 n43 n105
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 9} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n105)

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

theorem c9929 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 2, 9} → T {4, 5, 8} → False := by
  intro a179 a43 a103
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 9} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a43 a103

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

theorem c11048 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 2, 9} → ¬ T {3, 6, 7} → False := by
  intro a187 n43 n95
  have hc := h.complementary {0, 4, 5, 8} {1, 2, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n95)

theorem c11052 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 7} → ¬ T {2, 6, 9} → False := by
  intro a187 n47 n82
  have hc := h.complementary {0, 4, 5, 8} {1, 3, 7} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 6, 9} := by decide
  rw [he] at hc
  exact n47 (hc.mpr n82)

theorem c11058 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 6, 9} → ¬ T {2, 3, 7} → False := by
  intro a187 n61 n68
  have hc := h.complementary {0, 4, 5, 8} {1, 6, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 6, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n61 (hc.mpr n68)

theorem c11076 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 6} → ¬ T {1, 3, 7} → ¬ T {1, 3, 9} → False := by
  intro a187 n46 n47 n49
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {1, 3} {6, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) ht)

theorem c11133 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {2, 3, 9} → T {2, 6, 9} → T {2, 7, 9} → False := by
  intro a187 a70 a82 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {2, 9} {3, 6, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c11323 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {5, 8, 9} → False := by
  intro a189 a37 a116
  have hc := h.complementary {0, 4, 6, 7} {1, 2, 3} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a116

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

theorem c12185 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a195 a37 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 2} {3, 4, 9} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c12864 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {3, 6, 7} → False := by
  intro a200 n38 n95
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 4} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n95)

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

theorem c12977 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {2, 3, 7} → T {3, 4, 7} → T {3, 6, 7} → False := by
  intro a200 a68 a88 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {3, 7} {2, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)

theorem c12982 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a200 n51 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {4, 6} {1, 3, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c13025 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a201 a37 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 2} {3, 4, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

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

theorem c20838 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n31 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {6, 7} {0, 3, 4} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

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

theorem c22076 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a265 n57 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {5, 8} {1, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c22083 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a265 a31 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {6, 7} {0, 5, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

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

theorem c23796 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {1, 3, 9} → False := by
  intro a278 n31 n49
  have hc := h.complementary {2, 4, 5, 8} {0, 6, 7} a278 (by decide) (by decide)
  have he : ( {2, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n49)

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

theorem c25738 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n31 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {6, 7} {0, 3, 4} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

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

theorem c27423 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {5, 6, 8} → False := by
  intro a304 a1 a112
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 2} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a112

theorem c27439 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 5, 8} → T {1, 2, 6} → False := by
  intro a304 a29 a40
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a40

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

theorem c28421 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 6, 7} → T {1, 2, 4} → False := by
  intro a311 a31 a38
  have hc := h.complementary {3, 5, 8, 9} {0, 6, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a31 a38

theorem c28468 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → False := by
  intro a311 n38 n40 n41
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {1, 2} {4, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)

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

theorem c31528 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 6, 7} → ¬ Q {3, 4, 5, 8} → ¬ T {3, 6, 7} → ¬ T {1, 3, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n31 n298 n95 n49 n118
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
  have u4_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u0_121 hv n118
  have u5_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c23796 h hv n31 n49
  have u6_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c19002 h hv n31 n95 n118
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c1534 h hv u6_243 u5_278 n298 u3_317 u2_319 u1_321
  exact c31421 h h0 u6_243 u4_103 u7_187 u5_278

theorem c31529 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a311 a116 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u3_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u4_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv a116
  have u5_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u1_121 u4_105 hv u3_118
  have u6_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2089 h hv u2_90 u5_117
  have u7_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26723 h hv u0_1 u5_117
  have u8_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u1_121 u4_105 hv u3_118
  have u9_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2509 h hv u2_90 u8_111
  have u10_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27563 h hv u0_1 u8_111
  have u11_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u12_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u11_29 hv
  have u13_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u3_118
  have u14_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u1_121 u13_103 hv a116
  have u15_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u12_40 u14_114
  have u16_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u1_121 hv u14_114
  have u17_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u18_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u19_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u18_99 u13_103
  have u20_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1395 h a311 hv
  have u21_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1410 h a311 hv
  have u22_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2373 h hv u20_93 u16_107
  have u23_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1949 h hv u21_94 u5_117
  have u24_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c4 h u1_121 u23_122 u6_123 u19_124 u22_125 u9_126 hv
  have u25_86 : ¬ T {3, 4, 5} := by
    intro hv
    exact c2643 h u24_127 hv u5_117
  have u26_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c2763 h u24_127 hv u8_111 u5_117
  have u27_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1288 h hv u25_86
  have u28_31 : T {0, 6, 7} := by
    by_contra hv
    exact c31528 h h0 hv u27_298 u26_95 n49 u3_118
  have u29_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22083 h hv u28_31 u8_111 u5_117
  have u30_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28421 h a311 u28_31 hv
  have u31_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1349 h a304 u15_174 u17_230 u29_265 u7_299 hv u10_305
  have u32_41 : T {1, 2, 7} := by
    by_contra hv
    exact c28468 h a311 u30_38 u12_40 hv
  exact c27159 h u31_302 u11_29 u32_41

theorem c31530 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 4} → ¬ T {3, 6, 7} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 2, 5, 8} → T {0, 5, 8} → Q {3, 4, 7, 9} → False := by
  classical
  intro n38 n95 n141 n198 n162 a29 a304
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u3_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12303 h hv u0_37 u2_109
  have u4_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9642 h hv n38 u1_118
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c12864 h hv n38 n95
  exact c31443 h u4_177 n141 a29 u5_200 n162 n198 u3_196

theorem c31531 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 1, 2, 9} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a127 a116 n49 a304
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u5_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u6_103 : T {4, 5, 8} := by
    by_contra hv
    exact c1806 h u1_121 hv u5_118
  have u7_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c1883 h u1_121 u6_103 hv a116
  have u8_107 : T {4, 6, 9} := by
    by_contra hv
    exact c1814 h u1_121 hv u7_114
  have u9_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u4_90 u8_107 u3_109
  have u10_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u7_114
  have u11_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1811 h u1_121 hv a116
  have u12_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv n49 u11_105
  have u13_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1898 h u1_121 u11_105 hv u5_118
  have u14_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1896 h u1_121 u11_105 hv u5_118
  have u15_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c11323 h hv u2_37 a116
  have u16_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u17_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c1758 h hv u5_118
  have u18_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c27423 h a304 u0_1 hv
  have u19_43 : T {1, 2, 9} := by
    by_contra hv
    exact c633 h a127 hv
  have u20_86 : ¬ T {3, 4, 5} := by
    intro hv
    exact c2643 h a127 hv u13_117
  have u21_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c2763 h a127 hv u14_111 u13_117
  have u22_93 : T {3, 5, 8} := by
    by_contra hv
    exact c2754 h a127 hv u18_112 u7_114
  have u23_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9929 h hv u19_43 u6_103
  have u24_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1288 h hv u20_86
  have u25_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7945 h hv u22_93 u6_103 a116
  have u26_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5005 h hv u22_93 u6_103 a116
  have u27_31 : T {0, 6, 7} := by
    by_contra hv
    exact c31528 h h0 hv u24_298 u21_95 n49 u5_118
  have u28_38 : T {1, 2, 4} := by
    by_contra hv
    exact c31530 h h0 hv u21_95 u9_141 u10_198 u12_162 u16_29 a304
  have u29_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12185 h hv u2_37 u28_38 u19_43
  have u30_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13025 h hv u2_37 u28_38 u19_43
  exact c452 h u27_31 u26_143 u25_164 u23_179 u15_189 u29_195 u30_201 u17_202

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

theorem c31631 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  classical
  intro n103 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1806 h u0_121 n103 n118

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

theorem c31708 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → T {5, 8, 9} → T {4, 5, 8} → False := by
  classical
  intro a114 a116 a103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1883 h u0_121 a103 a114 a116

theorem c31721 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  classical
  intro n111 n105 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1896 h u0_121 n105 n111 n118

theorem c31723 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  classical
  intro n117 n105 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1898 h u0_121 n105 n117 n118

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

theorem c31807 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a189 a116
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11323 h a189 u0_37 a116

theorem c31869 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 7} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a195 a38 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12185 h a195 u0_37 a38 a43

theorem c31877 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a196 a109
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12303 h a196 u0_37 a109

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

theorem c31929 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 6, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a201 a38 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13025 h a201 u0_37 a38 a43

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

theorem c32397 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a299 a117
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26723 h a299 u0_1 a117

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

theorem c32447 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a304 a112
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27423 h a304 u0_1 a112

theorem c32457 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 8, 9} → T {5, 6, 7} → False := by
  classical
  intro a305 a111
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27563 h a305 u0_1 a111

private theorem c32567 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 2, 6, 7} → T {0, 6, 7} → T {1, 2, 4} →
      ¬ Q {0, 3, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 6, 7, 9} → False := by
  classical
  intro a43 n143 n164 a31 a38 n179 n189 n202
  have u0_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c31869 h h0 hv a38 a43
  have u1_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c31929 h h0 hv a38 a43
  exact c452 h a31 n143 n164 n179 n189 u0_195 u1_201 n202

private theorem c32568 (h : TenSystem T Q) :
    ¬ T {1, 2, 9} → ¬ T {3, 6, 7} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 5, 7, 8} →
      ¬ Q {0, 2, 5, 8} → ¬ T {4, 6, 7} → T {0, 5, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n43 n95 n141 n198 n162 n105 a29 n196
  have u0_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9648 h hv n43 n105
  have u1_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11048 h hv n43 n95
  have u2_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31443 h u0_177 n141 a29 hv n162 n198 n196
  exact c436 h u2_200 n141 n162 u0_177 u1_187 n196 n198

theorem c32569 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 6, 7} → ¬ T {3, 6, 7} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a31 n95 a116 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u0_109
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u3_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u4_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv n49 u3_105
  have u5_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u6_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u5_118
  have u7_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv a116 u6_103
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u7_114
  have u9_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u10_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u7_114
  have u11_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u9_90 u10_107 u0_109
  have u12_43 : T {1, 2, 9} := by
    by_contra hv
    exact c32568 h hv n95 u11_141 u8_198 u4_162 u3_105 u2_29 u1_196
  have u13_38 : T {1, 2, 4} := by
    by_contra hv
    exact c31530 h h0 hv n95 u11_141 u8_198 u4_162 u2_29 a304
  have u14_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c1413 h hv n95
  have u15_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c31531 h h0 hv a116 n49 a304
  have u16_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u3_105 u5_118
  have u17_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2089 h hv u9_90 u16_117
  have u18_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u16_117
  have u19_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u3_105 u5_118
  have u20_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2509 h hv u9_90 u19_111
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32457 h h0 hv u19_111
  have u22_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u2_29 hv
  have u23_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u22_40 u7_114
  have u24_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c31807 h h0 hv a116
  have u25_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u26_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u27_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u26_99 u6_103
  have u28_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c1758 h hv u5_118
  have u29_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22083 h hv a31 u19_111 u16_117
  have u30_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1349 h a304 u23_174 u25_230 u29_265 u18_299 hv u21_305
  have u31_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1305 h u30_302 hv
  have u32_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1449 h u30_302 hv
  have u33_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2365 h hv u31_87 a116
  have u34_122 : Q {0, 1, 2, 4} := by
    by_contra hv
    exact c31532 h h0 hv u33_125 u27_124 u15_127 u17_123 u20_126
  have u35_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c2001 h u34_122 u32_97 u26_99 hv
  have u36_94 : ¬ T {3, 5, 9} := by
    intro hv
    exact c1949 h u34_122 hv u16_117
  have u37_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1946 h u34_122 hv u5_118
  have u38_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7910 h hv n49 u36_94 u35_100
  have u39_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5005 h hv u37_93 u6_103 a116
  exact c32567 h h0 u12_43 u39_143 u38_164 a31 u13_38 u14_179 u24_189 u28_202

end BorsukNine.FiniteObstruction

end OAI
end

section
-- module Solutions.OAIQ058_BK.Borsuk_FiniteCases_Cases110
attribute [-instance] _root_.OAI.BorsukNine.sphereMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32570 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 6, 7} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n95 a116 n49 a304
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c31529 h h0 hv a116 n49 a304
  have u1_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u2_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c32569 h h0 hv n95 a116 n49 a304
  have u3_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25738 h hv u2_31 n95 u1_105
  have u4_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20838 h hv u2_31 n95 u1_105
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 a116 hv u0_311 u3_291
  exact c31604 h h0 u5_200 u3_291 u4_256 u0_311

theorem c32571_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a116 n49 a304
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u1_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u0_29 hv
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u3_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv n49 u2_112
  have u4_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u5_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u6_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u7_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u6_118
  have u8_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u5_99 u7_103
  have u9_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u9_109
  have u11_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u13_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u14_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv a116 u7_103
  have u15_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u13_105 u6_118
  have u16_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u13_105 u6_118
  have u17_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv n49 u13_105
  have u18_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u14_114
  have u19_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u14_114
  have u20_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u1_40 u14_114
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32457 h h0 hv u15_111
  have u22_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2509 h hv u11_90 u15_111
  have u23_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u16_117
  have u24_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2089 h hv u11_90 u16_117
  have u25_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u11_90 u19_107 u9_109
  have u26_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c31531 h h0 hv a116 n49 a304
  have u27_95 : T {3, 6, 7} := by
    by_contra hv
    exact c32570 h h0 hv a116 n49 a304
  have u28_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1951 h hv u27_95 a116
  have u29_125 : Q {0, 1, 2, 7} := by
    by_contra hv
    exact c31532 h h0 u28_122 hv u8_124 u26_127 u24_123 u22_126
  have u30_41 : T {1, 2, 7} := by
    by_contra hv
    exact c603 h u29_125 hv
  have u31_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c2365 h u29_125 hv a116
  have u32_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9647 h hv u30_41 u19_107
  have u33_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27159 h hv u0_29 u30_41
  have u34_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31443 h u32_177 u25_141 u0_29 hv u17_162 u18_198 u10_196
  have u35_265 : Q {2, 3, 4, 9} := by
    by_contra hv
    exact c1349 h a304 u20_174 u4_230 hv u23_299 u33_302 u21_305
  have u36_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c436 h u34_200 u25_141 u17_162 u32_177 hv u10_196 u18_198
  have u37_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c12975 h u34_200 hv u12_88 u27_95
  have u38_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c12977 h u34_200 hv u12_88 u27_95
  have u39_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12982 h u34_200 hv u31_87 u13_105
  have u40_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1042 h u35_265 hv
  have u41_57 : T {1, 5, 8} := by
    by_contra hv
    exact c22076 h u35_265 hv u2_112 u14_114
  have u42_82 : T {2, 6, 9} := by
    by_contra hv
    exact c11052 h u36_187 u37_47 hv
  have u43_61 : T {1, 6, 9} := by
    by_contra hv
    exact c11058 h u36_187 hv u38_68
  have u44_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c11133 h u36_187 u40_70 u42_82 hv
  have u45_46 : T {1, 3, 6} := by
    by_contra hv
    exact c11076 h u36_187 hv u37_47 n49
  have u46_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c1008 h hv u38_68
  have u47_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7837 h hv u41_57 u11_90
  have u48_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8289 h hv u45_46 u39_51 u43_61
  have u49_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7441 h hv u45_46 u39_51 u43_61
  have u50_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c1248 h hv u44_84
  exact c184 h u29_125 u46_152 u3_157 u49_161 u47_164 u48_167 u50_168

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32571_oai := @OAI.BorsukNine.FiniteObstruction.c32571_oai
