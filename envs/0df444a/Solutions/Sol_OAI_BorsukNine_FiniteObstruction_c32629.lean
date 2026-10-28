-- Prove2me | solution 1 for OAI.BorsukNine.FiniteObstruction.c32629
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:21:53.745666+00:00
-- url     : https://prove2.me/submissions/6435027b-5b90-4c7a-8205-9d5123c0fbb7

import Mathlib
import Definitions.Def_OAIQ058B000
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

theorem c18 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 1, 3} → False := by
  intro a121 n2
  exact n2 (h.down {0, 1, 2, 3} {0, 1, 3} a121 (by decide) (by decide))

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

theorem c673 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 3, 5} → False := by
  intro a233 n45
  exact n45 (h.down {1, 3, 5, 8} {1, 3, 5} a233 (by decide) (by decide))

theorem c714 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 3, 8} → False := by
  intro a233 n48
  exact n48 (h.down {1, 3, 5, 8} {1, 3, 8} a233 (by decide) (by decide))

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

theorem c847 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 5, 8} → False := by
  intro a233 n57
  exact n57 (h.down {1, 3, 5, 8} {1, 5, 8} a233 (by decide) (by decide))

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

theorem c1067 (h : TenSystem T Q) :
    T {2, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a72 n156 n212 n262 n276 n280 n281 n282
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 6} a72
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n280 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 6} = {2, 4, 6, 7} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

theorem c1077 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a280 n156 n212 n262 n276 n281 n282
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {2, 4, 6} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

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

theorem c1818 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 9} → ¬ T {5, 6, 8} → False := by
  intro a121 n109 n112
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n109 (hc.mpr n112)

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

theorem c6727 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 3, 5} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a156 a45 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 6} {1, 3} {5, 8, 9} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

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

theorem c14267 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {5, 6, 8} → False := by
  intro a210 a24 a112
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a112

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

theorem c17485 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 6} → T {4, 7, 9} → False := by
  intro a233 a12 a109
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 6} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a12 a109

theorem c17493 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {2, 6, 9} → False := by
  intro a233 a24 a82
  have hc := h.complementary {1, 3, 5, 8} {0, 4, 7} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a82

theorem c17552 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 9} → False := by
  intro a233 n12 n72 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {2, 6} {0, 4, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) ht)

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

theorem c24405 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 8} → False := by
  intro a282 a2 a45 a48
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {1, 3} {0, 5, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)

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

theorem c31204 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 1, 3} → False := by
  classical
  intro n2
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c18 h u0_121 n2

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

theorem c31226 (h : TenSystem T Q) :
    ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → ¬ Q {0, 2, 4, 6} → T {2, 4, 6} →
      ¬ Q {2, 4, 5, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → False := by
  classical
  intro n281 n282 n156 a72 n276 n212 n262
  have u0_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c1067 h a72 n156 n212 n262 n276 hv n281 n282
  exact c1077 h u0_280 n156 n212 n262 n276 n281 n282

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

theorem c31643 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 9} → ¬ T {5, 6, 8} → False := by
  classical
  intro n109 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1818 h u0_121 n109 n112

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

theorem c32176 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 6} → T {1, 3, 8} → T {1, 3, 9} → False := by
  classical
  intro a276 a48 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23567 h a276 u0_2 a48 a49

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

theorem c32225 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 8} → T {1, 3, 5} → T {1, 3, 9} → False := by
  classical
  intro a281 a45 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24265 h a281 u0_2 a45 a49

theorem c32235 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 9} → T {1, 3, 5} → T {1, 3, 8} → False := by
  classical
  intro a282 a45 a48
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24405 h a282 u0_2 a45 a48

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

theorem c32629_oai (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {0, 5, 8} → T {5, 8, 9} → ¬ Q {1, 2, 4, 6} → T {1, 3, 9} → False := by
  classical
  intro a233 a24 a29 a116 n212 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c14267 h u0_210 a24 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u1_112
  have u3_45 : T {1, 3, 5} := by
    by_contra hv
    exact c673 h a233 hv
  have u4_48 : T {1, 3, 8} := by
    by_contra hv
    exact c714 h a233 hv
  have u5_57 : T {1, 5, 8} := by
    by_contra hv
    exact c847 h a233 hv
  have u6_82 : ¬ T {2, 6, 9} := by
    intro hv
    exact c17493 h a233 a24 hv
  have u7_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17485 h a233 hv u2_109
  have u8_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c32225 h h0 hv u3_45 a49
  have u9_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6727 h hv u3_45 u4_48 a49
  have u10_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c32235 h h0 hv u3_45 u4_48
  have u11_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c32176 h h0 hv u4_48 a49
  have u12_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21645 h hv a29 u5_57 a116
  have u13_72 : T {2, 4, 6} := by
    by_contra hv
    exact c17552 h a233 u7_12 hv u6_82
  exact c31226 h u8_281 u10_282 u9_156 u13_72 u11_276 n212 u12_262

end BorsukNine.FiniteObstruction

end OAI
end

theorem solution : type_of% @OAI.BorsukNine.FiniteObstruction.c32629_oai := @OAI.BorsukNine.FiniteObstruction.c32629_oai
