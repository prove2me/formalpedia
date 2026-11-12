-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:51.437409+00:00
-- url     : https://prove2.me/submissions/1cf241e3-eca1-4a4d-ad19-0593f7cb942e

import Mathlib
import Definitions.Def_Q238L009
import Definitions.Def_Q238L010
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_boundedRationalDecide_correct_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReverseRow
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma reverseRow_holds {n : ℕ} (q : Row n) (x : Fin n → ℝ) :
    (reverseRow q).RealHolds x ↔ (q.bound:ℝ)≤q.realValue x := by
  simp [reverseRow,Row.RealHolds,Row.realValue,Finset.sum_neg_distrib]

lemma faceRows_holds {n : ℕ} (rows picked : List (Row n)) (x : Fin n → ℝ) :
    (∀ q∈faceRows rows picked, q.RealHolds x) ↔
      (∀ q∈rows, q.RealHolds x) ∧ (∀ q∈picked, q.realValue x=(q.bound:ℝ)) := by
  constructor
  · intro h
    refine ⟨fun q hq => h q (List.mem_append_left _ (List.mem_append_left _ hq)),?_⟩
    intro q hq
    have hp := h q (List.mem_append_left _ (List.mem_append_right _ hq))
    have hm := h (reverseRow q) (List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    exact le_antisymm hp ((reverseRow_holds _ _).mp hm)
  · rintro ⟨ha,hp⟩ q hq
    rcases List.mem_append.mp hq with hq|hq
    · rcases List.mem_append.mp hq with hq|hq
      · exact ha q hq
      · exact (hp q hq).le
    · obtain ⟨p,hp0,he⟩ := List.mem_map.mp hq
      subst q
      exact (reverseRow_holds _ _).mpr (hp p hp0).ge

lemma decide_face {n : ℕ} (rows picked : List (Row n)) (B : ℕ) :
    boundedRationalDecide (faceRows rows picked) B=true ↔ ∃ x, Face rows picked B x := by
  rw [boundedRationalDecide_correct_s238r]
  apply exists_congr
  intro x
  rw [faceRows_holds]
  exact and_assoc

lemma Face.of_subset {n : ℕ} {rows picked more : List (Row n)} {B : ℕ} {x : Fin n → ℝ}
    (hx : Face rows more B x) (hp : picked ⊆ more) : Face rows picked B x :=
  ⟨hx.1,fun q hq => hx.2.1 q (hp hq),hx.2.2⟩

lemma Face.cons {n : ℕ} {rows picked : List (Row n)} {B : ℕ} {x : Fin n → ℝ}
    (hx : Face rows picked B x) (q : Row n) (hq : q.realValue x=(q.bound:ℝ)) :
    Face rows (q::picked) B x := by
  refine ⟨hx.1,?_,hx.2.2⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl|hp
  · exact hq
  · exact hx.2.1 p hp

lemma selectFace_spec_s238r_oai {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (todo picked : List (Row n)) (hfeas : ∃ x, Face rows picked B x) :
    picked ⊆ selectFace rows B todo picked ∧
    (∃ x, Face rows (selectFace rows B todo picked) B x) ∧
    (∀ x, Face rows (selectFace rows B todo picked) B x → ∀ q∈todo,
      q.realValue x=(q.bound:ℝ) → q∈selectFace rows B todo picked) := by
  induction todo generalizing picked with
  | nil => exact ⟨List.Subset.refl _,hfeas,by simp⟩
  | cons q todo ih =>
    unfold selectFace
    by_cases hd : boundedRationalDecide (faceRows rows (q::picked)) B=true
    · rw [ite_eq_left hd]
      obtain ⟨hs,hf,ha⟩ := ih (q::picked) ((decide_face _ _ _).mp hd)
      refine ⟨List.Subset.trans (List.subset_cons_self q picked) hs,hf,?_⟩
      intro x hx r hr he
      rcases List.mem_cons.mp hr with rfl|hr
      · exact hs (List.mem_cons_self)
      · exact ha x hx r hr he
    · rw [ite_eq_right hd]
      obtain ⟨hs,hf,ha⟩ := ih picked hfeas
      refine ⟨hs,hf,?_⟩
      intro x hx r hr he
      rcases List.mem_cons.mp hr with rfl|hr
      · exact (hd ((decide_face _ _ _).mpr ⟨x,(hx.of_subset hs).cons r he⟩)).elim
      · exact ha x hx r hr he

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r_oai := @OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r_oai
