-- Prove2me | solution 1 for OAI.MatchingSmoothing.simultaneous_sign_eigenvector_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:30.94293+00:00
-- url     : https://prove2.me/submissions/0f7bd98a-453d-4bf0-a413-0f57e9c7ea4a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Involutions.lean:L79-L107
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.simultaneous_sign_eigenvector_preserving. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD

-- ---- from OAI.Combinatorics.MatchingPSD.Involutions ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

section CommutingInvolutions

variable {ι : Type u_1} {V : Type u_2} [AddCommGroup V] [Module ℝ V]

lemma eigen_add_commuting (A B : Module.End ℝ V) (hAB : Commute A B)
    (v : V) (c : ℝ) (hv : A v = c • v) :
    A (v + B v) = c • (v + B v) := by
  have hc : A (B v) = B (A v) := congrArg (fun f : Module.End ℝ V => f v) hAB.eq
  rw [map_add, hv, hc, hv, map_smul, smul_add]

lemma eigen_sub_commuting (A B : Module.End ℝ V) (hAB : Commute A B)
    (v : V) (c : ℝ) (hv : A v = c • v) :
    A (v - B v) = c • (v - B v) := by
  have hc : A (B v) = B (A v) := congrArg (fun f : Module.End ℝ V => f v) hAB.eq
  rw [map_sub, hv, hc, hv, map_smul, smul_sub]

lemma simultaneous_sign_eigenvector_on (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) (s : Finset ι) :
    ∃ (χ : ι → ℝ) (v : V), v ∈ W ∧ v ≠ 0 ∧
      ∀ i ∈ s, (χ i = 1 ∨ χ i = -1) ∧ A i v = χ i • v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv, hv0⟩ := hne
    exact ⟨fun _ => 1, v, hv, hv0, by simp⟩
  | @insert i s his ih =>
    obtain ⟨χ, v, hv, hv0, heig⟩ := ih
    by_cases hp : v + A i v = 0
    · have hm : v - A i v ≠ 0 := by
        intro hm
        have htwo : (2 : ℝ) • v = 0 := by
          rw [two_smul]
          linear_combination (norm := abel) hp + hm
        exact hv0 ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
      refine ⟨Function.update χ i (-1), v - A i v,
        W.sub_mem hv (hstable i v hv), hm, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self, neg_smul, one_smul]
        refine ⟨by simp, ?_⟩
        rw [map_sub, hinv]
        abel
      · have hji : j ≠ i := by intro h; subst j; exact his hj
        rw [Function.update_of_ne hji]
        exact ⟨(heig j hj).1, eigen_sub_commuting (A j) (A i) (hcomm j i)
          v (χ j) (heig j hj).2⟩
    · refine ⟨Function.update χ i 1, v + A i v,
        W.add_mem hv (hstable i v hv), hp, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self, one_smul]
        refine ⟨by simp, ?_⟩
        rw [map_add, hinv, add_comm]
      · have hji : j ≠ i := by intro h; subst j; exact his hj
        rw [Function.update_of_ne hji]
        exact ⟨(heig j hj).1, eigen_add_commuting (A j) (A i) (hcomm j i)
          v (χ j) (heig j hj).2⟩

lemma simultaneous_sign_eigenvector [Fintype ι] (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) :
    ∃ (χ : ι → ℝ) (v : V), v ∈ W ∧ v ≠ 0 ∧
      ∀ i, (χ i = 1 ∨ χ i = -1) ∧ A i v = χ i • v := by
  simpa using simultaneous_sign_eigenvector_on A hcomm hinv W hstable hne Finset.univ

lemma simultaneous_sign_eigenvector_preserving [Fintype ι]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (s : Finset ι) (χ : ι → ℝ)
    (v : V) (hv : v ∈ W) (hv0 : v ≠ 0) (he : ∀ i ∈ s, A i v = χ i • v) :
    ∃ (ψ : ι → ℝ) (w : V), w ∈ W ∧ w ≠ 0 ∧
      (∀ i, (ψ i = 1 ∨ ψ i = -1) ∧ A i w = ψ i • w) ∧
      ∀ i ∈ s, ψ i = χ i := by
  let U : Submodule ℝ V :=
    { carrier := {w | w ∈ W ∧ ∀ i ∈ s, A i w = χ i • w}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha, hea⟩ ⟨hb, heb⟩
        exact ⟨W.add_mem ha hb, fun i hi => by rw [map_add, hea i hi, heb i hi, smul_add]⟩
      smul_mem' := by
        rintro c a ⟨ha, hea⟩
        exact ⟨W.smul_mem c ha, fun i hi => by rw [map_smul, hea i hi, smul_comm]⟩ }
  have hU (j : ι) (w : V) (hw : w ∈ U) : A j w ∈ U := by
    refine ⟨hstable j w hw.1, ?_⟩
    intro i hi
    have hc := congrArg (fun f : Module.End ℝ V => f w) (hcomm i j).eq
    change A i (A j w) = A j (A i w) at hc
    rw [hc, hw.2 i hi, map_smul]
  obtain ⟨ψ, w, hw, hw0, hew⟩ := simultaneous_sign_eigenvector A hcomm hinv U hU
    ⟨v, ⟨hv, he⟩, hv0⟩
  refine ⟨ψ, w, hw.1, hw0, hew, ?_⟩
  intro i hi
  exact smul_left_injective ℝ hw0 ((hew i).2.symm.trans (hw.2 i hi))

end CommutingInvolutions
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.simultaneous_sign_eigenvector_preserving := @_root_.OAI.MatchingSmoothing.simultaneous_sign_eigenvector_preserving
