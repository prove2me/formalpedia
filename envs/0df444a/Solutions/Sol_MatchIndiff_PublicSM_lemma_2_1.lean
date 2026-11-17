-- Prove2me | solution 1 for MatchIndiff.PublicSM.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-16T20:47:21.333052+00:00
-- url     : https://prove2.me/submissions/f4bdf8d5-6332-4c82-8de8-11fa22beff0a

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Protocol

open MatchIndiff MatchIndiff.PublicSM

namespace P2MHole01_644052ad
universe u_4 u_3 u_2 u_1
theorem solution {V : Type u_1} {R : V → Type u_2} {X : V → Type u_3} {C : Type u_4}
  (p : VerifProtocol R X C) (T : (v : V) → Set (R v)) (c : C) :
  {Q : (v : V) → R v | (∀ (v : V), Q v ∈ T v) ∧ ∀ (v : V), p.chk v (Q v) c = true} ⊆
    Set.univ.pi fun (v : V) => {x : R v | x ∈ T v ∧ p.chk v x c = true} := by
  intro Q hQ
  rw [Set.mem_univ_pi]
  exact fun v => ⟨hQ.1 v, hQ.2 v⟩
end P2MHole01_644052ad

/-- The set of accepted profiles (left side) is contained in the product of the fibres. -/
theorem sub_left_to_right {V : Type*} {R X : V → Type*} {C : Type*} (p : VerifProtocol R X C)
    (T : (v : V) → Set (R v)) (c : C) :
    {Q : (v : V) → R v | (∀ v, Q v ∈ T v) ∧ ∀ v, p.chk v (Q v) c = true} ⊆
        Set.pi Set.univ (fun v => {x : R v | x ∈ T v ∧ p.chk v x c = true}) := by
  (first | exact P2MHole01_644052ad.solution p T c | (apply P2MHole01_644052ad.solution <;> assumption))

namespace P2MHole02_178b1dbb
universe u_4 u_3 u_2 u_1
theorem solution {V : Type u_1} {R : V → Type u_2} {X : V → Type u_3} {C : Type u_4}
  (p : VerifProtocol R X C) (T : (v : V) → Set (R v)) (c : C) :
  (Set.univ.pi fun (v : V) => {x : R v | x ∈ T v ∧ p.chk v x c = true}) ⊆
    {Q : (v : V) → R v | (∀ (v : V), Q v ∈ T v) ∧ ∀ (v : V), p.chk v (Q v) c = true} := by
  intro Q hQ
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq] at hQ ⊢
  exact ⟨fun v => (hQ v).1, fun v => (hQ v).2⟩
end P2MHole02_178b1dbb

/-- The product of the fibres is contained in the set of accepted profiles (right side). -/
theorem sub_right_to_left {V : Type*} {R X : V → Type*} {C : Type*} (p : VerifProtocol R X C)
    (T : (v : V) → Set (R v)) (c : C) :
    Set.pi Set.univ (fun v => {x : R v | x ∈ T v ∧ p.chk v x c = true}) ⊆
        {Q : (v : V) → R v | (∀ v, Q v ∈ T v) ∧ ∀ v, p.chk v (Q v) c = true} := by
  (first | exact P2MHole02_178b1dbb.solution p T c | (apply P2MHole02_178b1dbb.solution <;> assumption))

/-- Lemma 2.1 (p. 7): for a fixed board `c`, the profiles of the product domain `∏ T_v` on which
all checks accept `c` form exactly `∏_v S_v(c)`, `S_v(c) = {x ∈ T_v : V_v(x, c) = 1}`; and a fixed
row and board give the same decoded component. -/
theorem solution {V : Type*} {R X : V → Type*} {C : Type*} (p : VerifProtocol R X C)
    (T : (v : V) → Set (R v)) (c : C) :
    {P : (v : V) → R v | (∀ v, P v ∈ T v) ∧ ∀ v, p.chk v (P v) c = true} =
        Set.pi Set.univ (fun v => {x : R v | x ∈ T v ∧ p.chk v x c = true}) ∧
      ∀ (P P' : (v : V) → R v) (v : V), P v = P' v → p.dec v (P v) c = p.dec v (P' v) c := by
  have heq : {P : (v : V) → R v | (∀ v, P v ∈ T v) ∧ ∀ v, p.chk v (P v) c = true} =
      Set.pi Set.univ (fun v => {x : R v | x ∈ T v ∧ p.chk v x c = true}) :=
    Set.Subset.antisymm (sub_left_to_right p T c) (sub_right_to_left p T c)
  exact ⟨heq, fun P P' v h => congrArg (fun x => p.dec v x c) h⟩
