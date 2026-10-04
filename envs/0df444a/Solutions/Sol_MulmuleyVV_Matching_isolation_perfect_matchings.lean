-- Prove2me | solution 1 for MulmuleyVV.Matching.isolation_perfect_matchings
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:54:03.600315+00:00
-- url     : https://prove2.me/submissions/011a731a-7ae6-4121-ac9b-2e9231581458

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

set_option autoImplicit false

namespace P5c05fc80

open MulmuleyVV.Matching

/-- `e` is ambiguous for `w`: some minimum-weight set contains `e` and another omits it. -/
def Amb {α : Type*} (F : Finset (Finset α)) (w : α → ℕ) (e : α) : Prop :=
  ∃ S ∈ F, ∃ T ∈ F, e ∈ S ∧ e ∉ T ∧ (∀ U ∈ F, setWeight w S ≤ setWeight w U) ∧
    (∀ U ∈ F, setWeight w T ≤ setWeight w U)

lemma exists_amb {α : Type*} (F : Finset (Finset α)) (hF : F.Nonempty) (w : α → ℕ)
    (h : ¬ HasUniqueMin F w) : ∃ e, Amb F w e := by
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image F (setWeight w) hF
  have : ∃ T ∈ F, T ≠ S ∧ setWeight w T ≤ setWeight w S := by
    by_contra hc
    push Not at hc
    exact h ⟨S, hS, fun T hT hTS => hc T hT hTS⟩
  obtain ⟨T, hT, hTS, hle⟩ := this
  have hTmin : ∀ U ∈ F, setWeight w T ≤ setWeight w U :=
    fun U hU => le_trans hle (hmin U hU)
  have : ∃ e, (e ∈ S ∧ e ∉ T) ∨ (e ∈ T ∧ e ∉ S) := by
    by_contra hc
    apply hTS
    ext x
    constructor
    · intro hx
      by_contra hxS
      exact hc ⟨x, Or.inr ⟨hx, hxS⟩⟩
    · intro hx
      by_contra hxT
      exact hc ⟨x, Or.inl ⟨hx, hxT⟩⟩
  obtain ⟨e, he | he⟩ := this
  · exact ⟨e, S, hS, T, hT, he.1, he.2, hmin, hTmin⟩
  · exact ⟨e, T, hT, S, hS, he.1, he.2, hTmin, hmin⟩

lemma weight_not_mem {α : Type*} [DecidableEq α] (w w' : α → ℕ) (e : α)
    (hag : ∀ x, x ≠ e → w x = w' x) (U : Finset α) (he : e ∉ U) :
    setWeight w U = setWeight w' U := by
  unfold setWeight
  refine Finset.sum_congr rfl fun x hx => hag x ?_
  rintro rfl
  exact he hx

lemma weight_mem {α : Type*} [DecidableEq α] (w w' : α → ℕ) (e : α)
    (hag : ∀ x, x ≠ e → w x = w' x) (U : Finset α) (he : e ∈ U) :
    setWeight w U + w' e = setWeight w' U + w e := by
  unfold setWeight
  rw [← Finset.add_sum_erase U w he, ← Finset.add_sum_erase U w' he]
  have : ∑ x ∈ U.erase e, w x = ∑ x ∈ U.erase e, w' x :=
    Finset.sum_congr rfl fun x hx => hag x (Finset.ne_of_mem_erase hx)
  rw [this]
  ring

lemma amb_le {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (w w' : α → ℕ) (e : α)
    (hag : ∀ x, x ≠ e → w x = w' x) (hw : Amb F w e) (hw' : Amb F w' e) :
    w e ≤ w' e := by
  obtain ⟨S, hS, T, hT, heS, heT, hSmin, hTmin⟩ := hw
  obtain ⟨S', hS', T', hT', heS', heT', hSmin', hTmin'⟩ := hw'
  have h1 := hTmin T' hT'
  have h2 := hTmin' T hT
  have e1 := weight_not_mem w w' e hag T heT
  have e2 := weight_not_mem w w' e hag T' heT'
  have h3 := hSmin T hT
  have h4 := hTmin S hS
  have h5 := hTmin' S hS
  have e3 := weight_mem w w' e hag S heS
  omega

lemma amb_inj {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (w w' : α → ℕ) (e : α)
    (hw : Amb F w e) (hw' : Amb F w' e)
    (h : Function.update w e 1 = Function.update w' e 1) : w = w' := by
  have hag : ∀ x, x ≠ e → w x = w' x := by
    intro x hx
    have := congrFun h x
    simpa [Function.update_of_ne hx] using this
  have hag' : ∀ x, x ≠ e → w' x = w x := fun x hx => (hag x hx).symm
  have := le_antisymm (amb_le F w w' e hag hw hw') (amb_le F w' w e hag' hw' hw)
  funext x
  by_cases hx : x = e
  · subst hx; exact this
  · exact hag x hx

lemma card_slice {α : Type*} [Fintype α] [DecidableEq α] (N : ℕ) (e : α) :
    (Fintype.piFinset (Function.update (fun _ : α => Finset.Icc 1 N) e {1})).card
      = N ^ (Fintype.card α - 1) := by
  rw [Fintype.card_piFinset]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  simp only [Function.update_self, Finset.card_singleton, one_mul]
  rw [Finset.prod_congr rfl (g := fun _ => N)]
  · rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ]
  · intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    simp

open Classical in
lemma card_amb {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Finset α)) (N : ℕ) (e : α) :
    ((Fintype.piFinset fun _ : α => Finset.Icc 1 N).filter (fun w => Amb F w e)).card
      ≤ N ^ (Fintype.card α - 1) := by
  rw [← card_slice N e]
  apply Finset.card_le_card_of_injOn (fun w => Function.update w e 1)
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset] at hw
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro a
    by_cases ha : a = e
    · subst ha; simp
    · rw [Function.update_of_ne ha, Function.update_of_ne ha]
      exact hw.1 a
  · intro w hw w' hw' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hw hw'
    exact amb_inj F w w' e hw.2 hw'.2 h

open Classical in
theorem lemma1 {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (hF : F.Nonempty) :
    (2 * Fintype.card α) ^ Fintype.card α ≤
      2 * ((Fintype.piFinset fun _ : α => Finset.Icc 1 (2 * Fintype.card α)).filter
        (fun w => HasUniqueMin F w)).card := by
  set n := Fintype.card α with hn
  set N := 2 * n with hN
  set P := Fintype.piFinset fun _ : α => Finset.Icc 1 N with hP
  have htot : P.card = N ^ n := by
    rw [hP, Fintype.card_piFinset]
    simp [Nat.card_Icc, Finset.prod_const, Finset.card_univ, hn]
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (p := fun w => HasUniqueMin F w)
  have hbad : (P.filter (fun w => ¬ HasUniqueMin F w)).card ≤ n * N ^ (n - 1) := by
    have hsub : P.filter (fun w => ¬ HasUniqueMin F w) ⊆
        Finset.univ.biUnion (fun e => P.filter (fun w => P5c05fc80.Amb F w e)) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨e, he⟩ := P5c05fc80.exists_amb F hF w hw.2
      rw [Finset.mem_biUnion]
      exact ⟨e, Finset.mem_univ e, Finset.mem_filter.2 ⟨hw.1, he⟩⟩
    calc (P.filter (fun w => ¬ HasUniqueMin F w)).card
        ≤ (Finset.univ.biUnion (fun e => P.filter (fun w => P5c05fc80.Amb F w e))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ e, (P.filter (fun w => P5c05fc80.Amb F w e)).card := Finset.card_biUnion_le
      _ ≤ ∑ _e : α, N ^ (n - 1) := Finset.sum_le_sum fun e _ => P5c05fc80.card_amb F N e
      _ = n * N ^ (n - 1) := by simp [Finset.sum_const, Finset.card_univ, hn]
  have hkey : 2 * (n * N ^ (n - 1)) ≤ N ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ, hN, hk]
      apply le_of_eq
      ring
  generalize N ^ n = M at htot hkey
  generalize n * N ^ (n - 1) = B at hbad hkey
  omega

end P5c05fc80

open Classical MulmuleyVV.Matching in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∃ M : Finset G.edgeSet, IsPerfectMatchingEdges G M) :
    (2 * Fintype.card G.edgeSet) ^ Fintype.card G.edgeSet ≤
      2 * ((Fintype.piFinset fun _ : G.edgeSet => Finset.Icc 1 (2 * Fintype.card G.edgeSet)).filter
        (fun w => HasUniqueMin (perfectMatchings G) w)).card := by
  have hne : (perfectMatchings G).Nonempty := by
    obtain ⟨M, hM⟩ := hG
    refine ⟨M, ?_⟩
    unfold perfectMatchings
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hM
  exact P5c05fc80.lemma1 (perfectMatchings G) hne
