-- Prove2me | solution 1 for GlobalTheory.DualTransfer.mem_of_double_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:40.809598+00:00
-- url     : https://prove2.me/submissions/5b8c88db-a574-4b85-832f-ae7af1eb3f40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality
import Theorems.Thm_GlobalTheory_DualTransfer_exists_separating
import Theorems.Thm_GlobalTheory_DualTransfer_finite_quot
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_nsmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer
namespace GlobalTheory.DualTransfer
theorem _root_.solution : ∀ {G : Type} [AddCommGroup G] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (X Y L₀ L₀' L : AddSubgroup G), L₀ ≤ X → L₀' ≤ Y → L ≤ X → (∀ u ∈ L₀, ∀ y ∈ L₀', χ u y = 1) → (∀ x ∈ X, (∀ y ∈ L₀', χ x y = 1) → x ∈ L₀) → (∀ y ∈ Y, (∀ u ∈ L₀, χ u y = 1) → y ∈ L₀') → (∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) → (∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y) → (∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀', ∃ r ∈ R, ∃ u ∈ L₀', t = r + k • u) → ∀ N : ℕ, 0 < N → (∀ u ∈ L₀, N • u ∈ L) → (∀ u ∈ L, N • u ∈ L₀) → ∀ x ∈ X, N • x ∈ L₀ → (∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → χ x y = 1) → x ∈ L := by
  intro G _ χ hχ X Y L₀ L₀' L hL₀ hL₀' hL hortho hX hY dX dY tf fin0 fin0' N hN hNL hLN x hx hNx hxY
  by_contra hxL
  set P : AddSubgroup G := X ⊓ L₀.comap (nsmulAddMonoidHom N) with hP
  set Q : AddSubgroup G := Y ⊓ L₀'.comap (nsmulAddMonoidHom N) with hQ
  have memP : ∀ t, t ∈ P ↔ t ∈ X ∧ N • t ∈ L₀ := fun t => Iff.rfl
  have memQ : ∀ t, t ∈ Q ↔ t ∈ Y ∧ N • t ∈ L₀' := fun t => Iff.rfl
  set M := (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf P with hM
  set K := (L₀'.map (nsmulAddMonoidHom N)).addSubgroupOf Q with hK
  have fM : Finite (P ⧸ M) :=
    finite_quot P L₀ N hN (tf N hN) (fun t ht => ((memP t).mp ht).2) fin0
  have fK : Finite (Q ⧸ K) :=
    finite_quot Q L₀' N hN (tf N hN) (fun t ht => ((memQ t).mp ht).2) fin0'
  have memM : ∀ a : P, a ∈ M ↔ ∃ u ∈ L₀, N • u = (a : G) := by
    intro a
    simp only [M, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, nsmulAddMonoidHom_apply]
  have memK : ∀ b : Q, b ∈ K ↔ ∃ v ∈ L₀', N • v = (b : G) := by
    intro b
    simp only [K, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, nsmulAddMonoidHom_apply]
  have eM : ∀ a : P, a ∈ M ↔ ∀ b : Q, χ a b = 1 := by
    intro a
    rw [memM]
    constructor
    · rintro ⟨u, hu, hua⟩ b
      rw [← hua, hχ.nsmul]
      exact hortho u hu _ ((memQ b).mp b.2).2
    · intro h
      obtain ⟨x', hx'X, hx'a⟩ := dX N hN a ((memP a).mp a.2).1
      refine ⟨x', hX x' hx'X (fun y hy => ?_), hx'a⟩
      obtain ⟨y', hy'Y, hy'y⟩ := dY N hN y (hL₀' hy)
      have hy'Q : y' ∈ Q := (memQ y').mpr ⟨hy'Y, hy'y ▸ hy⟩
      rw [← hy'y, ← hχ.nsmul, hx'a]
      exact h ⟨y', hy'Q⟩
  have eK : ∀ b : Q, b ∈ K ↔ ∀ a : P, χ a b = 1 := by
    intro b
    rw [memK]
    constructor
    · rintro ⟨v, hv, hvb⟩ a
      rw [← hvb, ← hχ.nsmul]
      exact hortho _ ((memP a).mp a.2).2 v hv
    · intro h
      obtain ⟨y', hy'Y, hy'b⟩ := dY N hN b ((memQ b).mp b.2).1
      refine ⟨y', hY y' hy'Y (fun u hu => ?_), hy'b⟩
      obtain ⟨x', hx'X, hx'u⟩ := dX N hN u (hL₀ hu)
      have hx'P : x' ∈ P := (memP x').mpr ⟨hx'X, hx'u ▸ hu⟩
      rw [← hx'u, hχ.nsmul, hy'b]
      exact h ⟨x', hx'P⟩
  have hMH : M ≤ L.addSubgroupOf P := by
    intro a ha
    obtain ⟨u, hu, hua⟩ := (memM a).mp ha
    rw [AddSubgroup.mem_addSubgroupOf, ← hua]
    exact hNL u hu
  have hxP : x ∈ P := (memP x).mpr ⟨hx, hNx⟩
  have hxH : (⟨x, hxP⟩ : P) ∉ L.addSubgroupOf P := by
    rw [AddSubgroup.mem_addSubgroupOf]
    exact hxL
  obtain ⟨b, hb1, hb2⟩ := exists_separating (fun (a : P) (b : Q) => χ a b)
    (fun a a' b => hχ.left a a' b) (fun a b b' => hχ.right a b b')
    (fun b => hχ.zero_left b) (fun a => hχ.zero_right a) M K eM eK
    (L.addSubgroupOf P) hMH ⟨x, hxP⟩ hxH
  apply hb2
  refine hxY b ((memQ b).mp b.2).1 (fun u hu => ?_)
  have huP : u ∈ P := (memP u).mpr ⟨hL hu, hLN u hu⟩
  exact hb1 ⟨u, huP⟩ ((AddSubgroup.mem_addSubgroupOf).mpr hu)
end GlobalTheory.DualTransfer
