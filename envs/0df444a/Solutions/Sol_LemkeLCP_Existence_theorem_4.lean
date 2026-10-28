-- Prove2me | solution 1 for LemkeLCP.Existence.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T02:13:20.147487+00:00
-- url     : https://prove2.me/submissions/b9e15d50-536e-4e7e-85bb-867c9eee4008

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting


/-!
# Brouwer library (staged build for 6f936c65)

Stage S1: Sperner's lemma on Kuhn's triangulation of the cube (door-to-door parity,
induction on the dimension) and Brouwer's fixed point theorem on the unit cube.

Everything here is free of Arrow-Debreu definitions.
-/

set_option autoImplicit false

universe u

namespace BrouwerLib

open Finset

/-! ## Parity of an involution -/

/-- An involution on a finite set has as many fixed points as the set has elements, mod 2. -/
theorem card_zmod_two_eq_card_fixed {α : Type u} [DecidableEq α] (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) :
    ((s.card : ℕ) : ZMod 2) = ((s.filter (fun a => g a = a)).card : ZMod 2) := by
  have h1 : ∑ a ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => g a) ?_ ?_ ?_ ?_
    · intro a _; decide
    · intro a ha _; exact (Finset.mem_filter.mp ha).2
    · intro a ha
      obtain ⟨has, hne⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨hmem a has, ?_⟩
      rw [hinv a has]; exact fun h => hne h.symm
    · intro a ha; exact hinv a (Finset.mem_filter.mp ha).1
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun a => g a = a)
  rw [← h2]
  push_cast
  have h3 : (((s.filter (fun a => ¬ g a = a)).card : ℕ) : ZMod 2)
      = ∑ a ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) := by simp
  rw [h3, h1, add_zero]

/-! ## Kuhn simplices -/

/-- Vertex `j` of the Kuhn simplex with base `v` and rank permutation `r`: coordinate `i` is
incremented at step `r i`, so vertex `j` is `v + ∑_{r i < j} e_i`. -/
def kvert {n : ℕ} (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)) (j : ℕ) : Fin n → ℕ :=
  fun i => v i + if ((r i : Fin n) : ℕ) < j then 1 else 0

/-- Door condition: the facet opposite vertex `k` carries every label `1, …, n`. -/
def Door {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (v : Fin n → ℕ) (r : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) : Prop :=
  ∀ c, 1 ≤ c → c ≤ n → ∃ j : Fin (n + 1), j ≠ k ∧ ℓ (kvert v r j) = c

/-- A completely labelled Kuhn simplex: its `n + 1` vertices carry all labels `0, …, n`. -/
def FullyLabelled {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ c, c ≤ n → ∃ j : Fin (n + 1), ℓ (kvert v r j) = c

/-- The base points of the Kuhn simplices of the grid `{0, …, p}^n`. -/
def kgrid (n p : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ : Fin n => Finset.range p

theorem mem_kgrid {n p : ℕ} (v : Fin n → ℕ) : v ∈ kgrid n p ↔ ∀ i, v i < p := by
  simp [kgrid, Fintype.mem_piFinset]

/-- On a door, the labels of the other `n` vertices are exactly `1, …, n`. -/
theorem door_image {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) :
    ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))) = Finset.Icc 1 n := by
  apply Finset.eq_of_superset_of_card_ge
  · intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hc
    obtain ⟨j, hjk, hj⟩ := hd c h1 h2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, hj⟩
  · calc ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))).card
        ≤ (Finset.univ.erase k).card := Finset.card_image_le
      _ = n := by simp
      _ = (Finset.Icc 1 n).card := by simp

theorem door_label_pos {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) (j : Fin (n + 1)) (hj : j ≠ k) :
    1 ≤ ℓ (kvert v r j) := by
  have hmem : ℓ (kvert v r j) ∈
      ((Finset.univ.erase k).image (fun j : Fin (n + 1) => ℓ (kvert v r j))) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, rfl⟩
  rw [door_image hd] at hmem
  exact (Finset.mem_Icc.mp hmem).1

theorem door_inj {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v : Fin n → ℕ} {r : Equiv.Perm (Fin n)}
    {k : Fin (n + 1)} (hd : Door ℓ v r k) (j₁ j₂ : Fin (n + 1)) (h₁ : j₁ ≠ k) (h₂ : j₂ ≠ k)
    (h : ℓ (kvert v r j₁) = ℓ (kvert v r j₂)) : j₁ = j₂ := by
  have hinj : Set.InjOn (fun j : Fin (n + 1) => ℓ (kvert v r j)) (Finset.univ.erase k : Finset _) := by
    rw [← Finset.card_image_iff, door_image hd]
    simp
  exact hinj (by simpa using h₁) (by simpa using h₂) h

/-! ## Counting doors -/

section Counting

open scoped Classical

/-- The Kuhn simplices of the grid `{0, …, p}^n`, as (base, rank permutation). -/
noncomputable def ksimp (n p : ℕ) : Finset ((Fin n → ℕ) × Equiv.Perm (Fin n)) :=
  kgrid n p ×ˢ Finset.univ

/-- Pairs (simplex, vertex index) whose opposite facet is a door. -/
noncomputable def kdoors (n p : ℕ) (ℓ : (Fin n → ℕ) → ℕ) :
    Finset (((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) :=
  (ksimp n p ×ˢ Finset.univ).filter (fun x => Door ℓ x.1.1 x.1.2 x.2)

/-- The completely labelled Kuhn simplices. -/
noncomputable def kfull (n p : ℕ) (ℓ : (Fin n → ℕ) → ℕ) :
    Finset ((Fin n → ℕ) × Equiv.Perm (Fin n)) :=
  (ksimp n p).filter (fun σ => FullyLabelled ℓ σ.1 σ.2)

/-- Door-to-door inside a simplex: move to the other vertex carrying the same label. -/
noncomputable def gA {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) :
    ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1) :=
  if h : ∃ j : Fin (n + 1), j ≠ x.2 ∧ ℓ (kvert x.1.1 x.1.2 j) = ℓ (kvert x.1.1 x.1.2 x.2) ∧
      ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0 then (x.1, h.choose) else x

theorem gA_of_zero {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1))
    (h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0) : gA ℓ x = x := by
  unfold gA
  rw [dif_neg]
  rintro ⟨j, -, -, h⟩
  exact h h0

theorem gA_spec {n : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1))
    (hx : Door ℓ x.1.1 x.1.2 x.2) (hne : ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0) :
    (gA ℓ x).1 = x.1 ∧ (gA ℓ x).2 ≠ x.2 ∧
      ℓ (kvert x.1.1 x.1.2 (gA ℓ x).2) = ℓ (kvert x.1.1 x.1.2 x.2) := by
  have hex : ∃ j : Fin (n + 1), j ≠ x.2 ∧ ℓ (kvert x.1.1 x.1.2 j) = ℓ (kvert x.1.1 x.1.2 x.2) ∧
      ℓ (kvert x.1.1 x.1.2 x.2) ≠ 0 := by
    obtain ⟨j, hj, hj'⟩ := hx _ (Nat.one_le_iff_ne_zero.mpr hne) (hle _)
    exact ⟨j, hj, hj', hne⟩
  unfold gA
  rw [dif_pos hex]
  exact ⟨rfl, hex.choose_spec.1, hex.choose_spec.2.1⟩

theorem gA_mem {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ x ∈ kdoors n p ℓ := by
  by_cases h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0
  · rw [gA_of_zero ℓ x h0]; exact hx
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨e1, e2, e3⟩ := gA_spec ℓ hle x hd h0
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    rw [e1]; exact (Finset.mem_product.mp hxs).1
  · rw [e1]
    intro c hc1 hc2
    obtain ⟨j, hjk, hj⟩ := hd c hc1 hc2
    by_cases hj2 : j = (gA ℓ x).2
    · refine ⟨x.2, fun h => e2 h.symm, ?_⟩
      rw [← e3, ← hj2]; exact hj
    · exact ⟨j, hj2, hj⟩

theorem gA_inv {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ (gA ℓ x) = x := by
  by_cases h0 : ℓ (kvert x.1.1 x.1.2 x.2) = 0
  · rw [gA_of_zero ℓ x h0, gA_of_zero ℓ x h0]
  obtain ⟨-, hd⟩ := Finset.mem_filter.mp hx
  obtain ⟨e1, e2, e3⟩ := gA_spec ℓ hle x hd h0
  have hy := gA_mem ℓ hle x hx
  obtain ⟨-, hdy⟩ := Finset.mem_filter.mp hy
  have h0y : ℓ (kvert (gA ℓ x).1.1 (gA ℓ x).1.2 (gA ℓ x).2) ≠ 0 := by
    rw [e1, e3]; exact h0
  obtain ⟨f1, f2, f3⟩ := gA_spec ℓ hle (gA ℓ x) hdy h0y
  rw [e1] at hdy f3
  have key : (gA ℓ (gA ℓ x)).2 = x.2 := by
    apply door_inj hdy _ _ f2 (fun h => e2 h.symm)
    rw [f3]; exact e3
  exact Prod.ext (by rw [f1, e1]) key

theorem gA_fixed_iff {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (x : ((Fin n → ℕ) × Equiv.Perm (Fin n)) × Fin (n + 1)) (hx : x ∈ kdoors n p ℓ) :
    gA ℓ x = x ↔ ℓ (kvert x.1.1 x.1.2 x.2) = 0 := by
  constructor
  · intro h
    by_contra h0
    obtain ⟨-, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, e2, -⟩ := gA_spec ℓ hle x hd h0
    exact e2 (by rw [h])
  · exact gA_of_zero ℓ x

/-- Step A: the number of doors has the parity of the number of completely labelled simplices. -/
theorem stepA {n p : ℕ} (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n) :
    (((kdoors n p ℓ).card : ℕ) : ZMod 2) = ((kfull n p ℓ).card : ZMod 2) := by
  rw [card_zmod_two_eq_card_fixed (kdoors n p ℓ) (gA ℓ) (gA_mem ℓ hle) (gA_inv ℓ hle)]
  congr 1
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx1
    have h0 := (gA_fixed_iff ℓ hle x hx1).mp hx2
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hxs).1, ?_⟩
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · exact ⟨x.2, h0⟩
    · obtain ⟨j, -, hj⟩ := hd c hc0 hc
      exact ⟨j, hj⟩
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    obtain ⟨-, hdx⟩ := Finset.mem_filter.mp hx1
    have h0y := (gA_fixed_iff ℓ hle y hy1).mp hy2
    refine Prod.ext hxy ?_
    by_contra hne
    have := door_label_pos hdx y.2 (fun h => hne h.symm)
    rw [hxy, h0y] at this
    exact absurd this (by norm_num)
  · intro σ hσ
    obtain ⟨hσs, hfl⟩ := Finset.mem_filter.mp hσ
    obtain ⟨k, hk⟩ := hfl 0 (Nat.zero_le _)
    have hmem : (σ, k) ∈ kdoors n p ℓ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hσs, Finset.mem_univ _⟩, ?_⟩
      intro c hc1 hc2
      obtain ⟨j, hj⟩ := hfl c hc2
      refine ⟨j, ?_, hj⟩
      rintro rfl
      omega
    exact ⟨(σ, k), Finset.mem_filter.mpr ⟨hmem, gA_of_zero ℓ _ hk⟩, rfl⟩

/-! ## Door-to-door across facets -/

theorem door_transfer {n : ℕ} {ℓ : (Fin n → ℕ) → ℕ} {v v' : Fin n → ℕ}
    {r r' : Equiv.Perm (Fin n)} {k k' : Fin (n + 1)} (φ : Fin (n + 1) → Fin (n + 1))
    (hφ : ∀ j, j ≠ k → φ j ≠ k' ∧ kvert v' r' (φ j) = kvert v r j) (hd : Door ℓ v r k) :
    Door ℓ v' r' k' := by
  intro c h1 h2
  obtain ⟨j, hj, hjc⟩ := hd c h1 h2
  obtain ⟨ha, hb⟩ := hφ j hj
  exact ⟨φ j, ha, by rw [hb]; exact hjc⟩

theorem finRotate_symm_zero (m : ℕ) : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]


theorem val_ne_zero_of_ne {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) : (a : ℕ) ≠ 0 :=
  fun h' => h (Fin.ext (by rw [h', Fin.val_zero]))

theorem val_ne_of_ne_last {n : ℕ} {a : Fin (n + 1)} (h : a ≠ Fin.last n) : (a : ℕ) ≠ n :=
  fun h' => h (Fin.ext (by rw [h', Fin.val_last]))

theorem last_ne_zero' (m : ℕ) : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

theorem kvert_move_zero {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j ≤ m) :
    kvert (Function.update v (r.symm 0) (v (r.symm 0) + 1)) (r.trans (finRotate (m + 1)).symm) j
      = kvert v r (j + 1) := by
  funext i
  unfold kvert
  by_cases hi : i = r.symm 0
  · subst hi
    simp only [Function.update_self, Equiv.trans_apply, Equiv.apply_symm_apply,
      finRotate_symm_zero, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · rw [Function.update_of_ne hi, Equiv.trans_apply]
    have hr : r i ≠ 0 := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    rw [coe_finRotate_symm_of_ne_zero hr]
    have : ((r i : Fin (m + 1)) : ℕ) ≠ 0 := val_ne_zero_of_ne hr
    split_ifs <;> omega

theorem kvert_move_last {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1))) (j : ℕ)
    (hj : j ≤ m) (hv : 0 < v (r.symm (Fin.last m))) :
    kvert (Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1))
      (r.trans (finRotate (m + 1))) (j + 1) = kvert v r j := by
  funext i
  unfold kvert
  by_cases hi : i = r.symm (Fin.last m)
  · subst hi
    simp only [Function.update_self, Equiv.trans_apply, Equiv.apply_symm_apply,
      finRotate_last, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · rw [Function.update_of_ne hi, Equiv.trans_apply]
    have hr : r i ≠ Fin.last m := fun h => hi (by rw [← h, Equiv.symm_apply_apply])
    rw [coe_finRotate_of_ne_last hr]
    split_ifs <;> omega

theorem kvert_swap {m : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (m + 1)) (j : ℕ) (hj : j ≠ (k : ℕ)) :
    kvert v (r.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))) j = kvert v r j := by
  funext i
  unfold kvert
  rw [Equiv.trans_apply]
  have h1 : ((k.pred hk0 : Fin (m + 1)) : ℕ) = k - 1 := Fin.val_pred k hk0
  have h2 : ((k.castPred hkl : Fin (m + 1)) : ℕ) = k := Fin.coe_castPred k hkl
  have hkpos : (k : ℕ) ≠ 0 := val_ne_zero_of_ne hk0
  rcases eq_or_ne (r i) (k.pred hk0) with ha | ha
  · rw [ha, Equiv.swap_apply_left, h1, h2]
    split_ifs <;> omega
  · rcases eq_or_ne (r i) (k.castPred hkl) with hb | hb
    · rw [hb, Equiv.swap_apply_right, h1, h2]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Door-to-door across a facet of a Kuhn simplex (dimension `m + 1`). -/
noncomputable def gB {m : ℕ} (p : ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2)) :
    ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2) :=
  if hk0 : x.2 = 0 then
    (if x.1.1 (x.1.2.symm 0) + 1 < p then
      ((Function.update x.1.1 (x.1.2.symm 0) (x.1.1 (x.1.2.symm 0) + 1),
        x.1.2.trans (finRotate (m + 1)).symm), Fin.last (m + 1))
    else x)
  else if hkl : x.2 = Fin.last (m + 1) then
    (if 0 < x.1.1 (x.1.2.symm (Fin.last m)) then
      ((Function.update x.1.1 (x.1.2.symm (Fin.last m)) (x.1.1 (x.1.2.symm (Fin.last m)) - 1),
        x.1.2.trans (finRotate (m + 1))), 0)
    else x)
  else ((x.1.1, x.1.2.trans (Equiv.swap (x.2.pred hk0) (x.2.castPred hkl))), x.2)

theorem gB_zero_move {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : v (r.symm 0) + 1 < p) :
    gB p ((v, r), 0) = ((Function.update v (r.symm 0) (v (r.symm 0) + 1),
        r.trans (finRotate (m + 1)).symm), Fin.last (m + 1)) := by
  simp [gB, h]

theorem gB_zero_stay {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : ¬ v (r.symm 0) + 1 < p) : gB p ((v, r), 0) = ((v, r), 0) := by
  simp [gB, h]

theorem gB_last_move {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : 0 < v (r.symm (Fin.last m))) :
    gB p ((v, r), Fin.last (m + 1)) =
      ((Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1),
        r.trans (finRotate (m + 1))), 0) := by
  simp [gB, h, last_ne_zero' m]

theorem gB_last_stay {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (h : ¬ 0 < v (r.symm (Fin.last m))) :
    gB p ((v, r), Fin.last (m + 1)) = ((v, r), Fin.last (m + 1)) := by
  simp [gB, h, last_ne_zero' m]

theorem gB_mid {m p : ℕ} (v : Fin (m + 1) → ℕ) (r : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 2)) (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (m + 1)) :
    gB p ((v, r), k) = ((v, r.trans (Equiv.swap (k.pred hk0) (k.castPred hkl))), k) := by
  simp [gB, hk0, hkl]

theorem gB_mem {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) : gB p x ∈ kdoors (m + 1) p ℓ := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  simp only at hd
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
        intro i
        simp only [Function.update_apply]
        split_ifs with hi
        · exact h
        · exact hv i
      · refine door_transfer (fun j => ⟨(j : ℕ) - 1, by omega⟩) ?_ hd
        intro j hj
        have hj0 : (j : ℕ) ≠ 0 := val_ne_zero_of_ne hj
        have hjlt := j.isLt
        refine ⟨?_, ?_⟩
        · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
          omega
        · have := kvert_move_zero v r ((j : ℕ) - 1) (by omega)
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)] at this
          exact this
    · rw [gB_zero_stay v r h]; exact hx
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr
            ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩
          intro i
          simp only [Function.update_apply]
          split_ifs with hi
          · have := hv (r.symm (Fin.last m)); omega
          · exact hv i
        · refine door_transfer (fun j => ⟨min ((j : ℕ) + 1) (m + 1), by omega⟩) ?_ hd
          intro j hj
          have hjl : (j : ℕ) ≠ m + 1 := val_ne_of_ne_last hj
          have hjlt := j.isLt
          refine ⟨?_, ?_⟩
          · simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
            omega
          · have := kvert_move_last v r (j : ℕ) (by omega) h
            have e : min ((j : ℕ) + 1) (m + 1) = (j : ℕ) + 1 := by omega
            dsimp only
            rw [e]
            exact this
      · rw [gB_last_stay v r h]; exact hx
    · rw [gB_mid v r k hk0 hkl]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨(mem_kgrid _).mpr hv, Finset.mem_univ _⟩, Finset.mem_univ _⟩
      · refine door_transfer id ?_ hd
        intro j hj
        exact ⟨hj, kvert_swap v r k hk0 hkl j (fun h => hj (Fin.ext h))⟩

theorem gB_inv {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) : gB p (gB p x) = x := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h]
      have e1 : (r.trans (finRotate (m + 1)).symm).symm (Fin.last m) = r.symm 0 := by
        rw [Equiv.symm_trans_apply, Equiv.symm_symm, finRotate_last]
      have h' : 0 < Function.update v (r.symm 0) (v (r.symm 0) + 1)
          ((r.trans (finRotate (m + 1)).symm).symm (Fin.last m)) := by
        rw [e1, Function.update_self]; omega
      rw [gB_last_move _ _ h']
      refine Prod.ext (Prod.ext ?_ ?_) rfl
      · simp only [e1, Function.update_self, Function.update_idem, Nat.add_sub_cancel,
          Function.update_eq_self]
      · exact Equiv.ext fun i => by simp
    · rw [gB_zero_stay v r h, gB_zero_stay v r h]
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h]
        have e1 : (r.trans (finRotate (m + 1))).symm 0 = r.symm (Fin.last m) := by
          rw [Equiv.symm_trans_apply, finRotate_symm_zero]
        have h' : Function.update v (r.symm (Fin.last m)) (v (r.symm (Fin.last m)) - 1)
            ((r.trans (finRotate (m + 1))).symm 0) + 1 < p := by
          rw [e1, Function.update_self]; have := hv (r.symm (Fin.last m)); omega
        rw [gB_zero_move _ _ h']
        refine Prod.ext (Prod.ext ?_ ?_) rfl
        · simp only [e1, Function.update_self, Function.update_idem, Nat.sub_add_cancel h,
            Function.update_eq_self]
        · exact Equiv.ext fun i => by simp
      · rw [gB_last_stay v r h, gB_last_stay v r h]
    · rw [gB_mid v r k hk0 hkl, gB_mid v _ k hk0 hkl]
      refine Prod.ext (Prod.ext rfl ?_) rfl
      exact Equiv.ext fun i => by simp [Equiv.swap_apply_self]

theorem gB_fixed_facts {m p : ℕ} (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (h0 : ∀ x (i : Fin (m + 1)), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin (m + 1)), x i = p → (i : ℕ) + 1 ≤ ℓ x)
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (hx : x ∈ kdoors (m + 1) p ℓ) (hfix : gB p x = x) :
    x.2 = 0 ∧ x.1.1 0 = p - 1 ∧ x.1.2 0 = 0 := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx
  have hv : ∀ i, v i < p :=
    (mem_kgrid v).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
  simp only at hd ⊢
  by_cases hk0 : k = 0
  · subst hk0
    by_cases h : v (r.symm 0) + 1 < p
    · rw [gB_zero_move v r h] at hfix
      simp [Fin.ext_iff] at hfix
    · have hvp0 := hv (r.symm 0)
      have hvp : v (r.symm 0) = p - 1 := by omega
      obtain ⟨j, hj, hjl⟩ := hd 1 le_rfl (by omega)
      have hj0 : (j : ℕ) ≠ 0 := val_ne_zero_of_ne hj
      have hcoord : kvert v r j (r.symm 0) = p := by
        simp only [kvert, Equiv.apply_symm_apply, Fin.val_zero]
        rw [if_pos (by omega)]
        omega
      have hle := hP _ _ hcoord
      rw [hjl] at hle
      have hi0 : r.symm 0 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      refine ⟨rfl, ?_, ?_⟩
      · rw [← hi0]; exact hvp
      · exact ((Equiv.symm_apply_eq r).mp hi0).symm
  · by_cases hkl : k = Fin.last (m + 1)
    · subst hkl
      by_cases h : 0 < v (r.symm (Fin.last m))
      · rw [gB_last_move v r h] at hfix
        exact absurd (congrArg Prod.snd hfix).symm (last_ne_zero' m)
      · exfalso
        have hv0 : v (r.symm (Fin.last m)) = 0 := by omega
        have hilt := (r.symm (Fin.last m)).isLt
        obtain ⟨j, hj, hjl⟩ := hd ((r.symm (Fin.last m) : ℕ) + 1) (by omega) (by omega)
        have hjm : (j : ℕ) ≤ m := by
          have := j.isLt
          have : (j : ℕ) ≠ m + 1 := val_ne_of_ne_last hj
          omega
        have hcoord : kvert v r j (r.symm (Fin.last m)) = 0 := by
          simp only [kvert, Equiv.apply_symm_apply, Fin.val_last]
          rw [if_neg (by omega)]
          omega
        exact h0 _ _ hcoord hjl
    · rw [gB_mid v r k hk0 hkl] at hfix
      exfalso
      have h2 := congrArg (fun y => y.1.2 (r.symm (k.pred hk0))) hfix
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left] at h2
      have h3 := congrArg Fin.val h2
      rw [Fin.coe_castPred, Fin.val_pred] at h3
      have hkpos : (k : ℕ) ≠ 0 := val_ne_zero_of_ne hk0
      omega

theorem kvert_face {m : ℕ} (p : ℕ) (hp : 0 < p) (v : Fin m → ℕ) (r : Equiv.Perm (Fin m))
    (j : ℕ) :
    kvert (Fin.cons (p - 1) v : Fin (m + 1) → ℕ) (Equiv.Perm.decomposeFin.symm (0, r)) (j + 1)
      = (Fin.cons p (kvert v r j) : Fin (m + 1) → ℕ) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [kvert, Fin.cons_zero, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero]
    rw [if_pos (by omega)]
    omega
  | succ i =>
    simp only [kvert, Fin.cons_succ, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
      Equiv.refl_apply, Fin.val_succ]
    split_ifs <;> omega

theorem face_door_iff {m p : ℕ} (hp : 0 < p) (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (hP0 : ∀ y : Fin m → ℕ, 1 ≤ ℓ (Fin.cons p y)) (v : Fin m → ℕ) (r : Equiv.Perm (Fin m)) :
    Door ℓ (Fin.cons (p - 1) v) (Equiv.Perm.decomposeFin.symm (0, r)) 0 ↔
      FullyLabelled (fun y => ℓ (Fin.cons p y) - 1) v r := by
  constructor
  · intro hd c hc
    obtain ⟨j, hj, hjc⟩ := hd (c + 1) (by omega) (by omega)
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    refine ⟨j', ?_⟩
    rw [Fin.val_succ, kvert_face p hp] at hjc
    simp only
    omega
  · intro hfl c hc1 hc2
    obtain ⟨j', hj'⟩ := hfl (c - 1) (by omega)
    refine ⟨j'.succ, Fin.succ_ne_zero _, ?_⟩
    rw [Fin.val_succ, kvert_face p hp]
    have := hP0 (kvert v r j')
    simp only at hj'
    omega

theorem perm_decompose_of_zero {m : ℕ} (r : Equiv.Perm (Fin (m + 1))) (hr : r 0 = 0) :
    Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin r).2) = r := by
  obtain ⟨a, e, hae⟩ : ∃ a e, Equiv.Perm.decomposeFin r = (a, e) := ⟨_, _, rfl⟩
  have hr' : r = Equiv.Perm.decomposeFin.symm (a, e) := by rw [← hae, Equiv.symm_apply_apply]
  have ha : a = 0 := by
    have := Equiv.Perm.decomposeFin_symm_apply_zero a e
    rw [← hr', hr] at this
    exact this.symm
  rw [hae, ha, ← ha, ← hr']

theorem fixed_eq_face {m p : ℕ}
    (x : ((Fin (m + 1) → ℕ) × Equiv.Perm (Fin (m + 1))) × Fin (m + 2))
    (e0 : x.2 = 0) (ev : x.1.1 0 = p - 1) (er : x.1.2 0 = 0) :
    ((Fin.cons (p - 1) (Fin.tail x.1.1),
      Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin x.1.2).2)), 0) = x := by
  obtain ⟨⟨v, r⟩, k⟩ := x
  simp only at e0 ev er ⊢
  rw [perm_decompose_of_zero r er, e0, ← ev, Fin.cons_self_tail]

/-- Step B: the number of doors has the parity of the number of completely labelled simplices
of the face `x₀ = p`, with the induced labelling. -/
theorem stepB {m p : ℕ} (hp : 0 < p) (ℓ : (Fin (m + 1) → ℕ) → ℕ)
    (h0 : ∀ x (i : Fin (m + 1)), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin (m + 1)), x i = p → (i : ℕ) + 1 ≤ ℓ x) :
    (((kdoors (m + 1) p ℓ).card : ℕ) : ZMod 2) =
      ((kfull m p (fun y => ℓ (Fin.cons p y) - 1)).card : ZMod 2) := by
  have hP0 : ∀ y : Fin m → ℕ, 1 ≤ ℓ (Fin.cons p y) := fun y => by
    simpa using hP (Fin.cons p y) 0 (by simp)
  rw [card_zmod_two_eq_card_fixed (kdoors (m + 1) p ℓ) (gB p) (gB_mem ℓ) (gB_inv ℓ)]
  congr 1
  apply Finset.card_nbij' (fun x => (Fin.tail x.1.1, (Equiv.Perm.decomposeFin x.1.2).2))
    (fun σ => ((Fin.cons (p - 1) σ.1, Equiv.Perm.decomposeFin.symm (0, σ.2)), 0))
  · intro x hx
    rw [Finset.mem_coe] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨e0, ev, er⟩ := gB_fixed_facts ℓ h0 hP x hx1 hx2
    obtain ⟨hxs, hd⟩ := Finset.mem_filter.mp hx1
    have hv : ∀ i, x.1.1 i < p :=
      (mem_kgrid _).mp (Finset.mem_product.mp (Finset.mem_product.mp hxs).1).1
    have hd' : Door ℓ (Fin.cons (p - 1) (Fin.tail x.1.1))
        (Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin x.1.2).2)) 0 := by
      have h := fixed_eq_face x e0 ev er
      rw [← h] at hd
      exact hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_kgrid _).mpr (fun i => hv i.succ), Finset.mem_univ _⟩, ?_⟩
    exact (face_door_iff hp ℓ hP0 _ _).mp hd'
  · intro σ hσ
    rw [Finset.mem_coe] at hσ ⊢
    obtain ⟨hσs, hfl⟩ := Finset.mem_filter.mp hσ
    have hv : ∀ i, σ.1 i < p := (mem_kgrid _).mp (Finset.mem_product.mp hσs).1
    have hmem : ((Fin.cons (p - 1) σ.1, Equiv.Perm.decomposeFin.symm (0, σ.2)), 0)
        ∈ kdoors (m + 1) p ℓ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(mem_kgrid _).mpr ?_, Finset.mem_univ _⟩, Finset.mem_univ _⟩,
        (face_door_iff hp ℓ hP0 _ _).mpr hfl⟩
      intro i
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; omega
      | succ i => simp only [Fin.cons_succ]; exact hv i
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    have hR : (Equiv.Perm.decomposeFin.symm (0, σ.2)).symm 0 = 0 := by
      rw [Equiv.symm_apply_eq, Equiv.Perm.decomposeFin_symm_apply_zero]
    apply gB_zero_stay
    rw [hR, Fin.cons_zero]
    omega
  · intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨e0, ev, er⟩ := gB_fixed_facts ℓ h0 hP x hx1 hx2
    exact fixed_eq_face x e0 ev er
  · intro σ _
    simp

/-- The number of completely labelled Kuhn simplices is odd (induction on the dimension). -/
theorem kfull_card_odd (n : ℕ) : ∀ (p : ℕ), 0 < p → ∀ (ℓ : (Fin n → ℕ) → ℕ), (∀ y, ℓ y ≤ n) →
    (∀ x (i : Fin n), x i = 0 → ℓ x ≠ (i : ℕ) + 1) →
    (∀ x (i : Fin n), x i = p → (i : ℕ) + 1 ≤ ℓ x) → Odd (kfull n p ℓ).card := by
  induction n with
  | zero =>
    intro p hp ℓ hle h0 hP
    have hfull : kfull 0 p ℓ = ksimp 0 p := by
      apply Finset.filter_true_of_mem
      intro σ _ c hc
      refine ⟨0, ?_⟩
      have := hle (kvert σ.1 σ.2 0)
      simp only [Fin.val_zero]
      omega
    rw [hfull]
    have hc : (ksimp 0 p).card = 1 := by
      simp [ksimp, kgrid]
    rw [hc]
    exact odd_one
  | succ m ih =>
    intro p hp ℓ hle h0 hP
    have hA := stepA (p := p) ℓ hle
    have hB := stepB hp ℓ h0 hP
    have hodd := ih p hp (fun y => ℓ (Fin.cons p y) - 1)
      (fun y => by
        show ℓ (Fin.cons p y) - 1 ≤ m
        have := hle (Fin.cons p y)
        omega)
      (fun y i hy => by
        show ℓ (Fin.cons p y) - 1 ≠ (i : ℕ) + 1
        have h1 := h0 (Fin.cons p y) i.succ (by simpa using hy)
        have h2 := hP (Fin.cons p y) 0 (by simp)
        simp only [Fin.val_succ, Fin.val_zero] at h1 h2
        omega)
      (fun y i hy => by
        show (i : ℕ) + 1 ≤ ℓ (Fin.cons p y) - 1
        have h1 := hP (Fin.cons p y) i.succ (by simpa using hy)
        simp only [Fin.val_succ] at h1
        omega)
    rw [← ZMod.natCast_eq_one_iff_odd] at hodd ⊢
    rw [← hA, hB, hodd]

end Counting

/-- **Sperner's lemma** on Kuhn's triangulation of the cube `[0, p]^n`.

Label the lattice points `x : Fin n → ℕ` by `ℓ x ∈ {0, …, n}` such that a point with `x i = 0`
never carries label `i + 1`, and a point with `x i = p` carries a label `≥ i + 1`. Then some
Kuhn simplex (base `v` with `v i < p`, vertices `kvert v r j`, `j = 0, …, n`) is completely
labelled. (In fact their number is odd: `kfull_card_odd`.) -/
theorem sperner_kuhn (n p : ℕ) (hp : 0 < p) (ℓ : (Fin n → ℕ) → ℕ) (hle : ∀ y, ℓ y ≤ n)
    (h0 : ∀ x (i : Fin n), x i = 0 → ℓ x ≠ (i : ℕ) + 1)
    (hP : ∀ x (i : Fin n), x i = p → (i : ℕ) + 1 ≤ ℓ x) :
    ∃ (v : Fin n → ℕ) (r : Equiv.Perm (Fin n)), (∀ i, v i < p) ∧ FullyLabelled ℓ v r := by
  classical
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp (kfull_card_odd n p hp ℓ hle h0 hP).pos
  obtain ⟨hs, hfl⟩ := Finset.mem_filter.mp hσ
  exact ⟨σ.1, σ.2, (mem_kgrid _).mp (Finset.mem_product.mp hs).1, hfl⟩

/-! ## Brouwer's fixed point theorem on the unit cube -/

section BrouwerCube

open Filter Topology

theorem mem_cube_iff {N : ℕ} (x : Fin N → ℝ) :
    x ∈ Set.Icc (0 : Fin N → ℝ) 1 ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The point of the unit cube represented by the lattice point `x` of `{0, …, p}^N`
(coordinates clamped at `p`). -/
noncomputable def cubePt {N : ℕ} (p : ℕ) (x : Fin N → ℕ) : Fin N → ℝ :=
  fun i => ((min (x i) p : ℕ) : ℝ) / p

theorem cubePt_mem {N p : ℕ} (hp : 0 < p) (x : Fin N → ℕ) :
    cubePt p x ∈ Set.Icc (0 : Fin N → ℝ) 1 := by
  rw [mem_cube_iff]
  intro i
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨by unfold cubePt; positivity, ?_⟩
  unfold cubePt
  rw [div_le_one hp']
  exact_mod_cast min_le_right _ _

open scoped Classical in
/-- Kuhn's labelling for a self-map `f` of the cube: `0` if no coordinate is pushed down,
otherwise `1 +` the largest coordinate `i` with `x i ≠ 0` and `f x i ≤ x i`. -/
noncomputable def cubeLabel {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ) :
    ℕ :=
  (Finset.univ.filter (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i)).sup
    (fun i => (i : ℕ) + 1)

theorem cubeLabel_le {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ) :
    cubeLabel f p x ≤ N := by
  unfold cubeLabel
  apply Finset.sup_le
  intro i _
  exact i.isLt

theorem cubeLabel_mem {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ)
    (i : Fin N) (h : cubeLabel f p x = (i : ℕ) + 1) :
    cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i := by
  classical
  unfold cubeLabel at h
  set s := Finset.univ.filter
    (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) with hs
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty] at h
    exact absurd h (by simp)
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup s hne (fun i : Fin N => (i : ℕ) + 1)
    rw [hjeq] at h
    have hji : j = i := Fin.ext (by have h' : (j : ℕ) + 1 = (i : ℕ) + 1 := h; omega)
    subst hji
    exact (Finset.mem_filter.mp hj).2

theorem cubeLabel_zero {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (p : ℕ) (hp : 0 < p) (x : Fin N → ℕ)
    (h : cubeLabel f p x = 0) (i : Fin N) : cubePt p x i ≤ f (cubePt p x) i := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hfx := (mem_cube_iff _).mp (hmap (cubePt_mem hp x)) i
  have hmem : i ∈ Finset.univ.filter
      (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hlt.le⟩
    intro h0
    rw [h0] at hlt
    linarith [hfx.1]
  have := Finset.le_sup (f := fun i : Fin N => (i : ℕ) + 1) hmem
  unfold cubeLabel at h
  omega

theorem cubeLabel_h0 {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (p : ℕ) (x : Fin N → ℕ)
    (i : Fin N) (hx : x i = 0) : cubeLabel f p x ≠ (i : ℕ) + 1 := by
  intro h
  have := (cubeLabel_mem f p x i h).1
  apply this
  simp [cubePt, hx]

theorem cubeLabel_hP {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (p : ℕ) (hp : 0 < p) (x : Fin N → ℕ)
    (i : Fin N) (hx : x i = p) : (i : ℕ) + 1 ≤ cubeLabel f p x := by
  classical
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hpt : cubePt p x i = 1 := by
    simp only [cubePt, hx, min_self]
    exact div_self hp'.ne'
  have hfx := (mem_cube_iff _).mp (hmap (cubePt_mem hp x)) i
  have hmem : i ∈ Finset.univ.filter
      (fun i : Fin N => cubePt p x i ≠ 0 ∧ f (cubePt p x) i ≤ cubePt p x i) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hpt]; exact one_ne_zero
    · rw [hpt]; exact hfx.2
  have := Finset.le_sup (f := fun i : Fin N => (i : ℕ) + 1) hmem
  unfold cubeLabel
  exact this

theorem dist_cubePt_kvert_le {N p : ℕ} (hp : 0 < p) (v : Fin N → ℕ) (hv : ∀ i, v i < p)
    (r : Equiv.Perm (Fin N)) (j : ℕ) :
    dist (cubePt p (kvert v r j)) (cubePt p v) ≤ 1 / (p : ℝ) := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have h1 : min (kvert v r j i) p = kvert v r j i :=
    min_eq_left (by unfold kvert; have := hv i; split_ifs <;> omega)
  have h2 : min (v i) p = v i := min_eq_left (hv i).le
  simp only [cubePt, h1, h2, Real.dist_eq]
  unfold kvert
  split_ifs
  · push_cast
    rw [show ((v i : ℝ) + 1) / p - v i / p = 1 / p by ring, abs_of_pos (by positivity)]
  · simp only [add_zero, sub_self, abs_zero]
    positivity

/-- Approximate fixed points from Sperner's lemma: at mesh `1 / (k + 1)` there is a base point
`b`, a nearby point `a` pushed up in every coordinate, and for each coordinate `i` a nearby
point `c i` pushed down in coordinate `i`. -/
theorem cube_approx {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (k : ℕ) :
    ∃ (b a : Fin N → ℝ) (c : Fin N → Fin N → ℝ),
      b ∈ Set.Icc (0 : Fin N → ℝ) 1 ∧ a ∈ Set.Icc (0 : Fin N → ℝ) 1 ∧
      (∀ i, c i ∈ Set.Icc (0 : Fin N → ℝ) 1) ∧
      dist a b ≤ 1 / ((k : ℝ) + 1) ∧ (∀ i, dist (c i) b ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ i, a i ≤ f a i) ∧ (∀ i, f (c i) i ≤ c i i) := by
  have hp : 0 < k + 1 := Nat.succ_pos k
  obtain ⟨v, r, hv, hfl⟩ := sperner_kuhn N (k + 1) hp (cubeLabel f (k + 1))
    (cubeLabel_le f (k + 1)) (fun x i hx => cubeLabel_h0 f (k + 1) x i hx)
    (fun x i hx => cubeLabel_hP f hmap (k + 1) hp x i hx)
  obtain ⟨j0, hj0⟩ := hfl 0 (Nat.zero_le _)
  have hJ : ∀ i : Fin N, ∃ j : Fin (N + 1), cubeLabel f (k + 1) (kvert v r j) = (i : ℕ) + 1 :=
    fun i => hfl _ (by omega)
  choose J hJ using hJ
  have hk : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  refine ⟨cubePt (k + 1) v, cubePt (k + 1) (kvert v r j0),
    fun i => cubePt (k + 1) (kvert v r (J i)),
    cubePt_mem hp v, cubePt_mem hp _, fun i => cubePt_mem hp _, ?_, ?_, ?_, ?_⟩
  · rw [← hk]; exact dist_cubePt_kvert_le hp v hv r _
  · intro i; rw [← hk]; exact dist_cubePt_kvert_le hp v hv r _
  · exact cubeLabel_zero f hmap (k + 1) hp _ hj0
  · intro i
    exact (cubeLabel_mem f (k + 1) _ i (hJ i)).2

/-- **Brouwer's fixed point theorem** on the unit cube `[0, 1]^N`, for `f` continuous on the
cube and mapping it into itself. -/
theorem brouwer_cube_Icc {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hf : ContinuousOn f (Set.Icc 0 1)) (hmap : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : Fin N → ℝ) 1, f x = x := by
  choose b a c hb ha hc hab hcb ha' hc' using cube_approx f hmap
  obtain ⟨x, hx, φ, hφ, hlim⟩ :=
    (isCompact_Icc (a := (0 : Fin N → ℝ)) (b := 1)).tendsto_subseq hb
  refine ⟨x, hx, ?_⟩
  have hε : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlimA : Tendsto (fun k => a (φ k)) atTop (𝓝 x) := by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hε
    rw [dist_comm]
    exact hab (φ k)
  have hlimC : ∀ i, Tendsto (fun k => c (φ k) i) atTop (𝓝 x) := fun i => by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hε
    rw [dist_comm]
    exact hcb (φ k) i
  have hfx : ∀ u : ℕ → Fin N → ℝ, (∀ k, u k ∈ Set.Icc (0 : Fin N → ℝ) 1) →
      Tendsto u atTop (𝓝 x) → Tendsto (fun k => f (u k)) atTop (𝓝 (f x)) := fun u hu hlu =>
    (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlu, Filter.Eventually.of_forall hu⟩)
  funext i
  apply le_antisymm
  · have h1 := ((continuous_apply i).tendsto (f x)).comp
      (hfx (fun k => c (φ k) i) (fun k => hc (φ k) i) (hlimC i))
    have h2 := ((continuous_apply i).tendsto x).comp (hlimC i)
    exact le_of_tendsto_of_tendsto' h1 h2 (fun k => hc' (φ k) i)
  · have h1 := ((continuous_apply i).tendsto (f x)).comp
      (hfx (fun k => a (φ k)) (fun k => ha (φ k)) hlimA)
    have h2 := ((continuous_apply i).tendsto x).comp hlimA
    exact le_of_tendsto_of_tendsto' h2 h1 (fun k => ha' (φ k) i)

/-- **Brouwer's fixed point theorem** on the unit cube, coordinate form, for `f` continuous on
the cube. -/
theorem brouwer_cube_continuousOn (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ))
    (hf : ContinuousOn f {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1})
    (hmap : ∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) :
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x := by
  have hset : {x : Fin N → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1} = Set.Icc 0 1 :=
    Set.ext fun x => (mem_cube_iff x).symm
  rw [hset] at hf
  obtain ⟨x, hx, hfx⟩ := brouwer_cube_Icc f hf
    (fun x hx => (mem_cube_iff _).mpr (hmap x ((mem_cube_iff x).mp hx)))
  exact ⟨x, (mem_cube_iff x).mp hx, hfx⟩

/-- **Brouwer's fixed point theorem** on the unit cube: a continuous `f : ℝ^N → ℝ^N` mapping
the cube `{x | ∀ i, 0 ≤ x i ≤ 1}` into itself has a fixed point in the cube. -/
theorem brouwer_cube (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ)) (hf : Continuous f)
    (hmap : ∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) :
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x :=
  brouwer_cube_continuousOn N f hf.continuousOn hmap

end BrouwerCube

end BrouwerLib




open Matrix Filter Topology

namespace LemkeAux

open LemkeLCP.Existence

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A solution of the LCP with `w = M z - p`. -/
def Solv (M : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  ∃ z : ι → ℝ, 0 ≤ z ∧ 0 ≤ M *ᵥ z - p ∧ z ⬝ᵥ (M *ᵥ z - p) = 0

theorem sum_coe_eq {E : Type*} [AddCommMonoid E] (S : Finset ι) (f : ι → E)
    (h : ∀ i ∉ S, f i = 0) : ∑ i : S, f i = ∑ i, f i := by
  rw [Finset.sum_coe_sort S f]
  exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => h i hi)

theorem cara_step {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ι → E) (u : ι → ℝ)
    (hu : 0 ≤ u)
    (hli : ¬ LinearIndependent ℝ (fun i : (Finset.univ.filter (fun i => u i ≠ 0)) => v i)) :
    ∃ u' : ι → ℝ, 0 ≤ u' ∧ ∑ i, u' i • v i = ∑ i, u i • v i ∧
      (Finset.univ.filter (fun i => u' i ≠ 0)).card <
        (Finset.univ.filter (fun i => u i ≠ 0)).card := by
  set S := Finset.univ.filter (fun i => u i ≠ 0) with hS
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let g' : ι → ℝ := fun i => if h : i ∈ S then g ⟨i, h⟩ else 0
  have hg'0 : ∀ i ∉ S, g' i = 0 := fun i hi => by simp [g', hi]
  have hg'sum : ∑ i, g' i • v i = 0 := by
    rw [← sum_coe_eq S (fun i => g' i • v i) (fun i hi => by simp [hg'0 i hi])]
    rw [← hg]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, hi⟩ _
    simp [g', hi]
  have hne : g' i0 ≠ 0 := by simpa [g', i0.2] using hi0
  obtain ⟨h, hh0, hhsum, hpos⟩ : ∃ h : ι → ℝ, (∀ i ∉ S, h i = 0) ∧ ∑ i, h i • v i = 0 ∧
      ∃ i, 0 < h i := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨-g', fun i hi => by simp [hg'0 i hi], ?_, ⟨i0, by simp; linarith⟩⟩
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hg'sum, neg_zero]
    · exact ⟨g', hg'0, hg'sum, ⟨i0, hgt⟩⟩
  set P := Finset.univ.filter (fun i => 0 < h i) with hP
  have hPne : P.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simp [P, hi]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => u i / h i) hPne
  have hj : 0 < h j := by simpa [P] using hjP
  have hjS : j ∈ S := by
    by_contra hc
    have := hh0 j hc
    linarith
  have huj : 0 < u j := by
    have h1 : u j ≠ 0 := (Finset.mem_filter.mp hjS).2
    exact lt_of_le_of_ne (hu j) (Ne.symm h1)
  set t := u j / h j with ht
  have htpos : 0 < t := div_pos huj hj
  refine ⟨u - t • h, ?_, ?_, ?_⟩
  · intro i
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : 0 < h i
    · have h2 := hjmin i (by simp [P, hi])
      rw [le_div_iff₀ hi] at h2
      linarith
    · push_neg at hi
      have hui : 0 ≤ u i := hu i
      nlinarith [mul_nonneg htpos.le (neg_nonneg.mpr hi)]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib,
      mul_smul]
    rw [← Finset.smul_sum, hhsum, smul_zero, sub_zero]
  · have hsub : Finset.univ.filter (fun i => (u - t • h) i ≠ 0) ⊆ S := by
      refine Finset.subset_iff.mpr fun i hi => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at hi ⊢
      intro hui
      apply hi
      have := hh0 i (by simp [S, hui])
      simp [hui, this]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨j, hjS, ?_⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [ht, div_mul_cancel₀ _ hj.ne', sub_self]

theorem cara {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ι → E) :
    ∀ u : ι → ℝ, 0 ≤ u →
      ∃ u' : ι → ℝ, 0 ≤ u' ∧ ∑ i, u' i • v i = ∑ i, u i • v i ∧
        LinearIndependent ℝ (fun i : (Finset.univ.filter (fun i => u' i ≠ 0)) => v i) := by
  suffices H : ∀ n : ℕ, ∀ u : ι → ℝ, 0 ≤ u → (Finset.univ.filter (fun i => u i ≠ 0)).card = n →
      ∃ u' : ι → ℝ, 0 ≤ u' ∧ ∑ i, u' i • v i = ∑ i, u i • v i ∧
        LinearIndependent ℝ (fun i : (Finset.univ.filter (fun i => u' i ≠ 0)) => v i) from
    fun u hu => H _ u hu rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu hn
    by_cases hli : LinearIndependent ℝ (fun i : (Finset.univ.filter (fun i => u i ≠ 0)) => v i)
    · exact ⟨u, hu, rfl, hli⟩
    · obtain ⟨u'', hu'', hsum, hlt⟩ := cara_step v u hu hli
      obtain ⟨u', h1, h2, h3⟩ := ih _ (hn ▸ hlt) u'' hu'' rfl
      exact ⟨u', h1, h2.trans hsum, h3⟩

theorem cone_closed {κ : Type*} [Fintype κ] (v : ι → (κ → ℝ)) :
    IsClosed {x : κ → ℝ | ∃ u : ι → ℝ, 0 ≤ u ∧ x = ∑ i, u i • v i} := by
  have hEq : {x : κ → ℝ | ∃ u : ι → ℝ, 0 ≤ u ∧ x = ∑ i, u i • v i} =
      ⋃ S : Finset ι, ⋃ (_ : LinearIndependent ℝ (fun i : S => v i)),
        (Fintype.linearCombination ℝ (fun i : S => v i)) '' {c | 0 ≤ c} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨u', hu', hsum, hli⟩ := cara v u hu
      refine ⟨_, hli, fun i => u' i, fun i => hu' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hsum]
      exact sum_coe_eq _ (fun i => u' i • v i) (fun i hi => by simp at hi; simp [hi])
    · rintro ⟨S, _, c, hc, rfl⟩
      refine ⟨fun i => if h : i ∈ S then c ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i
        by_cases h : i ∈ S
        · simp only [h, dif_pos, Pi.zero_apply]; exact hc ⟨i, h⟩
        · simp [h]
      · rw [Fintype.linearCombination_apply]
        rw [← sum_coe_eq S _ (fun i hi => by simp [hi])]
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi⟩ _
        simp [hi]
  rw [hEq]
  refine isClosed_iUnion_of_finite fun S => isClosed_iUnion_of_finite fun hli => ?_
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : S => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hli
  exact (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap _
    (isClosed_le continuous_const continuous_id)

/-- the generator of the complementary cone for the pattern `α` -/
def vcol (M : Matrix ι ι ℝ) (α : Finset ι) (i : ι) : ι → ℝ :=
  if i ∈ α then (fun j => M j i) else -(Pi.single i (1 : ℝ))

theorem vcol_sum (M : Matrix ι ι ℝ) (α : Finset ι) (u : ι → ℝ) :
    ∑ i, u i • vcol M α i =
      M *ᵥ (fun i => if i ∈ α then u i else 0) - (fun i => if i ∈ α then 0 else u i) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.mulVec,
    dotProduct]
  have hj : (if j ∈ α then (0 : ℝ) else u j) =
      ∑ i, u i * (if i ∈ α then 0 else (Pi.single i (1 : ℝ) : ι → ℝ) j) := by
    rw [Finset.sum_eq_single j]
    · by_cases hj : j ∈ α <;> simp [hj]
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  rw [hj, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ α
  · simp [vcol, hi]; ring
  · simp [vcol, hi]

theorem solv_closed (M : Matrix ι ι ℝ) : IsClosed {p : ι → ℝ | Solv M p} := by
  have hEq : {p : ι → ℝ | Solv M p} =
      ⋃ α : Finset ι, {x | ∃ u : ι → ℝ, 0 ≤ u ∧ x = ∑ i, u i • vcol M α i} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz0, hw0, hc⟩
      have hterm : ∀ i, z i * (M *ᵥ z - p) i = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_nonneg (hz0 i) (hw0 i))).mp hc
        exact fun i => this i (Finset.mem_univ i)
      refine ⟨Finset.univ.filter (fun i => z i ≠ 0),
        fun i => if z i ≠ 0 then z i else (M *ᵥ z - p) i, ?_, ?_⟩
      · intro i
        by_cases h : z i ≠ 0
        · show 0 ≤ if z i ≠ 0 then z i else (M *ᵥ z - p) i
          rw [if_pos h]; exact hz0 i
        · show 0 ≤ if z i ≠ 0 then z i else (M *ᵥ z - p) i
          rw [if_neg h]; exact hw0 i
      · rw [vcol_sum]
        have h1 : (fun i => if i ∈ Finset.univ.filter (fun i => z i ≠ 0) then
            (if z i ≠ 0 then z i else (M *ᵥ z - p) i) else 0) = z := by
          funext i
          by_cases h : z i ≠ 0
          · simp [h]
          · push_neg at h; simp [h]
        have h2 : (fun i => if i ∈ Finset.univ.filter (fun i => z i ≠ 0) then 0 else
            (if z i ≠ 0 then z i else (M *ᵥ z - p) i)) = M *ᵥ z - p := by
          funext i
          by_cases h : z i ≠ 0
          · have := hterm i
            show (if i ∈ Finset.univ.filter (fun i => z i ≠ 0) then 0 else
              (if z i ≠ 0 then z i else (M *ᵥ z - p) i)) = (M *ᵥ z - p) i
            rw [if_pos (by simp [h])]
            rcases mul_eq_zero.mp this with h' | h'
            · exact absurd h' h
            · exact h'.symm
          · simp [h]
        rw [h1, h2]
        abel
    · rintro ⟨α, u, hu, rfl⟩
      refine ⟨fun i => if i ∈ α then u i else 0, ?_, ?_, ?_⟩
      · intro i; have hui : 0 ≤ u i := hu i; by_cases h : i ∈ α <;> simp [h, hui]
      · rw [vcol_sum]
        intro i; have hui : 0 ≤ u i := hu i; by_cases h : i ∈ α <;> simp [h, hui]
      · rw [vcol_sum, sub_sub_cancel]
        simp only [dotProduct]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases h : i ∈ α <;> simp [h]
  rw [hEq]
  exact isClosed_iUnion_of_finite fun α => cone_closed _

end General

section Analytic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Brouwer's fixed point theorem on the unit cube, as a proposition. -/
def BrouwerCube : Prop := ∀ (N : ℕ) (f : (Fin N → ℝ) → (Fin N → ℝ)), Continuous f →
    (∀ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∀ i, 0 ≤ f x i ∧ f x i ≤ 1) →
    ∃ x, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ f x = x

theorem clamp_fix {x f R : ℝ} (hR : 0 ≤ R) (h : x = max 0 (min R (x - f))) :
    (x = 0 ∧ 0 ≤ f) ∨ (0 ≤ x ∧ x ≤ R ∧ f = 0) ∨ (x = R ∧ f ≤ 0) := by
  rcases le_total (x - f) 0 with h1 | h1
  · left
    have h2 : min R (x - f) ≤ 0 := (min_le_right _ _).trans h1
    rw [max_eq_left h2] at h
    exact ⟨h, by linarith⟩
  · rcases le_total (x - f) R with h2 | h2
    · right; left
      rw [min_eq_right h2, max_eq_right h1] at h
      exact ⟨by linarith, by linarith, by linarith⟩
    · right; right
      rw [min_eq_left h2, max_eq_right hR] at h
      exact ⟨h, by linarith⟩

theorem box_fix (hB : BrouwerCube) {R : ℝ} (hR : 0 < R) (T : (ι → ℝ) → (ι → ℝ))
    (hT : Continuous T) (hmap : ∀ z i, 0 ≤ T z i ∧ T z i ≤ R) : ∃ z, T z = z := by
  let e := Fintype.equivFin ι
  let f : (Fin (Fintype.card ι) → ℝ) → (Fin (Fintype.card ι) → ℝ) :=
    fun x k => T (fun i => R * x (e i)) (e.symm k) / R
  have hf : Continuous f := by
    refine continuous_pi fun k => ?_
    exact ((continuous_apply _).comp (hT.comp (continuous_pi fun i =>
      continuous_const.mul (continuous_apply (e i))))).div_const R
  obtain ⟨x, -, hx⟩ := hB _ f hf (fun x _ k =>
    ⟨div_nonneg (hmap _ _).1 hR.le, (div_le_one hR).mpr (hmap _ _).2⟩)
  refine ⟨fun i => R * x (e i), funext fun i => ?_⟩
  have h1 := congrFun hx (e i)
  simp only [f, Equiv.symm_apply_apply] at h1
  rw [div_eq_iff hR.ne'] at h1
  rw [h1]; ring

theorem reg_solv (hB : BrouwerCube) (M : Matrix ι ι ℝ)
    (hcop : ∀ u : ι → ℝ, 0 ≤ u → 0 ≤ u ⬝ᵥ (M *ᵥ u)) {δ : ℝ} (hδ : 0 < δ) (p : ι → ℝ) :
    ∃ z : ι → ℝ, 0 ≤ z ∧ 0 ≤ M *ᵥ z + δ • z - p ∧ z ⬝ᵥ (M *ᵥ z + δ • z - p) = 0 := by
  set P : ℝ := ∑ i, |p i| with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R : ℝ := P / δ + 1 with hR
  have hRpos : 0 < R := by positivity
  have hδR : δ * R = P + δ := by rw [hR]; field_simp
  let F : (ι → ℝ) → (ι → ℝ) := fun z => M *ᵥ z + δ • z - p
  have hF : Continuous F := by fun_prop
  let T : (ι → ℝ) → (ι → ℝ) := fun z i => max 0 (min R (z i - F z i))
  have hT : Continuous T := continuous_pi fun i =>
    continuous_const.max (continuous_const.min ((continuous_apply i).sub
      ((continuous_apply i).comp hF)))
  obtain ⟨z, hz⟩ := box_fix hB hRpos T hT (fun z i =>
    ⟨le_max_left _ _, max_le hRpos.le (min_le_left _ _)⟩)
  have hzi : ∀ i, 0 ≤ z i ∧ z i ≤ R ∧ z i * F z i ≤ 0 ∧
      (z i < R → 0 ≤ F z i ∧ z i * F z i = 0) := by
    intro i
    rcases clamp_fix hRpos.le (congrFun hz i).symm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · refine ⟨by rw [h1], by rw [h1]; exact hRpos.le, by rw [h1]; simp,
        fun _ => ⟨h2, by rw [h1]; simp⟩⟩
    · refine ⟨h1, h2, by rw [h3]; simp, fun _ => ⟨by rw [h3], by rw [h3]; simp⟩⟩
    · refine ⟨by rw [h1]; exact hRpos.le, by rw [h1], by rw [h1]; nlinarith,
        fun h => absurd h (by rw [h1]; exact lt_irrefl R)⟩
  have hlt : ∀ i, z i < R := by
    intro j
    by_contra hcon
    have hzj : z j = R := le_antisymm (hzi j).2.1 (not_lt.mp hcon)
    have hsum : z ⬝ᵥ F z ≤ 0 := Finset.sum_nonpos fun i _ => (hzi i).2.2.1
    have hexp : z ⬝ᵥ F z = z ⬝ᵥ (M *ᵥ z) + δ * (z ⬝ᵥ z) - z ⬝ᵥ p := by
      simp only [F, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hzz : z j * z j ≤ z ⬝ᵥ z :=
      Finset.single_le_sum (f := fun i => z i * z i) (fun i _ => mul_self_nonneg _)
        (Finset.mem_univ j)
    have hzp : z ⬝ᵥ p ≤ R * P := by
      rw [hP, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      calc z i * p i ≤ z i * |p i| := mul_le_mul_of_nonneg_left (le_abs_self _) (hzi i).1
        _ ≤ R * |p i| := mul_le_mul_of_nonneg_right (hzi i).2.1 (abs_nonneg _)
    have hMz := hcop z (fun i => (hzi i).1)
    rw [hzj] at hzz
    have h3 : δ * (R * R) ≤ R * P := by nlinarith
    have h4 : (P + δ) * R ≤ R * P := by rw [← hδR]; linarith
    nlinarith
  refine ⟨z, fun i => (hzi i).1, fun i => ((hzi i).2.2.2 (hlt i)).1, ?_⟩
  exact Finset.sum_eq_zero fun i _ => ((hzi i).2.2.2 (hlt i)).2

theorem perturbed_solv (hB : BrouwerCube) (M : Matrix ι ι ℝ) (hM : CopositivePlus M)
    (p zh : ι → ℝ) (hzh : 0 ≤ zh) (hpos : ∀ i, 0 < (M *ᵥ zh - p) i) : Solv M p := by
  have hcop : ∀ u : ι → ℝ, 0 ≤ u → 0 ≤ u ⬝ᵥ (M *ᵥ u) := fun u hu => (hM u hu).1
  choose z hz0 hzw hzc using fun k : ℕ =>
    reg_solv hB M hcop (Nat.one_div_pos_of_nat (α := ℝ) (n := k)) p
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδdef
  let S : ℕ → ℝ := fun k => ∑ i, z k i
  have hS0 : ∀ k, 0 ≤ S k := fun k => Finset.sum_nonneg fun i _ => hz0 k i
  let t : ℕ → ℝ := fun k => 1 / (1 + S k)
  have htpos : ∀ k, 0 < t k := fun k => by have := hS0 k; simp only [t]; positivity
  let y : ℕ → ι → ℝ := fun k => t k • z k
  have hsumy : ∀ k, ∑ i, y k i + t k = 1 := by
    intro k
    have h1 : ∑ i, y k i = t k * S k := by
      simp only [y, S, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [h1]
    have := hS0 k
    simp only [t]
    field_simp
    ring
  have hy0 : ∀ k i, 0 ≤ y k i := fun k i => mul_nonneg (htpos k).le (hz0 k i)
  have hmem : ∀ k, (y k, t k) ∈ (Set.Icc (0 : ι → ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1) := by
    intro k
    have hs := hsumy k
    have hyle : ∀ i, y k i ≤ 1 := by
      intro i
      have h1 : y k i ≤ ∑ j, y k j :=
        Finset.single_le_sum (f := fun j => y k j) (fun j _ => hy0 k j) (Finset.mem_univ i)
      linarith [hsumy k, htpos k]
    refine ⟨⟨fun i => hy0 k i, fun i => hyle i⟩, ⟨(htpos k).le, ?_⟩⟩
    have : 0 ≤ ∑ i, y k i := Finset.sum_nonneg fun i _ => hy0 k i
    linarith
  obtain ⟨⟨yl, tl⟩, hlmem, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hδlim : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hX : Tendsto (fun k => ((y (φ k), t (φ k)), δ (φ k))) atTop (𝓝 ((yl, tl), 0)) :=
    hlim.prodMk_nhds hδlim
  -- scaled identities
  have hscale : ∀ k, M *ᵥ y k + δ k • y k - t k • p = t k • (M *ᵥ z k + δ k • z k - p) := by
    intro k
    simp only [y]
    rw [Matrix.mulVec_smul, smul_sub, smul_add, smul_comm (t k) (δ k) (z k)]
  have f1 : ∀ k i, 0 ≤ (M *ᵥ y k + δ k • y k - t k • p) i := by
    intro k i
    rw [hscale k]
    exact mul_nonneg (htpos k).le (hzw k i)
  have f2 : ∀ k, y k ⬝ᵥ (M *ᵥ y k + δ k • y k - t k • p) = 0 := by
    intro k
    rw [hscale k]
    simp only [y, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hzc k]; ring
  have f3 : ∀ k, 0 ≤ y k ⬝ᵥ p := by
    intro k
    have h1 := hzc k
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1
    have h2 := hcop (z k) (hz0 k)
    have h3 : 0 ≤ z k ⬝ᵥ z k := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h4 : 0 ≤ z k ⬝ᵥ p := by
      have : 0 ≤ δ k := (Nat.one_div_pos_of_nat (α := ℝ) (n := k)).le
      nlinarith
    simp only [y, smul_dotProduct, smul_eq_mul]
    exact mul_nonneg (htpos k).le h4
  -- limits
  have L1 : ∀ i, 0 ≤ (M *ᵥ yl - tl • p) i := by
    intro i
    have hc : Continuous (fun X : ((ι → ℝ) × ℝ) × ℝ =>
        (M *ᵥ X.1.1 + X.2 • X.1.1 - X.1.2 • p) i) := by fun_prop
    have := ge_of_tendsto' ((hc.tendsto _).comp hX) (fun k => f1 (φ k) i)
    simpa using this
  have L2 : yl ⬝ᵥ (M *ᵥ yl - tl • p) = 0 := by
    have hc : Continuous (fun X : ((ι → ℝ) × ℝ) × ℝ =>
        X.1.1 ⬝ᵥ (M *ᵥ X.1.1 + X.2 • X.1.1 - X.1.2 • p)) := by fun_prop
    have T := (hc.tendsto _).comp hX
    have a := ge_of_tendsto' T (fun k => (f2 (φ k)).ge)
    have b := le_of_tendsto' T (fun k => (f2 (φ k)).le)
    simp only [zero_smul, add_zero] at a b
    exact le_antisymm b a
  have L3 : 0 ≤ yl ⬝ᵥ p := by
    have hc : Continuous (fun X : ((ι → ℝ) × ℝ) × ℝ => X.1.1 ⬝ᵥ p) := by fun_prop
    exact ge_of_tendsto' ((hc.tendsto _).comp hX) (fun k => f3 (φ k))
  have L4 : ∑ i, yl i + tl = 1 := by
    have hc : Continuous (fun X : ((ι → ℝ) × ℝ) × ℝ => ∑ i, X.1.1 i + X.1.2) := by fun_prop
    have T := (hc.tendsto _).comp hX
    have a := ge_of_tendsto' T (fun k => (hsumy (φ k)).ge)
    have b := le_of_tendsto' T (fun k => (hsumy (φ k)).le)
    exact le_antisymm b a
  have hyl0 : 0 ≤ yl := hlmem.1.1
  have htl0 : 0 ≤ tl := hlmem.2.1
  rcases htl0.lt_or_eq with htl | htl
  · refine ⟨tl⁻¹ • yl, fun i => mul_nonneg (inv_nonneg.mpr htl0) (hyl0 i), ?_, ?_⟩
    · have : M *ᵥ (tl⁻¹ • yl) - p = tl⁻¹ • (M *ᵥ yl - tl • p) := by
        rw [Matrix.mulVec_smul, smul_sub, smul_smul, inv_mul_cancel₀ htl.ne', one_smul]
      rw [this]
      intro i
      exact mul_nonneg (inv_nonneg.mpr htl0) (L1 i)
    · have : M *ᵥ (tl⁻¹ • yl) - p = tl⁻¹ • (M *ᵥ yl - tl • p) := by
        rw [Matrix.mulVec_smul, smul_sub, smul_smul, inv_mul_cancel₀ htl.ne', one_smul]
      rw [this, smul_dotProduct, dotProduct_smul, L2]
      simp
  · exfalso
    subst htl
    have hMy : 0 ≤ M *ᵥ yl := fun i => by simpa using L1 i
    have hyMy : yl ⬝ᵥ (M *ᵥ yl) = 0 := by simpa using L2
    have hplus := (hM yl hyl0).2 hyMy
    have hsum1 : ∑ i, yl i = 1 := by simpa using L4
    obtain ⟨j, hj⟩ : ∃ j, 0 < yl j := by
      by_contra hc
      push_neg at hc
      have : ∑ i, yl i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
      linarith
    have hposdot : 0 < yl ⬝ᵥ (M *ᵥ zh - p) :=
      Finset.sum_pos' (fun i _ => mul_nonneg (hyl0 i) (hpos i).le)
        ⟨j, Finset.mem_univ j, mul_pos hj (hpos j)⟩
    have hT : Mᵀ *ᵥ yl = -(M *ᵥ yl) := eq_neg_of_add_eq_zero_right hplus
    have hdot : yl ⬝ᵥ (M *ᵥ zh) = -((M *ᵥ yl) ⬝ᵥ zh) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, neg_dotProduct]
    have hnn : 0 ≤ (M *ᵥ yl) ⬝ᵥ zh :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hMy i) (hzh i)
    rw [dotProduct_sub, hdot] at hposdot
    linarith

theorem lemke_of_brouwer (hB : BrouwerCube) (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hM : CopositivePlus M) (hZ : (Z M q).Nonempty) : ∃ z : ι → ℝ, IsEquilibriumPoint M q z := by
  obtain ⟨zh, hzh0, hzhw⟩ := hZ
  have hmem : ∀ k : ℕ, Solv M (q - (1 / ((k : ℝ) + 1)) • (fun _ => (1 : ℝ))) := by
    intro k
    refine perturbed_solv hB M hM _ zh hzh0 (fun i => ?_)
    have h1 := hzhw i
    have h2 := Nat.one_div_pos_of_nat (α := ℝ) (n := k)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at h1 ⊢
    linarith
  have hlim : Tendsto (fun k : ℕ => q - (1 / ((k : ℝ) + 1)) • (fun _ => (1 : ℝ))) atTop (𝓝 q) := by
    have h0 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • (fun _ : ι => (1 : ℝ))) atTop
        (𝓝 ((0 : ℝ) • (fun _ : ι => (1 : ℝ)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _
    simpa using (tendsto_const_nhds (x := q)).sub h0
  obtain ⟨z, hz0, hzw, hzc⟩ := (solv_closed M).mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact ⟨z, ⟨hz0, hzw⟩, hzc⟩

end Analytic

end LemkeAux


theorem brouwerCube_holds : LemkeAux.BrouwerCube :=
  fun N f hf hmap => BrouwerLib.brouwer_cube N f hf hmap

open LemkeLCP.Existence in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hnd : NonDegenerate M q) (hM : CopositivePlus M) (hZ : (Z M q).Nonempty) :
    ∃ z : ι → ℝ, IsEquilibriumPoint M q z := by
  exact LemkeAux.lemke_of_brouwer brouwerCube_holds M q hM hZ
