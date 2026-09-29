-- Prove2me | solution 1 for Milnor.fg_closure_zpow_conj_of_not_hasExponentialGrowth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-19T22:59:00.137659+00:00
-- url     : https://prove2.me/submissions/15882252-33d0-4f53-bc83-611bfea582d3

import Definitions.Def_Chou_Growth
import Mathlib

/-!
# Milnor, Lemma 1 (J. Differential Geometry 2 (1968) 447)

In the standing setting of an extension `1 → A → B → C → 1` with `A` abelian and `B` finitely
generated: if `B` does not have exponential growth, then for each `α ∈ A` and `β ∈ B` the set of
all conjugates `β ^ k * α * β ^ (-k)`, `k ∈ ℤ`, spans a finitely generated subgroup.
-/

namespace Milnor
namespace Lib

open Chou

open scoped IsMulCommutative

/-! ### Word balls (copied from `Chou.Lib`, `CH_growth3`) -/

section WordBall

variable {G : Type*} [Group G]

/-- The ball of radius `n` for a finite set `S` is finite. -/
lemma wordBall_finite (S : Finset G) (n : ℕ) : (wordBall (S : Set G) n).Finite := by
  classical
  induction n with
  | zero =>
      refine Set.Finite.subset (Set.finite_singleton (1 : G)) ?_
      rintro g ⟨l, hl, -, rfl⟩
      have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
      simp [hnil]
  | succ n ih =>
      have hT : ((↑(S ∪ S.image (fun y => y⁻¹)) : Set G)).Finite := Set.toFinite _
      refine Set.Finite.subset (Set.Finite.union (Set.finite_singleton (1 : G)) (hT.mul ih)) ?_
      rintro g ⟨l, hl, hmem, rfl⟩
      match l with
      | [] => exact Or.inl (by simp)
      | x :: t =>
          refine Or.inr ?_
          have hx : x ∈ ((↑(S ∪ S.image (fun y => y⁻¹)) : Set G)) := by
            have hx' := hmem x (by simp)
            simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
              Set.mem_image] at hx' ⊢
            rcases hx' with h | h
            · exact Or.inl (by simpa using h)
            · exact Or.inr ⟨x⁻¹, by simpa using h, by simp⟩
          have ht : t.prod ∈ wordBall (S : Set G) n :=
            ⟨t, by simpa using hl, fun y hy => hmem y (by simp [hy]), rfl⟩
          rw [List.prod_cons]
          exact Set.mul_mem_mul hx ht

end WordBall

/-! ### The conjugates `β ^ k * α * β ^ (-k)` -/

section Conj

variable {B : Type*} [Group B]

/-- `mconj α β k = β ^ k * α * β ^ (-k)`, Milnor's `α_k`. -/
def mconj (α β : B) (k : ℤ) : B := β ^ k * α * β ^ (-k)

lemma mconj_def (α β : B) (k : ℤ) : mconj α β k = β ^ k * α * β ^ (-k) := rfl

lemma mconj_zero (α β : B) : mconj α β 0 = α := by simp [mconj]

lemma mconj_succ (α β : B) (k : ℤ) : mconj α β (k + 1) = β * mconj α β k * β⁻¹ := by
  simp only [mconj, zpow_neg]
  group

lemma mconj_pred (α β : B) (k : ℤ) : mconj α β (k - 1) = β⁻¹ * mconj α β k * β := by
  simp only [mconj, zpow_neg]
  group

lemma mconj_pow (α β : B) (k : ℤ) (m : ℕ) : mconj α β k ^ m = β ^ k * α ^ m * β ^ (-k) := by
  simp only [mconj, zpow_neg]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      group

lemma mconj_mem {A : Subgroup B} [hA : A.Normal] {α : B} (hα : α ∈ A) (β : B) (k : ℤ) :
    mconj α β k ∈ A := by
  have h := hA.conj_mem α hα (β ^ k)
  simpa [mconj, zpow_neg] using h

/-- The conjugate `mconj α β k`, viewed as an element of the (abelian) subgroup `A`. -/
def mconjA {A : Subgroup B} [A.Normal] {α : B} (hα : α ∈ A) (β : B) (k : ℤ) : A :=
  ⟨mconj α β k, mconj_mem hα β k⟩

@[simp] lemma coe_mconjA {A : Subgroup B} [A.Normal] {α : B} (hα : α ∈ A) (β : B) (k : ℤ) :
    ((mconjA hα β k : A) : B) = mconj α β k := rfl

end Conj

/-! ### Words in `β` and `βα`, and their normal form -/

section Words

variable {B : Type*} [Group B]

/-- Milnor's word `β α ^ i₀ · β α ^ i₁ ⋯ β α ^ i_{n-1}`, with each exponent `0` or `1`. -/
def wrd (α β : B) {n : ℕ} (i : Fin n → Fin 2) : B :=
  (List.ofFn (fun k : Fin n => β * α ^ (i k : ℕ))).prod

lemma wrd_zero (α β : B) (i : Fin 0 → Fin 2) : wrd α β i = 1 := by simp [wrd]

lemma wrd_succ (α β : B) {n : ℕ} (i : Fin (n + 1) → Fin 2) :
    wrd α β i = (β * α ^ (i 0 : ℕ)) * wrd α β (fun k : Fin n => i k.succ) := by
  simp [wrd, List.ofFn_succ]

/-- Milnor's normal form: `β α^{i₀} ⋯ β α^{i_{n-1}} = α_1^{i₀} ⋯ α_n^{i_{n-1}} β^n`, stated
conjugated by `β ^ d` so that the induction goes through. -/
lemma wrd_eq {A : Subgroup B} [A.Normal] [IsMulCommutative A] {α : B} (hα : α ∈ A) (β : B) :
    ∀ (n : ℕ) (i : Fin n → Fin 2) (d : ℤ),
      β ^ d * wrd α β i * β ^ (-d)
        = ((∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1 + d) ^ (i k : ℕ) : A) : B) * β ^ n := by
  intro n
  induction n with
  | zero =>
      intro i d
      rw [wrd_zero]
      simp [zpow_neg]
  | succ n ih =>
      intro i d
      have hIH := ih (fun k : Fin n => i k.succ) (d + 1)
      rw [wrd_succ, Fin.prod_univ_succ]
      have hidx : ∀ k : Fin n, ((((k.succ : Fin (n + 1)) : ℕ) : ℤ) + 1 + d)
          = (((k : ℕ) : ℤ) + 1 + (d + 1)) := by
        intro k
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        ring
      simp only [hidx]
      have h0 : ((((0 : Fin (n + 1)) : ℕ) : ℤ) + 1 + d) = d + 1 := by
        simp only [Fin.val_zero, Nat.cast_zero, zero_add]
        ring
      rw [h0, Subgroup.coe_mul, Subgroup.coe_pow, coe_mconjA]
      have hpow : mconj α β (d + 1) ^ (i 0 : ℕ) = β ^ (d + 1) * α ^ (i 0 : ℕ) * β ^ (-(d + 1)) :=
        mconj_pow α β (d + 1) (i 0 : ℕ)
      set P : A := ∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1 + (d + 1)) ^ (i k.succ : ℕ)
        with hP
      set W : B := wrd α β (fun k : Fin n => i k.succ) with hW
      set c : B := α ^ (i 0 : ℕ) with hc
      calc β ^ d * (β * c * W) * β ^ (-d)
          = β ^ (d + 1) * c * β ^ (-(d + 1)) *
              (β ^ (d + 1) * W * β ^ (-(d + 1))) * β := by group
        _ = β ^ (d + 1) * c * β ^ (-(d + 1)) * ((P : B) * β ^ n) * β := by rw [hIH]
        _ = mconj α β (d + 1) ^ (i 0 : ℕ) * (P : B) * β ^ (n + 1) := by
              rw [hpow, pow_succ]; simp only [mul_assoc]

/-! ### Step 1: without exponential growth, two words must collide -/

lemma wrd_mem_wordBall {α β : B} (S : Finset B) (hβ : β ∈ S) (hβα : β * α ∈ S) {n : ℕ}
    (i : Fin n → Fin 2) : wrd α β i ∈ wordBall (S : Set B) n := by
  refine ⟨List.ofFn (fun k : Fin n => β * α ^ (i k : ℕ)), by simp, ?_, rfl⟩
  intro y hy
  rw [List.mem_ofFn'] at hy
  obtain ⟨k, rfl⟩ := hy
  refine Or.inl ?_
  dsimp only
  have hlt := (i k).isLt
  have h2 : (i k : ℕ) = 0 ∨ (i k : ℕ) = 1 := by omega
  rcases h2 with h2 | h2
  · rw [h2]; simpa using hβ
  · rw [h2]; simpa using hβα

lemma two_pow_le_card_wordBall' {α β : B} (S : Finset B) (hβ : β ∈ S) (hβα : β * α ∈ S) (n : ℕ)
    (hinj : Function.Injective (fun i : Fin n → Fin 2 => wrd α β i)) :
    2 ^ n ≤ Nat.card (wordBall (S : Set B) n) := by
  classical
  have hfin : Finite (wordBall (S : Set B) n) := (wordBall_finite S n).to_subtype
  let f : (Fin n → Fin 2) → wordBall (S : Set B) n :=
    fun i => ⟨wrd α β i, wrd_mem_wordBall S hβ hβα i⟩
  have hfinj : Function.Injective f := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hcard := Nat.card_le_card_of_injective f hfinj
  simpa using hcard

lemma exists_not_injective [Group.FG B] (h : ¬ HasExponentialGrowth B) (α β : B) :
    ∃ n : ℕ, ¬ Function.Injective (fun i : Fin n → Fin 2 => wrd α β i) := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  obtain ⟨S₀, hS₀⟩ := Group.FG.out (G := B)
  refine ⟨insert β (insert (β * α) S₀), ?_, 2, by norm_num, ?_⟩
  · refine eq_top_iff.mpr ?_
    rw [← hS₀]
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx ⊢
    tauto
  · intro n
    have hn := two_pow_le_card_wordBall' (α := α) (β := β) (insert β (insert (β * α) S₀))
      (by simp) (by simp) n (hcon n)
    have hc : ((2 ^ n : ℕ) : ℝ)
        ≤ (Nat.card (wordBall ((insert β (insert (β * α) S₀) : Finset B) : Set B) n) : ℝ) :=
      Nat.cast_le.mpr hn
    simpa using hc

end Words

/-! ### Step 3: the relation among the conjugates -/

section Relation

variable {B : Type*} [Group B]

/-- From the failure of injectivity we extract a nontrivial relation `∏ α_{k+1} ^ e k = 1`
with all exponents in `{-1, 0, 1}`. -/
lemma exists_relation [Group.FG B] {A : Subgroup B} [A.Normal] [IsMulCommutative A] {α : B}
    (hα : α ∈ A) (β : B) (h : ¬ HasExponentialGrowth B) :
    ∃ (n : ℕ) (e : Fin n → ℤ), (∀ k, e k = -1 ∨ e k = 0 ∨ e k = 1) ∧ (∃ k, e k ≠ 0) ∧
      (∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (e k) = 1) := by
  classical
  obtain ⟨n, hn⟩ := exists_not_injective h α β
  rw [Function.not_injective_iff] at hn
  obtain ⟨i, j, hij, hne⟩ := hn
  refine ⟨n, fun k => ((i k : ℕ) : ℤ) - ((j k : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro k
    dsimp only
    have h1 := (i k).isLt
    have h2 := (j k).isLt
    omega
  · by_contra hc
    push Not at hc
    apply hne
    funext k
    have hk := hc k
    exact Fin.ext (by omega)
  · have hi := wrd_eq hα β n i 0
    have hj := wrd_eq hα β n j 0
    simp only [zpow_zero, one_mul, neg_zero, mul_one, add_zero] at hi hj
    have hPP : ((∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (i k : ℕ) : A) : B)
             = ((∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (j k : ℕ) : A) : B) :=
      mul_right_cancel (hi.symm.trans (hij.trans hj))
    have hPA : (∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (i k : ℕ) : A)
             = (∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (j k : ℕ) : A) :=
      Subtype.ext hPP
    have hsplit : (∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^
            (((i k : ℕ) : ℤ) - ((j k : ℕ) : ℤ)))
        = (∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (i k : ℕ)) *
          (∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (j k : ℕ))⁻¹ := by
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro k _
      rw [zpow_sub, zpow_natCast, zpow_natCast]
    rw [hsplit, hPA, mul_inv_cancel]

/-- From the relation, the conjugate at an index `r` where `e r = ±1` lies in the subgroup
generated by the other conjugates occurring in the relation. -/
lemma mconj_mem_closure_of_rel {A : Subgroup B} [A.Normal] [IsMulCommutative A] {α : B}
    (hα : α ∈ A) (β : B) {n : ℕ} (e : Fin n → ℤ)
    (hrel : ∏ k : Fin n, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (e k) = 1)
    (r : Fin n) (hr : e r = 1 ∨ e r = -1) (X : Set ℤ)
    (hX : ∀ k : Fin n, k ≠ r → e k ≠ 0 → (((k : ℕ) : ℤ) + 1) ∈ X) :
    mconj α β (((r : ℕ) : ℤ) + 1) ∈ Subgroup.closure (mconj α β '' X) := by
  classical
  set N : Subgroup B := Subgroup.closure (mconj α β '' X) with hN
  set M : Subgroup A := N.comap A.subtype with hM
  have hprod : (∏ k ∈ Finset.univ.erase r, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (e k)) ∈ M := by
    refine Subgroup.prod_mem _ ?_
    intro k hk
    have hkr : k ≠ r := Finset.ne_of_mem_erase hk
    by_cases hek : e k = 0
    · simp [hek]
    · refine Subgroup.zpow_mem _ ?_ _
      have hmem : mconj α β (((k : ℕ) : ℤ) + 1) ∈ N :=
        Subgroup.subset_closure ⟨_, hX k hkr hek, rfl⟩
      simpa [hM, Subgroup.mem_subgroupOf] using hmem
  have hsplit := Finset.mul_prod_erase Finset.univ
    (fun k : Fin n => mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (e k)) (Finset.mem_univ r)
  rw [hrel] at hsplit
  have hinv : mconjA hα β (((r : ℕ) : ℤ) + 1) ^ (e r)
      = (∏ k ∈ Finset.univ.erase r, mconjA hα β (((k : ℕ) : ℤ) + 1) ^ (e k))⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hsplit
  have hmem : mconjA hα β (((r : ℕ) : ℤ) + 1) ^ (e r) ∈ M := by
    rw [hinv]; exact Subgroup.inv_mem _ hprod
  have hmem' : mconjA hα β (((r : ℕ) : ℤ) + 1) ∈ M := by
    rcases hr with hr | hr
    · rwa [hr, zpow_one] at hmem
    · rw [hr, zpow_neg, zpow_one] at hmem
      simpa using Subgroup.inv_mem _ hmem
  simpa [hM, Subgroup.mem_subgroupOf] using hmem'

end Relation

/-! ### Step 4: the subgroup generated by the conjugates -/

section Fg

variable {B : Type*} [Group B]

/-- Conjugating by `β` shifts indices up by one. -/
lemma conj_closure_succ (α β : B) (X Y : Set ℤ)
    (hXY : ∀ k ∈ X, mconj α β (k + 1) ∈ Subgroup.closure (mconj α β '' Y)) {x : B}
    (hx : x ∈ Subgroup.closure (mconj α β '' X)) :
    β * x * β⁻¹ ∈ Subgroup.closure (mconj α β '' Y) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [← mconj_succ]
      exact hXY k hk
  | one => simp
  | mul y z _ _ ihy ihz =>
      have hyz : β * (y * z) * β⁻¹ = (β * y * β⁻¹) * (β * z * β⁻¹) := by group
      rw [hyz]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
      have hy' : β * y⁻¹ * β⁻¹ = (β * y * β⁻¹)⁻¹ := by group
      rw [hy']
      exact Subgroup.inv_mem _ ihy

/-- Conjugating by `β⁻¹` shifts indices down by one. -/
lemma conj_closure_pred (α β : B) (X Y : Set ℤ)
    (hXY : ∀ k ∈ X, mconj α β (k - 1) ∈ Subgroup.closure (mconj α β '' Y)) {x : B}
    (hx : x ∈ Subgroup.closure (mconj α β '' X)) :
    β⁻¹ * x * β ∈ Subgroup.closure (mconj α β '' Y) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [← mconj_pred]
      exact hXY k hk
  | one => simp
  | mul y z _ _ ihy ihz =>
      have hyz : β⁻¹ * (y * z) * β = (β⁻¹ * y * β) * (β⁻¹ * z * β) := by group
      rw [hyz]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
      have hy' : β⁻¹ * y⁻¹ * β = (β⁻¹ * y * β)⁻¹ := by group
      rw [hy']
      exact Subgroup.inv_mem _ ihy


/-- Step 4: if the conjugate at the top of the window lies in the subgroup generated by the
window minus its top, and symmetrically at the bottom, then all conjugates lie in the subgroup
generated by the window, which is therefore finitely generated. -/
lemma fg_closure_range_mconj (α β : B) (P Q : ℤ) (hPQ : P ≤ Q)
    (htop : mconj α β Q ∈ Subgroup.closure (mconj α β '' Set.Icc P (Q - 1)))
    (hbot : mconj α β P ∈ Subgroup.closure (mconj α β '' Set.Icc (P + 1) Q)) :
    (Subgroup.closure (Set.range (mconj α β))).FG := by
  classical
  have hup : ∀ x ∈ Subgroup.closure (mconj α β '' Set.Icc P Q),
      β * x * β⁻¹ ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro x hx
    refine conj_closure_succ α β (Set.Icc P Q) (Set.Icc P Q) ?_ hx
    intro k hk
    rw [Set.mem_Icc] at hk
    by_cases hkQ : k = Q
    · rw [hkQ, mconj_succ]
      refine conj_closure_succ α β (Set.Icc P (Q - 1)) (Set.Icc P Q) ?_ htop
      intro m hm
      rw [Set.mem_Icc] at hm
      exact Subgroup.subset_closure ⟨m + 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Subgroup.subset_closure ⟨k + 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  have hdown : ∀ x ∈ Subgroup.closure (mconj α β '' Set.Icc P Q),
      β⁻¹ * x * β ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro x hx
    refine conj_closure_pred α β (Set.Icc P Q) (Set.Icc P Q) ?_ hx
    intro k hk
    rw [Set.mem_Icc] at hk
    by_cases hkP : k = P
    · rw [hkP, mconj_pred]
      refine conj_closure_pred α β (Set.Icc (P + 1) Q) (Set.Icc P Q) ?_ hbot
      intro m hm
      rw [Set.mem_Icc] at hm
      exact Subgroup.subset_closure ⟨m - 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Subgroup.subset_closure ⟨k - 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  have hbase : mconj α β P ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) :=
    Subgroup.subset_closure ⟨P, Set.mem_Icc.mpr ⟨le_refl P, hPQ⟩, rfl⟩
  have hshift : ∀ j : ℤ, mconj α β (P + j) ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ i ih =>
        have hEq : P + ((i : ℤ) + 1) = (P + (i : ℤ)) + 1 := by ring
        rw [hEq, mconj_succ]
        exact hup _ ih
    | pred i ih =>
        have hEq : P + (-(i : ℤ) - 1) = (P + -(i : ℤ)) - 1 := by ring
        rw [hEq, mconj_pred]
        exact hdown _ ih
  have hall : ∀ k : ℤ, mconj α β k ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro k
    have hk := hshift (k - P)
    simpa using hk
  have heq : Subgroup.closure (Set.range (mconj α β))
      = Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    refine le_antisymm ?_ (Subgroup.closure_mono ?_)
    · rw [Subgroup.closure_le]
      rintro x ⟨k, rfl⟩
      exact hall k
    · rintro x ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
  rw [heq]
  refine ⟨(Finset.Icc P Q).image (mconj α β), ?_⟩
  rw [Finset.coe_image, Finset.coe_Icc]

end Fg

/-! ### Milnor's Lemma 1 -/

/-- Milnor, Lemma 1 (p. 447): if `B` does not have exponential growth, then for each `α ∈ A`
and `β ∈ B` the set of all conjugates `β ^ k * α * β ^ (-k)`, `k ∈ ℤ`, spans a finitely
generated subgroup. -/
theorem fg_closure_zpow_conj_of_not_hasExponentialGrowth' {B : Type*} [Group B] [Group.FG B]
    (A : Subgroup B) [A.Normal] [IsMulCommutative A] (h : ¬ Chou.HasExponentialGrowth B)
    (α : B) (hα : α ∈ A) (β : B) :
    (Subgroup.closure {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)}).FG := by
  classical
  have hset : {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)} = Set.range (mconj α β) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  rw [hset]
  obtain ⟨n, e, hrange, ⟨k₀, hk₀⟩, hrel⟩ := exists_relation hα β h
  have hTne : (Finset.univ.filter (fun k : Fin n => e k ≠ 0)).Nonempty :=
    ⟨k₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk₀⟩⟩
  obtain ⟨p, hpe, hpmin⟩ : ∃ p : Fin n, e p ≠ 0 ∧ ∀ k : Fin n, e k ≠ 0 → p ≤ k := by
    refine ⟨(Finset.univ.filter (fun k : Fin n => e k ≠ 0)).min' hTne, ?_, ?_⟩
    · have hm := Finset.min'_mem _ hTne
      rw [Finset.mem_filter] at hm
      exact hm.2
    · intro k hk
      exact Finset.min'_le _ k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  obtain ⟨q, hqe, hqmax⟩ : ∃ q : Fin n, e q ≠ 0 ∧ ∀ k : Fin n, e k ≠ 0 → k ≤ q := by
    refine ⟨(Finset.univ.filter (fun k : Fin n => e k ≠ 0)).max' hTne, ?_, ?_⟩
    · have hm := Finset.max'_mem _ hTne
      rw [Finset.mem_filter] at hm
      exact hm.2
    · intro k hk
      exact Finset.le_max' _ k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  have hrq : e q = 1 ∨ e q = -1 := by
    rcases hrange q with hh | hh | hh
    · exact Or.inr hh
    · exact absurd hh hqe
    · exact Or.inl hh
  have hrp : e p = 1 ∨ e p = -1 := by
    rcases hrange p with hh | hh | hh
    · exact Or.inr hh
    · exact absurd hh hpe
    · exact Or.inl hh
  have hpq : ((p : ℕ)) ≤ ((q : ℕ)) := Fin.le_def.mp (hpmin q hqe)
  refine fg_closure_range_mconj α β (((p : ℕ) : ℤ) + 1) (((q : ℕ) : ℤ) + 1) (by omega) ?_ ?_
  · refine mconj_mem_closure_of_rel hα β e hrel q hrq _ ?_
    intro k hkq hek
    have h1 : ((p : ℕ)) ≤ ((k : ℕ)) := Fin.le_def.mp (hpmin k hek)
    have h2 : ((k : ℕ)) ≤ ((q : ℕ)) := Fin.le_def.mp (hqmax k hek)
    have h3 : ((k : ℕ)) ≠ ((q : ℕ)) := fun hc => hkq (Fin.ext hc)
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
  · refine mconj_mem_closure_of_rel hα β e hrel p hrp _ ?_
    intro k hkp hek
    have h1 : ((p : ℕ)) ≤ ((k : ℕ)) := Fin.le_def.mp (hpmin k hek)
    have h2 : ((k : ℕ)) ≤ ((q : ℕ)) := Fin.le_def.mp (hqmax k hek)
    have h3 : ((k : ℕ)) ≠ ((p : ℕ)) := fun hc => hkp (Fin.ext hc)
    exact Set.mem_Icc.mpr ⟨by omega, by omega⟩

end Lib
end Milnor

open Milnor

theorem solution {B : Type*} [Group B] [Group.FG B]
    (A : Subgroup B) [A.Normal] [IsMulCommutative A] (h : ¬ Chou.HasExponentialGrowth B)
    (α : B) (hα : α ∈ A) (β : B) :
    (Subgroup.closure {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)}).FG :=
  Milnor.Lib.fg_closure_zpow_conj_of_not_hasExponentialGrowth' A h α hα β
