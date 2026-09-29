-- Prove2me | solution 1 for GroupFiniteness.fg_closure_zpow_conj_of_not_hasExponentialGrowth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T12:38:52.021897+00:00
-- url     : https://prove2.me/submissions/59a0f757-c27d-414a-8aec-7f15a7e2e86a

import Definitions.Def_Chou_Growth
import Mathlib

/-!
# Milnor's Lemma 1 without the abelian hypothesis, and the cyclic-quotient assembly

Milnor, *Growth of finitely generated solvable groups*, J. Differential Geometry 2 (1968)
447–449, Lemma 1; Rosenblatt, *Invariant measures and growth conditions*, Trans. Amer. Math.
Soc. 193 (1974) 42–43, Lemma 4.8; Chou, *Elementary amenable groups*, Illinois J. Math. 24
(1980) 400, "(Milnor's Lemmas 1 and 2 are stated for abelian `A`.  The fact that `A` is abelian
is only used on line 10 of p. 448.  This can be avoided because what is needed is to express
`α_m` as a word in `α_1, …, α_{m-1}`.)"

The first half of this file proves Milnor's Lemma 1 with no abelian hypothesis — indeed with no
ambient normal subgroup at all: in a finitely generated group without exponential growth, for
every pair `α β` the conjugates `β ^ k * α * β ^ (-k)`, `k ∈ ℤ`, span a finitely generated
subgroup.  Milnor's proof multiplies the relation out in the abelian group `A`; here the
products are ordered products over lists, and the relation is exploited by cancelling the
common prefix and the common suffix of the two words, exactly as Rosenblatt does on p. 43.
-/

namespace Chou
namespace FgFp

open Chou

/-! ### Word balls -/

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

lemma mconj_succ (α β : B) (k : ℤ) : mconj α β (k + 1) = β * mconj α β k * β⁻¹ := by
  simp only [mconj, zpow_neg]
  group

lemma mconj_pred (α β : B) (k : ℤ) : mconj α β (k - 1) = β⁻¹ * mconj α β k * β := by
  simp only [mconj, zpow_neg]
  group

lemma mconj_pow (α β : B) (k : ℤ) (m : ℕ) :
    mconj α β k ^ m = β ^ k * α ^ m * (β ^ k)⁻¹ := by
  simp only [mconj, zpow_neg]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      group

end Conj

/-! ### Milnor's words `β α^{i₀} β α^{i₁} ⋯` and their normal form -/

section Words

variable {B : Type*} [Group B]

/-- Milnor's word `β α^{i 0} · β α^{i 1} ⋯ β α^{i (n-1)}`. -/
def wrd (α β : B) (i : ℕ → ℕ) (n : ℕ) : B :=
  ((List.range n).map (fun k => β * α ^ i k)).prod

/-- The `k`-th factor `α_{k+1} ^ (i k)` of Milnor's product. -/
def mfac (α β : B) (i : ℕ → ℕ) (k : ℕ) : B := mconj α β ((k : ℤ) + 1) ^ i k

/-- The ordered product `∏_{k ∈ L} α_{k+1} ^ (i k)` of Milnor's conjugates. -/
def wseg (α β : B) (i : ℕ → ℕ) (L : List ℕ) : B := (L.map (mfac α β i)).prod

@[simp] lemma wseg_nil (α β : B) (i : ℕ → ℕ) : wseg α β i [] = 1 := rfl

lemma wseg_cons (α β : B) (i : ℕ → ℕ) (k : ℕ) (L : List ℕ) :
    wseg α β i (k :: L) = mconj α β ((k : ℤ) + 1) ^ i k * wseg α β i L := by
  rw [wseg, List.map_cons, List.prod_cons, wseg, mfac]

lemma wseg_append (α β : B) (i : ℕ → ℕ) (L₁ L₂ : List ℕ) :
    wseg α β i (L₁ ++ L₂) = wseg α β i L₁ * wseg α β i L₂ := by
  rw [wseg, List.map_append, List.prod_append, wseg, wseg]

lemma wseg_congr (α β : B) {i j : ℕ → ℕ} {L : List ℕ} (h : ∀ k ∈ L, i k = j k) :
    wseg α β i L = wseg α β j L := by
  rw [wseg, wseg]
  congr 1
  refine List.map_congr_left ?_
  intro k hk
  rw [mfac, mfac, h k hk]

/-- Every ordered product of conjugates with indices in `X` lies in the subgroup they span. -/
lemma wseg_mem_closure (α β : B) (i : ℕ → ℕ) (X : Set ℤ) :
    ∀ L : List ℕ, (∀ k ∈ L, ((k : ℤ) + 1) ∈ X) →
      wseg α β i L ∈ Subgroup.closure (mconj α β '' X) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons k L ih =>
      intro hL
      rw [wseg_cons]
      refine Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _) (ih fun m hm => hL m (by simp [hm]))
      exact Subgroup.subset_closure ⟨(k : ℤ) + 1, hL k (by simp), rfl⟩

/-- Milnor's normal form (p. 448): `β α^{i 0} ⋯ β α^{i (n-1)} = α_1^{i 0} ⋯ α_n^{i (n-1)} β^n`,
with the product on the right an *ordered* product — no commutativity is used. -/
lemma wrd_eq (α β : B) (i : ℕ → ℕ) (n : ℕ) :
    wrd α β i n = wseg α β i (List.range n) * β ^ n := by
  induction n with
  | zero => simp [wrd, wseg]
  | succ n ih =>
      have hz : (β : B) ^ ((n : ℤ) + 1) = β ^ (n + 1) := by
        rw [← zpow_natCast β (n + 1)]
        norm_cast
      have hstep : β ^ n * (β * α ^ i n)
          = mconj α β ((n : ℤ) + 1) ^ i n * β ^ (n + 1) := by
        rw [mconj_pow, hz, pow_succ]
        group
      rw [wrd, List.range_succ, List.map_append, List.prod_append, ← wrd, ih, wseg_append,
        wseg_cons, wseg_nil, mul_one]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [mul_assoc, hstep, ← mul_assoc]

/-- The `2 ^ n` words `β α^{i 0} ⋯ β α^{i (n-1)}` all lie in the ball of radius `n` for any
generating set containing `β` and `β α`. -/
lemma wrd_mem_wordBall {α β : B} (S : Finset B) (hβ : β ∈ S) (hβα : β * α ∈ S) {i : ℕ → ℕ}
    (hi : ∀ k, i k ≤ 1) (n : ℕ) : wrd α β i n ∈ wordBall (S : Set B) n := by
  refine ⟨(List.range n).map (fun k => β * α ^ i k), by simp, ?_, rfl⟩
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨k, -, rfl⟩ := hy
  refine Or.inl ?_
  have h2 : i k = 0 ∨ i k = 1 := by have := hi k; omega
  rcases h2 with h2 | h2
  · rw [h2]; simpa using hβ
  · rw [h2]; simpa using hβα

/-- The extension of `f : Fin n → Fin 2` to a `{0,1}`-valued function on `ℕ`. -/
def ext {n : ℕ} (f : Fin n → Fin 2) : ℕ → ℕ :=
  fun k => if h : k < n then (f ⟨k, h⟩ : ℕ) else 0

lemma ext_le_one {n : ℕ} (f : Fin n → Fin 2) (k : ℕ) : ext f k ≤ 1 := by
  unfold ext
  split
  · exact Nat.lt_succ_iff.mp (f _).isLt
  · exact Nat.zero_le _

lemma ext_eq_zero {n : ℕ} (f : Fin n → Fin 2) {k : ℕ} (hk : n ≤ k) : ext f k = 0 := by
  unfold ext
  rw [dif_neg (by omega)]

lemma ext_injective {n : ℕ} : Function.Injective (ext (n := n)) := by
  intro f g hfg
  funext k
  have h := congrFun hfg (k : ℕ)
  unfold ext at h
  rw [dif_pos k.isLt, dif_pos k.isLt] at h
  exact Fin.ext (by simpa using h)

end Words

/-! ### Step 1: without exponential growth two of Milnor's words must collide -/

section Collision

variable {B : Type*} [Group B]

lemma two_pow_le_card_wordBall {α β : B} (S : Finset B) (hβ : β ∈ S) (hβα : β * α ∈ S) (n : ℕ)
    (hinj : Function.Injective (fun f : Fin n → Fin 2 => wrd α β (ext f) n)) :
    2 ^ n ≤ Nat.card (wordBall (S : Set B) n) := by
  classical
  have hfin : Finite (wordBall (S : Set B) n) := (wordBall_finite S n).to_subtype
  let F : (Fin n → Fin 2) → wordBall (S : Set B) n :=
    fun f => ⟨wrd α β (ext f) n, wrd_mem_wordBall S hβ hβα (ext_le_one f) n⟩
  have hFinj : Function.Injective F := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hcard := Nat.card_le_card_of_injective F hFinj
  simpa using hcard

/-- Milnor's counting argument: if `B` has no exponential growth, then for some `n` two of the
`2 ^ n` words `β α^{i 0} ⋯ β α^{i (n-1)}` coincide. -/
lemma exists_not_injective [Group.FG B] (h : ¬ HasExponentialGrowth B) (α β : B) :
    ∃ n : ℕ, ¬ Function.Injective (fun f : Fin n → Fin 2 => wrd α β (ext f) n) := by
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
    have hn := two_pow_le_card_wordBall (α := α) (β := β) (insert β (insert (β * α) S₀))
      (by simp) (by simp) n (hcon n)
    have hc : ((2 ^ n : ℕ) : ℝ)
        ≤ (Nat.card (wordBall ((insert β (insert (β * α) S₀) : Finset B) : Set B) n) : ℝ) :=
      Nat.cast_le.mpr hn
    simpa using hc

end Collision

/-! ### Step 2: exploiting the relation, without commutativity

From `wseg u L = wseg v L` with `u ≠ v` one solves for the conjugate at the last index where
`u` and `v` differ — Chou's `α_m^{j_m - i_m} = (α_1^{i_1} ⋯ α_{m-1}^{i_{m-1}})^{-1} ·
α_1^{j_1} ⋯ α_{m-1}^{j_{m-1}}` (p. 400) — and, symmetrically, at the first such index. -/

section Relation

variable {B : Type*} [Group B]

/-- Solving for the conjugate at the right-hand end of the relation. -/
lemma mconj_mem_closure_last (α β : B) (u v : ℕ → ℕ) (L : List ℕ) (X : Set ℤ)
    (hL : ∀ k ∈ L, ((k : ℤ) + 1) ∈ X) (r : ℕ) (hu : u r = 1) (hv : v r = 0)
    (h : wseg α β u (L ++ [r]) = wseg α β v (L ++ [r])) :
    mconj α β ((r : ℤ) + 1) ∈ Subgroup.closure (mconj α β '' X) := by
  simp only [wseg_append, wseg_cons, wseg_nil, mul_one, hu, hv, pow_one, pow_zero] at h
  have hm : mconj α β ((r : ℤ) + 1) = (wseg α β u L)⁻¹ * wseg α β v L := by
    rw [← h]; group
  rw [hm]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (wseg_mem_closure α β u X L hL))
    (wseg_mem_closure α β v X L hL)

/-- Solving for the conjugate at the left-hand end of the relation. -/
lemma mconj_mem_closure_head (α β : B) (u v : ℕ → ℕ) (L : List ℕ) (X : Set ℤ)
    (hL : ∀ k ∈ L, ((k : ℤ) + 1) ∈ X) (r : ℕ) (hu : u r = 1) (hv : v r = 0)
    (h : wseg α β u (r :: L) = wseg α β v (r :: L)) :
    mconj α β ((r : ℤ) + 1) ∈ Subgroup.closure (mconj α β '' X) := by
  simp only [wseg_cons, hu, hv, pow_one, pow_zero, one_mul] at h
  have hm : mconj α β ((r : ℤ) + 1) = wseg α β v L * (wseg α β u L)⁻¹ := by
    rw [← h]; group
  rw [hm]
  exact Subgroup.mul_mem _ (wseg_mem_closure α β v X L hL)
    (Subgroup.inv_mem _ (wseg_mem_closure α β u X L hL))

end Relation

/-! ### Step 3: from a window of conjugates to all of them -/

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

/-- If the conjugate at the top of a window lies in the subgroup generated by the window minus
its top, and symmetrically at the bottom, then all conjugates lie in the subgroup generated by
the window, which is therefore finitely generated. -/
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

/-! ### Milnor's Lemma 1, with no abelian hypothesis -/

/-- **Milnor's Lemma 1 (p. 447) without the abelian hypothesis.**  In a finitely generated group
without exponential growth, for every `α` and `β` the conjugates `β ^ k * α * β ^ (-k)`,
`k ∈ ℤ`, span a finitely generated subgroup.

Milnor's proof of the last step ("it follows that `α_m` can be expressed as a word in
`α_1, …, α_{m-1}`") uses that `A` is abelian only to collect the two sides of the relation into
one product; Chou (p. 400) observes that all that is needed is to solve the relation
`α_1^{i_1} ⋯ α_m^{i_m} = α_1^{j_1} ⋯ α_m^{j_m}` for `α_m`, and Rosenblatt (p. 43) writes the
proof that way.  Here `wseg` is that ordered product, and the relation is solved at its last
and at its first index of disagreement. -/
theorem fg_closure_range_mconj_of_not_hasExponentialGrowth {B : Type*} [Group B] [Group.FG B]
    (h : ¬ Chou.HasExponentialGrowth B) (α β : B) :
    (Subgroup.closure (Set.range (mconj α β))).FG := by
  classical
  obtain ⟨n, hn⟩ := exists_not_injective h α β
  rw [Function.not_injective_iff] at hn
  obtain ⟨f, g, hfg, hne⟩ := hn
  set u : ℕ → ℕ := ext f with hudef
  set v : ℕ → ℕ := ext g with hvdef
  have huv : u ≠ v := fun hc => hne (ext_injective hc)
  have hu1 : ∀ k, u k ≤ 1 := ext_le_one f
  have hv1 : ∀ k, v k ≤ 1 := ext_le_one g
  have hzeroU : ∀ k, n ≤ k → u k = 0 := fun k hk => ext_eq_zero f hk
  have hzeroV : ∀ k, n ≤ k → v k = 0 := fun k hk => ext_eq_zero g hk
  set D : Finset ℕ := (Finset.range n).filter (fun k => u k ≠ v k) with hDdef
  have hDne : D.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    apply huv
    funext k
    by_cases hk : k < n
    · by_contra hne'
      have hmem : k ∈ D := by rw [hDdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hne'⟩
      rw [hc] at hmem
      simp at hmem
    · rw [hzeroU k (by omega), hzeroV k (by omega)]
  set p : ℕ := D.min' hDne with hpdef
  set q : ℕ := D.max' hDne with hqdef
  have hpD : p ∈ D := D.min'_mem hDne
  have hqD : q ∈ D := D.max'_mem hDne
  have hpq : p ≤ q := D.min'_le q hqD
  have hqn : q < n := Finset.mem_range.mp (Finset.mem_filter.mp hqD).1
  have hupne : u p ≠ v p := (Finset.mem_filter.mp hpD).2
  have huqne : u q ≠ v q := (Finset.mem_filter.mp hqD).2
  have hagree : ∀ k, k < n → (k < p ∨ q < k) → u k = v k := by
    intro k hk hc
    by_contra hne'
    have hmem : k ∈ D := by rw [hDdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hne'⟩
    rcases hc with hc | hc
    · exact absurd (D.min'_le k hmem) (by omega)
    · exact absurd (D.le_max' k hmem) (by omega)
  -- the relation between the two ordered products
  have hrel : wseg α β u (List.range n) = wseg α β v (List.range n) := by
    have h1 := wrd_eq α β u n
    have h2 := wrd_eq α β v n
    rw [h1, h2] at hfg
    exact mul_right_cancel hfg
  -- cut the common prefix and the common suffix
  have e1 : List.range' p (q + 1 - p) ++ List.range' (q + 1) (n - (q + 1))
      = List.range' p (n - p) := by
    have h0 := List.range'_append_1 (s := p) (m := q + 1 - p) (n := n - (q + 1))
    rw [show p + (q + 1 - p) = q + 1 from by omega,
      show q + 1 - p + (n - (q + 1)) = n - p from by omega] at h0
    exact h0
  have e2 : List.range' 0 p ++ List.range' p (n - p) = List.range' 0 n := by
    have h0 := List.range'_append_1 (s := 0) (m := p) (n := n - p)
    rw [show 0 + p = p from by omega, show p + (n - p) = n from by omega] at h0
    exact h0
  have hsplit : List.range n
      = List.range' 0 p ++ (List.range' p (q + 1 - p) ++ List.range' (q + 1) (n - (q + 1))) := by
    rw [List.range_eq_range', ← e2, e1]
  have hmemA : ∀ k ∈ List.range' 0 p, u k = v k := by
    intro k hk
    rw [List.mem_range'_1] at hk
    exact hagree k (by omega) (Or.inl (by omega))
  have hmemE : ∀ k ∈ List.range' (q + 1) (n - (q + 1)), u k = v k := by
    intro k hk
    rw [List.mem_range'_1] at hk
    exact hagree k (by omega) (Or.inr (by omega))
  have hM : wseg α β u (List.range' p (q + 1 - p))
      = wseg α β v (List.range' p (q + 1 - p)) := by
    rw [hsplit, wseg_append, wseg_append, wseg_append, wseg_append,
      wseg_congr α β hmemA, wseg_congr α β hmemE] at hrel
    exact mul_right_cancel (mul_left_cancel hrel)
  -- the two ends of the relation
  have hMtop : List.range' p (q + 1 - p) = List.range' p (q - p) ++ [q] := by
    have h0 := List.range'_concat (s := p) (n := q - p) (step := 1)
    rw [show p + 1 * (q - p) = q from by omega] at h0
    rw [show q + 1 - p = q - p + 1 from by omega]
    exact h0
  have hMbot : List.range' p (q + 1 - p) = p :: List.range' (p + 1) (q - p) := by
    rw [show q + 1 - p = q - p + 1 from by omega]
    rfl
  have htop : mconj α β ((q : ℤ) + 1)
      ∈ Subgroup.closure (mconj α β '' Set.Icc ((p : ℤ) + 1) (((q : ℤ) + 1) - 1)) := by
    have hL : ∀ k ∈ List.range' p (q - p),
        ((k : ℤ) + 1) ∈ Set.Icc ((p : ℤ) + 1) (((q : ℤ) + 1) - 1) := by
      intro k hk
      rw [List.mem_range'_1] at hk
      have h1 : p ≤ k := hk.1
      have h2 : k < q := by omega
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    rcases Nat.lt_or_ge (u q) (v q) with hc | hc
    · have h1 : v q = 1 := by have := hv1 q; omega
      have h0 : u q = 0 := by omega
      exact mconj_mem_closure_last α β v u _ _ hL q h1 h0 (by rw [← hMtop]; exact hM.symm)
    · have h1 : u q = 1 := by have := hu1 q; omega
      have h0 : v q = 0 := by omega
      exact mconj_mem_closure_last α β u v _ _ hL q h1 h0 (by rw [← hMtop]; exact hM)
  have hbot : mconj α β ((p : ℤ) + 1)
      ∈ Subgroup.closure (mconj α β '' Set.Icc (((p : ℤ) + 1) + 1) ((q : ℤ) + 1)) := by
    have hL : ∀ k ∈ List.range' (p + 1) (q - p),
        ((k : ℤ) + 1) ∈ Set.Icc (((p : ℤ) + 1) + 1) ((q : ℤ) + 1) := by
      intro k hk
      rw [List.mem_range'_1] at hk
      have h1 : p + 1 ≤ k := hk.1
      have h2 : k ≤ q := by omega
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    rcases Nat.lt_or_ge (u p) (v p) with hc | hc
    · have h1 : v p = 1 := by have := hv1 p; omega
      have h0 : u p = 0 := by omega
      exact mconj_mem_closure_head α β v u _ _ hL p h1 h0 (by rw [← hMbot]; exact hM.symm)
    · have h1 : u p = 1 := by have := hu1 p; omega
      have h0 : v p = 0 := by omega
      exact mconj_mem_closure_head α β u v _ _ hL p h1 h0 (by rw [← hMbot]; exact hM)
  exact fg_closure_range_mconj α β ((p : ℤ) + 1) ((q : ℤ) + 1) (by omega) htop hbot

/-- Milnor's Lemma 1 in the shape in which it is stated on the platform, with no abelian
hypothesis on any ambient normal subgroup. -/
theorem fg_closure_zpow_conj {B : Type*} [Group B] [Group.FG B]
    (h : ¬ Chou.HasExponentialGrowth B) (α β : B) :
    (Subgroup.closure {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)}).FG := by
  have hset : {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)} = Set.range (mconj α β) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  rw [hset]
  exact fg_closure_range_mconj_of_not_hasExponentialGrowth h α β

end FgFp
end Chou

/-! ### Milnor's lemma: the kernel of a surjection onto `ℤ` is finitely generated

This is the assembly that Milnor's Lemmas 1 and 2 are *for*.  Milnor's own assembly (p. 449)
writes an arbitrary conjugate of `α_j` as `(β₁^{i₁} ⋯ β_p^{i_p})⁻¹ α_j (β₁^{i₁} ⋯ β_p^{i_p})`,
which uses both that the quotient is polycyclic and that `A` is abelian (so that the `A`-part of
the conjugator acts trivially).  Neither is available here, so the assembly below is the one
that needs neither: a finite generating set of `B` is corrected by powers of `β` into a finite
subset of `A`, Lemma 1 is applied to each correction, and the resulting finitely generated
`β`-invariant subgroup `H ≤ A` satisfies `H · ⟨β⟩ = B`, whence `H = A`.  No finite presentation
of the quotient is needed. -/

namespace Chou
namespace FgFp

open Chou

section Cyclic

variable {B : Type*} [Group B]

@[simp] lemma mconj_zero' (α β : B) : mconj α β 0 = α := by simp [mconj]

/-- Conjugation by all powers of `β`, from conjugation by `β` and by `β⁻¹`. -/
lemma zpow_conj_mem {H : Subgroup B} {β : B} (hup : ∀ x ∈ H, β * x * β⁻¹ ∈ H)
    (hdown : ∀ x ∈ H, β⁻¹ * x * β ∈ H) :
    ∀ (k : ℤ) (x : B), x ∈ H → β ^ k * x * (β ^ k)⁻¹ ∈ H := by
  intro k
  induction k using Int.induction_on with
  | zero => intro x hx; simpa using hx
  | succ i ih =>
      intro x hx
      have he : β ^ ((i : ℤ) + 1) * x * (β ^ ((i : ℤ) + 1))⁻¹
          = β * (β ^ (i : ℤ) * x * (β ^ (i : ℤ))⁻¹) * β⁻¹ := by
        rw [zpow_add, zpow_one]; group
      rw [he]
      exact hup _ (ih x hx)
  | pred i ih =>
      intro x hx
      have he : β ^ (-(i : ℤ) - 1) * x * (β ^ (-(i : ℤ) - 1))⁻¹
          = β⁻¹ * (β ^ (-(i : ℤ)) * x * (β ^ (-(i : ℤ)))⁻¹) * β := by
        rw [zpow_sub, zpow_one]; group
      rw [he]
      exact hdown _ (ih x hx)

/-- Lemma 1, applied to each member of a finite set at once. -/
lemma exists_finset_closure_biUnion [Group.FG B] (h : ¬ HasExponentialGrowth B) (β : B) :
    ∀ T : Finset B, ∃ U : Finset B, Subgroup.closure (U : Set B)
      = Subgroup.closure (⋃ t ∈ (T : Set B), Set.range (mconj t β)) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert t T ht ih =>
      obtain ⟨U, hU⟩ := ih
      obtain ⟨V, hV⟩ := fg_closure_range_mconj_of_not_hasExponentialGrowth h t β
      refine ⟨V ∪ U, ?_⟩
      rw [Finset.coe_union, Subgroup.closure_union, hU, hV, Finset.coe_insert,
        Set.biUnion_insert, Subgroup.closure_union]

/-- **Milnor's lemma** (Milnor 1968, Lemma 1 in the form in which it is applied; Grigorchuk's
survey, Lemma 6.2): in a finitely generated group without exponential growth, the kernel of a
homomorphism onto `ℤ` is finitely generated.  No hypothesis of commutativity on the kernel, and
no finite presentation, is needed. -/
theorem fg_ker_of_surjective_int {B : Type*} [Group B] [Group.FG B]
    (h : ¬ Chou.HasExponentialGrowth B) (φ : B →* Multiplicative ℤ)
    (hφ : Function.Surjective φ) : Group.FG φ.ker := by
  classical
  obtain ⟨β, hβ⟩ := hφ (Multiplicative.ofAdd 1)
  have hpow : ∀ k : ℤ, φ (β ^ k) = Multiplicative.ofAdd k := by
    intro k
    rw [map_zpow, hβ, ← ofAdd_zsmul]
    norm_num
  obtain ⟨S, hS⟩ := Group.FG.out (G := B)
  set aa : B → B := fun s => s * (β ^ (Multiplicative.toAdd (φ s)))⁻¹ with haadef
  have haa_mem : ∀ s : B, aa s ∈ φ.ker := by
    intro s
    rw [MonoidHom.mem_ker, haadef]
    simp only [map_mul, map_inv, hpow]
    simp
  have hs_eq : ∀ s : B, s = aa s * β ^ (Multiplicative.toAdd (φ s)) := by
    intro s; rw [haadef]; group
  obtain ⟨U, hU⟩ := exists_finset_closure_biUnion h β (S.image aa)
  set H : Subgroup B := Subgroup.closure (U : Set B) with hHdef
  have hgen : ∀ s ∈ S, ∀ k : ℤ, mconj (aa s) β k ∈ H := by
    intro s hs k
    rw [hU]
    refine Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨aa s, ?_, ⟨k, rfl⟩⟩)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem aa hs)
  -- `H` lies in the kernel
  have hHker : H ≤ φ.ker := by
    rw [hU, Subgroup.closure_le]
    rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨t, ht, k, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht)
    have hc := (MonoidHom.normal_ker φ).conj_mem _ (haa_mem s) (β ^ k)
    simpa [mconj, zpow_neg] using hc
  -- `H` is invariant under conjugation by `β`
  have hup : ∀ x ∈ H, β * x * β⁻¹ ∈ H := by
    intro x hx
    rw [hU] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨t, ht, k, rfl⟩ := hy
        rw [← mconj_succ]
        exact Subgroup.subset_closure (Set.mem_biUnion ht ⟨k + 1, rfl⟩)
    | one => simp
    | mul y z _ _ ihy ihz =>
        have hyz : β * (y * z) * β⁻¹ = (β * y * β⁻¹) * (β * z * β⁻¹) := by group
        rw [hyz]; exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
        have hy' : β * y⁻¹ * β⁻¹ = (β * y * β⁻¹)⁻¹ := by group
        rw [hy']; exact Subgroup.inv_mem _ ihy
  have hdown : ∀ x ∈ H, β⁻¹ * x * β ∈ H := by
    intro x hx
    rw [hU] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨t, ht, k, rfl⟩ := hy
        rw [← mconj_pred]
        exact Subgroup.subset_closure (Set.mem_biUnion ht ⟨k - 1, rfl⟩)
    | one => simp
    | mul y z _ _ ihy ihz =>
        have hyz : β⁻¹ * (y * z) * β = (β⁻¹ * y * β) * (β⁻¹ * z * β) := by group
        rw [hyz]; exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
        have hy' : β⁻¹ * y⁻¹ * β = (β⁻¹ * y * β)⁻¹ := by group
        rw [hy']; exact Subgroup.inv_mem _ ihy
  have hconj := zpow_conj_mem hup hdown
  -- `H` together with `β` generates the whole group
  have htop : Subgroup.closure ((H : Set B) ∪ {β}) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS, Subgroup.closure_le]
    intro s hs
    rw [hs_eq s]
    refine Subgroup.mul_mem _ ?_ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    refine Subgroup.subset_closure (Or.inl ?_)
    have := hgen s (Finset.mem_coe.mp hs) 0
    simpa using this
  -- every element of the group is an element of `H` times a power of `β`
  have hform : ∀ g : B, ∃ x ∈ H, ∃ k : ℤ, g = x * β ^ k := by
    intro g
    have hg : g ∈ Subgroup.closure ((H : Set B) ∪ {β}) := by rw [htop]; trivial
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact ⟨y, hy, 0, by simp⟩
        · rw [Set.mem_singleton_iff] at hy
          exact ⟨1, Subgroup.one_mem _, 1, by simp [hy]⟩
    | one => exact ⟨1, Subgroup.one_mem _, 0, by simp⟩
    | mul y z _ _ ihy ihz =>
        obtain ⟨x₁, hx₁, k₁, rfl⟩ := ihy
        obtain ⟨x₂, hx₂, k₂, rfl⟩ := ihz
        refine ⟨x₁ * (β ^ k₁ * x₂ * (β ^ k₁)⁻¹), Subgroup.mul_mem _ hx₁ (hconj k₁ x₂ hx₂),
          k₁ + k₂, ?_⟩
        rw [zpow_add]
        group
    | inv y _ ihy =>
        obtain ⟨x, hx, k, rfl⟩ := ihy
        refine ⟨β ^ (-k) * x⁻¹ * (β ^ (-k))⁻¹, hconj (-k) x⁻¹ (Subgroup.inv_mem _ hx), -k, ?_⟩
        group
  -- hence the kernel is exactly `H`
  have hker : φ.ker = H := by
    refine le_antisymm ?_ hHker
    intro g hg
    obtain ⟨x, hx, k, rfl⟩ := hform g
    have h1 : φ (β ^ k) = 1 := by
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp (hHker hx)
      have := MonoidHom.mem_ker.mp hg
      rw [map_mul, hx1, one_mul] at this
      exact this
    rw [hpow k] at h1
    have hk : k = 0 := by
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    rw [hk]
    simpa using hx
  rw [Group.fg_iff_subgroup_fg, hker]
  exact ⟨U, rfl⟩

end Cyclic

end FgFp
end Chou

theorem solution {B : Type*} [Group B] [Group.FG B]
    (h : ¬ Chou.HasExponentialGrowth B) (α β : B) :
    (Subgroup.closure {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)}).FG :=
  Chou.FgFp.fg_closure_zpow_conj h α β
