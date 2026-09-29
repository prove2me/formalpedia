-- Prove2me | solution 1 for GrigorchukPak.superpolynomial_and_subexponential_card_wordBall
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T14:28:47.413076+00:00
-- url     : https://prove2.me/submissions/3d6c79d3-aabf-449d-b449-450a0a8ba0d7

import Theorems.Thm_GrigorchukPak_superpolynomial_and_exp_rpow_le_card_wordBall
import Mathlib
import Definitions.Def_Garrido_Grigorchuk
import Theorems.Thm_Garrido_isExponentiallyBounded_grigorchukGroup


/-!
# Grigorchuk–Pak, Lemma 2.1 (Lower Bound Lemma)

Following the Appendix proof: pass to `π(n) = log f(n)`, turn `f(n)^m ≤ C f(Kn)` into the
linear recursion `π(Kn) ≥ m π(n) - log C`, iterate it along `n₀, K n₀, K² n₀, …`, and
interpolate between consecutive powers of `K`.  The additive constant is absorbed by the
shift `a(n) = π(n) - L` with `L = log C / (m - 1)`, which satisfies `a(Kn) ≥ m a(n)` exactly.
-/

namespace GrigorchukPak

end GrigorchukPak


/-!
# Growth of the Grigorchuk group (Grigorchuk–Pak, §§5–6, Exercises 1.3, 1.5)
-/

namespace GrigorchukPak

open Chou

section Ball
variable {G : Type*} [Group G] (S : Set G)

theorem one_mem_wordBall (k : ℕ) : (1 : G) ∈ wordBall S k :=
  ⟨[], by simp, by simp, by simp⟩

theorem wordBall_mono {k k' : ℕ} (h : k ≤ k') : wordBall S k ⊆ wordBall S k' := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

theorem mul_mem_wordBall {x y : G} {a b : ℕ} (hx : x ∈ wordBall S a) (hy : y ∈ wordBall S b) :
    x * y ∈ wordBall S (a + b) := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  obtain ⟨l', hl', hS', rfl⟩ := hy
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · exact hS z h
  · exact hS' z h

theorem inv_mem_wordBall {x : G} {a : ℕ} (hx : x ∈ wordBall S a) : x⁻¹ ∈ wordBall S a := by
  obtain ⟨l, hl, hS, rfl⟩ := hx
  refine ⟨(l.map (·⁻¹)).reverse, by simpa using hl, ?_, by simp [List.prod_inv_reverse]⟩
  intro z hz
  simp only [List.mem_reverse, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases hS w hw with h | h
  · right; simpa using h
  · left; exact h

theorem mem_wordBall_one_of_mem {s : G} (hs : s ∈ S) : s ∈ wordBall S 1 :=
  ⟨[s], by simp, by simp [hs], by simp⟩

/-- `B(k+1) = T₁ · B(k)` where `T₁ = {1} ∪ S ∪ S⁻¹`. -/
theorem mem_wordBall_succ_iff {g : G} {k : ℕ} :
    g ∈ wordBall S (k + 1) ↔ ∃ t : G, (t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S) ∧ ∃ g' ∈ wordBall S k, g = t * g' := by
  constructor
  · rintro ⟨l, hl, hS, rfl⟩
    cases l with
    | nil => exact ⟨1, Or.inl rfl, 1, one_mem_wordBall S k, by simp⟩
    | cons x l =>
      refine ⟨x, Or.inr (hS x (by simp)), l.prod, ⟨l, by simpa using hl, fun z hz => hS z (by simp [hz]), rfl⟩, by simp⟩
  · rintro ⟨t, ht, g', hg', rfl⟩
    rcases ht with rfl | ht
    · simpa using wordBall_mono S (Nat.le_succ k) hg'
    · have : t ∈ wordBall S 1 := ⟨[t], by simp, by simpa using ht, by simp⟩
      simpa [add_comm] using mul_mem_wordBall S this hg'

theorem wordBall_finite (hS : S.Finite) (k : ℕ) : (wordBall S k).Finite := by
  induction k with
  | zero =>
    apply (Set.finite_singleton (1 : G)).subset
    rintro g ⟨l, hl, -, rfl⟩
    simp at hl; simp [hl]
  | succ k ih =>
    have hT : ({t : G | t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S}).Finite := by
      have : {t : G | t = 1 ∨ t ∈ S ∨ t⁻¹ ∈ S} = {1} ∪ S ∪ S⁻¹ := by
        ext t; simp [or_assoc]
      rw [this]; exact ((Set.finite_singleton _).union hS).union hS.inv
    apply (hT.image2 (· * ·) ih).subset
    intro g hg
    obtain ⟨t, ht, g', hg', rfl⟩ := (mem_wordBall_succ_iff S).mp hg
    exact ⟨t, ht, g', hg', rfl⟩

theorem exists_mem_wordBall (hgen : Subgroup.closure S = ⊤) (g : G) : ∃ k, g ∈ wordBall S k := by
  have hg : g ∈ Subgroup.closure S := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, mem_wordBall_one_of_mem S hs⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, mul_mem_wordBall S ha hb⟩
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, inv_mem_wordBall S ha⟩


/-- Every element of a ball of `S` of radius `m` lies in the `S'`-ball of radius `K*m`, if
every element of `S` lies in the `S'`-ball of radius `K`. -/
theorem wordBall_subset_of_forall {S' : Set G} {K : ℕ} (hK : ∀ s ∈ S, s ∈ wordBall S' K)
    (n : ℕ) : wordBall S n ⊆ wordBall S' (K * n) := by
  rintro g ⟨l, hl, hS, rfl⟩
  have key : ∀ l : List G, (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) → l.prod ∈ wordBall S' (K * l.length) := by
    intro l
    induction l with
    | nil => intro _; simpa using one_mem_wordBall S' 0
    | cons x l ih =>
      intro h
      have hx : x ∈ wordBall S' K := by
        rcases h x (by simp) with h1 | h1
        · exact hK x h1
        · simpa using inv_mem_wordBall S' (hK _ h1)
      have := mul_mem_wordBall S' hx (ih fun z hz => h z (by simp [hz]))
      simpa [List.prod_cons, Nat.mul_succ, add_comm] using this
  exact wordBall_mono S' (Nat.mul_le_mul_left K hl) (key l hS)

end Ball

section Generic
variable {G : Type*} [Group G]

/-- Exercise 1.3 (generator change). -/
theorem exists_wordBall_subset (S S' : Finset G) (hS' : Subgroup.closure (S' : Set G) = ⊤) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, wordBall (S : Set G) n ⊆ wordBall (S' : Set G) (K * n) := by
  classical
  choose k hk using exists_mem_wordBall (S' : Set G) hS'
  refine ⟨S.sup k + 1, Nat.succ_pos _, wordBall_subset_of_forall _ fun s hs => ?_⟩
  exact wordBall_mono _ ((Finset.le_sup hs).trans (Nat.le_succ _)) (hk s)

theorem card_wordBall_le_of_subset {S S' : Finset G} {m n : ℕ}
    (h : wordBall (S : Set G) m ⊆ wordBall (S' : Set G) n) :
    (Nat.card (wordBall (S : Set G) m) : ℝ) ≤ Nat.card (wordBall (S' : Set G) n) := by
  exact_mod_cast Nat.card_mono (wordBall_finite _ S'.finite_toSet n) h

theorem one_le_card_wordBall (S : Finset G) (n : ℕ) :
    (1 : ℝ) ≤ Nat.card (wordBall (S : Set G) n) := by
  have : Finite (wordBall (S : Set G) n) := (wordBall_finite _ S.finite_toSet n).to_subtype
  have : Nonempty (wordBall (S : Set G) n) := ⟨⟨1, one_mem_wordBall _ n⟩⟩
  exact_mod_cast Nat.card_pos

/-- Subexponential growth transfers along generator change. -/
theorem tendsto_log_card_wordBall_div_of_isExponentiallyBounded (hG : IsExponentiallyBounded G)
    (S : Finset G) :
    Filter.Tendsto (fun n : ℕ => Real.log (Nat.card (wordBall (S : Set G) n) : ℝ) / n)
      Filter.atTop (nhds 0) := by
  obtain ⟨S₀, hS₀, hb⟩ := hG
  obtain ⟨K, hK, hsub⟩ := exists_wordBall_subset S S₀ hS₀
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall fun n => ?_, fun a ha => ?_⟩
  · exact ha.trans_le (div_nonneg (Real.log_nonneg (one_le_card_wordBall S n)) (Nat.cast_nonneg _))
  · obtain ⟨N, hN⟩ := hb (Real.exp (a / (2 * K))) (by rw [Real.one_lt_exp_iff]; positivity)
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 := card_wordBall_le_of_subset (hsub n)
    have h2 := hN (K * n) (le_trans (by omega) (Nat.le_mul_of_pos_left n hK))
    rw [← Real.exp_nat_mul] at h2
    have hpos : (0 : ℝ) < Nat.card (wordBall (S : Set G) n) :=
      lt_of_lt_of_le one_pos (one_le_card_wordBall S n)
    have h3 := Real.log_le_log hpos (h1.trans h2)
    rw [Real.log_exp] at h3
    rw [div_lt_iff₀ hn0]
    have : ((K * n : ℕ) : ℝ) * (a / (2 * K)) = a * n / 2 := by
      push_cast; field_simp
    rw [this] at h3
    linarith [mul_pos ha hn0]

end Generic

local notation "Γ" => Garrido.GrigorchukGroup

/-! ## The doubling inequality `γ(n)² ≤ C γ(K n)` (Lemmas 6.2, 6.3, Exercise 1.5) -/

section Doubling

open Garrido

local notation "P" => Equiv.Perm (List Bool)

@[simp] theorem a_apply (w : List Bool) :
    (((GrigorchukGroup.a : Γ) : BinaryTreeAut) : P) w = grigAFun w := rfl
@[simp] theorem b_apply (w : List Bool) :
    (((GrigorchukGroup.b : Γ) : BinaryTreeAut) : P) w = grigBFun w := rfl
@[simp] theorem c_apply (w : List Bool) :
    (((GrigorchukGroup.c : Γ) : BinaryTreeAut) : P) w = grigCFun w := rfl
@[simp] theorem d_apply (w : List Bool) :
    (((GrigorchukGroup.d : Γ) : BinaryTreeAut) : P) w = grigDFun w := rfl
@[simp] theorem mul_apply (g h : Γ) (w : List Bool) :
    (((g * h : Γ) : BinaryTreeAut) : P) w =
      ((g : BinaryTreeAut) : P) (((h : BinaryTreeAut) : P) w) := rfl
@[simp] theorem one_apply (w : List Bool) : (((1 : Γ) : BinaryTreeAut) : P) w = w := rfl

/-- The four generators as letters. -/
inductive Ltr | a | b | c | d

/-- The generator named by a letter. -/
def Ltr.g : Ltr → Γ
  | .a => GrigorchukGroup.a
  | .b => GrigorchukGroup.b
  | .c => GrigorchukGroup.c
  | .d => GrigorchukGroup.d

/-- Evaluation of a word. -/
def ev (u : List Ltr) : Γ := (u.map Ltr.g).prod

@[simp] theorem ev_nil : ev [] = 1 := rfl
@[simp] theorem ev_cons (x : Ltr) (u : List Ltr) : ev (x :: u) = x.g * ev u := by
  simp [ev]
@[simp] theorem ev_append (u v : List Ltr) : ev (u ++ v) = ev u * ev v := by
  simp [ev]

/-- Fixing the first level. -/
def Fix1 (g : BinaryTreeAut) : Prop := ∀ p : Bool, (g : P) [p] = [p]

theorem Fix1.mul {g h : BinaryTreeAut} (hg : Fix1 g) (hh : Fix1 h) : Fix1 (g * h) := by
  intro p
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hh p, hg p]

end Doubling

/-- Target 4: subexponential growth for every finite generating set. -/
theorem tendsto_log_card_wordBall_div (S : Finset Γ) (_hS : Subgroup.closure (S : Set Γ) = ⊤) :
    Filter.Tendsto (fun n : ℕ => Real.log (Nat.card (wordBall (S : Set Γ) n) : ℝ) / n)
      Filter.atTop (nhds 0) :=
  tendsto_log_card_wordBall_div_of_isExponentiallyBounded
    Garrido.isExponentiallyBounded_grigorchukGroup S

end GrigorchukPak

namespace GrigorchukPak

theorem superpolynomial_and_exp_rpow_le_card_wordBall' (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
        Real.exp ((n : ℝ) ^ α) ≤
          C * (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) (K * n)) : ℝ) :=
  by
  try haveI := S; try haveI := hS; first
    | exact GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall S hS
    | exact GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall
    | exact GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall ..
    | (apply GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall <;> first | assumption | infer_instance)
    | simpa using GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall


theorem superpolynomial_and_subexponential_card_wordBall' (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          n) Filter.atTop (nhds 0) :=
  ⟨(superpolynomial_and_exp_rpow_le_card_wordBall' S hS).1, tendsto_log_card_wordBall_div S hS⟩

end GrigorchukPak


theorem solution (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          n) Filter.atTop (nhds 0) :=
  GrigorchukPak.superpolynomial_and_subexponential_card_wordBall' S hS
