-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.strict_weighted_simplex_volume_lower_from_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:45:00.563918+00:00
-- url     : https://prove2.me/submissions/d1711bed-e677-46d0-82d1-8e7c3307ee98

import Mathlib
import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace A3S47SV

/-- `a^(n+1) - b^(n+1) ≤ (n+1) a^n (a - b)` for `0 ≤ b ≤ a`. -/
lemma pow_sub_pow_le (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * a ^ n * (a - b) := by
  rw [← geom_sum₂_mul]
  have ha : 0 ≤ a := hb.trans hab
  have h1 : ∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n + 1 - 1 - i) ≤
      ∑ i ∈ Finset.range (n + 1), a ^ n := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    calc a ^ i * b ^ (n + 1 - 1 - i) ≤ a ^ i * a ^ (n + 1 - 1 - i) := by
          gcongr
      _ = a ^ n := by rw [← pow_add]; congr 1; omega
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have : 0 ≤ a - b := by linarith
  calc (∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n + 1 - 1 - i)) * (a - b)
      ≤ ((n + 1 : ℕ) * a ^ n) * (a - b) := mul_le_mul_of_nonneg_right h1 this
    _ = (n + 1) * a ^ n * (a - b) := by push_cast; ring

/-- The discrete integral bound `T^(n+1) ≤ (n+1) v ∑_{k<K} (T - v k)^n`. -/
lemma telescope (v T : ℝ) (hv : 0 < v) (hT : 0 < T) (n : ℕ) :
    T ^ (n + 1) ≤ (n + 1) * v *
      ∑ k ∈ Finset.range ⌈T / v⌉₊, (T - v * k) ^ n := by
  set K := ⌈T / v⌉₊
  set f : ℕ → ℝ := fun k => (max (T - v * k) 0) ^ (n + 1)
  have hK : T - v * K ≤ 0 := by
    have : T / v ≤ K := Nat.le_ceil _
    rw [div_le_iff₀ hv] at this; linarith
  have htel := Finset.sum_range_sub f K
  have hf0 : f 0 = T ^ (n + 1) := by simp [f, hT.le]
  have hfK : f K = 0 := by simp [f, hK]
  have hterm : ∀ k ∈ Finset.range K, f k - f (k + 1) ≤ (n + 1) * v * (T - v * k) ^ n := by
    intro k hk
    have hk' : (k : ℝ) < T / v := Nat.lt_ceil.mp (Finset.mem_range.mp hk)
    have hpos : 0 < T - v * k := by rw [lt_div_iff₀ hv] at hk'; linarith
    have e1 : f k = (T - v * k) ^ (n + 1) := by simp [f, max_eq_left hpos.le]
    rw [e1]
    have hb : 0 ≤ max (T - v * ((k + 1 : ℕ) : ℝ)) 0 := le_max_right _ _
    have hab : max (T - v * ((k + 1 : ℕ) : ℝ)) 0 ≤ T - v * k := by
      refine max_le ?_ hpos.le; push_cast; nlinarith
    have := pow_sub_pow_le (T - v * k) _ hb hab n
    have h2 : (T - v * k) - max (T - v * ((k + 1 : ℕ) : ℝ)) 0 ≤ v := by
      have : T - v * ((k + 1 : ℕ) : ℝ) ≤ max (T - v * ((k + 1 : ℕ) : ℝ)) 0 := le_max_left _ _
      push_cast at this ⊢; linarith
    have h3 : 0 ≤ (n + 1 : ℝ) * (T - v * k) ^ n := by positivity
    calc (T - v * k) ^ (n + 1) - f (k + 1)
        ≤ (n + 1) * (T - v * k) ^ n * ((T - v * k) - max (T - v * ((k + 1 : ℕ) : ℝ)) 0) := this
      _ ≤ (n + 1) * (T - v * k) ^ n * v := mul_le_mul_of_nonneg_left h2 h3
      _ = (n + 1) * v * (T - v * k) ^ n := by ring
  have hsum : ∑ k ∈ Finset.range K, (f k - f (k + 1)) ≤
      ∑ k ∈ Finset.range K, (n + 1) * v * (T - v * k) ^ n := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have : ∑ k ∈ Finset.range K, (f k - f (k + 1)) = f 0 - f K := by
    rw [← neg_sub, ← htel, ← Finset.sum_neg_distrib]; simp
  rw [this, hf0, hfK] at hsum; linarith

/-- Finiteness of the strict weighted simplex. -/
lemma finite_simplex {ι : Type*} [Fintype ι] (v : ι → ℚ) (hv : ∀ i, 0 < (v i : ℝ)) (T : ℝ) :
    Finite (strictWeightedSimplex v T) := by
  classical
  let B : ι → ℕ := fun i => ⌈T / (v i : ℝ)⌉₊ + 1
  have hb : ∀ (a : strictWeightedSimplex v T) i, a.1 i < B i := by
    intro a i
    have hle : (v i : ℝ) * (a.1 i : ℝ) ≤ ∑ j, (v j : ℝ) * (a.1 j : ℝ) :=
      Finset.single_le_sum (f := fun j => (v j : ℝ) * (a.1 j : ℝ))
        (fun j _ => mul_nonneg (hv j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    have h1 : (a.1 i : ℝ) < T / (v i : ℝ) := by
      rw [lt_div_iff₀ (hv i)]; linarith [a.2]
    have h2 : T / (v i : ℝ) ≤ ⌈T / (v i : ℝ)⌉₊ := Nat.le_ceil _
    have : (a.1 i : ℝ) < (⌈T / (v i : ℝ)⌉₊ : ℝ) := lt_of_lt_of_le h1 h2
    have := Nat.cast_lt.mp this
    simp only [B]; omega
  refine Finite.of_injective (β := ∀ i, Fin (B i)) (fun a i => ⟨a.1 i, hb a i⟩) ?_
  intro a b h
  apply Subtype.ext; funext i
  have := congrFun h i
  simpa using congrArg Fin.val this

/-- The sigma decomposition along the first coordinate. -/
noncomputable def sigmaEquiv {n : ℕ} (v : Fin (n + 1) → ℚ) (hv : ∀ i, 0 < (v i : ℝ)) (T : ℝ) :
    strictWeightedSimplex v T ≃
      Σ k : Fin ⌈T / (v 0 : ℝ)⌉₊,
        strictWeightedSimplex (fun i : Fin n => v i.succ) (T - (v 0 : ℝ) * (k : ℕ)) where
  toFun a := by
    refine ⟨⟨a.1 0, ?_⟩, ⟨fun i => a.1 i.succ, ?_⟩⟩
    · have h := a.2
      rw [Fin.sum_univ_succ] at h
      have hnn : 0 ≤ ∑ i : Fin n, (v i.succ : ℝ) * (a.1 i.succ : ℝ) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hv _).le (Nat.cast_nonneg _))
      apply Nat.lt_ceil.mpr
      rw [lt_div_iff₀ (hv 0)]; linarith
    · have h := a.2
      rw [Fin.sum_univ_succ] at h
      show ∑ i : Fin n, (v i.succ : ℝ) * (a.1 i.succ : ℝ) < T - (v 0 : ℝ) * (a.1 0 : ℕ)
      linarith
  invFun p := by
    refine ⟨Fin.cons (p.1 : ℕ) p.2.1, ?_⟩
    show ∑ i, (v i : ℝ) * ((Fin.cons (p.1 : ℕ) p.2.1 : Fin (n + 1) → ℕ) i : ℝ) < T
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have := p.2.2
    linarith
  left_inv a := by
    apply Subtype.ext
    exact Fin.cons_self_tail a.1
  right_inv p := by
    rcases p with ⟨⟨k, hk⟩, ⟨b, hb⟩⟩
    rfl

/-- Main inequality on `Fin n`. -/
lemma main_fin (n : ℕ) : ∀ (v : Fin n → ℚ), (∀ i, 0 < (v i : ℝ)) → ∀ T : ℝ, 0 < T →
    T ^ n ≤ (n.factorial : ℝ) * (∏ i, (v i : ℝ)) * (strictWeightedSimplexCard v T : ℝ) := by
  induction n with
  | zero =>
    intro v hv T hT
    have : strictWeightedSimplexCard v T = 1 := by
      unfold strictWeightedSimplexCard strictWeightedSimplex
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩, ⟨⟨fun i => i.elim0, by simpa using hT⟩⟩⟩
    simp [this]
  | succ n ih =>
    intro v hv T hT
    set K := ⌈T / (v 0 : ℝ)⌉₊
    have hfin : ∀ k : Fin K, Finite (strictWeightedSimplex (fun i : Fin n => v i.succ)
        (T - (v 0 : ℝ) * (k : ℕ))) := fun k => finite_simplex _ (fun i => hv _) _
    have hcard : strictWeightedSimplexCard v T =
        ∑ k : Fin K, strictWeightedSimplexCard (fun i : Fin n => v i.succ)
          (T - (v 0 : ℝ) * (k : ℕ)) := by
      unfold strictWeightedSimplexCard
      rw [Nat.card_congr (sigmaEquiv v hv T), Nat.card_sigma]
    set Pt := ∏ i : Fin n, (v i.succ : ℝ)
    have hPt : 0 < Pt := Finset.prod_pos (fun i _ => hv _)
    have hv0 := hv 0
    have hIH : ∀ k ∈ Finset.range K, (T - (v 0 : ℝ) * k) ^ n ≤
        (n.factorial : ℝ) * Pt * (strictWeightedSimplexCard (fun i : Fin n => v i.succ)
          (T - (v 0 : ℝ) * k) : ℝ) := by
      intro k hk
      have hk' : (k : ℝ) < T / (v 0 : ℝ) := Nat.lt_ceil.mp (Finset.mem_range.mp hk)
      have hpos : 0 < T - (v 0 : ℝ) * k := by rw [lt_div_iff₀ hv0] at hk'; linarith
      exact ih _ (fun i => hv _) _ hpos
    have htel := telescope (v 0 : ℝ) T hv0 hT n
    have hsum := Finset.sum_le_sum hIH
    rw [← Finset.mul_sum] at hsum
    rw [hcard, Fin.prod_univ_succ, Nat.cast_sum,
      Fin.sum_univ_eq_sum_range (fun k => (strictWeightedSimplexCard (fun i : Fin n => v i.succ)
          (T - (v 0 : ℝ) * (k : ℕ)) : ℝ)), Nat.factorial_succ]
    have hc : 0 ≤ (n + 1 : ℝ) * (v 0 : ℝ) := by positivity
    calc T ^ (n + 1) ≤ (n + 1) * (v 0 : ℝ) *
          ∑ k ∈ Finset.range K, (T - (v 0 : ℝ) * k) ^ n := htel
      _ ≤ (n + 1) * (v 0 : ℝ) * ((n.factorial : ℝ) * Pt * ∑ k ∈ Finset.range K,
          (strictWeightedSimplexCard (fun i : Fin n => v i.succ)
            (T - (v 0 : ℝ) * k) : ℝ)) := mul_le_mul_of_nonneg_left hsum hc
      _ = _ := by push_cast; ring

/-- Transport along an equivalence of index types. -/
lemma card_congr {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : ι → ℚ) (T : ℝ) :
    strictWeightedSimplexCard v T = strictWeightedSimplexCard (fun j => v (e.symm j)) T := by
  unfold strictWeightedSimplexCard
  refine Nat.card_congr
    { toFun := fun a => ⟨fun j => a.1 (e.symm j), ?_⟩
      invFun := fun b => ⟨fun i => b.1 (e i), ?_⟩
      left_inv := fun a => Subtype.ext (funext fun i => by simp)
      right_inv := fun b => Subtype.ext (funext fun j => by simp) }
  · have h := a.2
    show ∑ j, (v (e.symm j) : ℝ) * (a.1 (e.symm j) : ℝ) < T
    rw [e.symm.sum_comp (fun i => (v i : ℝ) * (a.1 i : ℝ))]; exact h
  · have h := b.2
    show ∑ i, (v i : ℝ) * (b.1 (e i) : ℝ) < T
    have := e.sum_comp (fun j => (v (e.symm j) : ℝ) * (b.1 j : ℝ))
    simp only [Equiv.symm_apply_apply] at this
    rw [this]; exact h

end A3S47SV

open A3S47SV in
theorem solution
    {ι : Type*} [Fintype ι] (v : ι → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T) :
    Finite (strictWeightedSimplex v T) ∧
      T ^ Fintype.card ι ≤
        ((Fintype.card ι).factorial : Real) *
          (∏ i, (v i : Real)) * (strictWeightedSimplexCard v T : Real) := by
  refine ⟨finite_simplex v hv T, ?_⟩
  let e := Fintype.equivFin ι
  have h := main_fin (Fintype.card ι) (fun j => v (e.symm j)) (fun j => hv _) T hT
  rw [← card_congr e v T] at h
  have hp : ∏ j, (v (e.symm j) : ℝ) = ∏ i, (v i : ℝ) :=
    e.symm.prod_comp (fun i => (v i : ℝ))
  rw [hp] at h
  exact h
