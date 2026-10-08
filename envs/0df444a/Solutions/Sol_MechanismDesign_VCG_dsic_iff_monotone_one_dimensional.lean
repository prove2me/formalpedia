-- Prove2me | solution 1 for MechanismDesign.VCG.dsic_iff_monotone_one_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:16:29.923862+00:00
-- url     : https://prove2.me/submissions/70f27db9-6e54-4626-b327-664addf001a3

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

lemma cm_fin_telescope : ∀ (k : ℕ) (V : Fin (k + 1) → ℝ),
    ∑ κ : Fin k, (V κ.succ - V κ.castSucc) = V (Fin.last k) - V 0
  | 0, V => by simp
  | k + 1, V => by
    rw [Fin.sum_univ_castSucc]
    have ih := cm_fin_telescope k (fun j => V j.castSucc)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

section single
variable {A T : Type*} (v : A → T → ℝ) (g : T → A)

def cmW (x y : T) : ℝ := v (g x) y - v (g x) x

def cmChain (c x : T) : Set ℝ :=
  {s | ∃ (k : ℕ) (f : ℕ → T), f 0 = c ∧ f k = x ∧ s = ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1))}

noncomputable def cmPot (c x : T) : ℝ := sSup (cmChain v g c x)

lemma cm_ext_sum (f : ℕ → T) (k : ℕ) (y : T) :
    ∑ κ ∈ Finset.range (k + 1), cmW v g ((fun m => if m ≤ k then f m else y) κ)
        ((fun m => if m ≤ k then f m else y) (κ + 1))
      = ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) + cmW v g (f k) y := by
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro κ hκ
    have h1 := Finset.mem_range.mp hκ
    simp only [show κ ≤ k by omega, show κ + 1 ≤ k by omega, if_true]
  · simp

variable {v g}

lemma cm_ext_mem {c x : T} (y : T) {s : ℝ} (hs : s ∈ cmChain v g c x) :
    s + cmW v g x y ∈ cmChain v g c y := by
  obtain ⟨k, f, h0, hk, rfl⟩ := hs
  refine ⟨k + 1, fun m => if m ≤ k then f m else y, by simpa using h0, by simp, ?_⟩
  rw [cm_ext_sum, hk]

lemma cm_nonempty (c x : T) : (cmChain v g c x).Nonempty :=
  ⟨_, cm_ext_mem x (s := 0) ⟨0, fun _ => c, rfl, rfl, by simp⟩⟩

variable (hcm : ∀ (k : ℕ) (f : ℕ → T), f k = f 0 →
    ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) ≤ 0)
include hcm

lemma cm_bdd (c x : T) : BddAbove (cmChain v g c x) := by
  refine ⟨-cmW v g x c, fun s hs => ?_⟩
  have hm := cm_ext_mem c hs
  obtain ⟨k, f, h0, hk, he⟩ := hm
  have := hcm k f (by rw [hk, h0])
  linarith

lemma cm_pot_ineq (c x y : T) : cmPot v g c x + cmW v g x y ≤ cmPot v g c y := by
  have : cmPot v g c x ≤ cmPot v g c y - cmW v g x y := by
    apply csSup_le (cm_nonempty c x)
    intro s hs
    have := le_csSup (cm_bdd hcm c y) (cm_ext_mem y hs)
    unfold cmPot
    linarith
  linarith

end single

theorem dsic_iff_cyclically_monotone_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j) (k : ℕ) (θs : Fin (k + 1) → Θ i), θs (Fin.last k) = θs 0 →
        ∑ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ 0 := by
  constructor
  · rintro ⟨t, ht⟩ i θ k θs hlast
    let V : Fin (k + 1) → ℝ := fun m =>
      u i (q (Function.update θ i (θs m))) (θs m) - t i (Function.update θ i (θs m))
    have hle : ∀ κ : Fin k, (u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.succ)
          - u i (q (Function.update θ i (θs κ.castSucc))) (θs κ.castSucc)) ≤ V κ.succ - V κ.castSucc := by
      intro κ
      have h := ht (Function.update θ i (θs κ.succ)) i (θs κ.castSucc)
      simp only [Function.update_self, Function.update_idem] at h
      simp only [V]
      linarith
    calc _ ≤ ∑ κ : Fin k, (V κ.succ - V κ.castSucc) := Finset.sum_le_sum (fun κ _ => hle κ)
      _ = V (Fin.last k) - V 0 := cm_fin_telescope k V
      _ = 0 := by simp only [V, hlast]; ring
  · intro H
    classical
    refine ⟨fun i θ => u i (q θ) (θ i) -
      cmPot (u i) (fun x => q (Function.update θ i x)) (Classical.choice ⟨θ i⟩) (θ i), ?_⟩
    intro θ i x
    simp only
    have hcm : ∀ (k : ℕ) (f : ℕ → Θ i), f k = f 0 →
        ∑ κ ∈ Finset.range k, cmW (u i) (fun x => q (Function.update θ i x)) (f κ) (f (κ + 1)) ≤ 0 := by
      intro k f hf
      have := H i θ k (fun m => f m.val) (by simpa using hf)
      rw [Finset.sum_range (fun κ => cmW (u i) (fun x => q (Function.update θ i x)) (f κ) (f (κ + 1)))]
      exact this
    have hg : (fun y => q (Function.update (Function.update θ i x) i y)) =
        (fun y => q (Function.update θ i y)) := by
      funext y; rw [Function.update_idem]
    rw [hg]
    simp only [Function.update_self]
    have hp := cm_pot_ineq hcm (Classical.choice ⟨θ i⟩) x (θ i)
    have hq : q θ = q (Function.update θ i (θ i)) := by rw [Function.update_eq_self]
    simp only [cmW] at hp
    rw [hq]
    simp only [Function.update_eq_self] at hp ⊢
    linarith


section oned
variable {A T : Type*} (R : A → A → Prop) (v : A → T → ℝ) (g : T → A)

def odLe (x y : T) : Prop := x = y ∨ HigherType R v y x

variable {R v g}

lemma od_higher_trans {x y z : T} (h1 : HigherType R v x y) (h2 : HigherType R v y z) :
    HigherType R v x z := by
  refine ⟨fun a a' h => ?_, fun a a' h => ⟨(h1.2 a a' h).1, (h2.2 a a' h).2⟩⟩
  have := h1.1 a a' h
  have := h2.1 a a' h
  linarith

lemma od_le_trans {x y z : T} (h1 : odLe R v x y) (h2 : odLe R v y z) : odLe R v x z := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  exact Or.inr (od_higher_trans h2 h1)

variable (h1d : OneDimensional R v)
include h1d

lemma od_le_total (x y : T) : odLe R v x y ∨ odLe R v y x := by
  by_cases h : x = y
  · exact Or.inl (Or.inl h)
  rcases h1d x y h with h' | h'
  · exact Or.inr (Or.inr h')
  · exact Or.inl (Or.inr h')

lemma od_exists_max (f : ℕ → T) : ∀ k : ℕ, ∃ m, m ≤ k ∧ ∀ j ≤ k, odLe R v (f j) (f m)
  | 0 => ⟨0, le_rfl, fun j hj => by
      have : j = 0 := by omega
      subst this; exact Or.inl rfl⟩
  | k + 1 => by
    obtain ⟨m, hm, hmax⟩ := od_exists_max f k
    rcases od_le_total h1d (f (k + 1)) (f m) with h | h
    · refine ⟨m, by omega, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact hmax j (by omega)
      · have : j = k + 1 := by omega
        subst this; exact h
    · refine ⟨k + 1, le_rfl, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact od_le_trans (hmax j (by omega)) h
      · have : j = k + 1 := by omega
        subst this; exact Or.inl rfl

omit h1d in
lemma od_shortcut (hmono : MonotoneWRT R v g) {x y z : T}
    (hx : odLe R v x z) (hy : odLe R v y z) :
    cmW v g x z + cmW v g z y ≤ cmW v g x y := by
  simp only [cmW]
  rcases hx with rfl | hx
  · simp
  rcases hy with rfl | hy
  · simp
  have hR := hmono z x hx
  by_cases hs : R (g x) (g z)
  · have := hy.2 (g z) (g x) ⟨hR, hs⟩
    linarith [this.1, this.2]
  · have := hy.1 (g z) (g x) ⟨hR, hs⟩
    linarith

omit h1d in
lemma od_remove (f : ℕ → T) (p r : ℕ) :
    ∑ j ∈ Finset.range (p + 2 + r), cmW v g (f j) (f (j + 1)) =
      ∑ j ∈ Finset.range (p + 1 + r), cmW v g ((fun j => if j ≤ p then f j else f (j + 1)) j)
          ((fun j => if j ≤ p then f j else f (j + 1)) (j + 1))
        + (cmW v g (f p) (f (p + 1)) + cmW v g (f (p + 1)) (f (p + 2)) - cmW v g (f p) (f (p + 2))) := by
  rw [Finset.sum_range_add _ (p + 2) r, Finset.sum_range_add _ (p + 1) r,
    show p + 2 = p + 1 + 1 from rfl, Finset.sum_range_succ _ (p + 1), Finset.sum_range_succ _ p,
    Finset.sum_range_succ _ p]
  have e1 : ∑ j ∈ Finset.range p, cmW v g ((fun j => if j ≤ p then f j else f (j + 1)) j)
          ((fun j => if j ≤ p then f j else f (j + 1)) (j + 1)) =
      ∑ j ∈ Finset.range p, cmW v g (f j) (f (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    simp only [show j ≤ p by omega, show j + 1 ≤ p by omega, if_true]
  have e2 : ∑ j ∈ Finset.range r, cmW v g ((fun j => if j ≤ p then f j else f (j + 1)) (p + 1 + j))
          ((fun j => if j ≤ p then f j else f (j + 1)) (p + 1 + j + 1)) =
      ∑ j ∈ Finset.range r, cmW v g (f (p + 2 + j)) (f (p + 2 + j + 1)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [show ¬ (p + 1 + j ≤ p) by omega, show ¬ (p + 1 + j + 1 ≤ p) by omega, if_false]
    congr 2 <;> omega
  rw [e1, e2]
  simp only [le_rfl, if_true, show ¬ (p + 1 ≤ p) by omega, if_false]
  ring

lemma od_cycle (hmono : MonotoneWRT R v g) : ∀ (k : ℕ) (f : ℕ → T), f k = f 0 →
    ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) ≤ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro f hf
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp
    · simp [cmW, hf]
  -- reduce to a maximum at an index in [1, k-1]
  have main : ∀ f : ℕ → T, f k = f 0 → ∀ m, 1 ≤ m → m + 1 ≤ k →
      (∀ j ≤ k, odLe R v (f j) (f m)) → ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) ≤ 0 := by
    intro f hf m hm1 hmk hmax
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, k = p + 2 + r := ⟨k - (p + 2), by omega⟩
    rw [od_remove f p r]
    have hsc := od_shortcut hmono (hmax p (by omega)) (hmax (p + 2) (by omega))
    have hrec := ih (p + 1 + r) (by omega) (fun j => if j ≤ p then f j else f (j + 1)) (by
      simp only [show ¬ (p + 1 + r ≤ p) by omega, if_false, zero_le, if_true]
      rw [show p + 1 + r + 1 = p + 2 + r by omega, hf])
    linarith
  obtain ⟨m, hm, hmax⟩ := od_exists_max h1d f (k - 1)
  have hmax' : ∀ j ≤ k, odLe R v (f j) (f m) := by
    intro j hj
    rcases Nat.lt_or_ge j k with h | h
    · exact hmax j (by omega)
    · have : j = k := by omega
      subst this; rw [hf]; exact hmax 0 (by omega)
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · -- rotate by one
    subst h0
    let f' : ℕ → T := fun j => if j < k then f (j + 1) else f 1
    have hf' : f' k = f' 0 := by simp [f']
    have hsum : ∑ κ ∈ Finset.range k, cmW v g (f' κ) (f' (κ + 1)) =
        ∑ κ ∈ Finset.range k, cmW v g (f κ) (f (κ + 1)) := by
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have : ∑ κ ∈ Finset.range n, cmW v g (f' κ) (f' (κ + 1)) =
          ∑ κ ∈ Finset.range n, cmW v g (f (κ + 1)) (f (κ + 1 + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have := Finset.mem_range.mp hj
        simp only [f', show j < n + 1 by omega, show j + 1 < n + 1 by omega, if_true]
      rw [this]
      simp only [f', show n < n + 1 by omega, lt_irrefl, if_true, if_false, zero_add]
      rw [hf]
    rw [← hsum]
    apply main f' hf' (k - 1) (by omega) (by omega)
    intro j hj
    have e : f' (k - 1) = f 0 := by
      simp only [f', show k - 1 < k by omega, if_true, show k - 1 + 1 = k by omega, hf]
    rw [e]
    simp only [f']
    split_ifs
    · exact hmax' _ (by omega)
    · exact hmax' 1 (by omega)
  · exact main f hf m hpos (by omega) hmax'

end oned

theorem dsic_iff_monotone_one_dimensional_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι]
    [DecidableEq ι] (u : ∀ i, A → Θ i → ℝ) (R : ι → A → A → Prop)
    (hR : ∀ i, IsCompleteOrder (R i))
    (h1d : ∀ i, OneDimensional (R i) (u i)) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j),
        MonotoneWRT (R i) (u i) (fun x : Θ i => q (Function.update θ i x)) := by
  constructor
  · rintro ⟨t, ht⟩ i θ x y hxy
    by_contra hn
    have hyx : R i (q (Function.update θ i y)) (q (Function.update θ i x)) :=
      ((hR i).1 _ _).resolve_left hn
    have hs := hxy.1 _ _ ⟨hyx, hn⟩
    have h1 := ht (Function.update θ i x) i y
    have h2 := ht (Function.update θ i y) i x
    simp only [Function.update_self, Function.update_idem] at h1 h2
    linarith
  · intro hmono
    rw [dsic_iff_cyclically_monotone_core]
    intro i θ k θs hlast
    let f : ℕ → Θ i := fun j => θs ⟨min j k, by omega⟩
    have hc := od_cycle (h1d i) (hmono i θ) k f (by
      simp only [f, min_self, Nat.zero_min]
      have e1 : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
      have e0 : (⟨0, by omega⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp)
      rw [e1, e0]; exact hlast)
    rw [← Fin.sum_univ_eq_sum_range (fun j => cmW (u i) (fun x => q (Function.update θ i x)) (f j) (f (j + 1))) k] at hc
    convert hc using 2 with κ
    have e1 : f κ = θs κ.castSucc := by
      simp only [f]; congr 1; ext; simp
    have e2 : f (κ + 1) = θs κ.succ := by
      simp only [f]; congr 1; ext; simp
    simp only [cmW, e1, e2]

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι]
    [DecidableEq ι] [Finite A] (u : ∀ i, A → Θ i → ℝ) (R : ι → A → A → Prop)
    (hR : ∀ i, IsCompleteOrder (R i)) (hbdd : ∀ i, BoundedTypes (u i))
    (h1d : ∀ i, OneDimensional (R i) (u i)) (q : (∀ i, Θ i) → A) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ⟨q, t⟩) ↔
      ∀ (i : ι) (θ : ∀ j, Θ j),
        MonotoneWRT (R i) (u i) (fun x : Θ i => q (Function.update θ i x)) := by
  exact dsic_iff_monotone_one_dimensional_core u R hR h1d q
