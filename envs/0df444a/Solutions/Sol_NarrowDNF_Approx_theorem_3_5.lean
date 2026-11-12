-- Prove2me | solution 1 for NarrowDNF.Approx.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:54:28.079515+00:00
-- url     : https://prove2.me/submissions/6913a76c-d9c8-47f7-b200-a205b10a0b18

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Shifts
import Theorems.Thm_NarrowDNF_Approx_lemma_3_1
import Theorems.Thm_NarrowDNF_Approx_lemma_3_2
import Theorems.Thm_NarrowDNF_Approx_lemma_3_4

section
set_option autoImplicit false
namespace NarrowDNF.Dev.T35
open NarrowDNF.Approx

variable {n : ℕ}

noncomputable def wt (p : ℝ) (z : Cube n) : ℝ := ∏ i, FriedgutCoalition.bern p (z i)

lemma bern_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : Bool) : 0 < FriedgutCoalition.bern p c := by
  cases c <;> simp [FriedgutCoalition.bern] <;> linarith

lemma wt_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (z : Cube n) : 0 < wt p z :=
  Finset.prod_pos (fun i _ => bern_pos hp hp1 _)

lemma wt_sum_one (p : ℝ) : ∑ z : Cube n, wt p z = 1 := by
  have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun _ b => FriedgutCoalition.bern p b)
  rw [Fintype.piFinset_univ] at this
  have h2 : ∑ b : Bool, FriedgutCoalition.bern p b = 1 := by
    simp [Fintype.sum_bool, FriedgutCoalition.bern]
  simp only [h2, Finset.prod_const_one] at this
  exact this.symm

lemma expect_eq (p : ℝ) (c : Cube n → ℝ) : expect p c = ∑ z, wt p z * c z := rfl

lemma error_eq (p : ℝ) (f g : Cube n → Bool) :
    error p f g = ∑ z, wt p z * (if f z = g z then 0 else 1) := by
  unfold error prob FriedgutCoalition.wProb
  apply Finset.sum_congr rfl
  intro z _
  unfold wt
  split_ifs <;> simp_all

lemma error_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (f g : Cube n → Bool) : 0 ≤ error p f g := by
  rw [error_eq]
  apply Finset.sum_nonneg
  intro z _
  have := wt_pos hp hp1 z
  split_ifs <;> positivity

lemma flip_sum (i : Fin n) (Y : Cube n → ℝ) (hY : ∀ z b, Y (Function.update z i b) = Y z) :
    ∑ z : Cube n, (if z i = true then 0 else Y z) = ∑ z : Cube n, (if z i = true then Y z else 0) := by
  have inv : ∀ z : Cube n, Function.update (Function.update z i (!z i)) i (!(Function.update z i (!z i)) i) = z := by
    intro z; funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  let e : Equiv.Perm (Cube n) := ⟨fun z => Function.update z i (!z i), fun z => Function.update z i (!z i), inv, inv⟩
  rw [← Equiv.sum_comp e (fun z => if z i = true then Y z else 0)]
  apply Finset.sum_congr rfl
  intro z _
  show _ = if (Function.update z i (!z i)) i = true then Y (Function.update z i (!z i)) else 0
  rw [hY]
  cases h : z i <;> simp

lemma wt_split (p : ℝ) (i : Fin n) (z : Cube n) :
    wt p z = FriedgutCoalition.bern p (z i) * ∏ k ∈ Finset.univ.erase i, FriedgutCoalition.bern p (z k) := by
  unfold wt
  rw [Finset.mul_prod_erase _ (fun k => FriedgutCoalition.bern p (z k)) (Finset.mem_univ i)]

lemma r_indep (p : ℝ) (i : Fin n) (z : Cube n) (b : Bool) :
    ∏ k ∈ Finset.univ.erase i, FriedgutCoalition.bern p (Function.update z i b k)
      = ∏ k ∈ Finset.univ.erase i, FriedgutCoalition.bern p (z k) := by
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma key_split (p : ℝ) (i : Fin n) (A B : Cube n → ℝ)
    (hA : ∀ z b, A (Function.update z i b) = A z) (hB : ∀ z b, B (Function.update z i b) = B z) :
    ∑ z : Cube n, wt p z * (if z i = true then A z else B z)
      = ∑ z : Cube n, wt p z * ((1 - p) * B z + p * A z) := by
  set r : Cube n → ℝ := fun z => ∏ k ∈ Finset.univ.erase i, FriedgutCoalition.bern p (z k) with hr
  have hrI : ∀ z b, r (Function.update z i b) = r z := fun z b => r_indep p i z b
  have hw : ∀ z, wt p z = FriedgutCoalition.bern p (z i) * r z := fun z => wt_split p i z
  have fB := flip_sum i (fun z => r z * B z) (by intro z b; simp [hrI, hB])
  have L : ∑ z : Cube n, wt p z * (if z i = true then A z else B z)
      = p * ∑ z : Cube n, (if z i = true then r z * A z else 0)
        + (1 - p) * ∑ z : Cube n, (if z i = true then r z * B z else 0) := by
    rw [← fB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [hw]
    cases h : z i <;> simp [FriedgutCoalition.bern, h] <;> ring
  have R : ∑ z : Cube n, wt p z * ((1 - p) * B z + p * A z)
      = ((1 - p) * ∑ z : Cube n, (if z i = true then r z * B z else 0)
        + p * ∑ z : Cube n, (if z i = true then r z * A z else 0)) := by
    have fC := flip_sum i (fun z => r z * ((1 - p) * B z + p * A z)) (by intro z b; simp [hrI, hB, hA])
    have : ∑ z : Cube n, wt p z * ((1 - p) * B z + p * A z)
        = p * ∑ z : Cube n, (if z i = true then r z * ((1 - p) * B z + p * A z) else 0)
          + (1 - p) * ∑ z : Cube n, (if z i = true then 0 else r z * ((1 - p) * B z + p * A z)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      rw [hw]
      cases h : z i <;> simp [FriedgutCoalition.bern, h] <;> ring
    rw [fC] at this
    rw [this]
    have e1 : ∑ z : Cube n, (if z i = true then r z * ((1 - p) * B z + p * A z) else 0)
        = (1 - p) * ∑ z : Cube n, (if z i = true then r z * B z else 0)
          + p * ∑ z : Cube n, (if z i = true then r z * A z else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> ring
    rw [e1]; ring
  rw [L, R]; ring

end NarrowDNF.Dev.T35
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.T35
open NarrowDNF.Approx

variable {n : ℕ}

lemma mono_of_coord (v : Cube n → Bool) (h : ∀ i, CoordinateMonotone v i) : Monotone v := by
  classical
  have claim : ∀ (T : Finset (Fin n)) (x : Cube n), (∀ k ∈ T, x k = false) →
      v x ≤ v (fun k => if k ∈ T then true else x k) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro x _; simp
    | insert a T ha ih =>
      intro x hx
      have hxa : x a = false := hx a (Finset.mem_insert_self _ _)
      have ih' := ih x (fun k hk => hx k (Finset.mem_insert_of_mem hk))
      set x1 : Cube n := fun k => if k ∈ T then true else x k with hx1
      have h1a : x1 a = false := by simp [hx1, ha, hxa]
      have e1 : Function.update x1 a false = x1 := by
        rw [Function.update_eq_self_iff]; exact h1a.symm
      have e2 : (fun k => if k ∈ insert a T then true else x k) = Function.update x1 a true := by
        funext k
        by_cases hk : k = a
        · subst hk; simp
        · simp [hx1, hk, Function.update_of_ne hk]
      have := h a x1
      rw [e1] at this
      rw [e2]
      exact ih'.trans this
  intro x y hxy
  have := claim (Finset.univ.filter (fun k => x k = false ∧ y k = true)) x (by
    intro k hk; simp at hk; exact hk.1)
  have e : (fun k => if k ∈ Finset.univ.filter (fun k => x k = false ∧ y k = true) then true else x k) = y := by
    funext k
    have hk : x k = true → y k = true := Bool.le_iff_imp.1 (hxy k)
    cases hx : x k <;> cases hy : y k <;> simp_all
  rwa [e] at this

lemma applyShifts_append (s : List (Fin n × Bool)) (t : Fin n × Bool) (v : Cube n → Bool) :
    applyShifts (s ++ [t]) v =
      (if t.2 then lower t.1 (applyShifts s v) else upper t.1 (applyShifts s v)) := by
  simp [applyShifts, List.foldl_append]

lemma mono_inv {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (f h : Cube n → Bool) (hf : Monotone f)
    (s : List (Fin n × Bool)) : ∀ j ∈ s.map Prod.fst, CoordinateMonotone (applyShifts s h) j := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s t ih =>
    intro j hj
    rw [applyShifts_append]
    rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hj
    have h31 := lemma_3_1 p t.1 f (applyShifts s h) hp hp1 hf
    obtain ⟨_, hu, hl, hrest⟩ := h31
    by_cases hjt : j = t.1
    · subst hjt
      cases hb : t.2
      · simpa [hb] using hu
      · simpa [hb] using hl
    · have hj' : j ∈ s.map Prod.fst := by
        rcases hj with hj | hj
        · exact hj
        · exact absurd hj hjt
      have := hrest j hjt (ih j hj')
      cases hb : t.2 <;> simp [hb, this.1, this.2]

lemma applyShifts_indep (l : List (Fin n)) (i : Fin n) (hi : i ∉ l) (z : Cube n) (b : Bool)
    (h : Cube n → Bool) :
    applyShifts (l.map (fun j => (j, Function.update z i b j))) h
      = applyShifts (l.map (fun j => (j, z j))) h := by
  congr 1
  apply List.map_congr_left
  intro j hj
  have : j ≠ i := fun e => hi (e ▸ hj)
  simp [Function.update_of_ne this]

lemma chain {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (f h : Cube n → Bool) (hf : Monotone f)
    (l : List (Fin n)) (hl : l.Nodup) :
    ∑ z : Cube n, wt p z * error p f (applyShifts (l.map (fun j => (j, z j))) h) ≤ error p f h := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [List.map_nil, applyShifts, List.foldl_nil]
    rw [← Finset.sum_mul, wt_sum_one]; simp
  | append_singleton l i ih =>
    have hnd := List.nodup_append.1 hl
    have hl' : l.Nodup := hnd.1
    have hi : i ∉ l := by
      intro hm
      exact (hnd.2.2 i hm i (by simp)) rfl
    set u : Cube n → Cube n → Bool := fun z => applyShifts (l.map (fun j => (j, z j))) h with hu
    have hu' : ∀ z b, u (Function.update z i b) = u z := fun z b => applyShifts_indep l i hi z b h
    have eq : ∀ z, applyShifts ((l ++ [i]).map (fun j => (j, z j))) h
        = if z i then lower i (u z) else upper i (u z) := by
      intro z
      rw [List.map_append, List.map_singleton, applyShifts_append]
    have ks := key_split p i (fun z => error p f (lower i (u z))) (fun z => error p f (upper i (u z)))
      (by intro z b; simp [hu']) (by intro z b; simp [hu'])
    have step1 : ∑ z : Cube n, wt p z * error p f (applyShifts ((l ++ [i]).map (fun j => (j, z j))) h)
        = ∑ z : Cube n, wt p z * ((1 - p) * error p f (upper i (u z)) + p * error p f (lower i (u z))) := by
      rw [← ks]
      apply Finset.sum_congr rfl
      intro z _
      rw [eq]
      cases z i <;> simp
    have step2 : ∑ z : Cube n, wt p z * ((1 - p) * error p f (upper i (u z)) + p * error p f (lower i (u z)))
        ≤ ∑ z : Cube n, wt p z * error p f (u z) := by
      apply Finset.sum_le_sum
      intro z _
      have h31 := (lemma_3_1 p i f (u z) hp hp1 hf).1
      have := wt_pos hp hp1 z
      nlinarith [h31]
    exact step1.le.trans (step2.trans (ih hl'))
end NarrowDNF.Dev.T35
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.T35
open NarrowDNF.Approx

variable {n : ℕ}

lemma exists_le_avg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : Cube n → ℝ) (m : ℝ)
    (h : ∑ z, wt p z * c z ≤ m) : ∃ z, c z ≤ m := by
  by_contra hcon
  push_neg at hcon
  have hne : (Finset.univ : Finset (Cube n)).Nonempty := Finset.univ_nonempty
  have : ∑ z : Cube n, wt p z * m < ∑ z : Cube n, wt p z * c z :=
    Finset.sum_lt_sum_of_nonempty hne (fun z _ => mul_lt_mul_of_pos_left (hcon z) (wt_pos hp hp1 z))
  rw [← Finset.sum_mul, wt_sum_one] at this
  linarith

lemma activeCost_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (J : ActivationFamily n) :
    0 ≤ activeCost p J := by
  unfold activeCost
  rw [expect_eq]
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (wt_pos hp hp1 z).le (by positivity)

lemma force_empty' (J : ActivationFamily n) : force J ∅ = J := by
  funext S z
  unfold force
  simp

lemma ones_lower (z : Cube n) :
    lowerCoordinates ((List.finRange n).map (fun j => (j, z j))) = ones z := by
  ext k
  simp [lowerCoordinates, ones, List.mem_filterMap]

end NarrowDNF.Dev.T35

namespace NarrowDNF.Approx
open NarrowDNF.Dev.T35 in
theorem chk_theorem_3_5 {n : ℕ} (p : ℝ) (d : ℕ) (e L : ℝ)
    (f : Cube n → Bool) (J : ActivationFamily n) (h : Cube n → Bool)
    (hp : 0 < p) (hp_one : p < 1) (he : 0 ≤ e) (hL : 0 ≤ L)
    (hf : Monotone f) (hJ : IncreasingActivations J) (hh : AdaptiveMeasurable J h)
    (hd : ArityLE J d) (herr : error p f h ≤ e) (hload : load p J ≤ L) :
    ∀ τ : ℝ, 0 < τ → ∃ (D : Finset (Fin n)) (u : Cube n → Bool),
      Monotone u ∧ AdaptiveMeasurable (force J D) u ∧ error p f u ≤ e + τ ∧
      activeCost p (force J D) ≤ (2 - p) ^ d * L * (1 + e / τ) := by
  intro τ hτ
  classical
  let u : Cube n → Cube n → Bool :=
    fun z => applyShifts ((List.finRange n).map (fun j => (j, z j))) h
  have hmeas : ∀ z, AdaptiveMeasurable (force J (ones z)) (u z) := by
    intro z
    by_cases hne : Nonempty (Fin n)
    · obtain ⟨i0⟩ := hne
      have := (lemma_3_2 i0 J h hJ hh).2.2 ((List.finRange n).map (fun j => (j, z j)))
      rwa [ones_lower] at this
    · have hn : IsEmpty (Fin n) := not_nonempty_iff.1 hne
      have hl : (List.finRange n) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro a; exact hn.elim a
      have hu : u z = h := by simp [u, hl, applyShifts]
      have ho : ones z = ∅ := Finset.eq_empty_of_isEmpty _
      rw [hu, ho, force_empty']; exact hh
  have hmono : ∀ z, Monotone (u z) := by
    intro z
    apply mono_of_coord
    intro j
    exact mono_inv hp hp_one f h hf _ j (by simp)
  have hX : ∑ z : Cube n, wt p z * error p f (u z) ≤ e :=
    (chain hp hp_one f h hf (List.finRange n) (List.nodup_finRange n)).trans herr
  have hY : ∑ z : Cube n, wt p z * activeCost p (force J (ones z)) ≤ (2 - p) ^ d * L := by
    have h34 := (lemma_3_4 p d J hp hp_one hd).2.2.2
    rw [expect_eq] at h34
    have hpow : 0 ≤ (2 - p) ^ d := pow_nonneg (by linarith) d
    exact h34.trans (le_trans (mul_le_mul_of_nonneg_left hload hpow) le_rfl)
  have hXn : ∀ z, 0 ≤ error p f (u z) := fun z => error_nonneg hp hp_one _ _
  have hYn : ∀ z, 0 ≤ activeCost p (force J (ones z)) := fun z => activeCost_nonneg hp hp_one _
  have hpow : 0 ≤ (2 - p) ^ d := pow_nonneg (by linarith) d
  suffices hz : ∃ z, error p f (u z) ≤ e + τ ∧
      activeCost p (force J (ones z)) ≤ (2 - p) ^ d * L * (1 + e / τ) by
    obtain ⟨z, h1, h2⟩ := hz
    exact ⟨ones z, u z, hmono z, hmeas z, h1, h2⟩
  have hB : 0 ≤ (2 - p) ^ d * L := mul_nonneg hpow hL
  rcases hB.eq_or_lt with hB0 | hBpos
  · -- B = 0
    have hY0 : ∀ z, activeCost p (force J (ones z)) = 0 := by
      have hs : ∑ z : Cube n, wt p z * activeCost p (force J (ones z)) = 0 :=
        le_antisymm (by linarith)
          (Finset.sum_nonneg (fun z _ => mul_nonneg (wt_pos hp hp_one z).le (hYn z)))
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z _ => mul_nonneg (wt_pos hp hp_one z).le (hYn z))).1 hs
      intro z
      have := this z (Finset.mem_univ z)
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (wt_pos hp hp_one z).ne'
      · exact h0
    obtain ⟨z, hz⟩ := exists_le_avg hp hp_one (fun z => error p f (u z)) e hX
    have hz' : error p f (u z) ≤ e := hz
    refine ⟨z, by linarith, ?_⟩
    rw [hY0 z, ← hB0]; simp
  · set a := e + τ with ha
    have hapos : 0 < a := by linarith
    set b := (2 - p) ^ d * L * (1 + e / τ) with hb
    have hbpos : 0 < b := by positivity
    obtain ⟨z, hz⟩ := exists_le_avg hp hp_one (fun z => error p f (u z) / a +
      activeCost p (force J (ones z)) / b) 1 (by
        have e1 : ∑ z : Cube n, wt p z * (error p f (u z) / a + activeCost p (force J (ones z)) / b)
            = (∑ z : Cube n, wt p z * error p f (u z)) / a
              + (∑ z : Cube n, wt p z * activeCost p (force J (ones z))) / b := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro z _; ring
        rw [e1]
        have e2 : e / a + ((2 - p) ^ d * L) / b = 1 := by
          have key : ∀ B : ℝ, 0 < B → e / (e + τ) + B / (B * (1 + e / τ)) = 1 := by
            intro B hB; field_simp; ring
          rw [hb, ha]; exact key _ hBpos
        calc _ ≤ e / a + ((2 - p) ^ d * L) / b := by gcongr
          _ = 1 := e2)
    have t1 := div_nonneg (hXn z) hapos.le
    have t2 := div_nonneg (hYn z) hbpos.le
    refine ⟨z, ?_, ?_⟩
    · have : error p f (u z) / a ≤ 1 := by linarith
      rw [div_le_one hapos] at this; exact this
    · have : activeCost p (force J (ones z)) / b ≤ 1 := by linarith
      rw [div_le_one hbpos] at this; exact this
end NarrowDNF.Approx
end

theorem solution : type_of% @NarrowDNF.Approx.chk_theorem_3_5 := @NarrowDNF.Approx.chk_theorem_3_5
