-- Prove2me | solution 1 for OAI.SingleFold.Counter.System.selected_digit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:46:17.00663+00:00
-- url     : https://prove2.me/submissions/eaaf4cab-81c7-4654-a36c-c201580dc700

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h
omit h in
theorem hc3_bits_iff (x y : ℕ) : OAI.SingleFold.Counter.Bits x y ↔ ∀ i, x.testBit i = true → y.testBit i = true := by
  unfold OAI.SingleFold.Counter.Bits
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  refine forall_congr' (fun i => ?_)
  have h1 := Nat.mod_lt (x/2^i) (show 0 < 2 by norm_num)
  have h2 := Nat.mod_lt (y/2^i) (show 0 < 2 by norm_num)
  omega

omit h in
theorem hc3_bits_le {x y : ℕ} (hb : OAI.SingleFold.Counter.Bits x y) : x ≤ y :=
  Nat.le_of_testBit ((hc3_bits_iff x y).1 hb)

omit h in
theorem hc3_bits_zero (y : ℕ) : OAI.SingleFold.Counter.Bits 0 y := by
  intro i; simp

omit h in
theorem hc3_bits_refl (y : ℕ) : OAI.SingleFold.Counter.Bits y y := by
  intro i; exact le_rfl

omit h in
theorem hc3_bits_trans {x y z : ℕ} (h1 : OAI.SingleFold.Counter.Bits x y)
    (h2 : OAI.SingleFold.Counter.Bits y z) : OAI.SingleFold.Counter.Bits x z := by
  intro i; exact le_trans (h1 i) (h2 i)

omit h in
theorem hc3_digit_tb (w x t j : ℕ) :
    (OAI.SingleFold.Packed.digit (2^w) x t).testBit j = (decide (j < w) && x.testBit (j + w*t)) := by
  unfold OAI.SingleFold.Packed.digit
  rw [← pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

omit h in
theorem hc3_digit_le_w {w x y : ℕ} (hb : OAI.SingleFold.Counter.Bits x y) (t : ℕ) :
    OAI.SingleFold.Packed.digit (2^w) x t ≤ OAI.SingleFold.Packed.digit (2^w) y t := by
  apply Nat.le_of_testBit
  intro j hj
  rw [hc3_digit_tb] at hj ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj ⊢
  exact ⟨hj.1, (hc3_bits_iff x y).1 hb _ hj.2⟩

omit h in
theorem hc3_low (B s : ℕ) (f : ℕ → ℕ) (hf : ∀ t < s, f t < B) :
    ∑ t ∈ Finset.range s, f t * B^t < B^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih (fun t ht => hf t (by omega))
    have h2 := hf s (by omega)
    have : f s * B^s ≤ (B - 1) * B^s := Nat.mul_le_mul_right _ (by omega)
    have h3 : (B - 1) * B^s + B^s = B^s * B := by
      rcases B with _ | B
      · omega
      · simp only [Nat.add_sub_cancel]; ring
    omega

omit h in
theorem hc3_split (B s m : ℕ) (f : ℕ → ℕ) :
    ∑ t ∈ Finset.range (s+1+m), f t * B^t =
      ∑ t ∈ Finset.range s, f t * B^t +
        B^s * (f s + B * ∑ t ∈ Finset.range m, f (s+1+t) * B^t) := by
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.mul_sum, mul_add, Finset.mul_sum]
  have : ∀ t ∈ Finset.range m, f (s+1+t) * B^(s+1+t) = B^s * (B * (f (s+1+t) * B^t)) := by
    intro t _; rw [pow_add, pow_add]; ring
  rw [Finset.sum_congr rfl this]; ring

omit h in
theorem hc3_digit_aux (B s m : ℕ) (f : ℕ → ℕ) (hf : ∀ t ≤ s, f t < B) :
    (∑ t ∈ Finset.range (s+1+m), f t * B^t) / B^s % B = f s := by
  rw [hc3_split]
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hf s le_rfl)
  have hl := hc3_low B s f (fun t ht => hf t ht.le)
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf s le_rfl)]

omit h in
theorem hc3_pack_digit (B n : ℕ) (F : ℕ → ℕ) (hF : ∀ s < n, F s < B) (t : ℕ) (ht : t < n) :
    OAI.SingleFold.Packed.digit B (OAI.SingleFold.Packed.pack B n F) t = F t := by
  unfold OAI.SingleFold.Packed.digit OAI.SingleFold.Packed.pack
  have := hc3_digit_aux B t (n - t - 1) F (fun s hs => hF s (by omega))
  rwa [show t + 1 + (n - t - 1) = n by omega] at this

omit h in
theorem hc3_pack_mod (B k x : ℕ) : ∑ t ∈ Finset.range k, x/B^t%B*B^t = x % B^k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]; ring

omit h in
theorem hc3_pack_digits {B k x : ℕ} (hx : x < B^k) :
    OAI.SingleFold.Packed.pack B k (OAI.SingleFold.Packed.digit B x) = x := by
  unfold OAI.SingleFold.Packed.pack OAI.SingleFold.Packed.digit
  rw [hc3_pack_mod, Nat.mod_eq_of_lt hx]

omit h in
theorem hc3_sum_digit {ι : Type} (s : Finset ι) (g : ι → ℕ) (B k : ℕ)
    (hg : ∀ i ∈ s, g i < B^k)
    (hs : ∀ t < k, ∑ i ∈ s, OAI.SingleFold.Packed.digit B (g i) t < B) (t : ℕ) (ht : t < k) :
    OAI.SingleFold.Packed.digit B (∑ i ∈ s, g i) t = ∑ i ∈ s, OAI.SingleFold.Packed.digit B (g i) t := by
  have e : ∑ i ∈ s, g i = OAI.SingleFold.Packed.pack B k
      (fun t => ∑ i ∈ s, OAI.SingleFold.Packed.digit B (g i) t) := by
    rw [Finset.sum_congr rfl (fun i hi => (hc3_pack_digits (hg i hi)).symm)]
    unfold OAI.SingleFold.Packed.pack
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [e, hc3_pack_digit B k _ hs t ht]

omit h in
theorem hc3_digit_zero (B t : ℕ) : OAI.SingleFold.Packed.digit B 0 t = 0 := by
  simp [OAI.SingleFold.Packed.digit]

omit h in
theorem hc3_digit_succ {B a y : ℕ} (ha : a < B) (t : ℕ) :
    OAI.SingleFold.Packed.digit B (a + B * y) (t+1) = OAI.SingleFold.Packed.digit B y t := by
  unfold OAI.SingleFold.Packed.digit
  have hB : 0 < B := by omega
  rw [pow_succ, mul_comm (B^t) B, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
    Nat.div_eq_of_lt ha, zero_add]

omit h in
theorem hc3_digit_zero_pos {B a y : ℕ} (ha : a < B) :
    OAI.SingleFold.Packed.digit B (a + B * y) 0 = a := by
  unfold OAI.SingleFold.Packed.digit
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem hc3_B : 2 * (1 + Fintype.card Q + ∑ j, d j) < v.B := by
  have := h.bound; unfold baseC at this; exact this

theorem hc3_b : v.B = 4 * v.b ∧ 1 ≤ v.b := by
  have := hc3_B h; have := h.base; omega

theorem hc3_mask : v.mask = OAI.SingleFold.Packed.ones v.B v.k := by
  have hB2 := hc3_B h
  have hm := h.mask
  have hH := h.full
  rw [hH] at hm
  have hg : (v.B - 1) * OAI.SingleFold.Packed.ones v.B v.k = v.B ^ v.k - 1 := by
    unfold OAI.SingleFold.Packed.ones OAI.SingleFold.Packed.pack
    have hz : ((∑ t ∈ Finset.range v.k, (v.B:ℤ) ^ t) * ((v.B:ℤ) - 1)) = (v.B:ℤ) ^ v.k - 1 :=
      geom_sum_mul _ _
    have h1 : 1 ≤ v.B ^ v.k := Nat.one_le_pow _ _ (by omega)
    zify [h1, (by omega : 1 ≤ v.B)]
    push_cast
    simp only [one_mul]
    linarith
  have hpos : 0 < v.B - 1 := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos (hm.trans hg.symm)

theorem hc3_mask_lt : v.mask < v.B^v.k := by
  rw [hc3_mask h]
  have := hc3_B h
  exact hc3_low _ _ _ (fun _ _ => by omega)

theorem hc3_mask_digit (t : ℕ) (ht : t < v.k) : OAI.SingleFold.Packed.digit v.B v.mask t = 1 := by
  rw [hc3_mask h]
  have := hc3_B h
  exact hc3_pack_digit _ _ _ (fun _ _ => by omega) t ht

theorem hc3_digit_le {x y : ℕ} (hb : OAI.SingleFold.Counter.Bits x y) (t : ℕ) :
    OAI.SingleFold.Packed.digit v.B x t ≤ OAI.SingleFold.Packed.digit v.B y t := by
  rw [h.power]; exact hc3_digit_le_w hb t

theorem hc3_state_le (q : Q) : v.state q ≤ v.mask := hc3_bits_le (h.state_bits q)

theorem hc3_state_lt (q : Q) : v.state q < v.B^v.k :=
  lt_of_le_of_lt (hc3_state_le h q) (hc3_mask_lt h)

theorem hc3_state_digit (q : Q) (t : ℕ) (ht : t < v.k) :
    OAI.SingleFold.Packed.digit v.B (v.state q) t ≤ 1 := by
  have := hc3_digit_le h (h.state_bits q) t
  rwa [hc3_mask_digit h t ht] at this

theorem hc3_sum_state {ι : Type} [Fintype ι] (φ : ι → Q) (hφ : Fintype.card ι ≤ 2 * Fintype.card Q)
    (g : ι → ℕ) (hg : ∀ i, OAI.SingleFold.Counter.Bits (g i) (v.state (φ i))) (t : ℕ) (ht : t < v.k) :
    OAI.SingleFold.Packed.digit v.B (∑ i, g i) t = ∑ i, OAI.SingleFold.Packed.digit v.B (g i) t := by
  apply hc3_sum_digit
  · intro i _; exact lt_of_le_of_lt (hc3_bits_le (hg i)) (hc3_state_lt h _)
  · intro s hs
    have hle : ∑ i, OAI.SingleFold.Packed.digit v.B (g i) s ≤ ∑ _i : ι, 1 :=
      Finset.sum_le_sum (fun i _ => le_trans (hc3_digit_le h (hg i) s) (hc3_state_digit h _ s hs))
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hle
    have := hc3_B h
    omega
  · exact ht

theorem hc3_onehot (t : ℕ) (ht : t < v.k) :
    ∑ q, OAI.SingleFold.Packed.digit v.B (v.state q) t = 1 := by
  rw [← hc3_sum_state h (fun q => q) (by omega) v.state (fun q => hc3_bits_refl _) t ht,
    h.partition, hc3_mask_digit h t ht]

theorem hc3_zero_of_bits {x : ℕ} {q : Q} {t : ℕ} (hb : OAI.SingleFold.Counter.Bits x (v.state q))
    (hz : OAI.SingleFold.Packed.digit v.B (v.state q) t = 0) : OAI.SingleFold.Packed.digit v.B x t = 0 := by
  have := hc3_digit_le h hb t; omega

theorem hc3_arc_bits (q : Q) (b : Bool) : OAI.SingleFold.Counter.Bits (arc M v q b) (v.state q) := by
  have hb := h.branch q
  unfold arc
  revert hb
  cases M.instr q <;> cases b <;> intro hb <;> simp only at hb ⊢
  · exact hc3_bits_zero _
  · exact hc3_bits_zero _
  · exact hc3_bits_refl _
  · exact hc3_bits_zero _
  · exact hb.1
  · exact hb.2.1

theorem hc3_sel (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    OAI.SingleFold.Packed.digit v.B (selected (M:=M) (v:=v) P) t =
      ∑ q, ∑ b : Bool, if P q b then OAI.SingleFold.Packed.digit v.B (arc M v q b) t else 0 := by
  unfold selected
  rw [show (∑ q, ∑ b : Bool, if P q b then arc M v q b else 0) =
      ∑ x : Q × Bool, (if P x.1 x.2 then arc M v x.1 x.2 else 0) from (Fintype.sum_prod_type' _).symm]
  rw [hc3_sum_state h Prod.fst (by simp [Fintype.card_prod]; omega) _ ?_ t ht]
  · rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro x _
    split_ifs
    · rfl
    · exact hc3_digit_zero _ _
  · intro x
    split_ifs
    · exact hc3_arc_bits h _ _
    · exact hc3_bits_zero _

theorem solution (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    digit v.B (selected (M:=M) (v:=v) P) t=∑q,∑b : Bool,if P q b then digit v.B (arc M v q b) t else 0 := by
  exact hc3_sel h P t ht

