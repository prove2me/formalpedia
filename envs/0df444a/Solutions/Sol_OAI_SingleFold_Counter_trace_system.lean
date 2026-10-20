-- Prove2me | solution 1 for OAI.SingleFold.Counter.trace_system
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:21:05.253507+00:00
-- url     : https://prove2.me/submissions/5016b0d3-7190-4387-a37f-b3ac7910491f

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
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit

open OAI OAI.SingleFold OAI.SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
section hc3sec
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h
open System
attribute [local instance] Classical.propDecidable
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

omit h in
theorem hc3_digit_big {B k x : ℕ} (hB : 0 < B) (hx : x < B^k) (t : ℕ) (ht : k ≤ t) :
    OAI.SingleFold.Packed.digit B x t = 0 := by
  unfold OAI.SingleFold.Packed.digit
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right hB ht))]; simp

omit h in
theorem hc3_digit_lt {B : ℕ} (hB : 0 < B) (x t : ℕ) : OAI.SingleFold.Packed.digit B x t < B :=
  Nat.mod_lt _ hB

omit h in
theorem hc3_pack_add (B n : ℕ) (f g : ℕ → ℕ) :
    OAI.SingleFold.Packed.pack B n (fun t => f t + g t) =
      OAI.SingleFold.Packed.pack B n f + OAI.SingleFold.Packed.pack B n g := by
  unfold OAI.SingleFold.Packed.pack; simp [add_mul, Finset.sum_add_distrib]

omit h in
theorem hc3_pack_shift (B n a : ℕ) (u : ℕ → ℕ) :
    OAI.SingleFold.Packed.pack B (n+1) (fun t => if t = 0 then a else u (t-1)) =
      a + B * OAI.SingleFold.Packed.pack B n u := by
  unfold OAI.SingleFold.Packed.pack
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.add_one_ne_zero, if_false, if_true, pow_zero, mul_one, Nat.add_sub_cancel]
  rw [add_comm]; congr 1
  apply Finset.sum_congr rfl; intro t _; rw [pow_succ]; ring

omit h in
theorem hc3_add_digit {B k x y : ℕ} (hx : x < B^k) (hy : y < B^k)
    (hb : ∀ s < k, OAI.SingleFold.Packed.digit B x s + OAI.SingleFold.Packed.digit B y s < B)
    (t : ℕ) (ht : t < k) :
    OAI.SingleFold.Packed.digit B (x + y) t =
      OAI.SingleFold.Packed.digit B x t + OAI.SingleFold.Packed.digit B y t := by
  rw [← hc3_pack_digits hx, ← hc3_pack_digits hy, ← hc3_pack_add, hc3_pack_digit _ _ _ hb t ht]
  rw [hc3_pack_digits hx, hc3_pack_digits hy]

omit h in
theorem hc3_sub_digit {B k x y z : ℕ} (hB : 0 < B) (he : x + y = z) (hx : x < B^k) (hz : z < B^k)
    (hd : ∀ s < k, OAI.SingleFold.Packed.digit B x s ≤ OAI.SingleFold.Packed.digit B z s)
    (t : ℕ) (ht : t < k) :
    OAI.SingleFold.Packed.digit B y t =
      OAI.SingleFold.Packed.digit B z t - OAI.SingleFold.Packed.digit B x t := by
  have e : x + OAI.SingleFold.Packed.pack B k
      (fun s => OAI.SingleFold.Packed.digit B z s - OAI.SingleFold.Packed.digit B x s) = z := by
    have e2 : OAI.SingleFold.Packed.pack B k (OAI.SingleFold.Packed.digit B x) + OAI.SingleFold.Packed.pack B k
        (fun s => OAI.SingleFold.Packed.digit B z s - OAI.SingleFold.Packed.digit B x s) =
        OAI.SingleFold.Packed.pack B k (OAI.SingleFold.Packed.digit B z) := by
      rw [← hc3_pack_add]
      unfold OAI.SingleFold.Packed.pack
      apply Finset.sum_congr rfl; intro s hs
      have := hd s (Finset.mem_range.1 hs); congr 1; dsimp only; omega
    rwa [hc3_pack_digits hx, hc3_pack_digits hz] at e2
  have hy : y = OAI.SingleFold.Packed.pack B k
      (fun s => OAI.SingleFold.Packed.digit B z s - OAI.SingleFold.Packed.digit B x s) := by omega
  rw [hy, hc3_pack_digit _ _ _ (fun s _ => by have := hc3_digit_lt hB z s; omega) t ht]

omit h in
theorem hc3_scale {B k x : ℕ} (hB : 0 < B) (hx : x < B^k)
    (hd : ∀ s < k, OAI.SingleFold.Packed.digit B x s ≤ 1) (t : ℕ) (ht : t < k) :
    OAI.SingleFold.Packed.digit B ((B-1) * x) t = (B-1) * OAI.SingleFold.Packed.digit B x t := by
  have e : (B-1) * x = OAI.SingleFold.Packed.pack B k (fun s => (B-1) * OAI.SingleFold.Packed.digit B x s) := by
    conv_lhs => rw [← hc3_pack_digits hx]
    unfold OAI.SingleFold.Packed.pack
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  rw [e, hc3_pack_digit _ _ _ (fun s hs => ?_) t ht]
  have := hd s hs
  have : (B-1) * OAI.SingleFold.Packed.digit B x s ≤ (B-1) * 1 := Nat.mul_le_mul_left _ this
  omega

theorem hc3_counter_info (jj : Option J) : v.counter jj < v.B^v.k ∧
    ∀ t, OAI.SingleFold.Packed.digit v.B (v.counter jj) t < 2*v.b := by
  have hB2 := hc3_B h
  have hc := (h.counter jj).1
  rw [hc3_mask h, h.power] at hc
  have hw : 0 < v.w := by
    rcases Nat.eq_zero_or_pos v.w with h0 | h0
    · have := h.power; rw [h0] at this; omega
    · exact h0
  have hb : 2 * v.b - 1 < 2 ^ v.w := by
    have e1 := h.base; have e2 := h.power
    have : 2 ^ v.w = 4 * v.b := e2 ▸ e1
    omega
  have key := (OAI.SingleFold.Packed.bits_mask (x := v.counter jj) (k := v.k) hw hb).1 hc
  rw [h.power]
  have hb1 : 1 ≤ v.b := (hc3_b h).2
  refine ⟨key.1, fun t => ?_⟩
  by_cases ht : t < v.k
  · have h2 := key.2 t ht
    have h3 : OAI.SingleFold.Packed.digit (2 ^ v.w) (v.counter jj) t ≤ 2 * v.b - 1 :=
      Nat.le_of_testBit ((OAI.SingleFold.Packed.bits_testBit _ _).1 h2)
    omega
  · rw [hc3_digit_big (by positivity) key.1 t (by omega)]; omega

theorem hc3_dom (g : Q → ℕ) (hg : ∀ p, OAI.SingleFold.Counter.Bits (g p) (v.state p)) :
    ∑ p, g p < v.B^v.k ∧ ∀ t, OAI.SingleFold.Packed.digit v.B (∑ p, g p) t ≤ 1 := by
  have hlt : ∑ p, g p < v.B^v.k := by
    refine lt_of_le_of_lt ?_ (hc3_mask_lt h)
    rw [← h.partition]; exact Finset.sum_le_sum (fun p _ => hc3_bits_le (hg p))
  refine ⟨hlt, fun t => ?_⟩
  by_cases ht : t < v.k
  · rw [hc3_sum_state h (fun p => p) (by omega) g hg t ht, ← hc3_onehot h t ht]
    exact Finset.sum_le_sum (fun p _ => hc3_digit_le h (hg p) t)
  · have := hc3_B h
    rw [hc3_digit_big (by omega) hlt t (by omega)]; omega

theorem hc3_single (g : Q → ℕ) (hg : ∀ p, OAI.SingleFold.Counter.Bits (g p) (v.state p))
    (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀ p, OAI.SingleFold.Packed.digit v.B (v.state p) t = if p = q then 1 else 0) :
    OAI.SingleFold.Packed.digit v.B (∑ p, g p) t = OAI.SingleFold.Packed.digit v.B (g q) t := by
  rw [hc3_sum_state h (fun p => p) (by omega) g hg t ht, Finset.sum_eq_single q]
  · intro p _ hp; exact hc3_zero_of_bits h (hg p) (by rw [hs p, if_neg hp])
  · simp

theorem hc3_incr_dom (i : J) : increments M v i < v.B^v.k ∧
    ∀ t, OAI.SingleFold.Packed.digit v.B (increments M v i) t ≤ 1 := by
  unfold increments
  apply hc3_dom h
  intro p
  split
  · split_ifs
    · exact hc3_bits_refl _
    · exact hc3_bits_zero _
  · exact hc3_bits_zero _

theorem hc3_decr_dom (i : J) : decrements M v i < v.B^v.k ∧
    ∀ t, OAI.SingleFold.Packed.digit v.B (decrements M v i) t ≤ 1 := by
  unfold decrements
  apply hc3_dom h
  intro p
  have hb := h.branch p
  revert hb
  split
  · intro hb
    split_ifs
    · exact hb.2.1
    · exact hc3_bits_zero _
  · intro _; exact hc3_bits_zero _

end hc3sec

theorem hc3_value_bound (M : Machine Q J) (d : J → ℕ) (t : ℕ) (j : J) : (run M d t).value j ≤ d j+t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : run M d (t+1) = next M (run M d t) := by
      unfold run; rw [Function.iterate_succ_apply']
    rw [e]; unfold next
    split
    · omega
    · rename_i jj p _
      simp only
      by_cases hj : j = jj
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]; omega
    · rename_i jj p0 pd _
      split
      · simp only; omega
      · simp only
        by_cases hj : j = jj
        · subst hj; simp; omega
        · simp [Function.update_of_ne hj]; omega

theorem hc3_bits_of_digits {w x y : ℕ} (hw : 0 < w)
    (hxy : ∀ t, OAI.SingleFold.Counter.Bits (OAI.SingleFold.Packed.digit (2^w) x t) (OAI.SingleFold.Packed.digit (2^w) y t)) :
    OAI.SingleFold.Counter.Bits x y := by
  rw [hc3_bits_iff]; intro i hi
  have h1 := (hc3_bits_iff _ _).1 (hxy (i / w)) (i % w) (by
    rw [hc3_digit_tb]; simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.mod_lt _ hw, by rwa [Nat.mod_add_div]⟩)
  rw [hc3_digit_tb] at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  rw [Nat.mod_add_div] at h1; exact h1.2

theorem hc3_bits_small {a m : ℕ} (ha : a < 2^m) : OAI.SingleFold.Counter.Bits a (2^m - 1) := by
  rw [hc3_bits_iff]; intro i hi
  rw [Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  by_contra hc; push_neg at hc
  have := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hc))
  rw [this] at hi; exact absurd hi (by simp)

theorem hc3_bits_01 {a c : ℕ} (hac : a ≤ c) (hc : c ≤ 1) : OAI.SingleFold.Counter.Bits a c := by
  interval_cases c <;> interval_cases a
  · exact hc3_bits_zero _
  · exact hc3_bits_zero _
  · exact hc3_bits_refl _

theorem hc3_pack_digit_all {B n : ℕ} (hB : 0 < B) (F : ℕ → ℕ) (hF : ∀ s < n, F s < B) (t : ℕ) :
    OAI.SingleFold.Packed.digit B (OAI.SingleFold.Packed.pack B n F) t = if t < n then F t else 0 := by
  split_ifs with ht
  · exact hc3_pack_digit B n F hF t ht
  · exact hc3_digit_big hB (hc3_low B n F hF) t (by omega)

theorem hc3_pack_sum {ι : Type} (B n : ℕ) (s : Finset ι) (f : ι → ℕ → ℕ) :
    OAI.SingleFold.Packed.pack B n (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, OAI.SingleFold.Packed.pack B n (f i) := by
  unfold OAI.SingleFold.Packed.pack; simp only [Finset.sum_mul]; exact Finset.sum_comm

theorem hc3_pack_ite (B n : ℕ) (P : Prop) [Decidable P] (f : ℕ → ℕ) :
    OAI.SingleFold.Packed.pack B n (fun t => if P then f t else 0) = if P then OAI.SingleFold.Packed.pack B n f else 0 := by
  split_ifs <;> simp [OAI.SingleFold.Packed.pack]

theorem hc3_pack_zero (B n : ℕ) : OAI.SingleFold.Packed.pack B n (fun _ => 0) = 0 := by
  simp [OAI.SingleFold.Packed.pack]

theorem hc3_pack_succ' (B n : ℕ) (F : ℕ → ℕ) :
    OAI.SingleFold.Packed.pack B (n+1) F = F 0 + B * OAI.SingleFold.Packed.pack B n (fun t => F (t+1)) := by
  unfold OAI.SingleFold.Packed.pack
  rw [Finset.sum_range_succ', add_comm, Finset.mul_sum]
  simp only [pow_zero, mul_one]; congr 1
  apply Finset.sum_congr rfl; intro t _; rw [pow_succ]; ring

theorem hc3_pack_succ (B n : ℕ) (F : ℕ → ℕ) :
    OAI.SingleFold.Packed.pack B (n+1) F = OAI.SingleFold.Packed.pack B n F + F n * B^n := by
  unfold OAI.SingleFold.Packed.pack; rw [Finset.sum_range_succ]

theorem hc3_pack_congr (B n : ℕ) (F G : ℕ → ℕ) (h : ∀ t < n, F t = G t) :
    OAI.SingleFold.Packed.pack B n F = OAI.SingleFold.Packed.pack B n G := by
  unfold OAI.SingleFold.Packed.pack
  exact Finset.sum_congr rfl (fun t ht => by rw [h t (Finset.mem_range.1 ht)])

theorem hc3_arcAt_off (M : Machine Q J) (c : Cfg Q J) (q : Q) (hq : q ≠ c.state) (b : Bool) :
    arcAt M c q b = 0 := by
  unfold arcAt stateAt zeroAt decAt; cases M.instr q <;> cases b <;> simp [hq]

theorem hc3_incomingAt (M : Machine Q J) (c : Cfg Q J) (p : Q) :
    incomingAt M c p = ∑ b : Bool, if dest M c.state b = some p then arcAt M c c.state b else 0 := by
  unfold incomingAt; rw [Finset.sum_eq_single c.state]
  · intro q _ hq; apply Finset.sum_eq_zero; intro b _; rw [hc3_arcAt_off M c q hq]; simp
  · simp

theorem hc3_inc_step (M : Machine Q J) (c : Cfg Q J) (p : Q) (hc : c.state ≠ M.halt) :
    incomingAt M c p = stateAt (next M c) p := by
  rw [hc3_incomingAt, Fintype.sum_bool]
  rw [Ne, ← M.halt_iff] at hc
  unfold next
  cases hi : M.instr c.state with
  | halt => exact absurd hi hc
  | inc j p' => simp [dest, arcAt, stateAt, hi, eq_comm]
  | test j p0 pd =>
    by_cases hv : c.value j = 0 <;> simp [dest, arcAt, stateAt, zeroAt, decAt, hi, hv, eq_comm]

theorem hc3_inc_halt (M : Machine Q J) (c : Cfg Q J) (p : Q) (hc : c.state = M.halt) :
    incomingAt M c p = 0 := by
  rw [hc3_incomingAt, Fintype.sum_bool]
  rw [← M.halt_iff] at hc
  simp [dest, arcAt, hc]

theorem hc3_incAt (M : Machine Q J) (c : Cfg Q J) (i : J) :
    incAt M c i = match M.instr c.state with | .inc i' _ => if i' = i then 1 else 0 | _ => 0 := by
  unfold incAt; rw [Finset.sum_eq_single c.state]
  · cases M.instr c.state <;> simp [stateAt]
  · intro q _ hq; cases M.instr q <;> simp [stateAt, hq]
  · simp

theorem hc3_subAt (M : Machine Q J) (c : Cfg Q J) (i : J) :
    subAt M c i = match M.instr c.state with | .test i' _ _ => if i' = i ∧ c.value i' ≠ 0 then 1 else 0 | _ => 0 := by
  unfold subAt; rw [Finset.sum_eq_single c.state]
  · cases hi : M.instr c.state with
    | test j p0 pd =>
      simp only [decAt, hi]
      by_cases hj : j = i
      · subst hj; by_cases hv : c.value j = 0 <;> simp [hv]
      · simp [hj]
    | _ => simp [decAt, hi]
  · intro q _ hq; cases hi : M.instr q <;> simp [decAt, hq, hi]
  · simp

theorem hc3_val_step (M : Machine Q J) (c : Cfg Q J) (hc : c.state ≠ M.halt) (i : J) :
    (next M c).value i + subAt M c i = c.value i + incAt M c i := by
  rw [hc3_incAt, hc3_subAt]
  rw [Ne, ← M.halt_iff] at hc
  unfold next
  cases hi : M.instr c.state with
  | halt => exact absurd hi hc
  | inc j p' =>
    simp only
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, Function.update_of_ne (Ne.symm hj)]
  | test j p0 pd =>
    simp only
    by_cases hv : c.value j = 0
    · simp only [hv, if_true]
      by_cases hj : j = i
      · subst hj; simp [hv]
      · simp [hj]
    · simp only [hv, if_false]
      by_cases hj : j = i
      · subst hj; simp [hv]; omega
      · simp [hj, Function.update_of_ne (Ne.symm hj)]

theorem hc3_val_halt (M : Machine Q J) (c : Cfg Q J) (hc : c.state = M.halt) (i : J) :
    subAt M c i = 0 ∧ incAt M c i = 0 := by
  rw [hc3_incAt, hc3_subAt]
  rw [← M.halt_iff] at hc
  simp [hc]

theorem hc3_run_succ2 (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1) = next M (run M d t) := by
  unfold run
  rw [Function.iterate_succ_apply']

theorem hc3_tr_arc (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (q : Q) (bb : Bool) :
    arc M (trace M d B w b T) q bb = OAI.SingleFold.Packed.pack B (T+1) (fun t => arcAt M (run M d t) q bb) := by
  unfold arc arcAt; cases M.instr q <;> cases bb <;> simp [trace, hc3_pack_zero]

theorem hc3_tr_incoming (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (p : Q) :
    incoming M (trace M d B w b T) p = OAI.SingleFold.Packed.pack B (T+1) (fun t => incomingAt M (run M d t) p) := by
  unfold incoming incomingAt
  rw [hc3_pack_sum]; apply Finset.sum_congr rfl; intro q _
  rw [hc3_pack_sum]; apply Finset.sum_congr rfl; intro bb _
  rw [hc3_pack_ite, hc3_tr_arc]

theorem hc3_tr_incr (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (i : J) :
    increments M (trace M d B w b T) i = OAI.SingleFold.Packed.pack B (T+1) (fun t => incAt M (run M d t) i) := by
  unfold increments incAt
  rw [hc3_pack_sum]; apply Finset.sum_congr rfl; intro q _
  cases M.instr q with
  | inc i' p => rw [hc3_pack_ite]; rfl
  | _ => exact (hc3_pack_zero _ _).symm

theorem hc3_tr_decr (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ) (i : J) :
    decrements M (trace M d B w b T) i = OAI.SingleFold.Packed.pack B (T+1) (fun t => subAt M (run M d t) i) := by
  unfold decrements subAt
  rw [hc3_pack_sum]; apply Finset.sum_congr rfl; intro q _
  cases M.instr q with
  | test i' p0 pd => rw [hc3_pack_ite]; rfl
  | _ => exact (hc3_pack_zero _ _).symm

theorem solution (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ)
    (hT : HaltsAt M d T) (hB : B=2^w) (hw : 0 < w) (hb : 0 < b)
    (hbase : B=4*b) (hlarge : 2*(baseC Q d+T) < B) (hsmall : b ≤ baseC Q d+T) :
    System M d (trace M d B w b T) := by
  subst hB
  have hB0 : 0 < 2^w := by positivity
  have hbc : 1 ≤ baseC Q d := by unfold baseC; omega
  have hdl : ∀ j, d j < baseC Q d := by
    intro j
    have : d j ≤ ∑ i, d i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold baseC; omega
  have hval : ∀ jj t, t ≤ T → valueAt M d jj t < 2*b := by
    intro jj t ht
    cases jj with
    | none => simp only [valueAt]; omega
    | some j => simp only [valueAt]; have := hc3_value_bound M d t j; have := hdl j; omega
  have hrun : ∀ t < T, (run M d t).state ≠ M.halt := hT.2
  have hrunT := hT.1
  have hones : ones (2^w) (T+1) = pack (2^w) (T+1) (fun _ => 1) := rfl
  have h2b : 2^w = 2 * 2^(w-1) := by rw [← pow_succ']; congr 1; omega
  refine System.mk rfl hbase ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show 2 * baseC Q d < 2^w; omega
  · show 0 < T+1; omega
  · show 2^w * (2^w)^T = (2^w)^(T+1); ring
  · show (2^w - 1) * ones (2^w) (T+1) = (2^w)^(T+1) - 1
    unfold ones pack
    have hz : ((∑ t ∈ Finset.range (T+1), ((2^w:ℕ):ℤ) ^ t) * (((2^w:ℕ):ℤ) - 1)) = ((2^w:ℕ):ℤ) ^ (T+1) - 1 :=
      geom_sum_mul _ _
    have h1 : 1 ≤ (2^w) ^ (T+1) := Nat.one_le_pow _ _ hB0
    zify [h1, (by omega : 1 ≤ 2^w)]
    simp only [one_mul]
    push_cast at hz ⊢
    linarith
  · intro q
    show OAI.SingleFold.Counter.Bits (pack (2^w) (T+1) (fun t => stateAt (run M d t) q)) (ones (2^w) (T+1))
    apply hc3_bits_of_digits hw; intro t
    rw [hc3_pack_digit_all hB0 _ (fun s _ => by unfold stateAt; split_ifs <;> omega), hones,
      hc3_pack_digit_all hB0 _ (fun s _ => by omega)]
    split_ifs
    · exact hc3_bits_01 (by unfold stateAt; split_ifs <;> omega) le_rfl
    · exact hc3_bits_refl _
  · show ∑ q, pack (2^w) (T+1) (fun t => stateAt (run M d t) q) = ones (2^w) (T+1)
    rw [← hc3_pack_sum, hones]; apply hc3_pack_congr; intro t _
    unfold stateAt; simp
  · intro q
    have hs1 : ∀ t, stateAt (run M d t) q ≤ 1 := by intro t; unfold stateAt; split_ifs <;> omega
    cases hq : M.instr q with
    | test j p0 pd =>
      dsimp only [trace]
      simp only [hq]
      have hz : ∀ t, zeroAt M (run M d t) q ≤ stateAt (run M d t) q := by
        intro t; simp only [zeroAt, stateAt, hq]; by_cases h1 : q = (run M d t).state <;> by_cases h2 : (run M d t).value j = 0 <;> simp [h1, h2]
      have hd : ∀ t, decAt M (run M d t) q ≤ stateAt (run M d t) q := by
        intro t; simp only [decAt, stateAt, hq]; by_cases h1 : q = (run M d t).state <;> by_cases h2 : (run M d t).value j = 0 <;> simp [h1, h2]
      have hsum : ∀ t, zeroAt M (run M d t) q + decAt M (run M d t) q = stateAt (run M d t) q := by
        intro t; simp only [zeroAt, decAt, stateAt, hq]; by_cases h1 : q = (run M d t).state <;> by_cases h2 : (run M d t).value j = 0 <;> simp [h1, h2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply hc3_bits_of_digits hw; intro t
        rw [hc3_pack_digit_all hB0 _ (fun s _ => by have := hz s; have := hs1 s; omega),
          hc3_pack_digit_all hB0 _ (fun s _ => by have := hs1 s; omega)]
        split_ifs
        · exact hc3_bits_01 (hz t) (hs1 t)
        · exact hc3_bits_zero _
      · apply hc3_bits_of_digits hw; intro t
        rw [hc3_pack_digit_all hB0 _ (fun s _ => by have := hd s; have := hs1 s; omega),
          hc3_pack_digit_all hB0 _ (fun s _ => by have := hs1 s; omega)]
        split_ifs
        · exact hc3_bits_01 (hd t) (hs1 t)
        · exact hc3_bits_zero _
      · rw [← hc3_pack_add]; apply hc3_pack_congr; intro t _; exact hsum t
      · rw [← hc3_pack_add, hones]; apply hc3_pack_congr; intro t _
        have := hz t; have := hs1 t; omega
    | halt => simp [trace, zeroAt, decAt, hq, hc3_pack_zero]
    | inc j p => simp [trace, zeroAt, decAt, hq, hc3_pack_zero]
  · intro q
    show pack (2^w) (T+1) (fun t => stateAt (run M d t) q) = (if q = M.start then 1 else 0) +
      2^w * incoming M (trace M d (2^w) w b T) q
    rw [hc3_tr_incoming, hc3_pack_succ _ T (fun t => incomingAt M (run M d t) q), hc3_inc_halt M _ q hrunT,
      zero_mul, add_zero, hc3_pack_succ']
    have e2 : pack (2^w) T (fun t => stateAt (run M d (t+1)) q) = pack (2^w) T (fun t => incomingAt M (run M d t) q) := by
      apply hc3_pack_congr; intro t ht
      rw [hc3_inc_step M _ q (hrun t ht), hc3_run_succ2]
    show stateAt (run M d 0) q + 2^w * pack (2^w) T (fun t => stateAt (run M d (t+1)) q) = _
    rw [e2]; congr 1
  · intro jj
    refine ⟨?_, ?_, ?_⟩
    · show OAI.SingleFold.Counter.Bits (pack (2^w) (T+1) (valueAt M d jj)) ((2*b-1) * ones (2^w) (T+1))
      have e : (2*b-1) * ones (2^w) (T+1) = pack (2^w) (T+1) (fun _ => 2*b-1) := by
        rw [hones]; unfold pack; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
      rw [e]
      apply hc3_bits_of_digits hw; intro t
      rw [hc3_pack_digit_all hB0 _ (fun s hs => by have := hval jj s (by omega); omega),
        hc3_pack_digit_all hB0 _ (fun s _ => by omega)]
      split_ifs with ht
      · rw [show 2*b-1 = 2^(w-1)-1 by omega]
        exact hc3_bits_small (by have := hval jj t (by omega); omega)
      · exact hc3_bits_zero _
    · show pack (2^w) (T+1) (valueAt M d jj) = valueAt M d jj T * (2^w)^T + pack (2^w) T (valueAt M d jj)
      rw [hc3_pack_succ]; ring
    · show pack (2^w) T (valueAt M d jj) < (2^w)^T
      exact hc3_low _ _ _ (fun s hs => by have := hval jj s (by omega); omega)
  · intro j
    show pack (2^w) (T+1) (valueAt M d (some j)) + 2^w * decrements M (trace M d (2^w) w b T) j =
      d j + 2^w * (pack (2^w) T (valueAt M d (some j)) + increments M (trace M d (2^w) w b T) j)
    rw [hc3_tr_incr, hc3_tr_decr, hc3_pack_succ' _ _ (valueAt M d (some j)),
      hc3_pack_succ _ T (fun t => subAt M (run M d t) j), hc3_pack_succ _ T (fun t => incAt M (run M d t) j),
      (hc3_val_halt M _ hrunT j).1, (hc3_val_halt M _ hrunT j).2]
    have e0 : valueAt M d (some j) 0 = d j := by simp [valueAt]
    rw [e0, zero_mul, add_zero, add_zero, add_assoc, ← mul_add, ← hc3_pack_add, ← hc3_pack_add]
    congr 2
    apply hc3_pack_congr; intro t ht
    simp only [valueAt]
    rw [hc3_run_succ2]; exact hc3_val_step M _ (hrun t ht) j
  · intro q
    cases hq : M.instr q with
    | test j p0 pd =>
      dsimp only [trace]
      simp only [hq]
      have hz1 : ∀ t, zeroAt M (run M d t) q ≤ 1 := by
        intro t; simp only [zeroAt, hq]; split_ifs <;> omega
      have e : (2^w-1) * pack (2^w) (T+1) (fun t => 1 - zeroAt M (run M d t) q) =
          pack (2^w) (T+1) (fun t => (2^w-1) * (1 - zeroAt M (run M d t) q)) := by
        unfold pack; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
      rw [e]
      apply hc3_bits_of_digits hw; intro t
      rw [hc3_pack_digit_all hB0 _ (fun s hs => by have := hval (some j) s (by omega); omega),
        hc3_pack_digit_all hB0 _ (fun s _ => by
          have := hz1 s
          have : (2^w-1) * (1 - zeroAt M (run M d s) q) ≤ (2^w-1) * 1 := Nat.mul_le_mul_left _ (by omega)
          omega)]
      split_ifs with ht
      · by_cases hz : zeroAt M (run M d t) q = 1
        · have : valueAt M d (some j) t = 0 := by
            simp only [zeroAt, hq] at hz
            simp only [valueAt]
            split_ifs at hz with hh
            all_goals first | exact hh.2 | omega
          rw [this]; exact hc3_bits_zero _
        · rw [show 1 - zeroAt M (run M d t) q = 1 by have := hz1 t; omega, mul_one]
          exact hc3_bits_small (by have := hval (some j) t (by omega); omega)
      · exact hc3_bits_zero _
    | halt => trivial
    | inc j p => trivial
  · show pack (2^w) (T+1) (valueAt M d none) + 2^w * (2^w)^T =
      baseC Q d + 2^w * (pack (2^w) T (valueAt M d none) + ones (2^w) (T+1))
    rw [hc3_pack_succ' _ _ (valueAt M d none), hones, hc3_pack_succ _ T (fun _ => 1)]
    have e : pack (2^w) T (fun t => valueAt M d none (t+1)) =
        pack (2^w) T (valueAt M d none) + pack (2^w) T (fun _ => 1) := by
      rw [← hc3_pack_add]; apply hc3_pack_congr; intro t _; simp [valueAt]; ring
    rw [e]; simp [valueAt]; ring
  · show b ≤ valueAt M d none T; simp only [valueAt]; omega
  · show 2 * valueAt M d none T < 2^w; simp only [valueAt]; omega

