-- Prove2me | solution 1 for OAI.SingleFold.Counter.system_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:13:27.037456+00:00
-- url     : https://prove2.me/submissions/c2caa38e-f56a-4f48-989f-3f06d08f74f0

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
import Theorems.Thm_OAI_SingleFold_Packed_bits_mask
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit

open OAI OAI.SingleFold OAI.SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
section hc3sec
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

theorem hc3_incoming_val (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀ p, OAI.SingleFold.Packed.digit v.B (v.state p) t = if p = q then 1 else 0) (z : Q) :
    OAI.SingleFold.Packed.digit v.B (incoming M v z) t =
      ∑ b : Bool, if dest M q b = some z then OAI.SingleFold.Packed.digit v.B (arc M v q b) t else 0 := by
  unfold incoming
  rw [show (∑ q, ∑ b : Bool, if dest M q b = some z then arc M v q b else 0) =
      ∑ x : Q × Bool, (if dest M x.1 x.2 = some z then arc M v x.1 x.2 else 0) from
      (Fintype.sum_prod_type' _).symm]
  rw [hc3_sum_state h Prod.fst (by simp [Fintype.card_prod]; omega) _ ?_ t ht]
  · rw [Fintype.sum_prod_type' (f := fun a b => OAI.SingleFold.Packed.digit v.B
        (if dest M a b = some z then arc M v a b else 0) t), Finset.sum_eq_single q]
    · apply Finset.sum_congr rfl; intro b _
      split_ifs
      · rfl
      · exact hc3_digit_zero _ _
    · intro p _ hp
      apply Finset.sum_eq_zero; intro b _
      split_ifs
      · exact hc3_zero_of_bits h (hc3_arc_bits h p b) (by rw [hs p, if_neg hp])
      · exact hc3_digit_zero _ _
    · simp
  · intro x
    split_ifs
    · exact hc3_arc_bits h _ _
    · exact hc3_bits_zero _

theorem hc3_incr_val (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀ p, OAI.SingleFold.Packed.digit v.B (v.state p) t = if p = q then 1 else 0) (i : J) :
    OAI.SingleFold.Packed.digit v.B (increments M v i) t =
      match M.instr q with | .inc i' _ => if i' = i then 1 else 0 | _ => 0 := by
  unfold increments
  rw [hc3_single h _ ?_ t ht q hs]
  · cases hq : M.instr q <;> simp only [hq] <;> (try split_ifs) <;> simp [hs q, hc3_digit_zero]
  · intro p
    split
    · split_ifs
      · exact hc3_bits_refl _
      · exact hc3_bits_zero _
    · exact hc3_bits_zero _

theorem hc3_decr_val (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀ p, OAI.SingleFold.Packed.digit v.B (v.state p) t = if p = q then 1 else 0) (i : J) :
    OAI.SingleFold.Packed.digit v.B (decrements M v i) t =
      match M.instr q with | .test i' _ _ => if i' = i then OAI.SingleFold.Packed.digit v.B (v.decBranch q) t else 0 | _ => 0 := by
  unfold decrements
  rw [hc3_single h _ ?_ t ht q hs]
  · cases hq : M.instr q <;> simp only [hq] <;> (try split_ifs) <;> simp [hc3_digit_zero]
  · intro p
    have hb := h.branch p
    revert hb
    split
    · intro hb
      split_ifs
      · exact hb.2.1
      · exact hc3_bits_zero _
    · intro _; exact hc3_bits_zero _

theorem hc3_test_values (t : ℕ) (ht : t < v.k) (q : Q)
    (hs : ∀p, OAI.SingleFold.Packed.digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    (∀z,OAI.SingleFold.Packed.digit v.B (incoming M v z) t=
      (if z=pd then OAI.SingleFold.Packed.digit v.B (v.decBranch q) t else 0)+
      (if z=p0 then OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) t else 0)) ∧
    (∀i,OAI.SingleFold.Packed.digit v.B (increments M v i) t=0) ∧
    (∀i,OAI.SingleFold.Packed.digit v.B (decrements M v i) t=if i=j then OAI.SingleFold.Packed.digit v.B (v.decBranch q) t else 0) := by
  refine ⟨fun z => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hc3_incoming_val h t ht q hs z, Fintype.sum_bool]
    simp only [dest, arc, hi]
    by_cases h1 : z = pd <;> by_cases h2 : z = p0
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · rw [hc3_incr_val h t ht q hs i]; simp only [hi]
  · rw [hc3_decr_val h t ht q hs i]; simp only [hi]
    rcases eq_or_ne i j with h1 | h1
    · subst h1; simp
    · simp [h1, Ne.symm h1]

theorem hc3_counter_update (j : J) :
    OAI.SingleFold.Packed.digit v.B (v.counter (some j)) 0=d j ∧ ∀t < v.k-1,
    OAI.SingleFold.Packed.digit v.B (v.counter (some j)) (t+1)+OAI.SingleFold.Packed.digit v.B (decrements M v j) t=
      OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t+OAI.SingleFold.Packed.digit v.B (increments M v j) t := by
  have hk := h.length
  have hBb := hc3_b h
  have hBB := hc3_B h
  have hB0 : 0 < v.B := by omega
  obtain ⟨hclt, hcd⟩ := hc3_counter_info h (some j)
  obtain ⟨hDlt, hDd⟩ := hc3_decr_dom h j
  obtain ⟨hIlt, hId⟩ := hc3_incr_dom h j
  have hlast : v.last = v.B^(v.k-1) := by
    have e := h.last; rw [h.full] at e
    have : v.B^v.k = v.B * v.B^(v.k-1) := by rw [← pow_succ']; congr 1; omega
    rw [this] at e
    exact Nat.eq_of_mul_eq_mul_left hB0 e
  obtain ⟨_, hcR, hRl⟩ := h.counter (some j)
  rw [hlast] at hcR hRl
  have hRlt : v.rem (some j) < v.B^v.k :=
    lt_of_lt_of_le hRl (Nat.pow_le_pow_right hB0 (by omega))
  have hRd : ∀ t < v.k-1, OAI.SingleFold.Packed.digit v.B (v.rem (some j)) t =
      OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t := by
    intro t ht
    unfold OAI.SingleFold.Packed.digit
    rw [hcR]
    have : v.final (some j) * v.B^(v.k-1) = v.B^t * (v.B * (v.final (some j) * v.B^(v.k-2-t))) := by
      rw [show v.k - 1 = t + 1 + (v.k-2-t) by omega, pow_add, pow_add]; ring
    rw [this, add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  have hRb : ∀ s, OAI.SingleFold.Packed.digit v.B (v.rem (some j)) s < 2 * v.b := by
    intro s
    by_cases hs : s < v.k - 1
    · rw [hRd s hs]; exact hcd s
    · rw [hc3_digit_big hB0 hRl s (by omega)]; omega
  have he := h.update j
  have hclt' : v.counter (some j) < v.B^(v.k+1) :=
    lt_of_lt_of_le hclt (Nat.pow_le_pow_right hB0 (by omega))
  have eL : v.counter (some j) + v.B * decrements M v j = OAI.SingleFold.Packed.pack v.B (v.k+1)
      (fun t => OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t +
        (if t = 0 then 0 else OAI.SingleFold.Packed.digit v.B (decrements M v j) (t-1))) := by
    rw [hc3_pack_add, hc3_pack_shift, hc3_pack_digits hclt', hc3_pack_digits hDlt, zero_add]
  have eR : d j + v.B * (v.rem (some j) + increments M v j) = OAI.SingleFold.Packed.pack v.B (v.k+1)
      (fun t => if t = 0 then d j else (fun t => OAI.SingleFold.Packed.digit v.B (v.rem (some j)) t +
        OAI.SingleFold.Packed.digit v.B (increments M v j) t) (t-1)) := by
    rw [hc3_pack_shift v.B v.k (d j) (fun t => OAI.SingleFold.Packed.digit v.B (v.rem (some j)) t +
        OAI.SingleFold.Packed.digit v.B (increments M v j) t), hc3_pack_add, hc3_pack_digits hRlt, hc3_pack_digits hIlt]
  rw [eL, eR] at he
  have hdj : d j < v.B := by
    have : d j ≤ ∑ i, d i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have key := fun t (ht : t < v.k + 1) => (hc3_pack_digit _ _ _ (fun s _ => by
      have := hcd s
      split_ifs
      · omega
      · have := hDd (s-1); omega) t ht).symm.trans
    ((congrArg (fun x => OAI.SingleFold.Packed.digit v.B x t) he).trans
      (hc3_pack_digit _ _ _ (fun s _ => by
        split_ifs
        · exact hdj
        · have := hRb (s-1); have := hId (s-1); dsimp only; omega) t ht))
  refine ⟨?_, fun t ht => ?_⟩
  · have := key 0 (by omega); simpa using this
  · have := key (t+1) (by omega)
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at this
    rw [hRd t ht] at this
    exact this

theorem hc3_test_choice (t : ℕ) (ht : t < v.k-1) (q : Q)
    (hs : ∀p,OAI.SingleFold.Packed.digit v.B (v.state p) t=if p=q then 1 else 0)
    (j : J) (p0 pd : Q) (hi : M.instr q=.test j p0 pd) :
    OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) t=(if OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t=0 then 1 else 0) ∧
    OAI.SingleFold.Packed.digit v.B (v.decBranch q) t=(if OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t=0 then 0 else 1) := by
  have hk := h.length
  have hBB := hc3_B h
  have hB0 : 0 < v.B := by omega
  have hb := h.branch q
  rw [hi] at hb
  simp only at hb
  obtain ⟨hzb, hdb, hzd, hzc⟩ := hb
  have hzt := h.zero_test q
  rw [hi] at hzt
  simp only at hzt
  have hzlt : v.zeroBranch q < v.B^v.k := lt_of_le_of_lt (hc3_bits_le hzb) (hc3_state_lt h q)
  have hdlt : v.decBranch q < v.B^v.k := lt_of_le_of_lt (hc3_bits_le hdb) (hc3_state_lt h q)
  have hsum : OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) t + OAI.SingleFold.Packed.digit v.B (v.decBranch q) t = 1 := by
    rw [← hc3_add_digit hzlt hdlt (fun s hs => by
      have := hc3_digit_le h hzb s; have := hc3_digit_le h hdb s; have := hc3_state_digit h q s hs; omega) t (by omega), hzd, hs q, if_pos rfl]
  have hzm : ∀ s < v.k, OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) s ≤ OAI.SingleFold.Packed.digit v.B v.mask s :=
    fun s _ => hc3_digit_le h (hc3_bits_trans hzb (h.state_bits q)) s
  have hcomp : ∀ s < v.k, OAI.SingleFold.Packed.digit v.B (v.complement q) s =
      1 - OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) s := by
    intro s hs
    rw [hc3_sub_digit hB0 hzc hzlt (hc3_mask_lt h) hzm s hs, hc3_mask_digit h s hs]
  have hclt : v.complement q < v.B^v.k := by have := hc3_mask_lt h; omega
  by_cases hz : OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) t = 1
  · have hc0 : OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t = 0 := by
      have := hc3_digit_le h hzt t
      rw [hc3_scale hB0 hclt (fun s hs => by rw [hcomp s hs]; omega) t (by omega), hcomp t (by omega), hz] at this
      simpa using this
    rw [hc0]; simp; omega
  · have hd1 : OAI.SingleFold.Packed.digit v.B (v.decBranch q) t = 1 := by omega
    obtain ⟨_, hcu⟩ := hc3_counter_update h j
    have e := hcu t ht
    obtain ⟨_, hinc, hdec⟩ := hc3_test_values h t (by omega) q hs j p0 pd hi
    rw [hinc j, hdec j, if_pos rfl, hd1] at e
    have hne : OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t ≠ 0 := by omega
    simp [hne]; omega

omit h [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
theorem hc3_run_succ {Q J : Type} [DecidableEq Q] [DecidableEq J] (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1) = next M (run M d t) := by
  unfold run
  rw [Function.iterate_succ_apply']

theorem hc3_state_succ (p : Q) (t : ℕ) :
    OAI.SingleFold.Packed.digit v.B (v.state p) (t+1) = OAI.SingleFold.Packed.digit v.B (incoming M v p) t := by
  have := hc3_B h
  rw [h.transition p]
  exact hc3_digit_succ (by split_ifs <;> omega) t

theorem hc3_state_zero (p : Q) :
    OAI.SingleFold.Packed.digit v.B (v.state p) 0 = if p = M.start then 1 else 0 := by
  have := hc3_B h
  rw [h.transition p, hc3_digit_zero_pos (by split_ifs <;> omega)]

theorem hc3_decode (t : ℕ) (ht : t < v.k) :
    (∀q,OAI.SingleFold.Packed.digit v.B (v.state q) t=if q=(run M d t).state then 1 else 0) ∧
    (∀j,OAI.SingleFold.Packed.digit v.B (v.counter (some j)) t=(run M d t).value j) := by
  induction t with
  | zero =>
    refine ⟨fun q => ?_, fun j => ?_⟩
    · rw [hc3_state_zero h q, run_zero]
    · rw [run_zero]; exact (hc3_counter_update h j).1
  | succ t ih =>
    obtain ⟨hs, hc⟩ := ih (by omega)
    have hcu := fun j => (hc3_counter_update h j).2 t (by omega)
    have hst := hc3_state_succ h
    have hinc := hc3_incoming_val h t (by omega) _ hs
    have hincr := hc3_incr_val h t (by omega) _ hs
    have hdecr := hc3_decr_val h t (by omega) _ hs
    have htv := hc3_test_values h t (by omega) _ hs
    have htc := hc3_test_choice h t (by omega) _ hs
    rw [hc3_run_succ]
    generalize run M d t = c at hs hc hinc hincr hdecr htv htc ⊢
    unfold next
    cases hi : M.instr c.state with
    | halt =>
      exfalso
      have h1 := hc3_onehot h (t+1) ht
      have h0 : ∀ p, OAI.SingleFold.Packed.digit v.B (v.state p) (t+1) = 0 := by
        intro p; rw [hst, hinc p, Fintype.sum_bool]; simp [arc, hi, hc3_digit_zero]
      simp [h0] at h1
    | inc j p =>
      simp only
      refine ⟨fun z => ?_, fun i => ?_⟩
      · rw [hst, hinc z, Fintype.sum_bool]
        simp only [dest, arc, hi, hs c.state, if_true, reduceCtorEq, if_false, add_zero, Option.some.injEq]
        by_cases h1 : z = p
        · subst h1; simp
        · simp [h1, Ne.symm h1]
      · have e := hcu i
        rw [hincr i, hdecr i, hi, hc i] at e
        simp only [add_zero] at e
        by_cases h1 : i = j
        · subst h1; simp at e; simp; omega
        · simp [Ne.symm h1] at e; simp [h1]; omega
    | test j p0 pd =>
      obtain ⟨hv1, hv2, hv3⟩ := htv j p0 pd hi
      obtain ⟨hz, hd⟩ := htc j p0 pd hi
      rw [hc j] at hz hd
      simp only
      by_cases h0 : c.value j = 0
      · simp only [h0, if_true]
        rw [if_pos h0] at hz hd
        refine ⟨fun z => ?_, fun i => ?_⟩
        · rw [hst, hv1 z, hz, hd]; simp
        · have e := hcu i
          rw [hv2 i, hv3 i, hd, hc i] at e
          simpa using e
      · simp only [h0, if_false]
        rw [if_neg h0] at hz hd
        refine ⟨fun z => ?_, fun i => ?_⟩
        · rw [hst, hv1 z, hz, hd]; simp
        · have e := hcu i
          rw [hv2 i, hv3 i, hd, hc i] at e
          by_cases h1 : i = j
          · subst h1; simp at e; simp; omega
          · simp [h1] at e; simp [h1]; omega

theorem hc3_halt_mask : v.state M.halt=v.last := by
  classical
  -- arcs out of q sum to state q unless q is halt
  have harc : ∀ q, (∑ b : Bool, arc M v q b) = if q = M.halt then 0 else v.state q := by
    intro q
    have hb := h.branch q
    have hh := M.halt_iff q
    simp only [Fintype.sum_bool]
    unfold arc
    revert hb hh
    cases M.instr q <;> intro hb hh <;> simp only at hb ⊢
    · simp [hh.mp rfl]
    · simp at hh; simp [hh]
    · simp at hh; simp [hh]; try omega
  -- arcs with no destination vanish
  have hdest : ∀ q b, (∑ p, if dest M q b = some p then arc M v q b else 0) = arc M v q b := by
    intro q b
    cases hd : dest M q b with
    | none =>
      simp only [reduceCtorEq, if_false, Finset.sum_const_zero]
      unfold dest at hd; unfold arc
      revert hd
      cases M.instr q <;> cases b <;> simp
    | some p0 =>
      simp
  have hinc : (∑ p, incoming M v p) = v.mask - v.state M.halt := by
    unfold incoming
    rw [Finset.sum_comm]
    have hswap : ∀ q, (∑ p, ∑ b : Bool, if dest M q b = some p then arc M v q b else 0) =
        ∑ b : Bool, arc M v q b := by
      intro q; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun b _ => hdest q b)
    simp_rw [hswap, harc]
    rw [← h.partition, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun q => q = M.halt) v.state
    rw [Finset.filter_eq' Finset.univ M.halt] at this
    simp only [Finset.mem_univ, if_true, Finset.sum_singleton] at this
    omega
  have hsum : v.mask = 1 + v.B * (v.mask - v.state M.halt) := by
    have := Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => h.transition q)
    rw [h.partition, Finset.sum_add_distrib, ← Finset.mul_sum, hinc] at this
    simpa [Finset.sum_ite_eq'] using this
  have hle : v.state M.halt ≤ v.mask := by
    rw [← h.partition]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hm := h.mask
  have hl := h.last
  have hB : 0 < v.B := by have := h.bound; omega
  have hH : 1 ≤ v.H := by rw [h.full]; exact Nat.one_le_pow _ _ hB
  have key : v.B * v.state M.halt = v.B * v.last := by
    rw [hl]
    have e1 : v.B * (v.mask - v.state M.halt) + v.B * v.state M.halt = v.B * v.mask := by
      rw [← mul_add, Nat.sub_add_cancel hle]
    have e2 : (v.B - 1) * v.mask + v.mask = v.B * v.mask := by
      obtain ⟨c, hc⟩ : ∃ c, v.B = c + 1 := ⟨v.B - 1, by omega⟩
      rw [hc]; simp; ring
    omega
  exact Nat.eq_of_mul_eq_mul_left hB key

omit h in
theorem hc3_upd_core {B b k c D I R F x0 : ℕ} (hBb : B = 4*b) (hb1 : 1 ≤ b) (hk : 0 < k)
    (hclt : c < B^k) (hcd : ∀ t, OAI.SingleFold.Packed.digit B c t < 2*b)
    (hDlt : D < B^k) (hDd : ∀ t, OAI.SingleFold.Packed.digit B D t ≤ 1)
    (hIlt : I < B^k) (hId : ∀ t, OAI.SingleFold.Packed.digit B I t ≤ 1)
    (hcR : c = F*B^(k-1) + R) (hRl : R < B^(k-1)) (hx0 : x0 < B) (he : c + B*D = x0 + B*(R+I)) :
    OAI.SingleFold.Packed.digit B c 0 = x0 ∧ ∀ t < k-1,
      OAI.SingleFold.Packed.digit B c (t+1) + OAI.SingleFold.Packed.digit B D t =
        OAI.SingleFold.Packed.digit B c t + OAI.SingleFold.Packed.digit B I t := by
  have hB0 : 0 < B := by omega
  have hRlt : R < B^k :=
    lt_of_lt_of_le hRl (Nat.pow_le_pow_right hB0 (by omega))
  have hRd : ∀ t < k-1, OAI.SingleFold.Packed.digit B (R) t =
      OAI.SingleFold.Packed.digit B (c) t := by
    intro t ht
    unfold OAI.SingleFold.Packed.digit
    rw [hcR]
    have : F * B^(k-1) = B^t * (B * (F * B^(k-2-t))) := by
      rw [show k - 1 = t + 1 + (k-2-t) by omega, pow_add, pow_add]; ring
    rw [this, add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  have hRb : ∀ s, OAI.SingleFold.Packed.digit B (R) s < 2 * b := by
    intro s
    by_cases hs : s < k - 1
    · rw [hRd s hs]; exact hcd s
    · rw [hc3_digit_big hB0 hRl s (by omega)]; omega
  have hclt' : c < B^(k+1) :=
    lt_of_lt_of_le hclt (Nat.pow_le_pow_right hB0 (by omega))
  have eL : c + B * D = OAI.SingleFold.Packed.pack B (k+1)
      (fun t => OAI.SingleFold.Packed.digit B (c) t +
        (if t = 0 then 0 else OAI.SingleFold.Packed.digit B (D) (t-1))) := by
    rw [hc3_pack_add, hc3_pack_shift, hc3_pack_digits hclt', hc3_pack_digits hDlt, zero_add]
  have eR : x0 + B * (R + I) = OAI.SingleFold.Packed.pack B (k+1)
      (fun t => if t = 0 then x0 else (fun t => OAI.SingleFold.Packed.digit B (R) t +
        OAI.SingleFold.Packed.digit B (I) t) (t-1)) := by
    rw [hc3_pack_shift B k x0 (fun t => OAI.SingleFold.Packed.digit B (R) t +
        OAI.SingleFold.Packed.digit B (I) t), hc3_pack_add, hc3_pack_digits hRlt, hc3_pack_digits hIlt]
  rw [eL, eR] at he
  have key := fun t (ht : t < k + 1) => (hc3_pack_digit _ _ _ (fun s _ => by
      have := hcd s
      split_ifs
      · omega
      · have := hDd (s-1); omega) t ht).symm.trans
    ((congrArg (fun x => OAI.SingleFold.Packed.digit B x t) he).trans
      (hc3_pack_digit _ _ _ (fun s _ => by
        split_ifs
        · exact hx0
        · have := hRb (s-1); have := hId (s-1); dsimp only; omega) t ht))
  refine ⟨?_, fun t ht => ?_⟩
  · have := key 0 (by omega); simpa using this
  · have := key (t+1) (by omega)
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at this
    rw [hRd t ht] at this
    exact this


theorem hc3_last : v.last = v.B^(v.k-1) := by
  have hk := h.length
  have hB0 : 0 < v.B := by have := hc3_B h; omega
  have e := h.last; rw [h.full] at e
  have : v.B^v.k = v.B * v.B^(v.k-1) := by rw [← pow_succ']; congr 1; omega
  rw [this] at e
  exact Nat.eq_of_mul_eq_mul_left hB0 e

theorem hc3_last_digit (t : ℕ) (ht : t < v.k) :
    OAI.SingleFold.Packed.digit v.B (v.B^(v.k-1)) t = if t = v.k-1 then 1 else 0 := by
  have hB := hc3_B h
  have hB0 : 0 < v.B := by omega
  unfold OAI.SingleFold.Packed.digit
  split_ifs with h1
  · subst h1; rw [Nat.div_self (by positivity), Nat.mod_eq_of_lt (by omega)]
  · rw [show v.k-1 = t + (1 + (v.k-2-t)) by omega, pow_add, Nat.mul_div_cancel_left _ (by positivity),
      pow_add, pow_one, Nat.mul_mod_right]

theorem hc3_haltsAt : HaltsAt M d (v.k-1) := by
  have hk := h.length
  have hB := hc3_B h
  have hB0 : 0 < v.B := by omega
  have hlast : v.last = v.B^(v.k-1) := by
    have e := h.last; rw [h.full] at e
    have : v.B^v.k = v.B * v.B^(v.k-1) := by rw [← pow_succ']; congr 1; omega
    rw [this] at e
    exact Nat.eq_of_mul_eq_mul_left hB0 e
  have hm : v.state M.halt = v.B^(v.k-1) := (hc3_halt_mask h).trans hlast
  have hdig : ∀ t < v.k, OAI.SingleFold.Packed.digit v.B (v.state M.halt) t = if t = v.k-1 then 1 else 0 := by
    intro t ht; rw [hm]; unfold OAI.SingleFold.Packed.digit
    split_ifs with h1
    · subst h1; rw [Nat.div_self (by positivity), Nat.mod_eq_of_lt (by omega)]
    · rw [show v.k-1 = t + (1 + (v.k-2-t)) by omega, pow_add, Nat.mul_div_cancel_left _ (by positivity),
        pow_add, pow_one, Nat.mul_mod_right]
  refine ⟨?_, fun t ht heq => ?_⟩
  · have := (hc3_decode h (v.k-1) (by omega)).1 M.halt
    rw [hdig _ (by omega), if_pos rfl] at this
    by_contra hne
    rw [if_neg (Ne.symm hne)] at this
    omega
  · have := (hc3_decode h t (by omega)).1 M.halt
    rw [hdig t (by omega), if_neg (by omega)] at this
    simp [heq] at this

theorem hc3_clock_digits : ∀ t < v.k, OAI.SingleFold.Packed.digit v.B (v.counter none) t = baseC Q d + t := by
  have hk := h.length
  have hBb := hc3_b h
  have hBB := hc3_B h
  have hB0 : 0 < v.B := by omega
  obtain ⟨hclt, hcd⟩ := hc3_counter_info h none
  obtain ⟨_, hcR, hRl⟩ := h.counter none
  rw [hc3_last h] at hcR hRl
  have hlt : v.B^(v.k-1) < v.B^v.k := Nat.pow_lt_pow_right (by omega) (by omega)
  have core := hc3_upd_core (D := v.B^(v.k-1)) (I := v.mask) (x0 := baseC Q d) hBb.1 hBb.2 hk hclt hcd hlt
    (fun t => by
      by_cases ht : t < v.k
      · rw [hc3_last_digit h t ht]; split_ifs <;> omega
      · rw [hc3_digit_big hB0 hlt t (by omega)]; omega)
    (hc3_mask_lt h)
    (fun t => by
      by_cases ht : t < v.k
      · rw [hc3_mask_digit h t ht]
      · rw [hc3_digit_big hB0 (hc3_mask_lt h) t (by omega)]; omega)
    hcR hRl (by unfold baseC; omega) (by have := h.clock; rw [hc3_last h] at this; exact this)
  intro t ht
  induction t with
  | zero => simpa using core.1
  | succ t ih =>
    have e := core.2 t (by omega)
    rw [hc3_last_digit h t (by omega), if_neg (by omega), hc3_mask_digit h t (by omega), ih (by omega)] at e
    omega

theorem hc3_final_none : v.final none = baseC Q d + (v.k - 1) := by
  have hk := h.length
  have hB0 : 0 < v.B := by have := hc3_B h; omega
  obtain ⟨_, hcR, hRl⟩ := h.counter none
  rw [hc3_last h] at hcR hRl
  have e := hc3_clock_digits h (v.k-1) (by omega)
  have hF := h.scale_upper
  unfold OAI.SingleFold.Packed.digit at e
  rw [hcR, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hRl, zero_add,
    Nat.mod_eq_of_lt (by omega)] at e
  exact e

omit h in
theorem hc3_eq_digits {B k x y : ℕ} (hx : x < B^k) (hy : y < B^k)
    (he : ∀ t < k, OAI.SingleFold.Packed.digit B x t = OAI.SingleFold.Packed.digit B y t) : x = y := by
  rw [← hc3_pack_digits hx, ← hc3_pack_digits hy]
  unfold OAI.SingleFold.Packed.pack
  exact Finset.sum_congr rfl (fun t ht => by rw [he t (Finset.mem_range.1 ht)])

theorem hc3_zero_digit (q : Q) (j : J) (p0 pd : Q) (hi : M.instr q = .test j p0 pd) (t : ℕ) (ht : t < v.k) :
    OAI.SingleFold.Packed.digit v.B (v.zeroBranch q) t =
      (if t < v.k - 1 ∧ q = (run M d t).state ∧ (run M d t).value j = 0 then 1 else 0) ∧
    OAI.SingleFold.Packed.digit v.B (v.decBranch q) t =
      (if t < v.k - 1 ∧ q = (run M d t).state ∧ (run M d t).value j ≠ 0 then 1 else 0) := by
  have hb := h.branch q
  rw [hi] at hb
  simp only at hb
  obtain ⟨hs, hc⟩ := hc3_decode h t ht
  by_cases h1 : t < v.k - 1 ∧ q = (run M d t).state
  · obtain ⟨h1, h2⟩ := h1
    have hs' : ∀ p, OAI.SingleFold.Packed.digit v.B (v.state p) t = if p = q then 1 else 0 := by
      intro p; rw [hs p, h2]
    obtain ⟨hz, hd⟩ := hc3_test_choice h t h1 q hs' j p0 pd hi
    rw [hc j] at hz hd
    rw [hz, hd]
    by_cases h3 : (run M d t).value j = 0 <;> simp [h1, h2, h3]
  · have h0 : OAI.SingleFold.Packed.digit v.B (v.state q) t = 0 := by
      rw [hs q, if_neg]
      intro h2
      apply h1
      refine ⟨?_, h2⟩
      by_contra h3
      have ht' : t = v.k - 1 := by omega
      have hh := (hc3_haltsAt h).1
      rw [← ht', ← h2] at hh
      have := (M.halt_iff q).2 hh
      rw [hi] at this; exact absurd this (by simp)
    rw [hc3_zero_of_bits h hb.1 h0, hc3_zero_of_bits h hb.2.1 h0]
    constructor <;> (rw [if_neg]; tauto)

end hc3sec

theorem solution {v u : Witness Q J} (hv : System M d v) (hu : System M d u) : v=u := by
  classical
  have hkv := hv.length
  have hku := hu.length
  -- k
  have ek : v.k = u.k := by
    have a := hc3_haltsAt hv
    have b := hc3_haltsAt hu
    rcases lt_trichotomy (v.k-1) (u.k-1) with c | c | c
    · exact absurd a.1 (b.2 _ c)
    · omega
    · exact absurd b.1 (a.2 _ c)
  -- w
  have ew : v.w = u.w := by
    have fv := hc3_final_none hv
    have fu := hc3_final_none hu
    have s1 := hv.scale_lower; have s2 := hv.scale_upper
    have s3 := hu.scale_lower; have s4 := hu.scale_upper
    have pv := hv.power; have pu := hu.power
    have bv := hv.base; have bu := hu.base
    have key : ∀ w1 w2 : ℕ, w1 < w2 → ¬ (2 * (baseC Q d + (v.k-1)) < 2^w1 ∧ 2^w1 ≤ 4 * (baseC Q d + (v.k-1)) ∧
        2 * (baseC Q d + (v.k-1)) < 2^w2 ∧ 2^w2 ≤ 4 * (baseC Q d + (v.k-1))) := by
      intro w1 w2 hw ⟨a1, a2, a3, a4⟩
      have : 2^(w1+1) ≤ 2^w2 := Nat.pow_le_pow_right (by norm_num) hw
      rw [pow_succ] at this; omega
    have c1 : 2 * (baseC Q d + (v.k-1)) < 2^v.w ∧ 2^v.w ≤ 4 * (baseC Q d + (v.k-1)) := by
      constructor <;> omega
    have c2 : 2 * (baseC Q d + (v.k-1)) < 2^u.w ∧ 2^u.w ≤ 4 * (baseC Q d + (v.k-1)) := by
      rw [ek]; rw [ek] at fv; constructor <;> omega
    rcases lt_trichotomy v.w u.w with c | c | c
    · exact absurd ⟨c1.1, c1.2, c2.1, c2.2⟩ (key _ _ c)
    · exact c
    · exact absurd ⟨c2.1, c2.2, c1.1, c1.2⟩ (key _ _ c)
  have eB : v.B = u.B := by rw [hv.power, hu.power, ew]
  have eb : v.b = u.b := by have := hv.base; have := hu.base; omega
  have eH : v.H = u.H := by rw [hv.full, hu.full, eB, ek]
  have elast : v.last = u.last := by rw [hc3_last hv, hc3_last hu, eB, ek]
  have hB1 : 0 < v.B - 1 := by have := hc3_B hv; omega
  have emask : v.mask = u.mask := by
    have a := hv.mask; have b := hu.mask
    rw [eH, eB] at a
    exact Nat.eq_of_mul_eq_mul_left (by rw [← eB]; exact hB1) (a.trans b.symm)
  have estate : v.state = u.state := by
    funext q
    apply hc3_eq_digits (hc3_state_lt hv q) (by rw [eB, ek]; exact hc3_state_lt hu q)
    intro t ht
    rw [(hc3_decode hv t ht).1 q, eB, (hc3_decode hu t (by omega)).1 q]
  have ecounter : v.counter = u.counter := by
    funext jj
    apply hc3_eq_digits (hc3_counter_info hv jj).1 (by rw [eB, ek]; exact (hc3_counter_info hu jj).1)
    intro t ht
    cases jj with
    | none => rw [hc3_clock_digits hv t ht, eB, hc3_clock_digits hu t (by omega)]
    | some j => rw [(hc3_decode hv t ht).2 j, eB, (hc3_decode hu t (by omega)).2 j]
  have hlpos : 0 < v.last := by rw [hc3_last hv]; have := hc3_B hv; exact Nat.pow_pos (by omega)
  have efr : ∀ jj, v.final jj = u.final jj ∧ v.rem jj = u.rem jj := by
    intro jj
    obtain ⟨_, a1, a2⟩ := hv.counter jj
    obtain ⟨_, b1, b2⟩ := hu.counter jj
    rw [← ecounter, ← elast] at b1; rw [← elast] at b2
    have r1 : v.counter jj % v.last = v.rem jj := by
      rw [a1, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt a2]
    have r2 : v.counter jj % v.last = u.rem jj := by
      rw [b1, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b2]
    have er : v.rem jj = u.rem jj := r1.symm.trans r2
    refine ⟨?_, er⟩
    rw [er] at a1
    have : v.final jj * v.last = u.final jj * v.last := by omega
    exact Nat.eq_of_mul_eq_mul_right hlpos this
  have ezd : v.zeroBranch = u.zeroBranch ∧ v.decBranch = u.decBranch ∧ v.complement = u.complement := by
    have all : ∀ q, v.zeroBranch q = u.zeroBranch q ∧ v.decBranch q = u.decBranch q ∧
        v.complement q = u.complement q := by
      intro q
      have bv := hv.branch q
      have bu := hu.branch q
      cases hi : M.instr q with
      | test j p0 pd =>
        rw [hi] at bv bu
        simp only at bv bu
        have zlt : ∀ x, OAI.SingleFold.Counter.Bits x (v.state q) → x < v.B^v.k :=
          fun x hx => lt_of_le_of_lt (hc3_bits_le hx) (hc3_state_lt hv q)
        have zlt' : ∀ x, OAI.SingleFold.Counter.Bits x (u.state q) → x < v.B^v.k := by
          intro x hx; rw [eB, ek]; exact lt_of_le_of_lt (hc3_bits_le hx) (hc3_state_lt hu q)
        have ez : v.zeroBranch q = u.zeroBranch q := by
          apply hc3_eq_digits (zlt _ bv.1) (zlt' _ bu.1)
          intro t ht
          rw [(hc3_zero_digit hv q j p0 pd hi t ht).1, eB, (hc3_zero_digit hu q j p0 pd hi t (by omega)).1, ek]
        have ed : v.decBranch q = u.decBranch q := by
          apply hc3_eq_digits (zlt _ bv.2.1) (zlt' _ bu.2.1)
          intro t ht
          rw [(hc3_zero_digit hv q j p0 pd hi t ht).2, eB, (hc3_zero_digit hu q j p0 pd hi t (by omega)).2, ek]
        refine ⟨ez, ed, ?_⟩
        have := bv.2.2.2; have := bu.2.2.2
        rw [← ez, ← emask] at this
        omega
      | halt => rw [hi] at bv bu; simp only at bv bu; omega
      | inc j p => rw [hi] at bv bu; simp only at bv bu; omega
    exact ⟨funext (fun q => (all q).1), funext (fun q => (all q).2.1), funext (fun q => (all q).2.2)⟩
  have efinal : v.final = u.final := funext (fun jj => (efr jj).1)
  have erem : v.rem = u.rem := funext (fun jj => (efr jj).2)
  obtain ⟨ez, ed, ec⟩ := ezd
  cases v; cases u
  simp only [Witness.mk.injEq]
  exact ⟨ew, eB, eb, ek, eH, elast, emask, estate, ez, ed, ec, ecounter, efinal, erem⟩

