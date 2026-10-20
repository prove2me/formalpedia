-- Prove2me | solution 1 for OAI.SingleFold.Counter.System.counter_update
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:53:12.92998+00:00
-- url     : https://prove2.me/submissions/bd7ae3d3-3f4b-4847-9a1b-1b9f1c360e68

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

open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h
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

theorem solution (j : J) :
    digit v.B (v.counter (some j)) 0=d j ∧ ∀t < v.k-1,
    digit v.B (v.counter (some j)) (t+1)+digit v.B (decrements M v j) t=
      digit v.B (v.counter (some j)) t+digit v.B (increments M v j) t := by
  exact hc3_counter_update h j

