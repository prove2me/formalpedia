-- Prove2me | solution 2 for OAI.SingleFold.Packed.bits_mask
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:00:56.022179+00:00
-- url     : https://prove2.me/submissions/8e427d99-959c-43ed-85d2-c23d47152a7f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Packed.lean:L156-L175
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Packed.bits_mask. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_SingleFold_Packed_bits_testBit

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace SingleFold.Packed

lemma testBit_digit (w x t j : ℕ) :
    (digit (2^w) x t).testBit j=(decide (j < w) && x.testBit (w*t+j)) := by
  unfold digit
  rw [Nat.testBit_mod_two_pow,←pow_mul]
  congr 1
  simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.div_div_eq_div_mul,←pow_add]

lemma bits_blocks {w : ℕ} (hw : 0 < w) (x y : ℕ) :
    Bits x y ↔ ∀t, Bits (digit (2^w) x t) (digit (2^w) y t) := by
  simp only [bits_testBit,testBit_digit,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h t j hj
    exact ⟨hj.1,h _ hj.2⟩
  · intro h i hi
    have hh := h (i/w) (i%w) ⟨Nat.mod_lt i hw, by simpa [Nat.div_add_mod] using hi⟩
    simpa [Nat.div_add_mod] using hh.2

lemma digit_zero (B t : ℕ) : digit B 0 t=0 := by simp [digit]
lemma digit_high {B x t : ℕ} (hx : x < B^t) : digit B x t=0 := by simp [digit,Nat.div_eq_of_lt hx]

lemma pack_succ (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=pack B k f+f k*B^k := by
  simp [pack,Finset.sum_range_succ]
lemma pack_cons (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=f 0+B*pack B k (fun t=>f (t+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros; ring
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_mul (B k c : ℕ) (f : ℕ → ℕ) :
    pack B k (fun t=>c*f t)=c*pack B k f := by simp [pack,Finset.mul_sum,mul_assoc]
lemma pack_lt {B k : ℕ} (_hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) : pack B k f < B^k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack_succ,pow_succ]
    have hi := ih (fun t ht=>hf t (by omega))
    have hh := hf k (by omega)
    nlinarith only [hi,hh,pow_pos _hB k]

lemma digit_pack {B k : ℕ} (hB : 0 < B) {f : ℕ → ℕ} (hf : ∀ t < k,f t < B) (i : ℕ) :
    digit B (pack B k f) i=if i < k then f i else 0 := by
  induction k generalizing f i with
  | zero => simp [pack_zero,digit_zero]
  | succ k ih =>
    rw [pack_cons]
    cases i with
    | zero => simp [digit,Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      rw [digit,pow_succ',←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt (hf 0 (by omega)),zero_add]
      simpa only [digit, Nat.add_lt_add_iff_right] using ih (fun t ht=>hf (t+1) (by omega)) i

lemma bits_and (x y : ℕ) : Bits x y ↔ x&&&y=x := by
  rw [bits_testBit]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i  <;> simp [hx,h i]
  · intro h i hi
    have hh := congrArg (fun n=>Nat.testBit n i) h
    simpa [Nat.testBit_and,hi] using hh
lemma bits_le {x y : ℕ} (h : Bits x y) : x ≤ y := by
  rw [←(bits_and x y).mp h]
  exact Nat.and_le_right
lemma bits_refl (x : ℕ) : Bits x x := fun _=>le_rfl
lemma bits_zero_right (x : ℕ) : Bits x 0 ↔ x=0 := by
  exact ⟨fun h=>Nat.eq_zero_of_le_zero (bits_le h),fun h=>h ▸ bits_refl 0⟩
lemma ones_mul (B k c : ℕ) : c*ones B k=pack B k (fun _=>c) := by
  simpa [ones] using (pack_mul B k c (fun _=>1)).symm
lemma bits_mask {w k c x : ℕ} (hw : 0 < w) (hc : c < 2^w) :
    Bits x (c*ones (2^w) k) ↔ x < (2^w)^k ∧ ∀t < k, Bits (digit (2^w) x t) c := by
  rw [ones_mul]
  have hpos := Nat.two_pow_pos w
  have hlt := pack_lt hpos (fun _ _=>hc : ∀t < k,c < 2^w)
  constructor
  · intro h
    refine ⟨lt_of_le_of_lt (bits_le h) hlt,?_⟩
    intro t ht
    have hh := (bits_blocks hw x _).mp h t
    rwa [digit_pack hpos (fun _ _=>hc),ite_eq_left ht] at hh
  · rintro ⟨hx,h⟩
    apply (bits_blocks hw x _).mpr
    intro t
    rw [digit_pack hpos (fun _ _=>hc)]
    split_ifs with ht
    · exact h t ht
    · rw [bits_zero_right]
      apply digit_high
      exact lt_of_lt_of_le hx (Nat.pow_le_pow_right hpos (by omega))
end SingleFold.Packed

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Packed.bits_mask := @_root_.OAI.SingleFold.Packed.bits_mask
