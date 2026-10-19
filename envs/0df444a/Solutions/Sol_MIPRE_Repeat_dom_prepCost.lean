-- Prove2me | solution 1 for MIPRE.Repeat.dom_prepCost
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:48:44.752297+00:00
-- url     : https://prove2.me/submissions/17edbf1e-0a06-435d-ba76-6ef953c276f8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DeciderCost.lean (solution of MIPRE.Repeat.dom_prepCost);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Definitions.Def_MIPRE_Foundations_Repeat_DeciderCost
import Theorems.Thm_MIPRE_Cost_Data_length_le_size_list_prime
import Theorems.Thm_MIPRE_Cost_Data_size_sum_stackStep_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
/-- So the whole run adds at most the length of the string. -/
theorem size_sum_stackRun_le (x : BitStr) (s : List Data) :
    ((stackRun x s).map size).sum ≤ (s.map size).sum + x.length := by
  induction x generalizing s with
  | nil => simp
  | cons bit x ih =>
    rw [stackRun_cons]
    have h1 := ih (stackStep s bit)
    have h2 := size_sum_stackStep_le s bit
    simp only [List.length_cons]
    omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
/-- **What a string of length `L` can parse to**: a datum of size at most `L`, or `nil` when
the run leaves the stack empty. -/
theorem size_parse_le (x : BitStr) : (parse x).size ≤ max 1 x.length := by
  have h := size_sum_stackRun_le x []
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at h
  unfold parse
  rcases hs : stackRun x [] with _ | ⟨d, t⟩
  · simp
  · rw [hs] at h
    simp only [List.map_cons, List.sum_cons] at h
    simp only [List.headD_cons]
    exact le_max_of_le_right (by omega)
end
end MIPRE.Cost.Data

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem of_le {c m e v v' : ℕ} (h : Dom W X K c m e v) (hv : v' ≤ v) : Dom W X K c m e v' :=
  hv.trans h
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem const (c : ℕ) : Dom W X K c 0 0 c := by simp [Dom]
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem ofLeW {v : ℕ} (h : v ≤ W) : Dom W X K 1 1 0 v := by simp [Dom]; omega
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
/-- An affine function of `W` is dominated by `(a + b)(W + 1)`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : Dom W X K (a + b) 1 0 v := by
  simp only [Dom, pow_one, zero_mul, pow_zero, mul_one]
  nlinarith
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
/-- An affine function of `X` is dominated by `(a + b) X^{K+1}`. -/
theorem ofAffineX (hX : 1 ≤ X) {a b v : ℕ} (h : v ≤ a * X + b) : Dom W X K (a + b) 0 1 v := by
  simp only [Dom, pow_zero, mul_one, one_mul]
  have h1 : X ≤ X ^ (K + 1) := Nat.le_self_pow (by omega) X
  have h2 : b ≤ b * X := Nat.le_mul_of_pos_right b hX
  nlinarith
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem ofLeX (hX : 1 ≤ X) {v : ℕ} (h : v ≤ X) : Dom W X K 1 0 1 v := by
  simp only [Dom, one_mul, pow_zero, one_mul]
  exact h.trans (Nat.le_self_pow (by omega) X)
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : Dom W X K c m e v) (hc : c ≤ c') (hm : m ≤ m')
    (he : e ≤ e') : Dom W X K c' m' e' v := by
  unfold Dom at h ⊢
  refine h.trans ?_
  gcongr <;> first | omega | exact Nat.mul_le_mul_right _ he
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : Dom W X K c₁ m₁ e₁ v₁)
    (h₂ : Dom W X K c₂ m₂ e₂ v₂) : Dom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold Dom at h₁' h₂' ⊢
  rw [Nat.add_mul, Nat.add_mul]
  omega
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : Dom W X K c₁ m₁ e₁ v₁) (h₂ : Dom W X K c₂ m₂ e₂ v₂) :
    Dom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold Dom at h₁ h₂ ⊢
  calc v₁ * v₂ ≤ (c₁ * (W + 1) ^ m₁ * X ^ (e₁ * (K + 1))) * (c₂ * (W + 1) ^ m₂ * X ^ (e₂ * (K + 1))) :=
        Nat.mul_le_mul h₁ h₂
    _ = c₁ * c₂ * (W + 1) ^ (m₁ + m₂) * X ^ ((e₁ + e₂) * (K + 1)) := by
        rw [pow_add, Nat.add_mul, pow_add]; ring
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
theorem nat_size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
theorem esize_nat_le' (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := nat_size_le_self x; omega)
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_esize {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (esize x) :=
  Dom.ofAffine (by have := esize_nat_le' x; omega)
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_toUnaryCost : ∃ c m e, ∀ (W X K : ℕ) {x : ℕ}, 1 ≤ X → x ≤ W →
    Dom W X K c m e (toUnaryCost x) := by
  exact ⟨_, _, _, fun W X K {x} hX hx => by
    unfold toUnaryCost
    have h1 : Dom W X K (1 + 2) 1 0 (Nat.size x + 2) :=
      Dom.ofAffine (by have := nat_size_le_self x; omega)
    have h2 : Dom W X K (1 + 1) 1 0 (x + 1) := Dom.ofAffine (by omega)
    have h3 : Dom W X K (4 + 14) 1 0 (4 * x + 14) := Dom.ofAffine (by omega)
    have h5 : Dom W X K (8 + 0) 1 0 (8 * x) := Dom.ofAffine (by omega)
    exact h1.mul ((((h2.mul h3).add hX ((Dom.const 7).mul (dom_esize hx))).add hX h5).add hX
      (Dom.const 90))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_powCost : ∃ c m e', ∀ (W X K : ℕ) {e L sz : ℕ}, 1 ≤ X → e ≤ W → L ≤ 2 * W →
    sz ≤ 12 * W + 3 → Dom W X K c m e' (powCost e L sz) := by
  exact ⟨_, _, _, fun W X K {e L sz} hX he hL hsz => by
    unfold powCost
    have h1 : Dom W X K (1 + 1) 1 0 (e + 1) := Dom.ofAffine (by omega)
    have h2 : Dom W X K (2 + 1) 1 0 (L + 1) := Dom.ofAffine (by omega)
    have h3 : Dom W X K (12 + 3) 1 0 sz := Dom.ofAffine hsz
    have h4 : Dom W X K (2 + 0) 1 0 L := Dom.ofAffine (by omega)
    exact h1.mul (((Dom.const 8).mul h2).mul (((h3.add hX (((Dom.const 2).mul (Dom.ofLeW he)).mul
      h4)).add hX (Dom.ofLeW he)).add hX (Dom.const 14)))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
theorem length_toList_le (d : Data) : (toList d).length + 1 ≤ d.size := by
  have := length_le_size_list_prime (toList d)
  rwa [list_toList] at this
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
theorem size_ofBool_bitOf_le (a : Data) : (ofBool (bitOf a)).size ≤ a.size := by
  cases a with
  | nil => simp [bitOf, ofBool, size]
  | cons a b => simp only [bitOf, ofBool, size]; have := size_pos a; have := size_pos b; omega
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
theorem size_list_map_ofBool_bitOf_le (l : List Data) :
    (list ((l.map bitOf).map ofBool)).size ≤ (list l).size := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, size_list_cons]
    have := size_ofBool_bitOf_le a
    omega
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
/-- Sanitizing a datum into a bit string does not increase its size. -/
theorem size_encode_bitsOf_le (d : Data) : (encode (bitsOf (toList d)) : Data).size ≤ d.size := by
  have := size_list_map_ofBool_bitOf_le (toList d)
  rw [list_toList] at this
  rw [encode_bitStr_eq_list]
  exact this
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
theorem size_parse_bitsOf_le (d : Data) : (parse (bitsOf (toList d))).size ≤ d.size := by
  have h1 := size_parse_le (bitsOf (toList d))
  have h2 := length_toList_le d
  simp only [bitsOf, List.length_map] at h1 ⊢
  have := size_pos d
  omega
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_bitsCost : ∃ c m e, ∀ (W X K : ℕ) {L sz : ℕ}, 1 ≤ X → L ≤ X → sz ≤ X →
    Dom W X K c m e (bitsCost L sz) := by
  exact ⟨_, _, _, fun W X K {L sz} hX hL hsz => by
    unfold bitsCost
    have hL' : Dom W X K 1 0 1 L := Dom.ofLeX hX hL
    have hsz' : Dom W X K 1 0 1 sz := Dom.ofLeX hX hsz
    exact ((hL'.add hX (Dom.const 2)).mul ((hsz'.add hX ((Dom.const 2).mul hL')).add hX
      (Dom.const 15))).add hX ((hL'.add hX (Dom.const 2)).mul (((Dom.const 4).mul hL').add hX
      (Dom.const 20)))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_lenCost : ∃ c m e, ∀ (W X K : ℕ) {L sz : ℕ}, 1 ≤ X → L ≤ X → sz ≤ X →
    Dom W X K c m e (lenCost L sz) := by
  exact ⟨_, _, _, fun W X K {L sz} hX hL hsz => by
    unfold lenCost
    have hL' : Dom W X K 1 0 1 L := Dom.ofLeX hX hL
    have hsz' : Dom W X K 1 0 1 sz := Dom.ofLeX hX hsz
    exact ((hL'.add hX (Dom.const 1)).add hX (Dom.const 1)).mul
      ((((hsz'.add hX (Dom.const 1)).add hX ((Dom.const 2).mul hL')).add hX (Dom.const 13)))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_eqCost (c₁ m₁ e₁ c₂ m₂ e₂ : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {l₁ l₂ : Data}, 1 ≤ X →
    Dom W X K c₁ m₁ e₁ l₁.size → Dom W X K c₂ m₂ e₂ l₂.size → Dom W X K c m e (eqCost l₁ l₂) := by
  exact ⟨_, _, _, fun W X K {l₁ l₂} hX h₁ h₂ => by
    unfold eqCost
    exact ((h₁.of_le (spine_le_size l₁)).add hX (Dom.const 1)).mul ((h₁.add hX h₂).add hX
      (Dom.const 21))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_parseCost : ∃ c m e, ∀ (W X K : ℕ) {x : BitStr}, 1 ≤ X → x.length ≤ X →
    Dom W X K c m e (parseCost x) := by
  exact ⟨_, _, _, fun W X K {x} hX hx => by
    unfold parseCost
    have hL' : Dom W X K 1 0 1 x.length := Dom.ofLeX hX hx
    have he : Dom W X K (4 + 1) 0 1 (encode x : Data).size :=
      Dom.ofAffineX hX ((esize_bitStr_le x).trans (by omega))
    exact (hL'.add hX (Dom.const 2)).mul ((he.add hX ((Dom.const 2).mul hL')).add hX
      (Dom.const 25))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_serCost : ∃ c m e, ∀ (W X K : ℕ) {d : Data}, 1 ≤ X → d.size ≤ X →
    Dom W X K c m e (serCost d) := by
  exact ⟨_, _, _, fun W X K {d} hX hd => by
    unfold serCost
    have hd' : Dom W X K 1 0 1 d.size := Dom.ofLeX hX hd
    exact ((((Dom.const 3).mul hd').add hX (Dom.const 2)).mul (((Dom.const 16).mul hd').add hX
      (Dom.const 42))).add hX ((hd'.add hX (Dom.const 2)).mul (((Dom.const 5).mul hd').add hX
      (Dom.const 30)))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_dblCost : ∃ c m e, ∀ (W X K : ℕ) {mm a : ℕ}, 1 ≤ X → 2 ^ mm ≤ W → a ≤ W →
    Dom W X K c m e (dblCost mm a) := by
  exact ⟨_, _, _, fun W X K {m a} hX hm ha => by
    unfold dblCost
    have hm' : m ≤ W := (Nat.lt_two_pow_self).le.trans hm
    have h2 : Dom W X K 1 1 0 (2 ^ m) := Dom.ofLeW hm
    have ha' : Dom W X K 1 1 0 a := Dom.ofLeW ha
    exact ((Dom.ofLeW hm').add hX (Dom.const 1)).mul (((((h2.mul ha').add hX (Dom.const 1)).mul
      ((((Dom.const 4).mul h2).mul ha').add hX (Dom.const 14))).add hX
      (((Dom.const 10).mul h2).mul ha')).add hX ((Dom.const 2).mul (Dom.ofLeW hm')) |>.add hX
      (Dom.const 32))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_esize' {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (encode x : Data).size :=
  dom_esize hx
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem _root_.solution (cd md ed : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {sP dP : Data}
    {lam tau beta n s : ℕ} {xD yD aD bD : Data} {td : ℕ}, 1 ≤ X → 1 ≤ W →
    Dom W X K cd md ed td → sP.size ≤ W → dP.size ≤ W → lam ≤ W → tau ≤ W → beta ≤ W → n ≤ W →
    s ≤ W → 2 ^ (tau * (Nat.size lam + Nat.size n)) ≤ W →
    2 ^ (beta * (Nat.size lam + Nat.size n)) ≤ W → xD.size + yD.size + aD.size + bD.size + 3 ≤ X →
    Dom W X K c m e (prepCost sP dP lam tau beta n s xD yD aD bD td) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_toUnaryCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_powCost
  obtain ⟨c₃, m₃, e₃, h₃⟩ := dom_dblCost
  obtain ⟨c₄, m₄, e₄, h₄⟩ := dom_bitsCost
  obtain ⟨c₅, m₅, e₅, h₅⟩ := dom_lenCost
  obtain ⟨c₆, m₆, e₆, h₆⟩ := dom_eqCost 3 0 1 3 2 0
  obtain ⟨c₇, m₇, e₇, h₇⟩ := dom_eqCost 5 0 1 1 0 1
  obtain ⟨c₈, m₈, e₈, h₈⟩ := dom_parseCost
  obtain ⟨c₉, m₉, e₉, h₉⟩ := dom_serCost
  exact ⟨_, _, _, fun W X K {sP dP lam tau beta n s xD yD aD bD td} hX h1W htd hsP hdP hlam htau
      hbeta hn hs hreps hparse hd => by
    unfold prepCost prepPreCost
    have hxl := length_toList_le xD
    have hyl := length_toList_le yD
    have hal := length_toList_le aD
    have hbl := length_toList_le bD
    have hbx : (bitsOf (toList xD)).length = (toList xD).length := List.length_map ..
    have hby : (bitsOf (toList yD)).length = (toList yD).length := List.length_map ..
    have hba : (bitsOf (toList aD)).length = (toList aD).length := List.length_map ..
    have hbb : (bitsOf (toList bD)).length = (toList bD).length := List.length_map ..
    have hex := size_encode_bitsOf_le xD
    have hey := size_encode_bitsOf_le yD
    have hea := size_encode_bitsOf_le aD
    have heb := size_encode_bitsOf_le bD
    have hpa := size_parse_bitsOf_le aD
    have hpb := size_parse_bitsOf_le bD
    have hL : Nat.size lam + Nat.size n ≤ 2 * W := by
      have := nat_size_le_self lam; have := nat_size_le_self n; omega
    have hsz : (encode lam : Data).size + (encode n : Data).size + 1 ≤ 12 * W + 3 := by
      have := esize_nat_le' lam; have := esize_nat_le' n
      have e1 : (encode lam : Data).size = esize lam := rfl
      have e2 : (encode n : Data).size = esize n := rfl
      omega
    have dOfX : ∀ {v : ℕ}, v ≤ X → Dom W X K 1 0 1 v := fun h => Dom.ofLeX hX h
    have hs1x : Dom W X K 3 0 1 (ofNat (bitsOf (toList xD)).length).size := by
      rw [size_ofNat]
      exact (Dom.ofAffineX hX (a := 2) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs1y : Dom W X K 3 0 1 (ofNat (bitsOf (toList yD)).length).size := by
      rw [size_ofNat]
      exact (Dom.ofAffineX hX (a := 2) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs2 : Dom W X K 3 2 0 (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)).size := by
      rw [size_ofNat]
      exact ((((Dom.const 2).mul ((Dom.ofLeW hreps).mul (Dom.ofLeW hs))).add hX
        (Dom.const 1)).mono hX (by norm_num) (by norm_num) (by norm_num))
    have hs3a : Dom W X K 5 0 1 (encode (parse (bitsOf (toList aD))).toBitsPost : Data).size := by
      have := esize_bitStr_le (parse (bitsOf (toList aD))).toBitsPost
      have e : esize (parse (bitsOf (toList aD))).toBitsPost =
        (encode (parse (bitsOf (toList aD))).toBitsPost : Data).size := rfl
      simp only [length_toBitsPost] at this
      exact (Dom.ofAffineX hX (a := 4) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs3b : Dom W X K 5 0 1 (encode (parse (bitsOf (toList bD))).toBitsPost : Data).size := by
      have := esize_bitStr_le (parse (bitsOf (toList bD))).toBitsPost
      have e : esize (parse (bitsOf (toList bD))).toBitsPost =
        (encode (parse (bitsOf (toList bD))).toBitsPost : Data).size := rfl
      simp only [length_toBitsPost] at this
      exact (Dom.ofAffineX hX (a := 4) (b := 1) (by omega)).mono hX (by norm_num) le_rfl le_rfl
    have hs4a : Dom W X K 1 0 1 (encode (bitsOf (toList aD)) : Data).size := dOfX (by omega)
    have hs4b : Dom W X K 1 0 1 (encode (bitsOf (toList bD)) : Data).size := dOfX (by omega)
    have q1 := htd.add hX (h₁ W X K hX hs)
    have q2 := q1.add hX (h₁ W X K hX htau)
    have q3 := q2.add hX (h₁ W X K hX hbeta)
    have q4 := q3.add hX (h₂ W X K hX htau hL hsz)
    have q5 := q4.add hX (h₂ W X K hX hbeta hL hsz)
    have q6 := q5.add hX (h₃ W X K hX hreps hs)
    have q7 := q6.add hX (h₃ W X K hX hreps h1W)
    have q8 := q7.add hX (h₃ W X K hX hparse h1W)
    have q9 := q8.add hX (h₄ W X K (L := (toList xD).length) (sz := xD.size) hX (by omega) (by omega))
    have q10 := q9.add hX (h₄ W X K (L := (toList yD).length) (sz := yD.size) hX (by omega) (by omega))
    have q11 := q10.add hX (h₄ W X K (L := (toList aD).length) (sz := aD.size) hX (by omega) (by omega))
    have q12 := q11.add hX (h₄ W X K (L := (toList bD).length) (sz := bD.size) hX (by omega) (by omega))
    have q13 := q12.add hX (h₅ W X K (L := (bitsOf (toList xD)).length)
      (sz := (encode (bitsOf (toList xD)) : Data).size) hX (by omega) (by omega))
    have q14 := q13.add hX (h₅ W X K (L := (bitsOf (toList yD)).length)
      (sz := (encode (bitsOf (toList yD)) : Data).size) hX (by omega) (by omega))
    have q15 := q14.add hX (h₆ W X K hX hs1x hs2)
    have q16 := q15.add hX (h₆ W X K hX hs1y hs2)
    have q17 := q16.add hX (h₈ W X K (x := bitsOf (toList aD)) hX (by omega))
    have q18 := q17.add hX (h₉ W X K (d := parse (bitsOf (toList aD))) hX (by omega))
    have q19 := q18.add hX (h₇ W X K hX hs3a hs4a)
    have q20 := q19.add hX (h₈ W X K (x := bitsOf (toList bD)) hX (by omega))
    have q21 := q20.add hX (h₉ W X K (d := parse (bitsOf (toList bD))) hX (by omega))
    have q22 := q21.add hX (h₇ W X K hX hs3b hs4b)
    have r1 := (((((((((Dom.ofLeW hsP).add hX (Dom.ofLeW hdP)).add hX (dom_esize' hlam)).add hX
      (dom_esize' htau)).add hX (dom_esize' hbeta)).add hX (dom_esize' hn)).add hX
      (dOfX (v := xD.size) (by omega))).add hX (dOfX (v := yD.size) (by omega))).add hX
      (dOfX (v := aD.size) (by omega))).add hX (dOfX (v := bD.size) (by omega))
    have r2 := ((((((((Dom.ofLeW hdP).add hX (dom_esize' hn)).add hX
      ((Dom.const 2).mul (Dom.ofLeW hs))).add hX ((Dom.const 2).mul (Dom.ofLeW hparse))).add hX
      ((Dom.const 2).mul (Dom.ofLeW hreps))).add hX
      (dOfX (v := (encode (bitsOf (toList xD)) : Data).size) (by omega))).add hX
      (dOfX (v := (encode (bitsOf (toList yD)) : Data).size) (by omega))).add hX
      (dOfX (v := (parse (bitsOf (toList aD))).size) (by omega))).add hX
      (dOfX (v := (parse (bitsOf (toList bD))).size) (by omega))
    exact ((((Dom.const 6).mul q22).add hX ((Dom.const 8).mul r1)).add hX (Dom.const 500)).add hX
      ((Dom.const 8).mul r2) |>.add hX (Dom.const 100)⟩
end MIPRE.Repeat
