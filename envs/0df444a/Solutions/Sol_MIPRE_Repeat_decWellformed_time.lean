-- Prove2me | solution 1 for MIPRE.Repeat.decWellformed_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:52:08.637081+00:00
-- url     : https://prove2.me/submissions/24313688-73f9-4e2e-967b-c33ef12780f2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DeciderCost.lean (solution of MIPRE.Repeat.decWellformed_time);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Prog_coordLoop_runs_bounded
import Theorems.Thm_MIPRE_Cost_Prog_prepProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_runs
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Repeat_dom_prepCost
import Theorems.Thm_MIPRE_Repeat_loop_calls_time

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

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkProg_wellScoped : bitWalkProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitWalkBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem pairTakeProg_wellScoped : pairTakeProg.WellScoped 1 := by
  simp [pairTakeProg, WellScoped, takeBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
/-- The size of the encoded dimension query. -/
theorem size_encode_dimension : (encode CL.Sampler.Query.dimension : Data).size = 9 := rfl
end
end MIPRE.Cost.Prog

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem le {c m e v : ℕ} (h : Dom W X K c m e v) : v ≤ c * (W + 1) ^ m * X ^ (e * (K + 1)) := h
end
end MIPRE.Repeat.Dom

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

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem pow {c m e v : ℕ} (h : Dom W X K c m e v) (p : ℕ) :
    Dom W X K (c ^ p) (m * p) (e * p) (v ^ p) := by
  induction p with
  | zero => simpa using const 1
  | succ p ih =>
    have := ih.mul h
    simpa [pow_succ, Nat.mul_succ] using this
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
/-- `X^K` itself: one unit of the exponent. -/
theorem powK (hX : 1 ≤ X) : Dom W X K 1 0 1 (X ^ K) := by
  simp only [Dom, one_mul, pow_zero]
  exact Nat.pow_le_pow_right hX (by omega)
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
theorem univ_bound_le {y : ℕ} (hy : 1 ≤ y) : selfUniversal.bound.eval y ≤ cU * y ^ dU :=
  polynomial_eval_le_sum_coeff_mul_pow _ hy
end
end MIPRE.Repeat

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
/-- The time of the dimension query through the universal machine. -/
theorem dim_call_time (hS : S.TimeBoundAt n R.S R.k) :
    ∃ td, td ≤ selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k) ∧
      Eval [Data.cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension))]
        selfUniversal.univ (encode (S.dim n)) td := by
  obtain ⟨t, h⟩ := S.runs_dimension n
  obtain ⟨r', t', ht', h'⟩ := hS (encode CL.Sampler.Query.dimension)
  obtain ⟨rfl, rfl⟩ := h.deterministic h'
  obtain ⟨t'', ht'', h''⟩ := selfUniversal.time_le _ _ _ _ h
  refine ⟨t'', ht''.trans (polynomial_eval_mono _ ?_), h''⟩
  have hd : (encode (n, CL.Sampler.Query.dimension) : Data).size = esize n + 9 + 1 := rfl
  simp only [size_encode_dimension, show (9 : ℕ) + 1 = 10 from rfl] at ht'
  rw [hd]
  omega
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
/-- The self-interpreter's overhead polynomial at a dominated argument. -/
theorem dom_univ_bound (cy my ey : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X → 1 ≤ y →
    Dom W X K cy my ey y → Dom W X K c m e (selfUniversal.bound.eval y) := by
  exact ⟨_, _, _, fun W X K {y} _ hy h => ((Dom.const cU).mul (h.pow dU)).of_le (univ_bound_le hy)⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
/-- The argument of the dimension query's bound. -/
theorem dom_yd : ∃ c m e, ∀ (W X K : ℕ) {p n RS pk : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RS ≤ W →
    pk ≤ W → Dom W X K c m e (p + (esize n + 10) + RS * pk) := by
  exact ⟨_, _, _, fun W X K {p n RS pk} hX hp hn hRS hpk =>
    ((Dom.ofLeW hp).add hX ((dom_esize hn).add hX (Dom.const 10))).add hX
      ((Dom.ofLeW hRS).mul (Dom.ofLeW hpk))⟩
end
end MIPRE.Repeat

namespace MIPRE.Cost.Prog
section
open Data
theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_wellScoped : preProg.WellScoped 1 := by
  simp only [preProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, ⟨by omega, by omega, by omega⟩, ⟨by omega, pairTakeProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega, trivial,
    by omega, ⟨⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega,
      trivial, by omega, ⟨by omega, trivial, by omega, trivial, by omega, trivial,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩, trivial⟩, trivial⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coordBody univ).WellScoped 1 := by
  simp only [coordBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, ⟨by omega, finalProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, by omega, (stepProg_wellScoped hU).mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem prepState_eq (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) :
    prepState dP lam tau beta n s x y a b =
      decState (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (x.map ofBool) (y.map ofBool)
        (toList (parse a)) (toList (parse b))
        (decCtx dP (encode n) s (2 ^ (beta * (Nat.size lam + Nat.size n)))) := by
  simp [prepState, decState, encode_bitStr_eq_list, list_toList]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordLoop_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (Prog.loop (coordBody univ)).WellScoped 1 := ⟨Nat.zero_lt_one, coordBody_wellScoped hU⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem decMain_runs_nil {univ : Prog} (inp : Data) {t₀ : ℕ} (hp : Eval [inp] (prepProg univ) .nil t₀) :
    Eval [inp] (decMain univ) .nil (t₀ + 3) :=
  (Eval.let_ hp (Eval.elim_nil (i := 0) (by simp) (Eval.nil _))).cast_cost (by omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem decMain_runs_state {univ : Prog} (hU : univ.WellScoped 1) (inp st₀ st₁ : Data) {t₀ t₁ : ℕ}
    (hp : Eval [inp] (prepProg univ) (.cons st₀ st₁) t₀) {r : Data}
    (hl : Eval [Data.cons st₀ st₁] (.loop (coordBody univ)) r t₁) :
    Eval [inp] (decMain univ) r (t₀ + t₁ + (Data.cons st₀ st₁).size + 4) :=
  (Eval.let_ hp (Eval.elim_cons (i := 0) (a := st₀) (b := st₁) (by simp)
    (callVar_eval (coordLoop_wellScoped hU) (i := 2) (v := .cons st₀ st₁) (by simp) hl))).cast_cost
    (by omega)
end
end MIPRE.Cost.Prog

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
theorem dom_esize' {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (encode x : Data).size :=
  dom_esize hx
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
/-- The argument of the bound on a call of the input decider from the loop, on data of size
at most `M`. -/
theorem dom_yM : ∃ c m e, ∀ (W X K : ℕ) {p n RD M : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RD ≤ W →
    M + 1 ≤ X → Dom W X K c m e (p + (esize n + M + 1) + RD * (M + 1) ^ K) := by
  exact ⟨_, _, _, fun W X K {p n RD M} hX hp hn hRD hM =>
    ((Dom.ofLeW hp).add hX (((dom_esize hn).add hX (Dom.ofLeX hX (by omega))).add hX
      (Dom.const 1))).add hX ((Dom.ofLeW hRD).mul ((Dom.powK hX).of_le
        (Nat.pow_le_pow_left hM K)))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
theorem DecDom.one_le {ℓ : ℕ} {S : CL.Sampler ℓ} {D : Decider} {lam tau beta n : ℕ} {R : Budget}
    {W : ℕ} (hW : DecDom S D lam tau beta n R W) : 1 ≤ W :=
  (Nat.one_le_pow _ _ (by norm_num)).trans hW.pow_le
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
/-- The size of the parameters datum. -/
theorem size_encode_decParams_le {ℓ : ℕ} {S : CL.Sampler ℓ} {D : Decider} {lam tau beta n : ℕ}
    {R : Budget} {W : ℕ} (hW : DecDom S D lam tau beta n R W) :
    (encode ((S.prog, D.prog), lam, tau, beta) : Data).size ≤ 14 * W + 7 := by
  have h1 := hW.sizeS_le
  have h2 := hW.sizeD_le
  have h3 := (esize_nat_le' lam).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.lam_le) 1)
  have h4 := (esize_nat_le' tau).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.tau_le) 1)
  have h5 := (esize_nat_le' beta).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.beta_le) 1)
  simp only [encode_prod, size_cons, esize] at *
  omega
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
theorem _root_.solution : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
    (lam tau beta n : ℕ) (R : Budget) (W : ℕ) (xD yD aD bD : Data), DecDom S D lam tau beta n R W →
    S.TimeBoundAt n R.S R.k → D.TimeBoundAt n R.D R.k →
    ∃ r t, t ≤ c * (W + 1) ^ m *
        ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) ^ (e * (R.k + 1)) ∧
      (repDeciderProg S.prog D.prog lam tau beta).Runs
        (.cons (encode n) (.cons xD (.cons yD (.cons aD bD)))) r t := by
  obtain ⟨cd, md, ed, hd⟩ := dom_yd
  obtain ⟨cd', md', ed', hd'⟩ := dom_univ_bound cd md ed
  obtain ⟨cP, mP, eP, hP⟩ := dom_prepCost cd' md' ed'
  obtain ⟨cT, mT, eT, hT⟩ := dom_yM
  obtain ⟨cT', mT', eT', hT'⟩ := dom_univ_bound cT mT eT
  exact ⟨_, _, _, fun {ℓ} S D lam tau beta n R W xD yD aD bD hW hS hD => by
    have hX : 1 ≤ (Data.cons xD (.cons yD (.cons aD bD))).size + 1 := by omega
    have h1W : 1 ≤ W := hW.one_le
    have hreps : 2 ^ (tau * (Nat.size lam + Nat.size n)) ≤ W := hW.reps_le
    have hparse : 2 ^ (beta * (Nat.size lam + Nat.size n)) ≤ W := hW.parse_le
    have hdsz : (Data.cons xD (.cons yD (.cons aD bD))).size =
      xD.size + yD.size + aD.size + bD.size + 3 := by simp only [size_cons]; omega
    obtain ⟨td, htd, hdim⟩ := dim_call_time S n R hS
    obtain ⟨t₀, ht₀, hp⟩ := prepProg_runs selfUniversal.closed (encode S.prog) (encode D.prog)
      lam tau beta n (S.dim n) xD yD aD bD hdim
    have hdomtd := (hd' W _ R.k hX (by omega)
      (hd W _ R.k hX hW.sizeS_le hW.n_le hW.S_le hW.pow_le)).of_le htd
    have hdomP := hP W _ R.k (sP := encode S.prog) (dP := encode D.prog) (xD := xD) (yD := yD)
      (aD := aD) (bD := bD) hX h1W hdomtd
      hW.sizeS_le hW.sizeD_le hW.lam_le hW.tau_le hW.beta_le hW.n_le hW.dim_le hreps
      hparse (by omega)
    have hpar := size_encode_decParams_le hW
    have hdomPar : Dom W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k (14 + 7) 1 0
        (encode ((S.prog, D.prog), lam, tau, beta) : Data).size :=
      Dom.ofAffine hpar
    have hsX : Dom W _ R.k 1 0 1 xD.size := Dom.ofLeX hX (by omega)
    have hsY : Dom W _ R.k 1 0 1 yD.size := Dom.ofLeX hX (by omega)
    have hsA : Dom W _ R.k 1 0 1 aD.size := Dom.ofLeX hX (by omega)
    have hsB : Dom W _ R.k 1 0 1 bD.size := Dom.ofLeX hX (by omega)
    -- the sizes of the raw components of the input
    have hsum := (((((((((Dom.ofLeW (v := (encode S.prog : Data).size) hW.sizeS_le).add hX
      (Dom.ofLeW (v := (encode D.prog : Data).size) hW.sizeD_le)).add hX
      (dom_esize' hW.lam_le)).add hX (dom_esize' hW.tau_le)).add hX (dom_esize' hW.beta_le)).add hX
      (dom_esize' hW.n_le)).add hX hsX).add hX hsY).add hX hsA).add hX hsB
    have hin := ((dom_esize' hW.n_le).add hX ((((hsX.add hX hsY).add hX hsA).add hX hsB).add hX
      (Dom.const 3))).add hX (Dom.const 1)
    -- the lists of the loop's state
    have hlx : (list ((bitsOf (toList xD)).map ofBool)).size ≤ xD.size := by
      rw [← encode_bitStr_eq_list]; exact size_encode_bitsOf_le xD
    have hly : (list ((bitsOf (toList yD)).map ofBool)).size ≤ yD.size := by
      rw [← encode_bitStr_eq_list]; exact size_encode_bitsOf_le yD
    have hla : (list (toList (parse (bitsOf (toList aD))))).size ≤ aD.size := by
      rw [list_toList]; exact size_parse_bitsOf_le aD
    have hlb : (list (toList (parse (bitsOf (toList bD))))).size ≤ bD.size := by
      rw [list_toList]; exact size_parse_bitsOf_le bD
    -- domination of the loop's budget
    have hM : (list ((bitsOf (toList xD)).map ofBool)).size +
        (list ((bitsOf (toList yD)).map ofBool)).size +
        (list (toList (parse (bitsOf (toList aD))))).size +
        (list (toList (parse (bitsOf (toList bD))))).size + 3 + 1 ≤
        (Data.cons xD (.cons yD (.cons aD bD))).size + 1 := by rw [hdsz]; omega
    have hdomTu := hT' W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k hX (by omega)
      (hT W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k hX hW.sizeD_le hW.n_le hW.D_le hM)
    have hctx : Dom W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k
        ((1 + (4 + 1)) + (2 + 1) + (2 + 1) + 3) 1 0
        (decCtx (encode D.prog) (encode n) (S.dim n)
          (2 ^ (beta * (Nat.size lam + Nat.size n)))).size := by
      refine ((((Dom.ofLeW (v := (encode D.prog : Data).size) hW.sizeD_le).add hX
        (dom_esize' hW.n_le)).add hX
        (Dom.ofAffine (a := 2) (b := 1) (v := (ofNat (S.dim n)).size)
          (by rw [size_ofNat]; have := hW.dim_le; omega))).add hX
        (Dom.ofAffine (a := 2) (b := 1) (v := (ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))).size)
          (by rw [size_ofNat]; omega))).add hX
        (Dom.const 3) |>.of_le ?_ |>.mono hX ?_ ?_ ?_
      · simp only [decCtx, size_cons, size_ofNat]; omega
      · norm_num
      · norm_num
      · norm_num
    have hk : Dom W ((Data.cons xD (.cons yD (.cons aD bD))).size + 1) R.k (2 + 1) 1 0
        (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))).size :=
      Dom.ofAffine (a := 2) (b := 1) (by rw [size_ofNat]; omega)
    have hZ := (((((((Dom.ofLeW hW.dim_le).add hX
      (Dom.ofLeW (v := 2 ^ (beta * (Nat.size lam + Nat.size n))) hparse)).add hX
      (hsX.of_le hlx)).add hX (hsY.of_le hly)).add hX (hsA.of_le hla)).add hX
      (hsB.of_le hlb)).add hX hctx).add hX hk |>.add hX (Dom.const 10)
    have hiter := ((Dom.const 40).mul ((hZ.add hX (Dom.const 30)).pow 2)).add hX hdomTu
    have hloop := ((Dom.ofLeW (v := 2 ^ (tau * (Nat.size lam + Nat.size n))) hreps).add hX
      (Dom.const 1)).mul hiter
    -- the size of the loop's state
    have hst := ((((((hk.add hX (hsX.of_le hlx)).add hX (hsY.of_le hly)).add hX
      (hsA.of_le hla)).add hX (hsB.of_le hlb)).add hX hctx).add hX (Dom.const 5))
    -- the whole budget, shared by both branches
    have chain := ((((((hdomP.add hX hloop).add hX hst).add hX (Dom.const 4)).add hX
      ((Dom.const 2).mul hsum)).add hX (Dom.const 40)).add hX hdomPar).add hX hin |>.add hX
      (Dom.const 3)
    by_cases hok : prepOk lam tau n (S.dim n) (bitsOf (toList xD)) (bitsOf (toList yD))
        (bitsOf (toList aD)) (bitsOf (toList bD)) = true
    · rw [prepResult, if_pos hok, prepState_eq] at hp
      obtain ⟨fq, hfq⟩ := loop_calls_time D n R hD (S.dim n)
        (2 ^ (tau * (Nat.size lam + Nat.size n))) ((bitsOf (toList xD)).map ofBool)
        ((bitsOf (toList yD)).map ofBool) (toList (parse (bitsOf (toList aD))))
        (toList (parse (bitsOf (toList bD))))
      obtain ⟨r, t₁, ht₁, hl⟩ := coordLoop_runs_bounded selfUniversal.closed (encode D.prog)
        (encode n) (S.dim n) (2 ^ (beta * (Nat.size lam + Nat.size n))) fq _ _
        (2 ^ (tau * (Nat.size lam + Nat.size n))) ((bitsOf (toList xD)).map ofBool)
        ((bitsOf (toList yD)).map ofBool) (toList (parse (bitsOf (toList aD))))
        (toList (parse (bitsOf (toList bD)))) [] hfq le_rfl
      have hmain := decMain_runs_state selfUniversal.closed _ _ _ hp hl
      have hcore := repDecCore_runs selfUniversal.closed (encode S.prog) (encode D.prog)
        (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD hmain
      refine ⟨r, _, ?_, hardcode_time (repDecCore_wellScoped selfUniversal.closed) hcore⟩
      unfold coordIter at ht₁
      refine (chain.of_le ?_).le
      simp only [size_cons, size_ofNat] at ht₀ ht₁ ⊢
      omega
    · rw [prepResult, if_neg hok] at hp
      have hmain := decMain_runs_nil _ hp
      have hcore := repDecCore_runs selfUniversal.closed (encode S.prog) (encode D.prog)
        (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD hmain
      refine ⟨.nil, _, ?_, hardcode_time (repDecCore_wellScoped selfUniversal.closed) hcore⟩
      refine (chain.of_le ?_).le
      simp only [size_cons, size_ofNat] at ht₀ ⊢
      omega⟩
end MIPRE.Repeat
