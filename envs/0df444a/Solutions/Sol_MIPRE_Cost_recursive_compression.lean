-- Prove2me | solution 1 for MIPRE.Cost.recursive_compression
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:02:10.15101+00:00
-- url     : https://prove2.me/submissions/588af480-6afc-4119-affb-9eef870b0306

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.recursive_compression);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression
import Theorems.Thm_MIPRE_Cost_efficient_fixed_point
import Theorems.Thm_MIPRE_Cost_exists_clocked_universal
import Theorems.Thm_MIPRE_Cost_exists_efficient_universal
import Theorems.Thm_MIPRE_Cost_exists_threshold
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_isSuccinctDesc_hardcode

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem size_ofBool (b : Bool) : (ofBool b).size ≤ 3 := by cases b <;> simp [ofBool]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem size_ofList_le {α : Type*} {f : α → Data} {B : ℕ} (hf : ∀ a, (f a).size ≤ B)
    (l : List α) : (ofList f l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    have := hf a
    simp only [ofList, size_cons, List.length_cons, Nat.mul_succ]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost
theorem esize_bitStr_le (x : BitStr) : esize x ≤ 4 * x.length + 1 :=
  Data.size_ofList_le Data.size_ofBool x
end MIPRE.Cost

namespace MIPRE.Cost
theorem esize_nat_le (n : ℕ) : esize n ≤ 4 * Nat.size n + 1 := by
  have := esize_bitStr_le n.bits
  rw [Nat.size_eq_bits_len] at this
  exact this
end MIPRE.Cost

namespace MIPRE.Cost
theorem size_two_mul_add_one (n : ℕ) : Nat.size (2 * n + 1) = Nat.size n + 1 := by
  rw [← Nat.bit_true_apply, Nat.size_bit (by rw [Nat.bit_true_apply]; omega)]
end MIPRE.Cost

namespace MIPRE.Cost
open Polynomial
theorem evalWithin_isSome_iff (c : Prog) (v : Data) (k : ℕ) :
    (evalWithin c v k).isSome = true ↔ ∃ r t, t ≤ k ∧ c.Runs v r t := by
  unfold evalWithin
  split <;> simp_all
end MIPRE.Cost

namespace MIPRE.Cost
open Polynomial
theorem decFun_apply (U : UniversalMachine) (UT : ClockedUniversalMachine)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr) (y₀ : BitStr) (c' e : Prog) (n : ℕ) :
    decFun U UT Compr y₀ (c', (e, n)) =
      if (evalWithin e .nil (Nat.size n)).isSome then y₀
      else Compr ((hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), 2 * n + 1)), n), n) :=
  rfl
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (_hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : PolyTimeFun Prog BitStr,
      ∀ e : Prog,
        (Halts e .nil → g e ∈ A) ∧
        (¬ Halts e .nil → f (g e) = ⊤) := by
  obtain ⟨U⟩ := exists_efficient_universal
  obtain ⟨UT⟩ := exists_clocked_universal
  -- the decider, kept opaque through its functional equation
  obtain ⟨dec, hdec⟩ : ∃ dec : PolyTimeFun (Prog × (Prog × ℕ)) BitStr, ∀ c' e n,
      dec (c', (e, n)) = if (evalWithin e .nil (Nat.size n)).isSome then y₀
        else Compr ((hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), 2 * n + 1)), n), n) :=
    ⟨decFun U UT Compr y₀, decFun_apply U UT Compr y₀⟩
  -- the self-reference: `c` on `(e, n)` computes `dec (c, (e, n))`
  obtain ⟨F, hF⟩ : ∃ F : PolyTimeFun Prog Prog, ∀ c', F c' = hardcode dec.code (encode c') :=
    ⟨(PolyTimeFun.smn Prog).comp (PolyTimeFun.pair (PolyTimeFun.const dec.code)
      (PolyTimeFun.id Prog)), fun _ => rfl⟩
  obtain ⟨c, p, hc, -, hc_time⟩ := efficient_fixed_point F
  -- the time bound of `c`
  obtain ⟨cB, hcB⟩ : ∃ cB : Polynomial ℕ, ∀ x, cB.eval x =
      p.eval (2 * x + dec.timeBound.eval (x + (esize c + 1)) + (esize c + 5)) :=
    ⟨p.comp (C 2 * X + dec.timeBound.comp (X + C (esize c + 1)) + C (esize c + 5)),
      fun x => by simp [Polynomial.eval_comp]⟩
  have c_runs : ∀ e n, ∃ t ≤ cB.eval (esize e + esize n + 1),
      c.Runs (encode (e, n)) (encode (dec (c, (e, n)))) t := by
    intro e n
    obtain ⟨t₀, ht₀, h₀⟩ := dec.computes (c, (e, n))
    have h₁ := hardcode_time dec.closed (d := encode c) (x := encode (e, n)) h₀
    rw [← hF c] at h₁
    obtain ⟨t', ht', h'⟩ := hc_time _ _ _ h₁
    refine ⟨t', ?_, h'⟩
    rw [hcB]
    refine ht'.trans (polynomial_eval_mono p ?_)
    have hm := polynomial_eval_mono dec.timeBound
      (show esize (c, (e, n)) ≤ esize e + esize n + 1 + (esize c + 1) by
        simp only [esize_prod]; omega)
    have e1 : (encode (e, n)).size = esize e + esize n + 1 := rfl
    have e2 : (encode c).size = esize c := rfl
    omega
  -- `c` as a polynomial-time function of `(e, n)`
  obtain ⟨cFun, hcFun⟩ : ∃ cFun : PolyTimeFun (Prog × ℕ) BitStr, ∀ q, cFun q = dec (c, q) :=
    ⟨{ toFun := fun q => dec (c, q)
       code := c
       closed := hc
       timeBound := cB
       computes := fun q => by
         obtain ⟨e, n⟩ := q
         obtain ⟨t, ht, h⟩ := c_runs e n
         exact ⟨t, by rw [esize_prod]; exact ht, h⟩ }, fun _ => rfl⟩
  -- the overhead polynomial in `x = esize e + Nat.size n`, and the threshold constant
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Polynomial ℕ, ∀ x, Q₁.eval x = cB.eval (5 * x + 6) :=
    ⟨cB.comp (C 5 * X + C 6), fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : Polynomial ℕ, ∀ x, Q₂.eval x =
      (bitQueryBound U).eval (Q₁.eval x + 5 * x + (esize c + 6)) + 5 * x + (esize c + 12) :=
    ⟨(bitQueryBound U).comp (Q₁ + C 5 * X + C (esize c + 6)) + C 5 * X + C (esize c + 12),
      fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨K, hK⟩ := exists_threshold (Q₁ + Q₂)
  -- above the threshold, `c` at level `2n + 1` is fast and its output is succinctly
  -- described by the hardcoded bit-query program with parameter `n`
  have key : ∀ e n, 2 ^ (K + 1 + esize e) ≤ n →
      IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ) (encode ((c, e), 2 * n + 1))) n
        (dec (c, (e, 2 * n + 1))) := by
    intro e n hn
    obtain ⟨t, ht, hrun⟩ := c_runs e (2 * n + 1)
    have hQ := hK (esize e) n hn
    rw [Polynomial.eval_add, hQ₁, hQ₂, hQ₁] at hQ
    have hsz : esize (2 * n + 1) ≤ 4 * Nat.size n + 5 := by
      have := esize_nat_le (2 * n + 1)
      rw [size_two_mul_add_one] at this
      omega
    have ht₁ : t ≤ cB.eval (5 * (esize e + Nat.size n) + 6) :=
      ht.trans (polynomial_eval_mono cB (by omega))
    have hpow : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    refine isSuccinctDesc_hardcode U c e (2 * n + 1) n _ hrun (by omega) ?_
    have hb := polynomial_eval_mono (bitQueryBound U)
      (show esize c + esize e + esize (2 * n + 1) + t ≤
        cB.eval (5 * (esize e + Nat.size n) + 6) + 5 * (esize e + Nat.size n) + (esize c + 6)
        by omega)
    omega
  -- the reduction
  refine ⟨cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog) (PolyTimeFun.threshold K)),
    fun e => ?_⟩
  have hg : cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog) (PolyTimeFun.threshold K)) e =
      dec (c, (e, 2 ^ (K + 1 + esize e))) := by
    rw [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, hcFun, PolyTimeFun.id_apply,
      PolyTimeFun.threshold_apply]
  rw [hg]
  refine ⟨fun hh => ?_, fun hnh => ?_⟩
  · -- halting `e`: above `2 ^ T`, the decider returns `y₀`; below, `Compr` preserves `A`
    obtain ⟨r₀, T, hT⟩ := hh
    have htrue : ∀ n, T ≤ Nat.size n → (evalWithin e .nil (Nat.size n)).isSome = true :=
      fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r₀, T, hn, hT⟩
    have hmem : ∀ k n, 2 ^ (K + 1 + esize e) ≤ n → 2 ^ T ≤ n + k → dec (c, (e, n)) ∈ A := by
      intro k
      induction k with
      | zero =>
        intro n _ hk
        have hd := hdec c e n
        rw [htrue n (Nat.lt_size.mpr (by simpa using hk)).le, if_pos rfl] at hd
        rw [hd]
        exact hy₀
      | succ k ih =>
        intro n hn hk
        have hd := hdec c e n
        cases hb : (evalWithin e .nil (Nat.size n)).isSome with
        | true =>
          rw [hb, if_pos rfl] at hd
          rw [hd]
          exact hy₀
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at hd
          rw [hd]
          exact (hCompr _ _ _ n (key e n hn)).2 (ih (2 * n + 1) (by omega) (by omega))
    exact hmem (2 ^ T) _ le_rfl (Nat.le_add_left _ _)
  · -- non-halting `e`: the decider always compresses, and `f` grows without bound
    have hfalse : ∀ n, (evalWithin e .nil (Nat.size n)).isSome = false := fun n => by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
      exact hnh ⟨r, t, hr⟩
    have hstep : ∀ n : ℕ, 2 ^ (K + 1 + esize e) ≤ n →
        ((n : ℕ) : ℕ∞) ≤ f (dec (c, (e, n))) ∧
          f (dec (c, (e, 2 * n + 1))) ≤ f (dec (c, (e, n))) := by
      intro n hn
      have hd := hdec c e n
      rw [hfalse n, if_neg Bool.false_ne_true] at hd
      have := (hCompr _ _ _ n (key e n hn)).1
      rw [← hd] at this
      exact ⟨le_trans (le_max_right _ _) this, le_trans (le_max_left _ _) this⟩
    have hgrow : ∀ k n : ℕ, 2 ^ (K + 1 + esize e) ≤ n →
        ((n + k : ℕ) : ℕ∞) ≤ f (dec (c, (e, n))) := by
      intro k
      induction k with
      | zero => intro n hn; simpa using (hstep n hn).1
      | succ k ih =>
        intro n hn
        have h1 := ih (2 * n + 1) (by omega)
        have h2 := (hstep n hn).2
        refine le_trans ?_ (h1.trans h2)
        exact_mod_cast (show n + (k + 1) ≤ 2 * n + 1 + k by omega)
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    exact le_trans (by exact_mod_cast Nat.le_add_left m (2 ^ (K + 1 + esize e)))
      (hgrow m _ le_rfl)
