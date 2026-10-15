-- Prove2me | solution 1 for MIPRE.Cost.compressibility_criterion_nested
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:34:16.778798+00:00
-- url     : https://prove2.me/submissions/dedb7447-b20f-4fe1-bec5-8962e67e2b4d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.compressibility_criterion_nested);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Prog_searchProg_halts_of
import Theorems.Thm_MIPRE_Cost_Prog_searchProg_runs
import Theorems.Thm_MIPRE_Cost_efficient_fixed_point
import Theorems.Thm_MIPRE_Cost_exists_clocked_universal
import Theorems.Thm_MIPRE_Cost_exists_efficient_universal
import Theorems.Thm_MIPRE_Cost_exists_threshold
import Theorems.Thm_MIPRE_Cost_hardcode_size
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
theorem le_levels (R : ℕ) : ∀ k, R ≤ levels R k
  | 0 => le_rfl
  | k + 1 => (le_levels R k).trans (by rw [levels_succ]; omega)
end MIPRE.Cost

namespace MIPRE.Cost
open Polynomial
theorem levels_mono (R : ℕ) {j k : ℕ} (h : j ≤ k) : levels R j ≤ levels R k :=
  monotone_nat_of_le_succ (fun n => by rw [levels_succ]; omega) h
end MIPRE.Cost

namespace MIPRE.Cost
open Polynomial
theorem two_pow_le_levels {R : ℕ} (hR : 1 ≤ R) : ∀ k, 2 ^ k ≤ levels R k
  | 0 => by simpa using hR
  | k + 1 => by
    have := two_pow_le_levels hR k
    rw [pow_succ, levels_succ]
    omega
end MIPRE.Cost

namespace MIPRE.Cost
open Polynomial
theorem decFunV_apply (U : UniversalMachine) (UT : ClockedUniversalMachine) (S : Prog)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr) (yYes yNo : BitStr) (c' e : Prog) (m n : ℕ) :
    decFunV U UT S Compr yYes yNo (c', (e, (m, n))) =
      if (evalWithin e .nil (Nat.size n)).isSome then yYes
      else if (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c', (e, (m, m))), m)))
          .nil (Nat.size n)).isSome then yNo
      else Compr (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), (m, 2 * n + 1))), n) :=
  rfl
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution
    (A B₀ B₁ : ℕ → Set BitStr) (n₀ : ℕ) (hsub : ∀ n, B₀ n ⊆ B₁ n)
    (yYes : BitStr) (hyes : ∀ n, n₀ ≤ n → yYes ∈ A n)
    (yNo : BitStr) (hno : ∀ n, n₀ ≤ n → yNo ∈ B₀ n)
    (S : Prog) (hSws : S.WellScoped 1)
    (hS : ∀ (x : BitStr) (n : ℕ), Halts S (encode (x, n)) ↔ x ∉ B₁ n)
    (Compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
      IsSuccinctDesc c n x → x.length ≤ n + 1 →
        (x ∈ A (2 * n + 1) → Compr (c, n) ∈ A n) ∧ (x ∈ B₀ (2 * n + 1) → Compr (c, n) ∈ B₀ n)) :
    ∃ (g : PolyTimeFun Prog BitStr) (K : ℕ),
      ∀ e : Prog, n₀ ≤ 2 ^ (K + 1 + esize e) ∧
        (Halts e .nil → g e ∈ A (2 ^ (K + 1 + esize e))) ∧
        (¬ Halts e .nil → g e ∈ B₁ (2 ^ (K + 1 + esize e))) := by
  obtain ⟨U⟩ := exists_efficient_universal
  obtain ⟨UT⟩ := exists_clocked_universal
  -- the decider, kept opaque through its functional equation
  obtain ⟨dec, hdec⟩ : ∃ dec : PolyTimeFun (Prog × (Prog × (ℕ × ℕ))) BitStr, ∀ c' e m n,
      dec (c', (e, (m, n))) =
        if (evalWithin e .nil (Nat.size n)).isSome then yYes
        else if (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c', (e, (m, m))), m)))
            .nil (Nat.size n)).isSome then yNo
        else Compr (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), (m, 2 * n + 1))),
          n) :=
    ⟨decFunV U UT S Compr yYes yNo, decFunV_apply U UT S Compr yYes yNo⟩
  -- the self-reference: `c` on `q` computes `dec (c, q)`
  obtain ⟨F, hF⟩ : ∃ F : PolyTimeFun Prog Prog, ∀ c', F c' = hardcode dec.code (encode c') :=
    ⟨(PolyTimeFun.smn Prog).comp (PolyTimeFun.pair (PolyTimeFun.const dec.code)
      (PolyTimeFun.id Prog)), fun _ => rfl⟩
  obtain ⟨c, p, hc, -, hc_time⟩ := efficient_fixed_point F
  -- the time bound of `c`
  obtain ⟨cB, hcB⟩ : ∃ cB : Polynomial ℕ, ∀ x, cB.eval x =
      p.eval (2 * x + dec.timeBound.eval (x + (esize c + 1)) + (esize c + 5)) :=
    ⟨p.comp (C 2 * X + dec.timeBound.comp (X + C (esize c + 1)) + C (esize c + 5)),
      fun x => by simp [Polynomial.eval_comp]⟩
  have c_runs : ∀ q : Prog × (ℕ × ℕ), ∃ t ≤ cB.eval (esize q),
      c.Runs (encode q) (encode (dec (c, q))) t := by
    intro q
    obtain ⟨t₀, ht₀, h₀⟩ := dec.computes (c, q)
    have h₁ := hardcode_time dec.closed (d := encode c) (x := encode q) h₀
    rw [← hF c] at h₁
    obtain ⟨t', ht', h'⟩ := hc_time _ _ _ h₁
    refine ⟨t', ?_, h'⟩
    rw [hcB]
    refine ht'.trans (polynomial_eval_mono p ?_)
    have hm := polynomial_eval_mono dec.timeBound
      (show esize (c, q) ≤ esize q + (esize c + 1) by simp only [esize_prod]; omega)
    have e1 : (encode q).size = esize q := rfl
    have e2 : (encode c).size = esize c := rfl
    omega
  -- `c` as a polynomial-time function of `q = (e, (m, n))`
  obtain ⟨cFun, hcFun⟩ : ∃ cFun : PolyTimeFun (Prog × (ℕ × ℕ)) BitStr,
      ∀ q, cFun q = dec (c, q) :=
    ⟨{ toFun := fun q => dec (c, q)
       code := c
       closed := hc
       timeBound := cB
       computes := fun q => c_runs q }, fun _ => rfl⟩
  -- the overhead polynomials in `x = esize e + Nat.size n`, and the threshold constant:
  -- `Q₁` bounds the run of `c` at level `2n + 1`, `Q₂` the bit-query overhead, `Q₃` twice
  -- the size of the hardcoded bit-query program
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Polynomial ℕ, ∀ x, Q₁.eval x = cB.eval (9 * x + 8) :=
    ⟨cB.comp (C 9 * X + C 8), fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : Polynomial ℕ, ∀ x, Q₂.eval x =
      (bitQueryBound U).eval (Q₁.eval x + 9 * x + (esize c + 7)) + 9 * x + (esize c + 13) :=
    ⟨(bitQueryBound U).comp (Q₁ + C 9 * X + C (esize c + 7)) + C 9 * X + C (esize c + 13),
      fun x => by simp [Polynomial.eval_comp]⟩
  obtain ⟨Q₃, hQ₃⟩ : ∃ Q₃ : Polynomial ℕ, ∀ x, Q₃.eval x =
      2 * (esize (Prog.bitQueryProg U.univ) + esize c + 9 * x + 44) + 1 :=
    ⟨C 2 * (C (esize (Prog.bitQueryProg U.univ) + esize c + 44) + C 9 * X) + C 1,
      fun x => by simp; ring⟩
  obtain ⟨K₀, hK₀⟩ := exists_threshold (Q₁ + Q₂ + Q₃)
  -- the threshold constant also puts every level above `n₀`
  obtain ⟨K, hK, hKn₀⟩ : ∃ K : ℕ,
      (∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → (Q₁ + Q₂ + Q₃).eval (x + Nat.size n) ≤ n + 1) ∧
      ∀ x n : ℕ, 2 ^ (K + 1 + x) ≤ n → n₀ ≤ n := by
    refine ⟨K₀ + Nat.size n₀, fun x n hn => hK₀ x n ?_, fun x n hn => ?_⟩
    · exact le_trans (Nat.pow_le_pow_right two_pos (by omega)) hn
    · exact le_trans (Nat.lt_size_self n₀).le
        (le_trans (Nat.pow_le_pow_right two_pos (by omega)) hn)
  -- above the threshold `R = 2 ^ (K + 1 + esize e)`, which is also the start level, `c` at
  -- level `2n + 1` is fast and its output is succinctly described by the hardcoded bit-query
  -- program with parameter `n`; that program is short, and the level is at least `n₀`
  have key : ∀ e n, 2 ^ (K + 1 + esize e) ≤ n →
      n₀ ≤ n ∧
      2 * esize (hardcode (Prog.bitQueryProg U.univ)
        (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)))) ≤ n ∧
      IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ)
          (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)))) n
        (dec (c, (e, (2 ^ (K + 1 + esize e), 2 * n + 1)))) ∧
      (dec (c, (e, (2 ^ (K + 1 + esize e), 2 * n + 1)))).length ≤ n + 1 := by
    intro e n hn
    obtain ⟨t, ht, hrun⟩ := c_runs (e, (2 ^ (K + 1 + esize e), 2 * n + 1))
    have hQ := hK (esize e) n hn
    rw [Polynomial.eval_add, Polynomial.eval_add, hQ₁, hQ₂, hQ₁, hQ₃] at hQ
    have hlt : K + 1 + esize e < Nat.size n := Nat.lt_size.mpr hn
    have hsm : esize (2 ^ (K + 1 + esize e)) ≤ 4 * Nat.size n + 1 := by
      have h1 := esize_nat_le (2 ^ (K + 1 + esize e))
      rw [Nat.size_pow] at h1
      omega
    have hsz : esize (2 * n + 1) ≤ 4 * Nat.size n + 5 := by
      have := esize_nat_le (2 * n + 1)
      rw [size_two_mul_add_one] at this
      omega
    have hsize : esize (hardcode (Prog.bitQueryProg U.univ)
        (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)))) ≤
        esize (Prog.bitQueryProg U.univ) + esize c + 9 * (esize e + Nat.size n) + 44 := by
      rw [hardcode_size]
      have hd : (encode ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1))).size =
          esize ((c, e), (2 ^ (K + 1 + esize e), 2 * n + 1)) := rfl
      rw [hd]
      simp only [esize_prod]
      omega
    refine ⟨hKn₀ (esize e) n hn, by omega, ?_⟩
    have ht₁ : t ≤ cB.eval (9 * (esize e + Nat.size n) + 8) := by
      refine ht.trans (polynomial_eval_mono cB ?_)
      simp only [esize_prod]
      omega
    have hpow : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    -- the run producing `x` costs at most `n + 1`, so `x` is that short: the bound
    -- `IsSuccinctDesc` records is `2 ^ n`, which is what obligation O4 then cannot use
    have hxlen : (dec (c, (e, (2 ^ (K + 1 + esize e), 2 * n + 1)))).length ≤ n + 1 :=
      (length_le_esize_bitStr _).trans (hrun.size_le.trans (by omega))
    refine ⟨?_, hxlen⟩
    refine isSuccinctDesc_hardcode U c e (2 ^ (K + 1 + esize e), 2 * n + 1) n _ hrun
      (by omega) ?_
    have hb := polynomial_eval_mono (bitQueryBound U)
      (show esize c + esize e + esize (2 ^ (K + 1 + esize e), 2 * n + 1) + t ≤
        cB.eval (9 * (esize e + Nat.size n) + 8) + 9 * (esize e + Nat.size n) + (esize c + 7)
        by simp only [esize_prod]; omega)
    simp only [esize_prod] at hb ⊢
    omega
  -- the reduction: the string at level `R = 2 ^ (K + 1 + esize e)` of the recursion started
  -- at `R`
  refine ⟨cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog)
    (PolyTimeFun.pair (PolyTimeFun.threshold K) (PolyTimeFun.threshold K))), K, fun e => ?_⟩
  have hg : cFun.comp (PolyTimeFun.pair (PolyTimeFun.id Prog)
      (PolyTimeFun.pair (PolyTimeFun.threshold K) (PolyTimeFun.threshold K))) e =
      dec (c, (e, (2 ^ (K + 1 + esize e), 2 ^ (K + 1 + esize e)))) := by
    rw [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.pair_apply, hcFun,
      PolyTimeFun.id_apply, PolyTimeFun.threshold_apply]
  rw [hg]
  have key' := key e
  have hR1 : 1 ≤ 2 ^ (K + 1 + esize e) := Nat.one_le_two_pow
  have hRn₀ : n₀ ≤ 2 ^ (K + 1 + esize e) := hKn₀ (esize e) _ le_rfl
  generalize hR : 2 ^ (K + 1 + esize e) = R at key' hR1 hRn₀ ⊢
  -- the level of every step of the recursion is at least `n₀`
  have hlev : ∀ j, n₀ ≤ levels R j := fun j => hRn₀.trans (le_levels R j)
  -- the clocked halting test is monotone in the budget
  have hmono : ∀ (q : Prog) (k k' : ℕ), k ≤ k' → (evalWithin q .nil k).isSome = true →
      (evalWithin q .nil k').isSome = true := by
    intro q k k' hkk' h
    obtain ⟨r, t, ht, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
    exact (evalWithin_isSome_iff _ _ _).2 ⟨r, t, ht.trans hkk', hr⟩
  -- the search branch, both ways: it fires only if the start string is outside `B₁ R`, and it
  -- eventually fires if the start string is outside `B₁ R`
  have hsearch_of : ∀ k, (evalWithin (hardcode (Prog.searchProg U.univ S)
      (encode ((c, (e, (R, R))), R))) .nil k).isSome = true → dec (c, (e, (R, R))) ∉ B₁ R := by
    intro k h
    obtain ⟨r, t, -, hrun⟩ := (evalWithin_isSome_iff _ _ _).1 h
    obtain ⟨x, tx, hx, hSx⟩ := Prog.searchProg_halts_of U hSws hrun
    obtain ⟨t', -, hc'⟩ := c_runs (e, (R, R))
    obtain ⟨rfl, -⟩ := Eval.deterministic hx hc'
    exact (hS _ _).1 hSx
  have hsearch_fires : dec (c, (e, (R, R))) ∉ B₁ R → ∃ T₀, ∀ k, T₀ ≤ k →
      (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c, (e, (R, R))), R))) .nil
        k).isSome = true := by
    intro hnB
    obtain ⟨r, ts, hSr⟩ := (hS _ _).2 hnB
    obtain ⟨t', -, hc'⟩ := c_runs (e, (R, R))
    obtain ⟨T₀, hT₀⟩ := Prog.searchProg_runs U hSws hc' hSr
    exact ⟨T₀, fun k hk => (evalWithin_isSome_iff _ _ _).2 ⟨r, T₀, hk, hT₀⟩⟩
  refine ⟨hRn₀, fun hh => ?_, fun hnh => ?_⟩
  · -- halting `e`
    obtain ⟨r₀, T, hT⟩ := hh
    have htrue : ∀ n, T ≤ Nat.size n → (evalWithin e .nil (Nat.size n)).isSome = true :=
      fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r₀, T, hn, hT⟩
    -- below a level where the search fires while `e` has not yet halted, every level of the
    -- recursion is in `B₀`
    have hB : ∀ j₀, (evalWithin e .nil (Nat.size (levels R j₀))).isSome = false →
        (evalWithin (hardcode (Prog.searchProg U.univ S) (encode ((c, (e, (R, R))), R))) .nil
          (Nat.size (levels R j₀))).isSome = true →
        ∀ i j, j + i = j₀ → dec (c, (e, (R, levels R j))) ∈ B₀ (levels R j) := by
      intro j₀ hnot hfire i
      induction i with
      | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        subst hj
        rw [hdec, hnot, if_neg Bool.false_ne_true, hfire, if_pos rfl]
        exact hno _ (hlev _)
      | succ i ih =>
        intro j hj
        have hjle : Nat.size (levels R j) ≤ Nat.size (levels R j₀) :=
          Nat.size_le_size (levels_mono R (by omega))
        have hd := hdec c e R (levels R j)
        cases hb₁ : (evalWithin e .nil (Nat.size (levels R j))).isSome with
        | true =>
          exfalso
          rw [hmono e _ _ hjle hb₁] at hnot
          exact absurd hnot (by decide)
        | false =>
          rw [hb₁, if_neg Bool.false_ne_true] at hd
          cases hb₂ : (evalWithin (hardcode (Prog.searchProg U.univ S)
              (encode ((c, (e, (R, R))), R))) .nil (Nat.size (levels R j))).isSome with
          | true =>
            rw [hb₂, if_pos rfl] at hd
            rw [hd]
            exact hno _ (hlev _)
          | false =>
            rw [hb₂, if_neg Bool.false_ne_true] at hd
            rw [hd]
            have hnext := ih (j + 1) (by omega)
            rw [levels_succ] at hnext
            obtain ⟨h₀, h₁, h₂, h₃⟩ := key' (levels R j) (le_levels R j)
            exact (hCompr _ _ _ h₀ h₁ h₂ h₃).2 hnext
    -- from a level where `e` has halted, every level of the recursion is in `A`
    have hA : ∀ k j, T ≤ Nat.size (levels R (j + k)) →
        dec (c, (e, (R, levels R j))) ∈ A (levels R j) := by
      intro k
      induction k with
      | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        rw [hdec, htrue _ hj, if_pos rfl]
        exact hyes _ (hlev _)
      | succ k ih =>
        intro j hj
        have hd := hdec c e R (levels R j)
        cases hb₁ : (evalWithin e .nil (Nat.size (levels R j))).isSome with
        | true =>
          rw [hb₁, if_pos rfl] at hd
          rw [hd]
          exact hyes _ (hlev _)
        | false =>
          rw [hb₁, if_neg Bool.false_ne_true] at hd
          cases hb₂ : (evalWithin (hardcode (Prog.searchProg U.univ S)
              (encode ((c, (e, (R, R))), R))) .nil (Nat.size (levels R j))).isSome with
          | true =>
            exfalso
            have hRB := hB j hb₁ hb₂ j 0 (by omega)
            rw [levels_zero] at hRB
            exact hsearch_of _ hb₂ (hsub _ hRB)
          | false =>
            rw [hb₂, if_neg Bool.false_ne_true] at hd
            rw [hd]
            have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
            rw [levels_succ] at hnext
            obtain ⟨h₀, h₁, h₂, h₃⟩ := key' (levels R j) (le_levels R j)
            exact (hCompr _ _ _ h₀ h₁ h₂ h₃).1 hnext
    obtain ⟨k, hk⟩ : ∃ k, T ≤ Nat.size (levels R k) := by
      refine ⟨T, ?_⟩
      have h1 := Nat.size_le_size (two_pow_le_levels hR1 T)
      rw [Nat.size_pow] at h1
      omega
    have hfin := hA k 0 (by simpa using hk)
    rw [levels_zero] at hfin
    exact hfin
  · -- non-halting `e`
    have hfalse : ∀ n, (evalWithin e .nil (Nat.size n)).isSome = false := fun n => by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
      exact hnh ⟨r, t, hr⟩
    by_contra hnB
    obtain ⟨T₀, hT₀⟩ := hsearch_fires hnB
    -- from a level where the search fires, every level of the recursion is in `B₀`
    have hB : ∀ k j, T₀ ≤ Nat.size (levels R (j + k)) →
        dec (c, (e, (R, levels R j))) ∈ B₀ (levels R j) := by
      intro k
      induction k with
      | zero =>
        intro j hj
        rw [Nat.add_zero] at hj
        rw [hdec, hfalse (levels R j), if_neg Bool.false_ne_true, hT₀ _ hj, if_pos rfl]
        exact hno _ (hlev _)
      | succ k ih =>
        intro j hj
        have hd := hdec c e R (levels R j)
        rw [hfalse (levels R j), if_neg Bool.false_ne_true] at hd
        cases hb₂ : (evalWithin (hardcode (Prog.searchProg U.univ S)
            (encode ((c, (e, (R, R))), R))) .nil (Nat.size (levels R j))).isSome with
        | true =>
          rw [hb₂, if_pos rfl] at hd
          rw [hd]
          exact hno _ (hlev _)
        | false =>
          rw [hb₂, if_neg Bool.false_ne_true] at hd
          rw [hd]
          have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
          rw [levels_succ] at hnext
          obtain ⟨h₀, h₁, h₂, h₃⟩ := key' (levels R j) (le_levels R j)
          exact (hCompr _ _ _ h₀ h₁ h₂ h₃).2 hnext
    obtain ⟨k, hk⟩ : ∃ k, T₀ ≤ Nat.size (levels R k) := by
      refine ⟨T₀, ?_⟩
      have h1 := Nat.size_le_size (two_pow_le_levels hR1 T₀)
      rw [Nat.size_pow] at h1
      omega
    have hfin := hB k 0 (by simpa using hk)
    rw [levels_zero] at hfin
    exact hnB (hsub _ hfin)
