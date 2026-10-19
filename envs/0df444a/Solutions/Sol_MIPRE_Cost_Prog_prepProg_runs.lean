-- Prove2me | solution 1 for MIPRE.Cost.Prog.prepProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:37:12.893369+00:00
-- url     : https://prove2.me/submissions/9fd71f09-83f1-48f6-a794-b05d4b6ab4d7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecMain.lean (solution of MIPRE.Cost.Prog.prepProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Theorems.Thm_MIPRE_Cost_Data_size_sum_stackStep_le
import Theorems.Thm_MIPRE_Cost_Prog_prepProg_prefix

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
theorem andExpr_runs {env : Env} {i₁ i₂ i₃ i₄ : ℕ} {c₁ c₂ c₃ c₄ : Bool}
    (h₁ : env.get i₁ = ofBool c₁) (h₂ : env.get i₂ = ofBool c₂) (h₃ : env.get i₃ = ofBool c₃)
    (h₄ : env.get i₄ = ofBool c₄) :
    ∃ t ≤ 8, Eval env (andExpr i₁ i₂ i₃ i₄) (ofBool (c₁ && c₂ && c₃ && c₄)) t := by
  unfold andExpr
  cases c₁
  · exact ⟨2, by omega, Eval.elim_nil (i := i₁) (by simpa [ofBool] using h₁) (Eval.nil _)⟩
  cases c₂
  · exact ⟨3, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_nil (i := i₂ + 2) (by simpa [ofBool] using h₂) (Eval.nil _))⟩
  cases c₃
  · exact ⟨4, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_cons (i := i₂ + 2) (a := .nil) (b := .nil) (by simpa [ofBool] using h₂)
        (Eval.elim_nil (i := i₃ + 4) (by simpa [ofBool] using h₃) (Eval.nil _)))⟩
  cases c₄
  · exact ⟨5, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_cons (i := i₂ + 2) (a := .nil) (b := .nil) (by simpa [ofBool] using h₂)
        (Eval.elim_cons (i := i₃ + 4) (a := .nil) (b := .nil) (by simpa [ofBool] using h₃)
          (Eval.elim_nil (i := i₄ + 6) (by simpa [ofBool] using h₄) (Eval.nil _))))⟩
  · exact ⟨7, by omega, Eval.elim_cons (i := i₁) (a := .nil) (b := .nil) (by simpa [ofBool] using h₁)
      (Eval.elim_cons (i := i₂ + 2) (a := .nil) (b := .nil) (by simpa [ofBool] using h₂)
        (Eval.elim_cons (i := i₃ + 4) (a := .nil) (b := .nil) (by simpa [ofBool] using h₃)
          (Eval.elim_cons (i := i₄ + 6) (a := .nil) (b := .nil) (by simpa [ofBool] using h₄)
            (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (sP dP : Data)
    (lam tau beta n s : ℕ) (xD yD aD bD : Data) {td : ℕ}
    (hdim : Eval [Data.cons sP (.cons (encode n) (encode CL.Sampler.Query.dimension))] univ
      (encode s) td) :
    ∃ t ≤ prepCost sP dP lam tau beta n s xD yD aD bD td,
      Eval [decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD]
        (prepProg univ)
        (prepResult dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD))
          (bitsOf (toList aD)) (bitsOf (toList bD))) t := by
  set E := prepEnv univ sP dP lam tau beta n s xD yD aD bD with hE
  obtain ⟨t_ok, ht_ok, h_ok⟩ := andExpr_runs (env := E) (i₁ := 11) (i₂ := 8) (i₃ := 4) (i₄ := 0)
    (c₁ := decide ((bitsOf (toList xD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))) (c₂ := decide ((bitsOf (toList yD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))
    (c₃ := (parse (bitsOf (toList aD))).toBitsPost == (bitsOf (toList aD))) (c₄ := (parse (bitsOf (toList bD))).toBitsPost == (bitsOf (toList bD)))
    (by simp [hE, prepEnv]) (by simp [hE, prepEnv]) (by simp [hE, prepEnv]) (by simp [hE, prepEnv])
  set okv := decide ((bitsOf (toList xD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) && decide ((bitsOf (toList yD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) &&
    ((parse (bitsOf (toList aD))).toBitsPost == (bitsOf (toList aD))) && ((parse (bitsOf (toList bD))).toBitsPost == (bitsOf (toList bD))) with hokv
  have hokv' : prepOk lam tau n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) = okv := rfl
  set ctxv : Data := .cons dP (.cons (encode n) (.cons (ofNat s) (ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))))) with hctxv
  have hctx_build : Eval (ofBool okv :: E)
      (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19)))) ctxv
      (dP.size + 1 + ((encode n : Data).size + 1 + ((ofNat s).size + 1 + ((ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))).size + 1) + 1) + 1) + 1) :=
    Eval.cons (Eval.var_of_get (i := 49) (v := dP) (by simp [hE, prepEnv]))
      (Eval.cons (Eval.var_of_get (i := 41) (v := encode n) (by simp [hE, prepEnv]))
        (Eval.cons (Eval.var_of_get (i := 32) (v := ofNat s) (by simp [hE, prepEnv]))
          (Eval.var_of_get (i := 19) (v := ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))) (by simp [hE, prepEnv]))))
  have hsx : (encode (bitsOf (toList xD)) : Data).size ≤ 4 * (bitsOf (toList xD)).length + 1 := esize_bitStr_le (bitsOf (toList xD))
  have hsy : (encode (bitsOf (toList yD)) : Data).size ≤ 4 * (bitsOf (toList yD)).length + 1 := esize_bitStr_le (bitsOf (toList yD))
  by_cases hok : okv = true
  · have hc : Eval E (.let_ (andExpr 11 8 4 0)
        (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19))))
          (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11)
            (.cons (.var 7) (.var 2)))))))))
        (prepState dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD))) _ :=
      Eval.let_ h_ok
        (Eval.let_ hctx_build
          (Eval.elim_cons (i := 1) (n := .nil) (a := .nil) (b := .nil) (by simp [hok, ofBool])
            (Eval.cons (Eval.var_of_get (i := 27) (v := ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (by simp [hE, prepEnv]))
              (Eval.cons (Eval.var_of_get (i := 21) (v := encode (bitsOf (toList xD))) (by simp [hE, prepEnv]))
                (Eval.cons (Eval.var_of_get (i := 20) (v := encode (bitsOf (toList yD))) (by simp [hE, prepEnv]))
                  (Eval.cons (Eval.var_of_get (i := 11) (v := parse (bitsOf (toList aD))) (by simp [hE, prepEnv]))
                    (Eval.cons (Eval.var_of_get (i := 7) (v := parse (bitsOf (toList bD))) (by simp [hE, prepEnv]))
                      (Eval.var_of_get (i := 2) (v := ctxv) (by simp [hctxv])))))))))
    obtain ⟨t', ht', run⟩ := prepProg_prefix hU sP dP lam tau beta n s xD yD aD bD hdim hc
    rw [show prepResult dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) = prepState dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) by
      simp [prepResult, hokv', hok]]
    refine ⟨t', ?_, run⟩
    have hpa := size_parse_le (bitsOf (toList aD))
    have hpb := size_parse_le (bitsOf (toList bD))
    unfold prepCost
    simp only [size_ofNat, hctxv, size_cons] at ht' ⊢
    omega
  · have hc : Eval E (.let_ (andExpr 11 8 4 0)
        (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19))))
          (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11)
            (.cons (.var 7) (.var 2)))))))))
        .nil _ :=
      Eval.let_ h_ok
        (Eval.let_ hctx_build
          (Eval.elim_nil (i := 1) (by simp [Bool.eq_false_iff.mpr hok, ofBool]) (Eval.nil _)))
    obtain ⟨t', ht', run⟩ := prepProg_prefix hU sP dP lam tau beta n s xD yD aD bD hdim hc
    rw [show prepResult dP lam tau beta n s (bitsOf (toList xD)) (bitsOf (toList yD)) (bitsOf (toList aD)) (bitsOf (toList bD)) = .nil by
      simp [prepResult, hokv', hok]]
    refine ⟨t', ?_, run⟩
    unfold prepCost
    simp only [size_ofNat] at ht' ⊢
    omega
end MIPRE.Cost.Prog
