-- Prove2me | solution 1 for MIPRE.Cost.Prog.prepProg_prefix
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:35:12.978974+00:00
-- url     : https://prove2.me/submissions/f9ada595-457f-4534-8b23-4e7b9ca51d7c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecMain.lean (solution of MIPRE.Cost.Prog.prepProg_prefix);
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
import Theorems.Thm_MIPRE_Cost_Data_encode_nat_eq_list
import Theorems.Thm_MIPRE_Cost_Prog_bitsProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_dblLoop_runs
import Theorems.Thm_MIPRE_Cost_Prog_parseProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_powLoop_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
theorem eqBits_encode (x y : BitStr) : eqBits (encode x) (encode y) = (x == y) := by
  induction x generalizing y with
  | nil => cases y <;> simp [eqBits, encode_bitStr_nil, encode_bitStr_cons]
  | cons b x ih =>
    cases y with
    | nil => simp [eqBits, encode_bitStr_nil, encode_bitStr_cons]
    | cons c y => simp [eqBits, encode_bitStr_cons, ih]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
section
open Data
theorem powBody_wellScoped : powBody.WellScoped 1 := by
  simp [powBody, WellScoped, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dblBody_wellScoped : dblBody.WellScoped 1 := by
  simp [dblBody, WellScoped, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
/-- The size of the encoded dimension query. -/
theorem size_encode_dimension : (encode CL.Sampler.Query.dimension : Data).size = 9 := rfl
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem parseProg_wellScoped : parseProg.WellScoped 1 := by simp [parseProg, WellScoped, parseBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitsProg_wellScoped : bitsProg.WellScoped 1 := by
  simp [bitsProg, WellScoped, bitsBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem powLoop_wellScoped : (Prog.loop powBody).WellScoped 1 := ⟨Nat.zero_lt_one, powBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem dblLoop_wellScoped : (Prog.loop dblBody).WellScoped 1 := ⟨Nat.zero_lt_one, dblBody_wellScoped⟩
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution {univ : Prog} (hU : univ.WellScoped 1) (sP dP : Data)
    (lam tau beta n s : ℕ) (xD yD aD bD : Data) {td : ℕ}
    (hdim : Eval [Data.cons sP (.cons (encode n) (encode CL.Sampler.Query.dimension))] univ (encode s) td)
    {r : Data} {t : ℕ}
    (hc : Eval (prepEnv univ sP dP lam tau beta n s xD yD aD bD) (.let_ (andExpr 11 8 4 0) (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19)))) (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11) (.cons (.var 7) (.var 2))))))))) r t) :
    ∃ t' ≤ t + prepPreCost sP dP lam tau beta n s xD yD aD bD td,
      Eval [decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD] (prepProg univ) r t' := by
  obtain ⟨t_us, ht_us, h_us⟩ := toUnaryProg_runs s
  obtain ⟨t_ut, ht_ut, h_ut⟩ := toUnaryProg_runs tau
  obtain ⟨t_ub, ht_ub, h_ub⟩ := toUnaryProg_runs beta
  obtain ⟨t_mt, ht_mt, h_mt⟩ := powLoop_runs tau (lam.bits.map ofBool) (n.bits.map ofBool) [] []
  obtain ⟨t_mb, ht_mb, h_mb⟩ := powLoop_runs beta (lam.bits.map ofBool) (n.bits.map ofBool) [] []
  simp only [List.append_nil, ← ofNat_eq_list_replicate, List.length_map, Nat.size_eq_bits_len,
    powState, list_nil, ← encode_nat_eq_list, size_nil] at h_mt h_mb ht_mt ht_mb
  obtain ⟨t_uks, ht_uks, h_uks⟩ := dblLoop_runs (tau * (Nat.size lam + Nat.size n)) s []
  obtain ⟨t_uk, ht_uk, h_uk⟩ := dblLoop_runs (tau * (Nat.size lam + Nat.size n)) 1 []
  rw [mul_one] at h_uk
  obtain ⟨t_uB, ht_uB, h_uB⟩ := dblLoop_runs (beta * (Nat.size lam + Nat.size n)) 1 []
  rw [mul_one] at h_uB
  obtain ⟨t_x, ht_x, h_x⟩ := bitsProg_runs (toList xD)
  obtain ⟨t_y, ht_y, h_y⟩ := bitsProg_runs (toList yD)
  obtain ⟨t_a, ht_a, h_a⟩ := bitsProg_runs (toList aD)
  obtain ⟨t_b, ht_b, h_b⟩ := bitsProg_runs (toList bD)
  rw [list_toList] at h_x h_y h_a h_b ht_x ht_y ht_a ht_b
  obtain ⟨t_lx, ht_lx, h_lx⟩ := lenProg_runs ((bitsOf (toList xD)).map ofBool)
  obtain ⟨t_ly, ht_ly, h_ly⟩ := lenProg_runs ((bitsOf (toList yD)).map ofBool)
  rw [← encode_bitStr_eq_list, List.length_map] at h_lx h_ly ht_lx ht_ly
  obtain ⟨t_ex, ht_ex, h_ex⟩ := eqBitsProg_runs (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) [] _ le_rfl
  obtain ⟨t_ey, ht_ey, h_ey⟩ := eqBitsProg_runs (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) [] _ le_rfl
  rw [eqBits_ofNat] at h_ex h_ey
  simp only [encode_bool] at h_ex h_ey
  obtain ⟨t_pa, ht_pa, h_pa⟩ := parseProg_runs (bitsOf (toList aD))
  obtain ⟨t_sa, ht_sa, h_sa⟩ := serProg_runs (parse (bitsOf (toList aD)))
  obtain ⟨t_ea, ht_ea, h_ea⟩ := eqBitsProg_runs (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD))) [] _ le_rfl
  obtain ⟨t_pb, ht_pb, h_pb⟩ := parseProg_runs (bitsOf (toList bD))
  obtain ⟨t_sb, ht_sb, h_sb⟩ := serProg_runs (parse (bitsOf (toList bD)))
  obtain ⟨t_eb, ht_eb, h_eb⟩ := eqBitsProg_runs (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD))) [] _ le_rfl
  rw [eqBits_encode] at h_ea h_eb
  simp only [encode_bool] at h_ea h_eb
  have run : Eval [decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD] (prepProg univ) r _ :=
    Eval.elim_cons (i := 0) (n := .nil) (a := sP) (b := (Data.cons dP (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))))))) (by simp [decInput]) (Eval.elim_cons (i := 1) (n := .nil) (a := dP) (b := (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode lam)) (b := (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode tau)) (b := (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode beta)) (b := (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := (encode n)) (b := (Data.cons xD (Data.cons yD (Data.cons aD bD)))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := xD) (b := (Data.cons yD (Data.cons aD bD))) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := yD) (b := (Data.cons aD bD)) (by simp) (Eval.elim_cons (i := 1) (n := .nil) (a := aD) (b := bD) (by simp) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 16) (v := sP) (by simp)) (Eval.cons (Eval.var_of_get (i := 6) (v := (encode n)) (by simp)) (Eval.const _ _))) (Eval.let_ (callVar_eval hU (i := 0) (v := (Data.cons sP (Data.cons (encode n) (encode CL.Sampler.Query.dimension)))) (by simp) hdim) (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 0) (v := (encode s)) (by simp) h_us) (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 13) (v := (encode tau)) (by simp) h_ut) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat tau)) (by simp)) (Eval.cons (Eval.var_of_get (i := 16) (v := (encode lam)) (by simp)) (Eval.cons (Eval.var_of_get (i := 10) (v := (encode n)) (by simp)) (Eval.nil _)))) (Eval.let_ (callVar_eval powLoop_wellScoped (i := 0) (v := (Data.cons (ofNat tau) (Data.cons (encode lam) (Data.cons (encode n) Data.nil)))) (by simp) h_mt) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (tau * (Nat.size lam + Nat.size n)))) (by simp)) (Eval.var_of_get (i := 3) (v := (ofNat s)) (by simp))) (Eval.let_ (callVar_eval dblLoop_wellScoped (i := 0) (v := (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat s))) (by simp) h_uks) (Eval.let_ (Eval.const _ _) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 3) (v := (ofNat (tau * (Nat.size lam + Nat.size n)))) (by simp)) (Eval.var_of_get (i := 0) (v := (ofNat 1)) (by simp))) (Eval.let_ (callVar_eval dblLoop_wellScoped (i := 0) (v := (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat 1))) (by simp) h_uk) (Eval.let_ (callVar_eval toUnaryProg_wellScoped (i := 19) (v := (encode beta)) (by simp) h_ub) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat beta)) (by simp)) (Eval.cons (Eval.var_of_get (i := 24) (v := (encode lam)) (by simp)) (Eval.cons (Eval.var_of_get (i := 18) (v := (encode n)) (by simp)) (Eval.nil _)))) (Eval.let_ (callVar_eval powLoop_wellScoped (i := 0) (v := (Data.cons (ofNat beta) (Data.cons (encode lam) (Data.cons (encode n) Data.nil)))) (by simp) h_mb) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (beta * (Nat.size lam + Nat.size n)))) (by simp)) (Eval.var_of_get (i := 5) (v := (ofNat 1)) (by simp))) (Eval.let_ (callVar_eval dblLoop_wellScoped (i := 0) (v := (Data.cons (ofNat (beta * (Nat.size lam + Nat.size n))) (ofNat 1))) (by simp) h_uB) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 20) (v := xD) (by simp) h_x) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 19) (v := yD) (by simp) h_y) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 18) (v := aD) (by simp) h_a) (Eval.let_ (callVar_eval bitsProg_wellScoped (i := 20) (v := bD) (by simp) h_b) (Eval.let_ (callVar_eval lenProg_wellScoped (i := 3) (v := (encode (bitsOf (toList xD)))) (by simp) h_lx) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (bitsOf (toList xD)).length)) (by simp)) (Eval.var_of_get (i := 13) (v := (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))) (by simp) h_ex) (Eval.let_ (callVar_eval lenProg_wellScoped (i := 5) (v := (encode (bitsOf (toList yD)))) (by simp) h_ly) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (ofNat (bitsOf (toList yD)).length)) (by simp)) (Eval.var_of_get (i := 16) (v := (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))) (by simp) h_ey) (Eval.let_ (callVar_eval parseProg_wellScoped (i := 7) (v := (encode (bitsOf (toList aD)))) (by simp) h_pa) (Eval.let_ (callVar_eval serProg_wellScoped (i := 0) (v := (parse (bitsOf (toList aD)))) (by simp) h_sa) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (encode (parse (bitsOf (toList aD))).toBitsPost)) (by simp)) (Eval.var_of_get (i := 9) (v := (encode (bitsOf (toList aD)))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD))))) (by simp) h_ea) (Eval.let_ (callVar_eval parseProg_wellScoped (i := 10) (v := (encode (bitsOf (toList bD)))) (by simp) h_pb) (Eval.let_ (callVar_eval serProg_wellScoped (i := 0) (v := (parse (bitsOf (toList bD)))) (by simp) h_sb) (Eval.let_ (Eval.cons (Eval.var_of_get (i := 0) (v := (encode (parse (bitsOf (toList bD))).toBitsPost)) (by simp)) (Eval.var_of_get (i := 12) (v := (encode (bitsOf (toList bD)))) (by simp))) (Eval.let_ (callVar_eval eqBitsProg_wellScoped (i := 0) (v := (Data.cons (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD))))) (by simp) h_eb) (hc)))))))))))))))))))))))))))))))))))))))))))
  refine ⟨_, ?_, run⟩
  have s_us := h_us.size_le
  have s_ut := h_ut.size_le
  have s_ub := h_ub.size_le
  have s_mt := h_mt.size_le
  have s_mb := h_mb.size_le
  have s_uks := h_uks.size_le
  have s_uk := h_uk.size_le
  have s_uB := h_uB.size_le
  have s_x := h_x.size_le
  have s_y := h_y.size_le
  have s_a := h_a.size_le
  have s_b := h_b.size_le
  have s_lx := h_lx.size_le
  have s_ly := h_ly.size_le
  have s_ex := h_ex.size_le
  have s_ey := h_ey.size_le
  have s_pa := h_pa.size_le
  have s_sa := h_sa.size_le
  have s_ea := h_ea.size_le
  have s_pb := h_pb.size_le
  have s_sb := h_sb.size_le
  have s_eb := h_eb.size_le
  have s_sD := hdim.size_le
  have s_one : (ofNat 1).size = 3 := rfl
  have ht_us' : t_us ≤ toUnaryCost s := ht_us
  have ht_ut' : t_ut ≤ toUnaryCost tau := ht_ut
  have ht_ub' : t_ub ≤ toUnaryCost beta := ht_ub
  have ht_x' : t_x ≤ bitsCost (toList xD).length xD.size := ht_x
  have ht_y' : t_y ≤ bitsCost (toList yD).length yD.size := ht_y
  have ht_a' : t_a ≤ bitsCost (toList aD).length aD.size := ht_a
  have ht_b' : t_b ≤ bitsCost (toList bD).length bD.size := ht_b
  have ht_lx' : t_lx ≤ lenCost _ _ := ht_lx
  have ht_ly' : t_ly ≤ lenCost _ _ := ht_ly
  have ht_ex' : t_ex ≤ eqCost _ _ := ht_ex
  have ht_ey' : t_ey ≤ eqCost _ _ := ht_ey
  have ht_pa' : t_pa ≤ parseCost _ := ht_pa
  have ht_sa' : t_sa ≤ serCost _ := ht_sa
  have ht_ea' : t_ea ≤ eqCost _ _ := ht_ea
  have ht_pb' : t_pb ≤ parseCost _ := ht_pb
  have ht_sb' : t_sb ≤ serCost _ := ht_sb
  have ht_eb' : t_eb ≤ eqCost _ _ := ht_eb
  clear ht_us ht_ut ht_ub ht_x ht_y ht_a ht_b ht_lx ht_ly ht_ex ht_ey ht_pa ht_sa ht_ea ht_pb ht_sb ht_eb
  unfold prepPreCost
  simp only [size_cons, size_encode_dimension, size_nil]
  omega
end MIPRE.Cost.Prog
