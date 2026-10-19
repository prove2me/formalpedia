-- Prove2me | solution 1 for MIPRE.CL.ProductSampler.route_call_size
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:00.023613+00:00
-- url     : https://prove2.me/submissions/f26c3270-6070-4796-81a4-fe4bbf7e05a9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSamplerCost.lean (solution of MIPRE.CL.ProductSampler.route_call_size);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_CL_ProductSampler_size_queryA_le

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.ProductSampler
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
theorem _root_.solution (ap pp : Prog) (ℓa n : ℕ) (pdn q payload : Data)
    (h : route B D (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) =
      (true, payload)) :
    ∃ a ctx, payload = .cons (.cons (encode ap) a) ctx ∧
      a.size ≤ esize n + 12 * q.size + 4 * ℓa + 20 := by
  set x : Data := .cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q)) with hx
  have hlev : levelA x = ℓa := by
    simp only [levelA, comp_apply, x, treeTail_cons, treeHead_cons, encode_prod, readNat_encode]
  have hprog : progD x = encode ap := by
    simp only [progD, comp_apply, x, treeTail_cons, treeHead_cons, encode_prod]
  simp only [route, PolyTimeFun.ite_apply] at h
  split_ifs at h with h1 h2 h3
  · have hp := (Prod.mk.inj h).2
    simp only [ap₂_apply, treePair_apply, hprog, const_apply] at hp
    subst hp
    refine ⟨_, _, rfl, ?_⟩
    simp only [nD, x, comp_apply, treeHead_cons, treeTail_cons, Data.size_cons, Data.size_nil]
    change esize n + 1 + 1 ≤ _
    omega
  · have hp := (Prod.mk.inj h).2
    simp only [ap₂_apply, treePair_apply, hprog] at hp
    subst hp
    refine ⟨_, _, rfl, size_queryA_le D levA ap pp ℓa n pdn q ?_⟩
    show levA x ≤ ℓa
    have : levA x ≤ levelA x := by
      simp only [levA, PolyTimeFun.ite_apply, ap₂_apply, leNat_apply, decide_eq_true_eq]
      split_ifs with h4
      · exact h4
      · exact le_rfl
    rwa [hlev] at this
  · have hp := (Prod.mk.inj h).2
    simp only [ap₂_apply, treePair_apply, hprog] at hp
    subst hp
    refine ⟨_, _, rfl, size_queryA_le D lev ap pp ℓa n pdn q ?_⟩
    simpa [ap₂_apply, leNat_apply, hlev] using h3
  · simp [direct] at h
end MIPRE.CL.ProductSampler
