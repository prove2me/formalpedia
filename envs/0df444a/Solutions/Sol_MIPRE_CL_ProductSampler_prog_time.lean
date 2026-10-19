-- Prove2me | solution 1 for MIPRE.CL.ProductSampler.prog_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:16.479901+00:00
-- url     : https://prove2.me/submissions/86e63a2b-fbb7-4b61-affc-e488579792cb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSamplerCost.lean (solution of MIPRE.CL.ProductSampler.prog_time);
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
import Theorems.Thm_MIPRE_CL_ProductSampler_stage_time
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_seqProg_runs
import Theorems.Thm_MIPRE_Pipeline_PDom_ofCallPow
import Theorems.Thm_MIPRE_Pipeline_PDom_poly

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open PolyTimeFun
theorem callWithContext_closed {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) : (callWithContext p post).WellScoped 1 := by
  refine ⟨fstProg_wellScoped, hp.mono (by omega) _, ?_⟩
  exact ⟨⟨callVar_wellScoped (by decide) sndProg_wellScoped, by simp [WellScoped]⟩,
    post.closed.mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem callWithContext_cost {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (time : ℕ)
    (hr : p.Runs a r time) :
    ∃ t ≤ 2 * a.size + 2 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 12,
      (callWithContext p post).Runs (.cons a ctx) (post (ctx, r)) t := by
  obtain ⟨tp, htp, hpRun⟩ := post.computes (ctx, r)
  have ectx := callVar_eval (env := [r, a, Data.cons a ctx]) (i := 2)
    sndProg_wellScoped (by simp) (sndProg_runs a ctx)
  have run := Eval.let_ (fstProg_runs a ctx)
    (Eval.let_ (Eval.append_of_wellScoped hr hp _)
      (Eval.let_ (Eval.cons ectx (Eval.var_of_get (i := 0) (by simp)))
        (Eval.append_of_wellScoped hpRun post.closed _)))
  refine ⟨_, ?_, run⟩
  simp only [esize_prod, esize_data, Data.size_cons, encode_data] at *
  omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem routeOneCall_indirect_cost (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (x a ctx r : Data) (time : ℕ) (h : route x = (true, .cons a ctx))
    (hr : p.Runs a r time) :
    ∃ t ≤ route.timeBound.eval x.size + 3 * a.size + 3 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 18,
      (routeOneCall route p post).Runs x (post (ctx, r)) t := by
  obtain ⟨t, ht, hroute⟩ := route.computes x
  rw [h] at hroute
  obtain ⟨tc, htc, hc⟩ := callWithContext_cost hp post a ctx r time hr
  refine ⟨_, ?_, Eval.let_ hroute
    (Eval.elim_cons (i := 0) (a := Data.cons .nil .nil) (b := .cons a ctx)
      (by simp [encode, Data.ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := .nil) (by simp)
        (callVar_eval (i := 3) (callWithContext_closed hp post) (by simp) hc)))⟩
  simp only [esize_data, Data.size_cons] at *
  omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem of_le {c m e v v' : ℕ} (h : PDom W X K c m e v) (hv : v' ≤ v) : PDom W X K c m e v' :=
  hv.trans h
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : PDom W X K c m e v) (hc : c ≤ c')
    (hm : m ≤ m') (he : e ≤ e') : PDom W X K c' m' e' v := by
  refine h.trans (Nat.pow_le_pow_left ?_ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm))
    (Nat.pow_le_pow_right hX he)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A base of at least one is below its `(K + 1)`-st power. -/
theorem le_pow_succ {a : ℕ} : a ≤ a ^ (K + 1) :=
  Nat.le_self_pow (by omega) a
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem const (c : ℕ) : PDom W X K (c + 1) 0 0 c := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact (Nat.le_succ c).trans (le_pow_succ)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- An affine function of `W`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : PDom W X K (a + b + 1) 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one]
  refine h.trans ((?_ : a * W + b ≤ (a + b + 1) * (W + 1)).trans le_pow_succ)
  nlinarith
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem ofLeX {v : ℕ} (h : v ≤ X) : PDom W X K 1 0 1 v := by
  simp only [PDom, pow_zero, pow_one, Nat.mul_one, Nat.one_mul]
  exact h.trans (le_pow_succ)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) :
    PDom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold PDom at h₁' h₂' ⊢
  refine (Nat.add_le_add h₁' h₂').trans ?_
  rw [Nat.add_mul, Nat.add_mul]
  exact pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) : PDom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold PDom at h₁ h₂ ⊢
  refine (Nat.mul_le_mul h₁ h₂).trans (le_of_eq ?_)
  rw [← mul_pow, pow_add, pow_add]
  ring_nf
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.ProductSampler
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
theorem _root_.solution (ℓa cp mp ep cs ms es cA mA eA : ℕ) : ∃ C M E, ∀ {W K : ℕ} (ap pp : Prog)
    (n : ℕ) (pdn : Data) (BA : ℕ), n ≤ W →
    (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cp mp ep pp (encode n) pdn) →
    (∀ {X : ℕ}, 1 ≤ X → PDom W X K cs ms es (esize ap + esize pp)) →
    BA ≤ cA * (W + 1) ^ mA →
    (∀ d, HaltsWithin ap (.cons (encode n) d) (BA * (d.size + 1) ^ (eA * (K + 1)))) →
    ∀ q : Data, ∃ r t, PDom W (q.size + 1) K C M E t ∧
      (prog B D ap ℓa pp).Runs (.cons (encode n) q) r t := by
  exact ⟨_, _, _, fun {W K} ap pp n pdn BA hn hpp hsz hBA hA q => by
    have hX : 1 ≤ q.size + 1 := by omega
    obtain ⟨tp, htp, hprun⟩ := hpp hX
    have hs := hsz hX
    have en := esize_nat_le_four n
    have el := esize_nat_le_four ℓa
    have hpdn : PDom W (q.size + 1) K cp mp ep pdn.size := htp.of_le hprun.size_le
    have hnW : PDom W (q.size + 1) K _ _ _ (esize n) := PDom.ofAffine (a := 4) (b := 1) (by omega)
    have hq : PDom W (q.size + 1) K _ _ _ q.size := PDom.ofLeX (by omega)
    -- stage 0: the parameters
    set x0 : Data := .cons (encode (ap, ℓa, pp)) (.cons (encode n) q) with hx0def
    have hx0 : x0.size = esize ap + esize ℓa + esize pp + esize n + q.size + 4 := by
      simp only [x0, Data.size_cons, encode_prod]
      change esize ap + (esize ℓa + esize pp + 1) + 1 + (esize n + q.size + 1) + 1 = _
      omega
    have hX0 := (((hs.add hX hnW).add hX hq).add hX (PDom.const (esize ℓa + 4))).of_le
      (show x0.size ≤ esize ap + esize pp + esize n + q.size + (esize ℓa + 4) by omega)
    obtain ⟨tU0, htU0, hU0⟩ := selfUniversal.time_le pp (encode n) pdn tp hprun
    obtain ⟨t0, ht0, h0⟩ := Prog.routeOneCall_indirect_cost route0 selfUniversal.closed post0 x0
      (.cons (encode pp) (encode n)) x0 pdn tU0 rfl hU0
    have hpost0 : post0 (x0, pdn) = .cons pdn x0 := rfl
    rw [hpost0] at h0
    -- the routed stage
    obtain ⟨r, t1, ht1, h1⟩ := stage_time B D ap pp ℓa n pdn q BA (eA * (K + 1)) hA
    rw [← hx0def] at ht1 h1
    refine ⟨r, _, ?_, hardcode_time (core_closed B D)
      (show (core B D).Runs _ _ _ from seqProg_runs (stage_closed B D) h0 h1)⟩
    -- the accounting
    have hU0' : PDom W (q.size + 1) K _ _ _
        (selfUniversal.bound.eval (esize ap + esize pp + esize n + 1 + tp)) :=
      (((hs.add hX hnW).add hX (PDom.const 1)).add hX htp).poly hX selfUniversal.bound
    have hR0 := hX0.poly hX route0.timeBound
    have hP0 := ((hX0.add hX hpdn).add hX (PDom.const 1)).poly hX post0.timeBound
    have hx1 : PDom W (q.size + 1) K _ _ _ (pdn.size + x0.size + 1) :=
      (hpdn.add hX hX0).add hX (PDom.const 1)
    have hRt := hx1.poly hX (route B D).timeBound
    have hA' : PDom W (q.size + 1) K _ _ _
        (BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ (eA * (K + 1))) :=
      PDom.ofCallPow (c₁ := 4 * ℓa + 37) (m₁ := 1) (e₁ := 1) hBA
        (by
          simp only [pow_one]
          have h37 : 37 * (W + 1) * (q.size + 1) ≤ (4 * ℓa + 37) * (W + 1) * (q.size + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
          have hWq : W + q.size + 1 ≤ (W + 1) * (q.size + 1) := by nlinarith
          have h4l : 4 * ℓa ≤ 4 * ℓa * ((W + 1) * (q.size + 1)) :=
            Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
          have := Nat.mul_le_mul_left 37 hWq
          nlinarith) le_rfl
    have hlin : PDom W (q.size + 1) K _ _ _ (esize n + 12 * q.size + 4 * ℓa + 21) :=
      ((hnW.add hX ((PDom.const 12).mul hq)).add hX (PDom.const (4 * ℓa + 21)))
    have hU1 := (((hs.add hX hlin).add hX hA')).poly hX selfUniversal.bound
    have hP1 := ((hRt.add hX hU1).add hX (PDom.const 1)).poly hX post.timeBound
    have htot := (((((((((((PDom.const 3).mul hR0).add hX ((PDom.const 12).mul hX0)).add hX
      ((PDom.const 3).mul hpdn)).add hX ((PDom.const 3).mul hU0')).add hX
      ((PDom.const 3).mul hP0)).add hX ((PDom.const 4).mul hRt)).add hX
      ((PDom.const 3).mul hs)).add hX ((PDom.const 3).mul hlin)).add hX
      ((PDom.const 2).mul hU1)).add hX ((PDom.const 3).mul hP1)).add hX (PDom.const 200)
    refine htot.of_le ?_
    have hU0le : tU0 ≤ selfUniversal.bound.eval (esize ap + esize pp + esize n + 1 + tp) := by
      refine htU0.trans (polynomial_eval_mono _ ?_)
      change esize pp + (esize n) + tp ≤ _
      omega
    have hpdn_le : pdn.size ≤ tU0 := hU0.size_le
    have e1 : (encode pp : Data).size = esize pp := rfl
    have e2 : (encode n : Data).size = esize n := rfl
    have hP0le := polynomial_eval_mono post0.timeBound
      (show x0.size + pdn.size + 1 ≤ x0.size + pdn.size + 1 from le_rfl)
    simp only [stageBound, Data.size_cons] at ht1
    have hUm := polynomial_eval_mono selfUniversal.bound (show esize ap +
      (esize n + 12 * q.size + 4 * ℓa + 20) + BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^
        (eA * (K + 1)) ≤ esize ap + esize pp + (esize n + 12 * q.size + 4 * ℓa + 21) +
      BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ (eA * (K + 1)) by omega)
    have hPm := polynomial_eval_mono post.timeBound (show
      (route B D).timeBound.eval (pdn.size + x0.size + 1) + selfUniversal.bound.eval (esize ap +
        (esize n + 12 * q.size + 4 * ℓa + 20) + BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^
          (eA * (K + 1))) + 1 ≤
      (route B D).timeBound.eval (pdn.size + x0.size + 1) + selfUniversal.bound.eval (esize ap +
        esize pp + (esize n + 12 * q.size + 4 * ℓa + 21) +
          BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ (eA * (K + 1))) + 1 by omega)
    simp only [Data.size_cons] at ht0
    have hH : (encode (ap, ℓa, pp) : Data).size = esize ap + esize ℓa + esize pp + 2 := by
      simp only [encode_prod, Data.size_cons]
      change esize ap + (esize ℓa + esize pp + 1) + 1 = _
      omega
    simp only [Data.size_cons]
    rw [hH]
    omega⟩
end MIPRE.CL.ProductSampler
