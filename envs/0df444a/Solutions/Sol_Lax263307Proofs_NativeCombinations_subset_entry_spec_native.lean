-- Prove2me | solution 1 for Lax263307Proofs.NativeCombinations.subset_entry_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:40.786197+00:00
-- url     : https://prove2.me/submissions/df3f31f1-a2f6-4e6a-9a6e-399bc0b7439f

import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Take
import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax109476.RationalFeasibility
end Lax109476.RationalFeasibility
namespace Lax109476Proofs.BinaryOptimization
end Lax109476Proofs.BinaryOptimization
namespace Lax109476Proofs.BinaryOptimizationBounds
end Lax109476Proofs.BinaryOptimizationBounds
namespace Lax109476Proofs.CertificateSystems
end Lax109476Proofs.CertificateSystems
namespace Lax109476Proofs.CoordinateOptimization
end Lax109476Proofs.CoordinateOptimization
namespace Lax109476Proofs.DeterminantBounds
end Lax109476Proofs.DeterminantBounds
namespace Lax109476Proofs.EllipsoidDeterminant
end Lax109476Proofs.EllipsoidDeterminant
namespace Lax109476Proofs.EllipsoidStateSize
end Lax109476Proofs.EllipsoidStateSize
namespace Lax109476Proofs.EllipsoidTermination
end Lax109476Proofs.EllipsoidTermination
namespace Lax109476Proofs.IterationBudget
end Lax109476Proofs.IterationBudget
namespace Lax109476Proofs.LexicographicBounds
end Lax109476Proofs.LexicographicBounds
namespace Lax109476Proofs.PointRecovery
end Lax109476Proofs.PointRecovery
namespace Lax109476Proofs.RamEllipsoidStoredBounds
end Lax109476Proofs.RamEllipsoidStoredBounds
namespace Lax109476Proofs.RamEllipsoidWordBounds
end Lax109476Proofs.RamEllipsoidWordBounds
namespace Lax109476Proofs.RamFrame
end Lax109476Proofs.RamFrame
namespace Lax109476Proofs.RamPadEntries
end Lax109476Proofs.RamPadEntries
namespace Lax109476Proofs.RamPrimitiveBounds
end Lax109476Proofs.RamPrimitiveBounds
namespace Lax109476Proofs.RamRecoveryData
end Lax109476Proofs.RamRecoveryData
namespace Lax109476Proofs.RamScalarFrame
end Lax109476Proofs.RamScalarFrame
namespace Lax109476Proofs.RationalFeasibility
end Lax109476Proofs.RationalFeasibility
namespace Lax109476Proofs.RationalMinima
end Lax109476Proofs.RationalMinima
namespace Lax109476Proofs.SmallFeasiblePoint
end Lax109476Proofs.SmallFeasiblePoint
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
namespace Lax263307Proofs.ConditioningDistribution
end Lax263307Proofs.ConditioningDistribution
namespace Lax263307Proofs.EntropyDecrease
end Lax263307Proofs.EntropyDecrease
namespace Lax263307Proofs.LightSeparators
end Lax263307Proofs.LightSeparators
namespace Lax263307Proofs.NativeDistanceEntries
end Lax263307Proofs.NativeDistanceEntries
namespace Lax263307Proofs.NativeMachineSegment
end Lax263307Proofs.NativeMachineSegment
namespace Lax263307Proofs.NativeUniformWordGuards
end Lax263307Proofs.NativeUniformWordGuards
namespace Lax455465.ShortPathFlow
end Lax455465.ShortPathFlow
namespace Lax455465Proofs.AcyclicFlowPath
end Lax455465Proofs.AcyclicFlowPath
namespace Lax455465Proofs.LargePotentialData
end Lax455465Proofs.LargePotentialData
namespace Lax455465Proofs.PathSubtraction
end Lax455465Proofs.PathSubtraction
namespace Lax455465Proofs.RamFlowData
end Lax455465Proofs.RamFlowData
namespace Lax455465Proofs.RationalParser
end Lax455465Proofs.RationalParser
namespace Lax455465Proofs.RegionHistory
end Lax455465Proofs.RegionHistory
namespace Lax455465Proofs.RegionInterval
end Lax455465Proofs.RegionInterval
namespace Lax455465Proofs.RegionRuntimeState
end Lax455465Proofs.RegionRuntimeState
namespace Lax455465Proofs.RoundingConstants
end Lax455465Proofs.RoundingConstants
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
namespace Lax759944Proofs.Legacy.RamPolytime
end Lax759944Proofs.Legacy.RamPolytime
namespace Lax808846.RamComputes
end Lax808846.RamComputes
namespace Lax808846Proofs.Machine
end Lax808846Proofs.Machine

section

namespace Lax808846Proofs.Imp

@[simp] theorem Bop.apply_add (m n:ℕ):Bop.add.apply m n=m + n:=rfl
@[simp] theorem Bop.apply_sub (m n:ℕ):Bop.sub.apply m n=m - n:=rfl
@[simp] theorem Bop.apply_mul (m n:ℕ):Bop.mul.apply m n=m * n:=rfl
@[simp] theorem Bop.apply_div (m n:ℕ):Bop.div.apply m n=m / n:=rfl
@[simp] theorem Bop.apply_and (m n:ℕ):Bop.and.apply m n=Nat.land m n:=rfl
@[simp] theorem Bop.apply_or (m n:ℕ):Bop.or.apply m n=Nat.lor m n:=rfl
@[simp] theorem Bop.apply_xor (m n:ℕ):Bop.xor.apply m n=Nat.xor m n:=rfl
@[simp] theorem Bop.apply_shiftl (m n:ℕ):Bop.shiftl.apply m n=m * 2 ^ n:=rfl
@[simp] theorem Bop.apply_shiftr (m n:ℕ):Bop.shiftr.apply m n=m / 2 ^ n:=rfl

@[simp] theorem Expr.add_def (e f:Expr):Expr.add e f=.bin .add e f:=rfl
@[simp] theorem Expr.sub_def (e f:Expr):Expr.sub e f=.bin .sub e f:=rfl
@[simp] theorem Expr.mul_def (e f:Expr):Expr.mul e f=.bin .mul e f:=rfl
@[simp] theorem Expr.div_def (e f:Expr):Expr.div e f=.bin .div e f:=rfl
@[simp] theorem Expr.and_def (e f:Expr):Expr.and e f=.bin .and e f:=rfl
@[simp] theorem Expr.or_def (e f:Expr):Expr.or e f=.bin .or e f:=rfl
@[simp] theorem Expr.xor_def (e f:Expr):Expr.xor e f=.bin .xor e f:=rfl
@[simp] theorem Expr.shiftl_def (e f:Expr):Expr.shiftl e f=.bin .shiftl e f:=rfl
@[simp] theorem Expr.shiftr_def (e f:Expr):Expr.shiftr e f=.bin .shiftr e f:=rfl

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Imp

theorem fit_self {B v:ℕ} (h:v < B):fit B v=some v:=by rw [fit,if_pos h]

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

@[simp] theorem vars_setVar (σ:Env) (x:String) (v:ℕ) (y:String):
    (σ.setVar x v).vars y=if y=x then v else σ.vars y:=rfl

@[simp] theorem arrs_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).arrs=σ.arrs:=rfl

@[simp] theorem inp_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).inp=σ.inp:=rfl

@[simp] theorem out_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).out=σ.out:=rfl

@[simp] theorem vars_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).vars=σ.vars:=rfl

@[simp] theorem arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    (σ.setArr a i v).arrs b=if b=a then (σ.arrs a).set i v else σ.arrs b:=rfl

@[simp] theorem inp_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).inp=σ.inp:=rfl

@[simp] theorem out_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).out=σ.out:=rfl

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_get {B:ℕ} {a:String} {i:Expr} {σ:Env} {k v:ℕ}
    (hi:i.evalB B σ=some k) (hk:(σ.arrs a)[k]?=some v) (hv:v < B):
    (Expr.get a i).evalB B σ=some v:=by
  rw [Expr.evalB,hi,Option.bind_some,hk,Option.bind_some,fit_self hv]

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

theorem evalB_condEq {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.eq e f).evalB B σ=some (m == n):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

theorem evalB_condLt {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.lt e f).evalB B σ=some (decide (m < n)):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

@[simp] theorem size_lit (n:ℕ):(Expr.lit n).size=1:=rfl
@[simp] theorem size_var (x:String):(Expr.var x).size=1:=rfl
@[simp] theorem size_get (a:String) (i:Expr):(Expr.get a i).size=i.size + 1:=rfl
@[simp] theorem size_bin (op:Bop) (e f:Expr):
    (Expr.bin op e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_add (e f:Expr):(Expr.add e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_sub (e f:Expr):(Expr.sub e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_mul (e f:Expr):(Expr.mul e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_div (e f:Expr):(Expr.div e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_and (e f:Expr):(Expr.and e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_or (e f:Expr):(Expr.or e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_xor (e f:Expr):(Expr.xor e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftl (e f:Expr):(Expr.shiftl e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftr (e f:Expr):(Expr.shiftr e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condEq (e f:Expr):(Cond.eq e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condLt (e f:Expr):(Cond.lt e f).size=e.size + f.size + 1:=rfl

theorem Run.of_bigStepB {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ} (h:BigStepB B c σ σ' k):
    Run B c σ σ' k:= ⟨k,le_rfl,h⟩

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

theorem Run.skip {B:ℕ} {σ:Env}:Run B .skip σ σ 1:=.of_bigStepB .skip

theorem Run.assign {B:ℕ} {σ:Env} {x:String} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=.of_bigStepB (.assign h)

theorem Run.store {B:ℕ} {σ:Env} {a:String} {i e:Expr} {idx v:ℕ}
    (hi:i.evalB B σ=some idx) (he:e.evalB B σ=some v)
    (hidx:idx < (σ.arrs a).length):
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size):=
  .of_bigStepB (.store hi he hidx)

theorem Run.read {B:ℕ} {σ:Env} {x:String} {v:ℕ} {rest:List ℕ}
    (h:σ.inp=v::rest):
    Run B (.read x) σ { σ.setVar x v with inp:=rest } 1:=.of_bigStepB (.read h)

theorem Run.write {B:ℕ} {σ:Env} {e:Expr} {v:ℕ} (h:e.evalB B σ=some v):
    Run B (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size):=.of_bigStepB (.write h)

theorem Run.seq {B:ℕ} {c d:Com} {σ σ' σ'':Env} {K K':ℕ}
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):Run B (.seq c d) σ σ'' (K + K'):=by
  obtain ⟨k,hk,hbs⟩:=h
  obtain ⟨k',hk',hbs'⟩:=h'
  exact ⟨k + k',by omega, .seq hbs hbs'⟩

theorem Run.ite_true {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_true hb hbs⟩

theorem Run.ite_false {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_false hb hbs⟩

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

namespace RunStep

theorem eval_lit (B n:ℕ) (σ:Env) (h:n < B):
    (Expr.lit n).evalB B σ=some n:=evalB_lit h

theorem eval_var (B:ℕ) (σ:Env) (x:String) (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=evalB_var h

theorem eval_get (B:ℕ) (σ:Env) (a:String) (i:Expr) (k:ℕ)
    (hi:i.evalB B σ=some k) (hk:k < (σ.arrs a).length)
    (h:(σ.arrs a).getD k 0 < B):
    (Expr.get a i).evalB B σ=some ((σ.arrs a).getD k 0):=by
  refine evalB_get hi ?_ h
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
  rfl

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_sub (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m - n < B):
    (Expr.bin .sub e f).evalB B σ=some (m - n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem cond_eq_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m=n):
    (Cond.eq e f).evalB B σ=some true:=by
  rw [evalB_condEq he hf,h]; simp

theorem cond_eq_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m=n):
    (Cond.eq e f).evalB B σ=some false:=by
  rw [evalB_condEq he hf]; simp [h]

theorem cond_lt_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m < n):
    (Cond.lt e f).evalB B σ=some true:=by
  rw [evalB_condLt he hf]; simp [h]

theorem cond_lt_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m < n):
    (Cond.lt e f).evalB B σ=some false:=by
  rw [evalB_condLt he hf]; simp [h]

theorem skip (B:ℕ) (σ:Env):Run B .skip σ σ 1:=Run.skip

theorem assign (B:ℕ) (σ:Env) (x:String) (e:Expr) (v:ℕ)
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=Run.assign h

theorem store (B:ℕ) (σ:Env) (a:String) (i e:Expr) (idx v:ℕ)
    (hi:i.evalB B σ=some idx) (he:e.evalB B σ=some v)
    (hidx:idx < (σ.arrs a).length):
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size):=Run.store hi he hidx

theorem read (B:ℕ) (σ:Env) (x:String) (h:σ.inp ≠ []):
    Run B (.read x) σ { σ.setVar x (σ.inp.headD 0) with inp:=σ.inp.tail } 1:=by
  refine Run.read (v:=σ.inp.headD 0) (rest:=σ.inp.tail) ?_
  cases hl:σ.inp with
  | nil => exact absurd hl h
  | cons v rest => simp

theorem write (B:ℕ) (σ:Env) (e:Expr) (v:ℕ) (h:e.evalB B σ=some v):
    Run B (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size):=Run.write h

theorem seq (B:ℕ) (c d:Com) (σ σ' σ'':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):
    Run B (.seq c d) σ σ'' (K + K'):=h.seq h'

theorem ite_true (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_true hb h

theorem ite_false (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_false hb h

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

end RunStep

end Lax808846Proofs.Reasoning
end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeBlowUp

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm

theorem flattened_coordinate {α:Type*} (xs:List (List α)) (i:ℕ) (hi:i< xs.length)
    (j:ℕ) (hj:j< xs[i].length):
    xs.flatten[((xs.take i).map List.length).sum+j]?=some xs[i][j]:=by
  have he:xs=xs.take i++xs[i]::xs.drop (i+1):=by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hf:xs.flatten=(xs.take i).flatten++xs[i]++(xs.drop (i+1)).flatten:=by
    conv_lhs => rw [he]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
  rw [hf,List.append_assoc]
  rw [List.getElem?_append_right (by rw [List.length_flatten]; omega)]
  rw [List.length_flatten]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

open Lax109476Proofs

end Lax263307Proofs.NativeBlowUp

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCombinations

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

theorem table_length (n k:ℕ):(table n k).length=(n+1)*(k+1):=by
  simp [table,List.length_flatten,List.map_ofFn,List.sum_ofFn,Finset.sum_const]
  ring

theorem table_coordinate (n k i j:ℕ) (hi:i≤ n) (hj:j≤ k):
    (table n k)[i*(k+1)+j]?=some (i.choose j):=by
  let xs:=List.ofFn fun i:Fin (n+1) => List.ofFn fun j:Fin (k+1) => i.val.choose j.val
  have hi':i< xs.length:=by simp only [xs,List.length_ofFn]; omega
  have hj':j< xs[i].length:=by simp only [xs,List.getElem_ofFn,List.length_ofFn]; omega
  have hh:=NativeBlowUp.flattened_coordinate xs i hi' j hj'
  have hm:xs.map List.length=List.replicate (n+1) (k+1):=by
    dsimp only [xs]
    rw [List.map_ofFn,←List.ofFn_const]
    congr 1
    funext i
    exact List.length_ofFn
  have hp:((xs.take i).map List.length).sum=i*(k+1):=by
    rw [List.map_take,hm]
    simp [List.take_replicate,List.sum_replicate,Nat.min_eq_left (by omega:i≤ n+1)]
  simpa only [table,xs,hp,List.getElem_ofFn] using hh

theorem subset_entry_spec (B n k i need rank:ℕ) (hi:i< n) (hneed:need≤ k)
    (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
      σ.vars "subset.i"=i∧ σ.vars "subset.need"=need∧ σ.vars "subset.rank"=rank∧
      Prefix (table n k) "choose.table" σ) subsetEntry
      (fun _ τ => τ.vars "subset.bit"=(advance (n-i) need rank).1∧
        τ.vars "subset.need"=(advance (n-i) need rank).2.1∧
        τ.vars "subset.rank"=(advance (n-i) need rank).2.2) 40:=by
  rintro σ ⟨hn,hcols,hiσ,hneedσ,hrankσ,hprefix⟩
  have hrow:n-i-1≤ n:=by omega
  have hidx:(n-i-1)*(k+1)+need<(table n k).length:=by
    rw [table_length]
    nlinarith only [hrow,hneed]
  have hc:=table_coordinate n k (n-i-1) need hrow hneed
  have hp:=hprefix ((n-i-1)*(k+1)+need) hidx
  rw [List.getElem?_eq_getElem hidx] at hc
  have hget:=hp.trans hc
  have hroom:(n-i-1)*(k+1)+need<(σ.arrs "choose.table").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    contradiction
  have htableB:(table n k).length< B:=by rw [table_length]; omega
  have hidxB:=hidx.trans htableB
  have hmul:(n-i-1)*(k+1)< B:=by omega
  have hcB:=hcoeff (n-i-1) hrow need hneed
  by_cases hneed0:need=0
  · subst need
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c3:Prod Nat (Prod Nat Nat):=advance (c2 n i) (Env.vars σ "subset.need") rank; let c4:Nat:= @Prod.fst Nat (Prod Nat Nat) c3; let c5:Prod Nat Nat:= @Prod.snd Nat (Prod Nat Nat) c3; let c6:Nat:= @Prod.fst Nat Nat c5; let c7:Nat:= @Prod.snd Nat Nat c5; let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "subset.bit") c4) (And (@Eq Nat (Env.vars τ "subset.need") c6) (@Eq Nat (Env.vars τ "subset.rank") c7))) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (c8 σ'); let c10:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c17:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c18:Expr:=Expr.mul c17 (Expr.var "choose.cols"); let c19:Expr:=Expr.add c18 (Expr.var "subset.need"); let c20:Expr:=Expr.get "choose.table" c19; let c21:Com:=Com.assign "subset.count" c20; let c22:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c23:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c24:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c25:Com:=Com.assign "subset.need" c24; let c26:Com:=Com.seq c23 c25; let c27:Com:=Com.seq c22 c26; let c28:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27; let c29:Com:=Com.seq c21 c28; let c30:String→ Nat:=Env.vars c10; let c31:Nat:=c2 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c32:Nat:=c2 c31 ((1:Nat)); let c33:Nat:=Nat.mul c32 (Env.vars σ "choose.cols"); let c34:Nat:=c11 c33 (Env.vars σ "subset.need"); let c35:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c34 ((0:Nat)); let c36:Env:=Env.setVar σ "subset.count" c35; let c37:String→ Nat:=Env.vars c36; let c38:Nat:=c37 "subset.rank"; let c39:Nat:=c37 "subset.count"; let c40:Prop:=Nat.lt c38 c39; let c41:Prop:=Not c40; let c42:Nat→ Env:=Env.setVar c36 "subset.bit"; let c43:Env:=c42 ((0:Nat)); let c44:Nat:=c12 (Expr.size c20); let c45:Nat→ Nat:=c11 c44; let c46:Nat→ Nat:=c11 (c12 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c47:Nat:=c46 c15; let c48:Nat:=c45 c47; let c49:String→ Nat:=Env.vars c43; let c50:Env:=c42 ((1:Nat)); let c51:String→ Nat:=Env.vars c50; let c52:Nat:=c51 "subset.rank"; let c53:Nat:=c51 "subset.count"; let c54:Nat:=c2 c52 c53; let c55:Env:=Env.setVar c50 "subset.rank" c54; let c56:Nat:=Env.vars c55 "subset.need"; let c57:Nat:=c2 c56 ((1:Nat)); let c58:Env:=Env.setVar c55 "subset.need" c57; let c59:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c60:Nat:=c12 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c61:Nat:=c12 (Expr.size c24); let c62:Nat:=c11 c60 c61; let c63:Nat:=c11 c59 c62; let c64:Nat:=c46 c63; let c65:Nat:=c45 c64; let c66:String→ Nat:=Env.vars c58; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c9) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c9 c10 (@And.intro (Run B subsetEntry σ c10 ((40:Nat))) (c8 c10) (RunStep.mono B subsetEntry σ c10 (c14 c15) ((40:Nat)) (RunStep.ite_true B c13 c16 c29 σ c10 c15 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_2)))) (?nAX_g7928_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c40 c41 (fun (x:Or c40 c41) => @Exists Env c9) (Classical.em c40) (fun (hcase_1:c40) => @Exists.intro Env c9 c43 (@And.intro (Run B subsetEntry σ c43 ((40:Nat))) (c8 c43) (RunStep.mono B subsetEntry σ c43 (c14 c48) ((40:Nat)) (RunStep.ite_false B c13 c16 c29 σ c43 c48 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_5)) hcase) (RunStep.seq B c21 c28 σ c36 c43 c44 c47 (RunStep.assign B σ "subset.count" c20 c35 (RunStep.eval_get B σ "choose.table" c19 c34 (RunStep.eval_add B σ c18 (Expr.var "subset.need") c33 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c17 (Expr.var "choose.cols") c32 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c31 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_0_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_0_0_7)) (?nAX_g7928_0_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_0_0_9)) (?nAX_g7928_0_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_0_0_11)) (?nAX_g7928_0_0_12)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_13)) (?nAX_g7928_0_0_14)) (?nAX_g7928_0_0_15) (?nAX_g7928_0_0_16))) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27 c36 c43 c15 (RunStep.cond_lt_true B c36 (Expr.var "subset.rank") (Expr.var "subset.count") c38 c39 (RunStep.eval_var B c36 "subset.rank" (?nAX_g7928_0_0_17)) (RunStep.eval_var B c36 "subset.count" (?nAX_g7928_0_0_18)) hcase_1) (RunStep.assign B c36 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c36 (?nAX_g7928_0_0_19)))))) (?nAX_g7928_0_0_20)) ?_)) fun (hcase_1:c41) => @Exists.intro Env c9 c58 (@And.intro (Run B subsetEntry σ c58 ((40:Nat))) (c8 c58) (RunStep.mono B subsetEntry σ c58 (c14 c65) ((40:Nat)) (RunStep.ite_false B c13 c16 c29 σ c58 c65 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_21)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_22)) hcase) (RunStep.seq B c21 c28 σ c36 c58 c44 c64 (RunStep.assign B σ "subset.count" c20 c35 (RunStep.eval_get B σ "choose.table" c19 c34 (RunStep.eval_add B σ c18 (Expr.var "subset.need") c33 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c17 (Expr.var "choose.cols") c32 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c31 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_0_0_23)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_0_0_24)) (?nAX_g7928_0_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_0_0_26)) (?nAX_g7928_0_0_27)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_0_0_28)) (?nAX_g7928_0_0_29)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_30)) (?nAX_g7928_0_0_31)) (?nAX_g7928_0_0_32) (?nAX_g7928_0_0_33))) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27 c36 c58 c63 (RunStep.cond_lt_false B c36 (Expr.var "subset.rank") (Expr.var "subset.count") c38 c39 (RunStep.eval_var B c36 "subset.rank" (?nAX_g7928_0_0_34)) (RunStep.eval_var B c36 "subset.count" (?nAX_g7928_0_0_35)) hcase_1) (RunStep.seq B c22 c26 c36 c50 c58 c59 c62 (RunStep.assign B c36 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c36 (?nAX_g7928_0_0_36))) (RunStep.seq B c23 c25 c50 c55 c58 c60 c61 (RunStep.assign B c50 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c54 (RunStep.eval_sub B c50 (Expr.var "subset.rank") (Expr.var "subset.count") c52 c53 (RunStep.eval_var B c50 "subset.rank" (?nAX_g7928_0_0_37)) (RunStep.eval_var B c50 "subset.count" (?nAX_g7928_0_0_38)) (?nAX_g7928_0_0_39))) (RunStep.assign B c55 "subset.need" c24 c57 (RunStep.eval_sub B c55 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c56 ((1:Nat)) (RunStep.eval_var B c55 "subset.need" (?nAX_g7928_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c55 (?nAX_g7928_0_0_41)) (?nAX_g7928_0_0_42)))))))) (?nAX_g7928_0_0_43)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,advance]
  · by_cases hsmall:rank<(n-i-1).choose need
    · have ha:advance (n-i) need rank=(0,need,rank):=by simp [advance,hneed0,hsmall]
      simp only [ha]
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (And (@Eq Nat (Env.vars σ' "subset.bit") ((0:Nat))) (And (@Eq Nat (Env.vars σ' "subset.need") need) (@Eq Nat (Env.vars σ' "subset.rank") rank))); let c3:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c4:String→ Nat:=Env.vars c3; let c5:Prop:=And (@Eq Nat (c4 "subset.bit") ((0:Nat))) (And (@Eq Nat (c4 "subset.need") need) (@Eq Nat (c4 "subset.rank") rank)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c12:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c13:Expr:=Expr.mul c12 (Expr.var "choose.cols"); let c14:Expr:=Expr.add c13 (Expr.var "subset.need"); let c15:Expr:=Expr.get "choose.table" c14; let c16:Com:=Com.assign "subset.count" c15; let c17:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c18:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c19:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c20:Com:=Com.assign "subset.need" c19; let c21:Com:=Com.seq c18 c20; let c22:Com:=Com.seq c17 c21; let c23:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22; let c24:Com:=Com.seq c16 c23; let c25:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c26:Nat:=c25 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c27:Nat:=c25 c26 ((1:Nat)); let c28:Nat:=Nat.mul c27 (Env.vars σ "choose.cols"); let c29:Nat:=c6 c28 (Env.vars σ "subset.need"); let c30:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c29 ((0:Nat)); let c31:Env:=Env.setVar σ "subset.count" c30; let c32:String→ Nat:=Env.vars c31; let c33:Nat:=c32 "subset.rank"; let c34:Nat:=c32 "subset.count"; let c35:Prop:=Nat.lt c33 c34; let c36:Prop:=Not c35; let c37:Nat→ Env:=Env.setVar c31 "subset.bit"; let c38:Env:=c37 ((0:Nat)); let c39:String→ Nat:=Env.vars c38; let c40:Prop:=And (@Eq Nat (c39 "subset.bit") ((0:Nat))) (And (@Eq Nat (c39 "subset.need") need) (@Eq Nat (c39 "subset.rank") rank)); let c41:Nat:=c7 (Expr.size c15); let c42:Nat→ Nat:=c6 c41; let c43:Nat→ Nat:=c6 (c7 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c44:Nat:=c43 c10; let c45:Nat:=c42 c44; let c46:Nat→ Prop:=Nat.lt c29; let c47:Env:=c37 ((1:Nat)); let c48:String→ Nat:=Env.vars c47; let c49:Nat:=c48 "subset.rank"; let c50:Nat:=c48 "subset.count"; let c51:Nat:=c25 c49 c50; let c52:Env:=Env.setVar c47 "subset.rank" c51; let c53:Nat:=Env.vars c52 "subset.need"; let c54:Nat:=c25 c53 ((1:Nat)); let c55:Env:=Env.setVar c52 "subset.need" c54; let c56:String→ Nat:=Env.vars c55; let c57:Prop:=And (@Eq Nat (c56 "subset.bit") ((0:Nat))) (And (@Eq Nat (c56 "subset.need") need) (@Eq Nat (c56 "subset.rank") rank)); let c58:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c59:Nat:=c7 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c60:Nat:=c7 (Expr.size c19); let c61:Nat:=c6 c59 c60; let c62:Nat:=c6 c58 c61; let c63:Nat:=c43 c62; let c64:Nat:=c42 c63; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c2) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c2 c3 (@And.intro (Run B subsetEntry σ c3 ((40:Nat))) c5 (RunStep.mono B subsetEntry σ c3 (c9 c10) ((40:Nat)) (RunStep.ite_true B c8 c11 c24 σ c3 c10 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_2)))) (?nAX_g7928_1_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c35 c36 (fun (x:Or c35 c36) => @Exists Env c2) (Classical.em c35) (fun (hcase_1:c35) => @Exists.intro Env c2 c38 (@And.intro (Run B subsetEntry σ c38 ((40:Nat))) c40 (RunStep.mono B subsetEntry σ c38 (c9 c45) ((40:Nat)) (RunStep.ite_false B c8 c11 c24 σ c38 c45 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_5)) hcase) (RunStep.seq B c16 c23 σ c31 c38 c41 c44 (RunStep.assign B σ "subset.count" c15 c30 (RunStep.eval_get B σ "choose.table" c14 c29 (RunStep.eval_add B σ c13 (Expr.var "subset.need") c28 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c12 (Expr.var "choose.cols") c27 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c26 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_1_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_1_0_7)) (?nAX_g7928_1_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_1_0_9)) (?nAX_g7928_1_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_1_0_11)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_12)) ?_) ?_ ?_)) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22 c31 c38 c10 (RunStep.cond_lt_true B c31 (Expr.var "subset.rank") (Expr.var "subset.count") c33 c34 (RunStep.eval_var B c31 "subset.rank" (?nAX_g7928_1_0_13)) (RunStep.eval_var B c31 "subset.count" ?_) hcase_1) (RunStep.assign B c31 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c31 (?nAX_g7928_1_0_14)))))) (?nAX_g7928_1_0_15)) ?_)) fun (hcase_1:c36) => @Exists.intro Env c2 c55 (@And.intro (Run B subsetEntry σ c55 ((40:Nat))) c57 (RunStep.mono B subsetEntry σ c55 (c9 c64) ((40:Nat)) (RunStep.ite_false B c8 c11 c24 σ c55 c64 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_16)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_17)) hcase) (RunStep.seq B c16 c23 σ c31 c55 c41 c63 (RunStep.assign B σ "subset.count" c15 c30 (RunStep.eval_get B σ "choose.table" c14 c29 (RunStep.eval_add B σ c13 (Expr.var "subset.need") c28 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c12 (Expr.var "choose.cols") c27 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c26 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_1_0_18)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_1_0_19)) (?nAX_g7928_1_0_20)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_1_0_21)) (?nAX_g7928_1_0_22)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_1_0_23)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_24)) ?_) ?_ ?_)) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22 c31 c55 c62 (RunStep.cond_lt_false B c31 (Expr.var "subset.rank") (Expr.var "subset.count") c33 c34 (RunStep.eval_var B c31 "subset.rank" (?nAX_g7928_1_0_25)) (RunStep.eval_var B c31 "subset.count" ?_) hcase_1) (RunStep.seq B c17 c21 c31 c47 c55 c58 c61 (RunStep.assign B c31 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c31 (?nAX_g7928_1_0_26))) (RunStep.seq B c18 c20 c47 c52 c55 c59 c60 (RunStep.assign B c47 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c51 (RunStep.eval_sub B c47 (Expr.var "subset.rank") (Expr.var "subset.count") c49 c50 (RunStep.eval_var B c47 "subset.rank" (?nAX_g7928_1_0_27)) (RunStep.eval_var B c47 "subset.count" ?_) (?nAX_g7928_1_0_28))) (RunStep.assign B c52 "subset.need" c19 c54 (RunStep.eval_sub B c52 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c53 ((1:Nat)) (RunStep.eval_var B c52 "subset.need" (?nAX_g7928_1_0_29)) (RunStep.eval_lit B ((1:Nat)) c52 (?nAX_g7928_1_0_30)) (?nAX_g7928_1_0_31)))))))) (?nAX_g7928_1_0_32)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar,advance]
    · have ha:advance (n-i) need rank=(1,need-1,rank-(n-i-1).choose need):=by simp [advance,hneed0,hsmall]
      simp only [ha]
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c3:Nat:=c2 need ((1:Nat)); let c4:Nat:=c2 rank (Nat.choose (c2 (c2 n i) ((1:Nat))) need); let c5:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (And (@Eq Nat (Env.vars σ' "subset.bit") ((1:Nat))) (And (@Eq Nat (Env.vars σ' "subset.need") c3) (@Eq Nat (Env.vars σ' "subset.rank") c4))); let c6:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c7:String→ Nat:=Env.vars c6; let c8:Prop:=And (@Eq Nat (c7 "subset.bit") ((1:Nat))) (And (@Eq Nat (c7 "subset.need") c3) (@Eq Nat (c7 "subset.rank") c4)); let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c12:Nat→ Nat:=c9 (c10 (Cond.size c11)); let c13:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); let c14:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c15:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c16:Expr:=Expr.mul c15 (Expr.var "choose.cols"); let c17:Expr:=Expr.add c16 (Expr.var "subset.need"); let c18:Expr:=Expr.get "choose.table" c17; let c19:Com:=Com.assign "subset.count" c18; let c20:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c21:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c22:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c23:Com:=Com.assign "subset.need" c22; let c24:Com:=Com.seq c21 c23; let c25:Com:=Com.seq c20 c24; let c26:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25; let c27:Com:=Com.seq c19 c26; let c28:Nat:=c2 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c29:Nat:=c2 c28 ((1:Nat)); let c30:Nat:=Nat.mul c29 (Env.vars σ "choose.cols"); let c31:Nat:=c9 c30 (Env.vars σ "subset.need"); let c32:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c31 ((0:Nat)); let c33:Env:=Env.setVar σ "subset.count" c32; let c34:String→ Nat:=Env.vars c33; let c35:Nat:=c34 "subset.rank"; let c36:Nat:=c34 "subset.count"; let c37:Prop:=Nat.lt c35 c36; let c38:Prop:=Not c37; let c39:Nat→ Env:=Env.setVar c33 "subset.bit"; let c40:Env:=c39 ((0:Nat)); let c41:String→ Nat:=Env.vars c40; let c42:Prop:=And (@Eq Nat (c41 "subset.bit") ((1:Nat))) (And (@Eq Nat (c41 "subset.need") c3) (@Eq Nat (c41 "subset.rank") c4)); let c43:Nat:=c10 (Expr.size c18); let c44:Nat→ Nat:=c9 c43; let c45:Nat→ Nat:=c9 (c10 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c46:Nat:=c45 c13; let c47:Nat:=c44 c46; let c48:Nat→ Prop:=Nat.lt c31; let c49:Env:=c39 ((1:Nat)); let c50:String→ Nat:=Env.vars c49; let c51:Nat:=c50 "subset.rank"; let c52:Nat:=c50 "subset.count"; let c53:Nat:=c2 c51 c52; let c54:Env:=Env.setVar c49 "subset.rank" c53; let c55:Nat:=Env.vars c54 "subset.need"; let c56:Nat:=c2 c55 ((1:Nat)); let c57:Env:=Env.setVar c54 "subset.need" c56; let c58:String→ Nat:=Env.vars c57; let c59:Prop:=And (@Eq Nat (c58 "subset.bit") ((1:Nat))) (And (@Eq Nat (c58 "subset.need") c3) (@Eq Nat (c58 "subset.rank") c4)); let c60:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c61:Nat:=c10 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c62:Nat:=c10 (Expr.size c22); let c63:Nat:=c9 c61 c62; let c64:Nat:=c9 c60 c63; let c65:Nat:=c45 c64; let c66:Nat:=c44 c65; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c5 c6 (@And.intro (Run B subsetEntry σ c6 ((40:Nat))) c8 (RunStep.mono B subsetEntry σ c6 (c12 c13) ((40:Nat)) (RunStep.ite_true B c11 c14 c27 σ c6 c13 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_2)))) (?nAX_g7928_2_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c37 c38 (fun (x:Or c37 c38) => @Exists Env c5) (Classical.em c37) (fun (hcase_1:c37) => @Exists.intro Env c5 c40 (@And.intro (Run B subsetEntry σ c40 ((40:Nat))) c42 (RunStep.mono B subsetEntry σ c40 (c12 c47) ((40:Nat)) (RunStep.ite_false B c11 c14 c27 σ c40 c47 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_5)) hcase) (RunStep.seq B c19 c26 σ c33 c40 c43 c46 (RunStep.assign B σ "subset.count" c18 c32 (RunStep.eval_get B σ "choose.table" c17 c31 (RunStep.eval_add B σ c16 (Expr.var "subset.need") c30 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c15 (Expr.var "choose.cols") c29 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c28 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_2_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_2_0_7)) (?nAX_g7928_2_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_2_0_9)) (?nAX_g7928_2_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_2_0_11)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_12)) ?_) ?_ ?_)) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25 c33 c40 c13 (RunStep.cond_lt_true B c33 (Expr.var "subset.rank") (Expr.var "subset.count") c35 c36 (RunStep.eval_var B c33 "subset.rank" (?nAX_g7928_2_0_13)) (RunStep.eval_var B c33 "subset.count" ?_) hcase_1) (RunStep.assign B c33 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c33 (?nAX_g7928_2_0_14)))))) (?nAX_g7928_2_0_15)) ?_)) fun (hcase_1:c38) => @Exists.intro Env c5 c57 (@And.intro (Run B subsetEntry σ c57 ((40:Nat))) c59 (RunStep.mono B subsetEntry σ c57 (c12 c66) ((40:Nat)) (RunStep.ite_false B c11 c14 c27 σ c57 c66 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_16)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_17)) hcase) (RunStep.seq B c19 c26 σ c33 c57 c43 c65 (RunStep.assign B σ "subset.count" c18 c32 (RunStep.eval_get B σ "choose.table" c17 c31 (RunStep.eval_add B σ c16 (Expr.var "subset.need") c30 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c15 (Expr.var "choose.cols") c29 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c28 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_2_0_18)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_2_0_19)) (?nAX_g7928_2_0_20)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_2_0_21)) (?nAX_g7928_2_0_22)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_2_0_23)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_24)) ?_) ?_ ?_)) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25 c33 c57 c64 (RunStep.cond_lt_false B c33 (Expr.var "subset.rank") (Expr.var "subset.count") c35 c36 (RunStep.eval_var B c33 "subset.rank" (?nAX_g7928_2_0_25)) (RunStep.eval_var B c33 "subset.count" ?_) hcase_1) (RunStep.seq B c20 c24 c33 c49 c57 c60 c63 (RunStep.assign B c33 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g7928_2_0_26))) (RunStep.seq B c21 c23 c49 c54 c57 c61 c62 (RunStep.assign B c49 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c53 (RunStep.eval_sub B c49 (Expr.var "subset.rank") (Expr.var "subset.count") c51 c52 (RunStep.eval_var B c49 "subset.rank" (?nAX_g7928_2_0_27)) (RunStep.eval_var B c49 "subset.count" ?_) (?nAX_g7928_2_0_28))) (RunStep.assign B c54 "subset.need" c22 c56 (RunStep.eval_sub B c54 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c55 ((1:Nat)) (RunStep.eval_var B c54 "subset.need" (?nAX_g7928_2_0_29)) (RunStep.eval_lit B ((1:Nat)) c54 (?nAX_g7928_2_0_30)) (?nAX_g7928_2_0_31)))))))) (?nAX_g7928_2_0_32)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar,advance]
      all_goals omega

end Lax263307Proofs.NativeCombinations

end

theorem solution:∀ (B n k i need rank:Nat),
  Nat.lt i n→
    Nat.le need k→
      Nat.lt
          (Nat.add
            (Nat.add
              (Nat.add
                (Nat.mul
                  (Nat.add n
                    ((1:Nat)))
                  (Nat.add k
                    ((1:Nat))))
                n)
              k)
            ((3:Nat)))
          B→
        Nat.lt rank B→
          (∀ (i:Nat),
              Nat.le i n→ ∀ (j:Nat),Nat.le j k→ Nat.lt (i.choose j) B)→
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ:Lax808846Proofs.Imp.Env) =>
                And (@Eq Nat (σ.vars "choose.n") n)
                  (And
                    (@Eq Nat (σ.vars "choose.cols")
                      (Nat.add k
                        ((1:Nat))))
                    (And (@Eq Nat (σ.vars "subset.i") i)
                      (And (@Eq Nat (σ.vars "subset.need") need)
                        (And (@Eq Nat (σ.vars "subset.rank") rank)
                          (Lax455465Proofs.RamVirtualState.Prefix (Lax263307Proofs.NativeCombinations.table n k)
                            "choose.table" σ))))))
              Lax263307Proofs.NativeCombinations.subsetEntry
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And
                  (@Eq Nat (τ.vars "subset.bit")
                    (@Prod.fst Nat (Prod Nat Nat)
                      (Lax263307Proofs.NativeCombinations.advance
                        (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n i) need rank)))
                  (And
                    (@Eq Nat (τ.vars "subset.need")
                      (@Prod.fst Nat Nat
                        (@Prod.snd Nat (Prod Nat Nat)
                          (Lax263307Proofs.NativeCombinations.advance
                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n i) need rank))))
                    (@Eq Nat (τ.vars "subset.rank")
                      (@Prod.snd Nat Nat
                        (@Prod.snd Nat (Prod Nat Nat)
                          (Lax263307Proofs.NativeCombinations.advance
                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n i) need rank))))))
              ((40:Nat)):= @Lax263307Proofs.NativeCombinations.subset_entry_spec
