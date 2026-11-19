-- Prove2me | solution 1 for Lax263307Proofs.NativeCombinations.entry_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:41.561307+00:00
-- url     : https://prove2.me/submissions/de9f037d-2a35-4504-b7b0-199149a09310

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

theorem entry_spec (B n k i j:ℕ) (hi:i≤ n) (hj:j≤ k)
    (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.row"=i∧ σ.vars "choose.col"=j∧ σ.vars "choose.cols"=k+1∧
      Prefix ((table n k).take (i*(k+1)+j)) "choose.table" σ) entry
      (fun _ τ => τ.vars "choose.value"=i.choose j) 30:=by
  rintro σ ⟨hrow,hcol,hcols,hprefix⟩
  have hzero:0< B:=by omega
  have hone:1< B:=by omega
  have hiB:i< B:=by omega
  have hjB:j< B:=by omega
  have hkB:k+1< B:=by omega
  by_cases hj0:j=0
  · subst j
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose i (Env.vars σ "choose.col"))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:Nat→ Nat→ Nat:= @List.getD Nat (Env.arrs c33 "choose.table"); let c35:String→ Nat:=Env.vars c33; let c36:Nat:=c35 "choose.prev"; let c37:Nat→ Nat:=c5 c36; let c38:Nat:=c35 "choose.col"; let c39:Nat:=c30 c38 ((1:Nat)); let c40:Nat:=c37 c39; let c41:Nat:=c34 c40 ((0:Nat)); let c42:Nat:=c37 c38; let c43:Nat:=c34 c42 ((0:Nat)); let c44:Nat:=c5 c41 c43; let c45:Env:=Env.setVar c33 "choose.value" c44; let c46:Nat:=c6 (Expr.size c14); let c47:Nat:=c6 (Expr.size c20); let c48:Nat:=c5 c46 c47; let c49:Nat:=c27 c48; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_0_0_0)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_0_0_2)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c45 (@And.intro (Run B entry σ c45 ((30:Nat))) (c2 c45) (RunStep.mono B entry σ c45 (c8 c49) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c45 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c45 c48 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c45 c46 c47 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_4)) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_0_0_5)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_0_0_6)) (?nAX_g7914_0_0_7))) (RunStep.assign B c33 "choose.value" c20 c44 (RunStep.eval_add B c33 c18 c19 c41 c43 (RunStep.eval_get B c33 "choose.table" c17 c40 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c36 c39 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_0_0_8)) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c38 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_0_0_9)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_0_0_10)) (?nAX_g7914_0_0_11)) (?nAX_g7914_0_0_12) (?nAX_g7914_0_0_13)) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c42 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c36 c38 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_0_0_14)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_0_0_15)) (?nAX_g7914_0_0_16)) (?nAX_g7914_0_0_17) (?nAX_g7914_0_0_18)) (?nAX_g7914_0_0_19)))))) (?nAX_g7914_0_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · by_cases hi0:i=0
    · subst i
      have hchoose:Nat.choose 0 j=0:=Nat.choose_eq_zero_of_lt (by omega)
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose (Env.vars σ "choose.row") j)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:Nat→ Nat→ Nat:= @List.getD Nat (Env.arrs c33 "choose.table"); let c35:String→ Nat:=Env.vars c33; let c36:Nat:=c35 "choose.prev"; let c37:Nat→ Nat:=c5 c36; let c38:Nat:=c35 "choose.col"; let c39:Nat:=c30 c38 ((1:Nat)); let c40:Nat:=c37 c39; let c41:Nat:=c34 c40 ((0:Nat)); let c42:Nat:=c37 c38; let c43:Nat:=c34 c42 ((0:Nat)); let c44:Nat:=c5 c41 c43; let c45:Env:=Env.setVar c33 "choose.value" c44; let c46:Nat:=c6 (Expr.size c14); let c47:Nat:=c6 (Expr.size c20); let c48:Nat:=c5 c46 c47; let c49:Nat:=c27 c48; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_1_0_1)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_2)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_1_0_3)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c45 (@And.intro (Run B entry σ c45 ((30:Nat))) (c2 c45) (RunStep.mono B entry σ c45 (c8 c49) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c45 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_4)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c45 c48 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c45 c46 c47 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_1_0_5)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_1_0_6)) (?nAX_g7914_1_0_7))) (RunStep.assign B c33 "choose.value" c20 c44 (RunStep.eval_add B c33 c18 c19 c41 c43 (RunStep.eval_get B c33 "choose.table" c17 c40 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c36 c39 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_1_0_8)) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c38 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_1_0_9)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_1_0_10)) (?nAX_g7914_1_0_11)) (?nAX_g7914_1_0_12) (?nAX_g7914_1_0_13)) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c42 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c36 c38 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_1_0_14)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_1_0_15)) (?nAX_g7914_1_0_16)) (?nAX_g7914_1_0_17) (?nAX_g7914_1_0_18)) (?nAX_g7914_1_0_19)))))) (?nAX_g7914_1_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar]
    · have hjp:0< j:=by omega
      have hip:0 < i:=by omega
      have hrec:i.choose j=(i-1).choose (j-1)+(i-1).choose j:=by
        obtain ⟨i',rfl⟩:=Nat.exists_eq_succ_of_ne_zero hi0
        obtain ⟨j',rfl⟩:=Nat.exists_eq_succ_of_ne_zero hj0
        simp [Nat.choose_succ_succ]
      have hlast:i*(k+1)+j<(table n k).length:=by rw [table_length]; nlinarith only [hi,hj]
      have hidx0:(i-1)*(k+1)+(j-1)< i*(k+1)+j:=by
        have hsubi:i-1+1=i:=by omega
        have hsubj:j-1+1=j:=by omega
        nlinarith only [hsubi,hsubj]
      have hidx1:(i-1)*(k+1)+j< i*(k+1)+j:=by
        have hsubi:i-1+1=i:=by omega
        nlinarith only [hsubi]
      have get (a b:ℕ) (ha:a≤ n) (hb:b≤ k) (hlt:a*(k+1)+b< i*(k+1)+j):
          (σ.arrs "choose.table")[a*(k+1)+b]?=some (a.choose b):=by
        have hp:=hprefix (a*(k+1)+b) (by rw [List.length_take]; omega)
        rw [List.getElem_take] at hp
        have hc:=table_coordinate n k a b ha hb
        rw [List.getElem?_eq_getElem (hlt.trans hlast)] at hc
        exact hp.trans hc
      have hget0:=get (i-1) (j-1) (by omega) (by omega) hidx0
      have hget1:=get (i-1) j (by omega) hj hidx1
      have hroom0:(i-1)*(k+1)+(j-1)<(σ.arrs "choose.table").length:=by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget0
        contradiction
      have hroom1:(i-1)*(k+1)+j<(σ.arrs "choose.table").length:=by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget1
        contradiction
      have hc0:=hcoeff (i-1) (by omega) (j-1) (by omega)
      have hc1:=hcoeff (i-1) (by omega) j hj
      have hsum:(i-1).choose (j-1)+(i-1).choose j< B:=hrec ▸ hcoeff i hi j hj
      have hdim:(table n k).length< B:=by rw [table_length]; omega
      have hprev:(i-1)*(k+1)< B:=by omega
      have hb0:(i-1)*(k+1)+(j-1)< B:=(hidx0.trans hlast).trans hdim
      have hb1:(i-1)*(k+1)+j< B:=(hidx1.trans hlast).trans hdim
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose i j)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:List Nat:=Env.arrs c33 "choose.table"; let c35:Nat→ Nat→ Nat:= @List.getD Nat c34; let c36:String→ Nat:=Env.vars c33; let c37:Nat:=c36 "choose.prev"; let c38:Nat→ Nat:=c5 c37; let c39:Nat:=c36 "choose.col"; let c40:Nat:=c30 c39 ((1:Nat)); let c41:Nat:=c38 c40; let c42:Nat:=c35 c41 ((0:Nat)); let c43:Nat:=c38 c39; let c44:Nat:=c35 c43 ((0:Nat)); let c45:Nat:=c5 c42 c44; let c46:Env:=Env.setVar c33 "choose.value" c45; let c47:Nat:=c6 (Expr.size c14); let c48:Nat:=c6 (Expr.size c20); let c49:Nat:=c5 c47 c48; let c50:Nat:=c27 c49; let c51:Nat→ Prop:=Nat.lt c41; let c52:Nat:= @List.length Nat c34; let c53:Nat→ Prop:=Nat.lt c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_2_0_1)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_2)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_3)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_2_0_4)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c46 (@And.intro (Run B entry σ c46 ((30:Nat))) (c2 c46) (RunStep.mono B entry σ c46 (c8 c50) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c46 c50 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_5)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c46 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_6)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c46 c47 c48 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_7)) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_2_0_8)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_2_0_9)) ?_)) (RunStep.assign B c33 "choose.value" c20 c45 (RunStep.eval_add B c33 c18 c19 c42 c44 (RunStep.eval_get B c33 "choose.table" c17 c41 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c37 c40 (RunStep.eval_var B c33 "choose.prev" ?_) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c39 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_2_0_10)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_2_0_11)) ?_) ?_ ?_) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c43 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c37 c39 (RunStep.eval_var B c33 "choose.prev" ?_) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_2_0_12)) ?_) ?_ ?_) ?_))))) (?nAX_g7914_2_0_13)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar]

end Lax263307Proofs.NativeCombinations

end

theorem solution:∀ (B n k i j:Nat),
  Nat.le i n→
    Nat.le j k→
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
        (∀ (i:Nat),
            Nat.le i n→ ∀ (j:Nat),Nat.le j k→ Nat.lt (i.choose j) B)→
          Lax808846Proofs.Reasoning.Spec B
            (fun (σ:Lax808846Proofs.Imp.Env) =>
              And (@Eq Nat (σ.vars "choose.row") i)
                (And (@Eq Nat (σ.vars "choose.col") j)
                  (And
                    (@Eq Nat (σ.vars "choose.cols")
                      (Nat.add k
                        ((1:Nat))))
                    (Lax455465Proofs.RamVirtualState.Prefix
                      (@List.take Nat
                        (Nat.add
                          (Nat.mul i
                            (Nat.add k
                              ((1:Nat))))
                          j)
                        (Lax263307Proofs.NativeCombinations.table n k))
                      "choose.table" σ))))
            Lax263307Proofs.NativeCombinations.entry
            (fun (x τ:Lax808846Proofs.Imp.Env) => @Eq Nat (τ.vars "choose.value") (i.choose j))
            ((30:Nat)):= @Lax263307Proofs.NativeCombinations.entry_spec
