-- Prove2me | solution 1 for Lax109476Proofs.RamInitialState.initialState_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:57.165105+00:00
-- url     : https://prove2.me/submissions/7864f9a6-bed6-4678-9daf-57c2ba2b9382

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces

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

def Expr.eval:Expr→ Env→ Option ℕ
  | lit n,_ => some n
  | var x,σ => some (σ.vars x)
  | get a i,σ => (i.eval σ).bind fun k => (σ.arrs a)[k]?
  | bin op e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => op.apply m n

def Cond.eval:Cond→ Env→ Option Bool
  | eq e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => m == n
  | lt e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => decide (m < n)

inductive BigStep:Com→ Env→ Env→ ℕ→ Prop

  | skip {σ:Env}:BigStep .skip σ σ 1

  | assign {σ:Env} {x:String} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.assign x e) σ (σ.setVar x v) (1 + e.size)

  | store {σ:Env} {a:String} {i e:Expr} {k v:ℕ}
      (hi:i.eval σ=some k) (he:e.eval σ=some v)
      (hk:k < (σ.arrs a).length):
      BigStep (.store a i e) σ (σ.setArr a k v) (1 + i.size + e.size)

  | seq {c d:Com} {σ σ' σ'':Env} {k k':ℕ}:
      BigStep c σ σ' k→ BigStep d σ' σ'' k'→
      BigStep (.seq c d) σ σ'' (k + k')

  | ite_true {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | ite_false {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some false) (hd:BigStep d σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | while_true {b:Cond} {c:Com} {σ σ' σ'':Env} {k k':ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k)
      (hw:BigStep (.while b c) σ' σ'' k'):
      BigStep (.while b c) σ σ'' (1 + b.size + k + k')

  | while_false {b:Cond} {c:Com} {σ:Env} (hb:b.eval σ=some false):
      BigStep (.while b c) σ σ (1 + b.size)

  | read {σ:Env} {x:String} {v:ℕ} {rest:List ℕ} (h:σ.inp=v::rest):
      BigStep (.read x) σ { σ.setVar x v with inp:=rest } 1

  | write {σ:Env} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Imp

theorem fit_eq_some {B v u:ℕ}:fit B v=some u↔ u=v∧ v < B:=by
  constructor
  · intro h
    by_cases hv:v < B
    · rw [fit,if_pos hv] at h
      exact ⟨(Option.some.inj h).symm,hv⟩
    · rw [fit,if_neg hv] at h; exact absurd h (by simp)
  · rintro ⟨rfl,h⟩; rw [fit,if_pos h]

theorem fit_self {B v:ℕ} (h:v < B):fit B v=some v:=by rw [fit,if_pos h]

theorem Expr.eval_and_lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):e.eval σ=some v∧ v < B:=by
  induction e generalizing v with
  | lit n =>
      rw [Expr.evalB,fit_eq_some] at h
      obtain ⟨rfl,hn⟩:=h
      exact ⟨rfl,hn⟩
  | var x =>
      rw [Expr.evalB,fit_eq_some] at h
      obtain ⟨rfl,hn⟩:=h
      exact ⟨rfl,hn⟩
  | get a i ih =>
      rw [Expr.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨k,hk,h⟩:=h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨u,hu,h⟩:=h
      rw [fit_eq_some] at h
      obtain ⟨rfl,hlt⟩:=h
      exact ⟨by rw [Expr.eval, (ih hk).1]; exact hu,hlt⟩
  | bin op e f ihe ihf =>
      rw [Expr.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨n,hn,h⟩:=h
      rw [fit_eq_some] at h
      obtain ⟨rfl,hlt⟩:=h
      exact ⟨by rw [Expr.eval, (ihe hm).1, (ihf hn).1]; rfl,hlt⟩

theorem Expr.eval_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):e.eval σ=some v:=(eval_and_lt_of_evalB h).1

theorem Cond.eval_of_evalB {B:ℕ} {σ:Env} {b:Cond} {r:Bool}
    (h:b.evalB B σ=some r):b.eval σ=some r:=by
  cases b with
  | eq e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      rw [Cond.eval,Expr.eval_of_evalB hm,Expr.eval_of_evalB hn]; rfl
  | lt e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      rw [Cond.eval,Expr.eval_of_evalB hm,Expr.eval_of_evalB hn]; rfl

theorem BigStepB.bigStep {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStepB B c σ σ' k):BigStep c σ σ' k:=by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (Expr.eval_of_evalB h)
  | store hi he hk => exact .store (Expr.eval_of_evalB hi) (Expr.eval_of_evalB he) hk
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true hb _ ih => exact .ite_true (Cond.eval_of_evalB hb) ih
  | ite_false hb _ ih => exact .ite_false (Cond.eval_of_evalB hb) ih
  | while_true hb _ _ ih ih' => exact .while_true (Cond.eval_of_evalB hb) ih ih'
  | while_false hb => exact .while_false (Cond.eval_of_evalB hb)
  | read h => exact .read h
  | write h => exact .write (Expr.eval_of_evalB h)

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

@[simp] theorem length_arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    ((σ.setArr a i v).arrs b).length=(σ.arrs b).length:=by
  rw [arrs_setArr]; split
  · subst_vars; exact List.length_set ..
  · rfl

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

@[simp] theorem length_arrOf (n:ℕ) (f:ℕ→ ℕ):(arrOf n f).length=n:=by
  simp [arrOf]

theorem replicate_eq_arrOf (n v:ℕ):List.replicate n v=arrOf n (fun _ => v):=by
  simp [arrOf,List.map_const']

theorem arrOf_congr {n:ℕ} {f g:ℕ→ ℕ} (h:∀ i < n,f i=g i):
    arrOf n f=arrOf n g:=by
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp only [arrOf,List.length_map,List.length_range] at h₁
  simp [arrOf,h k h₁]

theorem set_arrOf {n i:ℕ} (f:ℕ→ ℕ) (v:ℕ):
    (arrOf n f).set i v=arrOf n (fun k => if k=i then v else f k):=by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set]
  by_cases hk:k=i
  · subst hk; simp [arrOf]
  · simp [arrOf,hk,Ne.symm hk]

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

@[simp] theorem evalB_condLt_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.lt e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=decide (m < n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

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

theorem evalB_condLt_vars {B:ℕ} {x y:String} {σ:Env}
    (hx:σ.vars x < B) (hy:σ.vars y < B):
    ∃ v, (Cond.lt (.var x) (.var y)).evalB B σ=some v:=
  ⟨_,evalB_condLt (evalB_var hx) (evalB_var hy)⟩

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

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

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

theorem Run.while_false {B:ℕ} {b:Cond} {c:Com} {σ:Env}
    (hb:b.evalB B σ=some false):Run B (.while b c) σ σ (1 + b.size):=
  .of_bigStepB (.while_false hb)

theorem Run.while_potential {B:ℕ} {b:Cond} {c:Com} (I:Env→ Prop) (Φ:Env→ ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hstep:∀ σ,I σ→ b.evalB B σ=some true→
      ∃ σ' K,Run B c σ σ' K∧ I σ'∧ 1 + b.size + K + Φ σ'≤ Φ σ)
    {σ:Env} (hI:I σ):
    ∃ σ' K,Run B (.while b c) σ σ' K∧ I σ'∧ b.evalB B σ'=some false∧
      K + Φ σ'≤ Φ σ + 1 + b.size:=by
  suffices H:∀ n σ,I σ→ Φ σ≤ n→
      ∃ σ' K,Run B (.while b c) σ σ' K∧ I σ'∧ b.evalB B σ'=some false∧
        K + Φ σ'≤ Φ σ + 1 + b.size from H (Φ σ) σ hI le_rfl
  clear hI σ
  intro n
  induction n with
  | zero =>
      intro σ hI hΦ
      obtain ⟨v,hv⟩:=hdef σ hI
      cases v with
      | false => exact ⟨σ,_,Run.while_false hv,hI,hv,by omega⟩
      | true =>
          obtain ⟨σ₁,K,hrun,_,hpay⟩:=hstep σ hI hv
          omega
  | succ n ih =>
      intro σ hI hΦ
      obtain ⟨v,hv⟩:=hdef σ hI
      cases v with
      | false => exact ⟨σ,_,Run.while_false hv,hI,hv,by omega⟩
      | true =>
          obtain ⟨σ₁,K,hrun,hI₁,hpay⟩:=hstep σ hI hv
          obtain ⟨σ',K',hrun',hI',hfalse,hpay'⟩:=ih σ₁ hI₁ (by omega)
          obtain ⟨k,hk,hbs⟩:=hrun
          obtain ⟨k',hk',hbs'⟩:=hrun'
          exact ⟨σ',1 + b.size + k + k', ⟨1 + b.size + k + k',le_rfl,
            .while_true hv hbs hbs'⟩,hI',hfalse,by omega⟩

theorem _root_.Lax808846Proofs.Imp.BigStep.out_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k):c.NoWrite→ σ'.out=σ.out:=by
  induction h with
  | skip => intro _; rfl
  | assign _ => intro _; rfl
  | store _ _ _ => intro _; rfl
  | seq _ _ ih ih' => intro hc; rw [ih' hc.2,ih hc.1]
  | ite_true _ _ ih => intro hc; exact ih hc.1
  | ite_false _ _ ih => intro hc; exact ih hc.2
  | while_true _ _ _ ih ih' => intro hc; rw [ih' hc,ih hc]
  | while_false _ => intro _; rfl
  | read _ => intro _; rfl
  | write _ => intro hc; exact absurd hc not_false

theorem Run.out_eq {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hc:c.NoWrite):σ'.out=σ.out:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.out_eq hc

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Imp

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

end Lax808846Proofs.Imp

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

theorem _root_.Lax808846Proofs.Imp.BigStep.vars_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) {y:String} (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  induction h with
  | skip => rfl
  | assign _ => simp only [Com.wvars,List.mem_singleton] at hy; simp [Env.setVar,hy]
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.wvars,List.mem_append,not_or] at hy
      rw [ih' hy.2,ih hy.1]
  | ite_true _ _ ih => simp only [Com.wvars,List.mem_append,not_or] at hy; exact ih hy.1
  | ite_false _ _ ih => simp only [Com.wvars,List.mem_append,not_or] at hy; exact ih hy.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.wvars] at hy
      rw [ih' (by simpa [Com.wvars] using hy),ih hy]
  | while_false _ => rfl
  | read _ => simp only [Com.wvars,List.mem_singleton] at hy; simp [Env.setVar,hy]
  | write _ => rfl

theorem _root_.Lax808846Proofs.Imp.BigStep.arrs_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) {a:String} (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [Com.warrs,List.mem_singleton] at ha; simp [Env.setArr,ha]
  | seq _ _ ih ih' =>
      simp only [Com.warrs,List.mem_append,not_or] at ha
      rw [ih' ha.2,ih ha.1]
  | ite_true _ _ ih => simp only [Com.warrs,List.mem_append,not_or] at ha; exact ih ha.1
  | ite_false _ _ ih => simp only [Com.warrs,List.mem_append,not_or] at ha; exact ih ha.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.warrs] at ha
      rw [ih' (by simpa [Com.warrs] using ha),ih ha]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem _root_.Lax808846Proofs.Imp.BigStep.inp_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) (hr:¬ c.reads):σ'.inp=σ.inp:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.reads,not_or] at hr
      rw [ih' hr.2,ih hr.1]
  | ite_true _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.1
  | ite_false _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.reads] at hr
      rw [ih' (by simpa [Com.reads] using hr),ih hr]
  | while_false _ => rfl
  | read _ => exact absurd (by rw [Com.reads]; trivial) hr
  | write _ => rfl

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

theorem Run.frame_inp {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hr:¬ c.reads):σ'.inp=σ.inp:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.inp_eq hr

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

variable {B:ℕ} {P P':Env→ Prop} {Q Q' R:Env→ Env→ Prop} {c d:Com} {K K':ℕ}

theorem Spec.run (h:Spec B P c Q K) {σ:Env} (hσ:P σ):
    ∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

theorem Spec.mono (h:Spec B P c Q K) (hK:K≤ K'):Spec B P c Q K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr.mono hK,hq⟩

theorem Spec.conseq (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ)
    (hQ:∀ σ σ',P' σ→ Q σ σ'→ Q' σ σ') (hK:K≤ K'):Spec B P' c Q' K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ (hP σ hσ)
  exact ⟨σ',hr.mono hK,hQ σ σ' hσ hq⟩

theorem Spec.pre (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ):Spec B P' c Q K:=
  h.conseq hP (fun _ _ _ hq => hq) le_rfl

theorem Spec.post (h:Spec B P c Q K) (hQ:∀ σ σ',P σ→ Q σ σ'→ Q' σ σ'):
    Spec B P c Q' K:=
  h.conseq (fun _ hσ => hσ) hQ le_rfl

theorem Spec.frame (h:Spec B P c Q K):
    Spec B P c (fun σ σ' => Q σ σ'∧
      (∀ y,y∉ c.wvars→ σ'.vars y=σ.vars y)∧
      (∀ a,a∉ c.warrs→ σ'.arrs a=σ.arrs a)∧
      (¬ c.reads→ σ'.inp=σ.inp)∧
      (c.NoWrite→ σ'.out=σ.out)) K:=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr,hq,fun y hy => hr.frame_var y hy,fun a ha => hr.frame_arr a ha,
    fun hc => hr.frame_inp hc,fun hc => hr.out_eq hc⟩

theorem Spec.assign {x:String} {e:Expr} {f:Env→ ℕ}
    (h:∀ σ,P σ→ e.evalB B σ=some (f σ)):
    Spec B P (.assign x e) (fun σ σ' => σ'=σ.setVar x (f σ)) (1 + e.size):=
  fun σ hσ => ⟨_,Run.assign (h σ hσ),rfl⟩

theorem Spec.seq (h:Spec B P c Q K) (h':Spec B P' d Q' K')
    (hmid:∀ σ σ',P σ→ Q σ σ'→ P' σ')
    (hpost:∀ σ σ' σ'',P σ→ Q σ σ'→ Q' σ' σ''→ R σ σ''):
    Spec B P (.seq c d) R (K + K'):=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  obtain ⟨σ'',hr',hq'⟩:=h' σ' (hmid σ σ' hσ hq)
  exact ⟨σ'',hr.seq hr',hpost σ σ' σ'' hσ hq hq'⟩

theorem Spec.while_potential {b:Cond} (I:Env→ Prop) (Φ:Env→ ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hstep:∀ σ,I σ→ b.evalB B σ=some true→
      ∃ σ' K,Run B c σ σ' K∧ I σ'∧ 1 + b.size + K + Φ σ'≤ Φ σ)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ Φ σ + 1 + b.size≤ K):
    Spec B P (.while b c) (fun _ σ' => I σ'∧ b.evalB B σ'=some false) K:=by
  intro σ hσ
  obtain ⟨σ',K₀,hr,hI,hfalse,hpay⟩:=Run.while_potential I Φ hdef hstep (hPI σ hσ)
  exact ⟨σ',hr.mono (by have:=hK σ hσ; omega),hI,hfalse⟩

theorem lt_of_condLt_true {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some true):ρ.vars x < ρ.vars y:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  simpa using hr.symm

theorem le_of_condLt_false {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some false):ρ.vars y≤ ρ.vars x:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  have:=hr.symm
  simp only [decide_eq_false_iff_not,not_lt] at this
  exact this

theorem Spec.forRange (x m:String) (I:Env→ Prop) (N Kb K:ℕ)
    (hxB:∀ σ,I σ→ σ.vars x < B) (hmB:∀ σ,I σ→ σ.vars m < B)
    (hm:∀ σ,I σ→ σ.vars m=N) (hxN:∀ σ,I σ→ σ.vars x≤ N)
    (hbody:Spec B (fun σ => I σ∧ σ.vars x < N) c
      (fun σ σ' => I σ'∧ σ'.vars x=σ.vars x + 1) Kb)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ (Kb + 4) * (N - σ.vars x) + 4≤ K):
    Spec B P (.while (.lt (.var x) (.var m)) c) (fun _ σ' => I σ'∧ σ'.vars x=N) K:=by
  have hsize:(Cond.lt (Expr.var x) (Expr.var m)).size=3:=by simp
  refine ((Spec.while_potential (b:=.lt (.var x) (.var m)) (c:=c) I
    (fun σ => (Kb + 4) * (N - σ.vars x))
    (fun σ hI => evalB_condLt_vars (hxB σ hI) (hmB σ hI)) ?_ hPI ?_).post ?_)
  · intro σ hI hv
    have hlt:σ.vars x < N:=by
      have:=lt_of_condLt_true hv
      rw [hm σ hI] at this
      exact this
    obtain ⟨σ',hr,hI',hx'⟩:=hbody σ ⟨hI,hlt⟩
    refine ⟨σ',Kb,hr,hI', ?_⟩
    show 1 + 3 + Kb + (Kb + 4) * (N - σ'.vars x)≤ (Kb + 4) * (N - σ.vars x)
    have hdrop:N - σ'.vars x + 1=N - σ.vars x:=by rw [hx']; omega
    exact le_of_eq (by rw [← hdrop]; ring)
  · intro σ hσ
    show (Kb + 4) * (N - σ.vars x) + 1 + 3≤ K
    have h:=hK σ hσ
    have hre:(Kb + 4) * (N - σ.vars x) + 1 + 3=(Kb + 4) * (N - σ.vars x) + 4:=by ring
    rw [hre]
    exact h
  · intro σ σ' _ hq
    refine ⟨hq.1, ?_⟩
    have:=le_of_condLt_false hq.2
    have h₁:=hm σ' hq.1
    have h₂:=hxN σ' hq.1
    omega

theorem Spec.forRangeZero (x m:String) (I:Env→ Prop) (N Kb:ℕ) (hNB:N < B)
    (hxN:∀ σ,I σ→ σ.vars x≤ N) (hm:∀ σ,I σ→ σ.vars m=N)
    (hbody:Spec B (fun σ => I σ∧ σ.vars x < N) c
      (fun σ σ' => I σ'∧ σ'.vars x=σ.vars x + 1) Kb):
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c))
      (fun _ σ' => I σ'∧ σ'.vars x=N) ((Kb + 4) * N + 6):=by
  intro σ hσ
  obtain ⟨σ',hrun,hI',hxN'⟩:=
    (Spec.forRange x m I N Kb ((Kb + 4) * N + 4)
      (fun _ hτ => lt_of_le_of_lt (hxN _ hτ) hNB) (fun _ hτ => hm _ hτ ▸ hNB) hm hxN hbody
      (fun _ h => h)
      (fun _ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)).run hσ
  exact ⟨σ', (Run.seq (Run.assign (v:=0) (by simp; omega)) hrun).mono (by simp; omega),
    hI',hxN'⟩

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

theorem eval_sub (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m - n < B):
    (Expr.bin .sub e f).evalB B σ=some (m - n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem eval_div (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / n < B):
    (Expr.bin .div e f).evalB B σ=some (m / n):=evalB_bin he hf h

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

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax109476Proofs.RamEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open Lax109476.RationalEncoding

theorem fractionValue_sign (s n d:ℕ) (hs:s≤ 1) (hd:0 < d):
    (if (fractionValue s n d).num < 0 then 1 else 0:ℕ) =
      if n=0 then 0 else s:=by
  have hscases:s=0∨ s=1:=by omega
  rcases hscases with rfl | rfl
  · have hq:0≤ fractionValue 0 n d:=by change (0:ℚ)≤ (n:ℚ) / d; positivity
    have hnum:=Rat.num_nonneg.mpr hq
    simp [not_lt.mpr hnum]
  · by_cases hz:n=0
    · simp [fractionValue,hz]
    · have hq:fractionValue 1 n d < 0:=by
        change -(n:ℚ) / d < 0
        have hp:(0:ℚ) < (n:ℚ) / d:=by positivity
        rw [neg_div]
        linarith
      have hnum:(fractionValue 1 n d).num < 0:=by
        rw [← not_le,Rat.num_nonneg]
        exact not_le_of_gt hq
      simp [hz,hnum]

end Lax109476Proofs.RamEncoding

end

section

namespace Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem storeReduced_spec (B:ℕ) (a:String) (qs:List ℚ) (q:ℚ) (i:ℕ)
    (hi:i < qs.length) (hB:1 < B) (hiB:i < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i∧ FractionOutput q σ)
      (storeReduced a) (fun _ τ => Represents a (qs.set i q) τ) 13:=by
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσi,hv,hratn,hratd,hrats⟩
  have hnB:σ.vars "rat.n" < B:=hratn ▸ hn
  have hdB:σ.vars "rat.d" < B:=hratd ▸ hd
  have hsB:σ.vars "rat.s" < B:=hrats.trans_lt hB
  have hsl:i < (σ.arrs (a ++ ".s")).length:=by rw [hσs,List.length_map]; exact hi
  have hnl:i < (σ.arrs (a ++ ".n")).length:=by rw [hσn,List.length_map]; exact hi
  have hdl:i < (σ.arrs (a ++ ".d")).length:=by rw [hσd,List.length_map]; exact hi
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  have hns:=Ne.symm hsn
  have hds:=Ne.symm hsd
  have hdn:=Ne.symm hnd
  have hsign:=RamEncoding.fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hrats (hratd ▸ q.den_pos)
  rw [hv] at hsign
  change rationalSign q=_ at hsign
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=Represents a (@List.set Rat qs i q); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced a) σ σ' ((13:Nat))) (c3 σ'); let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c6:String:=c5 ".s"; let c7:Nat→ Env:=Env.setArr σ c6 (Env.vars σ "vec.i"); let c8:Env:=c7 ((0:Nat)); let c9:String:=c5 ".n"; let c10:String→ Nat:=Env.vars c8; let c11:Nat:=c10 "vec.i"; let c12:Nat:=c10 "rat.n"; let c13:Env:=Env.setArr c8 c9 c11 c12; let c14:String:=c5 ".d"; let c15:String→ Nat:=Env.vars c13; let c16:Nat:=c15 "vec.i"; let c17:Nat:=c15 "rat.d"; let c18:Env:=Env.setArr c13 c14 c16 c17; let c19:Nat→ Nat→ Nat:=Nat.add; let c20:Nat→ Nat:=c19 ((1:Nat)); let c21:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c22:Nat→ Nat:=c19 (c20 (Cond.size c21)); let c23:Nat→ Nat:=c19 (c20 (Expr.size (Expr.var "vec.i"))); let c24:Nat:=c23 (Expr.size (Expr.lit ((0:Nat)))); let c25:Nat:=c22 c24; let c26:Nat:=c23 (Expr.size (Expr.var "rat.n")); let c27:Nat:=c23 (Expr.size (Expr.var "rat.d")); let c28:Nat:=c19 c26 c27; let c29:Expr→ Com:=Com.store c6 (Expr.var "vec.i"); let c30:Com:=c29 (Expr.lit ((0:Nat))); let c31:Com:=c29 (Expr.var "rat.s"); let c32:Com:=Com.store c9 (Expr.var "vec.i") (Expr.var "rat.n"); let c33:Com:=Com.store c14 (Expr.var "vec.i") (Expr.var "rat.d"); let c34:Env:=c7 (Env.vars σ "rat.s"); let c35:String→ Nat:=Env.vars c34; let c36:Nat:=c35 "vec.i"; let c37:Nat:=c35 "rat.n"; let c38:Env:=Env.setArr c34 c9 c36 c37; let c39:String→ Nat:=Env.vars c38; let c40:Nat:=c39 "vec.i"; let c41:Nat:=c39 "rat.d"; let c42:Env:=Env.setArr c38 c14 c40 c41; let c43:Nat:=c23 (Expr.size (Expr.var "rat.s")); let c44:Nat:=c22 c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c18 (@And.intro (Run B (storeReduced a) σ c18 ((13:Nat))) (c3 c18) (RunStep.mono B (storeReduced a) σ c18 (c19 c25 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c8 c18 c25 c28 (RunStep.ite_true B c21 c30 c31 σ c8 c24 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_0)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.lit ((0:Nat))) (Env.vars σ "vec.i") ((0:Nat)) (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_2)) (?nAX_g3962_0_0_3))) (RunStep.seq B c32 c33 c8 c13 c18 c26 c27 (RunStep.store B c8 c9 (Expr.var "vec.i") (Expr.var "rat.n") c11 c12 (RunStep.eval_var B c8 "vec.i" (?nAX_g3962_0_0_4)) (RunStep.eval_var B c8 "rat.n" (?nAX_g3962_0_0_5)) (?nAX_g3962_0_0_6)) (RunStep.store B c13 c14 (Expr.var "vec.i") (Expr.var "rat.d") c16 c17 (RunStep.eval_var B c13 "vec.i" (?nAX_g3962_0_0_7)) (RunStep.eval_var B c13 "rat.d" (?nAX_g3962_0_0_8)) (?nAX_g3962_0_0_9)))) (?nAX_g3962_0_0_10)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c42 (@And.intro (Run B (storeReduced a) σ c42 ((13:Nat))) (c3 c42) (RunStep.mono B (storeReduced a) σ c42 (c19 c44 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c34 c42 c44 c28 (RunStep.ite_false B c21 c30 c31 σ c34 c43 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_11)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.var "rat.s") (Env.vars σ "vec.i") (Env.vars σ "rat.s") (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_12)) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g3962_0_0_13))) (RunStep.seq B c32 c33 c34 c38 c42 c26 c27 (RunStep.store B c34 c9 (Expr.var "vec.i") (Expr.var "rat.n") c36 c37 (RunStep.eval_var B c34 "vec.i" (?nAX_g3962_0_0_14)) (RunStep.eval_var B c34 "rat.n" (?nAX_g3962_0_0_15)) (?nAX_g3962_0_0_16)) (RunStep.store B c38 c14 (Expr.var "vec.i") (Expr.var "rat.d") c40 c41 (RunStep.eval_var B c38 "vec.i" (?nAX_g3962_0_0_17)) (RunStep.eval_var B c38 "rat.d" (?nAX_g3962_0_0_18)) (?nAX_g3962_0_0_19)))) (?nAX_g3962_0_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Env.setArr,List.map_set]

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem spec_with_write_frame {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧
      ∀ a∉ c.warrs,τ.arrs a=σ.arrs a) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  exact ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx),
    fun a ha => hr.frame_arr a ha⟩

end Lax109476Proofs.RamFrame

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

open Lax808846.Ram Lax808846Proofs.Machine

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

theorem Fill.arr (h:Fill a x n i g F σ):σ.arrs a=arrOf n g:=h.1

theorem Fill.counter (h:Fill a x n i g F σ):σ.vars x=i:=h.2.1

theorem Fill.le (h:Fill a x n i g F σ):i≤ n:=h.2.2.1

theorem Fill.cell (h:Fill a x n i g F σ) (hj:j < i):g j=F j:=h.2.2.2 j hj

theorem Fill.length (h:Fill a x n i g F σ):(σ.arrs a).length=n:=by
  rw [h.arr,length_arrOf]

@[simp] theorem Fill.setVar_iff (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env)
    (y:String) (v:ℕ) (hy:y ≠ x):
    Fill a x n i g F (σ.setVar y v)↔ Fill a x n i g F σ:=by
  simp [Fill,Ne.symm hy]

theorem Fill.setVar (h:Fill a x n i g F σ) (hy:y ≠ x) (v:ℕ):
    Fill a x n i g F (σ.setVar y v):=
  (Fill.setVar_iff a x n i g F σ y v hy).2 h

theorem Fill.setCell (h:Fill a x n i g F σ) (v:ℕ):
    Fill a x n i (upd g i v) F (σ.setArr a i v):=
  ⟨by rw [arrs_setArr,if_pos rfl,h.arr,set_arrOf_eq_upd],by rw [vars_setArr,h.counter],
   h.2.2.1,fun j hj => by rw [upd_of_ne _ (by omega)]; exact h.cell hj⟩

theorem Fill.bump (h:Fill a x n i g F σ) (hin:i < n) (hgi:g i=F i):
    Fill a x n (i + 1) g F (σ.setVar x (i + 1)):=
  ⟨by rw [arrs_setVar,h.arr],by simp,hin,fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.cell hj
    · exact hgi⟩

namespace Fill

def Below (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ:Env):Prop:=
  ∃ g,Fill a x n (σ.vars x) g F σ

theorem Below.le (h:Below a x n F σ):σ.vars x≤ n:=by
  obtain ⟨_,hf⟩:=h; exact hf.le

theorem below_zero (h:σ.arrs a=arrOf n g) (hx:σ.vars x=0):Below a x n F σ:=
  ⟨g,h,rfl,by omega,fun j hj => absurd hj (by omega)⟩

theorem Below.done (h:Below a x n F σ) (hx:σ.vars x=n):
    ∃ g,σ.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j:=by
  obtain ⟨g,hf⟩:=h
  exact ⟨g,hf.arr,fun j hj => hf.cell (by omega)⟩

theorem Below.step (h:Below a x n F σ) (hlt:σ.vars x < n) (hv:v=F (σ.vars x)):
    Below a x n F ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)):=by
  obtain ⟨g,hf⟩:=h
  refine ⟨upd g (σ.vars x) v, ?_⟩
  rw [show ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)).vars x=σ.vars x + 1 by simp]
  exact (hf.setCell v).bump hlt (by simp [hv])

@[simp] theorem wvars_put (a x:String) (e:Expr):(put a x e).wvars=[x]:=by
  simp [put,Com.wvars]

abbrev PutPost (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ σ':Env):Prop:=
  Below a x n F σ'∧ σ'.vars x=σ.vars x + 1

theorem put_spec (B n:ℕ) (a x:String) (e:Expr) (F:ℕ→ ℕ) (P:Env→ Prop)
    (hP:∀ σ,P σ→ Below a x n F σ∧ σ.vars x < n) (hnB:n < B)
    (he:∀ σ,P σ→ e.evalB B σ=some (F (σ.vars x))):
    Spec B P (put a x e) (PutPost a x n F) (6 + e.size):=by
  intro σ hσ
  obtain ⟨hb,hlt⟩:=hP σ hσ
  obtain ⟨g,hf⟩:=hb
  refine ⟨_, (Run.seq (Run.store (idx:=σ.vars x) (v:=F (σ.vars x))
        (evalB_var (by omega)) (he σ hσ) (by rw [hf.length]; omega))
      (Run.assign (v:=σ.vars x + 1) ?_)).mono (by simp; omega), ?_,by simp⟩
  · rw [evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)]
    simp [Bop.apply]
  · exact Below.step ⟨g,hf⟩ hlt rfl

theorem loop_spec (B n:ℕ) (a x m:String) (e:Expr) (F:ℕ→ ℕ)
    (hxm:x ≠ m) (hnB:n < B)
    (he:∀ σ,Below a x n F σ→ σ.vars m=n→ σ.vars x < n→
      e.evalB B σ=some (F (σ.vars x))):
    Spec B (fun σ => (∃ g,σ.arrs a=arrOf n g)∧ σ.vars m=n)
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x e)))
      (fun _ σ' => (∃ g,σ'.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j)∧ σ'.vars x=n)
      ((10 + e.size) * n + 6):=by
  have hbody:Spec B (fun σ => (Below a x n F σ∧ σ.vars m=n)∧ σ.vars x < n) (put a x e)
      (fun σ σ' => (Below a x n F σ'∧ σ'.vars m=n)∧ σ'.vars x=σ.vars x + 1)
      (6 + e.size):=
    ((put_spec B n a x e F _ (fun _ hσ => ⟨hσ.1.1,hσ.2⟩) hnB
      (fun _ hσ => he _ hσ.1.1 hσ.1.2 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1,by rw [hq.2.1 m (by simp [Ne.symm hxm]),hσ.1.2]⟩,hq.1.2⟩)
  refine ((Spec.forRangeZero x m (fun σ => Below a x n F σ∧ σ.vars m=n) n (6 + e.size) hnB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g,harr⟩,hm⟩
    exact ⟨below_zero (by rw [arrs_setVar]; exact harr) (by simp),by simp [Ne.symm hxm,hm]⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2,hq.2⟩

namespace Demo

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

theorem exists_arrOf (xs:List ℕ) (n:ℕ) (h:xs.length=n):∃ g,xs=arrOf n g:=by
  refine ⟨fun i => xs.getD i 0, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [arrOf,List.getD_eq_getElem?_getD,hi]

theorem fillConstant_spec (B n v:ℕ) (a:String) (hnB:n < B) (hvB:v < B):
    Spec B (fun σ => (σ.arrs a).length=n∧ σ.vars "vec.n"=n) (fillConstant a v)
      (fun σ τ => τ.arrs a=List.replicate n v∧ τ.vars "vec.n"=n∧
        ∀ b ≠ a,τ.arrs b=σ.arrs b) (11 * n + 6):=by
  have hfill:=Lib.Fill.loop_spec B n a "vec.i" "vec.n" (.lit v) (fun _ => v)
    (by decide) hnB (by intros; exact evalB_lit hvB)
  intro σ hσ
  obtain ⟨τ,hr, ⟨g,hτg,hg⟩,_⟩:=hfill σ ⟨exists_arrOf _ _ hσ.1,hσ.2⟩
  refine ⟨τ,hr, ?_, ?_, ?_⟩
  · rw [hτg,replicate_eq_arrOf]
    exact arrOf_congr hg
  · exact (hr.frame_var "vec.n" (by simp [Lib.Fill.put,Com.wvars])).trans hσ.2
  · intro b hb
    exact hr.frame_arr b (by simp [Lib.Fill.put,Com.warrs,hb])

theorem zeroRationalArray_spec (B n:ℕ) (a:String) (hnB:n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (zeroRationalArray a)
      (fun σ τ => Represents a (List.replicate n 0) τ∧ τ.vars "vec.n"=n∧
        ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      (33 * n + 18):=by
  have h0:0 < B:=by omega
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  rintro σ ⟨hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτs,hτN,hτa⟩:=fillConstant_spec B n 0 (a ++ ".s") hnB h0 σ ⟨hσs,hσN⟩
  have hτn:(τ.arrs (a ++ ".n")).length=n:=by rw [hτa _ hsn.symm]; exact hσn
  obtain ⟨υ,hr₂,hυn,hυN,hυa⟩:=fillConstant_spec B n 0 (a ++ ".n") hnB h0 τ ⟨hτn,hτN⟩
  have hυd:(υ.arrs (a ++ ".d")).length=n:=by
    rw [hυa _ hnd.symm,hτa _ hsd.symm]; exact hσd
  obtain ⟨ρ,hr₃,hρd,hρN,hρa⟩:=fillConstant_spec B n 1 (a ++ ".d") hnB h1 υ ⟨hυd,hυN⟩
  have hρs:ρ.arrs (a ++ ".s")=List.replicate n 0:=by rw [hρa _ hsd,hυa _ hsn,hτs]
  have hρn:ρ.arrs (a ++ ".n")=List.replicate n 0:=by rw [hρa _ hnd,hυn]
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_,hρN, ?_⟩
  · simp [Represents,hρs,hρn,hρd,rationalSign]
  · intro b hb
    simp at hb
    exact (hρa b hb.2.2).trans ((hυa b hb.2.1).trans (hτa b hb.1))

end Lax109476Proofs.RamZeroArray

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

def filled {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun j => if j.val < k then v j else 0)

theorem filled_zero {n:ℕ} (v:Fin n→ ℚ):filled v 0=List.replicate n 0:=by simp [filled]

theorem filled_done {n:ℕ} (v:Fin n→ ℚ):filled v n=List.ofFn v:=by
  unfold filled
  congr 1
  funext j
  simp [j.isLt]

theorem filled_step {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    (filled v i.val).set i.val (v i)=filled v (i.val + 1):=by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkn:k < n:=by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki:i.val=k
    · have hfin:i=(⟨k,hkn⟩:Fin n):=Fin.ext hki
      simp [filled,hfin]
    · have hnext:k < i.val + 1↔ k < i.val:=by omega
      simp only [hki, ↓reduceIte,filled,List.getElem_ofFn]
      change (if k < i.val then v ⟨k,hkn⟩ else 0)=(if k < i.val + 1 then v ⟨k,hkn⟩ else 0)
      simp only [hnext]

end Lax109476Proofs.RamCenterUpdate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamMatrixStorage

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (a:String) (qs:List ℚ) (hσ:Represents a qs σ)
    (hs:a ++ ".s" ∉ c.warrs) (hn:a ++ ".n" ∉ c.warrs) (hd:a ++ ".d" ∉ c.warrs):
    Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") hs,
    hr.frame_arr (a ++ ".n") hn,hr.frame_arr (a ++ ".d") hd] using hσ

end Lax109476Proofs.RamEllipsoidUpdate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamEllipsoidWordBounds RamEllipsoidStoredBounds RamMatrixStorage

theorem array_length_of_bigStep {c:Com} {σ τ:Env} {K:ℕ}
    (hr:BigStep c σ τ K) (b:String):(τ.arrs b).length=(σ.arrs b).length:=by
  induction hr with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => exact ih'.trans ih
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih'.trans ih
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem extents_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (b:String) (n:ℕ) (hσ:Extents b n σ):Extents b n τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  intro s hs
  rw [array_length_of_bigStep hstep]
  exact hσ s hs

theorem workspace_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (n:ℕ) (hσ:Workspace n σ):Workspace n τ:=
  ⟨extents_of_run hr _ _ hσ.1,extents_of_run hr _ _ hσ.2.1,
    extents_of_run hr _ _ hσ.2.2.1,extents_of_run hr _ _ hσ.2.2.2⟩

end Lax109476Proofs.RamAdvanceState

end

section

open scoped Matrix

namespace Lax109476Proofs.RamInitialState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamZeroArray RamMatrixStorage RamCenterUpdate

def identityEntry (n k:ℕ):ℚ:=if k / n=k % n then 1 else 0

def identityValues (n:ℕ):Fin (n * n)→ ℚ:=fun k => identityEntry n k.val

set_option maxHeartbeats 0 in
theorem identityCoordinate_spec (B n k:ℕ) (xs:List ℚ)
    (hnB:n < B) (hkB:k < B) (h1:1 < B) (hk:k < xs.length):
    Spec B (fun σ => Represents "ell.shape" xs σ∧ σ.vars "vec.n"=n∧ σ.vars "init.k"=k)
      identityCoordinate
      (fun _ τ => Represents "ell.shape" (xs.set k (identityEntry n k)) τ) 35:=by
  have hdiv:k / n < B:=(Nat.div_le_self k n).trans_lt hkB
  have hprod:(k / n) * n < B:=(Nat.div_mul_le_self k n).trans_lt hkB
  have hmod:k % n < B:=(Nat.mod_le k n).trans_lt hkB
  have hmodEq:k - (k / n) * n=k % n:=by
    simpa [Nat.mul_comm] using (show k % n=k - n * (k / n) from Nat.mod_eq_sub_mul_div).symm
  have hnum:(identityEntry n k).num.natAbs < B:=by
    unfold identityEntry
    split_ifs <;> simp_all <;> omega
  have hden:(identityEntry n k).den < B:=by unfold identityEntry; split_ifs <;> simp_all
  have hstore:=storeReduced_spec B "ell.shape" xs (identityEntry n k) k hk h1 hkB hnum hden
  rintro σ ⟨hσA,hσn,hσk⟩
  (expose_names;
    (refine let c0:String→ Nat:=Env.vars (Env.setVar σ "vec.i" (Env.vars σ "init.k")); let c1:Nat:=c0 "init.k"; let c2:Nat:=c0 "vec.n"; let c3:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c1 c2; let c4:Env:=Env.setVar (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "init.row" c3; let c5:String→ Nat:=Env.vars c4; let c6:Nat:=c5 "init.k"; let c7:Nat:=c5 "init.row"; let c8:Nat:=c5 "vec.n"; let c9:Nat:=Nat.mul c7 c8; let c10:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c6 c9; let c11:Env:=Env.setVar c4 "init.col" c10; let c12:Env:=Env.setVar c11 "rat.s" ((0:Nat)); let c13:Env:=Env.setVar c12 "rat.d" ((1:Nat)); let c14:String→ Nat:=Env.vars c13; let c15:Nat:=c14 "init.row"; let c16:Nat:=c14 "init.col"; let c17:Prop:= @Eq Nat c15 c16; let c18:Prop:=Not c17; let c19:Env→ Prop:=Represents "ell.shape" (@List.set Rat xs k (identityEntry n k)); let c20:Env→ Env→ Prop:=fun (x τ:Env) => c19 τ; let c21:Env→ Prop:=c20 σ; let c22:Env→ Prop:=fun (σ':Env) => And (Run B identityCoordinate σ σ' ((35:Nat))) (c21 σ'); let c23:Prop:= @Exists Env c22; let c24:Nat→ Env:=Env.setVar c13 "rat.n"; let c25:Env:=c24 ((1:Nat)); let c26:Env→ Nat→ Prop:=Run B (storeReduced "ell.shape") c25; let c27:Env→ Prop:=fun (σ':Env) => And (c26 σ' ((13:Nat))) (c19 σ'); let c28:Nat→ Nat→ Nat:=Nat.add; let c29:Nat→ Nat:=c28 ((1:Nat)); let c30:Nat:=c29 (Expr.size (Expr.var "init.k")); let c31:Nat→ Nat:=c28 c30; let c32:Nat:=c29 (Expr.size (Expr.div (Expr.var "init.k") (Expr.var "vec.n"))); let c33:Nat→ Nat:=c28 c32; let c34:Expr:=Expr.sub (Expr.var "init.k") (Expr.mul (Expr.var "init.row") (Expr.var "vec.n")); let c35:Nat:=c29 (Expr.size c34); let c36:Nat→ Nat:=c28 c35; let c37:Nat:=c29 (Expr.size (Expr.lit ((0:Nat)))); let c38:Nat→ Nat:=c28 c37; let c39:Nat:=c29 (Expr.size (Expr.lit ((1:Nat)))); let c40:Nat→ Nat:=c28 c39; let c41:Nat→ Nat:=c28 (c29 (Cond.size (Cond.eq (Expr.var "init.row") (Expr.var "init.col")))); let c42:Nat:=c41 c39; let c43:Nat:=c28 c42 ((13:Nat)); let c44:Nat:=c40 c43; let c45:Nat:=c38 c44; let c46:Nat:=c36 c45; let c47:Nat:=c33 c46; let c48:Com:=Com.assign "init.row" (Expr.div (Expr.var "init.k") (Expr.var "vec.n")); let c49:Com:=Com.assign "init.col" c34; let c50:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c51:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c52:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c53:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c54:Com:=Com.ite (Cond.eq (Expr.var "init.row") (Expr.var "init.col")) c52 c53; let c55:Com:=Com.seq c54 (storeReduced "ell.shape"); let c56:Com:=Com.seq c51 c55; let c57:Com:=Com.seq c50 c56; let c58:Com:=Com.seq c49 c57; let c59:Env:=c24 ((0:Nat)); let c60:Env→ Nat→ Prop:=Run B (storeReduced "ell.shape") c59; let c61:Env→ Prop:=fun (σ':Env) => And (c60 σ' ((13:Nat))) (c19 σ'); let c62:Nat:=c41 c37; let c63:Nat:=c28 c62 ((13:Nat)); let c64:Nat:=c40 c63; let c65:Nat:=c38 c64; let c66:Nat:=c36 c65; let c67:Nat:=c33 c66; @Or.casesOn c17 c18 (fun (x:Or c17 c18) => c23) (Classical.em c17) (fun (hcase:c17) => @Exists.casesOn Env c27 (fun (x:@Exists Env c27) => c23) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.shape" xs σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") k) (FractionOutput (identityEntry n k) σ_1))) (storeReduced "ell.shape") c20 ((13:Nat)) hstore c25 ?_) fun (w:Env) (h:And (c26 w ((13:Nat))) (c19 w)) => let c0_1:Prop:=c26 w ((13:Nat)); @And.casesOn c0_1 (c19 w) (fun (x:And c0_1 (c19 w)) => c23) h fun (left:c0_1) (right:c19 w) => @Exists.intro Env c22 w (@And.intro (Run B identityCoordinate σ w ((35:Nat))) (c21 w) (RunStep.mono B identityCoordinate σ w (c31 c47) ((35:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "init.k")) (Com.seq c48 c58) σ (Env.setVar σ "vec.i" (Env.vars σ "init.k")) w c30 c47 (RunStep.assign B σ "vec.i" (Expr.var "init.k") (Env.vars σ "init.k") (RunStep.eval_var B σ "init.k" (?nAX_g4632_0_0_0))) (RunStep.seq B c48 c58 (Env.setVar σ "vec.i" (Env.vars σ "init.k")) c4 w c32 c46 (RunStep.assign B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "init.row" (Expr.div (Expr.var "init.k") (Expr.var "vec.n")) c3 (RunStep.eval_div B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) (Expr.var "init.k") (Expr.var "vec.n") c1 c2 (RunStep.eval_var B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "init.k" (?nAX_g4632_0_0_1)) (RunStep.eval_var B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "vec.n" (?nAX_g4632_0_0_2)) ?_)) (RunStep.seq B c49 c57 c4 c11 w c35 c45 (RunStep.assign B c4 "init.col" c34 c10 (RunStep.eval_sub B c4 (Expr.var "init.k") (Expr.mul (Expr.var "init.row") (Expr.var "vec.n")) c6 c9 (RunStep.eval_var B c4 "init.k" (?nAX_g4632_0_0_3)) (RunStep.eval_mul B c4 (Expr.var "init.row") (Expr.var "vec.n") c7 c8 (RunStep.eval_var B c4 "init.row" ?_) (RunStep.eval_var B c4 "vec.n" (?nAX_g4632_0_0_4)) ?_) (?nAX_g4632_0_0_5))) (RunStep.seq B c50 c56 c11 c12 w c37 c44 (RunStep.assign B c11 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c11 (?nAX_g4632_0_0_6))) (RunStep.seq B c51 c55 c12 c13 w c39 c43 (RunStep.assign B c12 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c12 h1)) (RunStep.seq B c54 (storeReduced "ell.shape") c13 c25 w c42 ((13:Nat)) (RunStep.ite_true B (Cond.eq (Expr.var "init.row") (Expr.var "init.col")) c52 c53 c13 c25 c39 (RunStep.cond_eq_true B c13 (Expr.var "init.row") (Expr.var "init.col") c15 c16 (RunStep.eval_var B c13 "init.row" ?_) (RunStep.eval_var B c13 "init.col" (?nAX_g4632_0_0_7)) hcase) (RunStep.assign B c13 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c13 h1))) left)))))) (?nAX_g4632_0_0_8)) ?_)) fun (hcase:c18) => @Exists.casesOn Env c61 (fun (x:@Exists Env c61) => c23) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.shape" xs σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") k) (FractionOutput (identityEntry n k) σ_1))) (storeReduced "ell.shape") c20 ((13:Nat)) hstore c59 ?_) fun (w:Env) (h:And (c60 w ((13:Nat))) (c19 w)) => let c0_1:Prop:=c60 w ((13:Nat)); @And.casesOn c0_1 (c19 w) (fun (x:And c0_1 (c19 w)) => c23) h fun (left:c0_1) (right:c19 w) => @Exists.intro Env c22 w (@And.intro (Run B identityCoordinate σ w ((35:Nat))) (c21 w) (RunStep.mono B identityCoordinate σ w (c31 c67) ((35:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "init.k")) (Com.seq c48 c58) σ (Env.setVar σ "vec.i" (Env.vars σ "init.k")) w c30 c67 (RunStep.assign B σ "vec.i" (Expr.var "init.k") (Env.vars σ "init.k") (RunStep.eval_var B σ "init.k" (?nAX_g4632_0_0_9))) (RunStep.seq B c48 c58 (Env.setVar σ "vec.i" (Env.vars σ "init.k")) c4 w c32 c66 (RunStep.assign B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "init.row" (Expr.div (Expr.var "init.k") (Expr.var "vec.n")) c3 (RunStep.eval_div B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) (Expr.var "init.k") (Expr.var "vec.n") c1 c2 (RunStep.eval_var B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "init.k" (?nAX_g4632_0_0_10)) (RunStep.eval_var B (Env.setVar σ "vec.i" (Env.vars σ "init.k")) "vec.n" (?nAX_g4632_0_0_11)) ?_)) (RunStep.seq B c49 c57 c4 c11 w c35 c65 (RunStep.assign B c4 "init.col" c34 c10 (RunStep.eval_sub B c4 (Expr.var "init.k") (Expr.mul (Expr.var "init.row") (Expr.var "vec.n")) c6 c9 (RunStep.eval_var B c4 "init.k" (?nAX_g4632_0_0_12)) (RunStep.eval_mul B c4 (Expr.var "init.row") (Expr.var "vec.n") c7 c8 (RunStep.eval_var B c4 "init.row" ?_) (RunStep.eval_var B c4 "vec.n" (?nAX_g4632_0_0_13)) ?_) (?nAX_g4632_0_0_14))) (RunStep.seq B c50 c56 c11 c12 w c37 c64 (RunStep.assign B c11 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c11 (?nAX_g4632_0_0_15))) (RunStep.seq B c51 c55 c12 c13 w c39 c63 (RunStep.assign B c12 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c12 h1)) (RunStep.seq B c54 (storeReduced "ell.shape") c13 c59 w c62 ((13:Nat)) (RunStep.ite_false B (Cond.eq (Expr.var "init.row") (Expr.var "init.col")) c52 c53 c13 c59 c37 (RunStep.cond_eq_false B c13 (Expr.var "init.row") (Expr.var "init.col") c15 c16 (RunStep.eval_var B c13 "init.row" ?_) (RunStep.eval_var B c13 "init.col" (?nAX_g4632_0_0_16)) hcase) (RunStep.assign B c13 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c13 (?nAX_g4632_0_0_17)))) left)))))) (?nAX_g4632_0_0_18)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4632_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4632_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hstore
  all_goals simp_all [FractionOutput,identityEntry,Represents,fractionValue]

def IdentityInvariant (n:ℕ) (σ:Env):Prop:=
  Represents "ell.shape" (filled (identityValues n) (σ.vars "init.k")) σ∧
    σ.vars "init.k" ≤ n * n∧ σ.vars "init.count"=n * n∧ σ.vars "vec.n"=n

theorem identityStep_spec (B n:ℕ) (hnB:n < B) (hnnB:n * n < B) (h1:1 < B):
    Spec B (fun σ => IdentityInvariant n σ∧ σ.vars "init.k" < n * n) identityStep
      (fun σ τ => IdentityInvariant n τ∧ τ.vars "init.k"=σ.vars "init.k" + 1) 39:=by
  rintro σ ⟨⟨hσA,hσkN,hσcount,hσn⟩,hσk⟩
  let k:Fin (n * n):= ⟨σ.vars "init.k",hσk⟩
  obtain ⟨τ,hr₁,hτA⟩:=identityCoordinate_spec B n k.val (filled (identityValues n) k.val)
    hnB (k.isLt.trans hnnB) h1 (by simp [filled]) σ ⟨hσA,hσn,rfl⟩
  have hτk:τ.vars "init.k"=k.val:=hr₁.frame_var _ (by decide)
  have hτn:τ.vars "vec.n"=n:=(hr₁.frame_var _ (by decide)).trans hσn
  have hτcount:τ.vars "init.count"=n * n:=(hr₁.frame_var _ (by decide)).trans hσcount
  have haddB:Bop.add.apply (τ.vars "init.k") 1 < B:=by
    simpa [Bop.apply,hτk] using lt_of_le_of_lt k.isLt hnnB
  have hr₂:Run B (.assign "init.k" (.add (.var "init.k") (.lit 1))) τ
      (τ.setVar "init.k" (k.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hτk] using
      (evalB_bin (evalB_var (hτk ▸ k.isLt.trans hnnB)) (evalB_lit h1) haddB))
  have hfilled:Represents "ell.shape" (filled (identityValues n) (k.val + 1)) τ:=by
    rw [← filled_step]
    exact hτA
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change k.val + 1≤ n * n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτn
  · simp [k]

theorem identityValues_eq (n:ℕ):List.ofFn (identityValues n)=flatten (1:Matrix (Fin n) (Fin n) ℚ):=by
  unfold flatten
  congr 1
  funext k
  simp [identityValues,identityEntry,Matrix.one_apply,Fin.ext_iff,Fin.divNat,Fin.modNat]

theorem identityLoop_spec (B n:ℕ) (hnB:n < B) (hnnB:n * n < B) (h1:1 < B):
    Spec B (fun σ => Represents "ell.shape" (List.replicate (n * n) 0) σ∧ σ.vars "vec.n"=n)
      identityLoop
      (fun _ τ => Represents "ell.shape" (flatten (1:Matrix (Fin n) (Fin n) ℚ)) τ∧ τ.vars "vec.n"=n)
      (43 * (n * n) + 10):=by
  have hlo:=Spec.forRangeZero "init.k" "init.count" (IdentityInvariant n) (n * n) 39 hnnB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) (identityStep_spec B n hnB hnnB h1)
  have hloop:Spec B (fun σ => Represents "ell.shape" (List.replicate (n * n) 0) σ∧
      σ.vars "init.count"=n * n∧ σ.vars "vec.n"=n)
      (.seq (.assign "init.k" (.lit 0)) (.while (.lt (.var "init.k") (.var "init.count")) identityStep))
      (fun _ τ => Represents "ell.shape" (flatten (1:Matrix (Fin n) (Fin n) ℚ)) τ∧ τ.vars "vec.n"=n)
      (43 * (n * n) + 6):=by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hA,hcount,hn⟩
      simp_all [IdentityInvariant,Represents,filled_zero]
    · rintro σ τ _ ⟨hτ,hk⟩
      refine ⟨?_,hτ.2.2.2⟩
      simpa only [hk,filled_done,identityValues_eq] using hτ.1
  rintro σ ⟨hσA,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "init.k" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "init.k") (Expr.var "init.count")) identityStep); let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c1 (Env.vars σ "vec.n") (Env.vars σ "vec.n"); let c3:Env:=Env.setVar σ "init.count" c2; let c4:Env→ Nat→ Prop:=Run B c0 c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c1 n n; let c7:Nat→ Nat:=c5 (c1 ((43:Nat)) c6); let c8:Nat:=c7 ((6:Nat)); let c9:Env→ Prop:=Represents "ell.shape" (@flatten n n (@OfNat.ofNat (Matrix (Fin n) (Fin n) Rat) (nat_lit 1) (@One.toOfNat1 (Matrix (Fin n) (Fin n) Rat) (@Matrix.one (Fin n) Rat (instDecidableEqFin n) (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)) (@AddMonoidWithOne.toOne Rat (@AddGroupWithOne.toAddMonoidWithOne Rat (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))))))); let c10:Env→ Prop:=fun (σ':Env) => And (c4 σ' c8) (And (c9 σ') (@Eq Nat (Env.vars σ' "vec.n") n)); let c11:Nat:=c7 ((10:Nat)); let c12:Env→ Env→ Prop:=fun (x τ:Env) => And (c9 τ) (@Eq Nat (Env.vars τ "vec.n") n); let c13:Env→ Prop:=c12 σ; let c14:Env→ Prop:=fun (σ':Env) => And (Run B identityLoop σ σ' c11) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:Env→ Prop:=Represents "ell.shape" (@List.replicate Rat c6 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c17:String→ Nat:=Env.vars c3; let c18:Nat:=c5 ((1:Nat)) (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))); @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c15) (RunStep.use B (fun (σ_1:Env) => And (c16 σ_1) (And (@Eq Nat (Env.vars σ_1 "init.count") c6) (@Eq Nat (Env.vars σ_1 "vec.n") n))) c0 c12 c8 hloop c3 ?_) fun (w:Env) (h:And (c4 w c8) (And (c9 w) (@Eq Nat (Env.vars w "vec.n") n))) => let c0_1:Prop:=And (c9 w) (@Eq Nat (Env.vars w "vec.n") n); @And.casesOn (c4 w c8) c0_1 (fun (x:And (c4 w c8) c0_1) => c15) h fun (left:c4 w c8) (right:c0_1) => @Exists.intro Env c14 w (@And.intro (Run B identityLoop σ w c11) (c13 w) (RunStep.mono B identityLoop σ w (c5 c18 c8) c11 (RunStep.seq B (Com.assign "init.count" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))) c0 σ c3 w c18 c8 (RunStep.assign B σ "init.count" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c2 (RunStep.eval_mul B σ (Expr.var "vec.n") (Expr.var "vec.n") (Env.vars σ "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4638_0_0_0)) (RunStep.eval_var B σ "vec.n" (?nAX_g4638_0_0_1)) ?_)) left) (?nAX_g4638_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4638_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4638_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4638_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hloop hlo
  all_goals simp_all [Represents]

theorem initializeIdentity_spec (B n:ℕ) (hnB:n < B) (hnnB:n * n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs "ell.shape.s").length=n * n∧
        (σ.arrs "ell.shape.n").length=n * n∧ (σ.arrs "ell.shape.d").length=n * n∧ σ.vars "vec.n"=n)
      initializeIdentity
      (fun _ τ => Represents "ell.shape" (flatten (1:Matrix (Fin n) (Fin n) ℚ)) τ∧ τ.vars "vec.n"=n)
      (76 * (n * n) + 36):=by
  have hz:=spec_with_write_frame ["init.savedn"] (zeroRationalArray_spec B (n * n) "ell.shape" hnnB h1)
    (by decide)
  have hi:=identityLoop_spec B n hnB hnnB h1
  rintro σ ⟨hs,hnum,hd,hn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=Env.vars (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) "vec.n"; let c2:Nat:=c0 c1 c1; let c3:Env:=Env.setVar (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) "vec.n" c2; let c4:Env→ Nat→ Prop:=Run B (zeroRationalArray "ell.shape") c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c0 n n; let c7:Nat:=c5 (c0 ((33:Nat)) c6) ((18:Nat)); let c8:Env→ Prop:=Represents "ell.shape" (@List.replicate Rat c6 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c9:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "ell.shape"; let c10:String:=c9 ".s"; let c11:String:=c9 ".n"; let c12:String:=c9 ".d"; let c13:String→ List Nat:=Env.arrs c3; let c14:Env→ Prop:=FieldsAgree (@List.cons String "init.savedn" (@List.nil String)) c3; let c15:Env→ Prop:=fun (σ':Env) => And (c4 σ' c7) (And (And (c8 σ') (And (@Eq Nat (Env.vars σ' "vec.n") c6) (∀ b∉ @List.cons String c10 (@List.cons String c11 (@List.cons String c12 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c13 b)))) (And (c14 σ') (∀ a∉ Com.warrs (zeroRationalArray "ell.shape"), @Eq (List Nat) (Env.arrs σ' a) (c13 a)))); let c16:Nat:=c5 (c0 ((76:Nat)) c6) ((36:Nat)); let c17:Env→ Prop:=Represents "ell.shape" (@flatten n n (@OfNat.ofNat (Matrix (Fin n) (Fin n) Rat) (nat_lit 1) (@One.toOfNat1 (Matrix (Fin n) (Fin n) Rat) (@Matrix.one (Fin n) Rat (instDecidableEqFin n) (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)) (@AddMonoidWithOne.toOne Rat (@AddGroupWithOne.toAddMonoidWithOne Rat (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))))))); let c18:Env→ Env→ Prop:=fun (x τ:Env) => And (c17 τ) (@Eq Nat (Env.vars τ "vec.n") n); let c19:Env→ Prop:=c18 σ; let c20:Env→ Prop:=fun (σ':Env) => And (Run B initializeIdentity σ σ' c16) (c19 σ'); let c21:Prop:= @Exists Env c20; let c22:Nat:=c5 (c0 ((43:Nat)) c6) ((10:Nat)); let c23:Nat→ Nat:=c5 ((1:Nat)); let c24:Nat:=c23 (Expr.size (Expr.var "vec.n")); let c25:Nat:=c23 (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))); let c26:Nat:=c23 (Expr.size (Expr.var "init.savedn")); let c27:Nat:=c5 c26 c22; let c28:Nat:=c5 c7 c27; let c29:Nat:=c5 c25 c28; let c30:Com:=Com.assign "vec.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")); let c31:Com:=Com.seq (zeroRationalArray "ell.shape") (Com.seq (Com.assign "vec.n" (Expr.var "init.savedn")) identityLoop); @Exists.casesOn Env c15 (fun (x:@Exists Env c15) => c21) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c10)) c6) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c11)) c6) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c12)) c6) (@Eq Nat (Env.vars σ_1 "vec.n") c6)))) (zeroRationalArray "ell.shape") (fun (σ_1 τ:Env) => And (And (c8 τ) (And (@Eq Nat (Env.vars τ "vec.n") c6) (∀ b∉ @List.cons String c10 (@List.cons String c11 (@List.cons String c12 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (FieldsAgree (@List.cons String "init.savedn" (@List.nil String)) σ_1 τ) (∀ a∉ Com.warrs (zeroRationalArray "ell.shape"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c7 hz c3 ?_) fun (w:Env) (h:And (c4 w c7) (And (And (c8 w) (And (@Eq Nat (Env.vars w "vec.n") c6) (∀ b∉ @List.cons String c10 (@List.cons String c11 (@List.cons String c12 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c13 b)))) (And (c14 w) (∀ a∉ Com.warrs (zeroRationalArray "ell.shape"), @Eq (List Nat) (Env.arrs w a) (c13 a))))) => let c0_1:Prop:=And (And (c8 w) (And (@Eq Nat (Env.vars w "vec.n") c6) (∀ b∉ @List.cons String c10 (@List.cons String c11 (@List.cons String c12 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c13 b)))) (And (c14 w) (∀ a∉ Com.warrs (zeroRationalArray "ell.shape"), @Eq (List Nat) (Env.arrs w a) (c13 a))); let c1_1:Env→ Nat→ Prop:=Run B identityLoop (Env.setVar w "vec.n" (Env.vars w "init.savedn")); let c2_1:Env→ Prop:=fun (σ':Env) => And (c1_1 σ' c22) (And (c17 σ') (@Eq Nat (Env.vars σ' "vec.n") n)); @And.casesOn (c4 w c7) c0_1 (fun (x:And (c4 w c7) c0_1) => c21) h fun (left:c4 w c7) (right:c0_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c21) (RunStep.use B (fun (σ_1:Env) => And (c8 σ_1) (@Eq Nat (Env.vars σ_1 "vec.n") n)) identityLoop c18 c22 hi (Env.setVar w "vec.n" (Env.vars w "init.savedn")) ?_) fun (w_1:Env) (h_1:And (c1_1 w_1 c22) (And (c17 w_1) (@Eq Nat (Env.vars w_1 "vec.n") n))) => let c0_2:Prop:=And (c17 w_1) (@Eq Nat (Env.vars w_1 "vec.n") n); @And.casesOn (c1_1 w_1 c22) c0_2 (fun (x:And (c1_1 w_1 c22) c0_2) => c21) h_1 fun (left_1:c1_1 w_1 c22) (right_1:c0_2) => @Exists.intro Env c20 w_1 (@And.intro (Run B initializeIdentity σ w_1 c16) (c19 w_1) (RunStep.mono B initializeIdentity σ w_1 (c5 c24 c29) c16 (RunStep.seq B (Com.assign "init.savedn" (Expr.var "vec.n")) (Com.seq c30 c31) σ (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) w_1 c24 c29 (RunStep.assign B σ "init.savedn" (Expr.var "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4640_0_0_0))) (RunStep.seq B c30 c31 (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) c3 w_1 c25 c28 (RunStep.assign B (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) "vec.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c2 (RunStep.eval_mul B (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) (Expr.var "vec.n") (Expr.var "vec.n") c1 c1 (RunStep.eval_var B (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) "vec.n" (?nAX_g4640_0_0_1)) (RunStep.eval_var B (Env.setVar σ "init.savedn" (Env.vars σ "vec.n")) "vec.n" (?nAX_g4640_0_0_2)) ?_)) (RunStep.seq B (zeroRationalArray "ell.shape") (Com.seq (Com.assign "vec.n" (Expr.var "init.savedn")) identityLoop) c3 w w_1 c7 c27 left (RunStep.seq B (Com.assign "vec.n" (Expr.var "init.savedn")) identityLoop w (Env.setVar w "vec.n" (Env.vars w "init.savedn")) w_1 c26 c22 (RunStep.assign B w "vec.n" (Expr.var "init.savedn") (Env.vars w "init.savedn") (RunStep.eval_var B w "init.savedn" ?_)) left_1)))) (?nAX_g4640_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4640_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4640_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4640_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4640_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hz hi
  all_goals simp_all [Represents,FieldsAgree]

theorem initialState_spec (B n:ℕ) (hnB:n < B) (hnnB:n * n < B) (h1:1 < B):
    Spec B (fun σ => RamEllipsoidStep.Extents "ell.center" n σ∧
        RamEllipsoidStep.Extents "ell.shape" (n * n) σ∧ RamEllipsoidStep.Workspace n σ∧
        σ.vars "vec.n"=n)
      initialState
      (fun _ τ => Represents "ell.center" (List.ofFn (0:Fin n→ ℚ)) τ∧
        Represents "ell.shape" (flatten (1:Matrix (Fin n) (Fin n) ℚ)) τ∧
        RamEllipsoidStep.Workspace n τ∧ τ.vars "vec.n"=n∧ τ.vars "iter.k"=0)
      (33 * n + 76 * (n * n) + 56):=by
  rintro σ ⟨hσc,hσA,hσw,hσn⟩
  obtain ⟨τ,hr₁,hτc,hτn,_⟩:=zeroRationalArray_spec B n "ell.center" hnB h1 σ
    ⟨hσc ".s" (by simp),hσc ".n" (by simp),hσc ".d" (by simp),hσn⟩
  have hτA:=RamAdvanceState.extents_of_run hr₁ "ell.shape" (n * n) hσA
  obtain ⟨υ,hr₂,hυA,hυn⟩:=initializeIdentity_spec B n hnB hnnB h1 τ
    ⟨hτA ".s" (by simp),hτA ".n" (by simp),hτA ".d" (by simp),hτn⟩
  have hυc:=RamEllipsoidUpdate.represents_frame hr₂ "ell.center" _ hτc
    (by decide) (by decide) (by decide)
  have hr₃:Run B (.assign "iter.k" (.lit 0)) υ (υ.setVar "iter.k" 0) 2:=
    Run.assign (evalB_lit (by omega))
  have hr:=hr₁.seq (hr₂.seq hr₃)
  have hzero:List.ofFn (0:Fin n→ ℚ)=List.replicate n 0:=List.ofFn_const n 0
  refine ⟨_,hr.mono (by omega), ?_, ?_,RamAdvanceState.workspace_of_run hr n hσw, ?_, ?_⟩
  · simpa only [hzero,Represents,arrs_setVar] using hυc
  · simpa only [Represents,arrs_setVar] using hυA
  · simpa using hυn
  · simp

end Lax109476Proofs.RamInitialState

end

theorem solution:∀ (B n:Nat),
  Nat.lt n B→
    Nat.lt (Nat.mul n n) B→
      Nat.lt ((1:Nat)) B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And (Lax109476Proofs.RamEllipsoidStep.Extents "ell.center" n σ)
              (And
                (Lax109476Proofs.RamEllipsoidStep.Extents "ell.shape"
                  (Nat.mul n n) σ)
                (And (Lax109476Proofs.RamEllipsoidStep.Workspace n σ) (@Eq Nat (σ.vars "vec.n") n))))
          Lax109476Proofs.RamInitialState.initialState
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And
              (Lax109476Proofs.RamRationalArrays.Represents "ell.center"
                (@List.ofFn Rat n
                  (@OfNat.ofNat (Fin n→ Rat) (nat_lit 0)
                    (@Zero.toOfNat0 (Fin n→ Rat)
                      (@Pi.instZero (Fin n) (fun (a:Fin n) => Rat) fun (i:Fin n) =>
                        @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
                τ)
              (And
                (Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                  (@Lax109476Proofs.RamMatrixStorage.flatten n n
                    (@OfNat.ofNat (Matrix (Fin n) (Fin n) Rat) (nat_lit 1)
                      (@One.toOfNat1 (Matrix (Fin n) (Fin n) Rat)
                        (@Matrix.one (Fin n) Rat (instDecidableEqFin n)
                          (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))
                          (@AddMonoidWithOne.toOne Rat
                            (@AddGroupWithOne.toAddMonoidWithOne Rat
                              (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing))))))))
                  τ)
                (And (Lax109476Proofs.RamEllipsoidStep.Workspace n τ)
                  (And (@Eq Nat (τ.vars "vec.n") n)
                    (@Eq Nat (τ.vars "iter.k") ((0:Nat)))))))
          (Nat.add
            (Nat.add
              (Nat.mul
                ((33:Nat)) n)
              (Nat.mul
                ((76:Nat))
                (Nat.mul n n)))
            ((56:Nat))):= @Lax109476Proofs.RamInitialState.initialState_spec
