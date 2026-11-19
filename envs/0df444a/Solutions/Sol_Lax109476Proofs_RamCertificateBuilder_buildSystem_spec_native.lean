-- Prove2me | solution 1 for Lax109476Proofs.RamCertificateBuilder.buildSystem_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:54:28.908092+00:00
-- url     : https://prove2.me/submissions/a1aafc93-4021-4929-a88e-5d9b6aa8fbcf

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces

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

def _root_.Lax808846Proofs.Imp.Com.NoWrite:Com→ Prop
  | .skip => True
  | .assign _ _ => True
  | .store _ _ _ => True
  | .read _ => True
  | .write _ => False
  | .seq c d => c.NoWrite∧ d.NoWrite
  | .ite _ c d => c.NoWrite∧ d.NoWrite
  | .while _ c => c.NoWrite

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

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

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

inductive SeqSplit:Com→ Com→ Com→ Prop

  | one (a r:Com):SeqSplit a r (.seq a r)

  | cons (a p r w:Com) (h:SeqSplit p r w):SeqSplit (.seq a p) r (.seq a w)

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

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

open Lax808846.Ram

def runOut (w:ℕ):ℕ→ Program→ State→ ℕ→ Option (List ℕ × ℕ)
  | 0,p,s,k => if s.pc < p.length then none else some (s.out,k)
  | fuel + 1,p,s,k =>
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out,k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out,k)

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

theorem Below.length (h:Below a x n F σ):(σ.arrs a).length=n:=by
  obtain ⟨_,hf⟩:=h; exact hf.length

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

def demo (a x m:String):Com:=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x (.var x)))

def demoWatched (a x m:String):Com:=
  .seq (.assign m (.lit 3))
    (.seq (demo a x m)
      (.seq (.write (.get a (.lit 0)))
        (.seq (.write (.get a (.lit 1))) (.write (.get a (.lit 2))))))

def layout:Lax808846Proofs.Compile.Layout:= ⟨["i", "m"], ["ar"],2⟩

def prog:Lax808846.Ram.Program:=
  Lax808846Proofs.Compile.compileProgram layout (demoWatched "ar" "i" "m")

def demoRun:Option (List ℕ × ℕ):=runOut 16 1000 prog (Lax808846.Ram.initState []) 0

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
open RamRational RamRationalArrays RamFractionInterface RationalArithmeticBounds
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

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamMatrixStorage

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

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamEllipsoidStep RamAdvanceState

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars
open RamBisectionCommit

def preserves (B:ℕ) (Q:Env→ Prop) (c:Com):Prop:=
  ∀ {σ τ k},Run B c σ τ k→ Q σ→ Q τ

end Lax109476Proofs.RamBisectionLoop

end

section

namespace Lax109476Proofs.RamCertificateSource

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def fields:List String:= ["source.m", "source.n"]
def arrays:List String:= ["source.A", "source.b", "source.c"]

theorem data_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℤ m n) (hσ:Data P σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):Data P τ:=by
  rcases hσ with ⟨hA,hb,hc,hm,hn⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hc hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn⟩

theorem data_setVar {m n:ℕ} (P:Program ℤ m n) (σ:Env) (v:String) (z:ℕ)
    (hv:v∉ fields) (hσ:Data P σ):Data P (σ.setVar v z):=by
  have hm:v ≠ "source.m" :=by intro h; subst v; simp [fields] at hv
  have hn:v ≠ "source.n" :=by intro h; subst v; simp [fields] at hv
  simpa [Data,Represents,arrs_setVar,vars_setVar,Ne.symm hm,Ne.symm hn] using hσ

end Lax109476Proofs.RamCertificateSource

end

section

namespace Lax109476Proofs.RamCertificateContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

theorem context_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (hσ:Context P r s σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ c.warrs):
    Context P r s τ:=by
  exact ⟨RamCertificateSource.data_frame hr P hσ.1
      (fun a h => hf a (by simp [RamCertificateSource.fields] at h; rcases h with rfl | rfl <;> simp [fields])) ha,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hσ.2.1,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hσ.2.2⟩

theorem context_setVar {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (σ:Env) (v:String) (z:ℕ)
    (hv:v∉ fields) (hσ:Context P r s σ):Context P r s (σ.setVar v z):=by
  have hr:v ≠ "system.m" :=by intro h; subst v; simp [fields] at hv
  have hs:v ≠ "system.n" :=by intro h; subst v; simp [fields] at hv
  exact ⟨RamCertificateSource.data_setVar P σ v z
    (fun h => hv (by simp [RamCertificateSource.fields] at h; rcases h with rfl | rfl <;> simp [fields])) hσ.1,
    by simpa [vars_setVar,Ne.symm hr] using hσ.2.1,
    by simpa [vars_setVar,Ne.symm hs] using hσ.2.2⟩

theorem preserves_context (B:ℕ) {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (c:Com)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ c.warrs):
    RamBisectionLoop.preserves B (Context P r s) c:=fun hr hσ => context_frame hr P r s hσ hf ha

end Lax109476Proofs.RamCertificateContext

end

section

namespace Lax109476Proofs.RamBuildVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCenterUpdate RamEllipsoidStep RationalArithmeticBounds

def Invariant {n:ℕ} (a:String) (v:Fin n→ ℚ) (Q:Env→ Prop) (σ:Env):Prop:=
  Q σ∧ Represents a (filled v (σ.vars "build.i")) σ∧
    σ.vars "build.i" ≤ n∧ σ.vars "build.count"=n

set_option maxHeartbeats 0 in
theorem step_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t)):
    Spec B (fun σ => Invariant a v Q σ∧ σ.vars "build.i" < n) (step a selector)
      (fun σ τ => Invariant a v Q τ∧ τ.vars "build.i"=σ.vars "build.i" + 1)
      (selectorCost + 19):=by
  rintro σ ⟨⟨hσQ,hσa,hσi,hσn⟩,hi⟩
  let i:Fin n:= ⟨σ.vars "build.i",hi⟩
  obtain ⟨τ,hr₁,hτQ,hτv⟩:=hselector i σ ⟨hσQ,rfl,hσn⟩
  have hτi:τ.vars "build.i"=i.val:=hr₁.frame_var _ hiFrame
  have hτa:Represents a (filled v i.val) τ:=RamReadBody.represents_frame _ _ hσa hr₁ haFrame
  have hiB:i.val < B:=i.isLt.trans hnB
  have hr₂:Run B (.assign "vec.i" (.var "build.i")) τ (τ.setVar "vec.i" i.val) 2:=
    Run.assign (by simpa only [hτi] using evalB_var (B:=B) (σ:=τ) (x:= "build.i") (hτi ▸ hiB))
  have hstore:=storeReduced_spec B a (filled v i.val) (v i) i.val
    (by simpa only [filled,List.length_ofFn] using i.isLt) h1 hiB
    ((hv i).1.trans_lt hMB) ((hv i).2.trans_lt hMB)
  obtain ⟨υ,hr₃,hυa⟩:=hstore (τ.setVar "vec.i" i.val)
    ⟨hτa,by simp,by simpa [FractionOutput,vars_setVar] using hτv⟩
  have hυQ:Q υ:=hQstore hr₃ (hQvec τ i.val hτQ)
  have hυi:υ.vars "build.i"=i.val:=
    (hr₃.frame_var _ (by simp [storeReduced,Com.wvars])).trans (by simpa using hτi)
  have hsumB:Bop.add.apply (υ.vars "build.i") 1 < B:=by simpa [hυi] using lt_of_le_of_lt i.isLt hnB
  have hr₄:Run B (.assign "build.i" (.add (.var "build.i") (.lit 1))) υ (υ.setVar "build.i" (i.val + 1)) 4:=
    Run.assign (by simpa only [hυi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "build.i") (hυi ▸ hiB)) (evalB_lit h1) hsumB))
  have hr:=(hr₁.seq (hr₂.seq hr₃)).seq hr₄
  have hfilled:Represents a (filled v (i.val + 1)) υ:=by rw [← filled_step]; exact hυa
  refine ⟨_,hr.mono (by omega), ⟨hQset υ (i.val + 1) hυQ, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change i.val + 1≤ n; exact i.isLt
  · exact (hr.frame_var _ (by simp [Com.wvars,storeReduced,hnFrame])).trans hσn
  · simp [i]

theorem loop_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t)):
    Spec B (fun σ => Q σ∧ Represents a (List.replicate n 0) σ∧ σ.vars "build.count"=n)
      (loop a selector) (fun _ τ => Q τ∧ Represents a (List.ofFn v) τ∧ τ.vars "build.count"=n)
      ((selectorCost + 23) * n + 6):=by
  have hlo:=Spec.forRangeZero "build.i" "build.count" (Invariant a v Q) n (selectorCost + 19) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2)
    (step_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector hiFrame hnFrame haFrame hQstore hQset hQvec)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσQ,hσa,hσn⟩
    exact ⟨hQset σ 0 hσQ,by simpa only [Represents,arrs_setVar,vars_setVar,ite_true,filled_zero] using hσa,by simp,by simpa using hσn⟩
  · rintro σ τ _ ⟨hτ,hcounter⟩
    exact ⟨hτ.1,by simpa only [hcounter,filled_done] using hτ.2.1,hτ.2.2.2⟩

theorem build_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQzero:RamBisectionLoop.preserves B Q (RamZeroArray.zeroRationalArray a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t))
    (hQlength:∀ σ t,Q σ→ Q (σ.setVar "vec.n" t)):
    Spec B (fun σ => Q σ∧ Extents a n σ∧ σ.vars "build.count"=n)
      (build a selector) (fun _ τ => Q τ∧ Represents a (List.ofFn v) τ∧ τ.vars "build.count"=n)
      ((selectorCost + 56) * n + 26):=by
  rintro σ ⟨hσQ,hσa,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var "build.count")) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:= "build.count") (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτa,hτn,hτframe⟩:=RamZeroArray.zeroRationalArray_spec B n a hnB h1
    (σ.setVar "vec.n" n) ⟨hσa ".s" (by simp),hσa ".n" (by simp),hσa ".d" (by simp),by simp⟩
  have hτQ:=hQzero hr₂ (hQlength σ n hσQ)
  have hτcount:τ.vars "build.count"=n:=
    (hr₂.frame_var _ (by simp [RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Com.wvars,Lib.Fill.put])).trans
      (by simpa using hσn)
  obtain ⟨υ,hr₃,hυ⟩:=loop_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector
    hiFrame hnFrame haFrame hQstore hQset hQvec τ ⟨hτQ,hτa,hτcount⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq hr₃)).mono ?_,hυ⟩
  simp only [Nat.add_mul]
  omega

end Lax109476Proofs.RamBuildVector

end

section

namespace Lax109476Proofs.RamCertificateMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

def values {r s:ℕ} (F:Program ℤ r s):Fin (r * s)→ ℚ:=
  fun i => F.A i.divNat i.modNat

set_option maxHeartbeats 0 in
theorem selectCoordinate_spec (B m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (hB:r * s + s + 4 < B)
    (hselector:∀ i j,Spec B
      (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.A i j:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ selector.warrs)
    (i:Fin (r * s)):
    Spec B (fun σ => Context P r s σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=r * s)
      (selectCoordinate selector) (fun _ τ => Context P r s τ∧ FractionOutput (values F i) τ)
      (selectorCost + 14):=by
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hs:s < B:=by omega
  have hdiv:i.val / s < B:=(Nat.div_le_self _ _).trans_lt hiB
  have hmul:(i.val / s) * s < B:=(Nat.div_mul_le_self _ _).trans_lt hiB
  have hsub:i.val - (i.val / s) * s < B:=(Nat.sub_le _ _).trans_lt hiB
  have hmod:i.val - (i.val / s) * s=i.val % s:=by
    simpa [Nat.mul_comm] using (Nat.mod_eq_sub_mul_div (x:=i.val) (k:=s)).symm
  have hsel:=hselector i.divNat i.modNat
  have hbase:Spec B (fun σ => Context P r s σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=r * s)
      (selectCoordinate selector) (fun _ τ => FractionOutput (values F i) τ) (selectorCost + 14):=by
    rintro σ ⟨⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσr,hσs⟩,hσi,hσcount⟩
    (expose_names;
      (refine let c0:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "build.i") (Env.vars σ "system.n"); let c1:Env:=Env.setVar σ "query.row" c0; let c2:String→ Nat:=Env.vars c1; let c3:Nat:=c2 "build.i"; let c4:Nat:=c2 "query.row"; let c5:Nat:=c2 "system.n"; let c6:Nat:=Nat.mul c4 c5; let c7:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c3 c6; let c8:Env:=Env.setVar c1 "query.col" c7; let c9:Env→ Nat→ Prop:=Run B selector c8; let c10:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.A Int r s F (@Fin.divNat r s i) (@Fin.modNat r s i))); let c11:Env→ Prop:=fun (σ':Env) => And (c9 σ' selectorCost) (And (@RamCertificateSource.Data m n P σ') (c10 σ')); let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat:=c12 selectorCost ((14:Nat)); let c14:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@values r s F i) τ) σ; let c15:Env→ Prop:=fun (σ':Env) => And (Run B (selectCoordinate selector) σ σ' c13) (c14 σ'); let c16:Prop:= @Exists Env c15; let c17:String→ Nat:=Env.vars c8; let c18:Nat→ Nat:=c12 ((1:Nat)); let c19:Nat:=c18 (Expr.size (Expr.div (Expr.var "build.i") (Expr.var "system.n"))); let c20:Expr:=Expr.sub (Expr.var "build.i") (Expr.mul (Expr.var "query.row") (Expr.var "system.n")); let c21:Nat:=c18 (Expr.size c20); let c22:Nat:=c12 c21 selectorCost; let c23:Com:=Com.assign "query.col" c20; @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c16) (RunStep.use B (fun (σ_1:Env) => And (@RamCertificateSource.Data m n P σ_1) (And (@Eq Nat (Env.vars σ_1 "query.row") (@Fin.val r (@Fin.divNat r s i))) (@Eq Nat (Env.vars σ_1 "query.col") (@Fin.val s (@Fin.modNat r s i))))) selector (fun (x τ:Env) => And (@RamCertificateSource.Data m n P τ) (c10 τ)) selectorCost hsel c8 ?_) fun (w:Env) (h:And (c9 w selectorCost) (And (@RamCertificateSource.Data m n P w) (c10 w))) => let c0_1:Prop:=And (@RamCertificateSource.Data m n P w) (c10 w); @And.casesOn (c9 w selectorCost) c0_1 (fun (x:And (c9 w selectorCost) c0_1) => c16) h fun (left:c9 w selectorCost) (right:c0_1) => @Exists.intro Env c15 w (@And.intro (Run B (selectCoordinate selector) σ w c13) (c14 w) (RunStep.mono B (selectCoordinate selector) σ w (c12 c19 c22) c13 (RunStep.seq B (Com.assign "query.row" (Expr.div (Expr.var "build.i") (Expr.var "system.n"))) (Com.seq c23 selector) σ c1 w c19 c22 (RunStep.assign B σ "query.row" (Expr.div (Expr.var "build.i") (Expr.var "system.n")) c0 (RunStep.eval_div B σ (Expr.var "build.i") (Expr.var "system.n") (Env.vars σ "build.i") (Env.vars σ "system.n") (RunStep.eval_var B σ "build.i" (?nAX_g4423_0_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g4423_0_0_1)) ?_)) (RunStep.seq B c23 selector c1 c8 w c21 selectorCost (RunStep.assign B c1 "query.col" c20 c7 (RunStep.eval_sub B c1 (Expr.var "build.i") (Expr.mul (Expr.var "query.row") (Expr.var "system.n")) c3 c6 (RunStep.eval_var B c1 "build.i" (?nAX_g4423_0_0_2)) (RunStep.eval_mul B c1 (Expr.var "query.row") (Expr.var "system.n") c4 c5 (RunStep.eval_var B c1 "query.row" ?_) (RunStep.eval_var B c1 "system.n" (?nAX_g4423_0_0_3)) ?_) (?nAX_g4423_0_0_4))) left)) (?nAX_g4423_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4423_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4423_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4423_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4423_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4423_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4423_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hsel
    all_goals simp_all [values,Fin.divNat,Fin.modNat,RamCertificateSource.Data,Represents,arrs_setVar]
    all_goals omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,context_frame hr P r s hσ.1 ?_ ?_,hτ⟩
  · intro a ha'
    have haRow:a ≠ "query.row" :=by simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide
    have haCol:a ≠ "query.col" :=by simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide
    simp [selectCoordinate,Com.wvars,haRow,haCol,hf a ha']
  · simpa [selectCoordinate,Com.warrs] using ha

set_option maxHeartbeats 0 in
theorem matrix_spec (B M m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (hM:1≤ M) (hMB:M < B) (hB:r * s + r + s + 4 < B)
    (hA:∀ i j, (F.A i j).natAbs≤ M)
    (hselector:∀ i j,Spec B
      (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.A i j:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ selector.warrs)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (htarget:∀ t∈ RamCopy.suffixes, "system.A" ++ t∉ selector.warrs):
    Spec B (fun σ => Context P r s σ∧ Extents "system.A" (r * s) σ) (matrix selector)
      (fun _ τ => Context P r s τ∧ Represents "system.A" (RamMatrixStorage.flatten (rationalProgram F).A) τ)
      ((selectorCost + 70) * (r * s) + 34):=by
  have h1:1 < B:=by omega
  have hNB:r * s < B:=by omega
  have hbuild:=RamBuildVector.build_spec B M (r * s) (selectorCost + 14) "system.A" (values F)
    (selectCoordinate selector) (Context P r s) h1 hNB hMB
    (fun i => ⟨by simpa [values] using hA i.divNat i.modNat,by simpa [values] using hM⟩)
    (selectCoordinate_spec B m n r s selectorCost P F selector (by omega) hselector hf ha)
    (by simpa [selectCoordinate,Com.wvars] using hiFrame)
    (by simpa [selectCoordinate,Com.wvars] using hnFrame)
    (by simpa [selectCoordinate,Com.warrs] using htarget)
    (preserves_context B P r s (storeReduced "system.A")
      (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha' t ht
        simp [RamCertificateSource.arrays] at ha'
        simp [RamCopy.suffixes] at ht
        rcases ha' with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (preserves_context B P r s (RamZeroArray.zeroRationalArray "system.A")
      (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha' t ht
        simp [RamCertificateSource.arrays] at ha'
        simp [RamCopy.suffixes] at ht
        rcases ha' with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (fun σ z h => context_setVar P r s σ "build.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.n" z (by decide) h)
  have hmeta:Spec B (fun σ => σ.vars "system.m"=r∧ σ.vars "system.n"=s) prepare
      (fun _ τ => τ.vars "build.count"=r * s) 4:=by
    rintro σ ⟨hr,hs⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 r s; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "build.count") c1) σ; let c3:Nat:=c0 (Env.vars σ "system.m") (Env.vars σ "system.n"); let c4:Env:=Env.setVar σ "build.count" c3; @Exists.intro Env (fun (σ':Env) => And (Run B prepare σ σ' ((4:Nat))) (c2 σ')) c4 (@And.intro (Run B prepare σ c4 ((4:Nat))) (c2 c4) (RunStep.mono B prepare σ c4 (Nat.add ((1:Nat)) (Expr.size (Expr.mul (Expr.var "system.m") (Expr.var "system.n")))) ((4:Nat)) (RunStep.assign B σ "build.count" (Expr.mul (Expr.var "system.m") (Expr.var "system.n")) c3 (RunStep.eval_mul B σ (Expr.var "system.m") (Expr.var "system.n") (Env.vars σ "system.m") (Env.vars σ "system.n") (RunStep.eval_var B σ "system.m" (?nAX_g4426_0_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g4426_0_0_1)) ?_)) (?nAX_g4426_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4426_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4426_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4426_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hσContext,hσtarget⟩
  obtain ⟨τ,hr₁,hτcount⟩:=hmeta σ hσContext.2
  have hτContext:=context_frame hr₁ P r s hσContext
    (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha' t ht; simp [prepare,Com.warrs])
  obtain ⟨υ,hr₂,hυContext,hυtarget,hυcount⟩:=hbuild τ
    ⟨hτContext,RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσtarget,hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_,hυContext, ?_⟩
  · simp only [Nat.add_assoc,Nat.reduceAdd]; omega
  · exact hυtarget

end Lax109476Proofs.RamCertificateMatrix

end

section

namespace Lax109476Proofs.RamCertificateBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

theorem selectCoordinate_spec (B m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (hrB:r < B)
    (hselector:∀ i,Spec B (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.b i:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars) (i:Fin r):
    Spec B (fun σ => Context P r s σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=r)
      (selectCoordinate selector) (fun _ τ => Context P r s τ∧ FractionOutput (F.b i:ℚ) τ)
      (selectorCost + 2):=by
  rintro σ ⟨hσContext,hσi,hσcount⟩
  have hr₁:Run B (.assign "query.row" (.var "build.i")) σ (σ.setVar "query.row" i.val) 2:=
    Run.assign (by simpa only [hσi] using evalB_var (B:=B) (σ:=σ) (x:= "build.i") (hσi ▸ i.isLt.trans hrB))
  have hτContext:=context_setVar P r s σ "query.row" i.val (by decide) hσContext
  obtain ⟨υ,hr₂,hυData,hυq⟩:=hselector i (σ.setVar "query.row" i.val) ⟨hτContext.1,by simp⟩
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ⟨hυData, ?_, ?_⟩,hυq⟩
  · exact (hr₂.frame_var _ (hf _ (by simp [fields]))).trans hτContext.2.1
  · exact (hr₂.frame_var _ (hf _ (by simp [fields]))).trans hτContext.2.2

set_option maxHeartbeats 0 in
theorem buildBound_spec (B M m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (h1:1 < B) (hMB:M < B) (hrB:r < B)
    (hb:∀ i,Height (F.b i:ℚ) M)
    (hselector:∀ i,Spec B (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.b i:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (htarget:∀ t∈ RamCopy.suffixes, "system.b" ++ t∉ selector.warrs):
    Spec B (fun σ => Context P r s σ∧ Extents "system.b" r σ) (buildBound selector)
      (fun _ τ => Context P r s τ∧ Represents "system.b" (List.ofFn (rationalProgram F).b) τ)
      ((selectorCost + 58) * r + 28):=by
  have hbuild:=RamBuildVector.build_spec B M r (selectorCost + 2) "system.b" (rationalProgram F).b
    (selectCoordinate selector) (Context P r s) h1 hrB hMB hb
    (selectCoordinate_spec B m n r s selectorCost P F selector hrB hselector hf)
    (by simpa [selectCoordinate,Com.wvars] using hiFrame)
    (by simpa [selectCoordinate,Com.wvars] using hnFrame)
    (by simpa [selectCoordinate,Com.warrs] using htarget)
    (preserves_context B P r s (storeReduced "system.b")
      (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha t ht
        simp [RamCertificateSource.arrays] at ha
        simp [RamCopy.suffixes] at ht
        rcases ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (preserves_context B P r s (RamZeroArray.zeroRationalArray "system.b")
      (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha t ht
        simp [RamCertificateSource.arrays] at ha
        simp [RamCopy.suffixes] at ht
        rcases ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (fun σ z h => context_setVar P r s σ "build.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.n" z (by decide) h)
  have hmeta:Spec B (fun σ => σ.vars "system.m"=r) prepare
      (fun _ τ => τ.vars "build.count"=r) 2:=by
    intro σ hr
    refine ⟨σ.setVar "build.count" r, ?_,by simp⟩
    exact Run.assign (by simpa only [hr] using evalB_var (B:=B) (σ:=σ) (x:= "system.m") (hr ▸ hrB))
  rintro σ ⟨hσContext,hσtarget⟩
  obtain ⟨τ,hr₁,hτcount⟩:=hmeta σ hσContext.2.1
  have hτContext:=context_frame hr₁ P r s hσContext
    (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha t ht; simp [prepare,Com.warrs])
  obtain ⟨υ,hr₂,hυContext,hυtarget,hυcount⟩:=hbuild τ
    ⟨hτContext,RamAdvanceState.extents_of_run hr₁ "system.b" r hσtarget,hτcount⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hυContext,hυtarget⟩

end Lax109476Proofs.RamCertificateBound

end

section

namespace Lax109476Proofs.RamCertificateBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

set_option maxHeartbeats 0 in
theorem buildSystem_spec (B M m n r s matrixCost boundCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (matrixSelector boundSelector:Com) (hM:1≤ M) (hMB:M < B)
    (hB:r * s + r + s + 4 < B)
    (hA:∀ i j, (F.A i j).natAbs≤ M) (hb:∀ i, (F.b i).natAbs≤ M)
    (hMatrix:∀ i j,Spec B
      (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      matrixSelector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.A i j:ℚ) τ) matrixCost)
    (hBound:∀ i,Spec B (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val)
      boundSelector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.b i:ℚ) τ) boundCost)
    (hfm:∀ a∈ fields,a∉ matrixSelector.wvars)
    (hfb:∀ a∈ fields,a∉ boundSelector.wvars)
    (him:"build.i" ∉ matrixSelector.wvars) (hnm:"build.count" ∉ matrixSelector.wvars)
    (hib:"build.i" ∉ boundSelector.wvars) (hnb:"build.count" ∉ boundSelector.wvars)
    (ham:matrixSelector.warrs=[]) (hab:boundSelector.warrs=[]):
    Spec B (fun σ => Context P r s σ∧ Extents "system.A" (r * s) σ∧ Extents "system.b" r σ)
      (buildSystem matrixSelector boundSelector)
      (fun _ τ => RamCertificateSource.Data P τ∧ RamEquationData.Data F τ)
      ((matrixCost + 70) * (r * s) + (boundCost + 58) * r + 62):=by
  have h1:1 < B:=by omega
  have hm:=RamCertificateMatrix.matrix_spec B M m n r s matrixCost P F matrixSelector hM hMB hB hA hMatrix hfm
    (by intro a ha t ht; rw [ham]; simp) him hnm (by intro t ht; rw [ham]; simp)
  have hbound:=RamCertificateBound.buildBound_spec B M m n r s boundCost P F boundSelector h1 hMB (by omega)
    (fun i => ⟨by simpa using hb i,by simpa using hM⟩) hBound hfb hib hnb
    (by intro t ht; rw [hab]; simp)
  rintro σ ⟨hσContext,hσA,hσb⟩
  obtain ⟨τ,hr₁,hτContext,hτA⟩:=hm σ ⟨hσContext,hσA⟩
  obtain ⟨υ,hr₂,hυContext,hυb⟩:=hbound τ
    ⟨hτContext,RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  have hυA:=RamReadBody.represents_frame "system.A" (RamMatrixStorage.flatten (rationalProgram F).A) hτA hr₂
    (by
      intro t ht
      simp [RamCopy.suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [RamCertificateBound.buildBound,RamCertificateBound.prepare,RamCertificateBound.selectCoordinate,
        RamBuildVector.build,RamBuildVector.loop,RamBuildVector.step,RamBuildVector.coordinate,
        RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put,storeReduced,Com.warrs,hab])
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυContext.1,hυA,hυb,hυContext.2⟩

end Lax109476Proofs.RamCertificateBuilder

end

theorem solution:∀ (B M m n r s matrixCost boundCost:Nat) (P:Lax109476.LinearProgram.Program Int m n)
  (F:Lax109476.LinearProgram.Program Int r s) (matrixSelector boundSelector:Lax808846Proofs.Imp.Com),
  Nat.le ((1:Nat)) M→
    Nat.lt M B→
      Nat.lt
          (Nat.add
            (Nat.add
              (Nat.add (Nat.mul r s)
                r)
              s)
            ((4:Nat)))
          B→
        (∀ (i:Fin r) (j:Fin s),Nat.le (@Lax109476.LinearProgram.Program.A Int r s F i j).natAbs M)→
          (∀ (i:Fin r),Nat.le (@Lax109476.LinearProgram.Program.b Int r s F i).natAbs M)→
            (∀ (i:Fin r) (j:Fin s),
                Lax808846Proofs.Reasoning.Spec B
                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                    And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                      (And (@Eq Nat (σ.vars "query.row") (@Fin.val r i)) (@Eq Nat (σ.vars "query.col") (@Fin.val s j))))
                  matrixSelector
                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                      (Lax109476Proofs.RamRational.FractionOutput
                        (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.A Int r s F i j)) τ))
                  matrixCost)→
              (∀ (i:Fin r),
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                        (@Eq Nat (σ.vars "query.row") (@Fin.val r i)))
                    boundSelector
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                        (Lax109476Proofs.RamRational.FractionOutput
                          (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.b Int r s F i)) τ))
                    boundCost)→
                (∀ (a:String),
                    @Membership.mem String (List String) (@List.instMembership String)
                        Lax109476Proofs.RamCertificateContext.fields a→
                      a∉ matrixSelector.wvars)→
                  (∀ (a:String),
                      @Membership.mem String (List String) (@List.instMembership String)
                          Lax109476Proofs.RamCertificateContext.fields a→
                        a∉ boundSelector.wvars)→
                    "build.i" ∉ matrixSelector.wvars→
                      "build.count" ∉ matrixSelector.wvars→
                        "build.i" ∉ boundSelector.wvars→
                          "build.count" ∉ boundSelector.wvars→
                            @Eq (List String) matrixSelector.warrs (@List.nil String)→
                              @Eq (List String) boundSelector.warrs (@List.nil String)→
                                Lax808846Proofs.Reasoning.Spec B
                                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateContext.Context m n P r s σ)
                                      (And
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.A"
                                          (Nat.mul r s) σ)
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.b" r σ)))
                                  (Lax109476Proofs.RamCertificateBuilder.buildSystem matrixSelector boundSelector)
                                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                                      (@Lax109476Proofs.RamEquationData.Data r s F τ))
                                  (Nat.add
                                    (Nat.add
                                      (Nat.mul
                                        (Nat.add matrixCost
                                          ((70:Nat)))
                                        (Nat.mul r s))
                                      (Nat.mul
                                        (Nat.add boundCost
                                          ((58:Nat)))
                                        r))
                                    ((62:Nat))):= @Lax109476Proofs.RamCertificateBuilder.buildSystem_spec
