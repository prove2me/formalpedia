-- Prove2me | solution 1 for Lax263307Proofs.NativeSeparatorProgram.exists_program_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:31:00.094031+00:00
-- url     : https://prove2.me/submissions/08702206-a523-416a-b073-8a6fb54b6142

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax455465Proofs_RamVirtualExecution_execute_spec_native

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

namespace Lax455465Proofs.RamVirtualExecution
end Lax455465Proofs.RamVirtualExecution
theorem Lax455465Proofs.RamVirtualExecution.execute_spec:∀ (B w k:Nat) (p:Lax808846.Ram.Program) (input:List Nat) (f:Lax455465Proofs.SparseRam.SparseState),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) w)
            ((2:Nat))))
        ((3:Nat)))
      B→
    LT.lt
        (HAdd.hAdd k ((1:Nat)))
        B→
      LT.lt
          (HAdd.hAdd (@List.length Lax808846.Ram.Instr p)
            ((1:Nat)))
          B→
        (∀ (i:Lax808846.Ram.Instr),
            @Membership.mem Lax808846.Ram.Instr Lax808846.Ram.Program (@List.instMembership Lax808846.Ram.Instr) p i→
              Lax455465Proofs.RamVirtualInstruction.LiteralsFit
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) B
                  ((1:Nat)))
                i)→
          LT.lt (@List.length Nat input) B→
            (∀ (x:Nat),
                @Membership.mem Nat (List Nat) (@List.instMembership Nat) input x→ LT.lt x B)→
              @Eq (Option Lax455465Proofs.SparseRam.SparseState)
                  (Lax455465Proofs.SparseRam.run w p k (Lax455465Proofs.SparseRam.init input))
                  (@Option.some Lax455465Proofs.SparseRam.SparseState f)→
                @Eq (Option Lax455465Proofs.SparseRam.SparseState) (Lax455465Proofs.SparseRam.step w p f)
                    (@Option.none Lax455465Proofs.SparseRam.SparseState)→
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Eq Nat (σ.vars "vm.width") w)
                        (And (Lax455465Proofs.RamVirtualState.Prefix input "vm.input" σ)
                          (And (@Eq Nat (σ.vars "vm.inputLength") (@List.length Nat input))
                            (And (LT.lt k (@List.length Nat (σ.arrs "vm.addresses")))
                              (And (LT.lt k (@List.length Nat (σ.arrs "vm.values")))
                                (LT.lt k (@List.length Nat (σ.arrs "vm.output"))))))))
                    (Lax455465Proofs.RamVirtualProgram.execute p)
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (Lax455465Proofs.RamVirtualState.Represents w f τ)
                        (@Eq Nat (τ.vars "vm.running") ((0:Nat))))
                    (HAdd.hAdd
                      (HMul.hMul
                        (HAdd.hAdd k
                          ((1:Nat)))
                        (HAdd.hAdd
                          (HAdd.hAdd
                            (HMul.hMul
                              ((4:Nat))
                              (@List.length Lax808846.Ram.Instr p))
                            (HMul.hMul
                              ((32:Nat)) k))
                          ((104:Nat))))
                      ((18:Nat))):= @Lax455465Proofs.RamVirtualExecution.execute_spec_native

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

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_get_iff {B:ℕ} {a:String} {i:Expr} {σ:Env} {v:ℕ}:
    (Expr.get a i).evalB B σ=some v↔
      ∃ k,i.evalB B σ=some k∧ (σ.arrs a)[k]?=some v∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨k,hk,u,hu,rfl,hlt⟩; exact ⟨k,hk,hu,hlt⟩
  · rintro ⟨k,hk,hu,hlt⟩; exact ⟨k,hk,v,hu,rfl,hlt⟩

@[simp] theorem evalB_condEq_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.eq e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=(m == n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

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

end Lax808846Proofs.Reasoning

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem bitSize_append (xs ys:List ℕ):bitSize (xs ++ ys)=bitSize xs + bitSize ys:=by
  simp [bitSize,encode]

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem bounded_size (xs:List ℕ) (K:ℕ) (h:∀ x∈ xs,x.size≤ K):
    bitSize xs≤ xs.length * (K + 1):=by
  induction xs with
  | nil => simp [bitSize_nil]
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [bitSize_cons]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem size_half (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne:Nat.bit b n ≠ 0:=by omega
    rw [Nat.bit_div_two,Nat.size_bit hne]

end Lax455465Proofs.WordSize

end

section

namespace Lax808846Proofs.Imp

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

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

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

theorem Spec.post (h:Spec B P c Q K) (hQ:∀ σ σ',P σ→ Q σ σ'→ Q' σ σ'):
    Spec B P c Q' K:=
  h.conseq (fun _ hσ => hσ) hQ le_rfl

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

theorem Spec.while_count {b:Cond} (I:Env→ Prop) (V:Env→ ℕ) (Kb:ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hbody:Spec B (fun σ => I σ∧ b.evalB B σ=some true) c
      (fun σ σ' => I σ'∧ V σ' < V σ) Kb)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ (1 + b.size + Kb) * V σ + 1 + b.size≤ K):
    Spec B P (.while b c) (fun _ σ' => I σ'∧ b.evalB B σ'=some false) K:=by
  refine Spec.while_potential I (fun σ => (1 + b.size + Kb) * V σ) hdef ?_ hPI hK
  intro σ hI hv
  obtain ⟨σ',hr,hI',hV⟩:=hbody σ ⟨hI,hv⟩
  refine ⟨σ',Kb,hr,hI', ?_⟩
  calc 1 + b.size + Kb + (1 + b.size + Kb) * V σ'
     =(1 + b.size + Kb) * (V σ' + 1):=by ring
    _≤ (1 + b.size + Kb) * V σ:=Nat.mul_le_mul_left _ hV

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

theorem eval_div (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / n < B):
    (Expr.bin .div e f).evalB B σ=some (m / n):=evalB_bin he hf h

theorem eval_and (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.land m n < B):
    (Expr.bin .and e f).evalB B σ=some (Nat.land m n):=evalB_bin he hf h

theorem eval_or (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.lor m n < B):
    (Expr.bin .or e f).evalB B σ=some (Nat.lor m n):=evalB_bin he hf h

theorem eval_xor (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.xor m n < B):
    (Expr.bin .xor e f).evalB B σ=some (Nat.xor m n):=evalB_bin he hf h

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

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

end Lax455465Proofs.RamRational

end

section

namespace Lax263307Proofs.NativeSignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational

theorem save_spec (B:ℕ) (name:String) (q:ℚ) (h1:1< B)
    (hn:q.num.natAbs< B) (hd:q.den< B)
    (hfresh:name++".s"≠"rat.n" ∧ name++".s"≠"rat.d" ∧ name++".n"≠"rat.d"):
    Spec B (FractionOutput q) (save name) (fun _ τ => Stored name q τ) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB:σ.vars "rat.s"< B:=hs.trans_lt h1
  have hsN:=Ne.symm hfresh.1
  have hsD:=Ne.symm hfresh.2.1
  have hnD:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Stored name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".s"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.s"); let c4:String:=c1 ".n"; let c5:Nat:=Env.vars c3 "rat.n"; let c6:Env:=Env.setVar c3 c4 c5; let c7:String:=c1 ".d"; let c8:Nat:=Env.vars c6 "rat.d"; let c9:Env:=Env.setVar c6 c7 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.var "rat.s")); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c4 (Expr.var "rat.n"); let c17:Com:=Com.assign c7 (Expr.var "rat.d"); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((6:Nat))) (c0 σ')) c9 (@And.intro (Run B (save name) σ c9 ((6:Nat))) (c0 c9) (RunStep.mono B (save name) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.s")) (Com.seq c16 c17) σ c3 c9 c12 c15 (RunStep.assign B σ c2 (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B c16 c17 c3 c6 c9 c13 c14 (RunStep.assign B c3 c4 (Expr.var "rat.n") c5 (RunStep.eval_var B c3 "rat.n" ?_)) (RunStep.assign B c6 c7 (Expr.var "rat.d") c8 (RunStep.eval_var B c6 "rat.d" ?_)))) (?nAX_g5443_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5443_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem load_spec (B:ℕ) (name:String) (q:ℚ) (h1:1< B)
    (hn:q.num.natAbs< B) (hd:q.den< B)
    (hfresh:name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n"):
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB:σ.vars (name++".s")< B:=hs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "rat.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "rat.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "rat.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "rat.n" c14; let c20:Com:=Com.assign "rat.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (load name) σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c9 (@And.intro (Run B (load name) σ c9 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c9) (RunStep.mono B (load name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "rat.s" c12 c2 (RunStep.eval_var B σ c1 hsB)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "rat.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "rat.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g5444_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax263307Proofs.NativeSignedArithmetic

end

section

namespace Lax455465Proofs.SparseRam

open Lax808846.Ram

theorem lookup_write (w:ℕ) (m:Memory) (a v:ℕ):
    lookup (write w m a v)=setCell w (lookup m) a v:=by
  funext b
  rfl

def expand (s:SparseState):State:= ⟨s.pc,lookup s.memory,s.input,s.inp,s.out⟩

theorem effect_expand (w:ℕ) (i:Instr) (s:SparseState):
    (effect w i s).map expand=i.effect w (expand s):=by
  cases i <;> simp only [effect,Instr.effect,assign,expand,lookup_write,Option.map_some,Option.map_none] <;> try rfl
  rename_i a
  cases s.inp.head? <;> simp only [Option.map_some,Option.map_none,expand,lookup_write]

theorem step_expand (w:ℕ) (p:Program) (s:SparseState):
    (step w p s).map expand=Lax808846.Ram.step w p (expand s):=by
  change (p[s.pc]?.bind fun i => effect w i s).map expand =
    p[s.pc]?.bind fun i => i.effect w (expand s)
  cases hi:p[s.pc]? with
  | none => rfl
  | some i => exact effect_expand w i s

theorem init_expand (x:List ℕ):expand (init x)=initState x:=rfl

theorem run_expand (w:ℕ) (p:Program) (t:ℕ) (s:SparseState):
    (run w p t s).map expand=Lax808846.Ram.run w p t (expand s):=by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [run,Lax808846.Ram.run]
    have he:=step_expand w p s
    cases hs:step w p s with
    | none =>
      have hn:Lax808846.Ram.step w p (expand s)=none:=by
        simpa only [hs,Option.map_none] using he.symm
      simp only [hn,Option.bind_none,Option.map_none]
    | some τ =>
      have hn:Lax808846.Ram.step w p (expand s)=some (expand τ):=by
        simpa only [hs,Option.map_some] using he.symm
      simp only [hn,Option.bind_some]
      exact ih τ

theorem effect_memory_le (w:ℕ) (i:Instr) (s τ:SparseState)
    (hs:effect w i s=some τ):τ.memory.length≤ s.memory.length + 1:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs; simp [assign,write])
    | solve | (cases hi:s.inp.head? <;> (try simp only [hi,Option.map_some,Option.map_none] at hs) <;> cases hs <;> simp [assign,write])

theorem step_memory_le (w:ℕ) (p:Program) (s τ:SparseState)
    (hs:step w p s=some τ):τ.memory.length≤ s.memory.length + 1:=by
  unfold step at hs
  cases hi:p[s.pc]? with
  | none => simp only [hi,Option.bind_none] at hs; cases hs
  | some i =>
    simp only [hi,Option.bind_some] at hs
    exact effect_memory_le w i s τ hs

theorem run_memory_le (w:ℕ) (p:Program) (t:ℕ) (s τ:SparseState)
    (hs:run w p t s=some τ):τ.memory.length≤ s.memory.length + t:=by
  induction t generalizing s τ with
  | zero =>
    simp only [run,Option.some.injEq] at hs
    subst τ
    omega
  | succ t ih =>
    obtain ⟨ν,hstep,hrest⟩:=Option.bind_eq_some_iff.mp hs
    have hfirst:=step_memory_le w p s ν hstep
    have hlast:=ih ν τ hrest
    omega

theorem exists_execution (w:ℕ) (p:Program) (x y:List ℕ) (t:ℕ)
    (h:RunsTo w p x y t):
    ∃ k≤ t, ∃ s:SparseState,
      run w p k (init x)=some s∧ step w p s=none∧ s.out=y∧
      s.memory.length≤ k∧ t=k + terminalCost p (expand s):=by
  obtain ⟨k,τ,hrun,hhalt,hout,htime⟩:=h
  have hexpand:=run_expand w p k (init x)
  rw [init_expand,hrun] at hexpand
  cases hs:run w p k (init x) with
  | none => simp only [hs,Option.map_none] at hexpand; cases hexpand
  | some s =>
    have heq:expand s=τ:=by simpa only [hs,Option.map_some,Option.some.injEq] using hexpand
    have hstop:step w p s=none:=by
      have he:=step_expand w p s
      rw [heq,hhalt] at he
      exact Option.map_eq_none_iff.mp he
    have hm:=run_memory_le w p k (init x) s hs
    have htime':t=k + terminalCost p (expand s):=by rw [heq]; exact htime
    refine ⟨k,by omega,s,hs,hstop, ?_, ?_,htime'⟩
    · change (expand s).out=y
      rw [heq]
      exact hout
    · simpa only [init,List.length_nil,Nat.zero_add] using hm

theorem polynomial_execution (solve:List ℕ→ List ℕ)
    (hsolve:Lax759944.RamPolytime.RamPolytime solve):
    ∃ (p:Program) (wordBound timeBound:Polynomial ℕ), ∀ x:List ℕ,
      Lax759944.RamPolytime.FitsInWords (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x))
        ((x.length::x) ++ solve x)∧
      ∃ k≤ timeBound.eval (Lax759944.BinaryWordEncoding.bitSize x), ∃ s:SparseState,
        run (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x)) p k (init (x.length::x))=some s∧
        step (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x)) p s=none∧
        s.out=solve x∧ s.memory.length≤ k:=by
  obtain ⟨p,wordBound,timeBound,hprogram⟩:=hsolve
  refine ⟨p,wordBound,timeBound, ?_⟩
  intro x
  obtain ⟨hfit,hwidth⟩:=hprogram x
  obtain ⟨t,ht,hrun⟩:=hwidth _ le_rfl
  obtain ⟨k,hkt,s,hs,hhalt,hout,hmemory,_⟩:=exists_execution _ p _ _ t hrun
  exact ⟨hfit,k,hkt.trans ht,s,hs,hhalt,hout,hmemory⟩

end Lax455465Proofs.SparseRam

end

section

namespace Lax455465Proofs.SparseBounds

open Lax808846.Ram SparseRam

theorem effect_output_le (w:ℕ) (i:Instr) (s τ:SparseState)
    (hs:effect w i s=some τ):τ.out.length≤ s.out.length + 1:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> simp [assign])
    | solve | (cases hi:s.inp.head? <;>
      (try simp only [hi,Option.map_some,Option.map_none] at hs) <;>
      cases hs <;> simp [assign])

theorem step_output_le (w:ℕ) (p:Program) (s τ:SparseState)
    (hs:step w p s=some τ):τ.out.length≤ s.out.length + 1:=by
  obtain ⟨i,_,he⟩:=Option.bind_eq_some_iff.mp hs
  exact effect_output_le w i s τ he

theorem run_output_le (w:ℕ) (p:Program) (t:ℕ) (s τ:SparseState)
    (hs:run w p t s=some τ):τ.out.length≤ s.out.length + t:=by
  induction t generalizing s τ with
  | zero => cases hs; omega
  | succ t ih =>
    obtain ⟨ν,hstep,hrest⟩:=Option.bind_eq_some_iff.mp hs
    have hfirst:=step_output_le w p s ν hstep
    have hlast:=ih ν τ hrest
    omega

end Lax455465Proofs.SparseBounds

end

section

namespace Lax455465Proofs.RamUnsignedBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

@[simp] theorem length_encode (qs:List ℚ≥0):(encode qs).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

end Lax455465Proofs.RamUnsignedBuffer

end

section

namespace Lax455465Proofs.RamFrames

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem array_length {c:Com} {σ τ:Env} {k:ℕ} (h:BigStep c σ τ k) (a:String):
    (τ.arrs a).length=(σ.arrs a).length:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [length_arrs_setArr]
  | seq _ _ ih ih' => rw [ih',ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih',ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_array_length {B K:ℕ} {c:Com} {σ τ:Env} (h:Run B c σ τ K) (a:String):
    (τ.arrs a).length=(σ.arrs a).length:=by
  obtain ⟨_,_,hs⟩:=h.bigStep
  exact array_length hs a

theorem keep_scalar {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (h:Spec B P c Q K) (x:String) (v:ℕ) (hx:x∉ c.wvars):
    Spec B (fun σ => P σ∧ σ.vars x=v) c (fun σ τ => Q σ τ∧ τ.vars x=v) K:=by
  rintro σ ⟨hp,hv⟩
  obtain ⟨τ,hr,hq⟩:=h σ hp
  exact ⟨τ,hr,hq, (hr.frame_var x hx).trans hv⟩

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem zero_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zero (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zero σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zero σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5825_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g5825_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5825_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5825_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

theorem one_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) one (fun _ τ => FractionOutput 1 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((1:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c8:Nat:=c4 c7 c7; let c9:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B one σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B one σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B one σ c3 (c4 c6 c8) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c9 c10) σ c1 c3 c6 c8 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5826_0_0_0))) (RunStep.seq B c9 c10 c1 c2 c3 c7 c7 (RunStep.assign B c1 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c1 h1)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5826_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5826_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5826_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

end Lax455465Proofs.RamFractionPrimitives

end

section

namespace Lax455465Proofs.RamWordBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

private theorem prefix_set (words buffer:List ℕ) (value:ℕ)
    (h:∀ i (hi:i < words.length),buffer[i]?=some words[i])
    (hroom:words.length < buffer.length):
    ∀ i (hi:i < (words ++ [value]).length),
      (buffer.set words.length value)[i]?=some (words ++ [value])[i]:=by
  intro i hi
  by_cases hlt:i < words.length
  · rw [← List.getElem_append_left' hlt,List.getElem?_set_ne (by omega:words.length ≠ i)]
    exact h i hlt
  · have he:i=words.length:=by simp only [List.length_append,List.length_singleton] at hi; omega
    subst i
    simp [List.getElem?_set_self hroom]

theorem append_spec (B:ℕ) (array cursor:String) (words:List ℕ) (value:ℕ) (e:Expr)
    (h1:1 < B) (hlen:words.length + 1 < B):
    Spec B (fun σ => Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length < (σ.arrs array).length∧ e.evalB B σ=some value) (append array cursor e)
      (fun _ τ => Prefix (words ++ [value]) array τ∧ τ.vars cursor=words.length + 1)
      (e.size + 6):=by
  rintro σ ⟨hprefix,hcursor,hroom,he⟩
  have hindex:(Expr.var cursor).evalB B σ=some words.length:=by
    rw [evalB_var_iff]
    exact ⟨hcursor.symm,hcursor ▸ (by omega:words.length < B)⟩
  have hstore:=Run.store hindex he hroom
  let ν:=σ.setArr array words.length value
  have hcounter:(Expr.add (.var cursor) (.lit 1)).evalB B ν=some (words.length + 1):=by
    apply evalB_bin (op:=.add) _ (evalB_lit h1) hlen
    rw [evalB_var_iff]
    exact ⟨by simpa [ν] using hcursor.symm,by simp [ν,hcursor]; omega⟩
  have hnext:=Run.assign (x:=cursor) hcounter
  refine ⟨ν.setVar cursor (words.length + 1), (hstore.seq hnext).mono (by simp [Expr.size]; omega), ?_⟩
  constructor
  · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_true] using
      prefix_set words (σ.arrs array) value hprefix hroom
  · simp

end Lax455465Proofs.RamWordBuffer

end

section

namespace Lax455465Proofs.RamVirtualTraceBounds

open Lax808846.Ram SparseRam RamVirtualInstruction

theorem literals_mono (i:Instr) {A B:ℕ} (h:LiteralsFit A i) (hab:A≤ B):
    LiteralsFit B i:=by
  cases i <;> simp_all [LiteralsFit] <;> omega

end Lax455465Proofs.RamVirtualTraceBounds

end

section

namespace Lax455465Proofs.RamVirtualConstants

open Lax808846.Ram RamVirtualInstruction RamVirtualTraceBounds

theorem literal_fits (i:Instr):LiteralsFit (literalBound i - 1) i:=by
  cases i <;> simp [LiteralsFit,literalBound]

theorem length_bound (p:Program):p.length + 1 < allowance p:=by
  unfold allowance
  omega

theorem literals_fit (p:Program):∀ i∈ p,LiteralsFit (allowance p - 1) i:=by
  intro i hi
  have hsum:literalBound i≤ (p.map literalBound).sum:=List.single_le_sum
    (fun j hj => Nat.zero_le _) (literalBound i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
  exact literals_mono i (literal_fits i) (by unfold allowance; omega)

end Lax455465Proofs.RamVirtualConstants

end

section

namespace Lax455465Proofs.RamBitSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem word_spec (B v:ℕ) (h2:2 < B) (hv:v < B):
    Spec B (fun σ => σ.vars "size.value"=v) word
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 6):=by
  let I:=fun σ:Env => σ.vars "size.value" ≤ v∧
    σ.vars "size.count" + (σ.vars "size.value").size=v.size
  have hs:v.size≤ v:=Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hlo:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => I τ∧ (Cond.lt (.lit 0) (.var "size.value")).evalB B τ=some false)
      (12 * v.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "size.value").size) 8
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))⟩
    · rintro σ ⟨hI,hcond⟩
      have hval:=hI.1.trans_lt hv
      have hp:0 < σ.vars "size.value" :=by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var hval)] at hcond
        simpa using hcond
      have hhalf:=WordSize.size_half (σ.vars "size.value") hp
      have hcounter:σ.vars "size.count" + 1 < B:=by
        have hsz:=Nat.size_pos.mpr hp
        have heq:=hI.2
        omega
      have hdiv:=(Nat.div_le_self (σ.vars "size.value") 2).trans_lt hval
      have hle:=(Nat.div_le_self (σ.vars "size.value") 2).trans hI.1
      (expose_names;
        (refine let c0:Env→ Prop:=(fun (σ_1 σ':Env) => And (I σ') (Nat.lt (Nat.size (Env.vars σ' "size.value")) (Nat.size (Env.vars σ_1 "size.value")))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "size.value") ((2:Nat)); let c2:Env:=Env.setVar σ "size.value" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=Env.vars c2 "size.count"; let c5:Nat:=c3 c4 ((1:Nat)); let c6:Env:=Env.setVar c2 "size.count" c5; let c7:Nat→ Nat:=c3 ((1:Nat)); let c8:Expr:=Expr.div (Expr.var "size.value") (Expr.lit ((2:Nat))); let c9:Nat:=c7 (Expr.size c8); let c10:Expr:=Expr.add (Expr.var "size.count") (Expr.lit ((1:Nat))); let c11:Nat:=c7 (Expr.size c10); @Exists.intro Env (fun (σ':Env) => And (Run B wordStep σ σ' ((8:Nat))) (c0 σ')) c6 (@And.intro (Run B wordStep σ c6 ((8:Nat))) (c0 c6) (RunStep.mono B wordStep σ c6 (c3 c9 c11) ((8:Nat)) (RunStep.seq B (Com.assign "size.value" c8) (Com.assign "size.count" c10) σ c2 c6 c9 c11 (RunStep.assign B σ "size.value" c8 c1 (RunStep.eval_div B σ (Expr.var "size.value") (Expr.lit ((2:Nat))) (Env.vars σ "size.value") ((2:Nat)) (RunStep.eval_var B σ "size.value" hval) (RunStep.eval_lit B ((2:Nat)) σ h2) hdiv)) (RunStep.assign B c2 "size.count" c10 c5 (RunStep.eval_add B c2 (Expr.var "size.count") (Expr.lit ((1:Nat))) c4 ((1:Nat)) (RunStep.eval_var B c2 "size.count" (?nAX_g6023_0_0_0)) (RunStep.eval_lit B ((1:Nat)) c2 (?nAX_g6023_0_0_1)) (?nAX_g6023_0_0_2)))) (?nAX_g6023_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [I]
      all_goals omega
    · rintro σ ⟨hvalue,hcount⟩
      simp [I,hvalue,hcount]
    · rintro σ ⟨hvalue,hcount⟩
      simp [hvalue]
  have hfinish:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 4):=hlo.post (by
    rintro σ τ _ ⟨hI,hcond⟩
    have hzero:τ.vars "size.value"=0:=by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))] at hcond
      simpa using hcond
    exact ⟨hzero,by simpa only [hzero,Nat.size_zero,Nat.add_zero] using hI.2⟩)
  rintro σ hvalue
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "size.count" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B wordLoop c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((12:Nat)) (Nat.size v)); let c4:Nat:=c3 ((4:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "size.value") ((0:Nat))) (@Eq Nat (Env.vars σ' "size.count") (Nat.size v))); let c6:Nat:=c3 ((6:Nat)); let c7:Env→ Env→ Prop:=fun (x τ:Env) => And (@Eq Nat (Env.vars τ "size.value") ((0:Nat))) (@Eq Nat (Env.vars τ "size.count") (Nat.size v)); let c8:Env→ Prop:=c7 σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B word σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:String→ Nat:=Env.vars c0; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "size.value") v) (@Eq Nat (Env.vars σ_1 "size.count") ((0:Nat)))) wordLoop c7 c4 hfinish c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c10) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B word σ w c6) (c8 w) (RunStep.mono B word σ w (c2 c12 c4) c6 (RunStep.seq B (Com.assign "size.count" (Expr.lit ((0:Nat)))) wordLoop σ c0 w c12 c4 (RunStep.assign B σ "size.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6023_1_0_0))) left) (?nAX_g6023_1_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

private theorem take_size_le (xs:List ℕ) (i:ℕ):
    Lax759944.BinaryWordEncoding.bitSize (xs.take i)≤ Lax759944.BinaryWordEncoding.bitSize xs:=by
  have h:=WordSize.bitSize_append (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at h
  omega

private theorem take_size_step (xs:List ℕ) (i:ℕ) (hi:i < xs.length):
    Lax759944.BinaryWordEncoding.bitSize (xs.take (i + 1)) =
      Lax759944.BinaryWordEncoding.bitSize (xs.take i) + xs[i].size + 1:=by
  rw [List.take_succ_eq_append_getElem hi,WordSize.bitSize_append,WordSize.bitSize_cons,
    WordSize.bitSize_nil]
  omega

open RamVirtualState Lax759944.BinaryWordEncoding

def ArrayInvariant (xs:List ℕ) (data lengthVar:String) (σ:Env):Prop:=
  σ.vars lengthVar=xs.length∧ σ.vars "size.i" ≤ xs.length∧
  σ.vars "size.total"=bitSize (xs.take (σ.vars "size.i"))∧ Prefix xs data σ

theorem arrayStep_spec (B:ℕ) (xs:List ℕ) (data lengthVar:String)
    (hfresh:∀ x∈ ["size.i", "size.value", "size.count", "size.total"],x ≠ lengthVar) (h2:2 < B) (hlen:xs.length < B)
    (hsize:bitSize xs + 1 < B) (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => ArrayInvariant xs data lengthVar σ∧ σ.vars "size.i" < xs.length) (arrayStep data)
      (fun σ τ => ArrayInvariant xs data lengthVar τ∧ τ.vars "size.i"=σ.vars "size.i" + 1)
      (12 * bitSize xs + 19):=by
  have hfi:=hfresh "size.i" (by simp)
  have hfv:=hfresh "size.value" (by simp)
  have hfc:=hfresh "size.count" (by simp)
  have hft:=hfresh "size.total" (by simp)
  have hfi':=Ne.symm hfi
  have hfv':=Ne.symm hfv
  have hfc':=Ne.symm hfc
  have hft':=Ne.symm hft
  rintro σ ⟨⟨hcount,hi,htotal,hp⟩,hpos⟩
  let i:=σ.vars "size.i"
  let value:=xs[i]
  have hvalue:value < B:=hwords _ (List.getElem_mem hpos)
  have hget:=hp i hpos
  have harray:i < (σ.arrs data).length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have hiB:σ.vars "size.i" < B:=hpos.trans hlen
  have hread:(Expr.get data (.var "size.i")).evalB B σ=some value:=by
    rw [evalB_get_iff]
    exact ⟨i,evalB_var hiB,hget,hvalue⟩
  let ν:=σ.setVar "size.value" value
  have hload:Run B (.assign "size.value" (.get data (.var "size.i"))) σ ν 3:=
    Run.assign hread
  obtain ⟨μ,hword,hzero,hbits⟩:=word_spec B value h2 hvalue ν (by simp [ν])
  have hiμ:μ.vars "size.i"=i:=(hword.frame_var _ (by simp [word,wordLoop,wordStep,Com.wvars])).trans
    (by simp [ν,i])
  have htotalμ:μ.vars "size.total"=bitSize (xs.take i):=
    (hword.frame_var _ (by simp [word,wordLoop,wordStep,Com.wvars])).trans (by simpa [ν,i] using htotal)
  have hlenμ:μ.vars lengthVar=xs.length:=
    (hword.frame_var _ (by simp [word,wordLoop,wordStep,Com.wvars,Ne.symm hfv,Ne.symm hfc])).trans (by simpa [ν,hfv,Ne.symm hfv] using hcount)
  have hdataμ:=hword.frame_arr data (by simp [word,wordLoop,wordStep,Com.warrs])
  have hpμ:Prefix xs data μ:=by simpa only [Prefix,hdataμ,ν,arrs_setVar] using hp
  have hstep:=take_size_step xs i hpos
  have hbound:=take_size_le xs (i + 1)
  have hsum:bitSize (xs.take i) + value.size + 1 < B:=by dsimp only [value]; omega
  have htotalB:bitSize (xs.take i) < B:=(take_size_le xs i).trans_lt (by omega)
  have hcountB:value.size < B:=by
    have hs:=WordSize.member_size xs value (List.getElem_mem hpos)
    omega
  have hiNext:i + 1 < B:=by omega
  have hfinish:Spec B (fun τ => τ.vars "size.i"=i∧ τ.vars "size.total"=bitSize (xs.take i)∧
      τ.vars "size.count"=value.size∧ τ.vars lengthVar=xs.length∧ Prefix xs data τ)
      (.seq (.assign "size.total" (.add (.add (.var "size.total") (.var "size.count")) (.lit 1)))
        (.assign "size.i" (.add (.var "size.i") (.lit 1))))
      (fun _ τ => ArrayInvariant xs data lengthVar τ∧ τ.vars "size.i"=i + 1) 10:=by
    rintro τ ⟨hiτ,htτ,hcτ,hlτ,hpτ⟩
    (expose_names;
      (refine let c0:Expr:=Expr.add (Expr.add (Expr.var "size.total") (Expr.var "size.count")) (Expr.lit ((1:Nat))); let c1:Com:=Com.assign "size.total" c0; let c2:Expr:=Expr.add (Expr.var "size.i") (Expr.lit ((1:Nat))); let c3:Com:=Com.assign "size.i" c2; let c4:Com:=Com.seq c1 c3; let c5:Env→ Nat→ Prop:=Run B c4 τ; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=c6 i ((1:Nat)); let c8:Env→ Prop:=(fun (x τ_1:Env) => And (ArrayInvariant xs data lengthVar τ_1) (@Eq Nat (Env.vars τ_1 "size.i") c7)) τ; let c9:Nat:=c6 (Env.vars τ "size.total") (Env.vars τ "size.count"); let c10:Nat:=c6 c9 ((1:Nat)); let c11:Env:=Env.setVar τ "size.total" c10; let c12:Nat:=Env.vars c11 "size.i"; let c13:Nat:=c6 c12 ((1:Nat)); let c14:Env:=Env.setVar c11 "size.i" c13; let c15:Nat→ Nat:=c6 ((1:Nat)); let c16:Nat:=c15 (Expr.size c0); let c17:Nat:=c15 (Expr.size c2); @Exists.intro Env (fun (σ':Env) => And (c5 σ' ((10:Nat))) (c8 σ')) c14 (@And.intro (c5 c14 ((10:Nat))) (c8 c14) (RunStep.mono B c4 τ c14 (c6 c16 c17) ((10:Nat)) (RunStep.seq B c1 c3 τ c11 c14 c16 c17 (RunStep.assign B τ "size.total" c0 c10 (RunStep.eval_add B τ (Expr.add (Expr.var "size.total") (Expr.var "size.count")) (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_add B τ (Expr.var "size.total") (Expr.var "size.count") (Env.vars τ "size.total") (Env.vars τ "size.count") (RunStep.eval_var B τ "size.total" (?nAX_g6028_0_0_0)) (RunStep.eval_var B τ "size.count" (?nAX_g6028_0_0_1)) (?nAX_g6028_0_0_2)) (RunStep.eval_lit B ((1:Nat)) τ (?nAX_g6028_0_0_3)) (?nAX_g6028_0_0_4))) (RunStep.assign B c11 "size.i" c2 c13 (RunStep.eval_add B c11 (Expr.var "size.i") (Expr.lit ((1:Nat))) c12 ((1:Nat)) (RunStep.eval_var B c11 "size.i" (?nAX_g6028_0_0_5)) (RunStep.eval_lit B ((1:Nat)) c11 (?nAX_g6028_0_0_6)) (?nAX_g6028_0_0_7)))) (?nAX_g6028_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6028_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear hload); (all_goals try clear hword))
    all_goals simp_all [ArrayInvariant,Prefix,value]
    all_goals omega
  obtain ⟨τ,hfinish,hpost⟩:=hfinish μ ⟨hiμ,htotalμ,hbits,hlenμ,hpμ⟩
  exact ⟨τ, (hload.seq (hword.seq hfinish)).mono (by
    have hs:=WordSize.member_size xs value (List.getElem_mem hpos)
    omega),hpost⟩

theorem array_spec (B:ℕ) (xs:List ℕ) (data lengthVar:String)
    (hfresh:∀ x∈ ["size.i", "size.value", "size.count", "size.total"],x ≠ lengthVar) (h2:2 < B) (hlen:xs.length < B)
    (hsize:bitSize xs + 1 < B) (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => σ.vars lengthVar=xs.length∧ Prefix xs data σ) (array data lengthVar)
      (fun _ τ => τ.vars "size.total"=bitSize xs)
      ((12 * bitSize xs + 23) * xs.length + 8):=by
  have hfi:=hfresh "size.i" (by simp)
  have hfv:=hfresh "size.value" (by simp)
  have hfc:=hfresh "size.count" (by simp)
  have hft:=hfresh "size.total" (by simp)
  have hfi':=Ne.symm hfi
  have hfv':=Ne.symm hfv
  have hfc':=Ne.symm hfc
  have hft':=Ne.symm hft
  have hscan:=Spec.forRangeZero "size.i" lengthVar (ArrayInvariant xs data lengthVar) xs.length
    (12 * bitSize xs + 19) hlen (fun _ h => h.2.1) (fun _ h => h.1)
    (arrayStep_spec B xs data lengthVar hfresh h2 hlen hsize hwords)
  have hfinish:Spec B (fun σ => ArrayInvariant xs data lengthVar (σ.setVar "size.i" 0))
      (.seq (.assign "size.i" (.lit 0)) (.while (.lt (.var "size.i") (.var lengthVar)) (arrayStep data)))
      (fun _ τ => τ.vars "size.total"=bitSize xs) ((12 * bitSize xs + 23) * xs.length + 6):=
    hscan.post (fun _ τ _ h => by simpa only [h.2,List.take_length] using h.1.2.2.1)
  rintro σ ⟨hlenσ,hpσ⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "size.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "size.i") (Expr.var lengthVar)) (arrayStep data)); let c1:Env:=Env.setVar σ "size.total" ((0:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat→ Nat:=c3 (c4 (c3 (c4 ((12:Nat)) (bitSize xs)) ((23:Nat))) (@List.length Nat xs)); let c6:Nat:=c5 ((6:Nat)); let c7:Env→ Prop:=fun (σ':Env) => And (c2 σ' c6) (@Eq Nat (Env.vars σ' "size.total") (bitSize xs)); let c8:Nat:=c5 ((8:Nat)); let c9:Env→ Env→ Prop:=fun (x τ:Env) => @Eq Nat (Env.vars τ "size.total") (bitSize xs); let c10:Env→ Prop:=c9 σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B (array data lengthVar) σ σ' c8) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => c12) (RunStep.use B (fun (σ_1:Env) => ArrayInvariant xs data lengthVar (Env.setVar σ_1 "size.i" ((0:Nat)))) c0 c9 c6 hfinish c1 ?_) fun (w:Env) (h:And (c2 w c6) (@Eq Nat (Env.vars w "size.total") (bitSize xs))) => let c0_1:Prop:= @Eq Nat (Env.vars w "size.total") (bitSize xs); @And.casesOn (c2 w c6) c0_1 (fun (x:And (c2 w c6) c0_1) => c12) h fun (left:c2 w c6) (right:c0_1) => @Exists.intro Env c11 w (@And.intro (Run B (array data lengthVar) σ w c8) (c10 w) (RunStep.mono B (array data lengthVar) σ w (c3 c13 c6) c8 (RunStep.seq B (Com.assign "size.total" (Expr.lit ((0:Nat)))) c0 σ c1 w c13 c6 (RunStep.assign B σ "size.total" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6030_0_0_0))) left) (?nAX_g6030_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6030_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6030_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [ArrayInvariant,Prefix,WordSize.bitSize_nil]

end Lax455465Proofs.RamBitSize

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem argument_frame (coefficients:List ℕ):"poly.argument" ∉ (command coefficients).wvars:=by
  induction coefficients with
  | nil => simp [command,Com.wvars]
  | cons a rest ih => simp [command,Com.wvars,ih]

theorem variable_frame (coefficients:List ℕ) (x:String) (hx:x ≠ "poly.value"):
    x∉ (command coefficients).wvars:=by
  induction coefficients with
  | nil => simp [command,Com.wvars,hx]
  | cons a rest ih => simp [command,Com.wvars,ih,hx]

theorem arrays_frame (coefficients:List ℕ):(command coefficients).warrs=[]:=by
  induction coefficients with
  | nil => simp [command,Com.warrs]
  | cons a rest ih => simp [command,Com.warrs,ih]

theorem value_mono (coefficients:List ℕ) {x y:ℕ} (h:x≤ y):
    value coefficients x≤ value coefficients y:=by
  induction coefficients with
  | nil => rfl
  | cons a rest ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

theorem command_spec (B:ℕ) (coefficients:List ℕ) (x:ℕ)
    (hB:0 < B) (hx:x < B) (hvalue:value coefficients (x + 1) < B):
    Spec B (fun σ => σ.vars "poly.argument"=x) (command coefficients)
      (fun _ τ => τ.vars "poly.value"=value coefficients x)
      (6 * coefficients.length + 2):=by
  induction coefficients with
  | nil =>
    intro σ hσ
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Nat.mul ((6:Nat)) (@List.length Nat (@List.nil Nat))) ((2:Nat)); let c2:Env→ Prop:=(fun (x_1 τ:Env) => @Eq Nat (Env.vars τ "poly.value") (value (@List.nil Nat) x)) σ; let c3:Env:=Env.setVar σ "poly.value" ((0:Nat)); @Exists.intro Env (fun (σ':Env) => And (Run B (command (@List.nil Nat)) σ σ' c1) (c2 σ')) c3 (@And.intro (Run B (command (@List.nil Nat)) σ c3 c1) (c2 c3) (RunStep.mono B (command (@List.nil Nat)) σ c3 (c0 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat))))) c1 (RunStep.assign B σ "poly.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hB)) (?nAX_g6037_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6037_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [value]
  | cons a rest ih =>
    have htail:value rest (x + 1)≤ value (a::rest) (x + 1):=by
      simp only [value]
      nlinarith
    have hrest:=ih (htail.trans_lt hvalue)
    have hrest':=RamFrames.keep_scalar hrest "poly.argument" x (argument_frame rest)
    have hsmall:=value_mono (a::rest) (show x≤ x + 1 by omega)
    have hresult:a + x * value rest x < B:=hsmall.trans_lt hvalue
    have ha:a < B:=by omega
    have hproduct:x * value rest x < B:=by omega
    have htailSmall:=value_mono rest (show x≤ x + 1 by omega)
    have hv:value rest x < B:=htailSmall.trans_lt (htail.trans_lt hvalue)
    rintro σ hσ
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((6:Nat)); let c3:Nat:=c0 (c2 (@List.length Nat rest)) ((2:Nat)); let c4:Env→ Prop:=fun (σ':Env) => And (Run B (command rest) σ σ' c3) (And (@Eq Nat (Env.vars σ' "poly.value") (value rest x)) (@Eq Nat (Env.vars σ' "poly.argument") x)); let c5:Env→ Nat→ Prop:=Run B (command (@List.cons Nat a rest)) σ; let c6:Nat:=c0 (c2 (@List.length Nat (@List.cons Nat a rest))) ((2:Nat)); let c7:Env→ Prop:=(fun (x_1 τ:Env) => @Eq Nat (Env.vars τ "poly.value") (value (@List.cons Nat a rest) x)) σ; let c8:Env→ Prop:=fun (σ':Env) => And (c5 σ' c6) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Expr:=Expr.add (Expr.lit a) (Expr.mul (Expr.var "poly.argument") (Expr.var "poly.value")); let c11:Nat:=c0 ((1:Nat)) (Expr.size c10); @Exists.casesOn Env c4 (fun (x_1:@Exists Env c4) => c9) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "poly.argument") x) (@Eq Nat (Env.vars σ_1 "poly.argument") x)) (command rest) (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "poly.value") (value rest x)) (@Eq Nat (Env.vars τ "poly.argument") x)) c3 hrest' σ ?_) fun (w:Env) (h:And (Run B (command rest) σ w c3) (And (@Eq Nat (Env.vars w "poly.value") (value rest x)) (@Eq Nat (Env.vars w "poly.argument") x))) => let c0_1:Prop:=Run B (command rest) σ w c3; let c1_1:Prop:=And (@Eq Nat (Env.vars w "poly.value") (value rest x)) (@Eq Nat (Env.vars w "poly.argument") x); let c2_1:Nat:=c1 (Env.vars w "poly.argument") (Env.vars w "poly.value"); let c3_1:Nat:=c0 a c2_1; let c4_1:Env:=Env.setVar w "poly.value" c3_1; @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c9) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c8 c4_1 (@And.intro (c5 c4_1 c6) (c7 c4_1) (RunStep.mono B (command (@List.cons Nat a rest)) σ c4_1 (c0 c3 c11) c6 (RunStep.seq B (command rest) (Com.assign "poly.value" c10) σ w c4_1 c3 c11 left (RunStep.assign B w "poly.value" c10 c3_1 (RunStep.eval_add B w (Expr.lit a) (Expr.mul (Expr.var "poly.argument") (Expr.var "poly.value")) a c2_1 (RunStep.eval_lit B a w ha) (RunStep.eval_mul B w (Expr.var "poly.argument") (Expr.var "poly.value") (Env.vars w "poly.argument") (Env.vars w "poly.value") (RunStep.eval_var B w "poly.argument" (?nAX_g6037_1_0_0)) (RunStep.eval_var B w "poly.value" (?nAX_g6037_1_0_1)) ?_) ?_))) (?nAX_g6037_1_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6037_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6037_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6037_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals simp_all [value]

theorem exists_coefficients (p:Polynomial ℕ):∃ coefficients:List ℕ,
    ∀ x:ℕ,value coefficients x=p.eval x:=by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[],fun _ => by simp [value]⟩
  · intro q a _ _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    cases coefficients with
    | nil =>
      refine ⟨[a], ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp [value]
    | cons b rest =>
      refine ⟨(b + a)::rest, ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp only [value]
      omega
  · intro q _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    refine ⟨0::coefficients, ?_⟩
    intro x
    simp only [value,Nat.zero_add,hcoeff,Polynomial.eval_mul,Polynomial.eval_X,Nat.mul_comm]

end Lax455465Proofs.RamPolynomial

end

section

namespace Lax455465Proofs.RamLpInputFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Invariant (xs:List ℕ) (σ:Env):Prop:=
  σ.vars "lp.position"=xs.length∧ σ.vars "frame.i" ≤ xs.length∧
  Prefix xs "lp.word" σ∧ Prefix (xs.length::xs.take (σ.vars "frame.i")) "vm.input" σ∧
  σ.vars "vm.inputLength"=σ.vars "frame.i" + 1∧ xs.length < (σ.arrs "vm.input").length

theorem step_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length + 1 < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => Invariant xs σ∧ σ.vars "frame.i" < xs.length) step
      (fun σ τ => Invariant xs τ∧ τ.vars "frame.i"=σ.vars "frame.i" + 1) 12:=by
  rintro σ ⟨⟨hpos,hi,hsource,hp,hcursor,hroom⟩,hlt⟩
  let i:=σ.vars "frame.i"
  let value:=xs[i]
  have hi':i≤ xs.length:=hi
  have hlt':i < xs.length:=hlt
  have hv:=hwords xs[i] (List.getElem_mem hlt)
  have hget:=hsource i hlt
  have hsourceRoom:i < (σ.arrs "lp.word").length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have he:(Expr.get "lp.word" (.var "frame.i")).evalB B σ=some value:=by
    rw [evalB_get_iff]
    exact ⟨i,evalB_var (by omega),hget,hv⟩
  have hprefixlen:(xs.length::xs.take i).length=i + 1:=by simp [List.length_take,Nat.min_eq_left hi']
  obtain ⟨ν,hwrite,hpost⟩:=RamWordBuffer.append_spec B "vm.input" "vm.inputLength"
    (xs.length::xs.take i) value (.get "lp.word" (.var "frame.i")) h1
    (by rw [hprefixlen]; omega) σ ⟨hp,by rwa [hprefixlen],by rw [hprefixlen]; omega,he⟩
  have hiν:ν.vars "frame.i"=i:=(hwrite.frame_var _ (by simp [RamWordBuffer.append,Com.wvars])).trans rfl
  have hposν:=(hwrite.frame_var "lp.position" (by simp [RamWordBuffer.append,Com.wvars])).trans hpos
  have hsourceν:Prefix xs "lp.word" ν:=by
    simpa only [Prefix,hwrite.frame_arr "lp.word" (by simp [RamWordBuffer.append,Com.warrs])] using hsource
  have hroomν:xs.length < (ν.arrs "vm.input").length:=by
    rwa [RamFrames.run_array_length hwrite "vm.input"]
  have htake:xs.take (i + 1)=xs.take i ++ [value]:=List.take_succ_eq_append_getElem hlt'
  have hpν:Prefix (xs.length::xs.take (i + 1)) "vm.input" ν:=by
    rw [htake]
    simpa only [List.cons_append] using hpost.1
  have hlenν:ν.vars "vm.inputLength"=i + 1 + 1:=by simpa only [hprefixlen] using hpost.2
  have hiNext:i + 1 < B:=by omega
  have hinc:Run B (.assign "frame.i" (.add (.var "frame.i") (.lit 1))) ν (ν.setVar "frame.i" (i + 1)) 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i < B)⟩)
      (evalB_lit h1) hiNext)
  refine ⟨ν.setVar "frame.i" (i + 1), (hwrite.seq hinc).mono (by simp [Expr.size]), ?_⟩
  constructor
  · simpa only [Invariant,Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_true,if_false]
      using And.intro hposν (And.intro (by omega:i + 1≤ xs.length)
        (And.intro hsourceν (And.intro hpν (And.intro hlenν hroomν))))
  · simp [i]

theorem command_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length + 1 < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => Prefix xs "lp.word" σ∧ σ.vars "lp.position"=xs.length∧
      xs.length < (σ.arrs "vm.input").length) command
      (fun _ τ => Prefix (xs.length::xs) "vm.input" τ∧ τ.vars "vm.inputLength"=xs.length + 1)
      (16 * xs.length + 15):=by
  have hscan:=Spec.forRangeZero "frame.i" "lp.position" (Invariant xs) xs.length 12
    (by omega) (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B xs h1 hlen hwords)
  have hfinish:Spec B (fun σ => Invariant xs (σ.setVar "frame.i" 0))
      (.seq (.assign "frame.i" (.lit 0)) (.while (.lt (.var "frame.i") (.var "lp.position")) step))
      (fun _ τ => Prefix (xs.length::xs) "vm.input" τ∧ τ.vars "vm.inputLength"=xs.length + 1)
      (16 * xs.length + 6):=hscan.post (fun _ τ _ h => by
        exact ⟨by simpa only [h.2,List.take_length] using h.1.2.2.2.1,by simpa only [h.2] using h.1.2.2.2.2.1⟩)
  have hprefix:=RamWordBuffer.append_spec B "vm.input" "vm.inputLength" [] xs.length (.var "lp.position") h1
    (by simp; omega)
  rintro σ ⟨hp,hpos,hroom⟩
  let ν:=σ.setVar "vm.inputLength" 0
  have hzero:Run B (.assign "vm.inputLength" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨μ,hhead,hheadPost⟩:=hprefix ν ⟨by intro i hi; simp at hi,by simp [ν],
    by simp [ν]; omega,by rw [evalB_var_iff]; exact ⟨by simp [ν,hpos],by simp [ν,hpos]; omega⟩⟩
  have hposμ:μ.vars "lp.position"=xs.length:=
    (hhead.frame_var _ (by simp [RamWordBuffer.append,Com.wvars])).trans (by simp [ν,hpos])
  have hpμ:Prefix xs "lp.word" μ:=by
    simpa only [Prefix,hhead.frame_arr "lp.word" (by simp [RamWordBuffer.append,Com.warrs]),
      ν,arrs_setVar] using hp
  have hroomμ:xs.length < (μ.arrs "vm.input").length:=by
    rw [RamFrames.run_array_length hhead "vm.input"]
    simpa only [ν,arrs_setVar] using hroom
  have hpre:Invariant xs (μ.setVar "frame.i" 0):=by
    simpa only [Invariant,Prefix,vars_setVar,String.reduceEq,if_true,if_false,
      arrs_setVar,List.take_zero,List.length_nil,List.nil_append,Nat.zero_add]
      using And.intro hposμ (And.intro (Nat.zero_le xs.length)
        (And.intro hpμ (And.intro hheadPost.1 (And.intro hheadPost.2 hroomμ))))
  obtain ⟨τ,hscan,hpost⟩:=hfinish μ hpre
  exact ⟨τ, (hzero.seq (hhead.seq hscan)).mono (by simp [Expr.size]; omega),hpost⟩

end Lax455465Proofs.RamLpInputFrame

end

section

namespace Lax455465Proofs.RamLpPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax759944.BinaryWordEncoding

theorem command_spec (B:ℕ) (coefficients:List ℕ) (xs:List ℕ) (h2:2 < B)
    (hlen:xs.length + 1 < B) (hsize:bitSize xs + 1 < B) (hwords:∀ x∈ xs,x < B)
    (hvalue:RamPolynomial.value coefficients (bitSize xs + 1) < B):
    Spec B (fun σ => Prefix xs "lp.word" σ∧ σ.vars "lp.position"=xs.length∧
      xs.length < (σ.arrs "vm.input").length) (command coefficients)
      (fun _ τ => τ.vars "vm.width"=RamPolynomial.value coefficients (bitSize xs)∧
        Prefix (xs.length::xs) "vm.input" τ∧ τ.vars "vm.inputLength"=xs.length + 1)
      ((12 * bitSize xs + 39) * xs.length + 6 * coefficients.length + 29):=by
  rintro σ ⟨hp,hpos,hroom⟩
  obtain ⟨ν,hcount,htotal⟩:=RamBitSize.array_spec B xs "lp.word" "lp.position"
    (by decide) h2 (by omega) hsize hwords σ ⟨hpos,hp⟩
  let δ:=ν.setVar "poly.argument" (bitSize xs)
  have harg:Run B (.assign "poly.argument" (.var "size.total")) ν δ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨htotal.symm,htotal ▸ (by omega:bitSize xs < B)⟩)
  obtain ⟨μ,hpoly,hpolyValue⟩:=RamPolynomial.command_spec B coefficients (bitSize xs)
    (by omega) (by omega) hvalue δ (by simp [δ])
  have hv:RamPolynomial.value coefficients (bitSize xs) < B:=
    (RamPolynomial.value_mono coefficients (show bitSize xs≤ bitSize xs + 1 by omega)).trans_lt hvalue
  let ε:=μ.setVar "vm.width" (RamPolynomial.value coefficients (bitSize xs))
  have hwidth:Run B (.assign "vm.width" (.var "poly.value")) μ ε 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hpolyValue.symm,hpolyValue ▸ hv⟩)
  have hpν:Prefix xs "lp.word" ν:=by
    simpa only [Prefix,hcount.frame_arr "lp.word" (by simp [RamBitSize.array,
      RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,Com.warrs])] using hp
  have hposν:=(hcount.frame_var "lp.position" (by simp [RamBitSize.array,RamBitSize.arrayStep,
    RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,Com.wvars])).trans hpos
  have hpμ:Prefix xs "lp.word" μ:=by
    simpa only [Prefix,hpoly.frame_arr "lp.word" (by simp [RamPolynomial.arrays_frame]),δ,arrs_setVar] using hpν
  have hposμ:=(hpoly.frame_var "lp.position" (RamPolynomial.variable_frame coefficients _ (by decide))).trans
    (show δ.vars "lp.position"=xs.length by simpa [δ] using hposν)
  have hpε:Prefix xs "lp.word" ε:=by simpa only [Prefix,ε,arrs_setVar] using hpμ
  have hposε:ε.vars "lp.position"=xs.length:=by simpa [ε] using hposμ
  have hroomε:xs.length < (ε.arrs "vm.input").length:=by
    rw [show ε.arrs "vm.input"=μ.arrs "vm.input" from rfl,
      RamFrames.run_array_length hpoly "vm.input",show δ.arrs "vm.input"=ν.arrs "vm.input" from rfl,
      RamFrames.run_array_length hcount "vm.input"]
    exact hroom
  obtain ⟨τ,hframe,hpost⟩:=RamLpInputFrame.command_spec B xs (by omega) hlen hwords ε ⟨hpε,hposε,hroomε⟩
  have hwτ:τ.vars "vm.width"=RamPolynomial.value coefficients (bitSize xs):=
    (hframe.frame_var "vm.width" (by simp [RamLpInputFrame.command,RamLpInputFrame.step,
      RamWordBuffer.append,Com.wvars])).trans (by simp [ε])
  refine ⟨τ, (hcount.seq (harg.seq (hpoly.seq (hwidth.seq hframe)))).mono ?_,hwτ,hpost⟩
  nlinarith

end Lax455465Proofs.RamLpPrepare

end

section

namespace Lax455465Proofs.RamUnsignedEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B:ℕ) (array cursor:String) (q:ℚ≥0) (words:List ℕ) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B) (hlen:words.length+2 < B) (hfresh:cursor ≠ "rat.d"):
    Spec B (fun σ => FractionOutput (q:ℚ) σ∧ Prefix words array σ∧
      σ.vars cursor=words.length∧ words.length+1 < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (words ++ Lax455465.RationalEncoding.encodeRational q) array τ∧
        τ.vars cursor=words.length+2) 14:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  have hnum:σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hf.2.1
  have hden:σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hf.2.2.1
  have hfirst:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B array cursor words q.num (.var "rat.n") h1 (by omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars,Ne.symm hfresh])
  obtain ⟨ν,hrn,hnPost⟩:=hfirst σ ⟨⟨hp,hpos,by omega,
    by rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hn⟩⟩,hden⟩
  have hroomν:(words ++ [q.num]).length < (ν.arrs array).length:=by
    rw [RamFrames.run_array_length hrn array,List.length_append,List.length_singleton]; exact hroom
  obtain ⟨τ,hrd,hdPost⟩:=RamWordBuffer.append_spec B array cursor (words ++ [q.num]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ν
      ⟨hnPost.1.1,by simpa only [List.length_append,List.length_singleton] using hnPost.1.2,hroomν,
        by rw [evalB_var_iff]; exact ⟨hnPost.2.symm,hnPost.2 ▸ hd⟩⟩
  refine ⟨τ,hrn.seq hrd,?_,?_⟩
  · simpa only [Lax455465.RationalEncoding.encodeRational,List.append_assoc,List.cons_append,List.nil_append] using hdPost.1
  · simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using hdPost.2

end Lax455465Proofs.RamUnsignedEncoding

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def sign (q:ℚ):ℕ:=if q.num < 0 then 1 else 0

theorem value_eq (q:ℚ):fractionValue (sign q) q.num.natAbs q.den=q:=by
  have hnum:(if q.num < 0 then -((q.num.natAbs:ℕ):ℚ) else ((q.num.natAbs:ℕ):ℚ))=(q.num:ℚ):=by
    generalize q.num=z
    cases z <;> simp
  by_cases h:q.num < 0
  · simp only [if_pos h] at hnum
    simpa only [fractionValue,sign,if_pos h,if_true,hnum] using q.num_div_den
  · simp only [if_neg h] at hnum
    simpa only [fractionValue,sign,if_neg h,show ¬(0:ℕ)=1 by decide,if_false,hnum] using q.num_div_den

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

theorem command_spec (B:ℕ) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front ++ (encodeRational q ++ tail)) "vm.output" σ∧
      σ.vars "cert.cursor"=front.length) command
      (fun _ τ => FractionOutput q τ∧ τ.vars "cert.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front ++ (encodeRational q ++ tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs "vm.output").length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "cert.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ "vm.output") (Env.vars σ "cert.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "cert.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 "vm.output") c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "cert.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 "vm.output") c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "cert.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "cert.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get "vm.output" (Expr.var "cert.cursor"))); let c18:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get "vm.output" c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get "vm.output" c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "cert.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B command σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B command σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor")) c3 (RunStep.eval_get B σ "vm.output" (Expr.var "cert.cursor") (Env.vars σ "cert.cursor") (RunStep.eval_var B σ "cert.cursor" (?nAX_g6135_0_0_0)) (?nAX_g6135_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 "vm.output" c18 c6 (RunStep.eval_add B c4 (Expr.var "cert.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "cert.cursor" (?nAX_g6135_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g6135_0_0_3)) (?nAX_g6135_0_0_4)) (?nAX_g6135_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 "vm.output" c21 c10 (RunStep.eval_add B c8 (Expr.var "cert.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "cert.cursor" (?nAX_g6135_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g6135_0_0_7)) (?nAX_g6135_0_0_8)) (?nAX_g6135_0_0_9) ?_)) (RunStep.assign B c12 "cert.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "cert.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "cert.cursor" (?nAX_g6135_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g6135_0_0_11)))))) (?nAX_g6135_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6135_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax455465Proofs.RamUnsignedVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (words:List ℕ) (array cursor:String) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ RamUnsignedBuffer.encode (qs.take (σ.vars index))) array σ∧
    σ.vars cursor=words.length+2*σ.vars index∧
    words.length+2*qs.length < (σ.arrs array).length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit array cursor:String)
    (qs:List ℚ≥0) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+2*qs.length+2 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput (qs[i]:ℚ) τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:cursor∉ body.wvars)
    (hbodyArray:array∉ body.warrs)
    (hemitIndex:index∉ (RamUnsignedEncoding.command array cursor).wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B (RamUnsignedEncoding.command array cursor) σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ cursor) (hcursorDen:cursor ≠ "rat.d"):
    Spec B (fun σ => R σ∧ Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length+2*qs.length < (σ.arrs array).length) (command index limit array cursor body)
      (fun _ τ => R τ∧ Prefix (words ++ RamUnsignedBuffer.encode qs) array τ∧
        τ.vars cursor=words.length+2*qs.length) ((K+22)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words array cursor σ∧ σ.vars index < qs.length)
      (step index array cursor body) (fun σ τ => Invariant R index qs words array cursor τ∧ τ.vars index=σ.vars index+1)
      (K+18):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ RamUnsignedBuffer.encode (qs.take i)).length=words.length+2*i:=by
      simp only [List.length_append,RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars cursor=words.length+2*i:=
      (hproduce.frame_var cursor hbodyPosition).trans hpos
    have hpν:Prefix (words ++ RamUnsignedBuffer.encode (qs.take i)) array ν:=by
      simpa only [Prefix,hproduce.frame_arr array hbodyArray] using hp
    have hroomν:words.length+2*qs.length < (ν.arrs array).length:=by
      rwa [RamFrames.run_array_length hproduce array]
    obtain ⟨μ,hemit,hemitted⟩:=RamUnsignedEncoding.command_spec B array cursor qs[i] (words ++ RamUnsignedBuffer.encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) hcursorDen ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+2*qs.length < (μ.arrs array).length:=by
      rwa [RamFrames.run_array_length hemit array]
    have hpμ:Prefix (words ++ RamUnsignedBuffer.encode (qs.take (i+1))) array μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars cursor=words.length+2*(i+1):=by rw [hpLen] at hemitted; omega
    have hnext:i+1 < B:=by omega
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) hnext)
    refine ⟨μ.setVar index (i+1),hproduce.seq (hemit.seq hinc),?_,?_⟩
    · refine ⟨hset μ (i+1) hRμ,by simp; omega,?_,?_,?_⟩
      · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hpμ
      · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true] using hposμ
      · simpa only [arrs_setVar] using hroomμ
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words array cursor) qs.length (K+18)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words array cursor (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamUnsignedVector

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

theorem adjacency_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:
    (adjacency G).length=n*n:=by
  simp [adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const]

open Lax109476Proofs

end Lax263307Proofs.NativeWeightReduction

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

theorem matrix_coordinate {n:ℕ} (f:Fin n→ Fin n→ ℕ) (i j:Fin n):
    (matrix f)[i.val*n+j.val]?=some (f i j):=by
  let xs:=List.ofFn fun i => List.ofFn (f i)
  have hi:i.val< xs.length:=by simpa only [xs,List.length_ofFn] using i.isLt
  have hj:j.val< xs[i.val].length:=by simpa only [xs,List.getElem_ofFn,List.length_ofFn] using j.isLt
  have hx:=flattened_coordinate xs i.val hi j.val hj
  have hp:((xs.take i.val).map List.length).sum=i.val*n:=by
    rw [List.map_take]
    have hm:xs.map List.length=List.replicate n n:=by
      dsimp only [xs]
      rw [List.map_ofFn,←List.ofFn_const]
      congr 1
      funext v
      exact List.length_ofFn
    rw [hm]
    simp [List.take_replicate,List.sum_replicate]
  simpa only [hp,matrix,xs,List.getElem_ofFn] using hx

def row {n:ℕ} (q:Fin (n*n)):Fin n:= ⟨q.val/n,by
  have hn:0< n:=by nlinarith only [q.isLt]
  exact (Nat.div_lt_iff_lt_mul hn).mpr q.isLt⟩

def col {n:ℕ} (q:Fin (n*n)):Fin n:= ⟨q.val%n,by
  have hn:0< n:=by nlinarith only [q.isLt]
  exact Nat.mod_lt _ hn⟩

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

open Lax109476Proofs

end Lax263307Proofs.NativeBlowUp

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

theorem mask_test_bit {n:ℕ} (I:Finset (Fin n)) (j:ℕ):
    (mask I).testBit j=decide (j∈I.image Fin.val):=by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff,←Nat.mem_bitIndices,←List.mem_toFinset]
  change j∈Finset.equivBitIndices (mask I)↔ j∈I.image Fin.val
  rw [mask,Lax263307.NativeCatalog.subsetMask,Equiv.apply_symm_apply]

theorem mask_member {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    (mask I).testBit v.val=decide (v∈I):=by
  rw [mask_test_bit]
  congr 1
  simp [Finset.mem_image,Fin.val_inj]

theorem mask_empty (n:ℕ):mask (∅:Finset (Fin n))=0:=by
  simp [mask,Lax263307.NativeCatalog.subsetMask,Finset.equivBitIndices]

theorem mask_bound {n:ℕ} (I:Finset (Fin n)):mask I<2^n:=by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro hjm
  obtain ⟨v,hv,hvj⟩:=Finset.mem_image.mp hjm
  have hvn:=v.isLt
  omega

theorem mask_insert {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    mask (insert v I)=Nat.lor (mask I) (2^v.val):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (insert v I)).testBit j=((mask I) ||| (2^v.val)).testBit j
  rw [Nat.testBit_or,mask_test_bit,mask_test_bit,Nat.testBit_two_pow]
  simp only [Finset.image_insert,Finset.mem_insert]
  by_cases he:j=v.val <;> by_cases hm:j∈I.image Fin.val <;> simp [he,hm,eq_comm]

def initialSet {n:ℕ} (I:Finset (Fin n)) (i:ℕ):Finset (Fin n):=
  I.filter fun v => v.val < i

theorem prefix_zero {n:ℕ} (I:Finset (Fin n)):initialSet I 0=∅:=by simp [initialSet]

theorem prefix_full {n:ℕ} (I:Finset (Fin n)):initialSet I n=I:=by simp [initialSet]

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

theorem prefix_step {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    Nat.lor (mask (initialSet I i)) ((if (⟨i,hi⟩:Fin n)∈I then 1 else 0)*2^i)=mask (initialSet I (i+1)):=by
  rw [prefix_succ I i hi]
  by_cases h:(⟨i,hi⟩:Fin n)∈I
  · simp only [if_pos h,one_mul,mask_insert]
  · simp [h]

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "mask.i"≤ n∧
  Prefix (encodeOutput I) "subset.bits" σ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

theorem step_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant I σ∧ σ.vars "mask.i"< n) step
      (fun σ τ => Invariant I τ∧ τ.vars "mask.i"=σ.vars "mask.i"+1) 11:=by
  rintro σ ⟨⟨hn,hle,hbits,hmask⟩,hlt⟩
  let i:=σ.vars "mask.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈I then 1 else 0
  have hbit:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hbitB:bit< B:=by omega
  have hiB:i< B:=by omega
  have hpow:2^i<2^n:=Nat.pow_lt_pow_right (by omega) hlt
  have hshift:bit*2^i< B:=(by simpa only [one_mul] using Nat.mul_le_mul_right (2^i) hbit:bit*2^i≤2^i).trans_lt (hpow.trans hm)
  have hget:(σ.arrs "subset.bits")[i]?=some bit:=by
    have hh:=hbits i (by simpa [encodeOutput] using hlt)
    simpa [encodeOutput,bit] using hh
  have hprev:mask (initialSet I i)< B:=(mask_bound _).trans hm
  have hnext:mask (initialSet I (i+1))< B:=(mask_bound _).trans hm
  have hval:(Expr.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i"))).evalB B σ=
      some (mask (initialSet I (i+1))):=by
    have hh:=evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hprev⟩)
      (evalB_bin (op:=.shiftl) (evalB_get (evalB_var hiB) hget hbitB) (evalB_var hiB) hshift)
      (by change Nat.lor (mask (initialSet I i)) (bit*2^i)< B; rw [prefix_step]; exact hnext)
    simpa only [Bop.apply_or,Bop.apply_shiftl,←show σ.vars "mask.i"=i from rfl,bit,prefix_step] using hh
  let ν:=σ.setVar "mask.value" (mask (initialSet I (i+1)))
  have r1:Run B (.assign "mask.value"
      (.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i")))) σ ν 7:=
    Run.assign hval
  have hiν:ν.vars "mask.i"=i:=by simp [ν,i]
  let τ:=ν.setVar "mask.i" (i+1)
  have r2:Run B (.assign "mask.i" (.add (.var "mask.i") (.lit 1))) ν τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) (evalB_lit (by omega))
      (by change i+1< B; omega))
  have rr:=r1.seq r2
  have ht:τ.vars "mask.i"=i+1:=by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,by rw [ht]; omega,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hbits
  · simp [τ,ν]

theorem command_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ Prefix (encodeOutput I) "subset.bits" σ) command
      (fun _ τ => τ.vars "mask.value"=mask I) (15*n+8):=by
  have hloop:=Spec.forRangeZero "mask.i" "graph.n" (Invariant I) n 11 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hbits⟩
  let ν:=σ.setVar "mask.value" 0
  have r1:Run B (.assign "mask.value" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant I (ν.setVar "mask.i" 0):=by
    refine ⟨?_,by simp,hbits,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp [ν,prefix_zero,mask_empty]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
  simpa only [p2.2,prefix_full] using p2.1.2.2.2

end Lax263307Proofs.NativeMasks

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMaskUnpack

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open NativeMasks

theorem bit_value {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    Nat.land (mask I / 2^v.val) 1=if v∈I then 1 else 0:=by
  rw [Nat.land_eq,Nat.and_one_is_mod]
  have h:=mask_member I v
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  have hm:=Nat.mod_lt (mask I / 2^v.val) (by omega:0<2)
  by_cases hv:v∈I
  · simp only [hv,decide_true,decide_eq_true_eq,if_true] at h ⊢
    exact h
  · simp only [hv,decide_false,decide_eq_false_iff_not,if_false] at h ⊢
    omega

theorem prefix_card_step {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    (initialSet I (i+1)).card=(initialSet I i).card+(if (⟨i,hi⟩:Fin n)∈I then 1 else 0):=by
  rw [prefix_succ I i hi]
  have hm:(⟨i,hi⟩:Fin n)∉initialSet I i:=by simp [initialSet]
  by_cases h:(⟨i,hi⟩:Fin n)∈I <;> simp [h,Finset.card_insert_of_notMem hm]

theorem card_bound {n:ℕ} (I:Finset (Fin n)):I.card≤ n:=by
  simpa using Finset.card_le_univ I

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "unpack.mask"=mask I∧ σ.vars "unpack.i"≤ n∧
  n≤(σ.arrs "subset.bits").length∧
  Prefix ((encodeOutput I).take (σ.vars "unpack.i")) "subset.bits" σ∧
  σ.vars "unpack.card"=(initialSet I (σ.vars "unpack.i")).card

theorem step_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant I σ∧ σ.vars "unpack.i"< n) step
      (fun σ τ => Invariant I τ∧ τ.vars "unpack.i"=σ.vars "unpack.i"+1) 17:=by
  rintro σ ⟨⟨hn,hmask,hle,hroom,hprefix,hcard⟩,hlt⟩
  let i:=σ.vars "unpack.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈I then 1 else 0
  have hbit:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hbitB:bit< B:=by omega
  have hiB:i< B:=by omega
  have hmaskB:mask I< B:=(mask_bound I).trans hm
  have hdiv:mask I/2^i< B:=(Nat.div_le_self _ _).trans_lt hmaskB
  have hval:(Expr.and (.shiftr (.var "unpack.mask") (.var "unpack.i")) (.lit 1)).evalB B σ=some bit:=by
    have hh:=evalB_bin (op:=.and)
      (evalB_bin (op:=.shiftr)
        (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hmaskB⟩) (evalB_var hiB) hdiv)
      (evalB_lit (show 1< B by omega)) (by change Nat.land (mask I/2^i) 1< B; rw [bit_value I ⟨i,hlt⟩]; exact hbitB)
    exact hh.trans (congrArg some (bit_value I ⟨i,hlt⟩))
  let ν:=σ.setVar "unpack.bit" bit
  have r1:Run B read σ ν 6:=Run.assign hval
  have hcardν:ν.vars "unpack.card"=(initialSet I i).card:=
    (r1.frame_var "unpack.card" (by decide)).trans hcard
  have hnextB:(initialSet I (i+1)).card< B:=(card_bound _).trans_lt (by omega)
  have hsum:(initialSet I i).card+bit< B:=by rw [←prefix_card_step I i hlt]; exact hnextB
  let μ:=ν.setVar "unpack.card" ((initialSet I i).card+bit)
  have r2:Run B (.assign "unpack.card" (.add (.var "unpack.card") (.var "unpack.bit"))) ν μ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hcardν.symm,hcardν ▸ (card_bound _).trans_lt (by omega)⟩)
      (by simpa [ν] using evalB_var (σ:=ν) (x:="unpack.bit") (show ν.vars "unpack.bit"< B by simp [ν]; exact hbitB)) hsum)
  have r12:=r1.seq r2
  have hiμ:μ.vars "unpack.i"=i:=r12.frame_var "unpack.i" (by decide)
  have hbitμ:μ.vars "unpack.bit"=bit:=by simp [μ,ν]
  have hlen:(encodeOutput I).length=n:=List.length_ofFn
  have hilen:i<(encodeOutput I).length:=by rwa [hlen]
  have htake:((encodeOutput I).take i).length=i:=by rw [List.length_take,hlen,Nat.min_eq_left hle]
  have hentry:(encodeOutput I)[i]=bit:=by simp [encodeOutput,bit]
  obtain ⟨τ,r3,p3⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "subset.bits" "unpack.i"
    ((encodeOutput I).take i) bit (.var "unpack.bit") (by omega) (by rw [htake]; omega) μ
    ⟨by simpa only [Prefix,r12.frame_arr "subset.bits" (by decide)] using hprefix,
      by rwa [htake],by rw [htake,Lax455465Proofs.RamFrames.run_array_length r12]; omega,
      by rw [evalB_var_iff]; exact ⟨hbitμ.symm,hbitμ ▸ hbitB⟩⟩
  have ht:τ.vars "unpack.i"=i+1:=by simpa only [htake] using p3.2
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (rr.frame_var "unpack.mask" (by decide)).trans hmask,by rw [ht]; omega,?_,?_,?_⟩
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hilen,hentry]
    exact p3.1
  · rw [ht,prefix_card_step I i hlt,r3.frame_var "unpack.card" (by decide)]
    simp [μ,bit]

theorem command_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "unpack.mask"=mask I∧ n≤(σ.arrs "subset.bits").length)
      command (fun _ τ => Prefix (encodeOutput I) "subset.bits" τ∧ τ.vars "unpack.card"=I.card) (21*n+8):=by
  have hloop:=Spec.forRangeZero "unpack.i" "graph.n" (Invariant I) n 17 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hmask,hroom⟩
  let ν:=σ.setVar "unpack.card" 0
  have r1:Run B (.assign "unpack.card" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant I (ν.setVar "unpack.i" 0):=by
    refine ⟨?_,?_,by simp,hroom,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hmask
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_,?_⟩
  · have htake:(encodeOutput I).take n=encodeOutput I:=List.take_of_length_le (by simp [encodeOutput])
    simpa only [p2.2,htake] using p2.1.2.2.2.2.1
  · simpa only [p2.2,prefix_full] using p2.1.2.2.2.2.2

end Lax263307Proofs.NativeMaskUnpack

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeRationalTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def words (xs:List ℚ):List ℕ:=xs.flatMap encodeRational

theorem words_length (xs:List ℚ):(words xs).length=3*xs.length:=by
  induction xs with
  | nil => simp [words]
  | cons x xs ih => simp only [words,List.flatMap_cons,List.length_append,encodeRational,List.length_cons,List.length_nil] at ih ⊢; omega

end Lax263307Proofs.NativeRationalTabulate

end

section

namespace Lax263307Proofs.NativeRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax455465Proofs.RamLpRationalRead

theorem command_spec (B:ℕ) (array:String) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front++(encodeRational q++tail)) array σ∧ σ.vars "read.cursor"=front.length)
      (command array) (fun _ τ => FractionOutput q τ∧ τ.vars "read.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front++(encodeRational q++tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs array).length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "read.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ array) (Env.vars σ "read.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "read.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 array) c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "read.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 array) c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "read.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "read.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get array (Expr.var "read.cursor"))); let c18:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get array c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "read.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B (command array) σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B (command array) σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B (command array) σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get array (Expr.var "read.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get array (Expr.var "read.cursor")) c3 (RunStep.eval_get B σ array (Expr.var "read.cursor") (Env.vars σ "read.cursor") (RunStep.eval_var B σ "read.cursor" (?nAX_g8234_0_0_0)) (?nAX_g8234_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 array c18 c6 (RunStep.eval_add B c4 (Expr.var "read.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "read.cursor" (?nAX_g8234_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g8234_0_0_3)) (?nAX_g8234_0_0_4)) (?nAX_g8234_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 array c21 c10 (RunStep.eval_add B c8 (Expr.var "read.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "read.cursor" (?nAX_g8234_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g8234_0_0_7)) (?nAX_g8234_0_0_8)) (?nAX_g8234_0_0_9) ?_)) (RunStep.assign B c12 "read.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "read.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "read.cursor" (?nAX_g8234_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g8234_0_0_11)))))) (?nAX_g8234_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8234_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

theorem vector_entry_spec (B:ℕ) (array:String) (front tail:List ℕ) (qs:List ℚ)
    (i:ℕ) (hi:i < qs.length) (h3:3 < B) (hlen:front.length+3*i+3 < B)
    (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Prefix (front++(NativeRationalTabulate.words qs++tail)) array σ∧
      σ.vars "read.cursor"=front.length+3*i) (command array)
      (fun _ τ => FractionOutput qs[i] τ∧ τ.vars "read.cursor"=front.length+3*i+3) 17:=by
  have he:qs=qs.take i++qs[i]::qs.drop (i+1):=by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hlen':(front++NativeRationalTabulate.words (qs.take i)).length=front.length+3*i:=by
    rw [List.length_append,NativeRationalTabulate.words_length,List.length_take,Nat.min_eq_left hi.le]
  have hew:front++(NativeRationalTabulate.words qs++tail)=
      (front++NativeRationalTabulate.words (qs.take i))++
        (encodeRational qs[i]++(NativeRationalTabulate.words (qs.drop (i+1))++tail)):=by
    conv_lhs => rw [he]
    simp only [NativeRationalTabulate.words,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have hh:=command_spec B array qs[i] (front++NativeRationalTabulate.words (qs.take i))
    (NativeRationalTabulate.words (qs.drop (i+1))++tail) h3 (by rwa [hlen']) hn hd
  simpa only [hlen',←hew] using hh

end Lax263307Proofs.NativeRationalRead

end

section

namespace Lax263307Proofs.NativeMatrixOrder

theorem row_pair (n:ℕ) (u v:Fin n):
    NativeBlowUp.row ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=u:=by
  have hn:0< n:=by have hu:=u.isLt; omega
  apply Fin.ext
  change (u.val*n+v.val)/n=u.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt,Nat.zero_add]

theorem col_pair (n:ℕ) (u v:Fin n):
    NativeBlowUp.col ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=v:=by
  apply Fin.ext
  simp [NativeBlowUp.col,Nat.mod_eq_of_lt v.isLt]

theorem flatten {α:Type*} (n:ℕ) (f:Fin n→ Fin n→ α):
    List.ofFn (fun i:Fin (n*n) => f (NativeBlowUp.row i) (NativeBlowUp.col i))=
      (List.ofFn fun u => List.ofFn (f u)).flatten:=by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  simp only [row_pair,col_pair]

end Lax263307Proofs.NativeMatrixOrder

end

section

namespace Lax263307Proofs.NativeOracleCalls

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

theorem exists_invocation (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ (p:Lax808846.Ram.Program) (wordBound timeBound:Polynomial ℕ) (coefficients:List ℕ),
    (∀ x:ℕ,RamPolynomial.value coefficients x=wordBound.eval x)∧
    ∀ x:List ℕ,
    FitsInWords (wordBound.eval (bitSize x)) ((x.length::x)++f x)∧
    ∀ B:ℕ,
      bitSize x+1< B→ wordBound.eval (bitSize x+1)< B→
      2*(2^wordBound.eval (bitSize x))^2+3< B→
      timeBound.eval (bitSize x)+1< B→ RamVirtualConstants.allowance p< B→
      Spec B (fun σ => Prefix x "lp.word" σ∧ σ.vars "lp.position"=x.length∧
        x.length<(σ.arrs "vm.input").length∧
        timeBound.eval (bitSize x)<(σ.arrs "vm.addresses").length∧
        timeBound.eval (bitSize x)<(σ.arrs "vm.values").length∧
        timeBound.eval (bitSize x)<(σ.arrs "vm.output").length)
        (command p coefficients)
        (fun _ τ => Prefix (f x) "vm.output" τ∧ τ.vars "vm.outputLength"=(f x).length∧
          τ.vars "vm.running"=0)
        (((12*bitSize x+39)*x.length+6*coefficients.length+29)+
          ((timeBound.eval (bitSize x)+1)*(4*p.length+32*timeBound.eval (bitSize x)+104)+18)):=by
  obtain ⟨p,wp,tp,hprogram⟩:=SparseRam.polynomial_execution f hf
  obtain ⟨coeff,hcoeff⟩:=RamPolynomial.exists_coefficients wp
  refine ⟨p,wp,tp,coeff,hcoeff,?_⟩
  intro x
  obtain ⟨hfit,k,hk,s,hrun,hhalt,hout,_⟩:=hprogram x
  refine ⟨hfit,?_⟩
  intro B hsize hpoly hB htime hallow
  let w:=wp.eval (bitSize x)
  let T:=tp.eval (bitSize x)
  have hM:2^w< B:=by nlinarith [Nat.two_pow_pos w]
  have hinput:FitsInWords w (x.length::x):=fun z hz => hfit z (List.mem_append_left _ hz)
  have hlenWord:x.length<2^w:=hinput _ List.mem_cons_self
  have hlen:(x.length::x).length< B:=by simp only [List.length_cons]; omega
  have hwords:∀ z∈x,z< B:=fun z hz =>
    (hinput z (List.mem_cons_of_mem _ hz)).trans hM
  have hphysical:∀ z∈(x.length::x),z< B:=fun z hz => (hinput z hz).trans hM
  have hp:p.length+1< B:=(RamVirtualConstants.length_bound p).trans hallow
  have hlit:∀ i∈p,RamVirtualInstruction.LiteralsFit (B-1) i:=fun i hi =>
    RamVirtualTraceBounds.literals_mono i (RamVirtualConstants.literals_fit p i hi) (by omega)
  have hnative:=RamVirtualExecution.execute_spec B w k p (x.length::x) s hB (by omega) hp hlit
    hlen hphysical hrun hhalt
  have hprepare:=RamLpPrepare.command_spec B coeff x (by omega) (by omega)
    hsize hwords (by simpa only [hcoeff] using hpoly)
  rintro σ ⟨hprefix,hpos,hroom,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩:=hprepare σ ⟨hprefix,hpos,hroom⟩
  have hAν:k<(ν.arrs "vm.addresses").length:=by
    rw [RamFrames.run_array_length r1]; omega
  have hVν:k<(ν.arrs "vm.values").length:=by
    rw [RamFrames.run_array_length r1]; omega
  have hOν:k<(ν.arrs "vm.output").length:=by
    rw [RamFrames.run_array_length r1]; omega
  obtain ⟨τ,r2,p2⟩:=hnative ν ⟨by simpa only [hcoeff] using p1.1,p1.2.1,p1.2.2,hAν,hVν,hOν⟩
  have hcost:=Nat.mul_le_mul (Nat.add_le_add_right hk 1)
    (show 4*p.length+32*k+104≤4*p.length+32*T+104 by omega)
  refine ⟨τ,(r1.seq r2).mono (by dsimp only [T] at hcost; omega),?_,?_,p2.2⟩
  · simpa only [hout] using p2.1.2.2.2.2.2.1
  · simpa only [hout] using p2.1.2.2.2.2.2.2

end Lax263307Proofs.NativeOracleCalls

end

section

namespace Lax263307Proofs.NativeOracleFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs

theorem instruction_array (i:Lax808846.Ram.Instr) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output"]):
    a∉ (RamVirtualProgram.instruction i).warrs:=by
  cases i <;> simp_all [RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.warrs]

theorem dispatch_array (p:Lax808846.Ram.Program) (offset:ℕ) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output"]):
    a∉ (RamVirtualProgram.dispatch p offset).warrs:=by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.warrs]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or] using
      And.intro (instruction_array i a ha) (ih (offset+1))

theorem command_array (p:Lax808846.Ram.Program) (coeff:List ℕ) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output","vm.input"]):
    a∉ (NativeOracleCalls.command p coeff).warrs:=by
  have hm:a∉ ["vm.addresses","vm.values","vm.output"]:=by simp_all
  have hd:=dispatch_array p 0 a hm
  simp_all [NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamPolynomial.arrays_frame,RamLpInputFrame.command,RamLpInputFrame.step,
    RamWordBuffer.append,RamVirtualProgram.execute,RamWordOps.modulus,
    RamVirtualProgram.initCommand,Com.warrs]

end Lax263307Proofs.NativeOracleFrame

end

section

namespace Lax263307Proofs.NativeConditioningFloor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem size_log (n:ℕ) (hn:0< n):n.size=Nat.log2 n+1:=by
  have hlo:2^(Nat.log2 n)≤ n:=by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 (by omega)
  have hhi:n<2^(Nat.log2 n+1):=by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) n
  have hslo:=Nat.lt_size.mpr hlo
  have hshi:=Nat.size_le.mpr hhi
  omega

end Lax263307Proofs.NativeConditioningFloor

end

section

namespace Lax263307Proofs.NativeRestrictionOrder

open Lax263307

def vertices {n:ℕ} (R:Finset (Fin n)):List (Fin n):=
  (List.finRange n).filter fun v => v∈R

theorem vertices_sort {n:ℕ} (R:Finset (Fin n)):vertices R=R.sort (·≤·):=by
  exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT.eq_of_mem_iff R.sortedLT_sort (by simp [vertices])

theorem vertices_labels {n:ℕ} (R:Finset (Fin n)):
    vertices R=List.ofFn (ComputedSeparators.label R):=by
  rw [vertices_sort]
  simpa only [List.finRange,List.map_ofFn,Function.comp_def,ComputedSeparators.label] using
    (Finset.listMap_orderEmbOfFin_finRange R rfl).symm

def selectedPrefix {n:ℕ} (R:Finset (Fin n)) (i:ℕ):List ℕ:=
  (((List.finRange n).take i).filter fun v => v∈R).map Fin.val

theorem prefix_zero {n:ℕ} (R:Finset (Fin n)):selectedPrefix R 0=[]:=by simp [selectedPrefix]

theorem prefix_length {n:ℕ} (R:Finset (Fin n)) (i:ℕ):(selectedPrefix R i).length≤ i:=by
  dsimp [selectedPrefix]
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp only [List.length_take]; omega)

theorem prefix_full {n:ℕ} (R:Finset (Fin n)):selectedPrefix R n=words R:=by
  unfold selectedPrefix
  rw [List.take_of_length_le (by simp)]
  change (vertices R).map Fin.val=words R
  rw [vertices_labels,List.map_ofFn]
  rfl

theorem prefix_step {n:ℕ} (R:Finset (Fin n)) (i:ℕ) (hi:i< n):
    selectedPrefix R (i+1)=if (⟨i,hi⟩:Fin n)∈R then selectedPrefix R i++[i] else selectedPrefix R i:=by
  unfold selectedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using hi),List.filter_append,List.map_append]
  simp only [List.getElem_finRange,Fin.cast_mk]
  split_ifs <;> simp_all

end Lax263307Proofs.NativeRestrictionOrder

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeSelectedVertices

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeRestrictionOrder

def Context {n:ℕ} (R:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ Prefix (encodeOutput R) "subset.bits" σ∧ n≤(σ.arrs "restrict.vertices").length

def Invariant {n:ℕ} (R:Finset (Fin n)) (σ:Env):Prop:=
  Context R σ∧ σ.vars "restrict.i"≤ n∧
    Prefix (selectedPrefix R (σ.vars "restrict.i")) "restrict.vertices" σ∧
    σ.vars "restrict.count"=(selectedPrefix R (σ.vars "restrict.i")).length

theorem step_spec (B n:ℕ) (R:Finset (Fin n)) (hB:n+2< B):
    Spec B (fun σ => Invariant R σ∧ σ.vars "restrict.i"< n) step
      (fun σ τ => Invariant R τ∧ τ.vars "restrict.i"=σ.vars "restrict.i"+1) 18:=by
  rintro σ ⟨⟨⟨hn,hsource,hroom⟩,hle,hprefix,hcount⟩,hlt⟩
  let i:=σ.vars "restrict.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈R then 1 else 0
  have hbitB:bit< B:=by dsimp [bit]; split_ifs <;> omega
  have hilen:i<(encodeOutput R).length:=by simpa only [encodeOutput,List.length_ofFn] using hlt
  have hg:=hsource i hilen
  have he:(encodeOutput R)[i]=bit:=by simp only [encodeOutput,List.getElem_ofFn]; rfl
  rw [he] at hg
  let ν:=σ.setVar "restrict.bit" bit
  have r1:Run B (.assign "restrict.bit" (.get "subset.bits" (.var "restrict.i"))) σ ν 3:=
    Run.assign (evalB_get (evalB_var (by omega:σ.vars "restrict.i"< B)) hg hbitB)
  have hlen:=prefix_length R i
  have htest:(Cond.eq (.var "restrict.bit") (.lit 1)).evalB B ν=some (decide (bit=1)):=
    evalB_condEq (by rw [evalB_var_iff]; simp [ν,hbitB]) (evalB_lit (by omega))
  have hc:∃ μ,Run B choose ν μ 11∧ Prefix (selectedPrefix R (i+1)) "restrict.vertices" μ∧
      μ.vars "restrict.count"=(selectedPrefix R (i+1)).length:=by
    by_cases hmem:(⟨i,hlt⟩:Fin n)∈R
    · obtain ⟨μ,rr,pp⟩:=RamWordBuffer.append_spec B "restrict.vertices" "restrict.count" (selectedPrefix R i) i
        (.var "restrict.i") (by omega) (by omega) ν
        ⟨by simpa only [Prefix,ν,arrs_setVar] using hprefix,
          by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcount,
          by simpa only [ν,arrs_setVar] using (show (selectedPrefix R i).length<(σ.arrs "restrict.vertices").length by omega),
          by rw [evalB_var_iff]; simp only [ν,vars_setVar,String.reduceEq,if_false]; exact ⟨rfl,by omega⟩⟩
      have hh:Run B choose ν μ 11:=(Run.ite_true (d:=.skip) (by simpa [bit,hmem] using htest) rr).mono (by decide)
      exact ⟨μ,hh,by simpa only [prefix_step R i hlt,if_pos hmem] using pp.1,
        by simpa only [prefix_step R i hlt,if_pos hmem,List.length_append,List.length_singleton] using pp.2⟩
    · have hh:Run B choose ν ν 11:=
        (Run.ite_false (c:=RamWordBuffer.append "restrict.vertices" "restrict.count" (.var "restrict.i"))
          (by simpa [bit,hmem] using htest) Run.skip).mono (by decide)
      exact ⟨ν,hh,by simpa only [prefix_step R i hlt,if_neg hmem,Prefix,ν,arrs_setVar] using hprefix,
        by simpa only [prefix_step R i hlt,if_neg hmem,ν,vars_setVar,String.reduceEq,if_false] using hcount⟩
  obtain ⟨μ,r2,hp2,hc2⟩:=hc
  have hiμ:μ.vars "restrict.i"=i:=(r1.seq r2).frame_var "restrict.i" (by decide)
  let τ:=μ.setVar "restrict.i" (i+1)
  have r3:Run B (.assign "restrict.i" (.add (.var "restrict.i") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i< B)⟩)
      (evalB_lit (by omega)) (by change i+1< B; omega))
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr,?_,by simp [τ,i]⟩
  refine ⟨⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩,by simp [τ]; omega,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hsource
  · rwa [RamFrames.run_array_length rr]
  · simpa only [τ,vars_setVar,if_true,Prefix,arrs_setVar] using hp2
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,if_true] using hc2

theorem command_spec (B n:ℕ) (R:Finset (Fin n)) (hB:n+2< B):
    Spec B (Context R) command
      (fun _ τ => Context R τ∧ Prefix (words R) "restrict.vertices" τ∧ τ.vars "restrict.count"=R.card)
      (22*n+8):=by
  have hloop:=Spec.forRangeZero "restrict.i" "graph.n" (Invariant R) n 18 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.1) (step_spec B n R hB)
  intro σ hc
  let ν:=σ.setVar "restrict.count" 0
  have r1:Run B (.assign "restrict.count" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant R (ν.setVar "restrict.i" 0):=by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [Prefix,prefix_zero]
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,ht⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),ht.1.1,?_,?_⟩
  · simpa only [ht.2,prefix_full] using ht.1.2.2.1
  · simpa only [ht.2,prefix_full,words,List.length_ofFn] using ht.1.2.2.2

end Lax263307Proofs.NativeSelectedVertices

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeLargeCapacity

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax263307 NativeSignedArithmetic

def value (b n r load k:ℕ):ℕ:=(numerator b n r k+denominator n load-1)/denominator n load+1

theorem ceil_ratio (a b:ℕ) (hb:0< b):⌈(a:ℚ)/b⌉₊=(a+b-1)/b:=by
  have hbq:(0:ℚ)< b:=by exact_mod_cast hb
  change ⌈(a:ℚ)/b⌉₊=a⌈/⌉b
  apply Nat.le_antisymm
  · rw [Nat.ceil_le,div_le_iff₀ hbq]
    have hh:a≤ b*(a⌈/⌉b):=(ceilDiv_le_iff_le_mul hb).mp le_rfl
    exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
  · rw [ceilDiv_le_iff_le_mul hb]
    have hh:=(div_le_iff₀ hbq).mp (Nat.le_ceil ((a:ℚ)/b))
    norm_cast at hh
    simpa only [Nat.mul_comm] using hh

theorem exact_value (b n r load k:ℕ) (hn:0< n) (hl:0< load):
    (ComputedSeparators.largeCapacity b n r load k:ℚ)=(value b n r load k:ℕ):=by
  have he:ComputedSeparators.ratio b n*(2*r:ℕ)^2/ComputedSeparators.scale n load k=
      (numerator b n r k:ℚ)/denominator n load:=by
    simp only [ComputedSeparators.ratio,ComputedSeparators.scale,numerator,denominator,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow,
      div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  have hd:0< denominator n load:=by unfold denominator; positivity
  change ((⌈ComputedSeparators.ratio b n*(2*r:ℕ)^2/ComputedSeparators.scale n load k⌉₊+1:ℕ):ℚ)=_
  rw [he,ceil_ratio _ _ hd]
  rfl

def Input (b n r load k:ℕ) (σ:Env):Prop:=
  σ.vars "class.B"=b∧ σ.vars "graph.n"=n∧ σ.vars "restrict.count"=r∧
    σ.vars "algorithm.load"=load∧ σ.vars "conditioning.k"=k

theorem command_spec (B b n r load k:ℕ) (hn:0< n) (hl:0< load)
    (hB:resource b n r load k< B):
    Spec B (Input b n r load k) command
      (fun _ τ => Stored "split.large" (ComputedSeparators.largeCapacity b n r load k:ℚ) τ)
      (12*(2*n).size+60):=by
  have hguards:=hB
  dsimp [resource] at hguards
  have hlog:=NativeConditioningFloor.size_log (2*n) (by omega)
  have hprod:Spec B (fun σ => Input b n r load k σ∧ σ.vars "size.count"=(2*n).size) products
      (fun _ τ => τ.vars "large.numerator"=numerator b n r k∧ τ.vars "large.denominator"=denominator n load) 22:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (Input b n r load k σ) (@Eq Nat (Env.vars σ "size.count") (Nat.size (Nat.mul ((2:Nat)) n)))) => let c0:Prop:=Input b n r load k σ; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((2:Nat)); let c3:Prop:= @Eq Nat (Env.vars σ "size.count") (Nat.size (c2 n)); let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "large.numerator") (numerator b n r k)) (@Eq Nat (Env.vars τ "large.denominator") (denominator n load))) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B products σ σ' ((22:Nat))) (c4 σ'); let c6:Nat:=c1 (Env.vars σ "class.B") (Env.vars σ "size.count"); let c7:Nat:=c2 (Env.vars σ "restrict.count"); let c8:Nat:=c1 c6 c7; let c9:Nat:=c1 c8 c7; let c10:Nat:=c1 ((3:Nat)) (Env.vars σ "conditioning.k"); let c11:Nat:=c1 c9 c10; let c12:Env:=Env.setVar σ "large.numerator" c11; let c13:String→ Nat:=Env.vars c12; let c14:Nat:=c13 "algorithm.load"; let c15:Nat:=c13 "graph.n"; let c16:Nat:=c1 c14 c15; let c17:Nat:=c1 c16 c15; let c18:Env:=Env.setVar c12 "large.denominator" c17; let c19:Nat→ Nat→ Nat:=Nat.add; let c20:Nat→ Nat:=c19 ((1:Nat)); let c21:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "restrict.count"); let c22:Expr:=Expr.mul (Expr.mul (Expr.var "class.B") (Expr.var "size.count")) c21; let c23:Expr:=Expr.mul c22 c21; let c24:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "conditioning.k"); let c25:Expr:=Expr.mul c23 c24; let c26:Nat:=c20 (Expr.size c25); let c27:Expr:=Expr.mul (Expr.mul (Expr.var "algorithm.load") (Expr.var "graph.n")) (Expr.var "graph.n"); let c28:Nat:=c20 (Expr.size c27); let c29:String→ Nat:=Env.vars c18; @And.casesOn c0 c3 (fun (x:And c0 c3) => @Exists Env c5) a fun (left:c0) (right:c3) => @Exists.intro Env c5 c18 (@And.intro (Run B products σ c18 ((22:Nat))) (c4 c18) (RunStep.mono B products σ c18 (c19 c26 c28) ((22:Nat)) (RunStep.seq B (Com.assign "large.numerator" c25) (Com.assign "large.denominator" c27) σ c12 c18 c26 c28 (RunStep.assign B σ "large.numerator" c25 c11 (RunStep.eval_mul B σ c23 c24 c9 c10 (RunStep.eval_mul B σ c22 c21 c8 c7 (RunStep.eval_mul B σ (Expr.mul (Expr.var "class.B") (Expr.var "size.count")) c21 c6 c7 (RunStep.eval_mul B σ (Expr.var "class.B") (Expr.var "size.count") (Env.vars σ "class.B") (Env.vars σ "size.count") (RunStep.eval_var B σ "class.B" ?_) (RunStep.eval_var B σ "size.count" (?nAX_g8755_0_0_0)) ?_) (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "restrict.count") ((2:Nat)) (Env.vars σ "restrict.count") (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8755_0_0_1)) (RunStep.eval_var B σ "restrict.count" ?_) ?_) ?_) (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "restrict.count") ((2:Nat)) (Env.vars σ "restrict.count") (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8755_0_0_2)) (RunStep.eval_var B σ "restrict.count" ?_) ?_) ?_) (RunStep.eval_mul B σ (Expr.lit ((3:Nat))) (Expr.var "conditioning.k") ((3:Nat)) (Env.vars σ "conditioning.k") (RunStep.eval_lit B ((3:Nat)) σ (?nAX_g8755_0_0_3)) (RunStep.eval_var B σ "conditioning.k" ?_) ?_) ?_)) (RunStep.assign B c12 "large.denominator" c27 c17 (RunStep.eval_mul B c12 (Expr.mul (Expr.var "algorithm.load") (Expr.var "graph.n")) (Expr.var "graph.n") c16 c15 (RunStep.eval_mul B c12 (Expr.var "algorithm.load") (Expr.var "graph.n") c14 c15 (RunStep.eval_var B c12 "algorithm.load" ?_) (RunStep.eval_var B c12 "graph.n" ?_) ?_) (RunStep.eval_var B c12 "graph.n" ?_) ?_))) (?nAX_g8755_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8755_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Input,numerator,denominator]
    all_goals omega
  have hvalueBound:value b n r load k< B:=by
    dsimp [value]
    have hh:=Nat.div_le_self (numerator b n r k+denominator n load-1) (denominator n load)
    omega
  have hfinish:Spec B (fun σ => σ.vars "large.numerator"=numerator b n r k∧ σ.vars "large.denominator"=denominator n load)
      finish (fun _ τ => τ.vars "split.large.s"=0∧ τ.vars "split.large.n"=value b n r load k∧ τ.vars "split.large.d"=1) 16:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "large.numerator") (numerator b n r k)) (@Eq Nat (Env.vars σ "large.denominator") (denominator n load))) => let c0:Prop:= @Eq Nat (Env.vars σ "large.numerator") (numerator b n r k); let c1:Prop:= @Eq Nat (Env.vars σ "large.denominator") (denominator n load); let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "split.large.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "split.large.n") (value b n r load k)) (@Eq Nat (Env.vars τ "split.large.d") ((1:Nat))))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B finish σ σ' ((16:Nat))) (c2 σ'); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 (Env.vars σ "large.numerator") (Env.vars σ "large.denominator"); let c6:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c5 ((1:Nat)); let c7:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c6 (Env.vars σ "large.denominator"); let c8:Nat:=c4 c7 ((1:Nat)); let c9:Env:=Env.setVar σ "large.value" c8; let c10:Env:=Env.setVar c9 "split.large.s" ((0:Nat)); let c11:Nat:=Env.vars c10 "large.value"; let c12:Env:=Env.setVar c10 "split.large.n" c11; let c13:Env:=Env.setVar c12 "split.large.d" ((1:Nat)); let c14:Nat→ Nat:=c4 ((1:Nat)); let c15:Expr:=Expr.sub (Expr.add (Expr.var "large.numerator") (Expr.var "large.denominator")) (Expr.lit ((1:Nat))); let c16:Expr:=Expr.div c15 (Expr.var "large.denominator"); let c17:Expr:=Expr.add c16 (Expr.lit ((1:Nat))); let c18:Nat:=c14 (Expr.size c17); let c19:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c20:Nat:=c14 (Expr.size (Expr.var "large.value")); let c21:Nat:=c14 (Expr.size (Expr.lit ((1:Nat)))); let c22:Nat:=c4 c20 c21; let c23:Nat:=c4 c19 c22; let c24:Com:=Com.assign "split.large.s" (Expr.lit ((0:Nat))); let c25:Com:=Com.assign "split.large.d" (Expr.lit ((1:Nat))); let c26:Com:=Com.seq (Com.assign "split.large.n" (Expr.var "large.value")) c25; let c27:String→ Nat:=Env.vars c13; @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c3) a fun (left:c0) (right:c1) => @Exists.intro Env c3 c13 (@And.intro (Run B finish σ c13 ((16:Nat))) (c2 c13) (RunStep.mono B finish σ c13 (c4 c18 c23) ((16:Nat)) (RunStep.seq B (Com.assign "large.value" c17) (Com.seq c24 c26) σ c9 c13 c18 c23 (RunStep.assign B σ "large.value" c17 c8 (RunStep.eval_add B σ c16 (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_div B σ c15 (Expr.var "large.denominator") c6 (Env.vars σ "large.denominator") (RunStep.eval_sub B σ (Expr.add (Expr.var "large.numerator") (Expr.var "large.denominator")) (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_add B σ (Expr.var "large.numerator") (Expr.var "large.denominator") (Env.vars σ "large.numerator") (Env.vars σ "large.denominator") (RunStep.eval_var B σ "large.numerator" (?nAX_g8755_1_0_0)) (RunStep.eval_var B σ "large.denominator" (?nAX_g8755_1_0_1)) (?nAX_g8755_1_0_2)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8755_1_0_3)) (?nAX_g8755_1_0_4)) (RunStep.eval_var B σ "large.denominator" (?nAX_g8755_1_0_5)) ?_) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8755_1_0_6)) ?_)) (RunStep.seq B c24 c26 c9 c10 c13 c19 c22 (RunStep.assign B c9 "split.large.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c9 (?nAX_g8755_1_0_7))) (RunStep.seq B (Com.assign "split.large.n" (Expr.var "large.value")) c25 c10 c12 c13 c20 c21 (RunStep.assign B c10 "split.large.n" (Expr.var "large.value") c11 (RunStep.eval_var B c10 "large.value" ?_)) (RunStep.assign B c12 "split.large.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c12 (?nAX_g8755_1_0_8)))))) (?nAX_g8755_1_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8755_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8755_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [value]
    all_goals omega
  intro σ hc
  let ν:=σ.setVar "size.value" (2*n)
  have r1:Run B (.assign "size.value" (.mul (.lit 2) (.var "graph.n"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega:n< B)⟩) (by change 2*n< B; omega))
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B (2*n) (by omega) (by omega) ν (by simp [ν])
  have hcμ:Input b n r load k μ:=by
    have rr:=r1.seq r2
    simpa only [Input,rr.frame_var "class.B" (by decide),rr.frame_var "graph.n" (by decide),
      rr.frame_var "restrict.count" (by decide),rr.frame_var "algorithm.load" (by decide),
      rr.frame_var "conditioning.k" (by decide)] using hc
  obtain ⟨ξ,r3,p3⟩:=hprod μ ⟨hcμ,p2.2⟩
  obtain ⟨τ,r4,p4⟩:=hfinish ξ p3
  have hp4:Stored "split.large" (value b n r load k:ℕ) τ:=by
    simp [Stored,p4.1,p4.2.1,p4.2.2,fractionValue]
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),by simpa only [exact_value b n r load k hn hl] using hp4⟩

end Lax263307Proofs.NativeLargeCapacity

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRestrictionRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

theorem frame {B n K:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ} {R:Finset (Fin n)} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hd:Data G x R σ)
    (ha:∀ s∈["restrict.vertices","search.graph","near.costs"],s∉c.warrs)
    (hv:∀ s∈["restrict.count","graph.n"],s∉c.wvars):Data G x R τ:=by
  refine ⟨?_,?_,?_,(rr.frame_var "restrict.count" (hv _ (by simp))).trans hd.count,
    (rr.frame_var "graph.n" (hv _ (by simp))).trans hd.order⟩
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" (ha _ (by simp))] using hd.labels
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp))] using hd.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" (ha _ (by simp))] using hd.costs

theorem label_get {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ} {R:Finset (Fin n)} {σ:Env} (hd:Data G x R σ) (i:Fin R.card):
    (σ.arrs "restrict.vertices")[i.val]?=some (ComputedSeparators.label R i).val:=by
  simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
    hd.labels i.val (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using i.isLt)

theorem graph_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (i j:Fin R.card) (hB:n*n+n+3< B):
    Spec B (fun σ => Data G x R σ∧ σ.vars "restrict.row"=i.val∧ σ.vars "restrict.col"=j.val)
      graphRead (fun _ τ => Data G x R τ∧
        τ.vars "restrict.edge"=if (ComputedSeparators.restriction G R).Adj i j then 1 else 0) 13:=by
  let u:=ComputedSeparators.label R i
  let v:=ComputedSeparators.label R j
  have hiB:i.val< B:=i.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have hjB:j.val< B:=j.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have huB:u.val< B:=u.isLt.trans (by omega)
  have hvB:v.val< B:=v.isLt.trans (by omega)
  have hind:u.val*n+v.val< n*n:=by nlinarith [u.isLt,v.isLt]
  rintro σ ⟨hd,hi,hj⟩
  let ν:=σ.setVar "restrict.u" u.val
  have r1:Run B (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (label_get hd i) huB)
  let μ:=ν.setVar "restrict.v" v.val
  have r2:Run B (.assign "restrict.v" (.get "restrict.vertices" (.var "restrict.col"))) ν μ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using
      (show j.val=σ.vars "restrict.col" ∧ σ.vars "restrict.col"< B from ⟨hj.symm,hj ▸ hjB⟩)) (label_get hd j) hvB)
  have hget:=NativeBlowUp.matrix_coordinate (fun a b => if G.Adj a b then 1 else 0) u v
  change (NativeWeightReduction.adjacency G)[u.val*n+v.val]?=some (if G.Adj u v then 1 else 0) at hget
  have hlen:u.val*n+v.val<(NativeWeightReduction.adjacency G).length:=by
    rw [NativeWeightReduction.adjacency_length]; exact hind
  rw [List.getElem?_eq_getElem hlen] at hget
  have hg:=(hd.graph _ hlen).trans hget
  let bit:ℕ:=if G.Adj u v then 1 else 0
  let τ:=μ.setVar "restrict.edge" bit
  have hgμ:(μ.arrs "search.graph")[u.val*n+v.val]?=some bit:=hg
  have r3:Run B (.assign "restrict.edge" (.get "search.graph" (.add (.mul (.var "restrict.u") (.var "graph.n")) (.var "restrict.v")))) μ τ 7:=by
    apply Run.assign
    apply evalB_get _ hgμ (by dsimp [bit]; split_ifs <;> omega)
    apply evalB_bin (op:=.add) _ _ (hind.trans (by omega))
    · apply evalB_bin (op:=.mul)
        (by rw [evalB_var_iff]; simp [μ,ν,huB])
        (by rw [evalB_var_iff]; simp only [μ,ν,vars_setVar,String.reduceEq,if_false]; exact ⟨hd.order.symm,hd.order ▸ (by omega:n< B)⟩)
        (by change u.val*n< B; nlinarith only [hind,hB])
    · rw [evalB_var_iff]
      simp [μ,hvB]
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simp [τ,bit,u,v,ComputedSeparators.restriction]⟩

theorem cost_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (i:Fin R.card) (hB:3*n+10< B) (hM:M< B)
    (hx:∀ v,Bounded M (x v)):
    Spec B (fun σ => Data G x R σ∧ σ.vars "restrict.row"=i.val) costRead
      (fun _ τ => Data G x R τ∧ RamRational.FractionOutput (x (ComputedSeparators.label R i)) τ) 24:=by
  let u:=ComputedSeparators.label R i
  have hiB:i.val< B:=i.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have huB:u.val< B:=u.isLt.trans (by omega)
  rintro σ ⟨hd,hi⟩
  let ν:=σ.setVar "restrict.u" u.val
  have r1:Run B (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (label_get hd i) huB)
  let μ:=ν.setVar "read.cursor" (3*u.val)
  have r2:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "restrict.u"))) ν μ 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simp [ν,huB]) (by change 3*u.val< B; have hh:=u.isLt; omega))
  obtain ⟨τ,r3,p3⟩:=NativeRationalRead.vector_entry_spec B "near.costs" [] [] (List.ofFn x) u.val
    (by simpa only [List.length_ofFn] using u.isLt) (by omega) (by have hh:=u.isLt; simp; omega)
    (by simpa only [List.getElem_ofFn] using (hx u).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (hx u).2.trans_lt hM) μ
    ⟨by simpa only [NativeRationalTabulate.words,encodeVector,List.nil_append,List.append_nil,Prefix,
        (r1.seq r2).frame_arr "near.costs" (by decide)] using hd.costs,by simp [μ]⟩
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simpa only [List.getElem_ofFn] using p3.1⟩

end Lax263307Proofs.NativeRestrictionRead

end

section

namespace Lax263307Proofs.NativeFlowPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding

theorem command_spec (B b n load k:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (hn:0< n) (hl:0< load)
    (hB:n+2< B) (hm:2^n< B) (hlarge:NativeLargeCapacity.resource b n R.card load k< B):
    Spec B (fun σ => Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
      Prefix (encodeVector x) "near.costs" σ∧ σ.vars "graph.n"=n∧
      σ.vars "separator.remaining"=NativeMasks.mask R∧ σ.vars "class.B"=b∧
      σ.vars "algorithm.load"=load∧ σ.vars "conditioning.k"=k∧
      n≤(σ.arrs "subset.bits").length∧ n≤(σ.arrs "restrict.vertices").length)
      command (fun _ τ => NativeRestrictionRead.Data G x R τ∧
        Stored "split.large" (ComputedSeparators.largeCapacity b n R.card load k:ℚ) τ)
      (43*n+12*(2*n).size+78):=by
  rintro σ ⟨hg,hx,hnσ,hR,hb,hlσ,hk,hbits,hvertices⟩
  let σ1:=σ.setVar "unpack.mask" (NativeMasks.mask R)
  have r1:Run B (.assign "unpack.mask" (.var "separator.remaining")) σ σ1 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hR.symm,hR ▸ (NativeMasks.mask_bound R).trans hm⟩)
  obtain ⟨σ2,r2,p2⟩:=NativeMaskUnpack.command_spec B R hB hm σ1
    ⟨by simpa [σ1] using hnσ,by simp [σ1],hbits⟩
  have r12:=r1.seq r2
  obtain ⟨σ3,r3,p3⟩:=NativeSelectedVertices.command_spec B n R hB σ2
    ⟨(r12.frame_var "graph.n" (by decide)).trans hnσ,p2.1,
      by rwa [RamFrames.run_array_length r12]⟩
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨τ,r4,p4⟩:=NativeLargeCapacity.command_spec B b n R.card load k hn hl hlarge σ3
    ⟨(r123.frame_var "class.B" (by decide)).trans hb,p3.1.1,p3.2.2,
      (r123.frame_var "algorithm.load" (by decide)).trans hlσ,
      (r123.frame_var "conditioning.k" (by decide)).trans hk⟩
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by omega),⟨?_,?_,?_,?_,?_⟩,p4⟩
  · simpa only [Prefix,r4.frame_arr "restrict.vertices" (by decide)] using p3.2.1
  · simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hg
  · simpa only [Prefix,rr.frame_arr "near.costs" (by decide)] using hx
  · exact (r4.frame_var "restrict.count" (by decide)).trans p3.2.2
  · exact (rr.frame_var "graph.n" (by decide)).trans hnσ

end Lax263307Proofs.NativeFlowPrepare

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeSplitEntry

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

def Data {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (σ:Env):Prop:=
  NativeRestrictionRead.Data G (fun v => (x v:ℚ)) R σ∧ Stored "split.large" (large:ℚ) σ∧
    σ.vars "split.order"=2*R.card∧ σ.vars "split.count"=(2*R.card)*(2*R.card)

theorem frame {B n K:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ≥0} {R:Finset (Fin n)} {large:ℚ≥0} {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hd:Data G x R large σ)
    (ha:∀ s∈["restrict.vertices","search.graph","near.costs"],s∉c.warrs)
    (hv:∀ s∈["restrict.count","graph.n","split.large.s","split.large.n","split.large.d","split.order","split.count"],s∉c.wvars):
    Data G x R large τ:=by
  refine ⟨NativeRestrictionRead.frame rr hd.1 ha (by
      intro s hs
      apply hv s
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ⊢
      tauto),?_,
    (rr.frame_var "split.order" (hv _ (by simp))).trans hd.2.2.1,
    (rr.frame_var "split.count" (hv _ (by simp))).trans hd.2.2.2⟩
  simpa only [Stored,String.reduceAppend,rr.frame_var "split.large.s" (hv _ (by simp)),
    rr.frame_var "split.large.n" (hv _ (by simp)),rr.frame_var "split.large.d" (hv _ (by simp))] using hd.2.1

theorem ports_spec (B s:ℕ) (i:Fin ((2*s)*(2*s))) (hB:(2*s)*(2*s)+2*s+4< B):
    Spec B (fun σ => σ.vars "split.order"=2*s∧ σ.vars "split.i"=i.val) ports
      (fun _ τ => τ.vars "split.u"=(NativeBlowUp.row i).val∧
        τ.vars "split.v"=(NativeBlowUp.col i).val∧
        τ.vars "restrict.row"=(original (NativeBlowUp.row i)).val∧
        τ.vars "restrict.col"=(original (NativeBlowUp.col i)).val∧
        τ.vars "split.up"=(NativeBlowUp.row i).val%2∧ τ.vars "split.vp"=(NativeBlowUp.col i).val%2) 30:=by
  have hn:0<2*s:=by have hh:=i.isLt; nlinarith
  have hi:=i.isLt
  have hdiv:=Nat.div_le_self i.val (2*s)
  have hprod:=Nat.div_mul_le_self i.val (2*s)
  have hmod:=Nat.mod_lt i.val hn
  have hv:i.val-i.val/(2*s)*(2*s)=i.val%(2*s):=Nat.mod_eq_sub_div_mul.symm
  have hur:i.val / (2*s) / 2 * 2≤ i.val / (2*s):=Nat.div_mul_le_self _ _
  have hvr:(i.val%(2*s))/2*2≤ i.val%(2*s):=Nat.div_mul_le_self _ _
  have hup:i.val/(2*s)-2*(i.val/(2*s)/2)=i.val/(2*s)%2:=by
    rw [Nat.mul_comm 2 (i.val/(2*s)/2)]; exact Nat.mod_eq_sub_div_mul.symm
  have hvp:i.val%(2*s)-2*((i.val%(2*s))/2)=i.val%(2*s)%2:=by
    rw [Nat.mul_comm 2 ((i.val%(2*s))/2)]; exact Nat.mod_eq_sub_div_mul.symm
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "split.order") (Nat.mul ((2:Nat)) s)) (@Eq Nat (Env.vars σ "split.i") (@Fin.val (Nat.mul (Nat.mul ((2:Nat)) s) (Nat.mul ((2:Nat)) s)) i))) => let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat→ Nat:=c0 ((2:Nat)); let c2:Nat:=c1 s; let c3:Prop:= @Eq Nat (Env.vars σ "split.order") c2; let c4:Prop:= @Eq Nat (Env.vars σ "split.i") (@Fin.val (c0 c2 c2) i); let c5:Fin c2→ Nat:= @Fin.val c2; let c6:Fin c2:= @NativeBlowUp.row c2 i; let c7:Nat:=c5 c6; let c8:Fin c2:= @NativeBlowUp.col c2 i; let c9:Nat:=c5 c8; let c10:Nat:= @Fin.val s (@original s c6); let c11:Nat:= @Fin.val s (@original s c8); let c12:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c13:Nat:=c12 c7 ((2:Nat)); let c14:Nat:=c12 c9 ((2:Nat)); let c15:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "split.u") c7) (And (@Eq Nat (Env.vars τ "split.v") c9) (And (@Eq Nat (Env.vars τ "restrict.row") c10) (And (@Eq Nat (Env.vars τ "restrict.col") c11) (And (@Eq Nat (Env.vars τ "split.up") c13) (@Eq Nat (Env.vars τ "split.vp") c14)))))) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B ports σ σ' ((30:Nat))) (c15 σ'); let c17:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c18:Nat:=c17 (Env.vars σ "split.i") (Env.vars σ "split.order"); let c19:Env:=Env.setVar σ "split.u" c18; let c20:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c21:String→ Nat:=Env.vars c19; let c22:Nat:=c21 "split.i"; let c23:Nat:=c21 "split.u"; let c24:Nat:=c21 "split.order"; let c25:Nat:=c0 c23 c24; let c26:Nat:=c20 c22 c25; let c27:Env:=Env.setVar c19 "split.v" c26; let c28:Nat:=Env.vars c27 "split.u"; let c29:Nat:=c17 c28 ((2:Nat)); let c30:Env:=Env.setVar c27 "restrict.row" c29; let c31:Nat:=Env.vars c30 "split.v"; let c32:Nat:=c17 c31 ((2:Nat)); let c33:Env:=Env.setVar c30 "restrict.col" c32; let c34:String→ Nat:=Env.vars c33; let c35:Nat:=c34 "split.u"; let c36:Nat:=c34 "restrict.row"; let c37:Nat:=c1 c36; let c38:Nat:=c20 c35 c37; let c39:Env:=Env.setVar c33 "split.up" c38; let c40:String→ Nat:=Env.vars c39; let c41:Nat:=c40 "split.v"; let c42:Nat:=c40 "restrict.col"; let c43:Nat:=c1 c42; let c44:Nat:=c20 c41 c43; let c45:Env:=Env.setVar c39 "split.vp" c44; let c46:Nat→ Nat→ Nat:=Nat.add; let c47:Nat→ Nat:=c46 ((1:Nat)); let c48:Nat:=c47 (Expr.size (Expr.div (Expr.var "split.i") (Expr.var "split.order"))); let c49:Expr:=Expr.sub (Expr.var "split.i") (Expr.mul (Expr.var "split.u") (Expr.var "split.order")); let c50:Nat:=c47 (Expr.size c49); let c51:Expr:=Expr.div (Expr.var "split.u") (Expr.lit ((2:Nat))); let c52:Nat:=c47 (Expr.size c51); let c53:Expr:=Expr.div (Expr.var "split.v") (Expr.lit ((2:Nat))); let c54:Nat:=c47 (Expr.size c53); let c55:Expr→ Expr:=Expr.mul (Expr.lit ((2:Nat))); let c56:Expr:=c55 (Expr.var "restrict.row"); let c57:Expr:=Expr.sub (Expr.var "split.u") c56; let c58:Nat:=c47 (Expr.size c57); let c59:Expr:=c55 (Expr.var "restrict.col"); let c60:Expr:=Expr.sub (Expr.var "split.v") c59; let c61:Nat:=c47 (Expr.size c60); let c62:Nat:=c46 c58 c61; let c63:Nat:=c46 c54 c62; let c64:Nat:=c46 c52 c63; let c65:Nat:=c46 c50 c64; let c66:Com:=Com.assign "split.v" c49; let c67:Com:=Com.assign "restrict.row" c51; let c68:Com:=Com.assign "restrict.col" c53; let c69:Com:=Com.assign "split.up" c57; let c70:Com:=Com.assign "split.vp" c60; let c71:Com:=Com.seq c69 c70; let c72:Com:=Com.seq c68 c71; let c73:Com:=Com.seq c67 c72; let c74:String→ Nat:=Env.vars c45; @And.casesOn c3 c4 (fun (x:And c3 c4) => @Exists Env c16) a fun (left:c3) (right:c4) => @Exists.intro Env c16 c45 (@And.intro (Run B ports σ c45 ((30:Nat))) (c15 c45) (RunStep.mono B ports σ c45 (c46 c48 c65) ((30:Nat)) (RunStep.seq B (Com.assign "split.u" (Expr.div (Expr.var "split.i") (Expr.var "split.order"))) (Com.seq c66 c73) σ c19 c45 c48 c65 (RunStep.assign B σ "split.u" (Expr.div (Expr.var "split.i") (Expr.var "split.order")) c18 (RunStep.eval_div B σ (Expr.var "split.i") (Expr.var "split.order") (Env.vars σ "split.i") (Env.vars σ "split.order") (RunStep.eval_var B σ "split.i" (?nAX_g8768_0_0_0)) (RunStep.eval_var B σ "split.order" (?nAX_g8768_0_0_1)) ?_)) (RunStep.seq B c66 c73 c19 c27 c45 c50 c64 (RunStep.assign B c19 "split.v" c49 c26 (RunStep.eval_sub B c19 (Expr.var "split.i") (Expr.mul (Expr.var "split.u") (Expr.var "split.order")) c22 c25 (RunStep.eval_var B c19 "split.i" (?nAX_g8768_0_0_2)) (RunStep.eval_mul B c19 (Expr.var "split.u") (Expr.var "split.order") c23 c24 (RunStep.eval_var B c19 "split.u" ?_) (RunStep.eval_var B c19 "split.order" (?nAX_g8768_0_0_3)) ?_) (?nAX_g8768_0_0_4))) (RunStep.seq B c67 c72 c27 c30 c45 c52 c63 (RunStep.assign B c27 "restrict.row" c51 c29 (RunStep.eval_div B c27 (Expr.var "split.u") (Expr.lit ((2:Nat))) c28 ((2:Nat)) (RunStep.eval_var B c27 "split.u" ?_) (RunStep.eval_lit B ((2:Nat)) c27 (?nAX_g8768_0_0_5)) ?_)) (RunStep.seq B c68 c71 c30 c33 c45 c54 c62 (RunStep.assign B c30 "restrict.col" c53 c32 (RunStep.eval_div B c30 (Expr.var "split.v") (Expr.lit ((2:Nat))) c31 ((2:Nat)) (RunStep.eval_var B c30 "split.v" (?nAX_g8768_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c30 (?nAX_g8768_0_0_7)) (?nAX_g8768_0_0_8))) (RunStep.seq B c69 c70 c33 c39 c45 c58 c61 (RunStep.assign B c33 "split.up" c57 c38 (RunStep.eval_sub B c33 (Expr.var "split.u") c56 c35 c37 (RunStep.eval_var B c33 "split.u" ?_) (RunStep.eval_mul B c33 (Expr.lit ((2:Nat))) (Expr.var "restrict.row") ((2:Nat)) c36 (RunStep.eval_lit B ((2:Nat)) c33 (?nAX_g8768_0_0_9)) (RunStep.eval_var B c33 "restrict.row" ?_) ?_) (?nAX_g8768_0_0_10))) (RunStep.assign B c39 "split.vp" c60 c44 (RunStep.eval_sub B c39 (Expr.var "split.v") c59 c41 c43 (RunStep.eval_var B c39 "split.v" (?nAX_g8768_0_0_11)) (RunStep.eval_mul B c39 (Expr.lit ((2:Nat))) (Expr.var "restrict.col") ((2:Nat)) c42 (RunStep.eval_lit B ((2:Nat)) c39 (?nAX_g8768_0_0_12)) (RunStep.eval_var B c39 "restrict.col" (?nAX_g8768_0_0_13)) (?nAX_g8768_0_0_14)) (?nAX_g8768_0_0_15)))))))) (?nAX_g8768_0_0_16)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8768_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8768_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeBlowUp.row,NativeBlowUp.col,original]
  all_goals omega

theorem choose_spec (B M s:ℕ) (G:SimpleGraph (Fin s)) [DecidableRel G.Adj]
    (x:Fin s→ ℚ≥0) (large:ℚ≥0) (u v:Fin (2*s)) (hB:2*s+M+4< B)
    (hx:Bounded M (x (original u):ℚ)) (hl:Bounded M (large:ℚ)):
    Spec B (fun σ => σ.vars "split.u"=u.val∧ σ.vars "split.v"=v.val∧
      σ.vars "split.up"=u.val%2∧ σ.vars "split.vp"=v.val%2∧
      σ.vars "restrict.edge"=(if G.Adj (original u) (original v) then 1 else 0)∧
      Stored "split.cost" (x (original u):ℚ) σ∧ Stored "split.large" (large:ℚ) σ)
      choose (fun _ τ => RamRational.FractionOutput ((splitInstance G x large).capacity u v:ℚ) τ) 26:=by
  have hu:=u.isLt
  have hv:=v.isLt
  have hum:=Nat.mod_lt u.val (by decide:0<2)
  have hvm:=Nat.mod_lt v.val (by decide:0<2)
  have hcost:=load_spec B "split.cost" (x (original u):ℚ) (by omega)
    (hx.1.trans_lt (by omega)) (hx.2.trans_lt (by omega)) (by decide)
  have hlarge:=load_spec B "split.large" (large:ℚ) (by omega)
    (hl.1.trans_lt (by omega)) (hl.2.trans_lt (by omega)) (by decide)
  have hzero:=RamFractionPrimitives.zero_spec B (by omega)
  have hu01:u.val%2=0∨ u.val%2=1:=by omega
  have hv01:v.val%2=0∨ v.val%2=1:=by omega
  rcases hu01 with hu0 | hu1 <;> rcases hv01 with hv0 | hv1 <;>
    by_cases hadj:G.Adj (original u) (original v)
  all_goals (first
             | (expose_names;
                 (refine
                     fun (σ:Env)
                       (a:
                         And
                           (@Eq Nat (Env.vars σ "split.u")
                             (@Fin.val
                               (Nat.mul
                                 ((2:Nat)) s)
                               u))
                           (And
                             (@Eq Nat (Env.vars σ "split.v")
                               (@Fin.val
                                 (Nat.mul
                                   ((2:Nat)) s)
                                 v))
                             (And
                               (@Eq Nat (Env.vars σ "split.up")
                                 (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod)
                                   (@Fin.val
                                     (Nat.mul
                                       ((2:Nat)) s)
                                     u)
                                   ((2:Nat))))
                               (And
                                 (@Eq Nat (Env.vars σ "split.vp")
                                   (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod)
                                     (@Fin.val
                                       (Nat.mul
                                         ((2:Nat)) s)
                                       v)
                                     ((2:Nat))))
                                 (And
                                   (@Eq Nat (Env.vars σ "restrict.edge")
                                     (@ite Nat (@SimpleGraph.Adj (Fin s) G (@original s u) (@original s v))
                                       (inst (@original s u) (@original s v)) ((1:Nat))
                                       ((0:Nat))))
                                   (And (Stored "split.cost" (@NNRat.cast Rat Rat.instNNRatCast (x (@original s u))) σ)
                                     (Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large) σ))))))) =>
                     let c0:Nat:=
                       Nat.mul ((2:Nat)) s;
                     let c1:Fin c0→ Nat:= @Fin.val c0;
                     let c2:Nat:=c1 u;
                     let c3:Prop:= @Eq Nat (Env.vars σ "split.u") c2;
                     let c4:Nat:=c1 v;
                     let c5:Prop:= @Eq Nat (Env.vars σ "split.v") c4;
                     let c6:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod);
                     let c7:Prop:=
                       @Eq Nat (Env.vars σ "split.up") (c6 c2 ((2:Nat)));
                     let c8:Prop:=
                       @Eq Nat (Env.vars σ "split.vp") (c6 c4 ((2:Nat)));
                     let c9:Prop:=
                       @Eq Nat (Env.vars σ "restrict.edge")
                         (@ite Nat (@SimpleGraph.Adj (Fin s) G (@original s u) (@original s v)) (inst (@original s u) (@original s v))
                           ((1:Nat))
                           ((0:Nat)));
                     let c10:Rat:= @NNRat.cast Rat Rat.instNNRatCast (x (@original s u));
                     let c11:Env→ Prop:=Stored "split.cost" c10;
                     let c12:Prop:=c11 σ;
                     let c13:Prop:=Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large) σ;
                     let c14:Prop:=And c12 c13;
                     let c15:Prop:=And c9 c14;
                     let c16:Prop:=And c8 c15;
                     let c17:Prop:=And c7 c16;
                     let c18:Prop:=And c5 c17;
                     let c19:Env→ Prop:=
                       RamRational.FractionOutput
                         (@NNRat.cast Rat Rat.instNNRatCast
                           (@Lax455465.RationalEncoding.RationalInstance.capacity c0 (@splitInstance s G inst x large) u v));
                     let c20:Env→ Prop:=(fun (x_1 τ:Env) => c19 τ) σ;
                     let c21:Env→ Prop:=fun (σ':Env) =>
                       And (Run B choose σ σ' ((26:Nat))) (c20 σ');
                     let c22:Prop:= @Exists Env c21;
                     let c23:Prop:= @Eq Nat (Env.vars σ "split.up") ((0:Nat));
                     let c24:Prop:=Not c23;
                     let c25:Nat→ Nat→ Nat:=Nat.add;
                     let c26:Nat:=c25 (Env.vars σ "split.u") ((1:Nat));
                     let c27:Prop:= @Eq Nat (Env.vars σ "split.v") c26;
                     let c28:Prop:=Not c27;
                     let c29:Env→ Prop:=RamRational.FractionOutput c10;
                     let c30:Env→ Prop:=fun (σ':Env) =>
                       And (Run B (load "split.cost") σ σ' ((6:Nat))) (c29 σ');
                     let c31:Nat→ Nat:=c25 ((1:Nat));
                     let c32:Cond:=
                       Cond.eq (Expr.var "split.up") (Expr.lit ((0:Nat)));
                     let c33:Nat→ Nat:=c25 (c31 (Cond.size c32));
                     let c34:Expr:=
                       Expr.add (Expr.var "split.u") (Expr.lit ((1:Nat)));
                     let c35:Cond:=Cond.eq (Expr.var "split.v") c34;
                     let c36:Nat:=c25 (c31 (Cond.size c35)) ((6:Nat));
                     let c37:Com:=Com.ite c35 (load "split.cost") RamFractionPrimitives.zero;
                     let c38:Expr:=
                       Expr.add (Expr.var "split.v") (Expr.lit ((1:Nat)));
                     let c39:Cond:=Cond.eq c38 (Expr.var "split.u");
                     let c40:Cond:=
                       Cond.eq (Expr.var "split.vp") (Expr.lit ((0:Nat)));
                     let c41:Cond:=
                       Cond.eq (Expr.var "restrict.edge") (Expr.lit ((1:Nat)));
                     let c42:Com:=Com.ite c41 (load "split.large") RamFractionPrimitives.zero;
                     let c43:Com:=Com.ite c40 c42 RamFractionPrimitives.zero;
                     let c44:Com:=Com.ite c39 (load "split.large") c43;
                     let c45:Env→ Prop:=fun (σ':Env) =>
                       And (Run B RamFractionPrimitives.zero σ σ' ((6:Nat)))
                         (RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ');
                     let c46:Nat:=c25 (Env.vars σ "split.v") ((1:Nat));
                     let c47:Prop:= @Eq Nat c46 (Env.vars σ "split.u");
                     let c48:Prop:=Not c47;
                     let c49:Env→ Prop:=fun (σ':Env) =>
                       And (Run B (load "split.large") σ σ' ((6:Nat)))
                         (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) σ');
                     let c50:Nat→ Nat:=c25 (c31 (Cond.size c39));
                     let c51:Nat:=c50 ((6:Nat));
                     let c52:Prop:= @Eq Nat (Env.vars σ "split.vp") ((0:Nat));
                     let c53:Prop:=Not c52;
                     let c54:Prop:= @Eq Nat (Env.vars σ "restrict.edge") ((1:Nat));
                     let c55:Prop:=Not c54;
                     let c56:Nat→ Nat:=c25 (c31 (Cond.size c40));
                     let c57:Nat:=c25 (c31 (Cond.size c41)) ((6:Nat));
                     let c58:Nat:=c56 c57;
                     let c59:Nat:=c50 c58;
                     let c60:Nat:=c56 ((6:Nat));
                     let c61:Nat:=c50 c60;
                     @And.casesOn c3 c18 (fun (x_1:And c3 c18) => c22) a fun (left:c3) (right:c18) =>
                       @And.casesOn c5 c17 (fun (x_1:c18) => c22) right fun (left_1:c5) (right_1:c17) =>
                         @And.casesOn c7 c16 (fun (x_1:c17) => c22) right_1 fun (left_2:c7) (right_2:c16) =>
                           @And.casesOn c8 c15 (fun (x_1:c16) => c22) right_2 fun (left_3:c8) (right_3:c15) =>
                             @And.casesOn c9 c14 (fun (x_1:c15) => c22) right_3 fun (left_4:c9) (right_4:c14) =>
                               @And.casesOn c12 c13 (fun (x_1:c14) => c22) right_4 fun (left_5:c12) (right_5:c13) =>
                                 @Or.casesOn c23 c24 (fun (x_1:Or c23 c24) => c22) (Classical.em c23)
                                   (fun (hcase:c23) =>
                                     @Or.casesOn c27 c28 (fun (x_1:Or c27 c28) => c22) (Classical.em c27)
                                       (fun (hcase_1:c27) =>
                                         @Exists.casesOn Env c30 (fun (x_1:@Exists Env c30) => c22)
                                           (RunStep.use B c11 (load "split.cost") (fun (x_1 τ:Env) => c29 τ)
                                             ((6:Nat)) hcost σ ?_)
                                           fun (w:Env)
                                             (h:
                                               And
                                                 (Run B (load "split.cost") σ w
                                                   ((6:Nat)))
                                                 (c29 w)) =>
                                           let c0_1:Prop:=
                                             Run B (load "split.cost") σ w ((6:Nat));
                                           @And.casesOn c0_1 (c29 w) (fun (x_1:And c0_1 (c29 w)) => c22) h
                                             fun (left_6:c0_1) (right_6:c29 w) =>
                                             @Exists.intro Env c21 w
                                               (@And.intro
                                                 (Run B choose σ w ((26:Nat))) (c20 w)
                                                 (RunStep.mono B choose σ w (c33 c36)
                                                   ((26:Nat))
                                                   (RunStep.ite_true B c32 c37 c44 σ w c36
                                                     (RunStep.cond_eq_true B σ (Expr.var "split.up")
                                                       (Expr.lit ((0:Nat)))
                                                       (Env.vars σ "split.up")
                                                       ((0:Nat))
                                                       (RunStep.eval_var B σ "split.up"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_lit B ((0:Nat)) σ
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase)
                                                     (RunStep.ite_true B c35 (load "split.cost") RamFractionPrimitives.zero σ w
                                                       ((6:Nat))
                                                       (RunStep.cond_eq_true B σ (Expr.var "split.v") c34 (Env.vars σ "split.v") c26
                                                         (RunStep.eval_var B σ "split.v"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_add B σ (Expr.var "split.u")
                                                           (Expr.lit ((1:Nat)))
                                                           (Env.vars σ "split.u")
                                                           ((1:Nat))
                                                           (RunStep.eval_var B σ "split.u"
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           (RunStep.eval_lit B
                                                             ((1:Nat)) σ
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase_1)
                                                       left_6))
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ?_))
                                       fun (hcase_1:c28) =>
                                       @Exists.casesOn Env c45 (fun (x_1:@Exists Env c45) => c22)
                                         (RunStep.use B (fun (x_1:Env) => True) RamFractionPrimitives.zero
                                           (fun (x_1 τ:Env) =>
                                             RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ)
                                           ((6:Nat)) hzero σ ?_)
                                         fun (w:Env)
                                           (h:
                                             And
                                               (Run B RamFractionPrimitives.zero σ w
                                                 ((6:Nat)))
                                               (RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                 w)) =>
                                         let c0_1:Prop:=
                                           Run B RamFractionPrimitives.zero σ w
                                             ((6:Nat));
                                         let c1_1:Prop:=
                                           RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w;
                                         @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c22) h
                                           fun (left_6:c0_1) (right_6:c1_1) =>
                                           @Exists.intro Env c21 w
                                             (@And.intro (Run B choose σ w ((26:Nat)))
                                               (c20 w)
                                               (RunStep.mono B choose σ w (c33 c36)
                                                 ((26:Nat))
                                                 (RunStep.ite_true B c32 c37 c44 σ w c36
                                                   (RunStep.cond_eq_true B σ (Expr.var "split.up")
                                                     (Expr.lit ((0:Nat)))
                                                     (Env.vars σ "split.up") ((0:Nat))
                                                     (RunStep.eval_var B σ "split.up"
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     (RunStep.eval_lit B ((0:Nat)) σ
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     hcase)
                                                   (RunStep.ite_false B c35 (load "split.cost") RamFractionPrimitives.zero σ w
                                                     ((6:Nat))
                                                     (RunStep.cond_eq_false B σ (Expr.var "split.v") c34 (Env.vars σ "split.v") c26
                                                       (RunStep.eval_var B σ "split.v"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_add B σ (Expr.var "split.u")
                                                         (Expr.lit ((1:Nat)))
                                                         (Env.vars σ "split.u")
                                                         ((1:Nat))
                                                         (RunStep.eval_var B σ "split.u"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((1:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase_1)
                                                     left_6))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_))
                                   fun (hcase:c24) =>
                                   @Or.casesOn c47 c48 (fun (x_1:Or c47 c48) => c22) (Classical.em c47)
                                     (fun (hcase_1:c47) =>
                                       @Exists.casesOn Env c49 (fun (x_1:@Exists Env c49) => c22)
                                         (RunStep.use B (Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large))
                                           (load "split.large")
                                           (fun (x_1 τ:Env) =>
                                             RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) τ)
                                           ((6:Nat)) hlarge σ ?_)
                                         fun (w:Env)
                                           (h:
                                             And
                                               (Run B (load "split.large") σ w
                                                 ((6:Nat)))
                                               (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                         let c0_1:Prop:=
                                           Run B (load "split.large") σ w ((6:Nat));
                                         @And.casesOn c0_1 (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)
                                           (fun
                                               (x_1:
                                                 And c0_1 (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                             c22)
                                           h
                                           fun (left_6:c0_1)
                                             (right_6:RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w) =>
                                           @Exists.intro Env c21 w
                                             (@And.intro (Run B choose σ w ((26:Nat)))
                                               (c20 w)
                                               (RunStep.mono B choose σ w (c33 c51)
                                                 ((26:Nat))
                                                 (RunStep.ite_false B c32 c37 c44 σ w c51
                                                   (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                     (Expr.lit ((0:Nat)))
                                                     (Env.vars σ "split.up") ((0:Nat))
                                                     (RunStep.eval_var B σ "split.up"
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     (RunStep.eval_lit B ((0:Nat)) σ
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     hcase)
                                                   (RunStep.ite_true B c39 (load "split.large") c43 σ w
                                                     ((6:Nat))
                                                     (RunStep.cond_eq_true B σ c38 (Expr.var "split.u") c46 (Env.vars σ "split.u")
                                                       (RunStep.eval_add B σ (Expr.var "split.v")
                                                         (Expr.lit ((1:Nat)))
                                                         (Env.vars σ "split.v")
                                                         ((1:Nat))
                                                         (RunStep.eval_var B σ "split.v"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((1:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_var B σ "split.u"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase_1)
                                                     left_6))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_))
                                     fun (hcase_1:c48) =>
                                     @Or.casesOn c52 c53 (fun (x_1:Or c52 c53) => c22) (Classical.em c52)
                                       (fun (hcase_2:c52) =>
                                         @Or.casesOn c54 c55 (fun (x_1:Or c54 c55) => c22) (Classical.em c54)
                                           (fun (hcase_3:c54) =>
                                             @Exists.casesOn Env c49 (fun (x_1:@Exists Env c49) => c22)
                                               (RunStep.use B (Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large))
                                                 (load "split.large")
                                                 (fun (x_1 τ:Env) =>
                                                   RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) τ)
                                                 ((6:Nat)) hlarge σ ?_)
                                               fun (w:Env)
                                                 (h:
                                                   And
                                                     (Run B (load "split.large") σ w
                                                       ((6:Nat)))
                                                     (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                               let c0_1:Prop:=
                                                 Run B (load "split.large") σ w
                                                   ((6:Nat));
                                               @And.casesOn c0_1
                                                 (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)
                                                 (fun
                                                     (x_1:
                                                       And c0_1
                                                         (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                                   c22)
                                                 h
                                                 fun (left_6:c0_1)
                                                   (right_6:
                                                     RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w) =>
                                                 @Exists.intro Env c21 w
                                                   (@And.intro
                                                     (Run B choose σ w ((26:Nat)))
                                                     (c20 w)
                                                     (RunStep.mono B choose σ w (c33 c59)
                                                       ((26:Nat))
                                                       (RunStep.ite_false B c32 c37 c44 σ w c59
                                                         (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                           (Expr.lit ((0:Nat)))
                                                           (Env.vars σ "split.up")
                                                           ((0:Nat))
                                                           (RunStep.eval_var B σ "split.up"
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           (RunStep.eval_lit B
                                                             ((0:Nat)) σ
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           hcase)
                                                         (RunStep.ite_false B c39 (load "split.large") c43 σ w c58
                                                           (RunStep.cond_eq_false B σ c38 (Expr.var "split.u") c46
                                                             (Env.vars σ "split.u")
                                                             (RunStep.eval_add B σ (Expr.var "split.v")
                                                               (Expr.lit ((1:Nat)))
                                                               (Env.vars σ "split.v")
                                                               ((1:Nat))
                                                               (RunStep.eval_var B σ "split.v"
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               (RunStep.eval_lit B
                                                                 ((1:Nat)) σ
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             (RunStep.eval_var B σ "split.u"
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             hcase_1)
                                                           (RunStep.ite_true B c40 c42 RamFractionPrimitives.zero σ w c57
                                                             (RunStep.cond_eq_true B σ (Expr.var "split.vp")
                                                               (Expr.lit ((0:Nat)))
                                                               (Env.vars σ "split.vp")
                                                               ((0:Nat))
                                                               (RunStep.eval_var B σ "split.vp"
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               (RunStep.eval_lit B
                                                                 ((0:Nat)) σ
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               hcase_2)
                                                             (RunStep.ite_true B c41 (load "split.large") RamFractionPrimitives.zero σ
                                                               w ((6:Nat))
                                                               (RunStep.cond_eq_true B σ (Expr.var "restrict.edge")
                                                                 (Expr.lit ((1:Nat)))
                                                                 (Env.vars σ "restrict.edge")
                                                                 ((1:Nat))
                                                                 (RunStep.eval_var B σ "restrict.edge"
                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                 (RunStep.eval_lit B
                                                                   ((1:Nat)) σ
                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                 hcase_3)
                                                               left_6))))
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     ?_))
                                           fun (hcase_3:c55) =>
                                           @Exists.casesOn Env c45 (fun (x_1:@Exists Env c45) => c22)
                                             (RunStep.use B (fun (x_1:Env) => True) RamFractionPrimitives.zero
                                               (fun (x_1 τ:Env) =>
                                                 RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                   τ)
                                               ((6:Nat)) hzero σ ?_)
                                             fun (w:Env)
                                               (h:
                                                 And
                                                   (Run B RamFractionPrimitives.zero σ w
                                                     ((6:Nat)))
                                                   (RamRational.FractionOutput
                                                     (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) =>
                                             let c0_1:Prop:=
                                               Run B RamFractionPrimitives.zero σ w
                                                 ((6:Nat));
                                             let c1_1:Prop:=
                                               RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                 w;
                                             @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c22) h
                                               fun (left_6:c0_1) (right_6:c1_1) =>
                                               @Exists.intro Env c21 w
                                                 (@And.intro
                                                   (Run B choose σ w ((26:Nat)))
                                                   (c20 w)
                                                   (RunStep.mono B choose σ w (c33 c59)
                                                     ((26:Nat))
                                                     (RunStep.ite_false B c32 c37 c44 σ w c59
                                                       (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                         (Expr.lit ((0:Nat)))
                                                         (Env.vars σ "split.up")
                                                         ((0:Nat))
                                                         (RunStep.eval_var B σ "split.up"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((0:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase)
                                                       (RunStep.ite_false B c39 (load "split.large") c43 σ w c58
                                                         (RunStep.cond_eq_false B σ c38 (Expr.var "split.u") c46 (Env.vars σ "split.u")
                                                           (RunStep.eval_add B σ (Expr.var "split.v")
                                                             (Expr.lit ((1:Nat)))
                                                             (Env.vars σ "split.v")
                                                             ((1:Nat))
                                                             (RunStep.eval_var B σ "split.v"
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             (RunStep.eval_lit B
                                                               ((1:Nat)) σ
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           (RunStep.eval_var B σ "split.u"
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           hcase_1)
                                                         (RunStep.ite_true B c40 c42 RamFractionPrimitives.zero σ w c57
                                                           (RunStep.cond_eq_true B σ (Expr.var "split.vp")
                                                             (Expr.lit ((0:Nat)))
                                                             (Env.vars σ "split.vp")
                                                             ((0:Nat))
                                                             (RunStep.eval_var B σ "split.vp"
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             (RunStep.eval_lit B
                                                               ((0:Nat)) σ
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             hcase_2)
                                                           (RunStep.ite_false B c41 (load "split.large") RamFractionPrimitives.zero σ w
                                                             ((6:Nat))
                                                             (RunStep.cond_eq_false B σ (Expr.var "restrict.edge")
                                                               (Expr.lit ((1:Nat)))
                                                               (Env.vars σ "restrict.edge")
                                                               ((1:Nat))
                                                               (RunStep.eval_var B σ "restrict.edge"
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               (RunStep.eval_lit B
                                                                 ((1:Nat)) σ
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               hcase_3)
                                                             left_6))))
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   ?_))
                                       fun (hcase_2:c53) =>
                                       @Exists.casesOn Env c45 (fun (x_1:@Exists Env c45) => c22)
                                         (RunStep.use B (fun (x_1:Env) => True) RamFractionPrimitives.zero
                                           (fun (x_1 τ:Env) =>
                                             RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ)
                                           ((6:Nat)) hzero σ ?_)
                                         fun (w:Env)
                                           (h:
                                             And
                                               (Run B RamFractionPrimitives.zero σ w
                                                 ((6:Nat)))
                                               (RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                 w)) =>
                                         let c0_1:Prop:=
                                           Run B RamFractionPrimitives.zero σ w
                                             ((6:Nat));
                                         let c1_1:Prop:=
                                           RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w;
                                         @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c22) h
                                           fun (left_6:c0_1) (right_6:c1_1) =>
                                           @Exists.intro Env c21 w
                                             (@And.intro (Run B choose σ w ((26:Nat)))
                                               (c20 w)
                                               (RunStep.mono B choose σ w (c33 c61)
                                                 ((26:Nat))
                                                 (RunStep.ite_false B c32 c37 c44 σ w c61
                                                   (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                     (Expr.lit ((0:Nat)))
                                                     (Env.vars σ "split.up") ((0:Nat))
                                                     (RunStep.eval_var B σ "split.up"
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     (RunStep.eval_lit B ((0:Nat)) σ
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     hcase)
                                                   (RunStep.ite_false B c39 (load "split.large") c43 σ w c60
                                                     (RunStep.cond_eq_false B σ c38 (Expr.var "split.u") c46 (Env.vars σ "split.u")
                                                       (RunStep.eval_add B σ (Expr.var "split.v")
                                                         (Expr.lit ((1:Nat)))
                                                         (Env.vars σ "split.v")
                                                         ((1:Nat))
                                                         (RunStep.eval_var B σ "split.v"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((1:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_var B σ "split.u"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase_1)
                                                     (RunStep.ite_false B c40 c42 RamFractionPrimitives.zero σ w
                                                       ((6:Nat))
                                                       (RunStep.cond_eq_false B σ (Expr.var "split.vp")
                                                         (Expr.lit ((0:Nat)))
                                                         (Env.vars σ "split.vp")
                                                         ((0:Nat))
                                                         (RunStep.eval_var B σ "split.vp"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((0:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase_2)
                                                       left_6)))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (all_goals try clear h); (all_goals try clear left_6))
             | (expose_names;
                 (refine
                     fun (σ:Env)
                       (a:
                         And
                           (@Eq Nat (Env.vars σ "split.u")
                             (@Fin.val
                               (Nat.mul
                                 ((2:Nat)) s)
                               u))
                           (And
                             (@Eq Nat (Env.vars σ "split.v")
                               (@Fin.val
                                 (Nat.mul
                                   ((2:Nat)) s)
                                 v))
                             (And
                               (@Eq Nat (Env.vars σ "split.up")
                                 (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod)
                                   (@Fin.val
                                     (Nat.mul
                                       ((2:Nat)) s)
                                     u)
                                   ((2:Nat))))
                               (And
                                 (@Eq Nat (Env.vars σ "split.vp")
                                   (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod)
                                     (@Fin.val
                                       (Nat.mul
                                         ((2:Nat)) s)
                                       v)
                                     ((2:Nat))))
                                 (And
                                   (@Eq Nat (Env.vars σ "restrict.edge")
                                     (@ite Nat (@SimpleGraph.Adj (Fin s) G (@original s u) (@original s v))
                                       (inst (@original s u) (@original s v)) ((1:Nat))
                                       ((0:Nat))))
                                   (And (Stored "split.cost" (@NNRat.cast Rat Rat.instNNRatCast (x (@original s u))) σ)
                                     (Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large) σ))))))) =>
                     let c0:Nat:=
                       Nat.mul ((2:Nat)) s;
                     let c1:Fin c0→ Nat:= @Fin.val c0;
                     let c2:Nat:=c1 u;
                     let c3:Prop:= @Eq Nat (Env.vars σ "split.u") c2;
                     let c4:Nat:=c1 v;
                     let c5:Prop:= @Eq Nat (Env.vars σ "split.v") c4;
                     let c6:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod);
                     let c7:Prop:=
                       @Eq Nat (Env.vars σ "split.up") (c6 c2 ((2:Nat)));
                     let c8:Prop:=
                       @Eq Nat (Env.vars σ "split.vp") (c6 c4 ((2:Nat)));
                     let c9:Prop:=
                       @Eq Nat (Env.vars σ "restrict.edge")
                         (@ite Nat (@SimpleGraph.Adj (Fin s) G (@original s u) (@original s v)) (inst (@original s u) (@original s v))
                           ((1:Nat))
                           ((0:Nat)));
                     let c10:Rat:= @NNRat.cast Rat Rat.instNNRatCast (x (@original s u));
                     let c11:Env→ Prop:=Stored "split.cost" c10;
                     let c12:Prop:=c11 σ;
                     let c13:Prop:=Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large) σ;
                     let c14:Prop:=And c12 c13;
                     let c15:Prop:=And c9 c14;
                     let c16:Prop:=And c8 c15;
                     let c17:Prop:=And c7 c16;
                     let c18:Prop:=And c5 c17;
                     let c19:Env→ Prop:=
                       RamRational.FractionOutput
                         (@NNRat.cast Rat Rat.instNNRatCast
                           (@Lax455465.RationalEncoding.RationalInstance.capacity c0 (@splitInstance s G inst x large) u v));
                     let c20:Env→ Prop:=(fun (x_1 τ:Env) => c19 τ) σ;
                     let c21:Env→ Prop:=fun (σ':Env) =>
                       And (Run B choose σ σ' ((26:Nat))) (c20 σ');
                     let c22:Prop:= @Exists Env c21;
                     let c23:Prop:= @Eq Nat (Env.vars σ "split.up") ((0:Nat));
                     let c24:Prop:=Not c23;
                     let c25:Nat→ Nat→ Nat:=Nat.add;
                     let c26:Nat:=c25 (Env.vars σ "split.u") ((1:Nat));
                     let c27:Prop:= @Eq Nat (Env.vars σ "split.v") c26;
                     let c28:Prop:=Not c27;
                     let c29:Env→ Prop:=RamRational.FractionOutput c10;
                     let c30:Env→ Prop:=fun (σ':Env) =>
                       And (Run B (load "split.cost") σ σ' ((6:Nat))) (c29 σ');
                     let c31:Nat→ Nat:=c25 ((1:Nat));
                     let c32:Cond:=
                       Cond.eq (Expr.var "split.up") (Expr.lit ((0:Nat)));
                     let c33:Nat→ Nat:=c25 (c31 (Cond.size c32));
                     let c34:Expr:=
                       Expr.add (Expr.var "split.u") (Expr.lit ((1:Nat)));
                     let c35:Cond:=Cond.eq (Expr.var "split.v") c34;
                     let c36:Nat:=c25 (c31 (Cond.size c35)) ((6:Nat));
                     let c37:Com:=Com.ite c35 (load "split.cost") RamFractionPrimitives.zero;
                     let c38:Expr:=
                       Expr.add (Expr.var "split.v") (Expr.lit ((1:Nat)));
                     let c39:Cond:=Cond.eq c38 (Expr.var "split.u");
                     let c40:Cond:=
                       Cond.eq (Expr.var "split.vp") (Expr.lit ((0:Nat)));
                     let c41:Cond:=
                       Cond.eq (Expr.var "restrict.edge") (Expr.lit ((1:Nat)));
                     let c42:Com:=Com.ite c41 (load "split.large") RamFractionPrimitives.zero;
                     let c43:Com:=Com.ite c40 c42 RamFractionPrimitives.zero;
                     let c44:Com:=Com.ite c39 (load "split.large") c43;
                     let c45:Env→ Prop:=fun (σ':Env) =>
                       And (Run B RamFractionPrimitives.zero σ σ' ((6:Nat)))
                         (RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ');
                     let c46:Nat:=c25 (Env.vars σ "split.v") ((1:Nat));
                     let c47:Prop:= @Eq Nat c46 (Env.vars σ "split.u");
                     let c48:Prop:=Not c47;
                     let c49:Env→ Prop:=fun (σ':Env) =>
                       And (Run B (load "split.large") σ σ' ((6:Nat)))
                         (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) σ');
                     let c50:Nat→ Nat:=c25 (c31 (Cond.size c39));
                     let c51:Nat:=c50 ((6:Nat));
                     let c52:Prop:= @Eq Nat (Env.vars σ "split.vp") ((0:Nat));
                     let c53:Prop:=Not c52;
                     let c54:Prop:= @Eq Nat (Env.vars σ "restrict.edge") ((1:Nat));
                     let c55:Prop:=Not c54;
                     let c56:Nat→ Nat:=c25 (c31 (Cond.size c40));
                     let c57:Nat:=c25 (c31 (Cond.size c41)) ((6:Nat));
                     let c58:Nat:=c56 c57;
                     let c59:Nat:=c50 c58;
                     let c60:Nat:=c56 ((6:Nat));
                     let c61:Nat:=c50 c60;
                     @And.casesOn c3 c18 (fun (x_1:And c3 c18) => c22) a fun (left:c3) (right:c18) =>
                       @And.casesOn c5 c17 (fun (x_1:c18) => c22) right fun (left_1:c5) (right_1:c17) =>
                         @And.casesOn c7 c16 (fun (x_1:c17) => c22) right_1 fun (left_2:c7) (right_2:c16) =>
                           @And.casesOn c8 c15 (fun (x_1:c16) => c22) right_2 fun (left_3:c8) (right_3:c15) =>
                             @And.casesOn c9 c14 (fun (x_1:c15) => c22) right_3 fun (left_4:c9) (right_4:c14) =>
                               @And.casesOn c12 c13 (fun (x_1:c14) => c22) right_4 fun (left_5:c12) (right_5:c13) =>
                                 @Or.casesOn c23 c24 (fun (x_1:Or c23 c24) => c22) (Classical.em c23)
                                   (fun (hcase:c23) =>
                                     @Or.casesOn c27 c28 (fun (x_1:Or c27 c28) => c22) (Classical.em c27)
                                       (fun (hcase_1:c27) =>
                                         @Exists.casesOn Env c30 (fun (x_1:@Exists Env c30) => c22)
                                           (RunStep.use B c11 (load "split.cost") (fun (x_1 τ:Env) => c29 τ)
                                             ((6:Nat)) hcost σ ?_)
                                           fun (w:Env)
                                             (h:
                                               And
                                                 (Run B (load "split.cost") σ w
                                                   ((6:Nat)))
                                                 (c29 w)) =>
                                           let c0_1:Prop:=
                                             Run B (load "split.cost") σ w ((6:Nat));
                                           @And.casesOn c0_1 (c29 w) (fun (x_1:And c0_1 (c29 w)) => c22) h
                                             fun (left_6:c0_1) (right_6:c29 w) =>
                                             @Exists.intro Env c21 w
                                               (@And.intro
                                                 (Run B choose σ w ((26:Nat))) (c20 w)
                                                 (RunStep.mono B choose σ w (c33 c36)
                                                   ((26:Nat))
                                                   (RunStep.ite_true B c32 c37 c44 σ w c36
                                                     (RunStep.cond_eq_true B σ (Expr.var "split.up")
                                                       (Expr.lit ((0:Nat)))
                                                       (Env.vars σ "split.up")
                                                       ((0:Nat))
                                                       (RunStep.eval_var B σ "split.up"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_lit B ((0:Nat)) σ
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase)
                                                     (RunStep.ite_true B c35 (load "split.cost") RamFractionPrimitives.zero σ w
                                                       ((6:Nat))
                                                       (RunStep.cond_eq_true B σ (Expr.var "split.v") c34 (Env.vars σ "split.v") c26
                                                         (RunStep.eval_var B σ "split.v"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_add B σ (Expr.var "split.u")
                                                           (Expr.lit ((1:Nat)))
                                                           (Env.vars σ "split.u")
                                                           ((1:Nat))
                                                           (RunStep.eval_var B σ "split.u"
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           (RunStep.eval_lit B
                                                             ((1:Nat)) σ
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase_1)
                                                       left_6))
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ?_))
                                       fun (hcase_1:c28) =>
                                       @Exists.casesOn Env c45 (fun (x_1:@Exists Env c45) => c22)
                                         (RunStep.use B (fun (x_1:Env) => True) RamFractionPrimitives.zero
                                           (fun (x_1 τ:Env) =>
                                             RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ)
                                           ((6:Nat)) hzero σ ?_)
                                         fun (w:Env)
                                           (h:
                                             And
                                               (Run B RamFractionPrimitives.zero σ w
                                                 ((6:Nat)))
                                               (RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                 w)) =>
                                         let c0_1:Prop:=
                                           Run B RamFractionPrimitives.zero σ w
                                             ((6:Nat));
                                         let c1_1:Prop:=
                                           RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w;
                                         @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c22) h
                                           fun (left_6:c0_1) (right_6:c1_1) =>
                                           @Exists.intro Env c21 w
                                             (@And.intro (Run B choose σ w ((26:Nat)))
                                               (c20 w)
                                               (RunStep.mono B choose σ w (c33 c36)
                                                 ((26:Nat))
                                                 (RunStep.ite_true B c32 c37 c44 σ w c36
                                                   (RunStep.cond_eq_true B σ (Expr.var "split.up")
                                                     (Expr.lit ((0:Nat)))
                                                     (Env.vars σ "split.up") ((0:Nat))
                                                     (RunStep.eval_var B σ "split.up"
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     (RunStep.eval_lit B ((0:Nat)) σ
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     hcase)
                                                   (RunStep.ite_false B c35 (load "split.cost") RamFractionPrimitives.zero σ w
                                                     ((6:Nat))
                                                     (RunStep.cond_eq_false B σ (Expr.var "split.v") c34 (Env.vars σ "split.v") c26
                                                       (RunStep.eval_var B σ "split.v"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_add B σ (Expr.var "split.u")
                                                         (Expr.lit ((1:Nat)))
                                                         (Env.vars σ "split.u")
                                                         ((1:Nat))
                                                         (RunStep.eval_var B σ "split.u"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((1:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase_1)
                                                     left_6))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_))
                                   fun (hcase:c24) =>
                                   @Or.casesOn c47 c48 (fun (x_1:Or c47 c48) => c22) (Classical.em c47)
                                     (fun (hcase_1:c47) =>
                                       @Exists.casesOn Env c49 (fun (x_1:@Exists Env c49) => c22)
                                         (RunStep.use B (Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large))
                                           (load "split.large")
                                           (fun (x_1 τ:Env) =>
                                             RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) τ)
                                           ((6:Nat)) hlarge σ ?_)
                                         fun (w:Env)
                                           (h:
                                             And
                                               (Run B (load "split.large") σ w
                                                 ((6:Nat)))
                                               (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                         let c0_1:Prop:=
                                           Run B (load "split.large") σ w ((6:Nat));
                                         @And.casesOn c0_1 (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)
                                           (fun
                                               (x_1:
                                                 And c0_1 (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                             c22)
                                           h
                                           fun (left_6:c0_1)
                                             (right_6:RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w) =>
                                           @Exists.intro Env c21 w
                                             (@And.intro (Run B choose σ w ((26:Nat)))
                                               (c20 w)
                                               (RunStep.mono B choose σ w (c33 c51)
                                                 ((26:Nat))
                                                 (RunStep.ite_false B c32 c37 c44 σ w c51
                                                   (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                     (Expr.lit ((0:Nat)))
                                                     (Env.vars σ "split.up") ((0:Nat))
                                                     (RunStep.eval_var B σ "split.up"
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     (RunStep.eval_lit B ((0:Nat)) σ
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     hcase)
                                                   (RunStep.ite_true B c39 (load "split.large") c43 σ w
                                                     ((6:Nat))
                                                     (RunStep.cond_eq_true B σ c38 (Expr.var "split.u") c46 (Env.vars σ "split.u")
                                                       (RunStep.eval_add B σ (Expr.var "split.v")
                                                         (Expr.lit ((1:Nat)))
                                                         (Env.vars σ "split.v")
                                                         ((1:Nat))
                                                         (RunStep.eval_var B σ "split.v"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((1:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_var B σ "split.u"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase_1)
                                                     left_6))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_))
                                     fun (hcase_1:c48) =>
                                     @Or.casesOn c52 c53 (fun (x_1:Or c52 c53) => c22) (Classical.em c52)
                                       (fun (hcase_2:c52) =>
                                         @Or.casesOn c54 c55 (fun (x_1:Or c54 c55) => c22) (Classical.em c54)
                                           (fun (hcase_3:c54) =>
                                             @Exists.casesOn Env c49 (fun (x_1:@Exists Env c49) => c22)
                                               (RunStep.use B (Stored "split.large" (@NNRat.cast Rat Rat.instNNRatCast large))
                                                 (load "split.large")
                                                 (fun (x_1 τ:Env) =>
                                                   RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) τ)
                                                 ((6:Nat)) hlarge σ ?_)
                                               fun (w:Env)
                                                 (h:
                                                   And
                                                     (Run B (load "split.large") σ w
                                                       ((6:Nat)))
                                                     (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                               let c0_1:Prop:=
                                                 Run B (load "split.large") σ w
                                                   ((6:Nat));
                                               @And.casesOn c0_1
                                                 (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)
                                                 (fun
                                                     (x_1:
                                                       And c0_1
                                                         (RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w)) =>
                                                   c22)
                                                 h
                                                 fun (left_6:c0_1)
                                                   (right_6:
                                                     RamRational.FractionOutput (@NNRat.cast Rat Rat.instNNRatCast large) w) =>
                                                 @Exists.intro Env c21 w
                                                   (@And.intro
                                                     (Run B choose σ w ((26:Nat)))
                                                     (c20 w)
                                                     (RunStep.mono B choose σ w (c33 c59)
                                                       ((26:Nat))
                                                       (RunStep.ite_false B c32 c37 c44 σ w c59
                                                         (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                           (Expr.lit ((0:Nat)))
                                                           (Env.vars σ "split.up")
                                                           ((0:Nat))
                                                           (RunStep.eval_var B σ "split.up"
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           (RunStep.eval_lit B
                                                             ((0:Nat)) σ
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           hcase)
                                                         (RunStep.ite_false B c39 (load "split.large") c43 σ w c58
                                                           (RunStep.cond_eq_false B σ c38 (Expr.var "split.u") c46
                                                             (Env.vars σ "split.u")
                                                             (RunStep.eval_add B σ (Expr.var "split.v")
                                                               (Expr.lit ((1:Nat)))
                                                               (Env.vars σ "split.v")
                                                               ((1:Nat))
                                                               (RunStep.eval_var B σ "split.v"
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               (RunStep.eval_lit B
                                                                 ((1:Nat)) σ
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             (RunStep.eval_var B σ "split.u"
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             hcase_1)
                                                           (RunStep.ite_true B c40 c42 RamFractionPrimitives.zero σ w c57
                                                             (RunStep.cond_eq_true B σ (Expr.var "split.vp")
                                                               (Expr.lit ((0:Nat)))
                                                               (Env.vars σ "split.vp")
                                                               ((0:Nat))
                                                               (RunStep.eval_var B σ "split.vp"
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               (RunStep.eval_lit B
                                                                 ((0:Nat)) σ
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               hcase_2)
                                                             (RunStep.ite_true B c41 (load "split.large") RamFractionPrimitives.zero σ
                                                               w ((6:Nat))
                                                               (RunStep.cond_eq_true B σ (Expr.var "restrict.edge")
                                                                 (Expr.lit ((1:Nat)))
                                                                 (Env.vars σ "restrict.edge")
                                                                 ((1:Nat))
                                                                 (RunStep.eval_var B σ "restrict.edge"
                                                                   ?_)
                                                                 (RunStep.eval_lit B
                                                                   ((1:Nat)) σ
                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                 hcase_3)
                                                               left_6))))
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     ?_))
                                           fun (hcase_3:c55) =>
                                           @Exists.casesOn Env c45 (fun (x_1:@Exists Env c45) => c22)
                                             (RunStep.use B (fun (x_1:Env) => True) RamFractionPrimitives.zero
                                               (fun (x_1 τ:Env) =>
                                                 RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                   τ)
                                               ((6:Nat)) hzero σ ?_)
                                             fun (w:Env)
                                               (h:
                                                 And
                                                   (Run B RamFractionPrimitives.zero σ w
                                                     ((6:Nat)))
                                                   (RamRational.FractionOutput
                                                     (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) =>
                                             let c0_1:Prop:=
                                               Run B RamFractionPrimitives.zero σ w
                                                 ((6:Nat));
                                             let c1_1:Prop:=
                                               RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                 w;
                                             @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c22) h
                                               fun (left_6:c0_1) (right_6:c1_1) =>
                                               @Exists.intro Env c21 w
                                                 (@And.intro
                                                   (Run B choose σ w ((26:Nat)))
                                                   (c20 w)
                                                   (RunStep.mono B choose σ w (c33 c59)
                                                     ((26:Nat))
                                                     (RunStep.ite_false B c32 c37 c44 σ w c59
                                                       (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                         (Expr.lit ((0:Nat)))
                                                         (Env.vars σ "split.up")
                                                         ((0:Nat))
                                                         (RunStep.eval_var B σ "split.up"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((0:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase)
                                                       (RunStep.ite_false B c39 (load "split.large") c43 σ w c58
                                                         (RunStep.cond_eq_false B σ c38 (Expr.var "split.u") c46 (Env.vars σ "split.u")
                                                           (RunStep.eval_add B σ (Expr.var "split.v")
                                                             (Expr.lit ((1:Nat)))
                                                             (Env.vars σ "split.v")
                                                             ((1:Nat))
                                                             (RunStep.eval_var B σ "split.v"
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             (RunStep.eval_lit B
                                                               ((1:Nat)) σ
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           (RunStep.eval_var B σ "split.u"
                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                           hcase_1)
                                                         (RunStep.ite_true B c40 c42 RamFractionPrimitives.zero σ w c57
                                                           (RunStep.cond_eq_true B σ (Expr.var "split.vp")
                                                             (Expr.lit ((0:Nat)))
                                                             (Env.vars σ "split.vp")
                                                             ((0:Nat))
                                                             (RunStep.eval_var B σ "split.vp"
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             (RunStep.eval_lit B
                                                               ((0:Nat)) σ
                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                             hcase_2)
                                                           (RunStep.ite_false B c41 (load "split.large") RamFractionPrimitives.zero σ w
                                                             ((6:Nat))
                                                             (RunStep.cond_eq_false B σ (Expr.var "restrict.edge")
                                                               (Expr.lit ((1:Nat)))
                                                               (Env.vars σ "restrict.edge")
                                                               ((1:Nat))
                                                               (RunStep.eval_var B σ "restrict.edge"
                                                                 ?_)
                                                               (RunStep.eval_lit B
                                                                 ((1:Nat)) σ
                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                               hcase_3)
                                                             left_6))))
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   ?_))
                                       fun (hcase_2:c53) =>
                                       @Exists.casesOn Env c45 (fun (x_1:@Exists Env c45) => c22)
                                         (RunStep.use B (fun (x_1:Env) => True) RamFractionPrimitives.zero
                                           (fun (x_1 τ:Env) =>
                                             RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ)
                                           ((6:Nat)) hzero σ ?_)
                                         fun (w:Env)
                                           (h:
                                             And
                                               (Run B RamFractionPrimitives.zero σ w
                                                 ((6:Nat)))
                                               (RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                                 w)) =>
                                         let c0_1:Prop:=
                                           Run B RamFractionPrimitives.zero σ w
                                             ((6:Nat));
                                         let c1_1:Prop:=
                                           RamRational.FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w;
                                         @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c22) h
                                           fun (left_6:c0_1) (right_6:c1_1) =>
                                           @Exists.intro Env c21 w
                                             (@And.intro (Run B choose σ w ((26:Nat)))
                                               (c20 w)
                                               (RunStep.mono B choose σ w (c33 c61)
                                                 ((26:Nat))
                                                 (RunStep.ite_false B c32 c37 c44 σ w c61
                                                   (RunStep.cond_eq_false B σ (Expr.var "split.up")
                                                     (Expr.lit ((0:Nat)))
                                                     (Env.vars σ "split.up") ((0:Nat))
                                                     (RunStep.eval_var B σ "split.up"
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     (RunStep.eval_lit B ((0:Nat)) σ
                                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                     hcase)
                                                   (RunStep.ite_false B c39 (load "split.large") c43 σ w c60
                                                     (RunStep.cond_eq_false B σ c38 (Expr.var "split.u") c46 (Env.vars σ "split.u")
                                                       (RunStep.eval_add B σ (Expr.var "split.v")
                                                         (Expr.lit ((1:Nat)))
                                                         (Env.vars σ "split.v")
                                                         ((1:Nat))
                                                         (RunStep.eval_var B σ "split.v"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((1:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       (RunStep.eval_var B σ "split.u"
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase_1)
                                                     (RunStep.ite_false B c40 c42 RamFractionPrimitives.zero σ w
                                                       ((6:Nat))
                                                       (RunStep.cond_eq_false B σ (Expr.var "split.vp")
                                                         (Expr.lit ((0:Nat)))
                                                         (Env.vars σ "split.vp")
                                                         ((0:Nat))
                                                         (RunStep.eval_var B σ "split.vp"
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         (RunStep.eval_lit B ((0:Nat))
                                                           σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase_2)
                                                       left_6)))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (all_goals try clear h); (all_goals try clear left_6))
            )
  all_goals simp_all [splitInstance]
  all_goals omega

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (i:Fin ((2*R.card)*(2*R.card)))
    (hB:4*n*n+6*n+M+20< B) (hx:∀ v,Bounded M (x v:ℚ)) (hl:Bounded M (large:ℚ)):
    Spec B (fun σ => Data G x R large σ∧ σ.vars "split.i"=i.val) command
      (fun _ τ => Data G x R large τ∧ RamRational.FractionOutput
        ((splitInstance (restriction G R) (fun v => x (label R v)) large).capacity
          (NativeBlowUp.row i) (NativeBlowUp.col i):ℚ) τ) 100:=by
  have hR:=NativeMaskUnpack.card_bound R
  let u:=NativeBlowUp.row i
  let v:=NativeBlowUp.col i
  rintro σ ⟨hd,hi⟩
  obtain ⟨σ1,r1,p1⟩:=ports_spec B R.card i (by nlinarith only [hB,Nat.mul_le_mul hR hR,hR]) σ ⟨hd.2.2.1,hi⟩
  have d1:=frame r1 hd (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩:=NativeRestrictionRead.graph_spec B n G (fun v => (x v:ℚ)) R (original u) (original v)
    (by nlinarith only [hB]) σ1 ⟨d1.1,p1.2.2.1,p1.2.2.2.1⟩
  have hrow2:σ2.vars "restrict.row"=(original u).val:=(r2.frame_var "restrict.row" (by decide)).trans p1.2.2.1
  obtain ⟨σ3,r3,p3⟩:=NativeRestrictionRead.cost_spec B M n G (fun v => (x v:ℚ)) R (original u)
    (by omega) (by omega) hx σ2 ⟨p2.1,hrow2⟩
  have hcost:=hx (label R (original u))
  obtain ⟨σ4,r4,p4⟩:=save_spec B "split.cost" (x (label R (original u)):ℚ) (by omega)
    (hcost.1.trans_lt (by omega)) (hcost.2.trans_lt (by omega)) (by decide) σ3 p3.2
  have r1234:=r1.seq (r2.seq (r3.seq r4))
  have r234:=r2.seq (r3.seq r4)
  have d4:=frame r1234 hd (by decide) (by decide)
  obtain ⟨τ,r5,p5⟩:=choose_spec B M R.card (restriction G R) (fun v => x (label R v)) large u v
    (by omega) hcost hl σ4
    ⟨(r234.frame_var "split.u" (by decide)).trans p1.1,
      (r234.frame_var "split.v" (by decide)).trans p1.2.1,
      (r234.frame_var "split.up" (by decide)).trans p1.2.2.2.2.1,
      (r234.frame_var "split.vp" (by decide)).trans p1.2.2.2.2.2,
      ((r3.seq r4).frame_var "restrict.edge" (by decide)).trans p2.2,p4,d4.2.1⟩
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr.mono (by omega),frame rr hd (by decide) (by decide),p5⟩

theorem height (M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (hM:1≤ M) (hx:∀ v,Bounded M (x v:ℚ))
    (hl:Bounded M (large:ℚ)) (u v:Fin (2*n)):
    Bounded M ((splitInstance G x large).capacity u v:ℚ):=by
  dsimp [splitInstance]
  split_ifs <;> first | exact hx _ | exact hl | exact ⟨by simp,by simpa using hM⟩

end Lax263307Proofs.NativeSplitEntry

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeSplitVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic NativeSplitEntry
open scoped NNRat

def entries {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0):List ℚ≥0:=
  List.ofFn fun i:Fin ((2*R.card)*(2*R.card)) =>
    (splitInstance (restriction G R) (fun v => x (label R v)) large).capacity
      (NativeBlowUp.row i) (NativeBlowUp.col i)

theorem matrix_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (front:List ℕ)
    (hM:1≤ M) (hB:4*n*n+6*n+M+20< B)
    (hf:front.length+2*((2*R.card)*(2*R.card))+2< B)
    (hx:∀ v,Bounded M (x v:ℚ)) (hl:Bounded M (large:ℚ)):
    Spec B (fun σ => Data G x R large σ∧ Prefix front "lp.word" σ∧ σ.vars "lp.position"=front.length∧
      front.length+2*((2*R.card)*(2*R.card))<(σ.arrs "lp.word").length) matrix
      (fun _ τ => Data G x R large τ∧ Prefix (front++RamUnsignedBuffer.encode (entries G x R large)) "lp.word" τ∧
        τ.vars "lp.position"=front.length+2*((2*R.card)*(2*R.card))) (122*((2*R.card)*(2*R.card))+6):=by
  have hh (i:Fin ((2*R.card)*(2*R.card))):=NativeSplitEntry.height M R.card (restriction G R)
    (fun v => x (label R v)) large hM (fun v => hx (label R v)) hl (NativeBlowUp.row i) (NativeBlowUp.col i)
  have hv:=RamUnsignedVector.command_spec B 100 (Data G x R large)
    "split.i" "split.count" "lp.word" "lp.position" (entries G x R large) front NativeSplitEntry.command
    (by omega) (by simpa only [entries,List.length_ofFn] using hf)
    (by intro i hi; simpa only [entries,List.getElem_ofFn,NNRat.natAbs_num_coe] using
      (hh ⟨i,by simpa only [entries,List.length_ofFn] using hi⟩).1.trans_lt (by omega:M< B))
    (by intro i hi; simpa only [entries,List.getElem_ofFn,NNRat.den_coe] using
      (hh ⟨i,by simpa only [entries,List.length_ofFn] using hi⟩).2.trans_lt (by omega:M< B))
    (by intro σ h; simpa only [entries,List.length_ofFn] using h.2.2.2)
    (by
      intro σ k h
      rcases h with ⟨hd,hs,hn,hc⟩
      refine ⟨⟨hd.labels,hd.graph,hd.costs,by simpa using hd.count,by simpa using hd.order⟩,?_,
        by simpa using hn,by simpa using hc⟩
      simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hs)
    (by intro i hi; simpa only [entries,List.getElem_ofFn] using
      NativeSplitEntry.command_spec B M n G x R large ⟨i,by simpa only [entries,List.length_ofFn] using hi⟩ hB hx hl)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hd => frame rr hd (by decide) (by decide)) (by decide) (by decide)
  simpa only [matrix,entries,List.length_ofFn,Nat.reduceAdd] using hv

theorem weights_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (front:List ℕ)
    (hB:front.length+4*R.card+3< B):
    Spec B (fun σ => Data G x R large σ∧ Prefix front "lp.word" σ∧ σ.vars "lp.position"=front.length∧
      front.length+4*R.card<(σ.arrs "lp.word").length) weights
      (fun _ τ => Data G x R large τ∧ Prefix (front++RamUnsignedBuffer.encode (List.replicate (2*R.card) 1)) "lp.word" τ∧
        τ.vars "lp.position"=front.length+4*R.card) (56*R.card+6):=by
  have hv:=RamUnsignedVector.command_spec B 6 (Data G x R large)
    "split.weight.i" "split.order" "lp.word" "lp.position" (List.replicate (2*R.card) (1:ℚ≥0)) front RamFractionPrimitives.one
    (by omega) (by simp only [List.length_replicate]; omega)
    (by intro i hi; simp; omega) (by intro i hi; simp; omega)
    (by intro σ h; simpa only [List.length_replicate] using h.2.2.1)
    (by
      intro σ k h
      rcases h with ⟨hd,hs,hn,hc⟩
      refine ⟨⟨hd.labels,hd.graph,hd.costs,by simpa using hd.count,by simpa using hd.order⟩,?_,
        by simpa using hn,by simpa using hc⟩
      simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hs)
    (by
      intro i hi σ h
      obtain ⟨τ,rr,ht⟩:=RamFractionPrimitives.one_spec B (by omega) σ trivial
      exact ⟨τ,rr,frame rr h.1 (by decide) (by decide),by simpa using ht⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hd => frame rr hd (by decide) (by decide)) (by decide) (by decide)
  convert hv using 1 <;> simp only [weights,List.length_replicate] <;> ring

theorem input_eq {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0):
    Lax455465.RationalEncoding.encodeInput .directed (splitInstance (restriction G R) (fun v => x (label R v)) large)=
      ([1,2*R.card]++RamUnsignedBuffer.encode (List.replicate (2*R.card) 1))++
        RamUnsignedBuffer.encode (entries G x R large):=by
  rw [Lax455465.RationalEncoding.encodeInput]
  rw [show entries G x R large=(List.ofFn fun u => List.ofFn
    ((splitInstance (restriction G R) (fun v => x (label R v)) large).capacity u)).flatten from
      NativeMatrixOrder.flatten _ _]
  simp only [splitInstance,List.ofFn_const,RamUnsignedBuffer.encode,List.append_assoc]

end Lax263307Proofs.NativeSplitVectors

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeSplitInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic NativeSplitEntry
open scoped NNRat

theorem sizes_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (hB:4*n*n+2*n+3< B):
    Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v:ℚ)) R σ∧ Stored "split.large" (large:ℚ) σ)
      sizes (fun _ τ => Data G x R large τ) 8:=by
  have hR:=NativeMaskUnpack.card_bound R
  have hsize:Spec B (fun σ => σ.vars "restrict.count"=R.card) sizes
      (fun _ τ => τ.vars "split.order"=2*R.card∧ τ.vars "split.count"=(2*R.card)*(2*R.card)) 8:=by
    have hh:(2*R.card)*(2*R.card)< B:=by nlinarith only [hB,Nat.mul_le_mul hR hR]
    (expose_names;
      (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ "restrict.count") (@Finset.card (Fin n) R)) => let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat→ Nat:=c0 ((2:Nat)); let c2:Nat:=c1 (@Finset.card (Fin n) R); let c3:Nat:=c0 c2 c2; let c4:Env→ Prop:=(fun (x_1 τ:Env) => And (@Eq Nat (Env.vars τ "split.order") c2) (@Eq Nat (Env.vars τ "split.count") c3)) σ; let c5:Nat:=c1 (Env.vars σ "restrict.count"); let c6:Env:=Env.setVar σ "split.order" c5; let c7:Nat:=Env.vars c6 "split.order"; let c8:Nat:=c0 c7 c7; let c9:Env:=Env.setVar c6 "split.count" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "restrict.count"); let c13:Nat:=c11 (Expr.size c12); let c14:Nat:=c11 (Expr.size (Expr.mul (Expr.var "split.order") (Expr.var "split.order"))); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B sizes σ σ' ((8:Nat))) (c4 σ')) c9 (@And.intro (Run B sizes σ c9 ((8:Nat))) (c4 c9) (RunStep.mono B sizes σ c9 (c10 c13 c14) ((8:Nat)) (RunStep.seq B (Com.assign "split.order" c12) (Com.assign "split.count" (Expr.mul (Expr.var "split.order") (Expr.var "split.order"))) σ c6 c9 c13 c14 (RunStep.assign B σ "split.order" c12 c5 (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "restrict.count") ((2:Nat)) (Env.vars σ "restrict.count") (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8782_0_0_0)) (RunStep.eval_var B σ "restrict.count" (?nAX_g8782_0_0_1)) (?nAX_g8782_0_0_2))) (RunStep.assign B c6 "split.count" (Expr.mul (Expr.var "split.order") (Expr.var "split.order")) c8 (RunStep.eval_mul B c6 (Expr.var "split.order") (Expr.var "split.order") c7 c7 (RunStep.eval_var B c6 "split.order" (?nAX_g8782_0_0_3)) (RunStep.eval_var B c6 "split.order" (?nAX_g8782_0_0_4)) ?_))) (?nAX_g8782_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8782_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8782_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8782_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8782_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8782_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8782_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hd,hl⟩
  obtain ⟨τ,rr,ht⟩:=hsize σ hd.count
  exact ⟨τ,rr,NativeRestrictionRead.frame rr hd (by decide) (by decide),
    by simpa only [Stored,String.reduceAppend,rr.frame_var "split.large.s" (by decide),
      rr.frame_var "split.large.n" (by decide),rr.frame_var "split.large.d" (by decide)] using hl,ht⟩

theorem header_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (hB:2*R.card+3< B):
    Spec B (fun σ => Data G x R large σ∧ 2<(σ.arrs "lp.word").length) header
      (fun _ τ => Data G x R large τ∧ Prefix [1,2*R.card] "lp.word" τ∧ τ.vars "lp.position"=2) 16:=by
  rintro σ ⟨hd,hr⟩
  let ν:=σ.setVar "lp.position" 0
  have r1:Run B (.assign "lp.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨μ,r2,p2⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position" [] 1 (.lit 1)
    (by omega) (by simp; omega) ν
    ⟨by simp [Prefix],by simp [ν],by change 0<(σ.arrs "lp.word").length; omega,evalB_lit (by omega)⟩
  have ho:μ.vars "split.order"=2*R.card:=((r1.seq r2).frame_var "split.order" (by decide)).trans hd.2.2.1
  obtain ⟨τ,r3,p3⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position" [1] (2*R.card) (.var "split.order")
    (by omega) (by simp; omega) μ
    ⟨by simpa using p2.1,by simpa using p2.2,
      by rw [RamFrames.run_array_length (r1.seq r2)]; simp only [List.length_singleton]; omega,
      by rw [evalB_var_iff]; exact ⟨ho.symm,ho ▸ (by omega:2*R.card< B)⟩⟩
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simpa using p3.1,by simpa using p3.2⟩

theorem input_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0):
    (Lax455465.RationalEncoding.encodeInput .directed
      (splitInstance (restriction G R) (fun v => x (label R v)) large)).length=wordLength R.card:=by
  rw [NativeSplitVectors.input_eq]
  simp only [List.length_append,List.length_cons,List.length_nil,RamUnsignedBuffer.length_encode,
    List.length_replicate,NativeSplitVectors.entries,List.length_ofFn,wordLength]
  ring

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0) (hM:1≤ M)
    (hB:8*n*n+6*n+M+40< B) (hx:∀ v,Bounded M (x v:ℚ)) (hl:Bounded M (large:ℚ)):
    Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v:ℚ)) R σ∧
      Stored "split.large" (large:ℚ) σ∧ wordLength R.card<(σ.arrs "lp.word").length)
      command (fun _ τ => Data G x R large τ∧
        Prefix (Lax455465.RationalEncoding.encodeInput .directed
          (splitInstance (restriction G R) (fun v => x (label R v)) large)) "lp.word" τ∧
        τ.vars "lp.position"=wordLength R.card) (488*R.card*R.card+56*R.card+36):=by
  have hR:=NativeMaskUnpack.card_bound R
  have hRR:=Nat.mul_le_mul hR hR
  have hsmall:4*n*n+6*n+M+20< B:=by nlinarith only [hB]
  have hlen:wordLength R.card+3< B:=by dsimp [wordLength]; nlinarith only [hB,hR,hRR]
  rintro σ ⟨hd,hlσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=sizes_spec B n G x R large (by omega) σ ⟨hd,hlσ⟩
  obtain ⟨σ2,r2,p2⟩:=header_spec B n G x R large (by dsimp [wordLength] at hlen; omega) σ1
    ⟨p1,by rw [RamFrames.run_array_length r1]; dsimp [wordLength] at hroom; omega⟩
  obtain ⟨σ3,r3,p3⟩:=NativeSplitVectors.weights_spec B n G x R large [1,2*R.card]
    (by simp only [List.length_cons,List.length_nil]; dsimp [wordLength] at hlen; omega) σ2
    ⟨p2.1,p2.2.1,by simpa using p2.2.2,
      by simp only [List.length_cons,List.length_nil]; rw [RamFrames.run_array_length (r1.seq r2)]; dsimp [wordLength] at hroom; omega⟩
  let front:= [1,2*R.card]++RamUnsignedBuffer.encode (List.replicate (2*R.card) 1)
  have hf:front.length=2+4*R.card:=by
    simp only [front,List.length_append,List.length_cons,List.length_nil,RamUnsignedBuffer.length_encode,List.length_replicate]
    ring
  have hlen':front.length+2*((2*R.card)*(2*R.card))=wordLength R.card:=by rw [hf]; dsimp [wordLength]; ring
  obtain ⟨τ,r4,p4⟩:=NativeSplitVectors.matrix_spec B M n G x R large front hM hsmall
    (by rw [hlen']; omega) hx hl σ3
    ⟨p3.1,p3.2.1,by simpa only [hf,List.length_cons,List.length_nil] using p3.2.2,
      by rw [hlen',RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hroom⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by nlinarith only []),p4.1,?_,?_⟩
  · simpa only [NativeSplitVectors.input_eq,front] using p4.2.1
  · simpa only [hlen'] using p4.2.2

end Lax263307Proofs.NativeSplitInput

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeOracleScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax455465Proofs

def reserved:List String:= ["frame.i","lookup.address","lookup.i","lookup.result","lp.position","lp.word","poly.argument","poly.value","put.address","put.value","size.count","size.i","size.total","size.value","vm.addresses","vm.count","vm.cursor","vm.input","vm.inputLength","vm.left","vm.modulus","vm.output","vm.outputLength","vm.pc","vm.result","vm.right","vm.running","vm.target","vm.values","vm.width"]

theorem instruction_variable (i:Lax808846.Ram.Instr) (x:String) (hx:x∉reserved):
    x∉(RamVirtualProgram.instruction i).wvars:=by
  cases i <;> simp_all [reserved,RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars]

theorem dispatch_variable (p:Lax808846.Ram.Program) (offset:ℕ) (x:String) (hx:x∉reserved):
    x∉(RamVirtualProgram.dispatch p offset).wvars:=by
  induction p generalizing offset with
  | nil => simp_all [reserved,RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or] using
      And.intro (instruction_variable i x hx) (ih (offset+1))

theorem command_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (x:String) (hx:x∉reserved):
    x∉(NativeOracleCalls.command p coeff).wvars:=by
  have hd:=dispatch_variable p 0 x hx
  have hp:=RamPolynomial.variable_frame coeff x (by simp_all [reserved])
  simp_all [reserved,NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,
    RamVirtualProgram.execute,RamWordOps.modulus,RamVirtualProgram.initCommand,Com.wvars]

end Lax263307Proofs.NativeOracleScalars

end

section

namespace Lax263307Proofs.NativeSplitOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

def query {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0):List ℕ:=
  Lax455465.RationalEncoding.encodeInput .directed (splitInstance (restriction G R) (fun v => x (label R v)) large)

theorem data_frame {B K n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ≥0} {R:Finset (Fin n)} {large:ℚ≥0}
    {p:Lax808846.Ram.Program} {coeff:List ℕ} {σ τ:Env}
    (rr:Run B (NativeOracleCalls.command p coeff) σ τ K) (hd:NativeSplitEntry.Data G x R large σ):
    NativeSplitEntry.Data G x R large τ:=by
  apply NativeSplitEntry.frame rr hd
  · intro s hs
    apply NativeOracleFrame.command_array p coeff s
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide
  · intro s hs
    apply NativeOracleScalars.command_variable p coeff s
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem exists_invocation (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ (p:Lax808846.Ram.Program) (wp tp:Polynomial ℕ) (coeff:List ℕ),
    (∀ z:ℕ,RamPolynomial.value coeff z=wp.eval z)∧
    ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0)
      (R:Finset (Fin n)) (large:ℚ≥0),
    let q:=query G x R large
    FitsInWords (wp.eval (bitSize q)) ((q.length::q)++f q)∧
    ∀ B M:ℕ,1≤ M→ 8*n*n+6*n+M+40< B→ (∀ v,Bounded M (x v:ℚ))→ Bounded M (large:ℚ)→
      bitSize q+1< B→ wp.eval (bitSize q+1)< B→ 2*(2^wp.eval (bitSize q))^2+3< B→
      tp.eval (bitSize q)+1< B→ RamVirtualConstants.allowance p< B→
      Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v:ℚ)) R σ∧
        Stored "split.large" (large:ℚ) σ∧ NativeSplitInput.wordLength R.card<(σ.arrs "lp.word").length∧
        q.length<(σ.arrs "vm.input").length∧ tp.eval (bitSize q)<(σ.arrs "vm.addresses").length∧
        tp.eval (bitSize q)<(σ.arrs "vm.values").length∧ tp.eval (bitSize q)<(σ.arrs "vm.output").length)
        (command p coeff) (fun _ τ => NativeSplitEntry.Data G x R large τ∧ Prefix (f q) "vm.output" τ∧
          τ.vars "vm.outputLength"=(f q).length∧ τ.vars "vm.running"=0)
        (cost R.card p coeff (tp.eval (bitSize q)) (bitSize q)):=by
  obtain ⟨p,wp,tp,coeff,hcoeff,hcall⟩:=NativeOracleCalls.exists_invocation f hf
  refine ⟨p,wp,tp,coeff,hcoeff,?_⟩
  intro n G _ x R large
  let q:=query G x R large
  obtain ⟨hfit,hcall⟩:=hcall q
  refine ⟨hfit,?_⟩
  intro B M hM hshape hx hl hsize hpoly hB htime hallow
  rintro σ ⟨hd,hlσ,hroom,hI,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩:=NativeSplitInput.command_spec B M n G x R large hM hshape hx hl σ ⟨hd,hlσ,hroom⟩
  obtain ⟨τ,r2,p2⟩:=hcall B hsize hpoly hB htime hallow ν
    ⟨p1.2.1,by simpa only [q,query,NativeSplitInput.input_length] using p1.2.2,
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [cost,q,query,NativeSplitInput.input_length]; omega),data_frame r2 p1.1,p2⟩

end Lax263307Proofs.NativeSplitOracle

end

section

namespace Lax263307Proofs.NativeOutputRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

theorem command_spec (B:ℕ) (xs:List ℕ) (i:ℕ) (hB:xs.length+i+2< B)
    (hwords:∀ x∈xs,x< B):
    Spec B (fun σ => Prefix xs "vm.output" σ∧ σ.vars "vm.outputLength"=xs.length∧ σ.vars "output.index"=i)
      command (fun _ τ => τ.vars "output.value"=xs.getD i 0) 7:=by
  rintro σ ⟨hp,hlen,hi⟩
  have hc:(Cond.lt (.var "output.index") (.var "vm.outputLength")).evalB B σ=some (decide (i< xs.length)):=
    evalB_condLt (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega:i< B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega:xs.length< B)⟩)
  by_cases h:i< xs.length
  · let τ:=σ.setVar "output.value" xs[i]
    have rr:Run B (.assign "output.value" (.get "vm.output" (.var "output.index"))) σ τ 3:=
      Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega:i< B)⟩)
        (hp i h) (hwords _ (List.getElem_mem h)))
    exact ⟨τ,Run.ite_true (by simpa only [h,decide_true] using hc) rr,by simp [τ,List.getD,List.getElem?_eq_getElem h]⟩
  · let τ:=σ.setVar "output.value" 0
    have rr:Run B (.assign "output.value" (.lit 0)) σ τ 2:=Run.assign (evalB_lit (by omega))
    exact ⟨τ,(Run.ite_false (by simpa only [h,decide_false] using hc) rr).mono (by decide),
      by simp [τ,List.getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]⟩

end Lax263307Proofs.NativeOutputRead

end

section

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):ℕ:=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem zero {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)):partialMask f S 0=0:=by
  simp only [partialMask,NativeMasks.prefix_zero,Finset.image_empty,NativeMasks.mask_empty]

theorem full {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)):
    partialMask f S r=NativeMasks.mask (S.image f):=by rw [partialMask,NativeMasks.prefix_full]

theorem bound {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):partialMask f S i<2^n:=
  NativeMasks.mask_bound _

theorem step {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:Fin r):
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1):=by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h:i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

theorem left_member {r:ℕ} (xs:List ℕ) (i:Fin r):
    i∈leftShore (decodeCut (2*r) xs)↔ xs.getD (2*i.val) 0=1:=by
  simp [leftShore,decodeCut,minus]

theorem right_member {r:ℕ} (xs:List ℕ) (i:Fin r):
    i∈rightShore (decodeCut (2*r) xs)↔ xs.getD (2*i.val+1) 0≠1:=by
  simp [rightShore,decodeCut,plus]

theorem orient_images {r n:ℕ} (f:Fin r→ Fin n) (hf:Function.Injective f)
    (A B:Finset (Fin r)):
    ((orient A B).1.image f,(orient A B).2.image f)=orient (A.image f) (B.image f):=by
  simp only [orient,Finset.card_image_of_injective _ hf]
  split_ifs <;> rfl

end Lax263307Proofs.NativeShoreMasks

end

section

namespace Lax263307Proofs.NativeShoreUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open NativeShoreMasks

theorem bit_spec (B:ℕ) (xs:List ℕ) (i:ℕ) (invert:Bool)
    (hB:xs.length+i+2< B) (hw:∀ x∈xs,x< B):
    Spec B (fun σ => Prefix xs "vm.output" σ∧ σ.vars "vm.outputLength"=xs.length∧ σ.vars "output.index"=i)
      (bitCommand invert) (fun _ τ => τ.vars "shore.bit"=
        if (if invert then xs.getD i 0≠1 else xs.getD i 0=1) then 1 else 0) 13:=by
  have hx:xs.getD i 0< B:=by
    by_cases h:i< xs.length
    · simpa only [List.getD,List.getElem?_eq_getElem h,Option.getD_some] using hw _ (List.getElem_mem h)
    · simp only [List.getD,List.getElem?_eq_none (Nat.le_of_not_gt h),Option.getD_none]; omega
  have hr:=NativeOutputRead.command_spec B xs i hB hw
  cases invert <;> (first
                    | (expose_names;
                        (refine
                            fun (σ:Env)
                              (a:
                                And (Prefix xs "vm.output" σ)
                                  (And (@Eq Nat (Env.vars σ "vm.outputLength") (@List.length Nat xs))
                                    (@Eq Nat (Env.vars σ "output.index") i))) =>
                            let c0:Prop:= @Eq Nat (Env.vars σ "vm.outputLength") (@List.length Nat xs);
                            let c1:Prop:=And c0 (@Eq Nat (Env.vars σ "output.index") i);
                            let c2:Prop:=And (Prefix xs "vm.output" σ) c1;
                            let c3:Nat:= @List.getD Nat xs i ((0:Nat));
                            let c4:Prop:= @Ne Nat c3 ((1:Nat));
                            let c5:Prop:= @Eq Nat c3 ((1:Nat));
                            let c6:Decidable (@Eq Nat c3 ((1:Nat))):=
                              instDecidableEqNat c3 ((1:Nat));
                            let c7:Nat:=
                              @ite Nat (@ite Prop (@Eq Bool false true) (instDecidableEqBool false true) c4 c5)
                                (@instDecidableIte (@Eq Bool false true) c4 c5 (instDecidableEqBool false true) (@instDecidableNot c5 c6) c6)
                                ((1:Nat))
                                ((0:Nat));
                            let c8:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "shore.bit") c7) σ;
                            let c9:Env→ Prop:=fun (σ':Env) =>
                              And (Run B (bitCommand false) σ σ' ((13:Nat))) (c8 σ');
                            let c10:Prop:= @Exists Env c9;
                            let c11:Env→ Prop:=fun (σ':Env) =>
                              And (Run B NativeOutputRead.command σ σ' ((7:Nat)))
                                (@Eq Nat (Env.vars σ' "output.value") c3);
                            let c12:Nat→ Nat→ Nat:= @ite Nat (@Eq Bool false true) (instDecidableEqBool false true);
                            let c13:Nat:=
                              c12 ((0:Nat))
                                ((1:Nat));
                            let c14:Nat→ Nat→ Nat:=Nat.add;
                            let c15:Nat→ Nat:=c14 ((7:Nat));
                            let c16:Nat→ Nat:=c14 ((1:Nat));
                            let c17:Cond:=
                              Cond.eq (Expr.var "output.value") (Expr.lit ((1:Nat)));
                            let c18:Nat→ Nat:=c14 (c16 (Cond.size c17));
                            let c19:Expr:=Expr.lit c13;
                            let c20:Nat:=c16 (Expr.size c19);
                            let c21:Nat:=c18 c20;
                            let c22:Com:=Com.assign "shore.bit" c19;
                            let c23:Nat:=
                              c12 ((1:Nat))
                                ((0:Nat));
                            let c24:Expr:=Expr.lit c23;
                            let c25:Com:=Com.assign "shore.bit" c24;
                            let c26:Nat:=c16 (Expr.size c24);
                            let c27:Nat:=c18 c26;
                            @And.casesOn (Prefix xs "vm.output" σ) c1 (fun (x:c2) => c10) a
                              fun (left:Prefix xs "vm.output" σ) (right:c1) =>
                              @And.casesOn c0 (@Eq Nat (Env.vars σ "output.index") i) (fun (x:c1) => c10) right
                                fun (left_1:c0) (right_1:@Eq Nat (Env.vars σ "output.index") i) =>
                                @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c10)
                                  (RunStep.use B
                                    (fun (σ_1:Env) =>
                                      And (Prefix xs "vm.output" σ_1)
                                        (And (@Eq Nat (Env.vars σ_1 "vm.outputLength") (@List.length Nat xs))
                                          (@Eq Nat (Env.vars σ_1 "output.index") i)))
                                    NativeOutputRead.command (fun (x τ:Env) => @Eq Nat (Env.vars τ "output.value") c3)
                                    ((7:Nat)) hr σ ?_)
                                  fun (w:Env)
                                    (h:
                                      And (Run B NativeOutputRead.command σ w ((7:Nat)))
                                        (@Eq Nat (Env.vars w "output.value") c3)) =>
                                  let c0_1:Prop:=
                                    Run B NativeOutputRead.command σ w ((7:Nat));
                                  let c1_1:Prop:=
                                    @Eq Nat (Env.vars w "output.value") ((1:Nat));
                                  let c2_1:Prop:=Not c1_1;
                                  @And.casesOn c0_1 (@Eq Nat (Env.vars w "output.value") c3)
                                    (fun (x:And c0_1 (@Eq Nat (Env.vars w "output.value") c3)) => c10) h
                                    fun (left_2:c0_1) (right_2:@Eq Nat (Env.vars w "output.value") c3) =>
                                    @Or.casesOn c1_1 c2_1 (fun (x:Or c1_1 c2_1) => c10) (Classical.em c1_1)
                                      (fun (hcase:c1_1) =>
                                        @Exists.intro Env c9 (Env.setVar w "shore.bit" c13)
                                          (@And.intro
                                            (Run B (bitCommand false) σ (Env.setVar w "shore.bit" c13)
                                              ((13:Nat)))
                                            (c8 (Env.setVar w "shore.bit" c13))
                                            (RunStep.mono B (bitCommand false) σ (Env.setVar w "shore.bit" c13) (c15 c21)
                                              ((13:Nat))
                                              (RunStep.seq B NativeOutputRead.command (Com.ite c17 c22 c25) σ w (Env.setVar w "shore.bit" c13)
                                                ((7:Nat)) c21 left_2
                                                (RunStep.ite_true B c17 c22 c25 w (Env.setVar w "shore.bit" c13) c20
                                                  (RunStep.cond_eq_true B w (Expr.var "output.value")
                                                    (Expr.lit ((1:Nat)))
                                                    (Env.vars w "output.value") ((1:Nat))
                                                    (RunStep.eval_var B w "output.value"
                                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                    (RunStep.eval_lit B ((1:Nat)) w
                                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                    hcase)
                                                  (RunStep.assign B w "shore.bit" c19 c13
                                                    (RunStep.eval_lit B c13 w
                                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                            ?_))
                                      fun (hcase:c2_1) =>
                                      @Exists.intro Env c9 (Env.setVar w "shore.bit" c23)
                                        (@And.intro
                                          (Run B (bitCommand false) σ (Env.setVar w "shore.bit" c23)
                                            ((13:Nat)))
                                          (c8 (Env.setVar w "shore.bit" c23))
                                          (RunStep.mono B (bitCommand false) σ (Env.setVar w "shore.bit" c23) (c15 c27)
                                            ((13:Nat))
                                            (RunStep.seq B NativeOutputRead.command (Com.ite c17 c22 c25) σ w (Env.setVar w "shore.bit" c23)
                                              ((7:Nat)) c27 left_2
                                              (RunStep.ite_false B c17 c22 c25 w (Env.setVar w "shore.bit" c23) c26
                                                (RunStep.cond_eq_false B w (Expr.var "output.value")
                                                  (Expr.lit ((1:Nat)))
                                                  (Env.vars w "output.value") ((1:Nat))
                                                  (RunStep.eval_var B w "output.value"
                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                  (RunStep.eval_lit B ((1:Nat)) w
                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                  hcase)
                                                (RunStep.assign B w "shore.bit" c24 c23
                                                  (RunStep.eval_lit B c23 w
                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (all_goals try clear h); (all_goals try clear left_2))
                    | (expose_names;
                        (refine
                            fun (σ:Env)
                              (a:
                                And (Prefix xs "vm.output" σ)
                                  (And (@Eq Nat (Env.vars σ "vm.outputLength") (@List.length Nat xs))
                                    (@Eq Nat (Env.vars σ "output.index") i))) =>
                            let c0:Prop:= @Eq Nat (Env.vars σ "vm.outputLength") (@List.length Nat xs);
                            let c1:Prop:=And c0 (@Eq Nat (Env.vars σ "output.index") i);
                            let c2:Prop:=And (Prefix xs "vm.output" σ) c1;
                            let c3:Nat:= @List.getD Nat xs i ((0:Nat));
                            let c4:Prop:= @Ne Nat c3 ((1:Nat));
                            let c5:Prop:= @Eq Nat c3 ((1:Nat));
                            let c6:Decidable (@Eq Nat c3 ((1:Nat))):=
                              instDecidableEqNat c3 ((1:Nat));
                            let c7:Nat:=
                              @ite Nat (@ite Prop (@Eq Bool true true) (instDecidableEqBool true true) c4 c5)
                                (@instDecidableIte (@Eq Bool true true) c4 c5 (instDecidableEqBool true true) (@instDecidableNot c5 c6) c6)
                                ((1:Nat))
                                ((0:Nat));
                            let c8:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "shore.bit") c7) σ;
                            let c9:Env→ Prop:=fun (σ':Env) =>
                              And (Run B (bitCommand true) σ σ' ((13:Nat))) (c8 σ');
                            let c10:Prop:= @Exists Env c9;
                            let c11:Env→ Prop:=fun (σ':Env) =>
                              And (Run B NativeOutputRead.command σ σ' ((7:Nat)))
                                (@Eq Nat (Env.vars σ' "output.value") c3);
                            let c12:Nat→ Nat→ Nat:= @ite Nat (@Eq Bool true true) (instDecidableEqBool true true);
                            let c13:Nat:=
                              c12 ((0:Nat))
                                ((1:Nat));
                            let c14:Nat→ Nat→ Nat:=Nat.add;
                            let c15:Nat→ Nat:=c14 ((7:Nat));
                            let c16:Nat→ Nat:=c14 ((1:Nat));
                            let c17:Cond:=
                              Cond.eq (Expr.var "output.value") (Expr.lit ((1:Nat)));
                            let c18:Nat→ Nat:=c14 (c16 (Cond.size c17));
                            let c19:Expr:=Expr.lit c13;
                            let c20:Nat:=c16 (Expr.size c19);
                            let c21:Nat:=c18 c20;
                            let c22:Com:=Com.assign "shore.bit" c19;
                            let c23:Nat:=
                              c12 ((1:Nat))
                                ((0:Nat));
                            let c24:Expr:=Expr.lit c23;
                            let c25:Com:=Com.assign "shore.bit" c24;
                            let c26:Nat:=c16 (Expr.size c24);
                            let c27:Nat:=c18 c26;
                            @And.casesOn (Prefix xs "vm.output" σ) c1 (fun (x:c2) => c10) a
                              fun (left:Prefix xs "vm.output" σ) (right:c1) =>
                              @And.casesOn c0 (@Eq Nat (Env.vars σ "output.index") i) (fun (x:c1) => c10) right
                                fun (left_1:c0) (right_1:@Eq Nat (Env.vars σ "output.index") i) =>
                                @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c10)
                                  (RunStep.use B
                                    (fun (σ_1:Env) =>
                                      And (Prefix xs "vm.output" σ_1)
                                        (And (@Eq Nat (Env.vars σ_1 "vm.outputLength") (@List.length Nat xs))
                                          (@Eq Nat (Env.vars σ_1 "output.index") i)))
                                    NativeOutputRead.command (fun (x τ:Env) => @Eq Nat (Env.vars τ "output.value") c3)
                                    ((7:Nat)) hr σ ?_)
                                  fun (w:Env)
                                    (h:
                                      And (Run B NativeOutputRead.command σ w ((7:Nat)))
                                        (@Eq Nat (Env.vars w "output.value") c3)) =>
                                  let c0_1:Prop:=
                                    Run B NativeOutputRead.command σ w ((7:Nat));
                                  let c1_1:Prop:=
                                    @Eq Nat (Env.vars w "output.value") ((1:Nat));
                                  let c2_1:Prop:=Not c1_1;
                                  @And.casesOn c0_1 (@Eq Nat (Env.vars w "output.value") c3)
                                    (fun (x:And c0_1 (@Eq Nat (Env.vars w "output.value") c3)) => c10) h
                                    fun (left_2:c0_1) (right_2:@Eq Nat (Env.vars w "output.value") c3) =>
                                    @Or.casesOn c1_1 c2_1 (fun (x:Or c1_1 c2_1) => c10) (Classical.em c1_1)
                                      (fun (hcase:c1_1) =>
                                        @Exists.intro Env c9 (Env.setVar w "shore.bit" c13)
                                          (@And.intro
                                            (Run B (bitCommand true) σ (Env.setVar w "shore.bit" c13)
                                              ((13:Nat)))
                                            (c8 (Env.setVar w "shore.bit" c13))
                                            (RunStep.mono B (bitCommand true) σ (Env.setVar w "shore.bit" c13) (c15 c21)
                                              ((13:Nat))
                                              (RunStep.seq B NativeOutputRead.command (Com.ite c17 c22 c25) σ w (Env.setVar w "shore.bit" c13)
                                                ((7:Nat)) c21 left_2
                                                (RunStep.ite_true B c17 c22 c25 w (Env.setVar w "shore.bit" c13) c20
                                                  (RunStep.cond_eq_true B w (Expr.var "output.value")
                                                    (Expr.lit ((1:Nat)))
                                                    (Env.vars w "output.value") ((1:Nat))
                                                    (RunStep.eval_var B w "output.value"
                                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                    (RunStep.eval_lit B ((1:Nat)) w
                                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                    hcase)
                                                  (RunStep.assign B w "shore.bit" c19 c13
                                                    (RunStep.eval_lit B c13 w
                                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                            ?_))
                                      fun (hcase:c2_1) =>
                                      @Exists.intro Env c9 (Env.setVar w "shore.bit" c23)
                                        (@And.intro
                                          (Run B (bitCommand true) σ (Env.setVar w "shore.bit" c23)
                                            ((13:Nat)))
                                          (c8 (Env.setVar w "shore.bit" c23))
                                          (RunStep.mono B (bitCommand true) σ (Env.setVar w "shore.bit" c23) (c15 c27)
                                            ((13:Nat))
                                            (RunStep.seq B NativeOutputRead.command (Com.ite c17 c22 c25) σ w (Env.setVar w "shore.bit" c23)
                                              ((7:Nat)) c27 left_2
                                              (RunStep.ite_false B c17 c22 c25 w (Env.setVar w "shore.bit" c23) c26
                                                (RunStep.cond_eq_false B w (Expr.var "output.value")
                                                  (Expr.lit ((1:Nat)))
                                                  (Env.vars w "output.value") ((1:Nat))
                                                  (RunStep.eval_var B w "output.value"
                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                  (RunStep.eval_lit B ((1:Nat)) w
                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                  hcase)
                                                (RunStep.assign B w "shore.bit" c24 c23
                                                  (RunStep.eval_lit B c23 w
                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (all_goals try clear h); (all_goals try clear left_2))
                   ) <;> simp_all <;> omega

theorem mask_spec {r n:ℕ} (B:ℕ) (reg:String) (f:Fin r→ Fin n)
    (S:Finset (Fin r)) (i:Fin r) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars reg=partialMask f S i.val∧
      σ.vars "shore.bit"=(if i∈S then 1 else 0)∧ σ.vars "shore.label"=(f i).val)
      (maskCommand reg) (fun _ τ => τ.vars reg=partialMask f S (i.val+1)) 6:=by
  rintro σ ⟨hprev,hbit,hlabel⟩
  let bit:ℕ:=if i∈S then 1 else 0
  have hb:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hbB:bit< B:=by omega
  have hlB:(f i).val< B:=(f i).isLt.trans (by omega)
  have hpB:partialMask f S i.val< B:=(bound f S i.val).trans hm
  have hnB:partialMask f S (i.val+1)< B:=(bound f S (i.val+1)).trans hm
  have hsB:bit*2^(f i).val< B:=
    (by simpa only [one_mul] using Nat.mul_le_mul_right (2^(f i).val) hb:bit*2^(f i).val≤2^(f i).val).trans_lt
      ((Nat.pow_lt_pow_right (by decide:1<2) (f i).isLt).trans hm)
  have he:=evalB_bin (op:=.or)
    (by rw [evalB_var_iff]; exact ⟨hprev.symm,hprev ▸ hpB⟩)
    (evalB_bin (op:=.shiftl)
      (by rw [evalB_var_iff]; exact ⟨hbit.symm,hbit ▸ hbB⟩)
      (by rw [evalB_var_iff]; exact ⟨hlabel.symm,hlabel ▸ hlB⟩) hsB)
    (by change Nat.lor (partialMask f S i.val) (bit*2^(f i).val)< B; rw [step]; exact hnB)
  have he':(Expr.or (.var reg) (.shiftl (.var "shore.bit") (.var "shore.label"))).evalB B σ=
      some (partialMask f S (i.val+1)):=by
    simpa only [Bop.apply_or,Bop.apply_shiftl,bit,step] using he
  exact ⟨σ.setVar reg (partialMask f S (i.val+1)),Run.assign he',by simp⟩

end Lax263307Proofs.NativeShoreUpdate

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeFlowShores

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting
open NativeShoreMasks NativeShoreUpdate

def Context {n:ℕ} (R:Finset (Fin n)) (xs:List ℕ) (σ:Env):Prop:=
  Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ∧ σ.vars "restrict.count"=R.card∧
    Prefix xs "vm.output" σ∧ σ.vars "vm.outputLength"=xs.length

theorem frame {B n K:ℕ} {R:Finset (Fin n)} {xs:List ℕ} {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hd:Context R xs σ)
    (ha:∀ s∈["restrict.vertices","vm.output"],s∉c.warrs)
    (hv:∀ s∈["restrict.count","vm.outputLength"],s∉c.wvars):Context R xs τ:=by
  refine ⟨?_,(rr.frame_var _ (hv _ (by simp))).trans hd.2.1,?_,(rr.frame_var _ (hv _ (by simp))).trans hd.2.2.2⟩
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" (ha _ (by simp))] using hd.1
  · simpa only [Prefix,rr.frame_arr "vm.output" (ha _ (by simp))] using hd.2.2.1

def left {n:ℕ} (R:Finset (Fin n)) (xs:List ℕ):Finset (Fin R.card):=leftShore (decodeCut (2*R.card) xs)
def right {n:ℕ} (R:Finset (Fin n)) (xs:List ℕ):Finset (Fin R.card):=rightShore (decodeCut (2*R.card) xs)

def Invariant {n:ℕ} (R:Finset (Fin n)) (xs:List ℕ) (σ:Env):Prop:=
  Context R xs σ∧ σ.vars "shore.i"≤ R.card∧
    σ.vars "shore.left"=partialMask (label R) (left R xs) (σ.vars "shore.i")∧
    σ.vars "shore.right"=partialMask (label R) (right R xs) (σ.vars "shore.i")

theorem step_spec (B n:ℕ) (R:Finset (Fin n)) (xs:List ℕ)
    (hB:xs.length+2*n+4< B) (hm:2^n< B) (hw:∀ x∈xs,x< B):
    Spec B (fun σ => Invariant R xs σ∧ σ.vars "shore.i"< R.card) step
      (fun σ τ => Invariant R xs τ∧ τ.vars "shore.i"=σ.vars "shore.i"+1) 55:=by
  have hR:=NativeMaskUnpack.card_bound R
  rintro σ ⟨⟨hc,hle,hleft,hright⟩,hlt⟩
  let i:Fin R.card:= ⟨σ.vars "shore.i",hlt⟩
  let v:=label R i
  have hiB:i.val< B:=by dsimp [i]; omega
  have hvB:v.val< B:=v.isLt.trans (by omega)
  have hg:(σ.arrs "restrict.vertices")[i.val]?=some v.val:=by
    simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
      hc.1 i.val (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using i.isLt)
  let σ1:=σ.setVar "shore.label" v.val
  have r1:Run B (.assign "shore.label" (.get "restrict.vertices" (.var "shore.i"))) σ σ1 3:=
    Run.assign (evalB_get (evalB_var hiB) hg hvB)
  let σ2:=σ1.setVar "output.index" (2*i.val)
  have r2:Run B leftIndex σ1 σ2 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simp only [σ1,vars_setVar,String.reduceEq,if_false]; exact ⟨rfl,hiB⟩)
      (by change 2*i.val< B; have hh:=i.isLt; omega))
  have d2:=frame (r1.seq r2) hc (by decide) (by decide)
  obtain ⟨σ3,r3,p3⟩:=bit_spec B xs (2*i.val) false (by have hh:=i.isLt; omega) hw σ2
    ⟨d2.2.2.1,d2.2.2.2,by simp [σ2]⟩
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩:=mask_spec B "shore.left" (label R) (left R xs) i (by omega) hm σ3
    ⟨(r123.frame_var "shore.left" (by decide)).trans hleft,
      by simpa only [Bool.false_eq_true,if_false,left,left_member] using p3,
      by simpa only [σ1,vars_setVar,if_true] using (r2.seq r3).frame_var "shore.label" (by decide)⟩
  have r1234:=r1.seq (r2.seq (r3.seq r4))
  have hi4:σ4.vars "shore.i"=i.val:=r1234.frame_var "shore.i" (by decide)
  let σ5:=σ4.setVar "output.index" (2*i.val+1)
  have r5:Run B rightIndex σ4 σ5 6:=Run.assign
    (evalB_bin (op:=.add) (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hi4.symm,hi4 ▸ hiB⟩)
      (by change 2*i.val< B; have hh:=i.isLt; omega)) (evalB_lit (by omega))
      (by change 2*i.val+1< B; have hh:=i.isLt; omega))
  have d5:=frame (r1234.seq r5) hc (by decide) (by decide)
  obtain ⟨σ6,r6,p6⟩:=bit_spec B xs (2*i.val+1) true (by have hh:=i.isLt; omega) hw σ5
    ⟨d5.2.2.1,d5.2.2.2,by simp [σ5]⟩
  have r123456:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  obtain ⟨σ7,r7,p7⟩:=mask_spec B "shore.right" (label R) (right R xs) i (by omega) hm σ6
    ⟨(r123456.frame_var "shore.right" (by decide)).trans hright,
      by simpa only [if_true,right,right_member] using p6,
      by simpa only [σ1,vars_setVar,if_true] using (r2.seq (r3.seq (r4.seq (r5.seq r6)))).frame_var "shore.label" (by decide)⟩
  have r1234567:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  have hi7:σ7.vars "shore.i"=i.val:=r1234567.frame_var "shore.i" (by decide)
  let τ:=σ7.setVar "shore.i" (i.val+1)
  have r8:Run B next σ7 τ 4:=Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hi7.symm,hi7 ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i.val+1< B; have hh:=i.isLt; omega))
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))
  have hit:τ.vars "shore.i"=i.val+1:=by simp [τ]
  refine ⟨τ,rr,⟨frame rr hc (by decide) (by decide),?_,?_,?_⟩,hit⟩
  · rw [hit]; exact i.isLt
  · rw [hit]
    exact ((r5.seq (r6.seq (r7.seq r8))).frame_var "shore.left" (by decide)).trans p4
  · rw [hit]
    exact (r8.frame_var "shore.right" (by decide)).trans p7

theorem command_spec (B n:ℕ) (R:Finset (Fin n)) (xs:List ℕ)
    (hB:xs.length+2*n+4< B) (hm:2^n< B) (hw:∀ x∈xs,x< B):
    Spec B (Context R xs) command
      (fun _ τ => Context R xs τ∧
        τ.vars "shore.left"=NativeMasks.mask ((left R xs).image (label R))∧
        τ.vars "shore.right"=NativeMasks.mask ((right R xs).image (label R))) (59*R.card+10):=by
  have hR:=NativeMaskUnpack.card_bound R
  have hloop:=Spec.forRangeZero "shore.i" "restrict.count" (Invariant R xs) R.card 55 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (step_spec B n R xs hB hm hw)
  intro σ hc
  let ν:=σ.setVar "shore.left" 0
  have r1:Run B (.assign "shore.left" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  let μ:=ν.setVar "shore.right" 0
  have r2:Run B (.assign "shore.right" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (by omega))
  have hinit:Invariant R xs (μ.setVar "shore.i" 0):=by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa only [Context,Prefix,μ,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [μ,ν,zero]
    · simp [μ,ν,zero]
  obtain ⟨τ,r3,ht⟩:=hloop μ hinit
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),ht.1.1,?_,?_⟩
  · simpa only [ht.2,full] using ht.1.2.2.1
  · simpa only [ht.2,full] using ht.1.2.2.2

end Lax263307Proofs.NativeFlowShores

end

section

namespace Lax263307Proofs.NativeShoreOrientation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs
open Lax263307 ComputedSeparators NativeMasks

theorem count_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (reg out:String)
    (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars reg=mask I∧ n≤(σ.arrs "subset.bits").length)
      (countCommand reg out) (fun _ τ => τ.vars out=I.card) (21*n+12):=by
  rintro σ ⟨hn,hI,hroom⟩
  let ν:=σ.setVar "unpack.mask" (mask I)
  have r1:Run B (.assign "unpack.mask" (.var reg)) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hI.symm,hI ▸ (mask_bound I).trans hm⟩)
  obtain ⟨μ,r2,p2⟩:=NativeMaskUnpack.command_spec B I hB hm ν
    ⟨by simpa [ν] using hn,by simp [ν],hroom⟩
  let τ:=μ.setVar out I.card
  have r3:Run B (.assign out (.var "unpack.card")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,p2.2 ▸ (NativeMaskUnpack.card_bound I).trans_lt (by omega)⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),by simp [τ]⟩

theorem choose_spec {n:ℕ} (B:ℕ) (A C:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "shore.left"=mask A∧ σ.vars "shore.right"=mask C∧
      σ.vars "shore.leftCard"=A.card∧ σ.vars "shore.rightCard"=C.card)
      choose (fun _ τ => τ.vars "cut.left"=mask (orient A C).1∧ τ.vars "cut.right"=mask (orient A C).2) 8:=by
  have hA:=(mask_bound A).trans hm
  have hC:=(mask_bound C).trans hm
  have hcA:=NativeMaskUnpack.card_bound A
  have hcC:=NativeMaskUnpack.card_bound C
  by_cases h:C.card≤ A.card
  all_goals simp only [orient,h,if_true,if_false]
  all_goals (first
             | (expose_names;
                 (refine
                     fun (σ:Env)
                       (a:
                         And (@Eq Nat (Env.vars σ "shore.left") (@mask n A))
                           (And (@Eq Nat (Env.vars σ "shore.right") (@mask n C))
                             (And (@Eq Nat (Env.vars σ "shore.leftCard") (@Finset.card (Fin n) A))
                               (@Eq Nat (Env.vars σ "shore.rightCard") (@Finset.card (Fin n) C))))) =>
                     let c0:Prop:= @Eq Nat (Env.vars σ "shore.left") (@mask n A);
                     let c1:Prop:= @Eq Nat (Env.vars σ "shore.right") (@mask n C);
                     let c2:Prop:= @Eq Nat (Env.vars σ "shore.leftCard") (@Finset.card (Fin n) A);
                     let c3:Prop:= @Eq Nat (Env.vars σ "shore.rightCard") (@Finset.card (Fin n) C);
                     let c4:Prop:=And c2 c3;
                     let c5:Prop:=And c1 c4;
                     let c6:Env→ Prop:=
                       (fun (x τ:Env) =>
                           And (@Eq Nat (Env.vars τ "cut.left") (@mask n A)) (@Eq Nat (Env.vars τ "cut.right") (@mask n C)))
                         σ;
                     let c7:Env→ Prop:=fun (σ':Env) =>
                       And (Run B choose σ σ' ((8:Nat))) (c6 σ');
                     let c8:Prop:= @Exists Env c7;
                     let c9:Prop:=Nat.lt (Env.vars σ "shore.leftCard") (Env.vars σ "shore.rightCard");
                     let c10:Prop:=Not c9;
                     let c11:Nat:=Env.vars (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "shore.left";
                     let c12:Env:=Env.setVar (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "cut.right" c11;
                     let c13:Nat→ Nat→ Nat:=Nat.add;
                     let c14:Nat→ Nat:=c13 ((1:Nat));
                     let c15:Nat→ Nat:=c13 (c14 (Cond.size (Cond.lt (Expr.var "shore.leftCard") (Expr.var "shore.rightCard"))));
                     let c16:Nat:=c14 (Expr.size (Expr.var "shore.right"));
                     let c17:Nat:=c14 (Expr.size (Expr.var "shore.left"));
                     let c18:Nat:=c13 c16 c17;
                     let c19:Com:=
                       Com.seq (Com.assign "cut.left" (Expr.var "shore.right")) (Com.assign "cut.right" (Expr.var "shore.left"));
                     let c20:Com:=
                       Com.seq (Com.assign "cut.left" (Expr.var "shore.left")) (Com.assign "cut.right" (Expr.var "shore.right"));
                     let c21:String→ Nat:=Env.vars c12;
                     let c22:Nat:=Env.vars (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "shore.right";
                     let c23:Env:=Env.setVar (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "cut.right" c22;
                     let c24:Nat:=c13 c17 c16;
                     let c25:String→ Nat:=Env.vars c23;
                     @And.casesOn c0 c5 (fun (x:And c0 c5) => c8) a fun (left:c0) (right:c5) =>
                       @And.casesOn c1 c4 (fun (x:c5) => c8) right fun (left_1:c1) (right_1:c4) =>
                         @And.casesOn c2 c3 (fun (x:c4) => c8) right_1 fun (left_2:c2) (right_2:c3) =>
                           @Or.casesOn c9 c10 (fun (x:Or c9 c10) => c8) (Classical.em c9)
                             (fun (hcase:c9) =>
                               @Exists.intro Env c7 c12
                                 (@And.intro (Run B choose σ c12 ((8:Nat))) (c6 c12)
                                   (RunStep.mono B choose σ c12 (c15 c18) ((8:Nat))
                                     (RunStep.ite_true B (Cond.lt (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")) c19 c20 σ
                                       c12 c18
                                       (RunStep.cond_lt_true B σ (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")
                                         (Env.vars σ "shore.leftCard") (Env.vars σ "shore.rightCard")
                                         (RunStep.eval_var B σ "shore.leftCard"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         (RunStep.eval_var B σ "shore.rightCard"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         hcase)
                                       (RunStep.seq B (Com.assign "cut.left" (Expr.var "shore.right"))
                                         (Com.assign "cut.right" (Expr.var "shore.left")) σ
                                         (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) c12 c16 c17
                                         (RunStep.assign B σ "cut.left" (Expr.var "shore.right") (Env.vars σ "shore.right")
                                           (RunStep.eval_var B σ "shore.right"
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                         (RunStep.assign B (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "cut.right"
                                           (Expr.var "shore.left") c11
                                           (RunStep.eval_var B (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "shore.left"
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   ?_))
                             fun (hcase:c10) =>
                             @Exists.intro Env c7 c23
                               (@And.intro (Run B choose σ c23 ((8:Nat))) (c6 c23)
                                 (RunStep.mono B choose σ c23 (c15 c24) ((8:Nat))
                                   (RunStep.ite_false B (Cond.lt (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")) c19 c20 σ
                                     c23 c24
                                     (RunStep.cond_lt_false B σ (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")
                                       (Env.vars σ "shore.leftCard") (Env.vars σ "shore.rightCard")
                                       (RunStep.eval_var B σ "shore.leftCard"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       (RunStep.eval_var B σ "shore.rightCard"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       hcase)
                                     (RunStep.seq B (Com.assign "cut.left" (Expr.var "shore.left"))
                                       (Com.assign "cut.right" (Expr.var "shore.right")) σ
                                       (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) c23 c17 c16
                                       (RunStep.assign B σ "cut.left" (Expr.var "shore.left") (Env.vars σ "shore.left")
                                         (RunStep.eval_var B σ "shore.left"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                       (RunStep.assign B (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "cut.right"
                                         (Expr.var "shore.right") c22
                                         (RunStep.eval_var B (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "shore.right"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                 ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
             | (expose_names;
                 (refine
                     fun (σ:Env)
                       (a:
                         And (@Eq Nat (Env.vars σ "shore.left") (@mask n A))
                           (And (@Eq Nat (Env.vars σ "shore.right") (@mask n C))
                             (And (@Eq Nat (Env.vars σ "shore.leftCard") (@Finset.card (Fin n) A))
                               (@Eq Nat (Env.vars σ "shore.rightCard") (@Finset.card (Fin n) C))))) =>
                     let c0:Prop:= @Eq Nat (Env.vars σ "shore.left") (@mask n A);
                     let c1:Prop:= @Eq Nat (Env.vars σ "shore.right") (@mask n C);
                     let c2:Prop:= @Eq Nat (Env.vars σ "shore.leftCard") (@Finset.card (Fin n) A);
                     let c3:Prop:= @Eq Nat (Env.vars σ "shore.rightCard") (@Finset.card (Fin n) C);
                     let c4:Prop:=And c2 c3;
                     let c5:Prop:=And c1 c4;
                     let c6:Env→ Prop:=
                       (fun (x τ:Env) =>
                           And (@Eq Nat (Env.vars τ "cut.left") (@mask n C)) (@Eq Nat (Env.vars τ "cut.right") (@mask n A)))
                         σ;
                     let c7:Env→ Prop:=fun (σ':Env) =>
                       And (Run B choose σ σ' ((8:Nat))) (c6 σ');
                     let c8:Prop:= @Exists Env c7;
                     let c9:Prop:=Nat.lt (Env.vars σ "shore.leftCard") (Env.vars σ "shore.rightCard");
                     let c10:Prop:=Not c9;
                     let c11:Nat:=Env.vars (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "shore.left";
                     let c12:Env:=Env.setVar (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "cut.right" c11;
                     let c13:Nat→ Nat→ Nat:=Nat.add;
                     let c14:Nat→ Nat:=c13 ((1:Nat));
                     let c15:Nat→ Nat:=c13 (c14 (Cond.size (Cond.lt (Expr.var "shore.leftCard") (Expr.var "shore.rightCard"))));
                     let c16:Nat:=c14 (Expr.size (Expr.var "shore.right"));
                     let c17:Nat:=c14 (Expr.size (Expr.var "shore.left"));
                     let c18:Nat:=c13 c16 c17;
                     let c19:Com:=
                       Com.seq (Com.assign "cut.left" (Expr.var "shore.right")) (Com.assign "cut.right" (Expr.var "shore.left"));
                     let c20:Com:=
                       Com.seq (Com.assign "cut.left" (Expr.var "shore.left")) (Com.assign "cut.right" (Expr.var "shore.right"));
                     let c21:String→ Nat:=Env.vars c12;
                     let c22:Nat:=Env.vars (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "shore.right";
                     let c23:Env:=Env.setVar (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "cut.right" c22;
                     let c24:Nat:=c13 c17 c16;
                     let c25:String→ Nat:=Env.vars c23;
                     @And.casesOn c0 c5 (fun (x:And c0 c5) => c8) a fun (left:c0) (right:c5) =>
                       @And.casesOn c1 c4 (fun (x:c5) => c8) right fun (left_1:c1) (right_1:c4) =>
                         @And.casesOn c2 c3 (fun (x:c4) => c8) right_1 fun (left_2:c2) (right_2:c3) =>
                           @Or.casesOn c9 c10 (fun (x:Or c9 c10) => c8) (Classical.em c9)
                             (fun (hcase:c9) =>
                               @Exists.intro Env c7 c12
                                 (@And.intro (Run B choose σ c12 ((8:Nat))) (c6 c12)
                                   (RunStep.mono B choose σ c12 (c15 c18) ((8:Nat))
                                     (RunStep.ite_true B (Cond.lt (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")) c19 c20 σ
                                       c12 c18
                                       (RunStep.cond_lt_true B σ (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")
                                         (Env.vars σ "shore.leftCard") (Env.vars σ "shore.rightCard")
                                         (RunStep.eval_var B σ "shore.leftCard"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         (RunStep.eval_var B σ "shore.rightCard"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         hcase)
                                       (RunStep.seq B (Com.assign "cut.left" (Expr.var "shore.right"))
                                         (Com.assign "cut.right" (Expr.var "shore.left")) σ
                                         (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) c12 c16 c17
                                         (RunStep.assign B σ "cut.left" (Expr.var "shore.right") (Env.vars σ "shore.right")
                                           (RunStep.eval_var B σ "shore.right"
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                         (RunStep.assign B (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "cut.right"
                                           (Expr.var "shore.left") c11
                                           (RunStep.eval_var B (Env.setVar σ "cut.left" (Env.vars σ "shore.right")) "shore.left"
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   ?_))
                             fun (hcase:c10) =>
                             @Exists.intro Env c7 c23
                               (@And.intro (Run B choose σ c23 ((8:Nat))) (c6 c23)
                                 (RunStep.mono B choose σ c23 (c15 c24) ((8:Nat))
                                   (RunStep.ite_false B (Cond.lt (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")) c19 c20 σ
                                     c23 c24
                                     (RunStep.cond_lt_false B σ (Expr.var "shore.leftCard") (Expr.var "shore.rightCard")
                                       (Env.vars σ "shore.leftCard") (Env.vars σ "shore.rightCard")
                                       (RunStep.eval_var B σ "shore.leftCard"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       (RunStep.eval_var B σ "shore.rightCard"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       hcase)
                                     (RunStep.seq B (Com.assign "cut.left" (Expr.var "shore.left"))
                                       (Com.assign "cut.right" (Expr.var "shore.right")) σ
                                       (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) c23 c17 c16
                                       (RunStep.assign B σ "cut.left" (Expr.var "shore.left") (Env.vars σ "shore.left")
                                         (RunStep.eval_var B σ "shore.left"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                       (RunStep.assign B (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "cut.right"
                                         (Expr.var "shore.right") c22
                                         (RunStep.eval_var B (Env.setVar σ "cut.left" (Env.vars σ "shore.left")) "shore.right"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                 ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
            )
  all_goals simp_all
  all_goals omega

theorem command_spec {n:ℕ} (B:ℕ) (A C:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "shore.left"=mask A∧ σ.vars "shore.right"=mask C∧
      n≤(σ.arrs "subset.bits").length) command
      (fun _ τ => τ.vars "cut.left"=mask (orient A C).1∧ τ.vars "cut.right"=mask (orient A C).2) (42*n+32):=by
  rintro σ ⟨hn,hA,hC,hroom⟩
  obtain ⟨ν,r1,p1⟩:=count_spec B A "shore.left" "shore.leftCard" hB hm σ ⟨hn,hA,hroom⟩
  obtain ⟨μ,r2,p2⟩:=count_spec B C "shore.right" "shore.rightCard" hB hm ν
    ⟨(r1.frame_var "graph.n" (by decide)).trans hn,(r1.frame_var "shore.right" (by decide)).trans hC,
      by rwa [RamFrames.run_array_length r1]⟩
  obtain ⟨τ,r3,p3⟩:=choose_spec B A C hB hm μ
    ⟨((r1.seq r2).frame_var "shore.left" (by decide)).trans hA,
      ((r1.seq r2).frame_var "shore.right" (by decide)).trans hC,
      (r2.frame_var "shore.leftCard" (by decide)).trans p1,p2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3⟩

end Lax263307Proofs.NativeShoreOrientation

end

section

namespace Lax263307Proofs.NativeOutputLength

open Lax455465Proofs
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

theorem exists_bound (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ P:Polynomial ℕ,∀ x:List ℕ,(f x).length≤ P.eval (bitSize x):=by
  obtain ⟨p,wp,tp,hr⟩:=SparseRam.polynomial_execution f hf
  refine ⟨tp,?_⟩
  intro x
  obtain ⟨_,k,hk,s,hrun,_,hout,_⟩:=hr x
  have h:=SparseBounds.run_output_le _ p k _ s hrun
  have hs:(f x).length≤ k:=by simpa only [hout,SparseRam.init,List.length_nil,Nat.zero_add] using h
  exact hs.trans hk

end Lax263307Proofs.NativeOutputLength

end

section

namespace Lax263307Proofs.NativeFlowCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

def decoded {n:ℕ} (R:Finset (Fin n)) (xs:List ℕ):Finset (Fin n) × Finset (Fin n):=
  let s:=orient (NativeFlowShores.left R xs) (NativeFlowShores.right R xs)
  (s.1.image (label R),s.2.image (label R))

theorem step_eq {n:ℕ} (f:List ℕ→ List ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (b load k:ℕ) (R:Finset (Fin n)):
    ComputedSeparators.step f G x b load k R=
      decoded R (f (NativeSplitOracle.query G x R (largeCapacity b n R.card load k))):=rfl

theorem decode_spec (B n:ℕ) (R:Finset (Fin n)) (xs:List ℕ)
    (hB:xs.length+2*n+4< B) (hm:2^n< B) (hw:∀ z∈xs,z< B):
    Spec B (fun σ => NativeFlowShores.Context R xs σ∧ σ.vars "graph.n"=n∧ n≤(σ.arrs "subset.bits").length)
      decodeCommand (fun _ τ => τ.vars "cut.left"=NativeMasks.mask (decoded R xs).1∧
        τ.vars "cut.right"=NativeMasks.mask (decoded R xs).2) (59*R.card+42*n+42):=by
  rintro σ ⟨hd,hn,hroom⟩
  obtain ⟨ν,r1,p1⟩:=NativeFlowShores.command_spec B n R xs hB hm hw σ hd
  obtain ⟨τ,r2,p2⟩:=NativeShoreOrientation.command_spec B
    ((NativeFlowShores.left R xs).image (label R)) ((NativeFlowShores.right R xs).image (label R))
    (by omega) hm ν
    ⟨(r1.frame_var "graph.n" (by decide)).trans hn,p1.2.1,p1.2.2,by rwa [RamFrames.run_array_length r1]⟩
  have he:=NativeShoreMasks.orient_images (label R) (label R).injective
    (NativeFlowShores.left R xs) (NativeFlowShores.right R xs)
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [←he,decoded] using p2⟩

theorem exists_invocation (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ (p:Lax808846.Ram.Program) (wp tp op:Polynomial ℕ) (coeff:List ℕ),
    (∀ z:ℕ,RamPolynomial.value coeff z=wp.eval z)∧
    (∀ q:List ℕ,(f q).length≤ op.eval (bitSize q))∧
    ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0)
      (R:Finset (Fin n)) (large:ℚ≥0),
    let q:=NativeSplitOracle.query G x R large
    FitsInWords (wp.eval (bitSize q)) ((q.length::q)++f q)∧
    ∀ B M:ℕ,1≤ M→ 8*n*n+6*n+M+40< B→ (∀ v,Bounded M (x v:ℚ))→ Bounded M (large:ℚ)→
      bitSize q+1< B→ wp.eval (bitSize q+1)< B→ 2*(2^wp.eval (bitSize q))^2+3< B→
      tp.eval (bitSize q)+1< B→ RamVirtualConstants.allowance p< B→
      op.eval (bitSize q)+2*n+4< B→ 2^n< B→
      Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v:ℚ)) R σ∧
        Stored "split.large" (large:ℚ) σ∧ NativeSplitInput.wordLength R.card<(σ.arrs "lp.word").length∧
        q.length<(σ.arrs "vm.input").length∧ tp.eval (bitSize q)<(σ.arrs "vm.addresses").length∧
        tp.eval (bitSize q)<(σ.arrs "vm.values").length∧ tp.eval (bitSize q)<(σ.arrs "vm.output").length∧
        n≤(σ.arrs "subset.bits").length)
        (command p coeff) (fun _ τ => NativeSplitEntry.Data G x R large τ∧
          τ.vars "cut.left"=NativeMasks.mask (decoded R (f q)).1∧
          τ.vars "cut.right"=NativeMasks.mask (decoded R (f q)).2)
        (NativeSplitOracle.cost R.card p coeff (tp.eval (bitSize q)) (bitSize q)+59*R.card+42*n+42):=by
  obtain ⟨p,wp,tp,coeff,hcoeff,hcall⟩:=NativeSplitOracle.exists_invocation f hf
  obtain ⟨op,hop⟩:=NativeOutputLength.exists_bound f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,hop,?_⟩
  intro n G _ x R large
  let q:=NativeSplitOracle.query G x R large
  obtain ⟨hfit,hcall⟩:=hcall n G x R large
  refine ⟨hfit,?_⟩
  intro B M hM hshape hx hl hsize hpoly hB htime hallow hout hm
  rintro σ ⟨hd,hlσ,hroom,hI,hA,hV,hO,hbits⟩
  obtain ⟨ν,r1,p1⟩:=hcall B M hM hshape hx hl hsize hpoly hB htime hallow σ
    ⟨hd,hlσ,hroom,hI,hA,hV,hO⟩
  have hword:2^wp.eval (bitSize q)< B:=by nlinarith [Nat.two_pow_pos (wp.eval (bitSize q))]
  have hwords:∀ z∈f q,z< B:=fun z hz => (hfit z (List.mem_append_right _ hz)).trans hword
  obtain ⟨τ,r2,p2⟩:=decode_spec B n R (f q) (by have hh:=hop q; dsimp only [q] at hh ⊢; omega) hm hwords ν
    ⟨⟨p1.1.1.labels,p1.1.1.count,p1.2.1,p1.2.2.1⟩,p1.1.1.order,by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),NativeSplitEntry.frame r2 p1.1 (by decide) (by decide),p2⟩

end Lax263307Proofs.NativeFlowCut

end

section

namespace Lax263307Proofs.NativeSeparatorContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding
open scoped NNRat

def protectedVars:List String:= ["graph.n","class.B","algorithm.load","conditioning.k"]

theorem frame {B K n b load k space:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ≥0} {c:Com} {σ τ:Env} (rr:Run B c σ τ K) (hd:Context G x b load k space σ)
    (hv:∀ s∈protectedVars,s∉c.wvars) (hg:"search.graph"∉c.warrs) (hx:"near.costs"∉c.warrs):
    Context G x b load k space τ:=by
  refine ⟨?_,?_,(rr.frame_var "graph.n" (hv _ (by simp [protectedVars]))).trans hd.order,
    (rr.frame_var "class.B" (hv _ (by simp [protectedVars]))).trans hd.classB,
    (rr.frame_var "algorithm.load" (hv _ (by simp [protectedVars]))).trans hd.load,
    (rr.frame_var "conditioning.k" (hv _ (by simp [protectedVars]))).trans hd.target,?_⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" hg] using hd.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" hx] using hd.costs
  · intro a ha; rw [RamFrames.run_array_length rr]; exact hd.room a ha

theorem callback_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hp:s∉NativeFlowPrepare.command.wvars) (hi:s∉NativeSplitInput.command.wvars)
    (ho:s∉NativeOracleScalars.reserved) (hd:s∉NativeFlowCut.decodeCommand.wvars):
    s∉(callback p coeff).wvars:=by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.wvars,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleScalars.command_variable p coeff s ho)) hd)

theorem callback_array (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hp:s∉NativeFlowPrepare.command.warrs) (hi:s∉NativeSplitInput.command.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"]) (hd:s∉NativeFlowCut.decodeCommand.warrs):
    s∉(callback p coeff).warrs:=by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.warrs,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleFrame.command_array p coeff s ho)) hd)

theorem callback_frame {B K n b load k space:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ≥0} {p:Lax808846.Ram.Program} {coeff:List ℕ} {σ τ:Env}
    (rr:Run B (callback p coeff) σ τ K) (hd:Context G x b load k space σ):
    Context G x b load k space τ:=by
  apply frame rr hd
  · intro s hs
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      exact callback_variable p coeff _ (by decide) (by decide) (by decide) (by decide)
  · exact callback_array p coeff _ (by decide) (by decide) (by decide) (by decide)
  · exact callback_array p coeff _ (by decide) (by decide) (by decide) (by decide)

theorem set_var {n b load k space:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ≥0} {σ:Env} (hd:Context G x b load k space σ) (s:String) (v:ℕ)
    (hs:s∉protectedVars):Context G x b load k space (σ.setVar s v):=by
  have hv:∀ a∈protectedVars,(σ.setVar s v).vars a=σ.vars a:=by
    intro a ha
    rw [vars_setVar]
    rw [if_neg (by intro he; subst a; exact hs ha)]
  exact ⟨hd.graph,hd.costs,(hv _ (by simp [protectedVars])).trans hd.order,
    (hv _ (by simp [protectedVars])).trans hd.classB,(hv _ (by simp [protectedVars])).trans hd.load,
    (hv _ (by simp [protectedVars])).trans hd.target,hd.room⟩

end Lax263307Proofs.NativeSeparatorContext

end

section

namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

theorem encode_words (M:ℕ) (qs:List ℚ≥0) (hq:∀ q∈qs,q.num≤ M∧ q.den≤ M):
    ∀ z∈RamUnsignedBuffer.encode qs,z≤ M:=by
  intro z hz
  simp only [RamUnsignedBuffer.encode,List.mem_flatMap] at hz
  obtain ⟨q,hmem,hz⟩:=hz
  simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl
  · exact (hq q hmem).1
  · exact (hq q hmem).2

theorem query_words (n h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0)
    (hx:∀ v,Bounded (2^h) (x v:ℚ)) (hl:Bounded (2^h) (large:ℚ)):
    ∀ z∈NativeSplitOracle.query G x R large,z≤2^(h+n+2):=by
  have hR:=NativeMaskUnpack.card_bound R
  have hp:2^h≤2^(h+n+2):=Nat.pow_le_pow_right (by decide) (by omega)
  have htwo:2*R.card≤2^(h+n+2):=by
    have hn:n≤2^n:=(Nat.lt_two_pow_self).le
    have hh:2^(n+1)≤2^(h+n+2):=Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hh
    omega
  have hM:1≤2^h:=Nat.one_le_two_pow
  have hw:=encode_words (2^h) (List.replicate (2*R.card) (1:ℚ≥0))
    (by intro q hq; have he:q=1:=List.eq_of_mem_replicate hq; subst q; simpa using And.intro hM hM)
  have hm:=encode_words (2^h) (NativeSplitVectors.entries G x R large) (by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    simpa only [Bounded,NNRat.natAbs_num_coe,NNRat.den_coe] using
      NativeSplitEntry.height (2^h) R.card (restriction G R) (fun v => x (label R v)) large hM
        (fun v => hx (label R v)) hl (NativeBlowUp.row i) (NativeBlowUp.col i))
  intro z hz
  simp only [NativeSplitOracle.query,NativeSplitVectors.input_eq,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with ((rfl | rfl) | hz) | hz
  · exact Nat.one_le_two_pow
  · exact htwo
  · exact (hw z hz).trans hp
  · exact (hm z hz).trans hp

theorem query_size (n h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (R:Finset (Fin n)) (large:ℚ≥0)
    (hx:∀ v,Bounded (2^h) (x v:ℚ)) (hl:Bounded (2^h) (large:ℚ)):
    bitSize (NativeSplitOracle.query G x R large)≤ sizeBound n h:=by
  have hs:=WordSize.bounded_size (NativeSplitOracle.query G x R large) (h+n+3)
    (by
      intro z hz
      apply Nat.size_le.mpr
      have hh:=query_words n h G x R large hx hl z hz
      have hp:=Nat.two_pow_pos (h+n+2)
      rw [show h+n+3=(h+n+2)+1 by omega,pow_succ]
      omega)
  have hR:=NativeMaskUnpack.card_bound R
  have hlens:NativeSplitInput.wordLength R.card≤ NativeSplitInput.wordLength n:=by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hR,Nat.mul_le_mul hR hR]
  simp only [NativeSplitOracle.query,NativeSplitInput.input_length] at hs
  exact hs.trans (Nat.mul_le_mul_right (h+n+4) hlens)

theorem eval_mono (P:Polynomial ℕ) {x y:ℕ} (h:x≤ y):P.eval x≤ P.eval y:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  simpa only [hcs] using RamPolynomial.value_mono cs h

end Lax263307Proofs.NativeFlowQueryResources

end

section

namespace Lax263307Proofs.NativeLargeResources

open Lax263307 ComputedSeparators NativeSignedArithmetic NativeLargeCapacity

theorem value_le (b n r load k:ℕ) (hn:0< n) (hl:0< load):
    value b n r load k≤ numerator b n r k+1:=by
  have hd:0< denominator n load:=by dsimp [denominator]; positivity
  have hm:numerator b n r k≤ numerator b n r k*denominator n load:=
    Nat.le_mul_of_pos_right _ hd
  have hp:(numerator b n r k+denominator n load-1)+1=numerator b n r k+denominator n load:=by omega
  have hdiv:(numerator b n r k+denominator n load-1)/denominator n load< numerator b n r k+1:=by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    nlinarith only [hp,hm]
  dsimp [value]
  omega

theorem numerator_mono (b n r s k:ℕ) (h:r≤ s):numerator b n r k≤ numerator b n s k:=by
  dsimp [numerator]
  gcongr

theorem resource_mono (b n r s load k:ℕ) (h:r≤ s):resource b n r load k≤ resource b n s load k:=by
  dsimp [resource,numerator]
  gcongr

theorem capacity_height (b n load k h:ℕ) (R:Finset (Fin n)) (hn:0< n) (hl:0< load):
    Bounded (2^heightExponent b n load k h) (largeCapacity b n R.card load k:ℚ):=by
  have hr:=NativeMaskUnpack.card_bound R
  have hv:value b n R.card load k≤ heightExponent b n load k h:=by
    have hh:=(value_le b n R.card load k hn hl).trans (Nat.add_le_add_right (numerator_mono b n R.card n k hr) 1)
    dsimp [heightExponent]
    omega
  rw [exact_value b n R.card load k hn hl]
  refine ⟨?_,?_⟩
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using hv.trans (Nat.lt_two_pow_self).le
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow:1≤2^heightExponent b n load k h)

theorem input_height (b n load k h:ℕ) (q:ℚ) (hq:Bounded (2^h) q):
    Bounded (2^heightExponent b n load k h) q:=by
  have hh:h≤ heightExponent b n load k h:=by dsimp [heightExponent]; omega
  have hp:=Nat.pow_le_pow_right (by decide:1≤2) hh
  exact ⟨hq.1.trans hp,hq.2.trans hp⟩

theorem resource_le_height (b n load k h:ℕ) (R:Finset (Fin n)):
    resource b n R.card load k≤ heightExponent b n load k h:=by
  have hh:=resource_mono b n R.card n load k (NativeMaskUnpack.card_bound R)
  dsimp [heightExponent]
  omega

end Lax263307Proofs.NativeLargeResources

end

section

namespace Lax263307Proofs.NativeUniformWordGuards

theorem scalar (v w:ℕ) (h:v≤ w):v<2^w:=h.trans_lt Nat.lt_two_pow_self

theorem power_add (u v w:ℕ) (hu:u+2≤ w) (hv:v+2≤ w):2^u+v<2^w:=by
  have huw:u≤ w-1:=by omega
  have hvw:v< w-1:=by omega
  have hp:2^u≤2^(w-1):=Nat.pow_le_pow_right (by decide) huw
  have hvp:v<2^(w-1):=hvw.trans Nat.lt_two_pow_self
  have he:w=(w-1)+1:=by omega
  rw [he,pow_succ]
  omega

theorem virtual (u w:ℕ) (h:2*u+4≤ w):2*(2^u)^2+3<2^w:=by
  have hpow:2^(u*2+4)≤2^w:=Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_add] at hpow
  norm_num at hpow
  rw [←pow_mul]
  have hp:=Nat.two_pow_pos (u*2)
  nlinarith only [hpow,hp]

end Lax263307Proofs.NativeUniformWordGuards

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeUniformFlow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeFlowQueryResources NativeUniformWordGuards
open scoped NNRat

theorem cost_mono (r n s S t T:ℕ) (p:Lax808846.Ram.Program) (coeff:List ℕ)
    (hr:r≤ n) (hs:s≤ S) (ht:t≤ T):NativeSplitOracle.cost r p coeff t s≤ NativeSplitOracle.cost n p coeff T S:=by
  have hlen:NativeSplitInput.wordLength r≤ NativeSplitInput.wordLength n:=by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hr,Nat.mul_le_mul hr hr]
  dsimp only [NativeSplitOracle.cost]
  gcongr

theorem exists_callback (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ (p:Lax808846.Ram.Program) (wp tp op:Polynomial ℕ) (coeff:List ℕ),
    (∀ z:ℕ,RamPolynomial.value coeff z=wp.eval z)∧
    ∀ (b n load k h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0),
    0< n→ 0< load→ (∀ v,Bounded (2^h) (x v:ℚ))→
    let H:=NativeLargeResources.heightExponent b n load k h
    ∀ w:ℕ,wordHeight n H p wp tp op≤ w→ ∀ R:Finset (Fin n),
    Spec (2^w) (fun σ => Context G x b load k (spaceBound n H tp) σ∧ σ.vars "separator.remaining"=NativeMasks.mask R)
      (callback p coeff) (fun _ τ => Context G x b load k (spaceBound n H tp) τ∧
        τ.vars "cut.left"=NativeMasks.mask (ComputedSeparators.step f G x b load k R).1∧
        τ.vars "cut.right"=NativeMasks.mask (ComputedSeparators.step f G x b load k R).2)
      (callbackTime n H p coeff tp):=by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,_,hcall⟩:=NativeFlowCut.exists_invocation f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,?_⟩
  intro b n load k h G _ x hn hl hx
  dsimp only
  let H:=NativeLargeResources.heightExponent b n load k h
  let S:=sizeBound n H
  let U:=wp.eval (S+1)
  let T:=tp.eval S
  let O:=op.eval S
  let A:=RamVirtualConstants.allowance p
  intro w hwidth R
  have hw:2*U+H+shape n+S+T+O+A+20≤ w:=hwidth
  have hHn:n+30≤ H:=by dsimp [H,NativeLargeResources.heightExponent]; omega
  have hL:3*n+5≤ shape n:=by dsimp [shape]; nlinarith only []
  have hxH:∀ v,Bounded (2^H) (x v:ℚ):=fun v => NativeLargeResources.input_height b n load k h _ (hx v)
  let large:=largeCapacity b n R.card load k
  let q:=NativeSplitOracle.query G x R large
  have hlH:Bounded (2^H) (large:ℚ):=NativeLargeResources.capacity_height b n load k h R hn hl
  have hs:bitSize q≤ S:=query_size n H G x R large hxH hlH
  have hu:wp.eval (bitSize q+1)≤ U:=eval_mono wp (Nat.add_le_add_right hs 1)
  have hu0:wp.eval (bitSize q)≤ U:=eval_mono wp (by omega)
  have ht:tp.eval (bitSize q)≤ T:=eval_mono tp hs
  have ho:op.eval (bitSize q)≤ O:=eval_mono op hs
  have hm:2^H<2^w:=by
    simpa only [Nat.add_zero] using power_add H 0 w (by omega) (by omega)
  have hnword:2^n<2^w:=(Nat.pow_le_pow_right (by decide) (by omega:n≤ H)).trans_lt hm
  have hshape:8*n*n+6*n+2^H+40<2^w:=by
    simpa only [shape,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using power_add H (shape n) w (by omega) (by omega)
  have hr:NativeLargeCapacity.resource b n R.card load k<2^w:=
    scalar _ w ((NativeLargeResources.resource_le_height b n load k h R).trans (by omega))
  have hR:=NativeMaskUnpack.card_bound R
  have hlen:NativeSplitInput.wordLength R.card≤ NativeSplitInput.wordLength n:=by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hR,Nat.mul_le_mul hR hR]
  have hspaceN:n≤ spaceBound n H tp:=by dsimp [spaceBound]; omega
  have hspaceQ:NativeSplitInput.wordLength R.card< spaceBound n H tp:=by dsimp [spaceBound]; omega
  have hspaceT:tp.eval (bitSize q)< spaceBound n H tp:=by dsimp [spaceBound]; change _< NativeSplitInput.wordLength n+T+n+2; omega
  obtain ⟨_,hquery⟩:=hcall n G x R large
  have hgSize:bitSize q+1<2^w:=scalar _ w (by omega)
  have hgPoly:wp.eval (bitSize q+1)<2^w:=scalar _ w (by omega)
  have hgVirtual:2*(2^wp.eval (bitSize q))^2+3<2^w:=virtual _ w (by omega)
  have hgTime:tp.eval (bitSize q)+1<2^w:=scalar _ w (by omega)
  have hgAllowance:RamVirtualConstants.allowance p<2^w:=scalar _ w (by change A≤ w; omega)
  have hgOutput:op.eval (bitSize q)+2*n+4<2^w:=scalar _ w (by omega)
  have hc:=hquery (2^w) (2^H) Nat.one_le_two_pow hshape hxH hlH
    hgSize hgPoly hgVirtual hgTime hgAllowance hgOutput hnword
  rintro σ ⟨hd,hremaining⟩
  obtain ⟨ν,r1,p1⟩:=NativeFlowPrepare.command_spec (2^w) b n load k G (fun v => (x v:ℚ)) R hn hl
    (scalar _ w (by omega)) hnword hr σ
    ⟨hd.graph,hd.costs,hd.order,hremaining,hd.classB,hd.load,hd.target,
      hspaceN.trans (hd.room "subset.bits" (by simp [workspace])),
      hspaceN.trans (hd.room "restrict.vertices" (by simp [workspace]))⟩
  have hroom (a:String) (ha:a∈workspace):spaceBound n H tp≤(ν.arrs a).length:=by
    rw [RamFrames.run_array_length r1]; exact hd.room a ha
  obtain ⟨τ,r2,p2⟩:=hc ν
    ⟨p1.1,p1.2,hspaceQ.trans_le (hroom "lp.word" (by simp [workspace])),
      by simpa only [q,NativeSplitOracle.query,NativeSplitInput.input_length] using
        hspaceQ.trans_le (hroom "vm.input" (by simp [workspace])),
      hspaceT.trans_le (hroom "vm.addresses" (by simp [workspace])),
      hspaceT.trans_le (hroom "vm.values" (by simp [workspace])),
      hspaceT.trans_le (hroom "vm.output" (by simp [workspace])),
      hspaceN.trans (hroom "subset.bits" (by simp [workspace]))⟩
  have hcost:NativeSplitOracle.cost R.card p coeff (tp.eval (bitSize q)) (bitSize q)+59*R.card+42*n+42≤
      NativeSplitOracle.cost n p coeff T S+59*n+42*n+42:=by
    have hh:=cost_mono R.card n (bitSize q) S (tp.eval (bitSize q)) T p coeff hR hs ht
    omega
  have rr:=r1.seq r2
  refine ⟨τ,rr.mono (by
      simpa only [callbackTime,Nat.add_assoc] using Nat.add_le_add_left hcost (43*n+12*(2*n).size+78)),
    callback_frame rr hd,?_,?_⟩
  · simpa only [NativeFlowCut.step_eq,q,large] using p2.2.1
  · simpa only [NativeFlowCut.step_eq,q,large] using p2.2.2

end Lax263307Proofs.NativeUniformFlow

end

section

namespace Lax263307Proofs.NativeSetMasks

open NativeMasks

theorem outside {n:ℕ} (A:Finset (Fin n)) (j:ℕ) (hj:n≤ j):(mask A).testBit j=false:=by
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro h
  obtain ⟨v,hv,hvj⟩:=Finset.mem_image.mp h
  have hh:=v.isLt
  omega

theorem union {n:ℕ} (A C:Finset (Fin n)):mask (A∪C)=Nat.lor (mask A) (mask C):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A∪C)).testBit j=((mask A)|||(mask C)).testBit j
  rw [Nat.testBit_or]
  by_cases hj:j< n
  · change (mask (A∪C)).testBit (⟨j,hj⟩:Fin n).val=_
    rw [mask_member (A∪C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA:(⟨j,hj⟩:Fin n)∈A <;> by_cases hC:(⟨j,hj⟩:Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.or_false]

theorem inter {n:ℕ} (A C:Finset (Fin n)):mask (A∩C)=Nat.land (mask A) (mask C):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A∩C)).testBit j=((mask A)&&&(mask C)).testBit j
  rw [Nat.testBit_and]
  by_cases hj:j< n
  · change (mask (A∩C)).testBit (⟨j,hj⟩:Fin n).val=_
    rw [mask_member (A∩C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA:(⟨j,hj⟩:Fin n)∈A <;> by_cases hC:(⟨j,hj⟩:Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.and_false]

theorem sdiff {n:ℕ} (A C:Finset (Fin n)):
    mask (A\C)=Nat.xor (mask A) (Nat.land (mask A) (mask C)):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A\C)).testBit j=((mask A)^^^((mask A)&&&(mask C))).testBit j
  rw [Nat.testBit_xor,Nat.testBit_and]
  by_cases hj:j< n
  · change (mask (A\C)).testBit (⟨j,hj⟩:Fin n).val=_
    rw [mask_member (A\C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA:(⟨j,hj⟩:Fin n)∈A <;> by_cases hC:(⟨j,hj⟩:Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.and_false,Bool.xor_self]

end Lax263307Proofs.NativeSetMasks

end

section

namespace Lax263307Proofs.NativeCutRecords

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

theorem length_words {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))):
    (words cs).length=2*cs.length:=by
  induction cs with
  | nil => rfl
  | cons s cs ih => simp only [words,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

theorem words_snoc {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (A C:Finset (Fin n)):
    words (cs++[(A,C)])=(words cs++[mask A])++[mask C]:=by
  simp [words,List.append_assoc]

theorem separator_snoc {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (A C:Finset (Fin n)):
    separator (cs++[(A,C)])=separator cs∪(A∩C):=by
  induction cs with
  | nil => simp [separator]
  | cons s cs ih =>
    simpa only [List.cons_append,separator,List.foldr_cons,Finset.union_assoc] using
      congrArg (fun S => (s.1∩s.2)∪S) ih

theorem update_spec {n:ℕ} (B k:ℕ) (A C S:Finset (Fin n)) (hB:k+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "cut.left"=mask A∧ σ.vars "cut.right"=mask C∧
      σ.vars "separator.value"=mask S∧ σ.vars "separator.count"=k) update
      (fun _ τ => τ.vars "separator.remaining"=mask (A\C)∧
        τ.vars "separator.value"=mask (S∪(A∩C))∧ τ.vars "separator.count"=k+1) 16:=by
  have ha:=(mask_bound A).trans hm
  have hc:=(mask_bound C).trans hm
  have hs:=(mask_bound S).trans hm
  have hi:=(mask_bound (A∩C)).trans hm
  have hd:=(mask_bound (A\C)).trans hm
  have hu:=(mask_bound (S∪(A∩C))).trans hm
  simp only [NativeSetMasks.sdiff,NativeSetMasks.union,NativeSetMasks.inter] at hi hd hu ⊢
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "cut.left") (@mask n A)) (And (@Eq Nat (Env.vars σ "cut.right") (@mask n C)) (And (@Eq Nat (Env.vars σ "separator.value") (@mask n S)) (@Eq Nat (Env.vars σ "separator.count") k)))) => let c0:Prop:= @Eq Nat (Env.vars σ "cut.left") (@mask n A); let c1:Prop:= @Eq Nat (Env.vars σ "cut.right") (@mask n C); let c2:Prop:= @Eq Nat (Env.vars σ "separator.value") (@mask n S); let c3:Prop:=And c2 (@Eq Nat (Env.vars σ "separator.count") k); let c4:Prop:=And c1 c3; let c5:Nat:=Nat.land (@mask n A) (@mask n C); let c6:Nat:=Nat.xor (@mask n A) c5; let c7:Nat:=Nat.lor (@mask n S) c5; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat:=c8 k ((1:Nat)); let c10:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "separator.remaining") c6) (And (@Eq Nat (Env.vars τ "separator.value") c7) (@Eq Nat (Env.vars τ "separator.count") c9))) σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((16:Nat))) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Nat:=Nat.land (Env.vars σ "cut.left") (Env.vars σ "cut.right"); let c14:Nat:=Nat.xor (Env.vars σ "cut.left") c13; let c15:Env:=Env.setVar σ "separator.remaining" c14; let c16:String→ Nat:=Env.vars c15; let c17:Nat:=c16 "separator.value"; let c18:Nat:=c16 "cut.left"; let c19:Nat:=c16 "cut.right"; let c20:Nat:=Nat.land c18 c19; let c21:Nat:=Nat.lor c17 c20; let c22:Env:=Env.setVar c15 "separator.value" c21; let c23:Nat:=Env.vars c22 "separator.count"; let c24:Nat:=c8 c23 ((1:Nat)); let c25:Env:=Env.setVar c22 "separator.count" c24; let c26:Nat→ Nat:=c8 ((1:Nat)); let c27:Expr:=Expr.xor (Expr.var "cut.left") (Expr.and (Expr.var "cut.left") (Expr.var "cut.right")); let c28:Nat:=c26 (Expr.size c27); let c29:Expr:=Expr.or (Expr.var "separator.value") (Expr.and (Expr.var "cut.left") (Expr.var "cut.right")); let c30:Nat:=c26 (Expr.size c29); let c31:Expr:=Expr.add (Expr.var "separator.count") (Expr.lit ((1:Nat))); let c32:Nat:=c26 (Expr.size c31); let c33:Nat:=c8 c30 c32; let c34:Com:=Com.assign "separator.value" c29; let c35:Com:=Com.assign "separator.count" c31; let c36:String→ Nat:=Env.vars c25; @And.casesOn c0 c4 (fun (x:And c0 c4) => c12) a fun (left:c0) (right:c4) => @And.casesOn c1 c3 (fun (x:c4) => c12) right fun (left_1:c1) (right_1:c3) => @And.casesOn c2 (@Eq Nat (Env.vars σ "separator.count") k) (fun (x:c3) => c12) right_1 fun (left_2:c2) (right_2:@Eq Nat (Env.vars σ "separator.count") k) => @Exists.intro Env c11 c25 (@And.intro (Run B update σ c25 ((16:Nat))) (c10 c25) (RunStep.mono B update σ c25 (c8 c28 c33) ((16:Nat)) (RunStep.seq B (Com.assign "separator.remaining" c27) (Com.seq c34 c35) σ c15 c25 c28 c33 (RunStep.assign B σ "separator.remaining" c27 c14 (RunStep.eval_xor B σ (Expr.var "cut.left") (Expr.and (Expr.var "cut.left") (Expr.var "cut.right")) (Env.vars σ "cut.left") c13 (RunStep.eval_var B σ "cut.left" (?nAX_g8875_0_0_0)) (RunStep.eval_and B σ (Expr.var "cut.left") (Expr.var "cut.right") (Env.vars σ "cut.left") (Env.vars σ "cut.right") (RunStep.eval_var B σ "cut.left" (?nAX_g8875_0_0_1)) (RunStep.eval_var B σ "cut.right" (?nAX_g8875_0_0_2)) ?_) ?_)) (RunStep.seq B c34 c35 c15 c22 c25 c30 c32 (RunStep.assign B c15 "separator.value" c29 c21 (RunStep.eval_or B c15 (Expr.var "separator.value") (Expr.and (Expr.var "cut.left") (Expr.var "cut.right")) c17 c20 (RunStep.eval_var B c15 "separator.value" (?nAX_g8875_0_0_3)) (RunStep.eval_and B c15 (Expr.var "cut.left") (Expr.var "cut.right") c18 c19 (RunStep.eval_var B c15 "cut.left" (?nAX_g8875_0_0_4)) (RunStep.eval_var B c15 "cut.right" (?nAX_g8875_0_0_5)) ?_) ?_)) (RunStep.assign B c22 "separator.count" c31 c24 (RunStep.eval_add B c22 (Expr.var "separator.count") (Expr.lit ((1:Nat))) c23 ((1:Nat)) (RunStep.eval_var B c22 "separator.count" (?nAX_g8875_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c22 (?nAX_g8875_0_0_7)) (?nAX_g8875_0_0_8))))) (?nAX_g8875_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8875_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8875_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all
  all_goals omega

theorem command_spec {n:ℕ} (B:ℕ) (cs:List (Finset (Fin n) × Finset (Fin n)))
    (A C:Finset (Fin n)) (hB:2*cs.length+4< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "cut.left"=mask A∧ σ.vars "cut.right"=mask C∧
      σ.vars "separator.value"=mask (separator cs)∧ σ.vars "separator.count"=cs.length∧
      Prefix (words cs) "separator.cuts" σ∧ σ.vars "separator.position"=2*cs.length∧
      2*cs.length+2≤(σ.arrs "separator.cuts").length) command
      (fun _ τ => τ.vars "separator.remaining"=mask (A\C)∧
        τ.vars "separator.value"=mask (separator (cs++[(A,C)]))∧ τ.vars "separator.count"=cs.length+1∧
        Prefix (words (cs++[(A,C)])) "separator.cuts" τ∧ τ.vars "separator.position"=2*(cs.length+1)) 30:=by
  rintro σ ⟨ha,hc,hs,hn,hprefix,hpos,hroom⟩
  obtain ⟨ν,r1,p1⟩:=RamWordBuffer.append_spec B "separator.cuts" "separator.position" (words cs) (mask A)
    (.var "cut.left") (by omega) (by rw [length_words]; omega) σ
    ⟨hprefix,by simpa only [length_words] using hpos,by rw [length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨ha.symm,ha ▸ (mask_bound A).trans hm⟩⟩
  have hcν:ν.vars "cut.right"=mask C:=(r1.frame_var "cut.right" (by decide)).trans hc
  obtain ⟨μ,r2,p2⟩:=RamWordBuffer.append_spec B "separator.cuts" "separator.position" (words cs++[mask A]) (mask C)
    (.var "cut.right") (by omega) (by simp only [List.length_append,List.length_singleton,length_words]; omega) ν
    ⟨p1.1,by simpa only [List.length_append,List.length_singleton] using p1.2,
      by rw [RamFrames.run_array_length r1]; simp only [List.length_append,List.length_singleton,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨hcν.symm,hcν ▸ (mask_bound C).trans hm⟩⟩
  have rr12:=r1.seq r2
  obtain ⟨τ,r3,p3⟩:=update_spec B cs.length A C (separator cs) (by omega) hm μ
    ⟨(rr12.frame_var "cut.left" (by decide)).trans ha,(rr12.frame_var "cut.right" (by decide)).trans hc,
      (rr12.frame_var "separator.value" (by decide)).trans hs,(rr12.frame_var "separator.count" (by decide)).trans hn⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by decide),p3.1,?_,p3.2.2,?_,?_⟩
  · simpa only [separator_snoc] using p3.2.1
  · simpa only [words_snoc,Prefix,r3.frame_arr "separator.cuts" (by decide)] using p2.1
  · rw [r3.frame_var "separator.position" (by decide),p2.2,List.length_append,List.length_singleton,length_words]
    omega

end Lax263307Proofs.NativeCutRecords

end

section

namespace Lax263307Proofs.NativeCutTrace

open Lax263307 ComputedSeparators

theorem small {n:ℕ} (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (fuel:ℕ) (R:Finset (Fin n)) (h:3*R.card≤2*n):cuts cut fuel R=[]:=by
  cases fuel <;> simp [cuts,h]

theorem advance {n:ℕ} (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (i:ℕ) (hi:i< n) (R:Finset (Fin n)) (h:¬3*R.card≤2*n):
    cuts cut (n-i) R=cut R::cuts cut (n-(i+1)) ((cut R).1\(cut R).2):=by
  have he:n-i=(n-(i+1))+1:=by omega
  rw [he,cuts,if_neg h]

theorem remaining_snoc {n:ℕ} (start:Finset (Fin n))
    (cs:List (Finset (Fin n) × Finset (Fin n))) (A C:Finset (Fin n)):
    remaining start (cs++[(A,C)])=A\C:=by
  simp [remaining,List.getElem_append_right]

theorem append_advance {n:ℕ} (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (i:ℕ) (hi:i< n) (R:Finset (Fin n)) (h:¬3*R.card≤2*n)
    (cs target:List (Finset (Fin n) × Finset (Fin n)))
    (he:cs++cuts cut (n-i) R=target):
    (cs++[cut R])++cuts cut (n-(i+1)) ((cut R).1\(cut R).2)=target:=by
  rw [advance cut i hi R h] at he
  simpa only [List.append_assoc,List.singleton_append] using he

theorem append_stop {n:ℕ} (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (i:ℕ) (R:Finset (Fin n)) (h:3*R.card≤2*n)
    (cs target:List (Finset (Fin n) × Finset (Fin n)))
    (he:cs++cuts cut (n-i) R=target):cs++cuts cut (n-(i+1)) R=target:=by
  simpa only [small cut _ R h] using he

end Lax263307Proofs.NativeCutTrace

end

section

namespace Lax263307Proofs.NativeCutTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeMasks

theorem finish_spec (B n r:ℕ) (hr:r≤ n) (hB:3*n+5< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "unpack.card"=r) finish
      (fun _ τ => τ.vars "separator.active"=(if 3*r≤2*n then 0 else 1)) 10:=by
  by_cases h:3*r≤2*n
  all_goals simp only [h,if_true,if_false]
  all_goals (first
             | (expose_names;
                 (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "unpack.card") r)) =>
                     let c0:Env→ Prop:=
                       (fun (x τ:Env) =>
                           @Eq Nat (Env.vars τ "separator.active") ((0:Nat)))
                         σ;
                     let c1:Env→ Prop:=fun (σ':Env) =>
                       And (Run B finish σ σ' ((10:Nat))) (c0 σ');
                     let c2:Prop:= @Exists Env c1;
                     let c3:Nat→ Nat→ Nat:=Nat.mul;
                     let c4:Nat:=c3 ((2:Nat)) (Env.vars σ "graph.n");
                     let c5:Nat:=c3 ((3:Nat)) (Env.vars σ "unpack.card");
                     let c6:Prop:=Nat.lt c4 c5;
                     let c7:Prop:=Not c6;
                     let c8:Env:=Env.setVar σ "separator.active" ((1:Nat));
                     let c9:Nat→ Nat→ Nat:=Nat.add;
                     let c10:Nat→ Nat:=c9 ((1:Nat));
                     let c11:Expr:=
                       Expr.mul (Expr.lit ((2:Nat))) (Expr.var "graph.n");
                     let c12:Expr:=
                       Expr.mul (Expr.lit ((3:Nat))) (Expr.var "unpack.card");
                     let c13:Cond:=Cond.lt c11 c12;
                     let c14:Nat→ Nat:=c9 (c10 (Cond.size c13));
                     let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                     let c16:Com:=
                       Com.assign "separator.active" (Expr.lit ((1:Nat)));
                     let c17:Com:=
                       Com.assign "separator.active" (Expr.lit ((0:Nat)));
                     let c18:Env:=Env.setVar σ "separator.active" ((0:Nat));
                     let c19:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                     @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "unpack.card") r)
                       (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "unpack.card") r)) => c2) a
                       fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:@Eq Nat (Env.vars σ "unpack.card") r) =>
                       @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c2) (Classical.em c6)
                         (fun (hcase:c6) =>
                           @Exists.intro Env c1 c8
                             (@And.intro (Run B finish σ c8 ((10:Nat))) (c0 c8)
                               (RunStep.mono B finish σ c8 (c14 c15) ((10:Nat))
                                 (RunStep.ite_true B c13 c16 c17 σ c8 c15
                                   (RunStep.cond_lt_true B σ c11 c12 c4 c5
                                     (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                       (Expr.var "graph.n") ((2:Nat))
                                       (Env.vars σ "graph.n")
                                       (RunStep.eval_lit B ((2:Nat)) σ
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       (RunStep.eval_var B σ "graph.n"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     (RunStep.eval_mul B σ (Expr.lit ((3:Nat)))
                                       (Expr.var "unpack.card") ((3:Nat))
                                       (Env.vars σ "unpack.card")
                                       (RunStep.eval_lit B ((3:Nat)) σ
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       (RunStep.eval_var B σ "unpack.card"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     hcase)
                                   (RunStep.assign B σ "separator.active"
                                     (Expr.lit ((1:Nat)))
                                     ((1:Nat))
                                     (RunStep.eval_lit B ((1:Nat)) σ
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                               ?_))
                         fun (hcase:c7) =>
                         @Exists.intro Env c1 c18
                           (@And.intro (Run B finish σ c18 ((10:Nat))) (c0 c18)
                             (RunStep.mono B finish σ c18 (c14 c19) ((10:Nat))
                               (RunStep.ite_false B c13 c16 c17 σ c18 c19
                                 (RunStep.cond_lt_false B σ c11 c12 c4 c5
                                   (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                     (Expr.var "graph.n") ((2:Nat))
                                     (Env.vars σ "graph.n")
                                     (RunStep.eval_lit B ((2:Nat)) σ
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     (RunStep.eval_var B σ "graph.n"
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   (RunStep.eval_mul B σ (Expr.lit ((3:Nat)))
                                     (Expr.var "unpack.card") ((3:Nat))
                                     (Env.vars σ "unpack.card")
                                     (RunStep.eval_lit B ((3:Nat)) σ
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     (RunStep.eval_var B σ "unpack.card"
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   hcase)
                                 (RunStep.assign B σ "separator.active"
                                   (Expr.lit ((0:Nat)))
                                   ((0:Nat))
                                   (RunStep.eval_lit B ((0:Nat)) σ
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
             | (expose_names;
                 (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "unpack.card") r)) =>
                     let c0:Env→ Prop:=
                       (fun (x τ:Env) =>
                           @Eq Nat (Env.vars τ "separator.active") ((1:Nat)))
                         σ;
                     let c1:Env→ Prop:=fun (σ':Env) =>
                       And (Run B finish σ σ' ((10:Nat))) (c0 σ');
                     let c2:Prop:= @Exists Env c1;
                     let c3:Nat→ Nat→ Nat:=Nat.mul;
                     let c4:Nat:=c3 ((2:Nat)) (Env.vars σ "graph.n");
                     let c5:Nat:=c3 ((3:Nat)) (Env.vars σ "unpack.card");
                     let c6:Prop:=Nat.lt c4 c5;
                     let c7:Prop:=Not c6;
                     let c8:Env:=Env.setVar σ "separator.active" ((1:Nat));
                     let c9:Nat→ Nat→ Nat:=Nat.add;
                     let c10:Nat→ Nat:=c9 ((1:Nat));
                     let c11:Expr:=
                       Expr.mul (Expr.lit ((2:Nat))) (Expr.var "graph.n");
                     let c12:Expr:=
                       Expr.mul (Expr.lit ((3:Nat))) (Expr.var "unpack.card");
                     let c13:Cond:=Cond.lt c11 c12;
                     let c14:Nat→ Nat:=c9 (c10 (Cond.size c13));
                     let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                     let c16:Com:=
                       Com.assign "separator.active" (Expr.lit ((1:Nat)));
                     let c17:Com:=
                       Com.assign "separator.active" (Expr.lit ((0:Nat)));
                     let c18:Env:=Env.setVar σ "separator.active" ((0:Nat));
                     let c19:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                     @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "unpack.card") r)
                       (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "unpack.card") r)) => c2) a
                       fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:@Eq Nat (Env.vars σ "unpack.card") r) =>
                       @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c2) (Classical.em c6)
                         (fun (hcase:c6) =>
                           @Exists.intro Env c1 c8
                             (@And.intro (Run B finish σ c8 ((10:Nat))) (c0 c8)
                               (RunStep.mono B finish σ c8 (c14 c15) ((10:Nat))
                                 (RunStep.ite_true B c13 c16 c17 σ c8 c15
                                   (RunStep.cond_lt_true B σ c11 c12 c4 c5
                                     (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                       (Expr.var "graph.n") ((2:Nat))
                                       (Env.vars σ "graph.n")
                                       (RunStep.eval_lit B ((2:Nat)) σ
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       (RunStep.eval_var B σ "graph.n"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     (RunStep.eval_mul B σ (Expr.lit ((3:Nat)))
                                       (Expr.var "unpack.card") ((3:Nat))
                                       (Env.vars σ "unpack.card")
                                       (RunStep.eval_lit B ((3:Nat)) σ
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       (RunStep.eval_var B σ "unpack.card"
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     hcase)
                                   (RunStep.assign B σ "separator.active"
                                     (Expr.lit ((1:Nat)))
                                     ((1:Nat))
                                     (RunStep.eval_lit B ((1:Nat)) σ
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                               ?_))
                         fun (hcase:c7) =>
                         @Exists.intro Env c1 c18
                           (@And.intro (Run B finish σ c18 ((10:Nat))) (c0 c18)
                             (RunStep.mono B finish σ c18 (c14 c19) ((10:Nat))
                               (RunStep.ite_false B c13 c16 c17 σ c18 c19
                                 (RunStep.cond_lt_false B σ c11 c12 c4 c5
                                   (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                     (Expr.var "graph.n") ((2:Nat))
                                     (Env.vars σ "graph.n")
                                     (RunStep.eval_lit B ((2:Nat)) σ
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     (RunStep.eval_var B σ "graph.n"
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   (RunStep.eval_mul B σ (Expr.lit ((3:Nat)))
                                     (Expr.var "unpack.card") ((3:Nat))
                                     (Env.vars σ "unpack.card")
                                     (RunStep.eval_lit B ((3:Nat)) σ
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     (RunStep.eval_var B σ "unpack.card"
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   hcase)
                                 (RunStep.assign B σ "separator.active"
                                   (Expr.lit ((0:Nat)))
                                   ((0:Nat))
                                   (RunStep.eval_lit B ((0:Nat)) σ
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
            )
  all_goals simp_all
  all_goals omega

theorem command_spec {n:ℕ} (B:ℕ) (R:Finset (Fin n)) (hB:3*n+5< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "separator.remaining"=mask R∧ n≤(σ.arrs "subset.bits").length)
      command (fun _ τ => τ.vars "separator.active"=(if 3*R.card≤2*n then 0 else 1)∧
        Prefix (Lax263307.IndependentSetEncoding.encodeOutput R) "subset.bits" τ∧ τ.vars "unpack.card"=R.card)
      (21*n+20):=by
  rintro σ ⟨hn,hR,hroom⟩
  let ν:=σ.setVar "unpack.mask" (mask R)
  have r1:Run B (.assign "unpack.mask" (.var "separator.remaining")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hR.symm,hR ▸ (mask_bound R).trans hm⟩)
  obtain ⟨μ,r2,p2⟩:=NativeMaskUnpack.command_spec B R (by omega) hm ν
    ⟨by simpa [ν] using hn,by simp [ν],hroom⟩
  obtain ⟨τ,r3,p3⟩:=finish_spec B n R.card (NativeMaskUnpack.card_bound R) hB μ
    ⟨((r1.seq r2).frame_var "graph.n" (by decide)).trans hn,p2.2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3,
    by simpa only [Prefix,r3.frame_arr "subset.bits" (by decide)] using p2.1,
    (r3.frame_var "unpack.card" (by decide)).trans p2.2⟩

end Lax263307Proofs.NativeCutTest

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeCutLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def preserved:List String:= ["separator.remaining","separator.value","separator.count","separator.position"]

structure State {n:ℕ} (Q:Env→ Prop) (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (start:Finset (Fin n)) (i:ℕ) (σ:Env) (cs:List (Finset (Fin n) × Finset (Fin n))) (R:Finset (Fin n)):Prop where
  context:Q σ
  length_le:cs.length≤ i
  suffix:cs++cuts cut (n-i) R=cuts cut n start
  last:R=remaining start cs
  remaining:σ.vars "separator.remaining"=mask R
  separator:σ.vars "separator.value"=mask (ComputedSeparators.separator cs)
  count:σ.vars "separator.count"=cs.length
  prefix_words:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  position:σ.vars "separator.position"=2*cs.length
  bitroom:n≤(σ.arrs "subset.bits").length
  cutroom:2*n≤(σ.arrs "separator.cuts").length

def Invariant {n:ℕ} (Q:Env→ Prop) (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (start:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "separator.i"≤ n∧ ∃ cs R,State Q cut start (σ.vars "separator.i") σ cs R

theorem state_frame {B n i K:ℕ} {Q:Env→ Prop}
    {cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n)} {start R:Finset (Fin n)}
    {cs:List (Finset (Fin n) × Finset (Fin n))} {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hs:State Q cut start i σ cs R) (hq:Q τ)
    (hv:∀ s∈preserved,s∉c.wvars) (ha:"separator.cuts"∉c.warrs):State Q cut start i τ cs R:=by
  refine ⟨hq,hs.length_le,hs.suffix,hs.last,
    (rr.frame_var "separator.remaining" (hv _ (by simp [preserved]))).trans hs.remaining,
    (rr.frame_var "separator.value" (hv _ (by simp [preserved]))).trans hs.separator,
    (rr.frame_var "separator.count" (hv _ (by simp [preserved]))).trans hs.count,?_,
    (rr.frame_var "separator.position" (hv _ (by simp [preserved]))).trans hs.position,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "separator.cuts" ha] using hs.prefix_words
  · rw [RamFrames.run_array_length rr]; exact hs.bitroom
  · rw [RamFrames.run_array_length rr]; exact hs.cutroom

theorem step_spec {n:ℕ} (B K:ℕ) (Q:Env→ Prop)
    (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n)) (start:Finset (Fin n)) (body:Com)
    (hB:3*n+5< B) (hm:2^n< B)
    (horder:∀ σ,Q σ→ σ.vars "graph.n"=n)
    (hset:∀ σ k,Q σ→ Q (σ.setVar "separator.i" k))
    (hcheck:∀ {σ τ:Env} {k:ℕ},Run B NativeCutTest.command σ τ k→ Q σ→ Q τ)
    (hrecord:∀ {σ τ:Env} {k:ℕ},Run B NativeCutRecords.command σ τ k→ Q σ→ Q τ)
    (hbody:∀ R:Finset (Fin n),¬3*R.card≤2*n→
      Spec B (fun σ => Q σ∧ σ.vars "separator.remaining"=mask R) body
        (fun _ τ => Q τ∧ τ.vars "cut.left"=mask (cut R).1∧ τ.vars "cut.right"=mask (cut R).2) K)
    (hvars:∀ s∈preserved,s∉body.wvars) (hindex:"separator.i"∉body.wvars)
    (harray:"separator.cuts"∉body.warrs):
    Spec B (fun σ => Invariant Q cut start σ∧ σ.vars "separator.i"< n) (step body)
      (fun σ τ => Invariant Q cut start τ∧ τ.vars "separator.i"=σ.vars "separator.i"+1) (21*n+K+58):=by
  rintro σ ⟨⟨hile,cs,R,hs⟩,hlt⟩
  let i:=σ.vars "separator.i"
  have hilt:i< n:=hlt
  have hlen:cs.length≤ i:=hs.length_le
  have hiB:i< B:=by dsimp [i]; omega
  obtain ⟨ν,r1,p1⟩:=NativeCutTest.command_spec B R hB hm σ ⟨horder σ hs.context,hs.remaining,hs.bitroom⟩
  have sn:=state_frame r1 hs (hcheck r1 hs.context) (by decide) (by decide)
  have hin:ν.vars "separator.i"=i:=r1.frame_var "separator.i" (by decide)
  have hflag:ν.vars "separator.active"< B:=by rw [p1.1]; split_ifs <;> omega
  have hc:(Cond.eq (.var "separator.active") (.lit 1)).evalB B ν=
      some (decide ((if 3*R.card≤2*n then 0 else 1)=1)):=
    evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.1.symm,hflag⟩) (evalB_lit (by omega))
  have hb:∃ μ,Run B (branch body) ν μ (K+34)∧ μ.vars "separator.i"=i∧
      ∃ cs' R',State Q cut start (i+1) μ cs' R':=by
    by_cases hsmall:3*R.card≤2*n
    · have rb:Run B (branch body) ν ν (K+34):=
        (Run.ite_false (c:=.seq body NativeCutRecords.command) (by simpa [hsmall] using hc) Run.skip).mono (by simp [Cond.size,Expr.size] <;> omega)
      refine ⟨ν,rb,hin,cs,R,⟨sn.context,?_,?_,sn.last,sn.remaining,sn.separator,sn.count,sn.prefix_words,sn.position,sn.bitroom,sn.cutroom⟩⟩
      · have hh:=sn.length_le; dsimp [i]; omega
      · exact NativeCutTrace.append_stop cut i R hsmall cs (cuts cut n start) sn.suffix
    · obtain ⟨μ,r2,p2⟩:=hbody R hsmall ν ⟨sn.context,sn.remaining⟩
      have sm:=state_frame r2 sn p2.1 hvars harray
      obtain ⟨ρ,r3,p3⟩:=NativeCutRecords.command_spec B cs (cut R).1 (cut R).2
        (by omega) hm μ
        ⟨p2.2.1,p2.2.2,sm.separator,sm.count,sm.prefix_words,sm.position,
          by have hh:=sm.cutroom; omega⟩
      have rb:Run B (branch body) ν ρ (K+34):=(Run.ite_true (d:=.skip)
        (by simpa [hsmall] using hc) (r2.seq r3)).mono (by simp [Cond.size,Expr.size] <;> omega)
      have hir:ρ.vars "separator.i"=i:=
        ((r2.seq r3).frame_var "separator.i" (by simp only [Com.wvars,List.mem_append,not_or]; exact ⟨hindex,by decide⟩)).trans hin
      refine ⟨ρ,rb,hir,cs++[cut R],(cut R).1\(cut R).2,
        ⟨hrecord r3 p2.1,?_,?_,?_,p3.1,p3.2.1,?_,p3.2.2.2.1,?_,?_,?_⟩⟩
      · simp only [List.length_append,List.length_singleton]; omega
      · exact NativeCutTrace.append_advance cut i hilt R hsmall cs (cuts cut n start) sm.suffix
      · exact (NativeCutTrace.remaining_snoc start cs (cut R).1 (cut R).2).symm
      · simpa only [List.length_append,List.length_singleton] using p3.2.2.1
      · simpa only [List.length_append,List.length_singleton] using p3.2.2.2.2
      · rw [RamFrames.run_array_length r3]; exact sm.bitroom
      · rw [RamFrames.run_array_length r3]; exact sm.cutroom
  obtain ⟨μ,r2,hiμ,cs',R',sm⟩:=hb
  let τ:=μ.setVar "separator.i" (i+1)
  have r3:Run B (.assign "separator.i" (.add (.var "separator.i") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i+1< B; dsimp [i]; omega))
  have st:=state_frame r3 sm (hset μ (i+1) sm.context) (by decide) (by decide)
  have hit:τ.vars "separator.i"=i+1:=by simp [τ]
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),⟨by rw [hit]; exact hlt,cs',R',by simpa only [hit] using st⟩,hit⟩

theorem command_spec {n:ℕ} (B K:ℕ) (Q:Env→ Prop)
    (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n)) (start:Finset (Fin n)) (body:Com)
    (hB:3*n+5< B) (hm:2^n< B)
    (horder:∀ σ,Q σ→ σ.vars "graph.n"=n)
    (hset:∀ σ s k,s∈["separator.i","separator.count","separator.position","separator.value"]→ Q σ→ Q (σ.setVar s k))
    (hcheck:∀ {σ τ:Env} {k:ℕ},Run B NativeCutTest.command σ τ k→ Q σ→ Q τ)
    (hrecord:∀ {σ τ:Env} {k:ℕ},Run B NativeCutRecords.command σ τ k→ Q σ→ Q τ)
    (hbody:∀ R:Finset (Fin n),¬3*R.card≤2*n→
      Spec B (fun σ => Q σ∧ σ.vars "separator.remaining"=mask R) body
        (fun _ τ => Q τ∧ τ.vars "cut.left"=mask (cut R).1∧ τ.vars "cut.right"=mask (cut R).2) K)
    (hvars:∀ s∈preserved,s∉body.wvars) (hindex:"separator.i"∉body.wvars)
    (harray:"separator.cuts"∉body.warrs):
    Spec B (fun σ => Q σ∧ σ.vars "separator.remaining"=mask start∧
      n≤(σ.arrs "subset.bits").length∧ 2*n≤(σ.arrs "separator.cuts").length) (command body)
      (fun _ τ => Q τ∧ τ.vars "separator.remaining"=mask (remaining start (cuts cut n start))∧
        τ.vars "separator.value"=mask (ComputedSeparators.separator (cuts cut n start))∧
        τ.vars "separator.count"=(cuts cut n start).length∧
        Prefix (NativeCutRecords.words (cuts cut n start)) "separator.cuts" τ∧
        τ.vars "separator.position"=2*(cuts cut n start).length) ((21*n+K+62)*n+12):=by
  have hstep:=step_spec B K Q cut start body hB hm horder
    (fun σ k h => hset σ "separator.i" k (by simp) h) hcheck hrecord hbody hvars hindex harray
  have hloop:=Spec.forRangeZero "separator.i" "graph.n" (Invariant Q cut start) n (21*n+K+58)
    (by omega) (fun _ h => h.1)
    (by intro σ h; obtain ⟨cs,R,hs⟩:=h.2; exact horder σ hs.context) hstep
  rintro σ ⟨hq,hR,hbits,hcuts⟩
  let σ1:=σ.setVar "separator.count" 0
  have r1:Run B (.assign "separator.count" (.lit 0)) σ σ1 2:=Run.assign (evalB_lit (by omega))
  let σ2:=σ1.setVar "separator.position" 0
  have r2:Run B (.assign "separator.position" (.lit 0)) σ1 σ2 2:=Run.assign (evalB_lit (by omega))
  let σ3:=σ2.setVar "separator.value" 0
  have r3:Run B (.assign "separator.value" (.lit 0)) σ2 σ3 2:=Run.assign (evalB_lit (by omega))
  have q1:Q σ1:=hset σ "separator.count" 0 (by simp) hq
  have q2:Q σ2:=hset σ1 "separator.position" 0 (by simp) q1
  have q3:Q σ3:=hset σ2 "separator.value" 0 (by simp) q2
  have r0:Run B (.assign "separator.i" (.lit 0)) σ3 (σ3.setVar "separator.i" 0) 2:=
    Run.assign (evalB_lit (by omega))
  have rr0:=r1.seq (r2.seq (r3.seq r0))
  have hinit:Invariant Q cut start (σ3.setVar "separator.i" 0):=by
    refine ⟨by simp,[],start,⟨hset σ3 "separator.i" 0 (by simp) q3,by simp,by simp,?_,?_,?_,?_,?_,?_,hbits,hcuts⟩⟩
    · simp [remaining]
    · exact (rr0.frame_var "separator.remaining" (by decide)).trans hR
    · rw [show ComputedSeparators.separator ([]:List (Finset (Fin n) × Finset (Fin n)))=∅ from rfl,mask_empty]
      exact (r0.frame_var "separator.value" (by decide)).trans (by simp only [σ3,vars_setVar,if_true])
    · change (σ3.setVar "separator.i" 0).vars "separator.count"=0
      exact ((r2.seq (r3.seq r0)).frame_var "separator.count" (by decide)).trans
        (by simp only [σ1,vars_setVar,if_true])
    · intro j hj
      change j<0 at hj
      omega
    · change (σ3.setVar "separator.i" 0).vars "separator.position"=0
      exact ((r3.seq r0).frame_var "separator.position" (by decide)).trans
        (by simp only [σ2,vars_setVar,if_true])
  obtain ⟨τ,r4,ht⟩:=hloop σ3 hinit
  obtain ⟨cs,R,hs⟩:=ht.1.2
  rw [ht.2] at hs
  have hcs:cs=cuts cut n start:=by simpa only [Nat.sub_self,cuts,List.append_nil] using hs.suffix
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by nlinarith only []),hs.context,?_,?_,?_,?_,?_⟩
  · rw [←hcs,←hs.last]; exact hs.remaining
  · simpa only [←hcs] using hs.separator
  · simpa only [←hcs] using hs.count
  · simpa only [←hcs] using hs.prefix_words
  · simpa only [←hcs] using hs.position

end Lax263307Proofs.NativeCutLoop

end

section

namespace Lax263307Proofs.NativeSeparatorProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs
open Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeUniformFlow
open scoped NNRat

theorem exists_program (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ (p:Lax808846.Ram.Program) (wp tp op:Polynomial ℕ) (coeff:List ℕ),
    (∀ z:ℕ,RamPolynomial.value coeff z=wp.eval z)∧
    ∀ (b n load k h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0),
    0< n→ 0< load→ (∀ v,Bounded (2^h) (x v:ℚ))→
    let H:=NativeLargeResources.heightExponent b n load k h
    ∀ w:ℕ,wordHeight n H p wp tp op≤ w→
    let cs:=cuts (ComputedSeparators.step f G x b load k) n Finset.univ
    Spec (2^w) (fun σ => Context G x b load k (spaceBound n H tp) σ∧
      σ.vars "separator.remaining"=NativeMasks.mask (Finset.univ:Finset (Fin n)))
      (command p coeff) (fun _ τ => Context G x b load k (spaceBound n H tp) τ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs)∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs)∧ τ.vars "separator.count"=cs.length∧
        Lax455465Proofs.RamVirtualState.Prefix (NativeCutRecords.words cs) "separator.cuts" τ∧
        τ.vars "separator.position"=2*cs.length) (timeBound n H p coeff tp):=by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,hcallback⟩:=NativeUniformFlow.exists_callback f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,?_⟩
  intro b n load k h G _ x hn hl hx
  try dsimp only
  let H:=NativeLargeResources.heightExponent b n load k h
  let Q:=Context G x b load k (spaceBound n H tp)
  let cut:=ComputedSeparators.step f G x b load k
  intro w hwidth
  try dsimp only
  have hh:n+30≤ H:=by dsimp [H,NativeLargeResources.heightExponent]; omega
  have hw:=hwidth
  dsimp only [wordHeight] at hw
  have hB:3*n+5<2^w:=NativeUniformWordGuards.scalar _ w (by
    have hs:3*n+5≤ shape n:=by dsimp [shape]; nlinarith only []
    omega)
  have hm:2^n<2^w:=Nat.pow_lt_pow_right (by decide) (by omega)
  have hspec:=NativeCutLoop.command_spec (2^w) (callbackTime n H p coeff tp) Q cut Finset.univ (callback p coeff)
    hB hm (fun _ hd => hd.order)
    (by
      intro σ s v hs hd
      apply set_var hd s v
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> decide)
    (fun rr hd => frame rr hd (by decide) (by decide) (by decide))
    (fun rr hd => frame rr hd (by decide) (by decide) (by decide))
    (fun R _ => hcallback b n load k h G x hn hl hx w hwidth R)
    (by
      intro s hs
      simp only [NativeCutLoop.preserved,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;>
        exact callback_variable p coeff _ (by decide) (by decide) (by decide) (by decide))
    (callback_variable p coeff _ (by decide) (by decide) (by decide) (by decide))
    (callback_array p coeff _ (by decide) (by decide) (by decide) (by decide))
  have hbits:n≤ spaceBound n H tp:=by dsimp [spaceBound]; omega
  have hcuts:2*n≤ spaceBound n H tp:=by
    dsimp [spaceBound,NativeSplitInput.wordLength]
    nlinarith only []
  rintro σ ⟨hd,hr⟩
  exact hspec σ ⟨hd,hr,hbits.trans (hd.room "subset.bits" (by simp [workspace])),
    hcuts.trans (hd.room "separator.cuts" (by simp [workspace]))⟩

end Lax263307Proofs.NativeSeparatorProgram

end

theorem solution:∀ (f:List Nat→ List Nat),
  Lax759944.RamPolytime.RamPolytime f→
    ∃ (p:Lax808846.Ram.Program) (wp:@Polynomial Nat Nat.instSemiring) (tp:@Polynomial Nat Nat.instSemiring) (op:
      @Polynomial Nat Nat.instSemiring) (coeff:List Nat),
      And
        (∀ (z:Nat),
          @Eq Nat (Lax455465Proofs.RamPolynomial.value coeff z) (@Polynomial.eval Nat Nat.instSemiring z wp))
        (∀ (b n load k h:Nat) (G:SimpleGraph (Fin n))
          [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x:Fin n→ NNRat),
          Nat.lt ((0:Nat)) n→
            Nat.lt ((0:Nat)) load→
              (∀ (v:Fin n),
                  Lax263307Proofs.NativeSignedArithmetic.Bounded
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) h)
                    (@NNRat.cast Rat Rat.instNNRatCast (x v)))→
                have H:=Lax263307Proofs.NativeLargeResources.heightExponent b n load k h;
                ∀ (w:Nat),
                  Nat.le (Lax263307Proofs.NativeUniformFlow.wordHeight n H p wp tp op) w→
                    have cs:=
                      @Lax263307.ComputedSeparators.cuts n (@Lax263307.ComputedSeparators.step n f G inst x b load k) n
                        (@Finset.univ (Fin n) (Fin.fintype n));
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And
                          (@Lax263307Proofs.NativeSeparatorContext.Context n G inst x b load k
                            (Lax263307Proofs.NativeUniformFlow.spaceBound n H tp) σ)
                          (@Eq Nat (σ.vars "separator.remaining")
                            (@Lax263307Proofs.NativeMasks.mask n (@Finset.univ (Fin n) (Fin.fintype n)))))
                      (Lax263307Proofs.NativeSeparatorProgram.command p coeff)
                      (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                        And
                          (@Lax263307Proofs.NativeSeparatorContext.Context n G inst x b load k
                            (Lax263307Proofs.NativeUniformFlow.spaceBound n H tp) τ)
                          (And
                            (@Eq Nat (τ.vars "separator.remaining")
                              (@Lax263307Proofs.NativeMasks.mask n
                                (@Lax263307.ComputedSeparators.remaining n (@Finset.univ (Fin n) (Fin.fintype n)) cs)))
                            (And
                              (@Eq Nat (τ.vars "separator.value")
                                (@Lax263307Proofs.NativeMasks.mask n (@Lax263307.ComputedSeparators.separator n cs)))
                              (And
                                (@Eq Nat (τ.vars "separator.count")
                                  (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))
                                (And
                                  (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeCutRecords.words n cs)
                                    "separator.cuts" τ)
                                  (@Eq Nat (τ.vars "separator.position")
                                    (Nat.mul
                                      ((2:Nat))
                                      (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))))))
                      (Lax263307Proofs.NativeSeparatorProgram.timeBound n H p coeff tp)):= @Lax263307Proofs.NativeSeparatorProgram.exists_program
