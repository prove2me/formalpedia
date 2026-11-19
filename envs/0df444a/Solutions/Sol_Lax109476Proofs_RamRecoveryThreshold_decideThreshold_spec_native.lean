-- Prove2me | solution 1 for Lax109476Proofs.RamRecoveryThreshold.decideThreshold_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:42:20.575212+00:00
-- url     : https://prove2.me/submissions/0d5abf15-07f2-4274-9e35-9c325d5f4ec5

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
import Theorems.Thm_Lax109476Proofs_RamStoredFeasibility_decideFeasible_condition_spec
import Theorems.Thm_Lax109476Proofs_RamRecoveryQuery_buildQuery_spec_native

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

namespace Lax109476Proofs.RamRecoveryQuery
end Lax109476Proofs.RamRecoveryQuery
theorem Lax109476Proofs.RamRecoveryQuery.buildQuery_spec:∀ (B M m n k:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat) (t:Rat)
  (hk:LT.lt k n),
  LE.le ((1:Nat)) M→
    LT.lt M B→
      LT.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd
                (HMul.hMul
                  (HAdd.hAdd
                    (HAdd.hAdd m
                      (HAdd.hAdd n n))
                    ((1:Nat)))
                  n)
                m)
              (HAdd.hAdd n n))
            ((4:Nat)))
          B→
        (∀ (i:Fin m) (j:Fin n),
            Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
          (∀ (i:Fin m),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i) M)→
            (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (x j) M)→
              Lax109476Proofs.RationalArithmeticBounds.Height t M→
                (∀ (j:Fin n),
                    @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                      (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamRecoveryData.Data m n P x k t σ)
                        (Lax109476Proofs.RamRecoveryQuery.Extent m n σ))
                    Lax109476Proofs.RamRecoveryQuery.buildQuery
                    (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamRecoveryData.Data m n P x k t τ)
                        (@Lax109476Proofs.RamStoredProgram.RepresentsProgram
                          (HAdd.hAdd
                            (HAdd.hAdd m
                              (HAdd.hAdd n n))
                            ((1:Nat)))
                          n
                          (@Lax109476Proofs.CoordinateOptimization.coordinateCut
                            (HAdd.hAdd m
                              (HAdd.hAdd n n))
                            n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) t)
                          τ))
                    (HAdd.hAdd
                      (HAdd.hAdd
                        (HAdd.hAdd
                          (HMul.hMul
                            ((142:Nat))
                            (HMul.hMul
                              (HAdd.hAdd
                                (HAdd.hAdd m
                                  (HAdd.hAdd n n))
                                ((1:Nat)))
                              n))
                          (HMul.hMul
                            ((138:Nat))
                            (HAdd.hAdd
                              (HAdd.hAdd m
                                (HAdd.hAdd n n))
                              ((1:Nat)))))
                        (HMul.hMul
                          ((33:Nat)) n))
                      ((106:Nat))):= @Lax109476Proofs.RamRecoveryQuery.buildQuery_spec_native

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

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

theorem Run.seq {B:ℕ} {c d:Com} {σ σ' σ'':Env} {K K':ℕ}
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):Run B (.seq c d) σ σ'' (K + K'):=by
  obtain ⟨k,hk,hbs⟩:=h
  obtain ⟨k',hk',hbs'⟩:=h'
  exact ⟨k + k',by omega, .seq hbs hbs'⟩

end Lax808846Proofs.Reasoning

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem size_le_self (a:ℕ):Nat.size a≤ a:=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))

end Lax109476Proofs.RationalSizeBounds

end

section

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_append (x y:List ℕ):bitSize (x ++ y)=bitSize x + bitSize y:=by
  simp [bitSize,encode]

theorem bitSize_cons (n:ℕ) (x:List ℕ):
    bitSize (n::x)=Nat.size n + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len]
  omega

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_flatMap {α:Type*} (x:List α) (f:α→ List ℕ):
    bitSize (x.flatMap f)=(x.map (fun a => bitSize (f a))).sum:=by
  induction x with
  | nil => rfl
  | cons a x ih => simp only [List.flatMap_cons,bitSize_append,
      List.map_cons,List.sum_cons,ih]

theorem rational_size_upper (q:ℚ):
    bitSize (encodeRational q)≤ 4 + Nat.size q.num.natAbs + Nat.size q.den:=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  split_ifs <;> norm_num [Nat.size] <;> omega

theorem vector_size {n:ℕ} (x:Fin n→ ℚ):
    bitSize (encodeVector x)=∑ j,bitSize (encodeRational (x j)):=by
  rw [encodeVector,bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
  rfl

theorem bounded_vector_size {n:ℕ} (x:Fin n→ ℚ) (B:ℕ)
    (hx:∀ j, (x j).num.natAbs≤ B∧ (x j).den≤ B):
    bitSize (encodeVector x)≤ n * (4 + 2 * Nat.size B):=by
  rw [vector_size]
  calc
    _≤ ∑ _j:Fin n, (4 + 2 * Nat.size B):=by
      apply Finset.sum_le_sum
      intro j _
      have hn:=Nat.size_le_size (hx j).1
      have hd:=Nat.size_le_size (hx j).2
      have hu:=rational_size_upper (x j)
      omega
    _=_:=by simp

theorem program_size {m n:ℕ} (P:Program ℚ m n):
    bitSize (encodeProgram P)=Nat.size m + Nat.size n + 2 +
      (∑ i, ∑ j,bitSize (encodeRational (P.A i j))) +
      (∑ i,bitSize (encodeRational (P.b i))) +
      (∑ j,bitSize (encodeRational (P.c j))):=by
  have hmatrix:bitSize ((List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap
      encodeRational)=∑ i, ∑ j,bitSize (encodeRational (P.A i j)):=by
    rw [List.flatten_eq_flatMap,List.flatMap_assoc,bitSize_flatMap,
      List.map_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    change bitSize ((List.ofFn (P.A i)).flatMap encodeRational)=_
    rw [bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
    rfl
  unfold encodeProgram
  rw [bitSize_append,bitSize_append,bitSize_append,bitSize_cons,
    bitSize_cons,bitSize_nil,vector_size,vector_size,hmatrix]
  omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

end Lax109476Proofs.EllipsoidSearch

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

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

theorem height_neg (q:ℚ) (B:ℕ) (hq:Height q B):Height (-q) B:=by
  simpa only [Height,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using hq

theorem height_encoding (q:ℚ) (B:ℕ) (hq:Height q B):
    bitSize (encodeRational q)≤ 4 + 2 * B.size:=by
  have hn:=Nat.size_le_size hq.1
  have hd:=Nat.size_le_size hq.2
  have he:=EncodingSize.rational_size_upper q
  omega

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

open Lax808846.Ram Lax808846Proofs.Machine

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

namespace Fill

namespace Demo

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax109476Proofs.RamScalarFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem value_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (q:ℚ) (h:Value name q σ)
    (hs:name ++ ".s" ∉ c.wvars) (hn:name ++ ".n" ∉ c.wvars)
    (hd:name ++ ".d" ∉ c.wvars):Value name q τ:=by
  simpa only [Value,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

end Lax109476Proofs.RamScalarFrame

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

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RecoveryQueryEntries

open Lax109476.LinearProgram CoordinateOptimization LexicographicMinima RationalArithmeticBounds

theorem entry_eq {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (hk:k < n)
    (t:ℚ) (i:Fin ((m + (n + n)) + 1)) (j:Fin n):
    entry P k i j=(coordinateCut (fixedPrefix P x k) ⟨k,hk⟩ t).A i j:=by
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp [-Fin.natAdd_eq_addNat,entry,coordinateCut,fixedPrefix,i.isLt]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hi:m + i.val < m + n:=by omega
        by_cases hik:i.val < k <;> by_cases hji:j.val=i.val <;>
          simp [-Fin.natAdd_eq_addNat,entry,coordinateCut,fixedPrefix,hi,Fin.ext_iff,hik,hji]
      · intro i
        have hi:¬ m + (n + i.val) < m + n:=by omega
        have hi':m + (n + i.val) < m + n + n:=by omega
        by_cases hik:i.val < k <;> by_cases hji:j.val=i.val <;>
          simp [-Fin.natAdd_eq_addNat,entry,coordinateCut,fixedPrefix,hi,hi',Fin.ext_iff,Nat.add_assoc,hik,hji]
  · intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat,entry,coordinateCut,fixedPrefix,Fin.ext_iff,Nat.add_assoc]

theorem bound_eq {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (hk:k < n)
    (t:ℚ) (i:Fin ((m + (n + n)) + 1)):
    bound P x k t i=(coordinateCut (fixedPrefix P x k) ⟨k,hk⟩ t).b i:=by
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp [-Fin.natAdd_eq_addNat,bound,coordinateCut,fixedPrefix,i.isLt]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hi:m + i.val < m + n:=by omega
        simp [-Fin.natAdd_eq_addNat,bound,coordinateCut,fixedPrefix,hi]
      · intro i
        have hi:¬ m + (n + i.val) < m + n:=by omega
        have hi':m + (n + i.val) < m + n + n:=by omega
        simp [-Fin.natAdd_eq_addNat,bound,coordinateCut,fixedPrefix,hi,hi',Nat.add_assoc]
  · intro i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat,bound,coordinateCut,fixedPrefix,Nat.add_assoc]

theorem entry_height {m n:ℕ} (P:Program ℚ m n) (k M:ℕ) (hM:1≤ M)
    (hA:∀ i j,Height (P.A i j) M) (i:Fin ((m + (n + n)) + 1)) (j:Fin n):
    Height (entry P k i j) M:=by
  unfold entry
  split_ifs
  · exact hA _ _
  all_goals simp_all [Height]

theorem bound_height {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k M:ℕ) (t:ℚ)
    (hM:1≤ M) (hb:∀ i,Height (P.b i) M) (hx:∀ j,Height (x j) M) (ht:Height t M)
    (i:Fin ((m + (n + n)) + 1)):Height (bound P x k t i) M:=by
  unfold bound
  split_ifs
  · exact hb _
  · exact hx _
  · exact height_mono _ height_zero hM
  · exact height_neg _ _ (hx _)
  · exact height_mono _ height_zero hM
  · exact ht

end Lax109476Proofs.RecoveryQueryEntries

end

section

namespace Lax109476Proofs.RamRecoveryData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamScalarFrame

def fields:List String:= ["point.m", "point.n", "point.k", "bisect.mid.s", "bisect.mid.n", "bisect.mid.d"]

def arrays:List String:= ["point.A", "point.b", "point.x"]

theorem data_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (t:ℚ) (hσ:Data P x k t σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):Data P x k t τ:=by
  rcases hσ with ⟨hA,hb,hx,hm,hn,hk,ht⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hx hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hk,
    value_frame hr "bisect.mid" t ht (hf _ (by simp [fields])) (hf _ (by simp [fields])) (hf _ (by simp [fields]))⟩

end Lax109476Proofs.RamRecoveryData

end

section

namespace Lax109476Proofs.RamRecoveryQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamRecoveryData RationalArithmeticBounds RamStoredProgram

theorem extent_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    (m n:ℕ) (hσ:Extent m n σ):Extent m n τ:=
  ⟨RamAdvanceState.extents_of_run hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2⟩

end Lax109476Proofs.RamRecoveryQuery

end

section

open scoped BigOperators

namespace Lax109476Proofs.RecoveryArithmeticBounds

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open PointRecovery CoordinateOptimization RationalArithmeticBounds
open BinaryOptimizationBounds LexicographicMinima EncodingSize

theorem program_height_size {m n:ℕ} (P:Program ℚ m n) (B:ℕ)
    (hA:∀ i j,Height (P.A i j) B) (hb:∀ i,Height (P.b i) B)
    (hc:∀ j,Height (P.c j) B):
    bitSize (encodeProgram P)≤ m + n + 2 + (m * n + m + n) * (4 + 2 * B.size):=by
  have hsA:(∑ i, ∑ j,bitSize (encodeRational (P.A i j)))≤ m * n * (4 + 2 * B.size):=by
    calc
      _≤ ∑ _i:Fin m, ∑ _j:Fin n, (4 + 2 * B.size):=by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => height_encoding _ B (hA i j)))
      _=_:=by simp; ring
  have hsb:=bounded_vector_size P.b B hb
  have hsc:=bounded_vector_size P.c B hc
  have hm:=RationalSizeBounds.size_le_self m
  have hn:=RationalSizeBounds.size_le_self n
  rw [program_size]
  rw [vector_size] at hsb hsc
  nlinarith

end Lax109476Proofs.RecoveryArithmeticBounds

end

section

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem workspace_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (m n:ℕ) (h:RamFeasibilityQuery.Workspace m n σ):RamFeasibilityQuery.Workspace m n τ:=by
  rcases h with ⟨hqA,hqb,hpA,hpb,hrows,hrhs,hcenter,hshape,hw,hnormal⟩
  exact ⟨RamAdvanceState.extents_of_run hr _ _ hqA,RamAdvanceState.extents_of_run hr _ _ hqb,
    RamAdvanceState.extents_of_run hr _ _ hpA,RamAdvanceState.extents_of_run hr _ _ hpb,
    RamAdvanceState.extents_of_run hr _ _ hrows,RamAdvanceState.extents_of_run hr _ _ hrhs,
    RamAdvanceState.extents_of_run hr _ _ hcenter,RamAdvanceState.extents_of_run hr _ _ hshape,
    RamAdvanceState.workspace_of_run hr _ hw,RamAdvanceState.extents_of_run hr _ _ hnormal⟩

end Lax109476Proofs.RamStoredFeasibility

end

section

namespace Lax109476Proofs.RamStoredFeasibilityBounds

theorem wordWidth_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.wordWidth L≤ RamStoredFeasibility.wordWidth S:=by
  unfold RamStoredFeasibility.wordWidth RamRationalFeasibility.wordWidth
    RamPaddedFeasibility.wordWidth RamIntegerFeasibility.wordWidth RamFeasibilitySetup.wordWidth
    RamFeasibilityScaleBounds.wordWidth RamSearchBounds.wordWidth RamEllipsoidBitBounds.wordWidth
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamTrajectoryBounds.stateBits RamNormalizedBounds.coefficientBits
    RamIntegerFeasibility.iterationBound RamDecoder.wordWidth
  gcongr

set_option maxRecDepth 30000 in
theorem instructionBound_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.instructionBound L≤ RamStoredFeasibility.instructionBound S:=by
  unfold RamStoredFeasibility.instructionBound RamRationalFeasibility.instructionBound
    RamPaddedFeasibility.instructionBound RamIntegerFeasibility.uniformInstructionBound
    RamFeasibilitySetup.instructionBound RamFeasibilityParameters.instructionBound
    RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamNormalizedBounds.coefficientBits RamIntegerFeasibility.iterationBound
  dsimp only
  gcongr

end Lax109476Proofs.RamStoredFeasibilityBounds

end

section

namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

theorem state_of_data {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (t:ℚ)
    (σ:Env) (h:RamRecoveryData.Data P x k t σ):State P x k σ:=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

theorem data_of_state {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (t:ℚ)
    (σ:Env) (h:State P x k σ) (ht:Value "bisect.mid" t σ):
    RamRecoveryData.Data P x k t σ:=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,ht⟩

theorem workspace_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    (m n:ℕ) (hσ:Workspace m n σ):Workspace m n τ:=
  ⟨RamRecoveryQuery.extent_frame hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2.2.1,
    RamStoredFeasibility.workspace_of_run hr _ _ hσ.2.2.2.2⟩

theorem query_size_bound {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k M:ℕ)
    (hk:k < n) (t:ℚ) (hM:1≤ M) (hA:∀ i j,Height (P.A i j) M)
    (hb:∀ i,Height (P.b i) M) (hx:∀ j,Height (x j) M) (ht:Height t M)
    (hc:∀ j,P.c j=0):
    bitSize (encodeProgram (CoordinateOptimization.coordinateCut
      (LexicographicMinima.fixedPrefix P x k) ⟨k,hk⟩ t))≤ sizeBound m n M:=by
  apply RecoveryArithmeticBounds.program_height_size
  · intro i j
    rw [← RecoveryQueryEntries.entry_eq P x k hk t i j]
    exact RecoveryQueryEntries.entry_height P k M hM hA i j
  · intro i
    rw [← RecoveryQueryEntries.bound_eq P x k hk t i]
    exact RecoveryQueryEntries.bound_height P x k M t hM hb hx ht i
  · intro j
    change Height (P.c j) M
    rw [hc j]
    exact height_mono 0 height_zero (by omega)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem decideThreshold_spec (m n k M w:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ) (t:ℚ)
    (hk:k < n) (hM:1≤ M) (hMB:M < 2 ^ w)
    (hB:((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w)
    (hw:RamStoredFeasibility.wordWidth (sizeBound m n M)≤ w)
    (hA:∀ i j,Height (P.A i j) M) (hb:∀ i,Height (P.b i) M)
    (hx:∀ j,Height (x j) M) (ht:Height t M) (hc:∀ j,P.c j=0):
    Spec (2 ^ w) (fun σ => Persistent P x k σ∧ Value "bisect.mid" t σ) decideThreshold
      (fun _ τ => Persistent P x k τ∧ RamBisectionCommit.condition.evalB (2 ^ w) τ =
        some (RationalFeasibilityDecision.feasible
          (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k,hk⟩ t)))
      (instructionBound m n M):=by
  let C:=CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k,hk⟩ t
  have hsize:=query_size_bound P x k M hk t hM hA hb hx ht hc
  have hwidth:RamStoredFeasibility.wordWidth (bitSize (encodeProgram C))≤ w:=
    (RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans hw
  rintro σ ⟨⟨hσState,hσWork⟩,hσt⟩
  obtain ⟨τ,hr₁,hτData,hτC⟩:=RamRecoveryQuery.buildQuery_spec (2 ^ w) M m n k P x t hk hM hMB hB
    hA hb hx ht hc σ ⟨data_of_state P x k t σ hσState hσt,hσWork.1⟩
  have hτWork:=workspace_frame hr₁ m n hσWork
  obtain ⟨υ,hr₂,hυBool⟩:=RamStoredFeasibility.decideFeasible_condition_spec _ _ C w hwidth τ
    ⟨hτC,hτWork.2.1,hτWork.2.2.1,hτWork.2.2.2.1,hτWork.2.2.2.2⟩
  have hυData:=RamRecoveryData.data_frame hr₂ P x k t hτData
    (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha s hs; simp [RamRecoveryData.arrays] at ha; simp [RamCopy.suffixes] at hs;
        rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide)
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, ⟨state_of_data P x k t υ hυData,
    workspace_frame hr₂ m n hτWork⟩,hυBool⟩
  exact Nat.add_le_add_left (RamStoredFeasibilityBounds.instructionBound_monotone hsize) _

end Lax109476Proofs.RamRecoveryThreshold

end

theorem solution:∀ (m n k M w:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat) (t:Rat)
  (hk:Nat.lt k n),
  Nat.le ((1:Nat)) M→
    Nat.lt M
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)→
      Nat.lt
          (Nat.add
            (Nat.add
              (Nat.add
                (Nat.mul
                  (Nat.add
                    (Nat.add m
                      (Nat.add n n))
                    ((1:Nat)))
                  n)
                m)
              (Nat.add n n))
            ((4:Nat)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) w)→
        Nat.le
            (Lax109476Proofs.RamStoredFeasibility.wordWidth (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n M)) w→
          (∀ (i:Fin m) (j:Fin n),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
            (∀ (i:Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i) M)→
              (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (x j) M)→
                Lax109476Proofs.RationalArithmeticBounds.Height t M→
                  (∀ (j:Fin n),
                      @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k σ)
                          (Lax109476Proofs.RamRationalScalars.Value "bisect.mid" t σ))
                      Lax109476Proofs.RamRecoveryThreshold.decideThreshold
                      (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                        And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k τ)
                          (@Eq (Option Bool)
                            (Lax808846Proofs.Imp.Cond.evalB
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                ((2:Nat)) w)
                              Lax109476Proofs.RamBisectionCommit.condition τ)
                            (@Option.some Bool
                              (@Lax109476Proofs.RationalFeasibilityDecision.feasible
                                (Nat.add
                                  (Nat.add m
                                    (Nat.add n n))
                                  ((1:Nat)))
                                n
                                (@Lax109476Proofs.CoordinateOptimization.coordinateCut
                                  (Nat.add m
                                    (Nat.add n n))
                                  n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) t)))))
                      (Lax109476Proofs.RamRecoveryThreshold.instructionBound m n M):= @Lax109476Proofs.RamRecoveryThreshold.decideThreshold_spec
