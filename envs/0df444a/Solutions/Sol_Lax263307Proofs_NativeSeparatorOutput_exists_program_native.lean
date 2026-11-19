-- Prove2me | solution 1 for Lax263307Proofs.NativeSeparatorOutput.exists_program_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:28:28.956482+00:00
-- url     : https://prove2.me/submissions/0a514428-31cd-4b99-850d-d78a3abc822d

import Mathlib.Tactic
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax263307Proofs_NativeSeparatorProgram_exists_program_native

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

namespace Lax263307Proofs.NativeSeparatorProgram
end Lax263307Proofs.NativeSeparatorProgram
theorem Lax263307Proofs.NativeSeparatorProgram.exists_program:∀ (f:List Nat→ List Nat),
  Lax759944.RamPolytime.RamPolytime f→
    ∃ (p:Lax808846.Ram.Program) (wp:@Polynomial Nat Nat.instSemiring) (tp:@Polynomial Nat Nat.instSemiring) (op:
      @Polynomial Nat Nat.instSemiring) (coeff:List Nat),
      And
        (∀ (z:Nat),
          @Eq Nat (Lax455465Proofs.RamPolynomial.value coeff z) (@Polynomial.eval Nat Nat.instSemiring z wp))
        (∀ (b n load k h:Nat) (G:SimpleGraph (Fin n))
          [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x:Fin n→ NNRat),
          LT.lt ((0:Nat)) n→
            LT.lt ((0:Nat)) load→
              (∀ (v:Fin n),
                  Lax263307Proofs.NativeSignedArithmetic.Bounded
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) h)
                    (@NNRat.cast Rat Rat.instNNRatCast (x v)))→
                have H:=Lax263307Proofs.NativeLargeResources.heightExponent b n load k h;
                ∀ (w:Nat),
                  LE.le (Lax263307Proofs.NativeUniformFlow.wordHeight n H p wp tp op) w→
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
                                    (HMul.hMul
                                      ((2:Nat))
                                      (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))))))
                      (Lax263307Proofs.NativeSeparatorProgram.timeBound n H p coeff tp)):= @Lax263307Proofs.NativeSeparatorProgram.exists_program_native

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

theorem eval_var (B:ℕ) (σ:Env) (x:String) (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=evalB_var h

theorem eval_and (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.land m n < B):
    (Expr.bin .and e f).evalB B σ=some (Nat.land m n):=evalB_bin he hf h

theorem eval_xor (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:Nat.xor m n < B):
    (Expr.bin .xor e f).evalB B σ=some (Nat.xor m n):=evalB_bin he hf h

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

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

end RunStep

end Lax808846Proofs.Reasoning
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

end Lax455465Proofs.RamFrames

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

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

end Lax455465Proofs.RamLpRationalRead

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

namespace Lax263307Proofs.NativeTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Invariant (array:String) (P:Env→ Prop) (xs:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "fill.i"≤ xs.length∧
  xs.length≤(σ.arrs array).length∧ Prefix (xs.take (σ.vars "fill.i")) array σ

theorem command_spec (B:ℕ) (xs:List ℕ) (array:String) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:xs.length+1< B) (hwords:∀ x∈xs,x< B)
    (hri:"fill.i"∉read.wvars) (hrl:"fill.length"∉read.wvars) (hra:array∉read.warrs)
    (hinit:∀ σ,P σ→ P (σ.setVar "fill.i" 0))
    (hwrite:∀ σ τ,Run B (append array) σ τ 7→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ∧ τ.vars "fill.value"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "fill.length"=xs.length∧ xs.length≤(σ.arrs array).length)
      (command array read) (fun _ τ => P τ∧ Prefix xs array τ) ((K+11)*xs.length+6):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant array P xs σ∧ σ.vars "fill.i"< xs.length)
      (.seq read (append array))
      (fun σ τ => Invariant array P xs τ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+7):=by
    rintro σ ⟨⟨hPσ,hlen,hle,hroom,hprefix⟩,hlt⟩
    let i:=σ.vars "fill.i"
    have htlen:(xs.take i).length=i:=by rw [List.length_take,Nat.min_eq_left hle]
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hPσ,rfl⟩
    have hiν:ν.vars "fill.i"=i:=r1.frame_var "fill.i" hri
    obtain ⟨τ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B array "fill.i" (xs.take i) xs[i]
      (.var "fill.value") h1 (by rw [htlen]; omega) ν
      ⟨by simpa only [Prefix,r1.frame_arr array hra] using hprefix,by rwa [htlen],
        by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
        by rw [evalB_var_iff]; exact ⟨p1.2.symm,p1.2 ▸ hwords _ (List.getElem_mem hlt)⟩⟩
    have r2':Run B (append array) ν τ 7:=r2
    have ht:τ.vars "fill.i"=i+1:=by simpa only [htlen] using p2.2
    have rr:=r1.seq r2'
    refine ⟨τ,rr,⟨hwrite ν τ r2' p1.1,?_,by rw [ht]; omega,?_,?_⟩,ht⟩
    · exact (r2'.frame_var "fill.length" (by simp [append,Lax455465Proofs.RamWordBuffer.append,Com.wvars])).trans
        ((r1.frame_var "fill.length" hrl).trans hlen)
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,List.take_succ_eq_append_getElem hlt]
      exact p2.1
  have hloop:=Spec.forRangeZero "fill.i" "fill.length" (Invariant array P xs) xs.length (K+7)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hroom⟩
  have hi:Invariant array P xs (σ.setVar "fill.i" 0):=by
    refine ⟨hinit σ hP,?_,by simp,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_⟩
  simpa only [p.2,List.take_length] using p.1.2.2.2.2

end Lax263307Proofs.NativeTabulate

end

section

namespace Lax263307Proofs.NativeFullSetMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks

def Invariant (n:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "separator.init.i"≤ n∧
    σ.vars "separator.remaining"=mask (initialSet (Finset.univ:Finset (Fin n)) (σ.vars "separator.init.i"))

theorem step_spec (B n:ℕ) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant n σ∧ σ.vars "separator.init.i"< n) step
      (fun σ τ => Invariant n τ∧ τ.vars "separator.init.i"=σ.vars "separator.init.i"+1) 10:=by
  rintro σ ⟨⟨hn,hle,hmask⟩,hlt⟩
  let i:=σ.vars "separator.init.i"
  let U:Finset (Fin n):=Finset.univ
  have hiB:i< B:=by dsimp [i]; omega
  have hp:2^i< B:=(Nat.pow_lt_pow_right (by decide:1<2) hlt).trans hm
  have hprev:=(mask_bound (initialSet U i)).trans hm
  have hnext:=(mask_bound (initialSet U (i+1))).trans hm
  have hu:Nat.lor (mask (initialSet U i)) (2^i)=mask (initialSet U (i+1)):=by
    simpa only [U,Finset.mem_univ,if_true,one_mul] using prefix_step U i hlt
  have he:=evalB_bin (op:=.or)
    (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hprev⟩)
    (evalB_bin (op:=.shiftl) (evalB_lit (show 1< B by omega)) (evalB_var hiB) (by change 1*2^i< B; simpa only [one_mul] using hp))
    (by change Nat.lor (mask (initialSet U i)) (1*2^i)< B; rw [one_mul,hu]; exact hnext)
  have he':(Expr.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i"))).evalB B σ=
      some (mask (initialSet U (i+1))):=by
    simp only [Bop.apply_or,Bop.apply_shiftl,one_mul] at he
    change (Expr.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i"))).evalB B σ=
      some (Nat.lor (mask (initialSet U i)) (2^i)) at he
    exact he.trans (congrArg some hu)
  let ν:=σ.setVar "separator.remaining" (mask (initialSet U (i+1)))
  have r1:Run B (.assign "separator.remaining"
      (.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i")))) σ ν 6:=Run.assign he'
  have hiν:ν.vars "separator.init.i"=i:=r1.frame_var "separator.init.i" (by decide)
  let τ:=ν.setVar "separator.init.i" (i+1)
  have r2:Run B (.assign "separator.init.i" (.add (.var "separator.init.i") (.lit 1))) ν τ 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i+1< B; dsimp [i]; omega))
  have rr:=r1.seq r2
  have hit:τ.vars "separator.init.i"=i+1:=by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩,hit⟩
  · rw [hit]; exact hlt
  · rw [hit]
    exact (r2.frame_var "separator.remaining" (by decide)).trans (by simp only [ν,vars_setVar,if_true] <;> rfl)

theorem command_spec (B n:ℕ) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "separator.remaining"=mask (Finset.univ:Finset (Fin n))) (14*n+8):=by
  have hloop:=Spec.forRangeZero "separator.init.i" "graph.n" (Invariant n) n 10 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B n hB hm)
  intro σ hn
  let ν:=σ.setVar "separator.remaining" 0
  have r1:Run B (.assign "separator.remaining" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have r0:Run B (.assign "separator.init.i" (.lit 0)) ν (ν.setVar "separator.init.i" 0) 2:=
    Run.assign (evalB_lit (by omega))
  have hinit:Invariant n (ν.setVar "separator.init.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · exact ((r1.seq r0).frame_var "graph.n" (by decide)).trans hn
    · change (ν.setVar "separator.init.i" 0).vars "separator.remaining"=mask (initialSet (Finset.univ:Finset (Fin n)) 0)
      rw [prefix_zero,mask_empty]
      exact (r0.frame_var "separator.remaining" (by decide)).trans (by simp only [ν,vars_setVar,if_true] <;> rfl)
  obtain ⟨τ,r2,ht⟩:=hloop ν hinit
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [ht.2,prefix_full] using ht.1.2.2⟩

end Lax263307Proofs.NativeFullSetMask

end

section

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):ℕ:=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem step {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:Fin r):
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1):=by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h:i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

end Lax263307Proofs.NativeShoreMasks

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

end Lax263307Proofs.NativeSeparatorContext

end

section

namespace Lax263307Proofs.NativeUniformWordGuards

theorem scalar (v w:ℕ) (h:v≤ w):v<2^w:=h.trans_lt Nat.lt_two_pow_self

end Lax263307Proofs.NativeUniformWordGuards

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

end Lax263307Proofs.NativeCutRecords

end

section

namespace Lax263307Proofs.NativeCutPairRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks

theorem pair_getD {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (i:ℕ):
    (NativeCutRecords.words cs).getD (2*i) 0=mask (cs.getD i (∅,∅)).1∧
    (NativeCutRecords.words cs).getD (2*i+1) 0=mask (cs.getD i (∅,∅)).2:=by
  induction cs generalizing i with
  | nil => simp [NativeCutRecords.words,mask_empty]
  | cons s cs ih =>
    cases i with
    | zero => simp [NativeCutRecords.words]
    | succ i => simpa [NativeCutRecords.words,Nat.mul_succ,Nat.add_assoc] using ih i

theorem command_spec {n:ℕ} (B:ℕ) (cs:List (Finset (Fin n) × Finset (Fin n)))
    (i:ℕ) (hi:i< cs.length) (hB:2*cs.length+4< B) (hm:2^n< B):
    Spec B (fun σ => Prefix (NativeCutRecords.words cs) "separator.cuts" σ∧ σ.vars "piece.i"=i) command
      (fun _ τ => τ.vars "fill.value"=mask (cs[i].2\cs[i].1)) 18:=by
  have hlen:=NativeCutRecords.length_words cs
  have h0:2*i<(NativeCutRecords.words cs).length:=by omega
  have h1:2*i+1<(NativeCutRecords.words cs).length:=by omega
  have he:=pair_getD cs i
  simp only [List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,
    Option.getD_some] at he
  rintro σ ⟨hp,hs⟩
  have hg0:=hp (2*i) h0
  have hg1:=hp (2*i+1) h1
  rw [he.1] at hg0
  rw [he.2] at hg1
  have hiB:i< B:=by omega
  let ν:=σ.setVar "piece.left" (mask cs[i].1)
  have r1:Run B (.assign "piece.left" (.get "separator.cuts" (.mul (.lit 2) (.var "piece.i")))) σ ν 5:=
    Run.assign (evalB_get (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩) (by change 2*i< B; omega)) hg0 ((mask_bound _).trans hm))
  let μ:=ν.setVar "piece.right" (mask cs[i].2)
  have hgν:(ν.arrs "separator.cuts")[2*i+1]?=some (mask cs[i].2):=hg1
  have r2:Run B (.assign "piece.right" (.get "separator.cuts" (.add (.mul (.lit 2) (.var "piece.i")) (.lit 1)))) ν μ 7:=
    Run.assign (evalB_get (evalB_bin (op:=.add) (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using And.intro hs.symm (hs ▸ hiB))
      (by change 2*i< B; omega)) (evalB_lit (by omega)) (by change 2*i+1< B; omega)) hgν ((mask_bound _).trans hm))
  have ht:=mask_bound (cs[i].2\cs[i].1)
  have hinter:=mask_bound (cs[i].2∩cs[i].1)
  have hlast:Spec B (fun σ => σ.vars "piece.left"=mask cs[i].1∧ σ.vars "piece.right"=mask cs[i].2)
      (.assign "fill.value" (.xor (.var "piece.right") (.and (.var "piece.right") (.var "piece.left"))))
      (fun _ τ => τ.vars "fill.value"=mask (cs[i].2\cs[i].1)) 6:=by
    have ha:=(mask_bound cs[i].1).trans hm
    have hb:=(mask_bound cs[i].2).trans hm
    have hc:=hinter.trans hm
    have hd:=ht.trans hm
    simp only [NativeSetMasks.inter,NativeSetMasks.sdiff] at hc hd ⊢
    (expose_names;
      (refine fun (σ_1:Env) (a:And (@Eq Nat (Env.vars σ_1 "piece.left") (@mask n (@Prod.fst (Finset (Fin n)) (Finset (Fin n)) (@getElem (List (Prod (Finset (Fin n)) (Finset (Fin n)))) Nat (Prod (Finset (Fin n)) (Finset (Fin n))) (fun (as:List (Prod (Finset (Fin n)) (Finset (Fin n)))) (i_1:Nat) => Nat.lt i_1 (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) as)) (@List.instGetElemNatLtLength (Prod (Finset (Fin n)) (Finset (Fin n)))) cs i hi)))) (@Eq Nat (Env.vars σ_1 "piece.right") (@mask n (@Prod.snd (Finset (Fin n)) (Finset (Fin n)) (@getElem (List (Prod (Finset (Fin n)) (Finset (Fin n)))) Nat (Prod (Finset (Fin n)) (Finset (Fin n))) (fun (as:List (Prod (Finset (Fin n)) (Finset (Fin n)))) (i_1:Nat) => Nat.lt i_1 (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) as)) (@List.instGetElemNatLtLength (Prod (Finset (Fin n)) (Finset (Fin n)))) cs i hi))))) => let c0:Type:=Prod (Finset (Fin n)) (Finset (Fin n)); let c1:Type:=List c0; let c2:c0:= @getElem c1 Nat c0 (fun (as:c1) (i_1:Nat) => Nat.lt i_1 (@List.length c0 as)) (@List.instGetElemNatLtLength c0) cs i hi; let c3:Nat:= @mask n (@Prod.fst (Finset (Fin n)) (Finset (Fin n)) c2); let c4:Prop:= @Eq Nat (Env.vars σ_1 "piece.left") c3; let c5:Nat:= @mask n (@Prod.snd (Finset (Fin n)) (Finset (Fin n)) c2); let c6:Prop:= @Eq Nat (Env.vars σ_1 "piece.right") c5; let c7:Expr:=Expr.xor (Expr.var "piece.right") (Expr.and (Expr.var "piece.right") (Expr.var "piece.left")); let c8:Com:=Com.assign "fill.value" c7; let c9:Env→ Nat→ Prop:=Run B c8 σ_1; let c10:Nat:=Nat.xor c5 (Nat.land c5 c3); let c11:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "fill.value") c10) σ_1; let c12:Env→ Prop:=fun (σ':Env) => And (c9 σ' ((6:Nat))) (c11 σ'); let c13:Nat:=Nat.land (Env.vars σ_1 "piece.right") (Env.vars σ_1 "piece.left"); let c14:Nat:=Nat.xor (Env.vars σ_1 "piece.right") c13; let c15:Env:=Env.setVar σ_1 "fill.value" c14; @And.casesOn c4 c6 (fun (x:And c4 c6) => @Exists Env c12) a fun (left:c4) (right:c6) => @Exists.intro Env c12 c15 (@And.intro (c9 c15 ((6:Nat))) (c11 c15) (RunStep.mono B c8 σ_1 c15 (Nat.add ((1:Nat)) (Expr.size c7)) ((6:Nat)) (RunStep.assign B σ_1 "fill.value" c7 c14 (RunStep.eval_xor B σ_1 (Expr.var "piece.right") (Expr.and (Expr.var "piece.right") (Expr.var "piece.left")) (Env.vars σ_1 "piece.right") c13 (RunStep.eval_var B σ_1 "piece.right" (?nAX_g8901_0_0_0)) (RunStep.eval_and B σ_1 (Expr.var "piece.right") (Expr.var "piece.left") (Env.vars σ_1 "piece.right") (Env.vars σ_1 "piece.left") (RunStep.eval_var B σ_1 "piece.right" (?nAX_g8901_0_0_1)) (RunStep.eval_var B σ_1 "piece.left" (?nAX_g8901_0_0_2)) ?_) ?_)) (?nAX_g8901_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8901_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8901_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8901_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8901_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear r1); (all_goals try clear r2))
    all_goals simp_all
  obtain ⟨τ,r3,p3⟩:=hlast μ ⟨by simp [μ,ν],by simp [μ]⟩
  exact ⟨τ,r1.seq (r2.seq r3),p3⟩

end Lax263307Proofs.NativeCutPairRead

end

section

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

structure Data {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (σ:Env):Prop where
  cuts:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count:σ.vars "separator.count"=cs.length
  remaining:σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

theorem frame {B K n:ℕ} {cs:List (Finset (Fin n) × Finset (Fin n))} {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hd:Data cs σ) (hc:"separator.cuts"∉c.warrs)
    (hn:"separator.count"∉c.wvars) (hr:"separator.remaining"∉c.wvars):Data cs τ:=by
  refine ⟨?_,(rr.frame_var _ hn).trans hd.count,(rr.frame_var _ hr).trans hd.remaining⟩
  simpa only [Prefix,rr.frame_arr "separator.cuts" hc] using hd.cuts

theorem read_spec {n:ℕ} (B:ℕ) (cs:List (Finset (Fin n) × Finset (Fin n)))
    (i:ℕ) (hi:i<(words cs).length) (hB:2*cs.length+5< B) (hm:2^n< B):
    Spec B (fun σ => Data cs σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => Data cs τ∧ τ.vars "fill.value"=(words cs)[i]) 26:=by
  have hlen:(words cs).length=cs.length+1:=by simp [words]
  have hiB:i< B:=by rw [hlen] at hi; omega
  rintro σ ⟨hd,hs⟩
  have hc:(Cond.eq (.var "fill.i") (.lit 0)).evalB B σ=some (decide (i=0)):=
    evalB_condEq (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩) (evalB_lit (by omega))
  by_cases h:i=0
  · cases h
    let τ:=σ.setVar "fill.value" (mask (remaining Finset.univ cs))
    have rr:Run B (.assign "fill.value" (.var "separator.remaining")) σ τ 2:=Run.assign
      (by rw [evalB_var_iff]; exact ⟨hd.remaining.symm,hd.remaining ▸ (mask_bound _).trans hm⟩)
    have rb:Run B read σ τ 26:=(Run.ite_true (by simpa only [decide_true] using hc) rr).mono (by simp [Cond.size,Expr.size])
    exact ⟨τ,rb,frame rb hd (by decide) (by decide) (by decide),by simp [τ,words]⟩
  · let j:=i-1
    have hj:j< cs.length:=by rw [hlen] at hi; dsimp [j]; omega
    have hij:i=j+1:=by dsimp [j]; omega
    let ν:=σ.setVar "piece.i" j
    have r1:Run B (.assign "piece.i" (.sub (.var "fill.i") (.lit 1))) σ ν 4:=Run.assign
      (evalB_bin (op:=.sub) (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩) (evalB_lit (by omega))
        (by change i-1< B; omega))
    obtain ⟨τ,r2,p2⟩:=NativeCutPairRead.command_spec B cs j hj (by omega) hm ν ⟨hd.cuts,by simp [ν]⟩
    have rb:Run B read σ τ 26:=(Run.ite_false (by simpa only [h,decide_false] using hc) (r1.seq r2)).mono
      (by simp [Cond.size,Expr.size])
    refine ⟨τ,rb,frame rb hd (by decide) (by decide) (by decide),?_⟩
    simpa only [hij,words,List.getElem_cons_succ,List.getElem_map] using p2

theorem command_spec {n:ℕ} (B:ℕ) (cs:List (Finset (Fin n) × Finset (Fin n)))
    (hB:2*cs.length+5< B) (hm:2^n< B):
    Spec B (fun σ => Data cs σ∧ cs.length+1≤(σ.arrs "separator.pieces").length) command
      (fun _ τ => Data cs τ∧ Prefix (words cs) "separator.pieces" τ) (37*(cs.length+1)+10):=by
  have hlen:(words cs).length=cs.length+1:=by simp [words]
  have hword:∀ x∈words cs,x< B:=by
    intro x hx
    simp only [words,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl | ⟨s,hs,rfl⟩ <;> exact (mask_bound _).trans hm
  have hv:=NativeTabulate.command_spec B (words cs) "separator.pieces" (Data cs) read 26
    (by rw [hlen]; omega) hword (by decide) (by decide) (by decide)
    (by intro σ hd; exact ⟨hd.cuts,by simpa using hd.count,by simpa using hd.remaining⟩)
    (fun _ _ rr hd => frame rr hd (by decide) (by decide) (by decide))
    (fun i hi => read_spec B cs i hi hB hm)
  rintro σ ⟨hd,hroom⟩
  let ν:=σ.setVar "fill.length" (cs.length+1)
  have r1:Run B (.assign "fill.length" (.add (.var "separator.count") (.lit 1))) σ ν 4:=Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega:cs.length< B)⟩)
      (evalB_lit (by omega)) (by change cs.length+1< B; omega))
  obtain ⟨τ,r2,p2⟩:=hv ν ⟨frame r1 hd (by decide) (by decide) (by decide),by simpa only [hlen] using
    (show ν.vars "fill.length"=cs.length+1 by simp [ν]),by simpa only [hlen,ν,arrs_setVar] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2⟩

end Lax263307Proofs.NativeCutPieces

end

section

namespace Lax263307Proofs.NativeSeparatorOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeUniformFlow
open scoped NNRat

theorem cuts_length {n:ℕ} (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (fuel:ℕ) (R:Finset (Fin n)):(cuts cut fuel R).length≤ fuel:=by
  induction fuel generalizing R with
  | zero => simp [cuts]
  | succ fuel ih =>
    simp only [cuts]
    split_ifs
    · simp
    · simpa only [List.length_cons] using Nat.succ_le_succ (ih _)

theorem exists_program (f:List ℕ→ List ℕ) (hf:RamPolytime f):
    ∃ (p:Lax808846.Ram.Program) (wp tp op:Polynomial ℕ) (coeff:List ℕ),
    (∀ z:ℕ,RamPolynomial.value coeff z=wp.eval z)∧
    ∀ (b n load k h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0),
    0< n→ 0< load→ (∀ v,Bounded (2^h) (x v:ℚ))→
    let H:=NativeLargeResources.heightExponent b n load k h
    ∀ w:ℕ,wordHeight n H p wp tp op≤ w→
    let cs:=cuts (ComputedSeparators.step f G x b load k) n Finset.univ
    Spec (2^w) (fun σ => Context G x b load k (spaceBound n H tp) σ∧
      n+1≤(σ.arrs "separator.pieces").length)
      (command p coeff) (fun _ τ => Context G x b load k (spaceBound n H tp) τ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs)∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs)∧ τ.vars "separator.count"=cs.length∧
        Prefix (NativeCutRecords.words cs) "separator.cuts" τ∧
        τ.vars "separator.position"=2*cs.length∧
        Prefix (NativeCutPieces.words cs) "separator.pieces" τ)
      (timeBound n H p coeff tp):=by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,hsep⟩:=NativeSeparatorProgram.exists_program f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,?_⟩
  intro b n load k h G _ x hn hl hx
  try dsimp only
  let H:=NativeLargeResources.heightExponent b n load k h
  intro w hwidth
  try dsimp only
  let cs:=cuts (ComputedSeparators.step f G x b load k) n Finset.univ
  have hcs:cs.length≤ n:=cuts_length _ _ _
  have hh:n+30≤ H:=by dsimp [H,NativeLargeResources.heightExponent]; omega
  have hw:=hwidth
  dsimp only [wordHeight] at hw
  have hm:2^n<2^w:=Nat.pow_lt_pow_right (by decide) (by omega)
  have hB:2*n+5<2^w:=NativeUniformWordGuards.scalar _ w (by
    have hs:2*n+5≤ shape n:=by dsimp [shape]; nlinarith only []
    omega)
  rintro σ ⟨hd,hr⟩
  obtain ⟨ν,r1,p1⟩:=NativeFullSetMask.command_spec (2^w) n (by omega) hm σ hd.order
  have hd1:=frame r1 hd (by decide) (by decide) (by decide)
  obtain ⟨μ,r2,p2⟩:=hsep b n load k h G x hn hl hx w hwidth ν ⟨hd1,p1⟩
  have hr2:cs.length+1≤(μ.arrs "separator.pieces").length:=by
    rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]
    omega
  obtain ⟨τ,r3,p3⟩:=NativeCutPieces.command_spec (2^w) cs (by omega) hm μ
    ⟨⟨p2.2.2.2.2.1,p2.2.2.2.1,p2.2.1⟩,hr2⟩
  have hd3:=frame r3 p2.1 (by decide) (by decide) (by decide)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono ?_,hd3,p3.1.remaining,?_,p3.1.count,p3.1.cuts,?_,p3.2⟩
  · dsimp only [timeBound]
    have ht:=Nat.mul_le_mul_left 37 (Nat.add_le_add_right hcs 1)
    omega
  · exact (r3.frame_var "separator.value" (by decide)).trans p2.2.2.1
  · exact (r3.frame_var "separator.position" (by decide)).trans p2.2.2.2.2.2

end Lax263307Proofs.NativeSeparatorOutput

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
                          (Nat.le
                            (Nat.add n
                              ((1:Nat)))
                            (@List.length Nat (σ.arrs "separator.pieces"))))
                      (Lax263307Proofs.NativeSeparatorOutput.command p coeff)
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
                                  (And
                                    (@Eq Nat (τ.vars "separator.position")
                                      (Nat.mul
                                        ((2:Nat))
                                        (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                    (Lax455465Proofs.RamVirtualState.Prefix
                                      (@Lax263307Proofs.NativeCutPieces.words n cs) "separator.pieces" τ)))))))
                      (Lax263307Proofs.NativeSeparatorOutput.timeBound n H p coeff tp)):= @Lax263307Proofs.NativeSeparatorOutput.exists_program
