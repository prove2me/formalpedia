-- Prove2me | solution 1 for Lax109476Proofs.RamSearchBounds.search_bounded_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:14:41.774877+00:00
-- url     : https://prove2.me/submissions/3d364474-256e-45b8-a054-c8e94edd41d5

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamSearchLoop_searchLoop_spec_native
import Theorems.Thm_Lax109476Proofs_RamInitialState_initialState_spec_native

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

namespace Lax109476Proofs.RamSearchLoop
end Lax109476Proofs.RamSearchLoop
theorem Lax109476Proofs.RamSearchLoop.searchLoop_spec:∀ {m n:Nat} (A:Matrix (Fin m) (Fin n) Int) (b:Fin m→ Rat),
  LE.le ((2:Nat)) n→
    ∀ (N l w:Nat),
      LT.lt N
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) w)→
        (∀ (i:Fin m) (j:Fin n),
            LE.le (A i j).natAbs
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) l))→
          (∀ (i:Fin m),
              Lax109476Proofs.RationalArithmeticBounds.Height (b i)
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) l))→
            LE.le
                (Lax109476Proofs.RamEllipsoidBitBounds.wordWidth n (Lax109476Proofs.RamTrajectoryBounds.stateBits n N l)
                  N)
                w→
              LT.lt
                  (HAdd.hAdd
                    (HAdd.hAdd
                      (HAdd.hAdd m n)
                      (HMul.hMul m n))
                    ((1:Nat)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w)→
                LT.lt
                    (HAdd.hAdd
                      (HMul.hMul
                        ((2:Nat))
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (Lax109476Proofs.RamDotProduct.cap n
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              ((2:Nat))
                              (Lax109476Proofs.RamTrajectoryBounds.stateBits n N l)))
                          ((2:Nat))))
                      ((3:Nat)))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And
                        (@Lax109476Proofs.RamSearchStep.State m n A b
                          ((0:Nat)) σ)
                        (And (@Eq Nat (σ.vars "search.limit") N)
                          (@Eq Nat (σ.vars "search.found") ((0:Nat)))))
                    Lax109476Proofs.RamSearchLoop.searchLoop
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamSearchLoop.Invariant m n A b N τ)
                        (@Eq (Option Bool)
                          (Lax808846Proofs.Imp.Cond.evalB
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              ((2:Nat)) w)
                            (Lax808846Proofs.Imp.Cond.lt (Lax808846Proofs.Imp.Expr.var "iter.k")
                              (Lax808846Proofs.Imp.Expr.var "search.limit"))
                            τ)
                          (@Option.some Bool Bool.false)))
                    (HAdd.hAdd
                      (HMul.hMul
                        (HAdd.hAdd (Lax109476Proofs.RamSearchStep.cost m n N l)
                          ((4:Nat)))
                        N)
                      ((4:Nat))):= @Lax109476Proofs.RamSearchLoop.searchLoop_spec_native
namespace Lax109476Proofs.RamInitialState
end Lax109476Proofs.RamInitialState
theorem Lax109476Proofs.RamInitialState.initialState_spec:∀ (B n:Nat),
  LT.lt n B→
    LT.lt (HMul.hMul n n) B→
      LT.lt ((1:Nat)) B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And (Lax109476Proofs.RamEllipsoidStep.Extents "ell.center" n σ)
              (And
                (Lax109476Proofs.RamEllipsoidStep.Extents "ell.shape"
                  (HMul.hMul n n) σ)
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
          (HAdd.hAdd
            (HAdd.hAdd
              (HMul.hMul
                ((33:Nat)) n)
              (HMul.hMul
                ((76:Nat))
                (HMul.hMul n n)))
            ((56:Nat))):= @Lax109476Proofs.RamInitialState.initialState_spec_native

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

theorem Run.assign {B:ℕ} {σ:Env} {x:String} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=.of_bigStepB (.assign h)

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

theorem size_mul_le (a b:ℕ):Nat.size (a * b)≤ Nat.size a + Nat.size b:=by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

theorem size_pow_le (a k:ℕ):Nat.size (a ^ k)≤ k * Nat.size a + 1:=by
  induction k with
  | zero => simp
  | succ k ih =>
    have h:=size_mul_le (a ^ k) a
    rw [pow_succ,Nat.succ_mul]
    omega

theorem size_add_one_le (a:ℕ):Nat.size (a + 1)≤ Nat.size a + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h:=Nat.lt_size_self a
  have hp:0 < 2 ^ Nat.size a:=by positivity
  omega

theorem size_add_le (a b:ℕ):Nat.size (a + b)≤ Nat.size a + Nat.size b + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ,pow_add]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hpa:0 < 2 ^ Nat.size a:=by positivity
  have hpb:0 < 2 ^ Nat.size b:=by positivity
  have h₁:=Nat.le_mul_of_pos_right (2 ^ Nat.size a) hpb
  have h₂:=Nat.le_mul_of_pos_left (2 ^ Nat.size b) hpa
  omega

end Lax109476Proofs.RationalSizeBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

theorem findFirst_eq_find (p:ℕ→ Bool) (start count:ℕ):
    findFirst p start count=(List.range' start count).find? p:=by
  induction count generalizing start with
  | zero => simp [findFirst]
  | succ count ih =>
    cases hp:p start <;> simp [findFirst,List.range'_succ,ih,hp]

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

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

variable {B:ℕ} {P P':Env→ Prop} {Q Q' R:Env→ Env→ Prop} {c d:Com} {K K':ℕ}

theorem Spec.mono (h:Spec B P c Q K) (hK:K≤ K'):Spec B P c Q K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr.mono hK,hq⟩

theorem le_of_condLt_false {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some false):ρ.vars y≤ ρ.vars x:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  have:=hr.symm
  simp only [decide_eq_false_iff_not,not_lt] at this
  exact this

end Lax808846Proofs.Reasoning

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

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

theorem centerCap_size (M:ℕ):(centerCap M).size≤ 4 * M.size + 8:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 4
  have hm:=RationalSizeBounds.size_mul_le 2 ((M + 1) ^ 4)
  have ha:=RationalSizeBounds.size_add_one_le (2 * (M + 1) ^ 4)
  have htwo:Nat.size 2=2:=by decide
  unfold centerCap
  omega

theorem updateCenter_cost_polynomial (n M:ℕ):
    33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)≤
      (720 * M.size + 1799) * n + 24:=by
  have hm:=Nat.mul_le_mul_left 180 (centerCap_size M)
  have hn:=Nat.mul_le_mul_right n (Nat.add_le_add_right hm 359)
  convert Nat.add_le_add_right hn 24 using 1 <;> ring

end Lax109476Proofs.RamCenterUpdate

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamDotProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamPrimitiveBounds RamFrame RationalArithmeticBounds

theorem cap_ge (n H:ℕ) (hH:1≤ H):H * H≤ cap n H∧ H≤ cap n H:=by
  have hb:1≤ 2 * (H * H):=by nlinarith
  have hp:=le_self_pow hb (by omega:n + 1 ≠ 0)
  change H * H≤ (2 * (H * H)) ^ (n + 1)∧ H≤ (2 * (H * H)) ^ (n + 1)
  constructor <;> nlinarith

theorem cap_size (n H:ℕ):(cap n H).size≤ (n + 1) * (2 * H.size + 3) + 1:=by
  have hh:=RationalSizeBounds.size_mul_le H H
  have ht:=RationalSizeBounds.size_mul_le 2 (H * H)
  have hp:=RationalSizeBounds.size_pow_le (2 * (H * H)) (n + 1)
  have htwo:Nat.size 2=2:=by decide
  have hb:(2 * (H * H)).size≤ 2 * H.size + 3:=by omega
  have hm:=Nat.mul_le_mul_left (n + 1) hb
  dsimp [cap]
  omega

end Lax109476Proofs.RamDotProduct

end

section

namespace Lax109476Proofs.RamShapeCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

theorem shapeCap_pow (M k:ℕ) (hk:k≤ 8):M ^ k≤ (M + 1) ^ 8:=
  (Nat.pow_le_pow_left (by omega:M≤ M + 1) k).trans
    (Nat.pow_le_pow_right (by omega:1≤ M + 1) hk)

theorem shapeCap_bounds (M:ℕ):
    M≤ shapeCap M∧ M ^ 2≤ shapeCap M∧ M ^ 3≤ shapeCap M∧
      2 * M ^ 4≤ shapeCap M∧ 2 * M ^ 5≤ shapeCap M∧
      2 * M ^ 6 + 1≤ shapeCap M∧ 6 * M ^ 7≤ shapeCap M∧ 6 * M ^ 8≤ shapeCap M:=by
  have hp1:=shapeCap_pow M 1 (by omega)
  have hp2:=shapeCap_pow M 2 (by omega)
  have hp3:=shapeCap_pow M 3 (by omega)
  have hp4:=shapeCap_pow M 4 (by omega)
  have hp5:=shapeCap_pow M 5 (by omega)
  have hp6:=shapeCap_pow M 6 (by omega)
  have hp7:=shapeCap_pow M 7 (by omega)
  have hp8:=shapeCap_pow M 8 (by omega)
  have hbase:1≤ (M + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at hp1
  unfold shapeCap
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,
    by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end Lax109476Proofs.RamShapeCoordinate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamShapeUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamShapeCoordinate RamZeroArray RamMatrixStorage

theorem shapeCap_size (M:ℕ):(shapeCap M).size≤ 8 * M.size + 13:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 8
  have hm:=RationalSizeBounds.size_mul_le 8 ((M + 1) ^ 8)
  have h8:Nat.size 8=4:=by decide
  unfold shapeCap
  omega

theorem updateShape_cost_polynomial (n M:ℕ):
    33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)≤
      (3744 * M.size + 6815) * (n * n) + 36:=by
  have hm:=Nat.mul_le_mul_left 468 (shapeCap_size M)
  have hn:=Nat.mul_le_mul_right (n * n) (Nat.add_le_add_right hm 731)
  convert Nat.add_le_add_right hn 36 using 1 <;> ring

end Lax109476Proofs.RamShapeUpdate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RationalArithmeticBounds

theorem ellipsoidMulVec_cost_polynomial (n H:ℕ):
    33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8)≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 + 78 * n + 26:=by
  have hm:=Nat.mul_le_mul_right (n * n)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 144 (cap_size n H)) 220)
  convert Nat.add_le_add_right hm (78 * n + 26) using 1 <;> ring

end Lax109476Proofs.RamMatrixVector

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamMatrixVector
open RationalArithmeticBounds

theorem formHeight_ge (n H:ℕ) (hH:1≤ H):cap n H≤ formHeight n H:=by
  have hcap:=(cap_ge n H hH).2
  exact (cap_ge n (cap n H) (hH.trans hcap)).2

theorem formHeight_size (n H:ℕ):
    (formHeight n H).size≤
      (n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1:=by
  have hc:=cap_size n H
  have hf:=cap_size n (cap n H)
  have hm:=Nat.mul_le_mul_left (n + 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 3)
  unfold formHeight
  omega

theorem ellipsoidForm_cost_polynomial (n H:ℕ):
    33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
      (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6)≤
    (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
      (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n + 44:=by
  have hd:=Nat.add_le_add_right
    (Nat.mul_le_mul_right n (Nat.add_le_add_right (Nat.mul_le_mul_left 144 (formHeight_size n H)) 214)) 18
  convert Nat.add_le_add (ellipsoidMulVec_cost_polynomial n H) hd using 1
  ring

end Lax109476Proofs.RamEllipsoidForm

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

theorem roundedUpdate_cost_polynomial (n M:ℕ):
    ((33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) +
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)))≤
      (720 * M.size + 1799) * n + (3744 * M.size + 6815) * (n * n) + 60:=by
  have h:=Nat.add_le_add (updateCenter_cost_polynomial n M) (updateShape_cost_polynomial n M)
  convert h using 1 <;> ring

end Lax109476Proofs.RamEllipsoidUpdate

end

section

namespace Lax109476Proofs.RamEllipsoidWordBounds

open RamEllipsoidCoefficients RamShapeCoordinate RamCenterCoordinate

theorem coefficientCap_bounds (M:ℕ):
    M≤ coefficientCap M∧ M ^ 3 + 2≤ coefficientCap M∧ 4 * (M + 1)≤ coefficientCap M:=by
  have hp1:M + 1≤ (M + 1) ^ 4:=
    le_self_pow (by omega) (by decide:(4:ℕ) ≠ 0)
  have hp3:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 3).trans
    (Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(3:ℕ)≤ 4))
  have hone:1≤ (M + 1) ^ 4:=Nat.one_le_pow _ _ (by omega)
  unfold coefficientCap
  omega

theorem shapeCap_linear (N:ℕ):8 * (N + 1)≤ shapeCap N:=by
  exact Nat.mul_le_mul_left 8 (le_self_pow (by omega) (by decide:(8:ℕ) ≠ 0))

theorem centerCap_le_shapeCap (N:ℕ):centerCap N≤ shapeCap N:=by
  have hp:=Nat.pow_le_pow_right (by omega:1≤ N + 1) (by decide:(4:ℕ)≤ 8)
  have hone:1≤ (N + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
  unfold centerCap shapeCap
  omega

theorem rootBound_le_shapeBound (M:ℕ):
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3≤ 2 * (shapeCap (coefficientCap M)) ^ 2 + 3:=by
  let N:=coefficientCap M
  let S:=shapeCap N
  have hM3:M ^ 3 + 2≤ N:=(coefficientCap_bounds M).2.1
  have hS:8 * (N + 1)≤ S:=shapeCap_linear N
  have hbase:2 * (M ^ 3 + 2) + 1≤ 2 * N + 1:=by omega
  have hsq:=Nat.pow_le_pow_left hbase 2
  calc
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3≤ (2 * N + 1) ^ 2 + N + 1:=by omega
    _≤ 2 * S ^ 2 + 3:=by nlinarith only [hS]

theorem dimensions_le_coefficientCap (n M:ℕ) (hn:2≤ n) (hnM:n * n≤ M):
    n + n + n * n + 1≤ coefficientCap M:=by
  have hnp:n≤ n * n:=by
    simpa only [pow_two] using le_self_pow (by omega:1≤ n) (by decide:(2:ℕ) ≠ 0)
  have hc:=(coefficientCap_bounds M).2.2
  omega

theorem unified_word_bounds (B M n:ℕ) (hn:2≤ n) (hnM:n * n≤ M)
    (hB:2 * (shapeCap (coefficientCap M)) ^ 2 + 3 < B):
    coefficientCap M < B∧ M < B∧ n ^ 2 < B∧ n < B∧ 5 < B∧
      n + n + n * n + 1 < B∧ 2 * M ^ 2 + 3 < B∧
      (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B∧
      2 * (centerCap (coefficientCap M)) ^ 2 + 3 < B:=by
  have hN:=(coefficientCap_bounds M).1
  have hNS:=(shapeCap_bounds (coefficientCap M)).1
  have hSB:shapeCap (coefficientCap M) < B:=by nlinarith only [hB]
  have hNB:=hNS.trans_lt hSB
  have hMB:=hN.trans_lt hNB
  have hnB:n < B:=lt_of_le_of_lt (by nlinarith only [hn,hnM]) hMB
  have h5B:5 < B:=by
    have hlin:=shapeCap_linear (coefficientCap M)
    omega
  have hdimB:=(dimensions_le_coefficientCap n M hn hnM).trans_lt hNB
  have hMS:=hN.trans hNS
  have hpow:=Nat.pow_le_pow_left hMS 2
  have hprim:2 * M ^ 2 + 3 < B:=lt_of_le_of_lt (by omega) hB
  have hroot:=(rootBound_le_shapeBound M).trans_lt hB
  have hcenter:=Nat.pow_le_pow_left (centerCap_le_shapeCap (coefficientCap M)) 2
  refine ⟨hNB,hMB, ?_,hnB,h5B,hdimB,hprim,hroot, ?_⟩
  · simpa only [pow_two] using hnM.trans_lt hMB
  · exact lt_of_le_of_lt (by omega) hB

end Lax109476Proofs.RamEllipsoidWordBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamEllipsoidUpdate RamEllipsoidWordBounds RamEllipsoidPrecision RamEllipsoidCoefficients
open RamEllipsoidScalars RamEllipsoidForm RamMatrixVector RamMatrixRows RamDotProduct RamMatrixStorage

theorem coefficientCap_size (M:ℕ):(coefficientCap M).size≤ 4 * M.size + 8:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 4
  have hm:=RationalSizeBounds.size_mul_le 4 ((M + 1) ^ 4)
  have hfour:Nat.size 4=3:=by decide
  unfold coefficientCap
  omega

theorem stepCost_polynomial (n H M:ℕ):
    stepCost n H M≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
      (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n +
      (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 582 * M.size + 1000:=by
  have hcap:=coefficientCap_size M
  have hlin:=Nat.mul_le_mul_right n (Nat.add_le_add_right (Nat.mul_le_mul_left 720 hcap) 1799)
  have hquad:=Nat.mul_le_mul_right (n * n) (Nat.add_le_add_right (Nat.mul_le_mul_left 3744 hcap) 6815)
  have hupdate:=roundedUpdate_cost_polynomial n (coefficientCap M)
  have hupdate':updateCost n (coefficientCap M)≤
      (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 60:=by
    have hp:=Nat.add_le_add_right (Nat.add_le_add hlin hquad) 60
    have hpay:=hupdate.trans hp
    convert hpay using 1 <;> first | rfl | ring | (simp only [updateCost] <;> ring)
  let P:=(144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
    (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n + 44
  let R:=(2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 60
  have hform:formCost n H≤ P:=ellipsoidForm_cost_polynomial n H
  have htotal:formCost n H + updateCost n (coefficientCap M)≤ P + R:=Nat.add_le_add hform hupdate'
  calc
    stepCost n H M=(formCost n H + updateCost n (coefficientCap M)) + (20 + (582 * M.size + 876)):=by
      unfold stepCost
      omega
    _≤ (P + R) + (20 + (582 * M.size + 876)):=Nat.add_le_add_right htotal _
    _=_:=by dsimp only [P,R]; ring

end Lax109476Proofs.RamEllipsoidStep

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

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamEllipsoidBitBounds

open RamDotProduct RamEllipsoidForm RamEllipsoidStep RamEllipsoidCoefficients
open RamShapeCoordinate RamShapeUpdate RationalSizeBounds

theorem cap_two_pow (n h:ℕ):cap n (2 ^ h)=2 ^ ((2 * h + 1) * (n + 1)):=by
  simp only [cap, ← pow_two]
  change (2 ^ 1 * (2 ^ h) ^ 2) ^ (n + 1)=_
  rw [← pow_mul, ← pow_add, ← pow_mul]
  congr 1
  ring

theorem formHeight_two_pow (n h:ℕ):formHeight n (2 ^ h)=2 ^ formExponent n h:=by
  simp only [formHeight,cap_two_pow,formExponent]

theorem guard_size (M:ℕ):
    (2 * (shapeCap (coefficientCap M)) ^ 2 + 3).size≤ 64 * M.size + 160:=by
  have hc:=coefficientCap_size M
  have hs:=shapeCap_size (coefficientCap M)
  have hp:=size_pow_le (shapeCap (coefficientCap M)) 2
  have hm:=size_mul_le 2 ((shapeCap (coefficientCap M)) ^ 2)
  have ha:=size_add_le (2 * (shapeCap (coefficientCap M)) ^ 2) 3
  have htwo:Nat.size 2=2:=by decide
  have hthree:Nat.size 3=2:=by decide
  omega

theorem magnitude_parameters (n h k:ℕ):
    n * n≤ 2 ^ magnitudeExponent n h k∧
      formHeight n (2 ^ h)≤ 2 ^ magnitudeExponent n h k∧
      2 ^ (2 * k + 3 * n + 9)≤ 2 ^ magnitudeExponent n h k∧
      2 ^ (2 * n + 4)≤ 2 ^ magnitudeExponent n h k:=by
  have hn:n * n < 2 ^ (n * n):=Nat.lt_two_pow_self
  have hexp:n * n≤ magnitudeExponent n h k:=by unfold magnitudeExponent; omega
  refine ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) hexp), ?_, ?_, ?_⟩
  · rw [formHeight_two_pow]
    apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega

theorem wordWidth_sufficient (n h k w:ℕ) (hw:wordWidth n h k≤ w):
    2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3 < 2 ^ w:=by
  have hg:=guard_size (2 ^ magnitudeExponent n h k)
  rw [Nat.size_pow] at hg
  have hp:=Nat.lt_size_self (2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3)
  apply hp.trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold wordWidth at hw
  omega

end Lax109476Proofs.RamEllipsoidBitBounds

end

section

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamTrajectoryBounds

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding Lax109476.RationalCertificates
open RationalArithmeticBounds EncodingSize EllipsoidSearch EllipsoidSequence
open RamEllipsoidBitBounds RamEllipsoidStep RamAdvanceState RamRationalArrays RamMatrixStorage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

set_option maxRecDepth 30000 in
theorem instructionBound_polynomial (n K l:ℕ):
    stepCost n (2 ^ stateBits n K l) (2 ^ magnitudeExponent n (stateBits n K l) K) +
      71 * n + 71 * (n * n) + 60≤ instructionBound n K l:=by
  have h:=stepCost_polynomial n (2 ^ stateBits n K l)
    (2 ^ magnitudeExponent n (stateBits n K l) K)
  rw [Nat.size_pow,Nat.size_pow] at h
  have htotal:=Nat.add_le_add_right h (71 * n + 71 * (n * n) + 60)
  dsimp only [instructionBound]
  omega

end Lax109476Proofs.RamTrajectoryBounds

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamSeparation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamComparison RationalArithmeticBounds

theorem rowCost_polynomial (n H:ℕ):
    rowCost n H≤ (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n + 75:=by
  have hc:=Nat.mul_le_mul_left 144 (cap_size n H)
  have hn:=Nat.mul_le_mul_right n (Nat.add_le_add_right hc 220)
  unfold rowCost
  convert Nat.add_le_add_right hn 75 using 1
  ring

theorem separateRows_cost_polynomial (m n H:ℕ):
    (rowCost n H + 16 + 4) * m + 8≤
      ((144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n + 95) * m + 8:=by
  have hr:=Nat.add_le_add_right (rowCost_polynomial n H) 20
  convert Nat.add_le_add_right (Nat.mul_le_mul_right m hr) 8 using 1

end Lax109476Proofs.RamSeparation

end

section

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows RamSeparation RamNormalSelection RamTrajectoryBounds
open RamEllipsoidStep RamEllipsoidBitBounds RamAdvanceState EllipsoidSearch RationalArithmeticBounds

theorem matrixRows_frame {B K:ℕ} {d:Com} {σ τ:Env} (hr:Run B d σ τ K)
    {m n:ℕ} (a:String) (A:Matrix (Fin m) (Fin n) ℚ) (hσ:MatrixRows a A σ)
    (hs:a ++ ".s" ∉ d.warrs) (hn:a ++ ".n" ∉ d.warrs) (hd:a ++ ".d" ∉ d.warrs):
    MatrixRows a A τ:=by
  intro i
  simpa only [Slice,hr.frame_arr _ hs,hr.frame_arr _ hn,hr.frame_arr _ hd] using hσ i

end Lax109476Proofs.RamSearchStep

end

section

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSearchStep EllipsoidSearch

theorem invariant_outcome {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (N B:ℕ) (σ:Env) (hI:Invariant A b N σ)
    (hfalse:(Cond.lt (.var "iter.k") (.var "search.limit")).evalB B σ=some false):
    findFirst (fun j => decide (RationalSeparation.firstViolation A b (trajectory A b j).2=none)) 0 N =
      if σ.vars "search.found"=1 then some (σ.vars "iter.k") else none:=by
  obtain ⟨k,hkN,hstate,hprior,hstatus⟩:=hI
  have hσk:σ.vars "iter.k"=k:=hstate.2.2.2.2.2.2.2.2
  have hle:=le_of_condLt_false hfalse
  rcases hstatus with ⟨hf,hlimit⟩ | ⟨hf,hlimit,hk,hsuccess⟩
  · have heq:k=N:=by omega
    simp only [hf,Nat.zero_ne_one,if_false,findFirst_eq_find,List.find?_eq_none]
    intro j hj
    have hjN:j < N:=by simpa using hj
    simpa only [decide_eq_true_eq] using hprior j (by omega)
  · simp only [hf,if_pos rfl,hσk,findFirst_eq_find]
    apply List.find?_range'_eq_some.mpr
    refine ⟨by simp [hsuccess],by simpa using hk, ?_⟩
    intro j _ hj
    simp [hprior j hj]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem search_spec {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (N l w:ℕ) (hNB:N < 2 ^ w)
    (hA:∀ i j, (A i j).natAbs≤ 2 ^ l)
    (hb:∀ i,RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw:RamEllipsoidBitBounds.wordWidth n (RamTrajectoryBounds.stateBits n N l) N≤ w)
    (hdims:m + n + m * n + 1 < 2 ^ w)
    (hsep:2 * (RamDotProduct.cap n (2 ^ RamTrajectoryBounds.stateBits n N l)) ^ 2 + 3 < 2 ^ w):
    Spec (2 ^ w) (fun σ => RamMatrixRows.MatrixRows "search.rows" (fun i j => (A i j:ℚ)) σ∧
        RamRationalArrays.Represents "search.rhs" (List.ofFn b) σ∧
        RamEllipsoidStep.Extents "ell.center" n σ∧ RamEllipsoidStep.Extents "ell.shape" (n * n) σ∧
        RamEllipsoidStep.Workspace n σ∧ RamEllipsoidStep.Extents "ell.normal" n σ∧
        σ.vars "vec.n"=n∧ σ.vars "row.m"=m∧ σ.vars "search.budget"=N)
      search
      (fun _ τ => Invariant A b N τ∧
        findFirst (fun j => decide (RationalSeparation.firstViolation A b (trajectory A b j).2=none)) 0 N =
          if τ.vars "search.found"=1 then some (τ.vars "iter.k") else none)
      (33 * n + 76 * (n * n) + (cost m n N l + 4) * N + 64):=by
  have h1:1 < 2 ^ w:=by omega
  have hnB:n < 2 ^ w:=by omega
  have hparams:=RamEllipsoidBitBounds.magnitude_parameters n (RamTrajectoryBounds.stateBits n N l) N
  have hguard:=RamEllipsoidBitBounds.wordWidth_sufficient n (RamTrajectoryBounds.stateBits n N l) N w hw
  have hbds:=RamEllipsoidWordBounds.unified_word_bounds _ _ n hn hparams.1 hguard
  have hnnB:n * n < 2 ^ w:=by simpa only [pow_two] using hbds.2.2.1
  rintro σ ⟨hσrows,hσrhs,hσc,hσA,hσwork,hσnormal,hσn,hσm,hσbudget⟩
  have hr₁:Run (2 ^ w) (.assign "search.limit" (.var "search.budget")) σ
      (σ.setVar "search.limit" N) 2:=
    Run.assign (by simpa [hσbudget] using (evalB_var (B:=2 ^ w) (σ:=σ) (x:= "search.budget") (by omega)))
  have hr₂:Run (2 ^ w) (.assign "search.found" (.lit 0)) (σ.setVar "search.limit" N)
      ((σ.setVar "search.limit" N).setVar "search.found" 0) 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨τ,hr₃,hτc,hτA,hτwork,hτn,hτk⟩:=RamInitialState.initialState_spec (2 ^ w) n hnB hnnB h1
    ((σ.setVar "search.limit" N).setVar "search.found" 0)
    ⟨by simpa only [RamEllipsoidStep.Extents,arrs_setVar] using hσc,
      by simpa only [RamEllipsoidStep.Extents,arrs_setVar] using hσA,
      by simpa only [RamEllipsoidStep.Workspace,RamEllipsoidStep.Extents,arrs_setVar] using hσwork,
      by simpa using hσn⟩
  have hinit:=hr₁.seq (hr₂.seq hr₃)
  have hτrows:=matrixRows_frame hinit "search.rows" _ hσrows (by decide) (by decide) (by decide)
  have hτrhs:=RamEllipsoidUpdate.represents_frame hinit "search.rhs" _ hσrhs (by decide) (by decide) (by decide)
  have hτnormal:=RamAdvanceState.extents_of_run hinit "ell.normal" n hσnormal
  have hτm:τ.vars "row.m"=m:=(hinit.frame_var _ (by decide)).trans hσm
  have hτlimit:τ.vars "search.limit"=N:=by simpa using (hr₃.frame_var "search.limit" (by decide))
  have hτfound:τ.vars "search.found"=0:=by simpa using (hr₃.frame_var "search.found" (by decide))
  have hτstate:State A b 0 τ:= ⟨hτA,hτc,hτwork,hτnormal,hτrows,hτrhs,hτn,hτm,hτk⟩
  obtain ⟨υ,hr₄,hυI,hυfalse⟩:=searchLoop_spec A b hn N l w hNB hA hb hw hdims hsep
    τ ⟨hτstate,hτlimit,hτfound⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono ?_,hυI,invariant_outcome A b N _ υ hυI hυfalse⟩
  omega

end Lax109476Proofs.RamSearchLoop

end

section

namespace Lax109476Proofs.RamSearchBounds

open RamTrajectoryBounds RamEllipsoidBitBounds RamEllipsoidStep RamEllipsoidWordBounds
open RamDotProduct RamEllipsoidForm

theorem wordWidth_parameters (m n N l w:ℕ) (hn:2≤ n) (hw:wordWidth m n N l≤ w):
    N < 2 ^ w∧ RamEllipsoidBitBounds.wordWidth n (stateBits n N l) N≤ w∧
      m + n + m * n + 1 < 2 ^ w∧
      2 * (cap n (2 ^ stateBits n N l)) ^ 2 + 3 < 2 ^ w:=by
  have hcut:RamEllipsoidBitBounds.wordWidth n (stateBits n N l) N≤ w:=by unfold wordWidth at hw; omega
  have hNB:N < 2 ^ w:=by
    have hN:N < 2 ^ N:=Nat.lt_two_pow_self
    exact hN.trans_le (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hdims:m + n + m * n + 1 < 2 ^ w:=by
    have hd:m + n + m * n + 1 < 2 ^ (m + n + m * n + 1):=Nat.lt_two_pow_self
    exact hd.trans_le (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hp:=magnitude_parameters n (stateBits n N l) N
  have hg:=wordWidth_sufficient n (stateBits n N l) N w hcut
  have hb:=unified_word_bounds _ _ n hn hp.1 hg
  have hH:1≤ 2 ^ stateBits n N l:=Nat.one_le_pow _ _ (by decide)
  have hc:=(formHeight_ge n (2 ^ stateBits n N l) hH).trans hp.2.1
  have hprim:=hb.2.2.2.2.2.2.1
  have hsq:=Nat.pow_le_pow_left hc 2
  refine ⟨hNB,hcut,hdims, ?_⟩
  omega

theorem stepBound_sufficient (m n N l:ℕ):RamSearchStep.cost m n N l≤ stepBound m n N l:=by
  have hs:=RamSeparation.separateRows_cost_polynomial m n (2 ^ stateBits n N l)
  rw [Nat.size_pow] at hs
  simp only [Nat.add_assoc,Nat.reduceAdd] at hs
  have hc:=RamTrajectoryBounds.instructionBound_polynomial n N l
  have htotal:=Nat.add_le_add hs hc
  unfold RamSearchStep.cost stepBound rowBound
  omega

theorem instructionBound_sufficient (m n N l:ℕ):
    33 * n + 76 * (n * n) + (RamSearchStep.cost m n N l + 4) * N + 64≤ instructionBound m n N l:=by
  have hstep:=Nat.mul_le_mul_right N (Nat.add_le_add_right (stepBound_sufficient m n N l) 4)
  unfold instructionBound
  omega

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamMatrixRows RamRationalArrays RamEllipsoidStep

theorem search_bounded_spec {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (N l w:ℕ)
    (hA:∀ i j, (A i j).natAbs≤ 2 ^ l)
    (hb:∀ i,RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw:wordWidth m n N l≤ w):
    Spec (2 ^ w) (Input A b N) RamSearchLoop.search
      (fun _ τ => RamSearchLoop.Invariant A b N τ∧
        EllipsoidSearch.findFirst
          (fun j => decide (RationalSeparation.firstViolation A b (EllipsoidSearch.trajectory A b j).2=none)) 0 N =
          if τ.vars "search.found"=1 then some (τ.vars "iter.k") else none)
      (instructionBound m n N l):=by
  have hp:=wordWidth_parameters m n N l w hn hw
  exact (RamSearchLoop.search_spec A b hn N l w hp.1 hA hb hp.2.1 hp.2.2.1 hp.2.2.2).mono
    (instructionBound_sufficient m n N l)

end Lax109476Proofs.RamSearchBounds

end

theorem solution:∀ {m n:Nat} (A:Matrix (Fin m) (Fin n) Int) (b:Fin m→ Rat),
  Nat.le ((2:Nat)) n→
    ∀ (N l w:Nat),
      (∀ (i:Fin m) (j:Fin n),
          Nat.le (A i j).natAbs
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) l))→
        (∀ (i:Fin m),
            Lax109476Proofs.RationalArithmeticBounds.Height (b i)
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) l))→
          Nat.le (Lax109476Proofs.RamSearchBounds.wordWidth m n N l) w→
            Lax808846Proofs.Reasoning.Spec
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) w)
              (@Lax109476Proofs.RamSearchBounds.Input m n A b N) Lax109476Proofs.RamSearchLoop.search
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamSearchLoop.Invariant m n A b N τ)
                  (@Eq (Option Nat)
                    (Lax109476Proofs.EllipsoidSearch.findFirst
                      (fun (j:Nat) =>
                        @Decidable.decide
                          (@Eq (Option (Fin m))
                            (@Lax109476Proofs.RationalSeparation.firstViolation m n A b
                              (@Prod.snd (Matrix (Fin n) (Fin n) Rat) (Fin n→ Rat)
                                (@Lax109476Proofs.EllipsoidSearch.trajectory m n A b j)))
                            (@Option.none (Fin m)))
                          (@Option.decidableEqNone (Fin m)
                            (@Lax109476Proofs.RationalSeparation.firstViolation m n A b
                              (@Prod.snd (Matrix (Fin n) (Fin n) Rat) (Fin n→ Rat)
                                (@Lax109476Proofs.EllipsoidSearch.trajectory m n A b j)))))
                      ((0:Nat)) N)
                    (@ite (Option Nat)
                      (@Eq Nat (τ.vars "search.found") ((1:Nat)))
                      (instDecidableEqNat (τ.vars "search.found")
                        ((1:Nat)))
                      (@Option.some Nat (τ.vars "iter.k")) (@Option.none Nat))))
              (Lax109476Proofs.RamSearchBounds.instructionBound m n N l):= @Lax109476Proofs.RamSearchBounds.search_bounded_spec
