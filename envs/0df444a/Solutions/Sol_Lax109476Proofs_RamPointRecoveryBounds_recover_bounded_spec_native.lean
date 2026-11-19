-- Prove2me | solution 1 for Lax109476Proofs.RamPointRecoveryBounds.recover_bounded_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:27:14.809785+00:00
-- url     : https://prove2.me/submissions/87793415-a902-46c0-b511-793440c6b4d9

import Mathlib.Tactic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax109476Proofs_RamPointRecoveryStep_step_spec_native

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

namespace Lax109476Proofs.RamPointRecoveryStep
end Lax109476Proofs.RamPointRecoveryStep
theorem Lax109476Proofs.RamPointRecoveryStep.step_spec:∀ (S N w D M m n k:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat),
  LT.lt k n→
    LT.lt
        (HAdd.hAdd
          (HMul.hMul ((4:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
              ((2:Nat))))
          ((3:Nat)))
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)→
      LT.lt (Lax109476Proofs.BinaryOptimization.steps D)
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) w)→
        LE.le
            (HMul.hMul
              (HAdd.hAdd D
                ((1:Nat)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) (Lax109476Proofs.BinaryOptimization.steps D)))
            M→
          LE.le M
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) S)→
            LE.le
                (HAdd.hAdd
                  (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                  ((1:Nat)))
                N→
              LE.le (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w→
                LT.lt D
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
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
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)→
                    LE.le
                        (Lax109476Proofs.RamStoredFeasibility.wordWidth
                          (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n
                            (HMul.hMul
                              ((4:Nat))
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                                ((2:Nat))))))
                        w→
                      (∀ (i:Fin m) (j:Fin n),
                          Lax109476Proofs.RationalArithmeticBounds.Height
                            (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
                        (∀ (i:Fin m),
                            Lax109476Proofs.RationalArithmeticBounds.Height
                              (@Lax109476.LinearProgram.Program.b Rat m n P i) M)→
                          (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (x j) M)→
                            (∀ (j:Fin n),
                                @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                                  (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                              @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                                  (@Lax109476.RationalCertificates.toReal m n P)
                                  (@Lax109476.RationalCertificates.realVector n x)→
                                (∀ (i:Fin n) (y:Fin n→ Real),
                                    @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                                        (@Lax109476.RationalCertificates.toReal m n P) y→
                                      (∀ (j:Fin n),
                                          @LT.lt (Fin n) (@instLTFin n) j i→
                                            @Eq Real (y j) (@Rat.cast Real Real.instRatCast (x j)))→
                                        @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (x i)) (y i))→
                                  (∀ (j:Fin n),
                                      And (@LE.le Rat Rat.instLE (x j) (@Nat.cast Rat Rat.instNatCast D))
                                        (LE.le (x j).den D))→
                                    Lax808846Proofs.Reasoning.Spec
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        ((2:Nat)) w)
                                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                                        And
                                          (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                            (@Lax109476Proofs.PointRecovery.prefixVector n x k) k σ)
                                          (And (@Eq Nat (σ.vars "minimum.bound") D)
                                            (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                                      Lax109476Proofs.RamPointRecoveryStep.step
                                      (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                                        And
                                          (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                            (@Lax109476Proofs.PointRecovery.prefixVector n x
                                              (HAdd.hAdd k
                                                ((1:Nat))))
                                            (HAdd.hAdd k
                                              ((1:Nat)))
                                            τ)
                                          (And (@Eq Nat (τ.vars "minimum.bound") D)
                                            (And (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)
                                              (@Eq Nat (τ.vars "point.k")
                                                (HAdd.hAdd (σ.vars "point.k")
                                                  ((1:Nat)))))))
                                      (HAdd.hAdd
                                        (Lax109476Proofs.RamPointRecoveryStep.coordinateCost S D M m n)
                                        ((25:Nat))):= @Lax109476Proofs.RamPointRecoveryStep.step_spec_native

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

theorem fit_eq_some {B v u:ℕ}:fit B v=some u↔ u=v∧ v < B:=by
  constructor
  · intro h
    by_cases hv:v < B
    · rw [fit,if_pos hv] at h
      exact ⟨(Option.some.inj h).symm,hv⟩
    · rw [fit,if_neg hv] at h; exact absurd h (by simp)
  · rintro ⟨rfl,h⟩; rw [fit,if_pos h]

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

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

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

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

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

namespace Lax109476Proofs.RationalReconstruction

def convergent:ℚ→ ℕ→ ℚ
  | a,0 => Int.floor a
  | a,k + 1 => Int.floor a + (convergent (Int.fract a)⁻¹ k)⁻¹

def reconstruct (l u:ℚ) (B:ℕ):Option ℚ:=
  ((List.range (2 * u.den.size + 1)).map (convergent u)).find?
    (fun q => decide (q.den≤ B∧ l≤ q∧ q≤ u))

end Lax109476Proofs.RationalReconstruction

end

section

namespace Lax109476Proofs.BinaryOptimization

open RationalReconstruction

def bisect (query:ℚ→ Bool):ℚ→ ℚ→ ℕ→ ℚ × ℚ
  | l,u,0 => (l,u)
  | l,u,k + 1 =>
    let old:=bisect query l u k
    let mid:=(old.1 + old.2) / 2
    if query mid then (old.1,mid) else (mid,old.2)

def minimum (query:ℚ→ Bool) (B:ℕ):Option ℚ:=
  let interval:=bisect query 0 B (steps B)
  reconstruct interval.1 interval.2 B

end Lax109476Proofs.BinaryOptimization

end

section

open scoped BigOperators

namespace Lax109476Proofs.CoordinateOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates

def coordinateCut {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (t:ℚ):
    Program ℚ (m + 1) n where
  A:=Fin.addCases P.A (fun _ k => if k=j then 1 else 0)
  b:=Fin.addCases P.b (fun _ => t)
  c:=P.c

def coordinateMinimum {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (B:ℕ):Option ℚ:=
  BinaryOptimization.minimum (fun t => RationalFeasibilityDecision.feasible (coordinateCut P j t)) B

end Lax109476Proofs.CoordinateOptimization

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates
open RationalMinima

def fixedPrefix {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ):
    Program ℚ (m + (n + n)) n where
  A:=Fin.addCases P.A (Fin.addCases
    (fun i j => if i.val < k then if j=i then 1 else 0 else 0)
    (fun i j => if i.val < k then if j=i then -1 else 0 else 0))
  b:=Fin.addCases P.b (Fin.addCases
    (fun i => if i.val < k then x i else 0)
    (fun i => if i.val < k then -x i else 0))
  c:=P.c

end Lax109476Proofs.LexicographicMinima

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization LexicographicBounds

def recoverPrefix {m n:ℕ} (P:Program ℚ m n) (B:ℕ):
    ℕ→ Option (Fin n→ ℚ)
  | 0 => some 0
  | k + 1 =>
    (recoverPrefix P B k).bind (fun old =>
      if h:k < n then
        (coordinateMinimum (fixedPrefix P old k) ⟨k,h⟩ B).map
          (fun v => Function.update old ⟨k,h⟩ v)
      else some old)

def recover {m n:ℕ} (P:Program ℚ m n) (B:ℕ):Option (Fin n→ ℚ):=
  recoverPrefix P B n

end Lax109476Proofs.PointRecovery

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

namespace Lax109476Proofs.RamSolverFrontEnd

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem clearing_word_guard (L w:ℕ) (hw:RamDecoder.wordWidth L≤ w):
    2 * (2 ^ L) ^ 2 + 3 < 2 ^ w:=by
  have he:2 * L + 3≤ w:=by unfold RamDecoder.wordWidth at hw; omega
  have hp:1≤ 2 ^ (2 * L):=Nat.one_le_pow _ _ (by decide)
  have hlarge:2 * (2 ^ L) ^ 2 + 3 < 2 ^ (2 * L + 3):=by
    rw [← pow_mul,Nat.mul_comm L 2,pow_add]
    norm_num
    omega
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) he)

end Lax109476Proofs.RamSolverFrontEnd

end

section

namespace Lax109476Proofs.RamPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRecoveryThreshold RamPointRecoveryStep RationalArithmeticBounds PointRecovery

structure Bounds (S N w D M m n:ℕ):Prop where
  midpoint:4 * M ^ 2 + 3 < 2 ^ w
  steps:BinaryOptimization.steps D < 2 ^ w
  interval:(D + 1) * 2 ^ BinaryOptimization.steps D≤ M
  height:M≤ 2 ^ S
  stack:RamRationalReconstruction.depthBound S + 1≤ N
  reconstruction:RamRationalReconstruction.wordWidth S≤ w
  cap:D < 2 ^ w
  dimensions:((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w
  query:RamStoredFeasibility.wordWidth (sizeBound m n (4 * M ^ 2))≤ w

def Invariant {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (D N:ℕ) (σ:Env):Prop:=
  Persistent P (prefixVector x (σ.vars "point.k")) (σ.vars "point.k") σ∧
    σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N∧ σ.vars "point.k" ≤ n

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recover_spec (S N w D M m n:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ)
    (b:Bounds S N w D M m n)
    (hA:∀ i j,Height (P.A i j) M) (hb:∀ i,Height (P.b i) M)
    (hxHeight:∀ j,Height (x j) M) (hc:∀ j,P.c j=0)
    (hx:PrimalFeasible (toReal P) (realVector x))
    (hlex:∀ i, ∀ y,PrimalFeasible (toReal P) y→
      (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i)
    (hxBound:∀ j,x j≤ D∧ (x j).den≤ D):
    Spec (2 ^ w) (fun σ => Persistent P (prefixVector x 0) 0 σ∧
      σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N) recover
      (fun _ τ => Persistent P x n τ∧ τ.vars "minimum.bound"=D∧ (τ.arrs "cf.stack").length=N)
      ((coordinateCost S D M m n + 29) * n + 6):=by
  have hnB:n < 2 ^ w:=by have:=b.dimensions; omega
  have hstep:Spec (2 ^ w) (fun σ => Invariant P x D N σ∧ σ.vars "point.k" < n)
      RamPointRecoveryStep.step (fun σ τ => Invariant P x D N τ∧ τ.vars "point.k"=σ.vars "point.k" + 1)
      (coordinateCost S D M m n + 25):=by
    rintro σ ⟨⟨hσP,hσD,hσN,hσk⟩,hi⟩
    obtain ⟨τ,hr,hτP,hτD,hτN,hτcounter⟩:=RamPointRecoveryStep.step_spec S N w D M m n (σ.vars "point.k") P x
      hi b.midpoint b.steps b.interval b.height b.stack b.reconstruction b.cap b.dimensions b.query
      hA hb hxHeight hc hx hlex hxBound σ ⟨hσP,hσD,hσN⟩
    have hτk:=hτP.1.2.2.2.2.2
    refine ⟨τ,hr, ⟨?_,hτD,hτN, ?_⟩,hτcounter⟩
    · simpa only [hτk] using hτP
    · rw [hτk]; omega
  have hlo:=Spec.forRangeZero "point.k" "point.n" (Invariant P x D N) n
    (coordinateCost S D M m n + 25) hnB
    (fun _ h => h.2.2.2) (fun _ h => h.1.1.2.2.2.2.1) hstep
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσP,hσD,hσN⟩
    refine ⟨?_,by simpa using hσD,by simpa using hσN,by simp⟩
    constructor
    · change State P (prefixVector x 0) 0 (σ.setVar "point.k" 0)
      rcases hσP.1 with ⟨hA,hb,hx,hm,hn,hk⟩
      exact ⟨hA,hb,hx,by simpa using hm,by simpa using hn,by simp⟩
    · exact hσP.2
  · rintro σ τ _ ⟨hτ,hτcounter⟩
    dsimp only [Invariant] at hτ
    rw [hτcounter] at hτ
    have he:prefixVector x n=x:=by funext j; simp [prefixVector,j.isLt]
    exact ⟨by simpa only [he] using hτ.1,hτ.2.1,hτ.2.2.1⟩

end Lax109476Proofs.RamPointRecovery

end

section

namespace Lax109476Proofs.RamPointRecoveryBounds

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RationalArithmeticBounds RamPointRecovery RamRecoveryThreshold

theorem threshold_size (m n S:ℕ):sizeBound m n (4 * (2 ^ S) ^ 2)=querySize m n S:=by
  have he:4 * (2 ^ S) ^ 2=2 ^ (2 * S + 2):=by
    rw [← pow_mul,pow_add]; norm_num; ring
  simp only [sizeBound,querySize,he,Nat.size_pow]

theorem resource_bounds (m n S C N D w:ℕ) (hD:D.size≤ C) (hS:4 * C + 2≤ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N) (hw:wordWidth m n S≤ w):
    Bounds S N w D (2 ^ S) m n:=by
  have hdecode:RamDecoder.wordWidth (S + 1)≤ w:=by unfold wordWidth at hw; omega
  have hclear:=RamSolverFrontEnd.clearing_word_guard (S + 1) w hdecode
  have hpow:2 ^ (S + 1)=2 ^ S * 2:=by rw [pow_succ]
  have hmid:4 * (2 ^ S) ^ 2 + 3 < 2 ^ w:=by rw [hpow] at hclear; nlinarith
  have hsteps:BinaryOptimization.steps D≤ 3 * C + 2:=by unfold BinaryOptimization.steps; omega
  have hstepsw:BinaryOptimization.steps D≤ w:=by unfold wordWidth RamDecoder.wordWidth at hw; omega
  have hdim:((m + (n + n)) + 1) * n + m + (n + n) + 4≤ w:=by unfold wordWidth at hw; omega
  have hDw:D.size≤ w:=by unfold wordWidth RamDecoder.wordWidth at hw; omega
  have hsmall:=Nat.lt_size_self D
  have hinterval:(D + 1) * 2 ^ BinaryOptimization.steps D≤ 2 ^ S:=by
    calc
      (D + 1) * 2 ^ BinaryOptimization.steps D≤ 2 ^ C * 2 ^ (3 * C + 2):=
        Nat.mul_le_mul ((by omega:D + 1≤ 2 ^ D.size).trans
          (Nat.pow_le_pow_right (by decide) hD)) (Nat.pow_le_pow_right (by decide) hsteps)
      _=2 ^ (4 * C + 2):=by rw [← pow_add]; congr 1; omega
      _≤ 2 ^ S:=Nat.pow_le_pow_right (by decide) hS
  refine ⟨hmid,hstepsw.trans_lt (Nat.lt_two_pow_self (n:=w)),hinterval,le_rfl,hN, ?_,
    (Nat.lt_size_self D).trans_le (Nat.pow_le_pow_right (by decide) hDw),
    hdim.trans_lt (Nat.lt_two_pow_self (n:=w)), ?_⟩
  · unfold wordWidth at hw; omega
  · rw [threshold_size]; unfold wordWidth at hw; omega

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recover_bounded_spec (m n S C N D w:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ)
    (hD:D.size≤ C) (hS:4 * C + 2≤ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N) (hw:wordWidth m n S≤ w)
    (hA:∀ i j,Height (P.A i j) (2 ^ S)) (hb:∀ i,Height (P.b i) (2 ^ S))
    (hxHeight:∀ j,Height (x j) (2 ^ S)) (hc:∀ j,P.c j=0)
    (hx:PrimalFeasible (toReal P) (realVector x))
    (hlex:∀ i, ∀ y,PrimalFeasible (toReal P) y→
      (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i)
    (hxBound:∀ j,x j≤ D∧ (x j).den≤ D):
    Spec (2 ^ w) (fun σ => Persistent P (PointRecovery.prefixVector x 0) 0 σ∧
      σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N) recover
      (fun _ τ => Persistent P x n τ∧ τ.vars "minimum.bound"=D∧ (τ.arrs "cf.stack").length=N)
      (instructionBound m n S C):=by
  have hr:=recover_spec S N w D (2 ^ S) m n P x (resource_bounds m n S C N D w hD hS hN hw)
    hA hb hxHeight hc hx hlex hxBound
  refine hr.mono ?_
  unfold RamPointRecoveryStep.coordinateCost instructionBound queryCost
  dsimp only [RamRecoveryThreshold.instructionBound]
  rw [Nat.size_pow,threshold_size]
  simp only [Nat.add_assoc,Nat.reduceAdd]
  have hsteps:BinaryOptimization.steps D≤ 3 * C + 2:=by unfold BinaryOptimization.steps; omega
  gcongr

end Lax109476Proofs.RamPointRecoveryBounds

end

theorem solution:∀ (m n S C N D w:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat),
  Nat.le D.size C→
    Nat.le
        (Nat.add
          (Nat.mul ((4:Nat))
            C)
          ((2:Nat)))
        S→
      Nat.le
          (Nat.add (Lax109476Proofs.RamRationalReconstruction.depthBound S)
            ((1:Nat)))
          N→
        Nat.le (Lax109476Proofs.RamPointRecoveryBounds.wordWidth m n S) w→
          (∀ (i:Fin m) (j:Fin n),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j)
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) S))→
            (∀ (i:Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i)
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) S))→
              (∀ (j:Fin n),
                  Lax109476Proofs.RationalArithmeticBounds.Height (x j)
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) S))→
                (∀ (j:Fin n),
                    @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                      (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                  @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                      (@Lax109476.RationalCertificates.toReal m n P) (@Lax109476.RationalCertificates.realVector n x)→
                    (∀ (i:Fin n) (y:Fin n→ Real),
                        @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                            (@Lax109476.RationalCertificates.toReal m n P) y→
                          (∀ (j:Fin n),
                              @LT.lt (Fin n) (@instLTFin n) j i→
                                @Eq Real (y j) (@Rat.cast Real Real.instRatCast (x j)))→
                            @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (x i)) (y i))→
                      (∀ (j:Fin n),
                          And (@LE.le Rat Rat.instLE (x j) (@Nat.cast Rat Rat.instNatCast D))
                            (Nat.le (x j).den D))→
                        Lax808846Proofs.Reasoning.Spec
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            ((2:Nat)) w)
                          (fun (σ:Lax808846Proofs.Imp.Env) =>
                            And
                              (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                (@Lax109476Proofs.PointRecovery.prefixVector n x
                                  ((0:Nat)))
                                ((0:Nat)) σ)
                              (And (@Eq Nat (σ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                          Lax109476Proofs.RamPointRecovery.recover
                          (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                            And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x n τ)
                              (And (@Eq Nat (τ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)))
                          (Lax109476Proofs.RamPointRecoveryBounds.instructionBound m n S C):= @Lax109476Proofs.RamPointRecoveryBounds.recover_bounded_spec
