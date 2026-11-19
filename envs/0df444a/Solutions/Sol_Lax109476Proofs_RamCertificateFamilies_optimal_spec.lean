-- Prove2me | solution 1 for Lax109476Proofs.RamCertificateFamilies.optimal_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:44.78072+00:00
-- url     : https://prove2.me/submissions/129ee75b-9fa8-441d-8344-126b8c695d49

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamPairSelector_selectEntry_spec_native
import Theorems.Thm_Lax109476Proofs_RamPairSelector_selectBound_spec_native
import Theorems.Thm_Lax109476Proofs_RamCertificateBuilder_buildSystem_spec_native

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

namespace Lax109476Proofs.RamPairSelector
end Lax109476Proofs.RamPairSelector
theorem Lax109476Proofs.RamPairSelector.selectEntry_spec:∀ (B M m n:Nat) (P:Lax109476.LinearProgram.Program Int m n)
  (i:
    Fin
      (HAdd.hAdd m
        (HAdd.hAdd n
          ((2:Nat)))))
  (j:Fin (HAdd.hAdd n m)),
  LE.le ((1:Nat)) M→
    LT.lt M B→
      LT.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd (HMul.hMul m n)
                (HMul.hMul
                  ((2:Nat)) m))
              (HMul.hMul
                ((2:Nat)) n))
            ((8:Nat)))
          B→
        (∀ (r:Fin m) (s:Fin n),LE.le (@Lax109476.LinearProgram.Program.A Int m n P r s).natAbs M)→
          (∀ (r:Fin m),LE.le (@Lax109476.LinearProgram.Program.b Int m n P r).natAbs M)→
            (∀ (s:Fin n),LE.le (@Lax109476.LinearProgram.Program.c Int m n P s).natAbs M)→
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                    (And
                      (@Eq Nat (σ.vars "query.row")
                        (@Fin.val
                          (HAdd.hAdd m
                            (HAdd.hAdd n
                              ((2:Nat))))
                          i))
                      (@Eq Nat (σ.vars "query.col")
                        (@Fin.val (HAdd.hAdd n m) j))))
                Lax109476Proofs.RamPairSelector.selectEntry
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                    (Lax109476Proofs.RamRational.FractionOutput
                      (@Int.cast Rat Rat.instIntCast (@Lax109476Proofs.CertificateFamilyEntries.pairEntry m n P i j))
                      τ))
                ((72:Nat)):= @Lax109476Proofs.RamPairSelector.selectEntry_spec_native
namespace Lax109476Proofs.RamPairSelector
end Lax109476Proofs.RamPairSelector
theorem Lax109476Proofs.RamPairSelector.selectBound_spec:∀ (B M m n:Nat) (P:Lax109476.LinearProgram.Program Int m n)
  (i:
    Fin
      (HAdd.hAdd m
        (HAdd.hAdd n
          ((2:Nat))))),
  LE.le ((1:Nat)) M→
    LT.lt M B→
      LT.lt
          (HAdd.hAdd (HAdd.hAdd m n)
            ((4:Nat)))
          B→
        (∀ (r:Fin m),LE.le (@Lax109476.LinearProgram.Program.b Int m n P r).natAbs M)→
          (∀ (s:Fin n),LE.le (@Lax109476.LinearProgram.Program.c Int m n P s).natAbs M)→
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                  (@Eq Nat (σ.vars "query.row")
                    (@Fin.val
                      (HAdd.hAdd m
                        (HAdd.hAdd n
                          ((2:Nat))))
                      i)))
              Lax109476Proofs.RamPairSelector.selectBound
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                  (Lax109476Proofs.RamRational.FractionOutput
                    (@Int.cast Rat Rat.instIntCast (@Lax109476Proofs.CertificateFamilyEntries.pairRhs m n P i)) τ))
              ((40:Nat)):= @Lax109476Proofs.RamPairSelector.selectBound_spec_native
namespace Lax109476Proofs.RamCertificateBuilder
end Lax109476Proofs.RamCertificateBuilder
theorem Lax109476Proofs.RamCertificateBuilder.buildSystem_spec:∀ (B M m n r s matrixCost boundCost:Nat) (P:Lax109476.LinearProgram.Program Int m n)
  (F:Lax109476.LinearProgram.Program Int r s) (matrixSelector boundSelector:Lax808846Proofs.Imp.Com),
  LE.le ((1:Nat)) M→
    LT.lt M B→
      LT.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd (HMul.hMul r s)
                r)
              s)
            ((4:Nat)))
          B→
        (∀ (i:Fin r) (j:Fin s),LE.le (@Lax109476.LinearProgram.Program.A Int r s F i j).natAbs M)→
          (∀ (i:Fin r),LE.le (@Lax109476.LinearProgram.Program.b Int r s F i).natAbs M)→
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
                                          (HMul.hMul r s) σ)
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.b" r σ)))
                                  (Lax109476Proofs.RamCertificateBuilder.buildSystem matrixSelector boundSelector)
                                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                                      (@Lax109476Proofs.RamEquationData.Data r s F τ))
                                  (HAdd.hAdd
                                    (HAdd.hAdd
                                      (HMul.hMul
                                        (HAdd.hAdd matrixCost
                                          ((70:Nat)))
                                        (HMul.hMul r s))
                                      (HMul.hMul
                                        (HAdd.hAdd boundCost
                                          ((58:Nat)))
                                        r))
                                    ((62:Nat))):= @Lax109476Proofs.RamCertificateBuilder.buildSystem_spec_native

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

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

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

theorem Spec.mono (h:Spec B P c Q K) (hK:K≤ K'):Spec B P c Q K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr.mono hK,hq⟩

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

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

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

namespace Fill

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

end Lax109476Proofs.RamCertificateSource

end

section

namespace Lax109476Proofs.RamCertificateMetadata

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamCertificateSource RamCertificateContext

theorem optimal_spec (B m n:ℕ) (P:Program ℤ m n) (hB:2 * m + 2 * n + 4 < B):
    Spec B (Data P) optimal (fun _ τ => Context P (m + (n + 2)) (n + m) τ) 10:=by
  have h1:1 < B:=by omega
  have h2:2 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hsum:m + n < B:=by omega
  have hn2:n + 2 < B:=by omega
  have hr:m + (n + 2) < B:=by omega
  have hbase:Spec B (fun σ => σ.vars "source.m"=m∧ σ.vars "source.n"=n) optimal
      (fun _ τ => τ.vars "system.m"=m + (n + 2)∧ τ.vars "system.n"=n + m) 10:=by
    rintro σ ⟨hσm,hσn⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat:=c0 n; let c2:Nat:=c0 m (c1 ((2:Nat))); let c3:Nat:=c1 m; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "system.m") c2) (@Eq Nat (Env.vars τ "system.n") c3)) σ; let c5:Nat:=c0 (Env.vars σ "source.n") ((2:Nat)); let c6:Nat:=c0 (Env.vars σ "source.m") c5; let c7:Env:=Env.setVar σ "system.m" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "source.n"; let c10:Nat:=c8 "source.m"; let c11:Nat:=c0 c9 c10; let c12:Env:=Env.setVar c7 "system.n" c11; let c13:Nat→ Nat:=c0 ((1:Nat)); let c14:Expr:=Expr.add (Expr.var "source.n") (Expr.lit ((2:Nat))); let c15:Expr:=Expr.add (Expr.var "source.m") c14; let c16:Nat:=c13 (Expr.size c15); let c17:Nat:=c13 (Expr.size (Expr.add (Expr.var "source.n") (Expr.var "source.m"))); let c18:String→ Nat:=Env.vars c12; @Exists.intro Env (fun (σ':Env) => And (Run B optimal σ σ' ((10:Nat))) (c4 σ')) c12 (@And.intro (Run B optimal σ c12 ((10:Nat))) (c4 c12) (RunStep.mono B optimal σ c12 (c0 c16 c17) ((10:Nat)) (RunStep.seq B (Com.assign "system.m" c15) (Com.assign "system.n" (Expr.add (Expr.var "source.n") (Expr.var "source.m"))) σ c7 c12 c16 c17 (RunStep.assign B σ "system.m" c15 c6 (RunStep.eval_add B σ (Expr.var "source.m") c14 (Env.vars σ "source.m") c5 (RunStep.eval_var B σ "source.m" (?nAX_g5019_0_0_0)) (RunStep.eval_add B σ (Expr.var "source.n") (Expr.lit ((2:Nat))) (Env.vars σ "source.n") ((2:Nat)) (RunStep.eval_var B σ "source.n" (?nAX_g5019_0_0_1)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g5019_0_0_2)) (?nAX_g5019_0_0_3))) (RunStep.assign B c7 "system.n" (Expr.add (Expr.var "source.n") (Expr.var "source.m")) c11 (RunStep.eval_add B c7 (Expr.var "source.n") (Expr.var "source.m") c9 c10 (RunStep.eval_var B c7 "source.n" (?nAX_g5019_0_0_4)) (RunStep.eval_var B c7 "source.m" (?nAX_g5019_0_0_5)) (?nAX_g5019_0_0_6)))) (?nAX_g5019_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5019_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5019_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ ⟨hσ.2.2.2.1,hσ.2.2.2.2⟩
  refine ⟨τ,hr,data_frame hr P hσ ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha t ht; change a ++ t∉ ([]:List String); simp

end Lax109476Proofs.RamCertificateMetadata

end

section

namespace Lax109476Proofs.CertificateFamilyEntries

open Lax109476.LinearProgram
open CertificateFamilyPrograms IntegerCertificates CertificateSearch IndexedPointRecovery

set_option maxHeartbeats 0 in
theorem pairEntry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (n + 2))) (j:Fin (n + m)):
    pairEntry P i j=(optimal P).A i j:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    all_goals simp [-Fin.natAdd_eq_addNat,pairEntry,optimal,reindexProgram,pairRows,pairMatrix,i.isLt,j.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,pairEntry,optimal,reindexProgram,pairRows,pairMatrix,i.isLt,j.isLt]
      all_goals omega
    · fin_cases i
      all_goals refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,pairEntry,optimal,reindexProgram,pairRows,pairMatrix,
        finTwoEquiv,j.isLt,Nat.add_assoc]
      all_goals omega

theorem pairRhs_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (n + 2))):
    pairRhs P i=(optimal P).b i:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [pairRhs,optimal,reindexProgram,pairRows,pairBound,i.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [-Fin.natAdd_eq_addNat,pairRhs,optimal,reindexProgram,pairRows,pairBound,i.isLt]
    · fin_cases i
      all_goals simp [-Fin.natAdd_eq_addNat,pairRhs,optimal,reindexProgram,pairRows,pairBound,finTwoEquiv]
      all_goals omega

end Lax109476Proofs.CertificateFamilyEntries

end

section

namespace Lax109476Proofs.CertificateFamilyHeight

open Lax109476.LinearProgram
open CertificateFamilyPrograms CertificateFamilyEntries

theorem optimal_A_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M)
    (hc:∀ j, (P.c j).natAbs≤ M):∀ i j, ((optimal P).A i j).natAbs≤ M:=by
  intro i j
  rw [← pairEntry_eq]
  unfold pairEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem optimal_b_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hb:∀ i, (P.b i).natAbs≤ M) (hc:∀ j, (P.c j).natAbs≤ M):
    ∀ i, ((optimal P).b i).natAbs≤ M:=by
  intro i
  rw [← pairRhs_eq]
  unfold pairRhs
  split_ifs <;> simp_all [Int.natAbs_neg]

end Lax109476Proofs.CertificateFamilyHeight

end

section

namespace Lax109476Proofs.RamCertificateFamilies

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateSource CertificateFamilyPrograms CertificateFamilyEntries

theorem withMetadata_spec (B m n r s metadataCost buildCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (metadata matrixSelector boundSelector:Com)
    (hmetadata:Spec B (Data P) metadata (fun _ τ => RamCertificateContext.Context P r s τ) metadataCost)
    (hbuild:Spec B (fun σ => RamCertificateContext.Context P r s σ∧ Extents "system.A" (r * s) σ∧ Extents "system.b" r σ)
      (RamCertificateBuilder.buildSystem matrixSelector boundSelector)
      (fun _ τ => Data P τ∧ RamEquationData.Data F τ) buildCost):
    Spec B (Input P r s) (withMetadata metadata matrixSelector boundSelector)
      (fun _ τ => Data P τ∧ RamEquationData.Data F τ) (metadataCost + buildCost):=by
  rintro σ ⟨hσData,hσA,hσb⟩
  obtain ⟨τ,hr₁,hτContext⟩:=hmetadata σ hσData
  obtain ⟨υ,hr₂,hυ⟩:=hbuild τ ⟨hτContext,
    RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσA,
    RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

theorem optimal_spec (B M m n:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hMB:M < B) (hSource:m * n + 2 * m + 2 * n + 8 < B)
    (hSystem:(m + (n + 2)) * (n + m) + (m + (n + 2)) + (n + m) + 4 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M)
    (hc:∀ j, (P.c j).natAbs≤ M):
    Spec B (Input P (m + (n + 2)) (n + m)) optimal
      (fun _ τ => Data P τ∧ RamEquationData.Data (CertificateFamilyPrograms.optimal P) τ)
      (142 * ((m + (n + 2)) * (n + m)) + 98 * (m + (n + 2)) + 72):=by
  have hbuild:=RamCertificateBuilder.buildSystem_spec B M m n (m + (n + 2)) (n + m) 72 40 P
    (CertificateFamilyPrograms.optimal P) RamPairSelector.selectEntry RamPairSelector.selectBound hM hMB hSystem
    (CertificateFamilyHeight.optimal_A_bound P M hA hb hc) (CertificateFamilyHeight.optimal_b_bound P M hb hc)
    (fun i j => by simpa only [pairEntry_eq] using RamPairSelector.selectEntry_spec B M m n P i j hM hMB hSource hA hb hc)
    (fun i => by simpa only [pairRhs_eq] using RamPairSelector.selectBound_spec B M m n P i hM hMB (by omega) hb hc)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl)
  exact (withMetadata_spec B m n (m + (n + 2)) (n + m) 10 _ P (CertificateFamilyPrograms.optimal P)
    RamCertificateMetadata.optimal RamPairSelector.selectEntry RamPairSelector.selectBound
    (RamCertificateMetadata.optimal_spec B m n P (by omega)) hbuild).mono (by omega)

end Lax109476Proofs.RamCertificateFamilies

end

theorem solution:∀ (B M m n:ℕ) (P:Lax109476.LinearProgram.Program ℤ m n),
  1≤ M→
    M < B→
      m * n + 2 * m + 2 * n + 8 < B→
        (m + (n + 2)) * (n + m) + (m + (n + 2)) + (n + m) + 4 < B→
          (∀ (i:Fin m) (j:Fin n), (P.A i j).natAbs≤ M)→
            (∀ (i:Fin m), (P.b i).natAbs≤ M)→
              (∀ (j:Fin n), (P.c j).natAbs≤ M)→
                Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamCertificateFamilies.Input P (m + (n + 2)) (n + m))
                  Lax109476Proofs.RamCertificateFamilies.optimal
                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamCertificateSource.Data P τ∧
                      Lax109476Proofs.RamEquationData.Data (Lax109476Proofs.CertificateFamilyPrograms.optimal P) τ)
                  (142 * ((m + (n + 2)) * (n + m)) + 98 * (m + (n + 2)) + 72):= @Lax109476Proofs.RamCertificateFamilies.optimal_spec
