-- Prove2me | solution 1 for Lax263307Proofs.NativeOriginalAccuracy.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:59.726353+00:00
-- url     : https://prove2.me/submissions/b2a573c4-f09f-4a57-83a4-4c383d38c675

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces

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

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_get {B:ℕ} {a:String} {i:Expr} {σ:Env} {k v:ℕ}
    (hi:i.evalB B σ=some k) (hk:(σ.arrs a)[k]?=some v) (hv:v < B):
    (Expr.get a i).evalB B σ=some v:=by
  rw [Expr.evalB,hi,Option.bind_some,hk,Option.bind_some,fit_self hv]

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

namespace Lax263307Proofs.NativeFrontend

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.WeightedIndependentSet

theorem tail_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w:Fin n→ ℚ) (ε:ℚ):(tailInput G w ε).length=n*n + 3*n + 3:=by
  simp [tailInput,encodeParameters,encodeRational,List.length_flatten,List.length_flatMap,
    List.sum_ofFn,Finset.sum_const,Nat.mul_comm,Nat.add_assoc]

end Lax263307Proofs.NativeFrontend

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

namespace Lax263307Proofs.NativeOriginalAccuracy

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeFrontend

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (weights:Fin n→ ℚ) (ε:ℚ) (hB:n*n+3*n+3< B)
    (hn:ε.num.natAbs< B) (hd:ε.den< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ Prefix (tailInput G weights ε) "input.data" σ)
      command (fun _ τ => τ.vars "accuracy.n"=ε.num.natAbs∧ τ.vars "accuracy.d"=ε.den) 18:=by
  rintro σ ⟨horder,hinput⟩
  have hnB:n< B:=by nlinarith only [hB]
  have hvar:(Expr.var "input.n").evalB B σ=some n:=by
    rw [evalB_var_iff]; exact ⟨horder.symm,horder ▸ hnB⟩
  let offset:=n*n+3*n
  let ν:=σ.setVar "source.accuracy" offset
  have r1:Run B (.assign "source.accuracy"
      (.add (.mul (.var "input.n") (.var "input.n")) (.mul (.lit 3) (.var "input.n")))) σ ν 8:=
    Run.assign (evalB_bin (op:=.add)
      (evalB_bin (op:=.mul) hvar hvar (by change n*n< B; omega))
      (evalB_bin (op:=.mul) (evalB_lit (show 3< B by omega)) hvar (by change 3*n< B; omega))
      (by change offset< B; dsimp [offset]; omega))
  have hnum:(tailInput G weights ε)[offset+1]?=some ε.num.natAbs:=by
    have hmatrix:(NativeWeightReduction.adjacency G).length=n*n:=NativeWeightReduction.adjacency_length G
    have hw:((List.ofFn weights).flatMap encodeRational).length=3*n:=by
      simp [encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]
    change (NativeWeightReduction.adjacency G++((List.ofFn weights).flatMap encodeRational++encodeRational ε))[offset+1]?=_
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hmatrix]
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hw]
    have hi:offset+1-n*n-3*n=1:=by dsimp [offset]; omega
    rw [hi]; rfl
  have hden:(tailInput G weights ε)[offset+2]?=some ε.den:=by
    have hmatrix:(NativeWeightReduction.adjacency G).length=n*n:=NativeWeightReduction.adjacency_length G
    have hw:((List.ofFn weights).flatMap encodeRational).length=3*n:=by
      simp [encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]
    change (NativeWeightReduction.adjacency G++((List.ofFn weights).flatMap encodeRational++encodeRational ε))[offset+2]?=_
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hmatrix]
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hw]
    have hi:offset+2-n*n-3*n=2:=by dsimp [offset]; omega
    rw [hi]; rfl
  have hindex1:offset+1<(tailInput G weights ε).length:=by rw [tail_length]; dsimp [offset]; omega
  have hindex2:offset+2<(tailInput G weights ε).length:=by rw [tail_length]; dsimp [offset]; omega
  have hnumσ:=(hinput _ hindex1).trans (by simpa only [List.getElem?_eq_getElem hindex1] using hnum)
  have hdenσ:=(hinput _ hindex2).trans (by simpa only [List.getElem?_eq_getElem hindex2] using hden)
  let μ:=ν.setVar "accuracy.n" ε.num.natAbs
  have r2:Run B (.assign "accuracy.n" (.get "input.data" (.add (.var "source.accuracy") (.lit 1)))) ν μ 5:=
    Run.assign (evalB_get
      (evalB_bin (op:=.add) (by rw [evalB_var_iff]; simp [ν]; dsimp [offset]; omega)
        (evalB_lit (show 1< B by omega)) (by change offset+1< B; dsimp [offset]; omega)) hnumσ hn)
  let τ:=μ.setVar "accuracy.d" ε.den
  have r3:Run B (.assign "accuracy.d" (.get "input.data" (.add (.var "source.accuracy") (.lit 2)))) μ τ 5:=
    Run.assign (evalB_get
      (evalB_bin (op:=.add) (by rw [evalB_var_iff]; simp [μ,ν]; dsimp [offset]; omega)
        (evalB_lit (show 2< B by omega)) (by change offset+2< B; dsimp [offset]; omega)) hdenσ hd)
  exact ⟨τ,r1.seq (r2.seq r3),by simp [τ,μ],by simp [τ]⟩

end Lax263307Proofs.NativeOriginalAccuracy

end

theorem solution:∀ {n:Nat} (B:Nat) (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
  (weights:Fin n→ Rat) (ε:Rat),
  Nat.lt
      (Nat.add
        (Nat.add (Nat.mul n n)
          (Nat.mul ((3:Nat))
            n))
        ((3:Nat)))
      B→
    Nat.lt ε.num.natAbs B→
      Nat.lt ε.den B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ.vars "input.n") n)
              (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeFrontend.tailInput n G inst weights ε)
                "input.data" σ))
          Lax263307Proofs.NativeOriginalAccuracy.command
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "accuracy.n") ε.num.natAbs) (@Eq Nat (τ.vars "accuracy.d") ε.den))
          ((18:Nat)):= @Lax263307Proofs.NativeOriginalAccuracy.command_spec
