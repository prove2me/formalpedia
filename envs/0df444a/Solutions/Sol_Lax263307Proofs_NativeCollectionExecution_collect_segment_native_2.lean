-- Prove2me | solution 2 for Lax263307Proofs.NativeCollectionExecution.collect_segment_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:25:38.707749+00:00
-- url     : https://prove2.me/submissions/11226aaa-9414-482a-b248-b32045f31283

import Mathlib.Tactic
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax263307Proofs_NativeCollectionExecution_iterations_native

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

namespace Lax263307Proofs.NativeCollectionExecution
end Lax263307Proofs.NativeCollectionExecution
theorem Lax263307Proofs.NativeCollectionExecution.iterations:∀ {n:Nat} {ι:Type} (D k r fuel S h T childSteps childTime:Nat) (cfg:Lax263307Proofs.NativeCoreMachine.Config)
  (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x:Fin n→ NNRat)
  (parts:ι→ Finset (Fin n)) (order:List ι) (A:Finset (Fin n)) (extent:String→ Nat) (front:List Nat)
  (base:Lax808846Proofs.Imp.Env)
  (child:(C:Finset (Fin n))→ Nat→ Option (Finset (Fin (@Finset.card (Fin n) C)))),
  Nat.lt ((0:Nat)) n→
    Nat.lt ((0:Nat)) D→
      (∀ (v:Fin n),
          Lax263307Proofs.NativeSignedArithmetic.Bounded
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) h)
            (@NNRat.cast Rat Rat.instNNRatCast (x v)))→
        ∀ (w:Nat),
          Nat.le (Lax263307Proofs.NativeComponentDecision.wordHeight n D k h) w→
            Nat.le (@List.length ι order)
                (HAdd.hAdd n
                  ((1:Nat)))→
              Nat.lt
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) n)
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w)→
                Nat.lt
                    (HAdd.hAdd
                      (HAdd.hAdd
                        (HAdd.hAdd
                          (HAdd.hAdd
                            (HAdd.hAdd
                              (HAdd.hAdd
                                (HAdd.hAdd
                                  (HAdd.hAdd
                                    (HAdd.hAdd (@List.length Nat front)
                                      (HMul.hMul S
                                        (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                                    (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                  (HMul.hMul n n))
                                (HMul.hMul
                                  ((2:Nat)) n))
                              (HMul.hMul
                                ((2:Nat)) (@List.length ι order)))
                            T)
                          fuel)
                        (HMul.hMul
                          ((3:Nat))
                          (Lax263307Proofs.NativeCatalogMetadata.N n r)))
                      ((80:Nat)))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  (∀ (i:ι),
                      @Membership.mem ι (List ι) (@List.instMembership ι) order i→
                        Nat.le
                          (Lax263307.ComputedRounding.target
                            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                              (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                              (@Nat.cast Rat Rat.instNatCast D))
                            (∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v)))
                          T)→
                    (∀ (a:String),
                        @Membership.mem String (List String) (@List.instMembership String)
                            (Lax263307Proofs.NativeCoreMachine.frameArrays cfg) a→
                          @Eq Nat (extent a) S)→
                      Nat.le
                          (HAdd.hAdd
                            (HAdd.hAdd (@List.length Nat front)
                              (HMul.hMul S
                                (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                            (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                          (extent "recursion.frames")→
                        Nat.le (HMul.hMul n n)
                            (extent "child.graph")→
                          Nat.le (HMul.hMul n n)
                              (extent "search.graph")→
                            Nat.le n (extent "subset.bits")→
                              Nat.le n (extent "restrict.vertices")→
                                Nat.lt
                                    (HMul.hMul
                                      ((3:Nat)) n)
                                    (extent "lp.word")→
                                  Nat.le
                                      (HMul.hMul
                                        ((3:Nat)) n)
                                      (extent "sum.input")→
                                    Nat.le
                                        (HMul.hMul
                                          ((3:Nat))
                                          (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                        (extent "lp.input")→
                                      Nat.le
                                          (HMul.hMul
                                            ((3:Nat))
                                            (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                          (extent "round.normal")→
                                        (∀ (i:ι),
                                            @Membership.mem ι (List ι) (@List.instMembership ι) order i→
                                              @LT.lt Rat Rat.instLT
                                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                    (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                        (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                        (@Nat.cast Rat Rat.instNatCast D))
                                                      (@Nat.cast Rat Rat.instNatCast k))
                                                    (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                      (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                                      (@Nat.cast Rat Rat.instNatCast n)))
                                                  (∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v))→
                                                ∀ (σ:Lax808846Proofs.Imp.Env),
                                                  @Lax263307Proofs.NativeCollectionExecution.Invariant n
                                                      (@HPow.hPow Nat Nat Nat
                                                        (@instHPow Nat Nat
                                                          (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                        ((2:Nat)) w)
                                                      D k r fuel S G inst x (@List.map ι (Finset (Fin n)) parts order) A
                                                      extent front base σ→
                                                    @Lax263307Proofs.NativeRestrictionRead.Data n G inst
                                                        (fun (v:Fin n) => @NNRat.cast Rat Rat.instNNRatCast (x v))
                                                        (parts i) σ→
                                                      @Eq Nat (σ.vars "component.mask")
                                                          (@Lax263307Proofs.NativeMasks.mask n (parts i))→
                                                        @Eq Nat (σ.vars "component.target")
                                                            (Lax263307.ComputedRounding.target
                                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                (@OfNat.ofNat Rat (nat_lit 1)
                                                                  (@Rat.instOfNat (nat_lit 1)))
                                                                (@Nat.cast Rat Rat.instNatCast D))
                                                              (∑ v∈ parts i,
                                                                @NNRat.cast Rat Rat.instNNRatCast (x v)))→
                                                          @Eq Nat (σ.vars "machine.running")
                                                              ((1:Nat))→
                                                            @Eq Nat (σ.vars "machine.phase")
                                                                ((11:Nat))→
                                                              @Lax263307Proofs.NativeCollectionChild.Recursive n
                                                                (@HPow.hPow Nat Nat Nat
                                                                  (@instHPow Nat Nat
                                                                    (@NPow.toPow Nat
                                                                      (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                  ((2:Nat))
                                                                  w)
                                                                S fuel childSteps childTime cfg G inst (parts i)
                                                                (Lax263307.ComputedRounding.target
                                                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                    (@OfNat.ofNat Rat (nat_lit 1)
                                                                      (@Rat.instOfNat (nat_lit 1)))
                                                                    (@Nat.cast Rat Rat.instNatCast D))
                                                                  (∑ v∈ parts i,
                                                                    @NNRat.cast Rat Rat.instNNRatCast (x v)))
                                                                front σ
                                                                (child (parts i)
                                                                  (Lax263307.ComputedRounding.target
                                                                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                      (@OfNat.ofNat Rat (nat_lit 1)
                                                                        (@Rat.instOfNat (nat_lit 1)))
                                                                      (@Nat.cast Rat Rat.instNatCast D))
                                                                    (∑ v∈ parts i,
                                                                      @NNRat.cast Rat Rat.instNNRatCast (x v)))))→
                                          @Lax263307Proofs.NativeCollectionTrace.Iterations n ι
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              ((2:Nat)) w)
                                            cfg
                                            (@Lax263307Proofs.NativeCollectionExecution.Invariant n
                                              (@HPow.hPow Nat Nat Nat
                                                (@instHPow Nat Nat
                                                  (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                ((2:Nat)) w)
                                              D k r fuel S G inst x (@List.map ι (Finset (Fin n)) parts order) A extent
                                              front base)
                                            (@Lax263307Proofs.NativeCollectionExecution.Cut n r A) parts
                                            (fun (i:ι) =>
                                              @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                                                (Lax263307.ComputedRounding.target
                                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                    (@Nat.cast Rat Rat.instNatCast D))
                                                  (∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v)))
                                                ((1:Nat)))
                                            (@Lax263307.ComputedRounding.answer n ι
                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                (@Nat.cast Rat Rat.instNatCast D))
                                              k (fun (i:ι) => ∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v))
                                              fun (i:ι) (t:Nat) =>
                                              @Option.map (Finset (Fin (@Finset.card (Fin n) (parts i))))
                                                (Finset (Fin n))
                                                (fun (I:Finset (Fin (@Finset.card (Fin n) (parts i)))) =>
                                                  @Finset.image (Fin (@Finset.card (Fin n) (parts i))) (Fin n)
                                                    (instDecidableEqFin n)
                                                    (@DFunLike.coe
                                                      (@OrderEmbedding (Fin (@Finset.card (Fin n) (parts i))) (Fin n)
                                                        (@instLEFin (@Finset.card (Fin n) (parts i))) (@instLEFin n))
                                                      (Fin (@Finset.card (Fin n) (parts i)))
                                                      (fun (x:Fin (@Finset.card (Fin n) (parts i))) => Fin n)
                                                      (@instFunLikeOrderEmbedding (Fin (@Finset.card (Fin n) (parts i)))
                                                        (Fin n) (@instLEFin (@Finset.card (Fin n) (parts i)))
                                                        (@instLEFin n))
                                                      (@Lax263307.ComputedSeparators.label n (parts i)))
                                                    I)
                                                (child (parts i) t))
                                            order
                                            (HAdd.hAdd childSteps
                                              ((5:Nat)))
                                            (Lax263307Proofs.NativeCollectionExecution.partCost cfg n r S h childTime):= @Lax263307Proofs.NativeCollectionExecution.iterations_native

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

theorem Expr.lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):v < B:=(eval_and_lt_of_evalB h).2

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

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

theorem evalB_condLt {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.lt e f).evalB B σ=some (decide (m < n)):=by
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

theorem Run.ite_false {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_false hb hbs⟩

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

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "mask.i"≤ n∧
  Prefix (encodeOutput I) "subset.bits" σ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

end Lax263307Proofs.NativeMasks

end

section

namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target index cursor count:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars count=xs.length
  counter:σ.vars index≤ xs.length
  position:σ.vars cursor=front.length+σ.vars index
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars index)) target σ

end Lax263307Proofs.NativeAppendBuffer

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

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def command:Com:=.ite (.eq (.var "recursion.return.tag") (.lit 1)) liftCommand
  (.assign "lift.mask" (.lit 0))

end Lax263307Proofs.NativeChildReturn

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeComponentControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks ComputedSeparators

theorem finish_spec {n:ℕ} (B ret:ℕ) (S:Finset (Fin n)) (hB:ret+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "component.union"=mask S) (finish ret)
      (fun _ τ => NativeTargetDriver.Reply (some S) τ∧ τ.vars "machine.phase"=ret) 6:=by
  have hmask:mask S< B:=(mask_bound S).trans hm
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:= @NativeTargetDriver.Reply n (@some (Finset (Fin n)) S); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (@Eq Nat (Env.vars τ "machine.phase") ret)) σ; let c2:Env:=Env.setVar σ "recursion.return.tag" ((1:Nat)); let c3:Nat:=Env.vars c2 "component.union"; let c4:Env:=Env.setVar c2 "recursion.return.mask" c3; let c5:Env:=Env.setVar c4 "machine.phase" ret; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "component.union")); let c10:Nat:=c7 (Expr.size (Expr.lit ret)); let c11:Nat:=c6 c9 c10; @Exists.intro Env (fun (σ':Env) => And (Run B (finish ret) σ σ' ((6:Nat))) (c1 σ')) c5 (@And.intro (Run B (finish ret) σ c5 ((6:Nat))) (c1 c5) (RunStep.mono B (finish ret) σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "recursion.return.tag" (Expr.lit ((1:Nat)))) (Com.seq (Com.assign "recursion.return.mask" (Expr.var "component.union")) (Com.assign "machine.phase" (Expr.lit ret))) σ c2 c5 c8 c11 (RunStep.assign B σ "recursion.return.tag" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9034_0_0_0))) (RunStep.seq B (Com.assign "recursion.return.mask" (Expr.var "component.union")) (Com.assign "machine.phase" (Expr.lit ret)) c2 c4 c5 c9 c10 (RunStep.assign B c2 "recursion.return.mask" (Expr.var "component.union") c3 (RunStep.eval_var B c2 "component.union" (?nAX_g9034_0_0_1))) (RunStep.assign B c4 "machine.phase" (Expr.lit ret) ret (RunStep.eval_lit B ret c4 (?nAX_g9034_0_0_2))))) (?nAX_g9034_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9034_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9034_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9034_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9034_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeComponentControl

end

section

namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars "stack.copy.length"=xs.length
  index:σ.vars "stack.i"≤ xs.length
  position:σ.vars "stack.words"=front.length+σ.vars "stack.i"
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars "stack.i")) target σ

end Lax263307Proofs.NativeBlockAppend

end

section

namespace Lax263307Proofs.NativeStateBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem set_var {B:ℕ} {σ:Env} (hd:Bounded B σ) (s:String) (v:ℕ) (hv:v< B):
    Bounded B (σ.setVar s v):=by
  refine ⟨?_,hd.2.1,hd.2.2⟩
  intro t
  simp only [vars_setVar]
  split_ifs <;> first | exact hv | exact hd.1 t

theorem set_arr {B:ℕ} {σ:Env} (hd:Bounded B σ) (a:String) (i v:ℕ) (hv:v< B):
    Bounded B (σ.setArr a i v):=by
  refine ⟨hd.1,?_,hd.2.2⟩
  intro b z hz
  simp only [arrs_setArr] at hz
  split_ifs at hz
  · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hd.2.1 a z hz
    · exact hv
  · exact hd.2.1 b z hz

theorem big_step {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:BigStepB B c σ τ K)
    (hd:Bounded B σ):Bounded B τ:=by
  induction rr with
  | skip => exact hd
  | assign he => exact set_var hd _ _ (Expr.lt_of_evalB he)
  | store hi he hk => exact set_arr hd _ _ _ (Expr.lt_of_evalB he)
  | seq r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | ite_true hc rr ih => exact ih hd
  | ite_false hc rr ih => exact ih hd
  | while_true hc r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | while_false hc => exact hd
  | read hh =>
    rename_i σ0 s v rest
    have hv:=hd.2.2 _ (by rw [hh]; exact List.mem_cons_self)
    have hs:=set_var hd s v hv
    refine ⟨hs.1,hs.2.1,?_⟩
    intro z hz
    exact hd.2.2 z (by rw [hh]; exact List.mem_cons_of_mem _ hz)
  | write he => exact ⟨hd.1,hd.2.1,hd.2.2⟩

theorem run {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:Run B c σ τ K)
    (hd:Bounded B σ):Bounded B τ:=by
  obtain ⟨_,_,rr⟩:=rr
  exact big_step rr hd

end Lax263307Proofs.NativeStateBounds

end

section

namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

theorem append {B s t s' t':ℕ} {cases:List Com} {σ μ τ:Env}
    (a:Segment B cases s t σ μ) (b:Segment B cases s' t' μ τ):
    Segment B cases (s+s') (t+t') σ τ:=by
  induction a with
  | nil => simpa only [Nat.zero_add] using b
  | step h j hj rr rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm] using Segment.step h j hj rr (ih b)

theorem phase {B K:ℕ} {cases:List Com} {σ τ:Env}
    (running:σ.vars "machine.running"=1) (j:Fin cases.length)
    (phase:σ.vars "machine.phase"=j.val) (rr:Run B cases[j.val] σ τ K):
    Segment B cases 1 K σ τ:=by
  simpa only [Nat.zero_add,Nat.add_zero] using Segment.step running j phase rr (Segment.nil τ)

end Lax263307Proofs.NativeMachineSegment

end

section

namespace Lax263307Proofs.NativeCollectionSemantics

open Lax263307 ComputedRounding

def loop {n:ℕ} {ι:Type} (parts:ι→ Finset (Fin n)) (bound:ι→ ℕ)
    (reply:ι→ Option (Finset (Fin n))):List ι→ Finset (Fin n)→ Result n
  | [],S => .found S
  | i::is,S => match reply i with
    | none => .cut (parts i) (bound i)
    | some I => loop parts bound reply is (S∪I)

theorem loop_find {n:ℕ} {ι:Type} [DecidableEq ι]
    (parts:ι→ Finset (Fin n)) (bound:ι→ ℕ) (reply:ι→ Option (Finset (Fin n)))
    (order:List ι) (S:Finset (Fin n)):
    loop parts bound reply order S =
      match order.find? (fun i => (reply i).isNone) with
      | some i => .cut (parts i) (bound i)
      | none => .found (S∪order.toFinset.biUnion (fun i => (reply i).getD ∅)):=by
  induction order generalizing S with
  | nil => simp [loop]
  | cons i is ih =>
    cases hi:reply i with
    | none => simp [loop,hi]
    | some I =>
      simp only [loop,hi,ih,List.find?_cons,Option.isNone_some,Bool.false_eq_true,if_false]
      cases hs:is.find? (fun i => (reply i).isNone) with
      | some j => simp
      | none => simp [List.toFinset_cons,Finset.biUnion_insert,hi,Finset.union_assoc]

theorem realizes_collect {n:ℕ} {ι:Type} [Fintype ι] (order:List ι)
    (complete:∀ i,i∈order) (parts:ι→ Finset (Fin n)) (δ:ℚ) (k:ℕ)
    (cost:ι→ ℚ) (query:ι→ ℕ→ Option (Finset (Fin n))):
    loop parts (fun i => target δ (cost i)-1) (answer δ k cost query) order ∅ =
      collect order parts δ k cost query:=by
  classical
  rw [loop_find]
  have hall:order.toFinset=Finset.univ:=by ext i; simp [complete i]
  simp only [hall,Finset.empty_union,collect,SeparatorComponents.combine]
  rfl

end Lax263307Proofs.NativeCollectionSemantics

end

section

namespace Lax263307Proofs.NativeCollectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks

theorem loop_segment {n:ℕ} {ι:Type} (B:ℕ) (cfg:Config) (Q:Env→ Prop)
    (cut:Finset (Fin n)→ ℕ→ Env→ Prop) (parts:ι→ Finset (Fin n)) (bound:ι→ ℕ)
    (reply:ι→ Option (Finset (Fin n))) (order:List ι) (S K:ℕ)
    (hB:2*order.length+16< B) (hm:2^n< B)
    (hcount:∀ σ,Q σ→ σ.vars "component.count"=order.length)
    (hfinish:∀ σ τ t,Run B (NativeComponentControl.finish 14) σ τ t→ Q σ→ Q τ)
    (hsteps:Iterations B cfg Q cut parts bound reply order S K):
    ∀ suffix pre,pre++suffix=order→ ∀ U σ,At Q pre.length U σ→
      ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ∧
        transitions≤ S*suffix.length+1∧ total≤ K*suffix.length+10∧
        ResultOutput Q cut (NativeCollectionSemantics.loop parts bound reply suffix U) τ:=by
  intro suffix
  induction suffix with
  | nil =>
    intro pre hp U σ hin
    have hlen:pre.length=order.length:=by simpa using congrArg List.length hp
    obtain ⟨τ,rr,po⟩:=NativeComponentControl.finish_spec B 14 U (by omega) hm σ hin.2.2.1
    have ht:(Cond.lt (.var "component.i") (.var "component.count")).evalB B σ=some false:=by
      have ei:(Expr.var "component.i").evalB B σ=some pre.length:=by
        rw [evalB_var_iff]; exact ⟨hin.2.1.symm,hin.2.1 ▸ (by omega)⟩
      have ec:(Expr.var "component.count").evalB B σ=some order.length:=by
        rw [evalB_var_iff]; exact ⟨(hcount σ hin.1).symm,(hcount σ hin.1) ▸ (by omega)⟩
      simpa only [hlen,lt_self_iff_false,decide_false] using evalB_condLt ei ec
    have run:Run B component σ τ 10:=
      (Run.ite_false (c:=.seq NativeComponentLoad.command (go 10)) ht rr).mono (by simp [Cond.size,Expr.size])
    refine ⟨τ,1,10,NativeMachineSegment.phase hin.2.2.2.1 ⟨9,by change 9<16; decide⟩ hin.2.2.2.2 run,
      by simp,by simp,hfinish σ τ 6 rr hin.1,?_,po.2,po.1⟩
    exact (rr.frame_var _ (by decide)).trans hin.2.2.2.1
  | cons i suffix ih =>
    intro pre hp U σ hin
    obtain ⟨ν,s,t,first,hs,ht,ho⟩:=hsteps pre i suffix hp U σ hin
    cases he:reply i with
    | none =>
      refine ⟨ν,s,t,first,by simp only [List.length_cons]; nlinarith only [hs],
        by simp only [List.length_cons]; nlinarith only [ht],?_⟩
      simpa only [NativeCollectionSemantics.loop,he] using ho
    | some I =>
      have hnext:At Q (pre++[i]).length (U∪I) ν:=by
        simpa only [he,List.length_append,List.length_singleton] using ho
      have horder:(pre++[i])++suffix=order:=by simpa only [List.append_assoc,List.singleton_append] using hp
      obtain ⟨τ,s',t',rest,hs',ht',hout⟩:=ih (pre++[i]) horder (U∪I) ν hnext
      refine ⟨τ,s+s',t+t',NativeMachineSegment.append first rest,
        by simp only [List.length_cons]; nlinarith only [hs,hs'],
        by simp only [List.length_cons]; nlinarith only [ht,ht'],?_⟩
      simpa only [NativeCollectionSemantics.loop,he] using hout

theorem collect_segment {n:ℕ} {ι:Type} [Fintype ι]
    (B:ℕ) (cfg:Config) (Q:Env→ Prop) (cut:Finset (Fin n)→ ℕ→ Env→ Prop)
    (parts:ι→ Finset (Fin n)) (δ:ℚ) (k:ℕ) (cost:ι→ ℚ)
    (query:ι→ ℕ→ Option (Finset (Fin n))) (order:List ι) (complete:∀ i,i∈order) (S K:ℕ)
    (hB:2*order.length+16< B) (hm:2^n< B)
    (hcount:∀ σ,Q σ→ σ.vars "component.count"=order.length)
    (hfinish:∀ σ τ t,Run B (NativeComponentControl.finish 14) σ τ t→ Q σ→ Q τ)
    (hsteps:Iterations B cfg Q cut parts (fun i => target δ (cost i)-1)
      (answer (n:=n) δ k cost query) order S K) (σ:Env) (hin:At (n:=n) Q 0 ∅ σ):
    ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ∧
      transitions≤ S*order.length+1∧ total≤ K*order.length+10∧
      ResultOutput Q cut (collect order parts δ k cost query) τ:=by
  obtain ⟨τ,s,t,tr,hs,ht,ho⟩:=loop_segment B cfg Q cut parts (fun i => target δ (cost i)-1)
    (answer (n:=n) δ k cost query) order S K hB hm hcount hfinish hsteps order [] (by simp) ∅ σ hin
  exact ⟨τ,s,t,tr,hs,ht,by simpa only [NativeCollectionSemantics.realizes_collect order complete] using ho⟩

end Lax263307Proofs.NativeCollectionTrace

end

section

namespace Lax263307Proofs.NativeCollectionAnchor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine

theorem trans {base σ τ:Env} (h:Anchor base σ) (hnext:Anchor σ τ):Anchor base τ:=
  ⟨fun s hs => (hnext.1 s hs).trans (h.1 s hs),
    fun a ha => (hnext.2 a ha).trans (h.2 a ha)⟩

theorem frame {B K:ℕ} {c:Com} {base σ τ:Env} (rr:Run B c σ τ K)
    (hc:Anchor base σ) (hv:∀ s∈c.wvars,s∈workScalars)
    (ha:∀ a∈c.warrs,a∈workArrays):Anchor base τ:=by
  constructor
  · intro s hs
    exact (rr.frame_var s (fun h => hs (hv s h))).trans (hc.1 s hs)
  · intro a ha'
    exact (rr.frame_arr a (fun h => ha' (ha a h))).trans (hc.2 a ha')

end Lax263307Proofs.NativeCollectionAnchor

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCollectionContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks

def scalars:List String:= ["graph.n","component.count","algorithm.D",
  "conditioning.k","catalog.count","conditioning.choice","stack.words",
  "recursion.stride","recursion.fuel"]
def arrays:List String:= ["search.graph","near.costs","separator.pieces",
  "catalog.mask","recursion.frames"]

theorem frame_order {n B D k r fuel stride K:ℕ}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {x:Fin n→ ℚ≥0}
    {parts:List (Finset (Fin n))} {A:Finset (Fin n)}
    {extent:String→ ℕ} {front:List ℕ} {σ τ:Env} {c:Com}
    (rr:Run B c σ τ K) (hc:Context B D k r fuel stride G x parts A extent front σ)
    (hn:τ.vars "graph.n"=n)
    (hv:∀ s∈scalars,s≠"graph.n" → s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r fuel stride G x parts A extent front τ:=by
  refine ⟨hn,?_,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.count,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.denominator,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.target,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.dimension,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.conditioning,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.cursor,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.width,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.depth⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp [arrays]))] using hc.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" (ha _ (by simp [arrays]))] using hc.costs
  · simpa only [Prefix,rr.frame_arr "separator.pieces" (ha _ (by simp [arrays]))] using hc.pieces
  · simpa only [Prefix,rr.frame_arr "catalog.mask" (ha _ (by simp [arrays]))] using hc.catalog
  · intro a; rw [RamFrames.run_array_length rr]; exact hc.lengths a
  · simpa only [Prefix,rr.frame_arr "recursion.frames" (ha _ (by simp [arrays]))] using hc.stack

theorem frame {n B D k r fuel stride K:ℕ}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {x:Fin n→ ℚ≥0}
    {parts:List (Finset (Fin n))} {A:Finset (Fin n)}
    {extent:String→ ℕ} {front:List ℕ} {σ τ:Env} {c:Com}
    (rr:Run B c σ τ K) (hc:Context B D k r fuel stride G x parts A extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r fuel stride G x parts A extent front τ:=by
  exact frame_order rr hc ((rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.order)
    (fun s hs _ => hv s hs) ha

end Lax263307Proofs.NativeCollectionContext

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCollectionExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks NativeCollectionContext

theorem collect_segment {n:ℕ} {ι:Type} [Fintype ι] (D k r fuel S h T childSteps childTime:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0)
    (parts:ι→ Finset (Fin n)) (order:List ι) (A:Finset (Fin n))
    (extent:String→ ℕ) (front:List ℕ) (base:Env)
    (child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card)))
    (complete:∀ i,i∈order)
    (hn:0< n) (hD:0< D) (hx:∀ v,NativeSignedArithmetic.Bounded (2^h) (x v:ℚ))
    (w:ℕ) (hw:NativeComponentDecision.wordHeight n D k h≤ w)
    (hparts:order.length≤ n+1) (hm:2^n<2^w)
    (hB:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
      2*order.length+T+fuel+3*NativeCatalogMetadata.N n r+80<2^w)
    (htarget:∀ i∈order,target (1/(D:ℚ)) (∑ v∈parts i,(x v:ℚ))≤ T)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (hstack:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤ extent "recursion.frames")
    (hchild:n*n≤ extent "child.graph") (hsearch:n*n≤ extent "search.graph")
    (hbits:n≤ extent "subset.bits") (hlabels:n≤ extent "restrict.vertices")
    (hword:3*n< extent "lp.word") (hsum:3*n≤ extent "sum.input")
    (hlp:3*NativeCatalogMetadata.N n r≤ extent "lp.input")
    (hnormal:3*NativeCatalogMetadata.N n r≤ extent "round.normal")
    (recursive:∀ i∈order,(1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈parts i,(x v:ℚ))→ ∀ σ,
      Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base σ→
      NativeRestrictionRead.Data G (fun v => (x v:ℚ)) (parts i) σ→
      σ.vars "component.mask"=mask (parts i)→
      σ.vars "component.target"=target (1/(D:ℚ)) (∑ v∈parts i,(x v:ℚ))→
      σ.vars "machine.running"=1→ σ.vars "machine.phase"=11→
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (parts i)
        (target (1/(D:ℚ)) (∑ v∈parts i,(x v:ℚ))) front σ
        (child (parts i) (target (1/(D:ℚ)) (∑ v∈parts i,(x v:ℚ)))))
    (σ:Env) (hin:NativeCollectionTrace.At (n:=n)
      (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) 0 ∅ σ):
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ∧
      transitions≤(childSteps+5)*order.length+1∧
      total≤ partCost cfg n r S h childTime*order.length+10∧
      NativeCollectionTrace.ResultOutput
        (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) (Cut r A)
        (collect order parts (1/(D:ℚ)) k (fun i => ∑ v∈parts i,(x v:ℚ))
          (fun i t => (child (parts i) t).map (fun I => I.image (ComputedSeparators.label (parts i))))) τ:=by
  have actual:=iterations D k r fuel S h T childSteps childTime cfg G x parts order A extent front base child
    hn hD hx w hw hparts hm hB htarget hext hstack hchild hsearch hbits hlabels hword hsum hlp hnormal recursive
  exact NativeCollectionTrace.collect_segment (2^w) cfg
    (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) (Cut r A)
    parts (1/(D:ℚ)) k (fun i => ∑ v∈parts i,(x v:ℚ))
    (fun i t => (child (parts i) t).map (fun I => I.image (ComputedSeparators.label (parts i))))
    order complete (childSteps+5) (partCost cfg n r S h childTime) (by omega) hm
    (fun σ hc => by simpa only [List.length_map] using hc.1.count)
    (fun σ τ t rr hc => ⟨NativeCollectionContext.frame rr hc.1 (by decide) (by decide),
      NativeCollectionAnchor.frame rr hc.2 (by decide) (by decide)⟩) actual σ hin

end Lax263307Proofs.NativeCollectionExecution

end

theorem solution:∀ {n:Nat} {ι:Type} [inst:Fintype ι] (D k r fuel S h T childSteps childTime:Nat)
  (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n))
  [inst_1:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x:Fin n→ NNRat) (parts:ι→ Finset (Fin n))
  (order:List ι) (A:Finset (Fin n)) (extent:String→ Nat) (front:List Nat) (base:Lax808846Proofs.Imp.Env)
  (child:(C:Finset (Fin n))→ Nat→ Option (Finset (Fin (@Finset.card (Fin n) C)))),
  (∀ (i:ι), @Membership.mem ι (List ι) (@List.instMembership ι) order i)→
    Nat.lt ((0:Nat)) n→
      Nat.lt ((0:Nat)) D→
        (∀ (v:Fin n),
            Lax263307Proofs.NativeSignedArithmetic.Bounded
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) h)
              (@NNRat.cast Rat Rat.instNNRatCast (x v)))→
          ∀ (w:Nat),
            Nat.le (Lax263307Proofs.NativeComponentDecision.wordHeight n D k h) w→
              Nat.le (@List.length ι order)
                  (Nat.add n
                    ((1:Nat)))→
                Nat.lt
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) n)
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  Nat.lt
                      (Nat.add
                        (Nat.add
                          (Nat.add
                            (Nat.add
                              (Nat.add
                                (Nat.add
                                  (Nat.add
                                    (Nat.add
                                      (Nat.add (@List.length Nat front)
                                        (Nat.mul S
                                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                                      (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                    (Nat.mul n n))
                                  (Nat.mul
                                    ((2:Nat)) n))
                                (Nat.mul
                                  ((2:Nat)) (@List.length ι order)))
                              T)
                            fuel)
                          (Nat.mul
                            ((3:Nat))
                            (Lax263307Proofs.NativeCatalogMetadata.N n r)))
                        ((80:Nat)))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)→
                    (∀ (i:ι),
                        @Membership.mem ι (List ι) (@List.instMembership ι) order i→
                          Nat.le
                            (Lax263307.ComputedRounding.target
                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                (@Nat.cast Rat Rat.instNatCast D))
                              (∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v)))
                            T)→
                      (∀ (a:String),
                          @Membership.mem String (List String) (@List.instMembership String)
                              (Lax263307Proofs.NativeCoreMachine.frameArrays cfg) a→
                            @Eq Nat (extent a) S)→
                        Nat.le
                            (Nat.add
                              (Nat.add (@List.length Nat front)
                                (Nat.mul S
                                  (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                            (extent "recursion.frames")→
                          Nat.le (Nat.mul n n)
                              (extent "child.graph")→
                            Nat.le (Nat.mul n n)
                                (extent "search.graph")→
                              Nat.le n (extent "subset.bits")→
                                Nat.le n (extent "restrict.vertices")→
                                  Nat.lt
                                      (Nat.mul
                                        ((3:Nat)) n)
                                      (extent "lp.word")→
                                    Nat.le
                                        (Nat.mul
                                          ((3:Nat)) n)
                                        (extent "sum.input")→
                                      Nat.le
                                          (Nat.mul
                                            ((3:Nat))
                                            (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                          (extent "lp.input")→
                                        Nat.le
                                            (Nat.mul
                                              ((3:Nat))
                                              (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                            (extent "round.normal")→
                                          (∀ (i:ι),
                                              @Membership.mem ι (List ι) (@List.instMembership ι) order i→
                                                @LT.lt Rat Rat.instLT
                                                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                      (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                          (@Nat.cast Rat Rat.instNatCast D))
                                                        (@Nat.cast Rat Rat.instNatCast k))
                                                      (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                        (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                                        (@Nat.cast Rat Rat.instNatCast n)))
                                                    (∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v))→
                                                  ∀ (σ:Lax808846Proofs.Imp.Env),
                                                    @Lax263307Proofs.NativeCollectionExecution.Invariant n
                                                        (@HPow.hPow Nat Nat Nat
                                                          (@instHPow Nat Nat
                                                            (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                          ((2:Nat)) w)
                                                        D k r fuel S G inst_1 x
                                                        (@List.map ι (Finset (Fin n)) parts order) A extent front base
                                                        σ→
                                                      @Lax263307Proofs.NativeRestrictionRead.Data n G inst_1
                                                          (fun (v:Fin n) => @NNRat.cast Rat Rat.instNNRatCast (x v))
                                                          (parts i) σ→
                                                        @Eq Nat (σ.vars "component.mask")
                                                            (@Lax263307Proofs.NativeMasks.mask n (parts i))→
                                                          @Eq Nat (σ.vars "component.target")
                                                              (Lax263307.ComputedRounding.target
                                                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                  (@OfNat.ofNat Rat (nat_lit 1)
                                                                    (@Rat.instOfNat (nat_lit 1)))
                                                                  (@Nat.cast Rat Rat.instNatCast D))
                                                                (∑ v∈ parts i,
                                                                  @NNRat.cast Rat Rat.instNNRatCast (x v)))→
                                                            @Eq Nat (σ.vars "machine.running")
                                                                ((1:Nat))→
                                                              @Eq Nat (σ.vars "machine.phase")
                                                                  ((11:Nat))→
                                                                @Lax263307Proofs.NativeCollectionChild.Recursive n
                                                                  (@HPow.hPow Nat Nat Nat
                                                                    (@instHPow Nat Nat
                                                                      (@NPow.toPow Nat
                                                                        (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                    ((2:Nat))
                                                                    w)
                                                                  S fuel childSteps childTime cfg G inst_1 (parts i)
                                                                  (Lax263307.ComputedRounding.target
                                                                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                      (@OfNat.ofNat Rat (nat_lit 1)
                                                                        (@Rat.instOfNat (nat_lit 1)))
                                                                      (@Nat.cast Rat Rat.instNatCast D))
                                                                    (∑ v∈ parts i,
                                                                      @NNRat.cast Rat Rat.instNNRatCast (x v)))
                                                                  front σ
                                                                  (child (parts i)
                                                                    (Lax263307.ComputedRounding.target
                                                                      (@HDiv.hDiv Rat Rat Rat
                                                                        (@instHDiv Rat Rat.instDiv)
                                                                        (@OfNat.ofNat Rat (nat_lit 1)
                                                                          (@Rat.instOfNat (nat_lit 1)))
                                                                        (@Nat.cast Rat Rat.instNatCast D))
                                                                      (∑ v∈ parts i,
                                                                        @NNRat.cast Rat Rat.instNNRatCast (x v)))))→
                                            ∀ (σ:Lax808846Proofs.Imp.Env),
                                              @Lax263307Proofs.NativeCollectionTrace.At n
                                                  (@Lax263307Proofs.NativeCollectionExecution.Invariant n
                                                    (@HPow.hPow Nat Nat Nat
                                                      (@instHPow Nat Nat
                                                        (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                      ((2:Nat)) w)
                                                    D k r fuel S G inst_1 x (@List.map ι (Finset (Fin n)) parts order) A
                                                    extent front base)
                                                  ((0:Nat))
                                                  (@EmptyCollection.emptyCollection (Finset (Fin n))
                                                    (@Finset.instEmptyCollection (Fin n)))
                                                  σ→
                                                ∃ (τ:Lax808846Proofs.Imp.Env) (transitions:Nat) (total:Nat),
                                                  And
                                                    (Lax263307Proofs.NativeMachineSegment.Segment
                                                      (@HPow.hPow Nat Nat Nat
                                                        (@instHPow Nat Nat
                                                          (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                        ((2:Nat)) w)
                                                      (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ
                                                      τ)
                                                    (And
                                                      (Nat.le transitions
                                                        (Nat.add
                                                          (Nat.mul
                                                            (Nat.add
                                                              childSteps
                                                              ((5:Nat)))
                                                            (@List.length ι order))
                                                          ((1:Nat))))
                                                      (And
                                                        (Nat.le total
                                                          (Nat.add
                                                            (Nat.mul
                                                              (Lax263307Proofs.NativeCollectionExecution.partCost cfg n
                                                                r S h childTime)
                                                              (@List.length ι order))
                                                            ((10:Nat))))
                                                        (@Lax263307Proofs.NativeCollectionTrace.ResultOutput n
                                                          (@Lax263307Proofs.NativeCollectionExecution.Invariant n
                                                            (@HPow.hPow Nat Nat Nat
                                                              (@instHPow Nat Nat
                                                                (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                              ((2:Nat))
                                                              w)
                                                            D k r fuel S G inst_1 x
                                                            (@List.map ι (Finset (Fin n)) parts order) A extent front
                                                            base)
                                                          (@Lax263307Proofs.NativeCollectionExecution.Cut n r A)
                                                          (@Lax263307.ComputedRounding.collect n ι inst order parts
                                                            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                              (@OfNat.ofNat Rat (nat_lit 1)
                                                                (@Rat.instOfNat (nat_lit 1)))
                                                              (@Nat.cast Rat Rat.instNatCast D))
                                                            k
                                                            (fun (i:ι) =>
                                                              ∑ v∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v))
                                                            fun (i:ι) (t:Nat) =>
                                                            @Option.map (Finset (Fin (@Finset.card (Fin n) (parts i))))
                                                              (Finset (Fin n))
                                                              (fun
                                                                  (I:Finset (Fin (@Finset.card (Fin n) (parts i)))) =>
                                                                @Finset.image (Fin (@Finset.card (Fin n) (parts i)))
                                                                  (Fin n) (instDecidableEqFin n)
                                                                  (@DFunLike.coe
                                                                    (@OrderEmbedding
                                                                      (Fin (@Finset.card (Fin n) (parts i))) (Fin n)
                                                                      (@instLEFin (@Finset.card (Fin n) (parts i)))
                                                                      (@instLEFin n))
                                                                    (Fin (@Finset.card (Fin n) (parts i)))
                                                                    (fun (x:Fin (@Finset.card (Fin n) (parts i))) =>
                                                                      Fin n)
                                                                    (@instFunLikeOrderEmbedding
                                                                      (Fin (@Finset.card (Fin n) (parts i))) (Fin n)
                                                                      (@instLEFin (@Finset.card (Fin n) (parts i)))
                                                                      (@instLEFin n))
                                                                    (@Lax263307.ComputedSeparators.label n (parts i)))
                                                                  I)
                                                              (child (parts i) t))
                                                          τ))):= @Lax263307Proofs.NativeCollectionExecution.collect_segment
