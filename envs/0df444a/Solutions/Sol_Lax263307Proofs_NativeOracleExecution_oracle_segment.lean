-- Prove2me | solution 1 for Lax263307Proofs.NativeOracleExecution.oracle_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:12:39.339627+00:00
-- url     : https://prove2.me/submissions/ef7c5b76-012c-43d6-8310-a5548525344a

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax263307Proofs_NativeNearExecution_near_segment_native

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

namespace Lax109476Proofs.RamArithmetic
end Lax109476Proofs.RamArithmetic
theorem Lax109476Proofs.RamArithmetic.normalizeFraction_spec:∀ (B n d:Nat),
  LT.lt n B→
    LT.lt d B→
      LT.lt ((0:Nat)) d→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "rat.n") n) (@Eq Nat (σ.vars "rat.d") d))
          Lax109476Proofs.RamArithmetic.normalizeFraction
          (fun (x σ':Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ'.vars "rat.n") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n (n.gcd d)))
              (@Eq Nat (σ'.vars "rat.d") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) d (n.gcd d))))
          (HAdd.hAdd
            (HMul.hMul
              ((36:Nat)) d.size)
            ((16:Nat))):= @Lax109476Proofs.RamArithmetic.normalizeFraction_spec_native
namespace Lax263307Proofs.NativeNearExecution
end Lax263307Proofs.NativeNearExecution
theorem Lax263307Proofs.NativeNearExecution.near_segment:∀ {n r:Nat} (D k p b load F fuel S v limit M h T w space flowTime childSteps childTime:Nat)
  (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (flow:List Nat→ List Nat)
  (x:Fin (Lax263307Proofs.NativeCatalogMetadata.N n r)→ Rat) (extent:String→ Nat) (front:List Nat)
  (child:(C:Finset (Fin n))→ Nat→ Option (Finset (Fin (@Finset.card (Fin n) C)))),
  Lax263307Proofs.NativeNearExecution.Bounds n r D k p M h T fuel S w cfg extent front→
    (∀ (i:Fin (Lax263307Proofs.NativeCatalogMetadata.N n r)),
        Lax263307Proofs.NativeSignedArithmetic.Bounded M (x i))→
      (∀ (A:Finset (Fin n)),
          @Eq (Option (Finset (Fin n)))
              (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                (@Lax263307.MomentLP.decode Rat n r x))
              (@Option.some (Finset (Fin n)) A)→
            LE.le (@Finset.card (Fin n) A) r)→
        (∀ (A:Finset (Fin n)),
            @Eq (Option (Finset (Fin n)))
                (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                  (@Lax263307.MomentLP.decode Rat n r x))
                (@Option.some (Finset (Fin n)) A)→
              ∀ (C:Finset (Fin n)),
                LE.le
                  (Lax263307.ComputedRounding.target
                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                      (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D))
                    (∑ v∈ C,
                      @NNRat.cast Rat Rat.instNNRatCast
                        (@Lax263307.NearOracle.costs n r (@Lax263307.MomentLP.decode Rat n r x) A v)))
                  T)→
          (∀ (a:String),
              @Membership.mem String (List String) (@List.instMembership String)
                  Lax263307Proofs.NativeSeparatorContext.workspace a→
                LE.le space (extent a))→
            (∀ (A:Finset (Fin n)),
                have costs:= @Lax263307.NearOracle.costs n r (@Lax263307.MomentLP.decode Rat n r x) A;
                have cs:=
                  @Lax263307.ComputedSeparators.cuts n (@Lax263307.ComputedSeparators.step n flow G inst costs b load k)
                    n (@Finset.univ (Fin n) (Fin.fintype n));
                Lax808846Proofs.Reasoning.Spec
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w)
                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                    And (@Lax263307Proofs.NativeSeparatorContext.Context n G inst costs b load k space σ)
                      (LE.le
                        (HAdd.hAdd n
                          ((1:Nat)))
                        (@List.length Nat (σ.arrs "separator.pieces"))))
                  (Lax263307Proofs.NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                    And (@Lax263307Proofs.NativeSeparatorContext.Context n G inst costs b load k space τ)
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
                                  (HMul.hMul
                                    ((2:Nat))
                                    (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeCutPieces.words n cs)
                                  "separator.pieces" τ)))))))
                  flowTime)→
              (∀ (A:Finset (Fin n)),
                  @Eq (Option (Finset (Fin n)))
                      (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                        (@Lax263307.MomentLP.decode Rat n r x))
                      (@Option.some (Finset (Fin n)) A)→
                    let costs:= @Lax263307.NearOracle.costs n r (@Lax263307.MomentLP.decode Rat n r x) A;
                    let cs:=
                      @Lax263307.ComputedSeparators.cuts n
                        (@Lax263307.ComputedSeparators.step n flow G inst costs b load k) n
                        (@Finset.univ (Fin n) (Fin.fintype n));
                    ∀ (i:Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))),
                      @Membership.mem (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                          (List (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))
                          (@List.instMembership
                            (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs))))
                          (Lax263307.NearOracle.order (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)) i→
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
                            (∑ v∈ @Lax263307.ComputedSeparators.pieces n cs i,
                              @NNRat.cast Rat Rat.instNNRatCast (costs v))→
                          ∀ (base σ:Lax808846Proofs.Imp.Env),
                            Lax263307Proofs.NativeOracleContext.Protocol
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  ((2:Nat)) w)
                                D S v cfg extent front σ→
                              @Lax263307Proofs.NativeCollectionExecution.Invariant n
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    ((2:Nat)) w)
                                  D k r fuel S G inst costs
                                  (@List.map (Option (Fin (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                    (Finset (Fin n)) (@Lax263307.ComputedSeparators.pieces n cs)
                                    (Lax263307.NearOracle.order
                                      (@List.length (Prod (Finset (Fin n)) (Finset (Fin n))) cs)))
                                  A extent front base σ→
                                @Lax263307Proofs.NativeRestrictionRead.Data n G inst
                                    (fun (v:Fin n) => @NNRat.cast Rat Rat.instNNRatCast (costs v))
                                    (@Lax263307.ComputedSeparators.pieces n cs i) σ→
                                  @Eq Nat (σ.vars "component.mask")
                                      (@Lax263307Proofs.NativeMasks.mask n
                                        (@Lax263307.ComputedSeparators.pieces n cs i))→
                                    @Eq Nat (σ.vars "component.target")
                                        (Lax263307.ComputedRounding.target
                                          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                            (@Nat.cast Rat Rat.instNatCast D))
                                          (∑ v∈ @Lax263307.ComputedSeparators.pieces n cs i,
                                            @NNRat.cast Rat Rat.instNNRatCast (costs v)))→
                                      @Eq Nat (σ.vars "machine.running")
                                          ((1:Nat))→
                                        @Eq Nat (σ.vars "machine.phase")
                                            ((11:Nat))→
                                          @Lax263307Proofs.NativeCollectionChild.Recursive n
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              ((2:Nat)) w)
                                            S fuel childSteps childTime cfg G inst
                                            (@Lax263307.ComputedSeparators.pieces n cs i)
                                            (Lax263307.ComputedRounding.target
                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                (@Nat.cast Rat Rat.instNatCast D))
                                              (∑ v∈ @Lax263307.ComputedSeparators.pieces n cs i,
                                                @NNRat.cast Rat Rat.instNNRatCast (costs v)))
                                            front σ
                                            (child (@Lax263307.ComputedSeparators.pieces n cs i)
                                              (Lax263307.ComputedRounding.target
                                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                  (@OfNat.ofNat Rat (nat_lit 1)
                                                    ((have costs:=
                                                        @Lax263307.NearOracle.costs n r
                                                          (@Lax263307.MomentLP.decode Rat n r x) A;
                                                      have cs:=
                                                        @Lax263307.ComputedSeparators.cuts n
                                                          (@Lax263307.ComputedSeparators.step n flow G inst costs b load
                                                            k)
                                                          n (@Finset.univ (Fin n) (Fin.fintype n));
                                                      fun
                                                        (i:
                                                          Option
                                                            (Fin
                                                              (@List.length (Prod (Finset (Fin n)) (Finset (Fin n)))
                                                                cs)))
                                                        (base σ:Lax808846Proofs.Imp.Env) =>
                                                      @Rat.instOfNat (nat_lit 1))
                                                      i base σ))
                                                  (@Nat.cast Rat Rat.instNatCast D))
                                                (∑ v∈ @Lax263307.ComputedSeparators.pieces n cs i,
                                                  @NNRat.cast Rat Rat.instNNRatCast (costs v)))))→
                ∀ (j:Nat) (state:Lax263307.RoundedOracleSearch.State (Lax263307Proofs.NativeCatalogMetadata.N n r))
                  (σ:Lax808846Proofs.Imp.Env),
                  @Lax263307Proofs.NativeOracleContext.Context n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)
                      D k r p b load F fuel S v limit cfg G inst extent front σ→
                    @Lax263307Proofs.NativeRoundedTrace.StoredState (Lax263307Proofs.NativeCatalogMetadata.N n r) j
                        state σ→
                      Lax455465Proofs.RamVirtualState.Prefix
                          (@Lax109476.RationalEncoding.encodeVector (Lax263307Proofs.NativeCatalogMetadata.N n r) x)
                          "lp.word" σ→
                        @Eq Nat (σ.vars "machine.running") ((1:Nat))→
                          @Eq Nat (σ.vars "machine.phase") ((6:Nat))→
                            ∃ (τ:Lax808846Proofs.Imp.Env) (transitions:Nat) (total:Nat),
                              And
                                (Lax263307Proofs.NativeMachineSegment.Segment
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    ((2:Nat)) w)
                                  (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ τ)
                                (And
                                  (LE.le transitions
                                    (HAdd.hAdd
                                      (HMul.hMul
                                        (HAdd.hAdd childSteps
                                          ((5:Nat)))
                                        (HAdd.hAdd n
                                          ((1:Nat))))
                                      ((4:Nat))))
                                  (And
                                    (LE.le total
                                      (Lax263307Proofs.NativeNearExecution.timeBound cfg n r M S h childTime flowTime))
                                    (And
                                      (@Lax263307Proofs.NativeOracleContext.Context n
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat)) w)
                                        D k r p b load F fuel S v limit cfg G inst extent front τ)
                                      (And
                                        (@Lax263307Proofs.NativeRoundedTrace.StoredState
                                          (Lax263307Proofs.NativeCatalogMetadata.N n r) j state τ)
                                        (And
                                          (@Lax263307Proofs.NativeNearExecution.Output n r
                                            (@Lax263307Proofs.NativeNearExecution.run n r flow G inst D k p b load
                                              (@Lax263307.MomentLP.decode Rat n r x) child)
                                            τ)
                                          (Lax263307Proofs.NativeOracleContext.RootData σ τ)))))):= @Lax263307Proofs.NativeNearExecution.near_segment_native

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

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

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

namespace Lax455465Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem normalizeFraction_spec (B n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d) normalizeFraction
      (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d) (36 * d.size + 16)  :=by
  exact Lax109476Proofs.RamArithmetic.normalizeFraction_spec B n d hn hd hdpos

end Lax455465Proofs.RamArithmetic

end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

theorem fractionValue_reduce (s n d:ℕ):
    fractionValue s (n / Nat.gcd n d) (d / Nat.gcd n d)=fractionValue s n d:=by
  have h:((n / Nat.gcd n d:ℕ):ℚ) / ((d / Nat.gcd n d:ℕ):ℚ)=(n:ℚ) / d:=
    Nat.cast_div_div_div_cancel_right (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  unfold fractionValue
  split_ifs
  · simpa only [neg_div] using congrArg Neg.neg h
  · exact h

theorem normalizeFraction_signed_spec (B s n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d∧ σ'.vars "rat.s"=s) (36 * d.size + 16):=by
  rintro σ ⟨hσn,hσd,hσs⟩
  obtain ⟨τ,hr,hτn,hτd⟩:=normalizeFraction_spec B n d hn hd hdpos σ ⟨hσn,hσd⟩
  have hτs:=hr.frame_var "rat.s" (by decide)
  exact ⟨τ,hr,hτn,hτd,hτs.trans hσs⟩

theorem fractionValue_num_den (s n d:ℕ) (hd:0 < d):
    (fractionValue s n d).num.natAbs=n / Nat.gcd n d∧
      (fractionValue s n d).den=d / Nat.gcd n d:=by
  have h:(((n:ℚ) / d).num.natAbs=n / Nat.gcd n d)∧
      ((n:ℚ) / d).den=d / Nat.gcd n d:=by
    have he:(n:ℚ) / d=mkRat (n:ℤ) d:=by simp [Rat.mkRat_eq_div]
    rw [he]
    simp [Rat.num_mkRat,Rat.den_mkRat,ne_of_gt hd,
      Int.natAbs_ediv_of_nonneg (by positivity:(0:ℤ)≤ n),Nat.gcd_comm]
  unfold fractionValue
  split_ifs
  · simpa only [neg_div,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using h
  · exact h

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

theorem normalizeFraction_output_spec (B s n d:ℕ) (hs:s≤ 1)
    (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => FractionOutput (fractionValue s n d) σ')
      (36 * d.size + 16):=by
  apply (normalizeFraction_signed_spec B s n d hn hd hdpos).post
  rintro σ τ _ ⟨hτn,hτd,hτs⟩
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hτs,hτn,hτd]; exact fractionValue_reduce s n d,
    hτn.trans hnum.symm,hτd.trans hden.symm,hτs ▸ hs⟩

end Lax455465Proofs.RamRational

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

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

namespace Lax455465Proofs.RamFractionEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

theorem canonical_sign (q:ℚ) (σ:Env) (h:FractionOutput q σ):
    (if σ.vars "rat.n"=0 then 0 else σ.vars "rat.s")=if q.num < 0 then 1 else 0:=by
  by_cases hn:σ.vars "rat.n"=0
  · have hnum:q.num=0:=by
      have he:q.num.natAbs=0:=h.2.1.symm.trans hn
      exact Int.natAbs_eq_zero.mp he
    simp [hn,hnum]
  · have hs:σ.vars "rat.s"=0∨ σ.vars "rat.s"=1:=by have:=h.2.2.2; omega
    rcases hs with hs | hs
    · have hnonneg:0≤ q:=by
        rw [← h.1]
        simp only [fractionValue,hs,show ¬(0:ℕ)=1 by decide,if_false]
        positivity
      have hnum:=Rat.num_nonneg.mpr hnonneg
      simp [hn,hs,not_lt.mpr hnum]
    · have hnpos:(0:ℚ) < σ.vars "rat.n" :=by exact_mod_cast (show 0 < σ.vars "rat.n" by omega)
      have hdpos:(0:ℚ) < σ.vars "rat.d" :=by
        rw [h.2.2.1]
        exact_mod_cast q.den_pos
      have hneg:q < 0:=by
        rw [← h.1]
        simp only [fractionValue,hs,if_true]
        exact div_neg_of_neg_of_pos (by linarith) hdpos
      have hnum:q.num < 0:=by
        by_contra hnum
        have hq:=Rat.num_nonneg.mp (show 0≤ q.num by omega)
        linarith
      simp [hn,hs,hnum]

theorem sign_spec (B:ℕ) (q:ℚ) (h1:1 < B) (hn:q.num.natAbs < B):
    Spec B (FractionOutput q) sign
      (fun _ τ => τ.vars "emit.s"=if q.num < 0 then 1 else 0) 6:=by
  intro σ h
  have hvalue:=h.2.1
  have hsign:=h.2.2.2
  have hcanonical:=canonical_sign q σ h
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@LT.lt Int Int.instLTInt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Int.decLt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "emit.s") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B sign σ σ' ((6:Nat))) (c3 σ'); let c5:Env:=Env.setVar σ "emit.s" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "emit.s" (Expr.lit ((0:Nat))); let c12:Nat:=c7 (Expr.size (Expr.var "rat.s")); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c5 (@And.intro (Run B sign σ c5 ((6:Nat))) (c3 c5) (RunStep.mono B sign σ c5 (c9 c10) ((6:Nat)) (RunStep.ite_true B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ c5 c10 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_1)) hcase) (RunStep.assign B σ "emit.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_2)))) (?nAX_g5889_0_0_3)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (@And.intro (Run B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) ((6:Nat))) (c3 (Env.setVar σ "emit.s" (Env.vars σ "rat.s"))) (RunStep.mono B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (c9 c12) ((6:Nat)) (RunStep.ite_false B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) c12 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_5)) hcase) (RunStep.assign B σ "emit.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" (?nAX_g5889_0_0_6)))) (?nAX_g5889_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5889_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem emit_spec (B:ℕ) (q:ℚ) (words:List ℕ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hlen:words.length + 3 < B):
    Spec B (fun σ => FractionOutput q σ∧ Prefix words "lp.word" σ∧
      σ.vars "lp.position"=words.length∧ words.length + 2 < (σ.arrs "lp.word").length) emit
      (fun _ τ => Prefix (words ++ Lax109476.RationalEncoding.encodeRational q) "lp.word" τ∧
        τ.vars "lp.position"=words.length + 3) 27:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  let tag:=if q.num < 0 then 1 else 0
  have htag:tag < B:=by dsimp only [tag]; split_ifs <;> omega
  obtain ⟨ν,hsign,htagν⟩:=sign_spec B q h1 hn σ hf
  have hnumν:=(hsign.frame_var "rat.n" (by simp [sign,Com.wvars])).trans hf.2.1
  have hdenν:=(hsign.frame_var "rat.d" (by simp [sign,Com.wvars])).trans hf.2.2.1
  have hposν:=(hsign.frame_var "lp.position" (by simp [sign,Com.wvars])).trans hpos
  have hpν:Prefix words "lp.word" ν:=by
    simpa only [Prefix,hsign.frame_arr "lp.word" (by simp [sign,Com.warrs])] using hp
  have hroomν:words.length + 2 < (ν.arrs "lp.word").length:=by
    rwa [RamFrames.run_array_length hsign "lp.word"]
  have hnum:=RamFrames.keep_scalar (RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" words tag (.var "emit.s") h1 (by omega))
    "rat.n" q.num.natAbs (by simp [RamWordBuffer.append,Com.wvars]))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨μ,hfirst,hfirstPost⟩:=hnum ν ⟨⟨⟨hpν,hposν,by omega,
    by rw [evalB_var_iff]; exact ⟨htagν.symm,htagν ▸ htag⟩⟩,hnumν⟩,hdenν⟩
  have hroomμ:(words ++ [tag]).length + 1 < (μ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hfirst "lp.word",List.length_append,List.length_singleton]
    exact hroomν
  have hden:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" (words ++ [tag]) q.num.natAbs (.var "rat.n") h1
      (by simp only [List.length_append,List.length_singleton]; omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨ρ,hsecond,hsecondPost⟩:=hden μ ⟨⟨hfirstPost.1.1.1,
    by simpa only [List.length_append,List.length_singleton] using hfirstPost.1.1.2,
    by omega,by rw [evalB_var_iff]; exact ⟨hfirstPost.1.2.symm,hfirstPost.1.2 ▸ hn⟩⟩,hfirstPost.2⟩
  have hroomρ:((words ++ [tag]) ++ [q.num.natAbs]).length < (ρ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hsecond "lp.word",List.length_append,List.length_singleton]
    exact hroomμ
  obtain ⟨τ,hthird,hthirdPost⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position"
    ((words ++ [tag]) ++ [q.num.natAbs]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ρ
    ⟨hsecondPost.1.1,by simpa only [List.length_append,List.length_singleton] using hsecondPost.1.2,
      hroomρ,by rw [evalB_var_iff]; exact ⟨hsecondPost.2.symm,hsecondPost.2 ▸ hd⟩⟩
  refine ⟨τ, (hsign.seq (hfirst.seq (hsecond.seq hthird))).mono (by simp [Expr.size]), ?_⟩
  simpa only [Lax109476.RationalEncoding.encodeRational,tag,List.append_assoc,
    List.cons_append,List.nil_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc]
    using hthirdPost

end Lax455465Proofs.RamFractionEncoding

end

section

namespace Lax455465Proofs.RamVectorEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding

def encode (qs:List ℚ):List ℕ:=qs.flatMap encodeRational

@[simp] theorem length_encode (qs:List ℚ):(encode qs).length=3*qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ) (words:List ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ encode (qs.take (σ.vars index))) "lp.word" σ∧
    σ.vars "lp.position"=words.length+3*σ.vars index∧
    words.length+3*qs.length < (σ.arrs "lp.word").length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+3*qs.length+3 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num.natAbs < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput qs[i] τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:"lp.position" ∉ body.wvars)
    (hbodyArray:"lp.word" ∉ body.warrs)
    (hemitIndex:index∉ RamFractionEncoding.emit.wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B RamFractionEncoding.emit σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ "lp.position"):
    Spec B (fun σ => R σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*qs.length < (σ.arrs "lp.word").length) (command index limit body)
      (fun _ τ => R τ∧ Prefix (words ++ encode qs) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*qs.length) ((K+35)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs words τ∧ τ.vars index=σ.vars index+1)
      (K+31):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ encode (qs.take i)).length=words.length+3*i:=by
      simp only [List.length_append,length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars "lp.position"=words.length+3*i:=
      (hproduce.frame_var "lp.position" hbodyPosition).trans hpos
    have hpν:Prefix (words ++ encode (qs.take i)) "lp.word" ν:=by
      simpa only [Prefix,hproduce.frame_arr "lp.word" hbodyArray] using hp
    have hroomν:words.length+3*qs.length < (ν.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hproduce "lp.word"]
    obtain ⟨μ,hemit,hemitted⟩:=RamFractionEncoding.emit_spec B qs[i] (words ++ encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+3*qs.length < (μ.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hemit "lp.word"]
    have hpμ:Prefix (words ++ encode (qs.take (i+1))) "lp.word" μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars "lp.position"=words.length+3*(i+1):=by rw [hpLen] at hemitted; omega
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
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words) qs.length (K+31)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamVectorEncoding

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem variable_frame (coefficients:List ℕ) (x:String) (hx:x ≠ "poly.value"):
    x∉ (command coefficients).wvars:=by
  induction coefficients with
  | nil => simp [command,Com.wvars,hx]
  | cons a rest ih => simp [command,Com.wvars,ih,hx]

theorem arrays_frame (coefficients:List ℕ):(command coefficients).warrs=[]:=by
  induction coefficients with
  | nil => simp [command,Com.warrs]
  | cons a rest ih => simp [command,Com.warrs,ih]

end Lax455465Proofs.RamPolynomial

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

namespace Lax263307Proofs.NativeRationalBounds

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem vector_words (B M n:ℕ) (x:Fin n→ ℚ) (h1:1< B) (hM:M< B)
    (hx:∀ i,Bounded M (x i)):
    ∀ v∈Lax109476.RationalEncoding.encodeVector x,v< B:=by
  intro v hv
  simp only [Lax109476.RationalEncoding.encodeVector,List.mem_flatMap,List.mem_ofFn] at hv
  obtain ⟨q,⟨i,rfl⟩,hv⟩:=hv
  simp only [Lax109476.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl
  · split_ifs <;> omega
  · exact (hx i).1.trans_lt hM
  · exact (hx i).2.trans_lt hM

end Lax263307Proofs.NativeRationalBounds

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

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCatalogMetadata

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

theorem data_frame {n B K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"catalog.count"∉c.wvars)
    (h2:"catalog.mask"∉c.warrs) (h3:"search.graph"∉c.warrs) (hσ:Data G r σ):Data G r τ:=by
  rcases hσ with ⟨hn,hc,hm,hg,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "catalog.count" h1).trans hc,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "catalog.mask" h2] using hm
  · simpa only [Prefix,rr.frame_arr "search.graph" h3] using hg
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

end Lax263307Proofs.NativeCatalogMetadata

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

namespace Lax263307Proofs.NativeAttemptReply

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

theorem none_spec (B n ret:ℕ) (hB:n+ret+5< B):
    Spec B (fun σ => σ.vars "graph.n"=n) (noneCommand ret)
      (fun _ τ => τ.vars "graph.n"=n∧ NativeTargetDriver.Reply (none:Option (Finset (Fin n))) τ∧
        τ.vars "machine.phase"=ret) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "graph.n") n) (And (@NativeTargetDriver.Reply n (@none (Finset (Fin n))) τ) (@Eq Nat (Env.vars τ "machine.phase") ret))) σ; let c1:Env:=Env.setVar σ "recursion.return.tag" ((0:Nat)); let c2:Env:=Env.setVar c1 "recursion.return.mask" ((0:Nat)); let c3:Env:=Env.setVar c2 "machine.phase" ret; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ret)); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "recursion.return.mask" (Expr.lit ((0:Nat))); let c11:String→ Nat:=Env.vars c3; @Exists.intro Env (fun (σ':Env) => And (Run B (noneCommand ret) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (noneCommand ret) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (noneCommand ret) σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "recursion.return.tag" (Expr.lit ((0:Nat)))) (Com.seq c10 (Com.assign "machine.phase" (Expr.lit ret))) σ c1 c3 c6 c9 (RunStep.assign B σ "recursion.return.tag" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8286_0_0_0))) (RunStep.seq B c10 (Com.assign "machine.phase" (Expr.lit ret)) c1 c2 c3 c6 c8 (RunStep.assign B c1 "recursion.return.mask" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g8286_0_0_1))) (RunStep.assign B c2 "machine.phase" (Expr.lit ret) ret (RunStep.eval_lit B ret c2 (?nAX_g8286_0_0_2))))) (?nAX_g8286_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8286_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeAttemptReply

end

section

namespace Lax263307Proofs.NativeSlice

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def Context (source:String) (front xs tail:List ℕ) (σ:Env):Prop:=
  Prefix (front++(xs++tail)) source σ∧ σ.vars "slice.start"=front.length

theorem read_spec (B:ℕ) (source:String) (front xs tail:List ℕ)
    (i:ℕ) (hi:i< xs.length) (hB:front.length+xs.length+1< B) (hv:xs[i]< B):
    Spec B (fun σ => Context source front xs tail σ∧ σ.vars "fill.i"=i) (read source)
      (fun _ τ => Context source front xs tail τ∧ τ.vars "fill.value"=xs[i]) 5:=by
  rintro σ ⟨⟨hp,hstart⟩,hindex⟩
  have hlen:front.length+i<(front++(xs++tail)).length:=by simp; omega
  have hget:(σ.arrs source)[front.length+i]?=some xs[i]:=by
    have hh:=hp (front.length+i) hlen
    simpa only [List.getElem_append_right (by omega:front.length≤ front.length+i),
      Nat.add_sub_cancel_left,List.getElem_append_left hi] using hh
  have hroom:front.length+i<(σ.arrs source).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  (expose_names;
    (refine let c0:Nat:= @getElem (List Nat) Nat Nat (fun (as:List Nat) (i_1:Nat) => Nat.lt i_1 (@List.length Nat as)) (@List.instGetElemNatLtLength Nat) xs i hi; let c1:Env→ Prop:=(fun (x τ:Env) => And (Context source front xs tail τ) (@Eq Nat (Env.vars τ "fill.value") c0)) σ; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 (Env.vars σ "slice.start") (Env.vars σ "fill.i"); let c4:Nat:= @List.getD Nat (Env.arrs σ source) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "fill.value" c4; let c6:Expr:=Expr.get source (Expr.add (Expr.var "slice.start") (Expr.var "fill.i")); @Exists.intro Env (fun (σ':Env) => And (Run B (read source) σ σ' ((5:Nat))) (c1 σ')) c5 (@And.intro (Run B (read source) σ c5 ((5:Nat))) (c1 c5) (RunStep.mono B (read source) σ c5 (c2 ((1:Nat)) (Expr.size c6)) ((5:Nat)) (RunStep.assign B σ "fill.value" c6 c4 (RunStep.eval_get B σ source (Expr.add (Expr.var "slice.start") (Expr.var "fill.i")) c3 (RunStep.eval_add B σ (Expr.var "slice.start") (Expr.var "fill.i") (Env.vars σ "slice.start") (Env.vars σ "fill.i") (RunStep.eval_var B σ "slice.start" (?nAX_g8333_0_0_0)) (RunStep.eval_var B σ "fill.i" (?nAX_g8333_0_0_1)) (?nAX_g8333_0_0_2)) (?nAX_g8333_0_0_3) ?_)) (?nAX_g8333_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8333_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,Prefix]

theorem command_spec (B:ℕ) (source target:String) (front xs tail:List ℕ)
    (hne:source≠target) (hB:front.length+xs.length+1< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Context source front xs tail σ∧ σ.vars "fill.length"=xs.length∧
      xs.length≤(σ.arrs target).length) (command source target)
      (fun _ τ => Context source front xs tail τ∧ Prefix xs target τ) (16*xs.length+6):=by
  have hh:=NativeTabulate.command_spec B xs target (Context source front xs tail) (read source) 5
    (by omega) hv (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by simp [read,Com.warrs])
    (fun σ h => by simpa only [Context,Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_false] using h)
    (fun σ τ rr h => by
      simpa only [Context,Prefix,rr.frame_arr source (by simp [NativeTabulate.append,RamWordBuffer.append,Com.warrs,hne]),
        rr.frame_var "slice.start" (by simp [NativeTabulate.append,RamWordBuffer.append,Com.wvars])] using h)
    (fun i hi => read_spec B source front xs tail i hi hB (hv _ (List.getElem_mem hi)))
  exact hh

end Lax263307Proofs.NativeSlice

end

section

namespace Lax263307Proofs.NativeProgramCache

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem copy_spec (B:ℕ) (source target lengthVar:String) (xs:List ℕ)
    (hne:source≠target) (hB:xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix xs source σ∧ σ.vars lengthVar=xs.length∧ xs.length≤(σ.arrs target).length)
      (copy source target lengthVar)
      (fun _ τ => Prefix xs source τ∧ Prefix xs target τ) (16*xs.length+10):=by
  rintro σ ⟨hp,hlen,hroom⟩
  let ν:=σ.setVar "fill.length" xs.length
  have r1:Run B (.assign "fill.length" (.var lengthVar)) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega)⟩)
  let μ:=ν.setVar "slice.start" 0
  have r2:Run B (.assign "slice.start" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (show 0< B by omega))
  obtain ⟨τ,r3,p3⟩:=NativeSlice.command_spec B source target [] xs [] hne (by simp; omega) hv μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,(r1.seq r2).frame_arr source (by simp [Com.warrs])] using hp,
      by rfl⟩,by simp [μ,ν],by rw [RamFrames.run_array_length (r1.seq r2)]; exact hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    by simpa only [NativeSlice.Context,List.nil_append,List.append_nil] using p3.1.1,p3.2⟩

theorem restore_spec (B:ℕ) (xs:List ℕ) (hB:xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix xs "moment.program" σ∧ σ.vars "node.programLength"=xs.length∧
      xs.length≤(σ.arrs "lp.input").length) restore
      (fun _ τ => Prefix xs "lp.input" τ∧ Prefix xs "moment.program" τ∧
        τ.vars "node.programLength"=xs.length) (16*xs.length+10):=by
  rintro σ ⟨hp,hlen,hroom⟩
  obtain ⟨τ,rr,p⟩:=copy_spec B "moment.program" "lp.input" "node.programLength" xs (by decide) hB hv σ
    ⟨hp,hlen,hroom⟩
  exact ⟨τ,rr,p.2,p.1,(rr.frame_var "node.programLength" (by decide)).trans hlen⟩

end Lax263307Proofs.NativeProgramCache

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

namespace Lax263307Proofs.NativeRoundedQuery

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch

theorem vector_length {n:ℕ} (v:Fin n→ ℚ):(encodeVector v).length=3*n:=by
  simp [encodeVector,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const] <;> ring

end Lax263307Proofs.NativeRoundedQuery

end

section

namespace Lax263307Proofs.NativeArrayBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

theorem big_step {B K:ℕ} {c:Com} {σ τ:Env} (rr:BigStepB B c σ τ K)
    (hb:Bounded B σ):Bounded B τ:=by
  induction rr with
  | skip => exact hb
  | assign _ => exact hb
  | store hi he hj =>
    intro a z hz
    simp only [arrs_setArr] at hz
    split_ifs at hz with h
    · obtain hz|rfl:=List.mem_or_eq_of_mem_set hz
      · exact hb _ _ hz
      · exact Expr.lt_of_evalB he
    · exact hb _ _ hz
  | seq _ _ ih ih' => exact ih' (ih hb)
  | ite_true _ _ ih => exact ih hb
  | ite_false _ _ ih => exact ih hb
  | while_true _ _ _ ih ih' => exact ih' (ih hb)
  | while_false _ => exact hb
  | read _ => exact hb
  | write _ => exact hb

theorem run {B K:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hb:Bounded B σ):Bounded B τ:=by
  obtain ⟨_,_,h⟩:=rr
  exact big_step h hb

theorem prefix_words {B:ℕ} {σ:Env} {xs:List ℕ} {a:String} (hb:Bounded B σ)
    (hp:Prefix xs a σ):∀ z∈ xs,z < B:=by
  intro z hz
  obtain ⟨i,hi,hz⟩:=List.getElem_of_mem hz
  have he:=hp i hi
  rw [hz] at he
  exact hb a z (List.mem_of_getElem? he)

end Lax263307Proofs.NativeArrayBounds

end

section

namespace Lax263307Proofs.NativeScaleFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamArithmetic
open NativeSignedArithmetic

theorem value (sign n d s:ℕ):fractionValue sign (n*s) d=fractionValue sign n d*(s:ℚ):=by
  unfold fractionValue
  split_ifs <;> push_cast <;> ring

theorem bounds (M s:ℕ) (q:ℚ) (hs:s≤ M) (hq:Bounded M q):
    Bounded (M^2) (q*(s:ℚ)):=by
  have hM:1≤ M:=q.den_pos.trans_le hq.2
  let sign:=RamLpRationalRead.sign q
  have hv:fractionValue sign q.num.natAbs q.den=q:=RamLpRationalRead.value_eq q
  have he:fractionValue sign (q.num.natAbs*s) q.den=q*(s:ℚ):=by rw [value,hv]
  obtain ⟨hn,hd⟩:=fractionValue_num_den sign (q.num.natAbs*s) q.den q.den_pos
  rw [he] at hn hd
  constructor
  · rw [hn]
    exact (Nat.div_le_self _ _).trans (by simpa only [pow_two] using Nat.mul_le_mul hq.1 hs)
  · rw [hd]
    exact (Nat.div_le_self _ _).trans (hq.2.trans (by nlinarith only [hM]))

theorem command_spec (B M s:ℕ) (q:ℚ) (hB:2*M^2+3< B) (hs:s≤ M) (hq:Bounded M q):
    Spec B (fun σ => FractionOutput q σ∧ σ.vars "scale.value"=s) command
      (fun _ τ => FractionOutput (q*(s:ℚ)) τ) (36*M.size+20):=by
  have hMpos:1≤ M:=q.den_pos.trans_le hq.2
  have hM:M< B:=by nlinarith only [hB,hMpos]
  have hprod:q.num.natAbs*s≤ M^2:=by simpa only [pow_two] using Nat.mul_le_mul hq.1 hs
  have hnum:q.num.natAbs*s< B:=hprod.trans_lt (by omega:M^2< B)
  rintro σ ⟨hqσ,hsσ⟩
  let ν:=σ.setVar "rat.n" (q.num.natAbs*s)
  have r1:Run B (.assign "rat.n" (.mul (.var "rat.n") (.var "scale.value"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hqσ.2.1.symm,hqσ.2.1 ▸ hq.1.trans_lt hM⟩)
      (by rw [evalB_var_iff]; exact ⟨hsσ.symm,hsσ ▸ hs.trans_lt hM⟩) hnum)
  obtain ⟨τ,r2,p2⟩:=normalizeFraction_output_spec B (σ.vars "rat.s") (q.num.natAbs*s) q.den
    hqσ.2.2.2 hnum (hq.2.trans_lt hM) q.den_pos ν
    ⟨by rfl,(r1.frame_var "rat.d" (by decide)).trans hqσ.2.2.1,
      r1.frame_var "rat.s" (by decide)⟩
  have he:fractionValue (σ.vars "rat.s") (q.num.natAbs*s) q.den=q*(s:ℚ):=by
    rw [value]
    have hv:fractionValue (σ.vars "rat.s") q.num.natAbs q.den=q:=by
      simpa only [hqσ.2.1,hqσ.2.2.1] using hqσ.1
    rw [hv]
  exact ⟨τ,(r1.seq r2).mono (by have hsize:=Nat.size_le_size hq.2; omega),by simpa only [he] using p2⟩

end Lax263307Proofs.NativeScaleFraction

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeProjectionCenter

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding NativeSignedArithmetic

def Context {n:ℕ} (x:Fin n→ ℚ) (σ:Env):Prop:=
  σ.vars "vec.n"=n∧ Prefix (encodeVector x) "round.center" σ

def Q {n:ℕ} (x:Fin n→ ℚ) (σ:Env):Prop:=Context x σ∧ σ.vars "scale.value"=4*n

theorem q_frame {B n t:ℕ} {x:Fin n→ ℚ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hs:Q x σ) (hn:"vec.n"∉c.wvars) (hv:"scale.value"∉c.wvars)
    (ha:"round.center"∉c.warrs):Q x τ:=by
  refine ⟨⟨(rr.frame_var _ hn).trans hs.1.1,?_⟩,(rr.frame_var _ hv).trans hs.2⟩
  simpa only [Prefix,rr.frame_arr "round.center" ha] using hs.1.2

theorem setup_spec (B n:ℕ) (x:Fin n→ ℚ) (hB:4*n+5< B):
    Spec B (Context x) setup (fun _ τ => Q x τ∧ τ.vars "lp.position"=0) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x_1 τ:Env) => And (@Q n x τ) (@Eq Nat (Env.vars τ "lp.position") ((0:Nat)))) σ; let c1:Nat:=Nat.mul ((4:Nat)) (Env.vars σ "vec.n"); let c2:Env:=Env.setVar σ "scale.value" c1; let c3:Env:=Env.setVar c2 "lp.position" ((0:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Expr:=Expr.mul (Expr.lit ((4:Nat))) (Expr.var "vec.n"); let c7:Nat:=c5 (Expr.size c6); let c8:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B setup σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B setup σ c3 (c4 c7 c8) ((6:Nat)) (RunStep.seq B (Com.assign "scale.value" c6) (Com.assign "lp.position" (Expr.lit ((0:Nat)))) σ c2 c3 c7 c8 (RunStep.assign B σ "scale.value" c6 c1 (RunStep.eval_mul B σ (Expr.lit ((4:Nat))) (Expr.var "vec.n") ((4:Nat)) (Env.vars σ "vec.n") (RunStep.eval_lit B ((4:Nat)) σ (?nAX_g8418_0_0_0)) (RunStep.eval_var B σ "vec.n" ?_) ?_)) (RunStep.assign B c2 "lp.position" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g8418_0_0_1)))) (?nAX_g8418_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8418_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8418_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8418_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Q,Context,Prefix,Env.setVar]
  all_goals omega

theorem read_spec (B M n:ℕ) (x:Fin n→ ℚ) (i:ℕ) (hi:i< n)
    (hB:2*M^2+3< B) (hshape:4*n+5< B) (hscale:4*n≤ M) (hx:∀ j,Bounded M (x j)):
    Spec B (fun σ => Q x σ∧ σ.vars "scale.i"=i) read
      (fun _ τ => Q x τ∧ FractionOutput (Lax263307.ProjectedOracle.raw x ⟨i,hi⟩) τ)
      (36*M.size+41):=by
  let j:Fin n:= ⟨i,hi⟩
  have hM:M< B:=by have hp:=(hx j).2; have hd:=(x j).den_pos; nlinarith only [hB,hp,hd]
  rintro σ ⟨hs,hiσ⟩
  let ν:=σ.setVar "read.cursor" (3*i)
  have r1:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "scale.i"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 3< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hiσ.symm,hiσ ▸ (by omega)⟩) (by change 3*i< B; omega))
  obtain ⟨μ,r2,p2⟩:=NativeRationalRead.vector_entry_spec B "round.center" [] [] (List.ofFn x)
    i (by simpa only [List.length_ofFn] using hi) (by omega) (by simp; omega)
    (by simpa only [List.getElem_ofFn] using (hx j).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (hx j).2.trans_lt hM) ν
    ⟨by simpa only [List.nil_append,List.append_nil,Prefix,r1.frame_arr "round.center" (by decide),
      NativeRationalTabulate.words,encodeVector] using hs.1.2,by simp [ν]⟩
  have hqμ:FractionOutput (x j) μ:=by simpa only [List.getElem_ofFn] using p2.1
  have hsμ:=((r1.seq r2).frame_var "scale.value" (by decide)).trans hs.2
  obtain ⟨τ,r3,p3⟩:=NativeScaleFraction.command_spec B M (4*n) (x j) hB hscale (hx j) μ ⟨hqμ,hsμ⟩
  have he:x j*(4*n:ℕ)=Lax263307.ProjectedOracle.raw x j:=by
    simp only [Lax263307.ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat]
    ring
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    q_frame (r1.seq (r2.seq r3)) hs (by decide) (by decide) (by decide),by simpa only [he] using p3⟩

theorem vector_spec (B M n:ℕ) (x:Fin n→ ℚ)
    (hB:2*M^2+3< B) (hshape:4*n+5< B) (hscale:4*n≤ M) (hx:∀ j,Bounded M (x j)):
    Spec B (fun σ => Context x σ∧ 3*n<(σ.arrs "lp.word").length) vector
      (fun _ τ => Q x τ∧ Prefix (encodeVector (Lax263307.ProjectedOracle.raw x)) "lp.word" τ∧
        τ.vars "lp.position"=3*n) ((36*M.size+76)*n+12):=by
  have hheight (j:Fin n):Bounded (M^2) (Lax263307.ProjectedOracle.raw x j):=by
    have hh:=NativeScaleFraction.bounds M (4*n) (x j) hscale (hx j)
    have he:x j*(4*n:ℕ)=Lax263307.ProjectedOracle.raw x j:=by
      simp only [Lax263307.ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simpa only [he] using hh
  have hh:=RamVectorEncoding.command_spec B (36*M.size+41) (Q x) "scale.i" "vec.n"
    (List.ofFn (Lax263307.ProjectedOracle.raw x)) [] read (by omega) (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).1.trans_lt (by omega))
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).2.trans_lt (by omega))
    (fun σ hs => by simpa only [List.length_ofFn] using hs.1.1)
    (fun σ k hs => by simpa only [Q,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hs)
    (fun i hi => by simpa only [List.getElem_ofFn] using read_spec B M n x i (by simpa using hi) hB hshape hscale hx)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hs => q_frame rr hs (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hs,hroom⟩
  obtain ⟨ν,r1,p1⟩:=setup_spec B n x hshape σ hs
  obtain ⟨τ,r2,p2⟩:=hh ν ⟨p1.1,by simp [Prefix],by simpa only [List.length_nil] using p1.2,
    by simpa only [List.length_nil,Nat.zero_add,List.length_ofFn,RamFrames.run_array_length r1] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn]; nlinarith only []),p2.1,
    by simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1,
    by simpa only [List.length_nil,Nat.zero_add,List.length_ofFn] using p2.2.2⟩

theorem command_spec (B M n:ℕ) (x:Fin n→ ℚ)
    (hB:2*M^2+3< B) (hshape:4*n+5< B) (hscale:4*n≤ M) (hx:∀ j,Bounded M (x j)):
    Spec B (fun σ => Context x σ∧ 3*n<(σ.arrs "lp.word").length∧
      3*n≤(σ.arrs "projection.center").length) command
      (fun _ τ => Context x τ∧ Prefix (encodeVector (Lax263307.ProjectedOracle.raw x)) "projection.center" τ)
      ((36*M.size+124)*n+22):=by
  have hlen:=NativeRoundedQuery.vector_length (Lax263307.ProjectedOracle.raw x)
  have hw:=NativeRationalBounds.vector_words B (M^2) n (Lax263307.ProjectedOracle.raw x) (by omega) (by omega)
    (fun j => by
      have hh:=NativeScaleFraction.bounds M (4*n) (x j) hscale (hx j)
      simpa only [Lax263307.ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh)
  rintro σ ⟨hs,hword,hroom⟩
  obtain ⟨ν,r1,p1⟩:=vector_spec B M n x hB hshape hscale hx σ ⟨hs,hword⟩
  obtain ⟨τ,r2,p2⟩:=NativeProgramCache.copy_spec B "lp.word" "projection.center" "lp.position"
    (encodeVector (Lax263307.ProjectedOracle.raw x)) (by decide) (by rw [hlen]; omega) hw ν
    ⟨p1.2.1,by simpa only [hlen] using p1.2.2,by rw [hlen,RamFrames.run_array_length r1]; exact hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; nlinarith only []),
    (q_frame r2 p1.1 (by decide) (by decide) (by decide)).1,p2.2⟩

end Lax263307Proofs.NativeProjectionCenter

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding
open Lax263307

def Context (n D R:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "node.D"=D∧ σ.vars "node.floorPower"=R

theorem coordinates (n D R:ℕ) (hn:0< n) (hD:0< D) (hR:0< R):
    (tolerance n D R).num=1∧ (tolerance n D R).den=denominator n D R:=by
  have hp:0< denominator n D R:=by unfold denominator; positivity
  have he:tolerance n D R=mkRat 1 (denominator n D R):=by simp [tolerance,Rat.mkRat_eq_div]
  rw [he]
  simp [Rat.num_mkRat,Rat.den_mkRat,ne_of_gt hp]

theorem setup_spec (B n D R:ℕ) (hn:0< n) (hD:0< D) (hR:0< R) (hB:guard n D R< B):
    Spec B (Context n D R) setup
      (fun _ τ => Context n D R τ∧ FractionOutput (tolerance n D R) τ∧ τ.vars "lp.position"=0) 18:=by
  have hcoords:=coordinates n D R hn hD hR
  have hv:fractionValue 0 1 (denominator n D R)=tolerance n D R:=by simp [fractionValue,tolerance]
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (Context n D R τ) (And (FractionOutput (tolerance n D R) τ) (@Eq Nat (Env.vars τ "lp.position") ((0:Nat))))) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((1:Nat)); let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:String→ Nat:=Env.vars c2; let c5:Nat:=c4 "graph.n"; let c6:Nat:=c3 ((32:Nat)) c5; let c7:Nat:=c3 c6 c5; let c8:Nat:=c4 "node.D"; let c9:Nat:=c3 c7 c8; let c10:Nat:=c3 c9 c8; let c11:Nat:=c4 "node.floorPower"; let c12:Nat:=c3 c10 c11; let c13:Env:=Env.setVar c2 "rat.d" c12; let c14:Env:=Env.setVar c13 "lp.position" ((0:Nat)); let c15:Nat→ Nat→ Nat:=Nat.add; let c16:Nat→ Nat:=c15 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.lit ((0:Nat)))); let c18:Nat:=c16 (Expr.size (Expr.lit ((1:Nat)))); let c19:Expr:=Expr.mul (Expr.lit ((32:Nat))) (Expr.var "graph.n"); let c20:Expr:=Expr.mul c19 (Expr.var "graph.n"); let c21:Expr:=Expr.mul c20 (Expr.var "node.D"); let c22:Expr:=Expr.mul c21 (Expr.var "node.D"); let c23:Expr:=Expr.mul c22 (Expr.var "node.floorPower"); let c24:Nat:=c16 (Expr.size c23); let c25:Nat:=c15 c24 c17; let c26:Nat:=c15 c18 c25; let c27:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c28:Com:=Com.assign "rat.d" c23; let c29:Com:=Com.assign "lp.position" (Expr.lit ((0:Nat))); let c30:Com:=Com.seq c28 c29; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((18:Nat))) (c0 σ')) c14 (@And.intro (Run B setup σ c14 ((18:Nat))) (c0 c14) (RunStep.mono B setup σ c14 (c15 c17 c26) ((18:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c27 c30) σ c1 c14 c17 c26 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8429_0_0_0))) (RunStep.seq B c27 c30 c1 c2 c14 c18 c25 (RunStep.assign B c1 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c1 ?_)) (RunStep.seq B c28 c29 c2 c13 c14 c24 c17 (RunStep.assign B c2 "rat.d" c23 c12 (RunStep.eval_mul B c2 c22 (Expr.var "node.floorPower") c10 c11 (RunStep.eval_mul B c2 c21 (Expr.var "node.D") c9 c8 (RunStep.eval_mul B c2 c20 (Expr.var "node.D") c7 c8 (RunStep.eval_mul B c2 c19 (Expr.var "graph.n") c6 c5 (RunStep.eval_mul B c2 (Expr.lit ((32:Nat))) (Expr.var "graph.n") ((32:Nat)) c5 (RunStep.eval_lit B ((32:Nat)) c2 ?_) (RunStep.eval_var B c2 "graph.n" ?_) ?_) (RunStep.eval_var B c2 "graph.n" ?_) ?_) (RunStep.eval_var B c2 "node.D" ?_) ?_) (RunStep.eval_var B c2 "node.D" ?_) ?_) (RunStep.eval_var B c2 "node.floorPower" ?_) ?_)) (RunStep.assign B c13 "lp.position" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c13 (?nAX_g8429_0_0_1)))))) (?nAX_g8429_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8429_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8429_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8429_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,FractionOutput,Env.setVar,guard,denominator,hcoords.1,hcoords.2,hv]
  all_goals omega

theorem context_frame {B n D R t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hs:Context n D R σ) (hn:"graph.n"∉c.wvars) (hD:"node.D"∉c.wvars)
    (hR:"node.floorPower"∉c.wvars):Context n D R τ:=
  ⟨(rr.frame_var _ hn).trans hs.1,(rr.frame_var _ hD).trans hs.2.1,(rr.frame_var _ hR).trans hs.2.2⟩

theorem command_spec (B n D R:ℕ) (hn:0< n) (hD:0< D) (hR:0< R) (hB:guard n D R< B):
    Spec B (fun σ => Context n D R σ∧ 3≤(σ.arrs "lp.word").length∧
      3≤(σ.arrs "projection.tolerance").length) command
      (fun _ τ => Context n D R τ∧ Prefix (encodeRational (tolerance n D R)) "projection.tolerance" τ) 103:=by
  have hcoords:=coordinates n D R hn hD hR
  have hd:denominator n D R< B:=by dsimp only [guard] at hB; omega
  have h1:1< B:=by dsimp only [guard] at hB; omega
  have he:encodeRational (tolerance n D R)=[0,1,denominator n D R]:=by
    simp [encodeRational,hcoords.1,hcoords.2]
  have hw:∀ z∈encodeRational (tolerance n D R),z< B:=by
    rw [he]
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> omega
  have hlen:(encodeRational (tolerance n D R)).length=3:=by rw [he]; rfl
  rintro σ ⟨hs,hword,hroom⟩
  obtain ⟨ν,r1,p1⟩:=setup_spec B n D R hn hD hR hB σ hs
  obtain ⟨μ,r2,p2⟩:=RamFractionEncoding.emit_spec B (tolerance n D R) [] h1
    (by simpa only [hcoords.1,Int.natAbs_one] using h1) (by rw [hcoords.2]; exact hd)
    (by dsimp only [guard] at hB; simp; omega) ν
    ⟨p1.2.1,by simp [Prefix],by simpa only [List.length_nil] using p1.2.2,
      by rw [RamFrames.run_array_length r1]; simp; omega⟩
  obtain ⟨τ,r3,p3⟩:=NativeProgramCache.copy_spec B "lp.word" "projection.tolerance" "lp.position"
    (encodeRational (tolerance n D R)) (by decide) (by rw [hlen]; dsimp only [guard] at hB; omega) hw μ
    ⟨by simpa only [List.nil_append] using p2.1,
      by simpa only [hlen,List.length_nil,Nat.zero_add] using p2.2,
      by rw [hlen,RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]),
    context_frame (r2.seq r3) p1.1 (by decide) (by decide) (by decide),p3.2⟩

end Lax263307Proofs.NativeNodeTolerance

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeProjectionPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding NativeSignedArithmetic

theorem command_spec (B M n D R m N:ℕ) (P:Program ℚ m N) (x:Fin N→ ℚ)
    (hn:0< n) (hD:0< D) (hR:0< R)
    (hLP:(encodeProgram P).length+2< B) (hB:2*M^2+3< B)
    (hshape:4*N+5< B) (hscale:4*N≤ M) (hx:∀ j,Bounded M (x j))
    (htol:NativeNodeTolerance.guard n D R< B):
    Spec B (fun σ => NativeProjectionCenter.Context x σ∧ NativeNodeTolerance.Context n D R σ∧
      Prefix (encodeProgram P) "moment.program" σ∧ σ.vars "node.programLength"=(encodeProgram P).length∧
      NativeArrayBounds.Bounded B σ∧ (encodeProgram P).length≤(σ.arrs "lp.input").length∧
      3*N<(σ.arrs "lp.word").length∧ 3*N≤(σ.arrs "projection.center").length∧
      3≤(σ.arrs "lp.word").length∧ 3≤(σ.arrs "projection.tolerance").length) command
      (fun _ τ => NativeProjectionCenter.Context x τ∧ NativeNodeTolerance.Context n D R τ∧
        Prefix (encodeProgram P) "lp.input" τ∧
        Prefix (encodeVector (Lax263307.ProjectedOracle.raw x)) "projection.center" τ∧
        Prefix (encodeRational (NativeNodeTolerance.tolerance n D R)) "projection.tolerance" τ)
      (16*(encodeProgram P).length+(36*M.size+124)*N+135):=by
  rintro σ ⟨hc,ht,hp,hlen,hbounded,hinput,hword,hcenter,hword3,htolerance⟩
  obtain ⟨ν,r1,p1⟩:=NativeProgramCache.restore_spec B (encodeProgram P) hLP
    (NativeArrayBounds.prefix_words hbounded hp) σ ⟨hp,hlen,hinput⟩
  have hc1:NativeProjectionCenter.Context x ν:=
    ⟨(r1.frame_var "vec.n" (by decide)).trans hc.1,
      by simpa only [Prefix,r1.frame_arr "round.center" (by decide)] using hc.2⟩
  obtain ⟨μ,r2,p2⟩:=NativeProjectionCenter.command_spec B M N x hB hshape hscale hx ν
    ⟨hc1,by rw [RamFrames.run_array_length r1]; exact hword,
      by rw [RamFrames.run_array_length r1]; exact hcenter⟩
  have ht2:=NativeNodeTolerance.context_frame (r1.seq r2) ht (by decide) (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩:=NativeNodeTolerance.command_spec B n D R hn hD hR htol μ
    ⟨ht2,by rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hword3,
      by rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact htolerance⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by nlinarith only []),
    ⟨(r3.frame_var "vec.n" (by decide)).trans p2.1.1,
      by simpa only [Prefix,r3.frame_arr "round.center" (by decide)] using p2.1.2⟩,
    p3.1,?_,?_,p3.2⟩
  · simpa only [Prefix,(r2.seq r3).frame_arr "lp.input" (by decide)] using p1.1
  · simpa only [Prefix,r3.frame_arr "projection.center" (by decide)] using p2.2

end Lax263307Proofs.NativeProjectionPrepare

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

namespace Lax263307Proofs.NativeCutRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding NativeSignedArithmetic

def Context {n:ℕ} (a:Fin n→ ℚ) (σ:Env):Prop:=
  Prefix (encodeVector a) "cut.source" σ∧ σ.vars "projection.n"=n

theorem command_spec (B M n:ℕ) (a:Fin n→ ℚ) (i:Fin n)
    (hM:M< B) (hs:3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Context a σ∧ σ.vars "cut.i"=i.val) command
      (fun _ τ => Context a τ∧ RamRational.FractionOutput (a i) τ) 21:=by
  rintro σ ⟨hc,hi⟩
  let ν:=σ.setVar "read.cursor" (3*i.val)
  have r1:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "cut.i"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega:3< B))
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega:i.val< B)⟩)
      (by change 3*i.val< B; omega))
  obtain ⟨τ,r2,p2⟩:=NativeRationalRead.vector_entry_spec B "cut.source" [] [] (List.ofFn a)
    i.val (by simpa using i.isLt) (by omega) (by simp; omega)
    (by simpa only [List.getElem_ofFn] using (ha i).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (ha i).2.trans_lt hM) ν
    ⟨by simpa only [List.nil_append,List.append_nil,NativeRationalTabulate.words,encodeVector,Prefix,ν,arrs_setVar] using hc.1,
      by simp [ν]⟩
  have rr:=r1.seq r2
  refine ⟨τ,rr,?_,by simpa only [List.getElem_ofFn] using p2.1⟩
  simpa only [Context,Prefix,rr.frame_arr "cut.source" (by decide),
    rr.frame_var "projection.n" (by decide)] using hc

end Lax263307Proofs.NativeCutRead

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

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

structure Data {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (σ:Env):Prop where
  cuts:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count:σ.vars "separator.count"=cs.length
  remaining:σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

end Lax263307Proofs.NativeCutPieces

end

section

namespace Lax263307Proofs.NativeScaledInteger

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational NativeSignedArithmetic

def value (q:ℚ) (D:ℕ):ℚ:=((q.num*(D/q.den:ℕ):ℤ):ℚ)

theorem numerator_value (q:ℚ) (s:ℕ)
    (hv:fractionValue s q.num.natAbs q.den=q):
    fractionValue s q.num.natAbs 1=(q.num:ℚ):=by
  have hd:(q.den:ℚ)≠0:=by exact_mod_cast q.den_ne_zero
  calc
    _=fractionValue s q.num.natAbs q.den*(q.den:ℚ):=by
      unfold fractionValue
      split_ifs <;> simp [hd]
    _=q*(q.den:ℚ):=by rw [hv]
    _=(q.num:ℚ):=((div_eq_iff hd).mp q.num_div_den).symm

theorem scaled_value (q:ℚ) (D s:ℕ)
    (hv:fractionValue s q.num.natAbs q.den=q):
    fractionValue s (q.num.natAbs*(D/q.den)) 1=value q D:=by
  have hmul:fractionValue s (q.num.natAbs*(D/q.den)) 1=
      fractionValue s q.num.natAbs 1*(D/q.den:ℕ):=by
    unfold fractionValue
    split_ifs <;> simp [Nat.cast_mul,neg_mul]
  rw [hmul,numerator_value q s hv]
  simp only [value,Int.cast_mul,Int.cast_natCast]

theorem magnitude (q:ℚ) (D:ℕ):(value q D).num.natAbs=q.num.natAbs*(D/q.den):=by
  simp only [value,Rat.num_intCast,Int.natAbs_mul,Int.natAbs_natCast]

theorem denominator (q:ℚ) (D:ℕ):(value q D).den=1:=by simp only [value,Rat.den_intCast]

theorem command_spec (B M D:ℕ) (q:ℚ) (h1:1< B) (hM:M< B) (hD:D< B)
    (hMD:M*D< B) (hq:Bounded M q):
    Spec B (fun σ => FractionOutput q σ∧ σ.vars "cut.denominator"=D) command
      (fun _ τ => FractionOutput (value q D) τ) 8:=by
  rintro σ ⟨h,hDσ⟩
  have hnum:q.num.natAbs*(D/q.den)< B:=
    (Nat.mul_le_mul hq.1 (Nat.div_le_self D q.den)).trans_lt hMD
  have hn:=hq.1.trans_lt hM
  have hd:=hq.2.trans_lt hM
  have hv:fractionValue (σ.vars "rat.s") q.num.natAbs q.den=q:=by
    simpa only [h.2.1,h.2.2.1] using h.1
  have hout:=scaled_value q D (σ.vars "rat.s") hv
  have hdiv:D/q.den< B:=(Nat.div_le_self _ _).trans_lt hD
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (value q D) τ) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "cut.denominator") (Env.vars σ "rat.d"); let c2:Nat:=Nat.mul (Env.vars σ "rat.n") c1; let c3:Env:=Env.setVar σ "rat.n" c2; let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Expr:=Expr.mul (Expr.var "rat.n") (Expr.div (Expr.var "cut.denominator") (Expr.var "rat.d")); let c8:Nat:=c6 (Expr.size c7); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((8:Nat))) (c0 σ')) c4 (@And.intro (Run B command σ c4 ((8:Nat))) (c0 c4) (RunStep.mono B command σ c4 (c5 c8 c9) ((8:Nat)) (RunStep.seq B (Com.assign "rat.n" c7) (Com.assign "rat.d" (Expr.lit ((1:Nat)))) σ c3 c4 c8 c9 (RunStep.assign B σ "rat.n" c7 c2 (RunStep.eval_mul B σ (Expr.var "rat.n") (Expr.div (Expr.var "cut.denominator") (Expr.var "rat.d")) (Env.vars σ "rat.n") c1 (RunStep.eval_var B σ "rat.n" ?_) (RunStep.eval_div B σ (Expr.var "cut.denominator") (Expr.var "rat.d") (Env.vars σ "cut.denominator") (Env.vars σ "rat.d") (RunStep.eval_var B σ "cut.denominator" (?nAX_g8981_0_0_0)) (RunStep.eval_var B σ "rat.d" ?_) ?_) ?_)) (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1))) (?nAX_g8981_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8981_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8981_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,magnitude,denominator]

end Lax263307Proofs.NativeScaledInteger

end

section

namespace Lax263307Proofs.NativeDenominatorData

open Lax263307.RationalCutBuffer

def product (qs:List ℚ):ℕ:=(qs.map Rat.den).prod

def partialProduct {n:ℕ} (a:Fin n→ ℚ) (i:ℕ):ℕ:=product ((List.ofFn a).take i)

theorem product_positive (qs:List ℚ):0< product qs:=by
  induction qs with
  | nil => simp [product]
  | cons q qs ih => exact Nat.mul_pos q.den_pos ih

theorem full_product {n:ℕ} (a:Fin n→ ℚ):partialProduct a n=denominator a:=by
  have ht:(List.ofFn a).take n=List.ofFn a:=by
    simpa only [List.length_ofFn] using (List.take_length:(List.ofFn a).take (List.ofFn a).length=List.ofFn a)
  rw [partialProduct,ht]
  simp only [product,denominator,List.map_ofFn,List.prod_ofFn,Function.comp_apply]

theorem partial_le {n:ℕ} (a:Fin n→ ℚ) (i:ℕ):partialProduct a i≤ denominator a:=by
  have hsplit:denominator a=partialProduct a i*product ((List.ofFn a).drop i):=by
    have ht:(List.ofFn a).take n=List.ofFn a:=by
      simpa only [List.length_ofFn] using (List.take_length:(List.ofFn a).take (List.ofFn a).length=List.ofFn a)
    have hf:product (List.ofFn a)=denominator a:=by
      simpa only [partialProduct,ht] using full_product a
    rw [←hf]
    conv_lhs => rw [←List.take_append_drop i (List.ofFn a)]
    simp only [partialProduct,product,List.map_append,List.prod_append]
  have hp:=product_positive ((List.ofFn a).drop i)
  rw [hsplit]
  nlinarith

theorem partial_step {n:ℕ} (a:Fin n→ ℚ) (i:Fin n):
    partialProduct a (i.val+1)=partialProduct a i.val*(a i).den:=by
  unfold partialProduct
  rw [List.take_succ_eq_append_getElem (by simpa using i.isLt)]
  simp only [product,List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Nat.mul_one,List.getElem_ofFn]

end Lax263307Proofs.NativeDenominatorData

end

section

namespace Lax263307Proofs.NativeCutCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutRead

def Data {n:ℕ} (a:Fin n→ ℚ) (σ:Env):Prop:=
  Context a σ∧ σ.vars "cut.denominator"=denominator a

theorem frame {n B K:ℕ} {a:Fin n→ ℚ} {σ τ:Env} {c:Com}
    (rr:Run B c σ τ K) (h:Data a σ) (hsource:"cut.source"∉c.warrs)
    (hN:"projection.n"∉c.wvars) (hD:"cut.denominator"∉c.wvars):Data a τ:=by
  simpa only [Data,Context,Prefix,rr.frame_arr "cut.source" hsource,
    rr.frame_var "projection.n" hN,rr.frame_var "cut.denominator" hD] using h

theorem command_spec (B M n:ℕ) (a:Fin n→ ℚ) (i:Fin n)
    (hB:M*denominator a+M+denominator a+3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Data a σ∧ σ.vars "cut.i"=i.val) command
      (fun _ τ => Data a τ∧ FractionOutput (integerNormal a i:ℚ) τ) 29:=by
  rintro σ ⟨hc,hi⟩
  obtain ⟨ν,r1,p1⟩:=NativeCutRead.command_spec B M n a i (by omega) (by omega) ha σ ⟨hc.1,hi⟩
  obtain ⟨τ,r2,p2⟩:=NativeScaledInteger.command_spec B M (denominator a) (a i)
    (by omega) (by omega) (by omega) (by omega) (ha i) ν
    ⟨p1.2,(r1.frame_var "cut.denominator" (by decide)).trans hc.2⟩
  have rr:=r1.seq r2
  exact ⟨τ,rr,frame rr hc (by decide) (by decide) (by decide),p2⟩

end Lax263307Proofs.NativeCutCoefficient

end

section

namespace Lax263307Proofs.NativeCutVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutCoefficient

theorem command_spec (B M n:ℕ) (a:Fin n→ ℚ)
    (hB:M*denominator a+M+denominator a+3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Data a σ∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Data a τ∧ Prefix (encodeVector (fun i => (integerNormal a i:ℚ))) "lp.word" τ∧
        τ.vars "lp.position"=3*n) (64*n+8):=by
  let values:=List.ofFn fun i => (integerNormal a i:ℚ)
  have hnum (i:Fin n):(integerNormal a i:ℚ).num.natAbs< B:=by
    change (NativeScaledInteger.value (a i) (denominator a)).num.natAbs< B
    rw [NativeScaledInteger.magnitude]
    exact (Nat.mul_le_mul (ha i).1 (Nat.div_le_self _ _)).trans_lt (by omega)
  have hden (i:Fin n):(integerNormal a i:ℚ).den< B:=by simp only [Rat.den_intCast]; omega
  have hh:=RamVectorEncoding.command_spec B 29 (Data a) "cut.i" "projection.n" values []
    NativeCutCoefficient.command (by omega) (by simp [values]; omega)
    (by intro i hi; simpa only [values,List.getElem_ofFn] using hnum ⟨i,by simpa [values] using hi⟩)
    (by intro i hi; simpa only [values,List.getElem_ofFn] using hden ⟨i,by simpa [values] using hi⟩)
    (fun σ h => by simpa only [values,List.length_ofFn] using h.1.2)
    (fun σ k h => by simpa only [Data,NativeCutRead.Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [values,List.getElem_ofFn] using NativeCutCoefficient.command_spec B M n a ⟨i,by simpa [values] using hi⟩ hB ha)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hc,hr⟩
  have r1:Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2:=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩:=hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hc (by decide) (by decide) (by decide),by simp [Prefix],by simp,by simpa only [values,List.length_ofFn,List.length_nil,Nat.zero_add,arrs_setVar] using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [values,List.length_ofFn,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,values,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [values,List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeCutVector

end

section

namespace Lax263307Proofs.NativeDenominatorProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeDenominatorData NativeCutRead

def Invariant {n:ℕ} (a:Fin n→ ℚ) (σ:Env):Prop:=
  Context a σ∧ σ.vars "cut.i"≤ n∧ σ.vars "cut.denominator"=partialProduct a (σ.vars "cut.i")

theorem update_spec (B n:ℕ) (a:Fin n→ ℚ) (i:Fin n)
    (hs:n+2< B) (hD:denominator a< B) (hd:(a i).den< B):
    Spec B (fun σ => σ.vars "cut.i"=i.val∧ σ.vars "cut.denominator"=partialProduct a i.val∧
      σ.vars "rat.d"=(a i).den) update
      (fun _ τ => τ.vars "cut.i"=i.val+1∧ τ.vars "cut.denominator"=partialProduct a (i.val+1)) 8:=by
  have hpart:partialProduct a i.val< B:=(partial_le a i.val).trans_lt hD
  have hnext:partialProduct a i.val*(a i).den< B:=by
    rw [←partial_step a i]
    exact (partial_le a (i.val+1)).trans_lt hD
  have hstep:=partial_step a i
  (expose_names;
    (refine fun (σ:Env) (a_1:And (@Eq Nat (Env.vars σ "cut.i") (@Fin.val n i)) (And (@Eq Nat (Env.vars σ "cut.denominator") (@partialProduct n a (@Fin.val n i))) (@Eq Nat (Env.vars σ "rat.d") (Rat.den (a i))))) => let c0:Prop:= @Eq Nat (Env.vars σ "cut.i") (@Fin.val n i); let c1:Prop:= @Eq Nat (Env.vars σ "cut.denominator") (@partialProduct n a (@Fin.val n i)); let c2:Prop:= @Eq Nat (Env.vars σ "rat.d") (Rat.den (a i)); let c3:Prop:=And c1 c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 (@Fin.val n i) ((1:Nat)); let c6:Nat:= @partialProduct n a c5; let c7:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "cut.i") c5) (@Eq Nat (Env.vars τ "cut.denominator") c6)) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((8:Nat))) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Nat:=Nat.mul (Env.vars σ "cut.denominator") (Env.vars σ "rat.d"); let c11:Env:=Env.setVar σ "cut.denominator" c10; let c12:Nat:=Env.vars c11 "cut.i"; let c13:Nat:=c4 c12 ((1:Nat)); let c14:Env:=Env.setVar c11 "cut.i" c13; let c15:Nat→ Nat:=c4 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.mul (Expr.var "cut.denominator") (Expr.var "rat.d"))); let c17:Expr:=Expr.add (Expr.var "cut.i") (Expr.lit ((1:Nat))); let c18:Nat:=c15 (Expr.size c17); let c19:String→ Nat:=Env.vars c14; @And.casesOn c0 c3 (fun (x:And c0 c3) => c9) a_1 fun (left:c0) (right:c3) => @And.casesOn c1 c2 (fun (x:c3) => c9) right fun (left_1:c1) (right_1:c2) => @Exists.intro Env c8 c14 (@And.intro (Run B update σ c14 ((8:Nat))) (c7 c14) (RunStep.mono B update σ c14 (c4 c16 c18) ((8:Nat)) (RunStep.seq B (Com.assign "cut.denominator" (Expr.mul (Expr.var "cut.denominator") (Expr.var "rat.d"))) (Com.assign "cut.i" c17) σ c11 c14 c16 c18 (RunStep.assign B σ "cut.denominator" (Expr.mul (Expr.var "cut.denominator") (Expr.var "rat.d")) c10 (RunStep.eval_mul B σ (Expr.var "cut.denominator") (Expr.var "rat.d") (Env.vars σ "cut.denominator") (Env.vars σ "rat.d") (RunStep.eval_var B σ "cut.denominator" (?nAX_g8999_0_0_0)) (RunStep.eval_var B σ "rat.d" (?nAX_g8999_0_0_1)) ?_)) (RunStep.assign B c11 "cut.i" c17 c13 (RunStep.eval_add B c11 (Expr.var "cut.i") (Expr.lit ((1:Nat))) c12 ((1:Nat)) (RunStep.eval_var B c11 "cut.i" (?nAX_g8999_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c11 (?nAX_g8999_0_0_3)) (?nAX_g8999_0_0_4)))) (?nAX_g8999_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8999_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8999_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8999_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8999_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8999_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8999_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all
  all_goals omega

theorem command_spec (B M n:ℕ) (a:Fin n→ ℚ)
    (hM:M< B) (hD:denominator a< B) (hs:3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (Context a) command
      (fun _ τ => Context a τ∧ τ.vars "cut.denominator"=denominator a) (33*n+8):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant a σ∧ σ.vars "cut.i"< n) step
      (fun σ τ => Invariant a τ∧ τ.vars "cut.i"=σ.vars "cut.i"+1) 29:=by
    rintro σ ⟨⟨hc,hi,hprod⟩,hlt⟩
    let i:Fin n:= ⟨σ.vars "cut.i",hlt⟩
    obtain ⟨ν,r1,p1⟩:=NativeCutRead.command_spec B M n a i hM hs ha σ ⟨hc,rfl⟩
    obtain ⟨τ,r2,p2⟩:=update_spec B n a i (by omega) hD ((ha i).2.trans_lt hM) ν
      ⟨r1.frame_var "cut.i" (by decide),(r1.frame_var "cut.denominator" (by decide)).trans hprod,p1.2.2.2.1⟩
    have rr:=r1.seq r2
    refine ⟨τ,rr,⟨?_,by rw [p2.1]; exact i.isLt,?_⟩,p2.1⟩
    · simpa only [Context,Prefix,r2.frame_arr "cut.source" (by decide),r2.frame_var "projection.n" (by decide)] using p1.1
    · simpa only [p2.1] using p2.2
  have hloop:=Spec.forRangeZero "cut.i" "projection.n" (Invariant a) n 29 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν:=σ.setVar "cut.denominator" 1
  have r1:Run B (.assign "cut.denominator" (.lit 1)) σ ν 2:=Run.assign (evalB_lit h1)
  have hinit:Invariant a (ν.setVar "cut.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [ν,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [ν,partialProduct,product]
  obtain ⟨τ,r2,p2⟩:=hloop ν hinit
  refine ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,?_⟩
  simpa only [p2.2,full_product] using p2.1.2.2

end Lax263307Proofs.NativeDenominatorProduct

end

section

namespace Lax263307Proofs.NativeClearNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.RationalCutBuffer NativeSignedArithmetic

theorem command_spec (B M n:ℕ) (a:Fin n→ ℚ)
    (hB:M*denominator a+M+denominator a+3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Prefix (encodeVector a) "lp.word" σ∧ σ.vars "projection.n"=n∧
      3*n≤(σ.arrs "cut.source").length∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Prefix (encodeVector (fun i => (integerNormal a i:ℚ))) "lp.word" τ∧
        τ.vars "lp.position"=3*n∧ τ.vars "projection.n"=n)
      (145*n+28):=by
  have hlen:(encodeVector a).length=3*n:=by
    change (RamVectorEncoding.encode (List.ofFn a)).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup:Spec B (fun σ => σ.vars "projection.n"=n) setup
      (fun _ τ => τ.vars "slice.start"=0∧ τ.vars "fill.length"=3*n) 6:=by
    intro σ hh
    (expose_names;
      (refine let c0:Nat→ Nat:=Nat.mul ((3:Nat)); let c1:Nat:=c0 n; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))) (@Eq Nat (Env.vars τ "fill.length") c1)) σ; let c3:Env:=Env.setVar σ "slice.start" ((0:Nat)); let c4:Nat:=Env.vars c3 "projection.n"; let c5:Nat:=c0 c4; let c6:Env:=Env.setVar c3 "fill.length" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c10:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "projection.n"); let c11:Nat:=c8 (Expr.size c10); let c12:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c2 σ')) c6 (@And.intro (Run B setup σ c6 ((6:Nat))) (c2 c6) (RunStep.mono B setup σ c6 (c7 c9 c11) ((6:Nat)) (RunStep.seq B (Com.assign "slice.start" (Expr.lit ((0:Nat)))) (Com.assign "fill.length" c10) σ c3 c6 c9 c11 (RunStep.assign B σ "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9003_0_0_0))) (RunStep.assign B c3 "fill.length" c10 c5 (RunStep.eval_mul B c3 (Expr.lit ((3:Nat))) (Expr.var "projection.n") ((3:Nat)) c4 (RunStep.eval_lit B ((3:Nat)) c3 (?nAX_g9003_0_0_1)) (RunStep.eval_var B c3 "projection.n" (?nAX_g9003_0_0_2)) (?nAX_g9003_0_0_3)))) (?nAX_g9003_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9003_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9003_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9003_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9003_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9003_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  rintro σ ⟨hp,hN,hS,hO⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ hN
  have hpν:Prefix (encodeVector a) "lp.word" ν:=by
    simpa only [Prefix,r1.frame_arr "lp.word" (by decide)] using hp
  obtain ⟨μ,r2,p2⟩:=NativeSlice.command_spec B "lp.word" "cut.source" [] (encodeVector a) [] (by decide)
    (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B M n a (by omega) (by omega) ha) ν
    ⟨⟨by simpa using hpν,by simpa using p1.1⟩,by simpa only [hlen] using p1.2,
      by rw [hlen,RamFrames.run_array_length r1]; exact hS⟩
  have hc:NativeCutRead.Context a μ:=
    ⟨p2.2,((r1.seq r2).frame_var "projection.n" (by decide)).trans hN⟩
  obtain ⟨ξ,r3,p3⟩:=NativeDenominatorProduct.command_spec B M n a (by omega) (by omega) (by omega) ha μ hc
  obtain ⟨τ,r4,p4⟩:=NativeCutVector.command_spec B M n a hB ha ξ
    ⟨p3,by rwa [RamFrames.run_array_length (r1.seq (r2.seq r3))]⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hlen]; omega),p4.2.1,p4.2.2,p4.1.1.2⟩

end Lax263307Proofs.NativeClearNormal

end

section

namespace Lax263307Proofs.NativeOracleCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

theorem far_spec (B M n next:ℕ) (a:Fin n→ ℚ)
    (hB:M*RationalCutBuffer.denominator a+M+RationalCutBuffer.denominator a+3*n+next+10< B)
    (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => NativeArrayBounds.Bounded B σ∧ Prefix (encodeVector a) "lp.word" σ∧
      σ.vars "projection.n"=n∧ 3*n≤(σ.arrs "cut.source").length∧
      3*n<(σ.arrs "lp.word").length∧ 3*n≤(σ.arrs "round.normal").length)
      (far next) (fun _ τ => Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal a)) "round.normal" τ∧
        τ.vars "machine.phase"=next) (193*n+40):=by
  rintro σ ⟨hb,hp,hn,hc,ho,hr⟩
  obtain ⟨ν,r1,p1⟩:=NativeClearNormal.command_spec B M n a (by omega) ha σ ⟨hp,hn,hc,ho⟩
  have hlen:(encodeVector (fun i => (RationalCutBuffer.integerNormal a i:ℚ))).length=3*n:=
    NativeRoundedQuery.vector_length _
  obtain ⟨μ,r2,p2⟩:=NativeProgramCache.copy_spec B "lp.word" "round.normal" "lp.position" _ (by decide)
    (by rw [hlen]; omega) (NativeArrayBounds.prefix_words (NativeArrayBounds.run r1 hb) p1.1) ν
    ⟨p1.1,by simpa only [hlen] using p1.2.1,by rw [hlen,RamFrames.run_array_length r1]; exact hr⟩
  let τ:=μ.setVar "machine.phase" next
  have r3:Run B (.assign "machine.phase" (.lit next)) μ τ 2:=Run.assign (evalB_lit (show next< B by omega))
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]; omega),p2.2,by simp [τ]⟩

end Lax263307Proofs.NativeOracleCut

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

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

theorem array_length {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases steps total σ τ) (a:String):(τ.arrs a).length=(σ.arrs a).length:=by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (Lax455465Proofs.RamFrames.run_array_length rr a)

theorem single_run {B total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases 1 total σ τ) (j:Fin cases.length)
    (hp:σ.vars "machine.phase"=j.val):Run B cases[j.val] σ τ total:=by
  cases trace with
  | step hr i hi rr rest =>
    cases rest with
    | nil =>
      have he:i=j:=Fin.ext (hi.symm.trans hp)
      subst i
      simpa only [Nat.add_zero] using rr

end Lax263307Proofs.NativeMachineFrame

end

section

namespace Lax263307Proofs.NativeMachineBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning NativeMachineSegment

theorem state {B steps total:ℕ} {phases:List Com} {σ τ:Env}
    (trace:Segment B phases steps total σ τ) (hσ:NativeStateBounds.Bounded B σ):
    NativeStateBounds.Bounded B τ:=by
  induction trace with
  | nil => exact hσ
  | step hr j hj rr rest ih => exact ih (NativeStateBounds.run rr hσ)

end Lax263307Proofs.NativeMachineBounds

end

section

namespace Lax263307Proofs.NativeProjectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeSignedArithmetic

theorem oracle_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hd:s∉NativeDistanceInput.command.wvars) (ho:s∉NativeOracleScalars.reserved)
    (ht:s∉NativeProjectionTolerance.command.wvars) (hr:s∉NativeProjectionResult.command.wvars):
    s∉(NativeProjectionOracle.command p coeff).wvars:=by
  simpa only [NativeProjectionOracle.command,NativeDistanceOracle.command,Com.wvars,List.mem_append,not_or]
    using And.intro (And.intro hd (NativeOracleScalars.command_variable p coeff s ho)) (And.intro ht hr)

theorem projection_segment {m N:ℕ} (B M n D R:ℕ) (cfg:Config)
    (P:Program ℚ m N) (x:Fin N→ ℚ) (result:RationalProjection.Outcome N)
    (oracleTime callCost:ℕ)
    (call:Spec B (InvocationInput P (ProjectedOracle.raw x) (NativeNodeTolerance.tolerance n D R) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (fun _ τ => NativeProjectionResult.Output result τ∧ τ.vars "projection.n"=N) callCost)
    (hn:0< n) (hD:0< D) (hR:0< R)
    (hLP:(encodeProgram P).length+2< B) (hB:2*M^2+3< B)
    (hshape:4*N+5< B) (hscale:4*N≤ M) (hx:∀ j,Bounded M (x j))
    (htol:NativeNodeTolerance.guard n D R< B):
    ∀ σ,NativeProjectionCenter.Context x σ→ NativeNodeTolerance.Context n D R σ→
      Prefix (encodeProgram P) "moment.program" σ→ σ.vars "node.programLength"=(encodeProgram P).length→
      NativeArrayBounds.Bounded B σ→ (encodeProgram P).length≤(σ.arrs "lp.input").length→
      3*N<(σ.arrs "lp.word").length→ 3*N≤(σ.arrs "projection.center").length→
      3≤(σ.arrs "lp.word").length→ 3≤(σ.arrs "projection.tolerance").length→
      NativeDistanceData.wordLength m N<(σ.arrs "lp.word").length→
      (encodeProgram (DistanceProjection.distanceProgram P (ProjectedOracle.raw x))).length<(σ.arrs "vm.input").length→
      oracleTime<(σ.arrs "vm.addresses").length→ oracleTime<(σ.arrs "vm.values").length→
      oracleTime<(σ.arrs "vm.output").length→
      σ.vars "machine.running"=1→ σ.vars "machine.phase"=4→
      ∃ τ,Segment B (phases cfg) 1
        (16*(encodeProgram P).length+(36*M.size+124)*N+135+callCost+2) σ τ∧
        τ.vars "machine.running"=1∧ τ.vars "machine.phase"=5∧ NativeProjectionResult.Output result τ∧ τ.vars "projection.n"=N:=by
  intro σ hc ht hp hlen hb hinput hword hcenter hword3 htol3 hdist hvm ha hv ho hr hphase
  obtain ⟨ν,r1,p1⟩:=NativeProjectionPrepare.command_spec B M n D R m N P x hn hD hR hLP hB
    hshape hscale hx htol σ ⟨hc,ht,hp,hlen,hb,hinput,hword,hcenter,hword3,htol3⟩
  obtain ⟨μ,r2,p2⟩:=call ν ⟨p1.2.2.1,p1.2.2.2.1,p1.2.2.2.2,
    by rw [RamFrames.run_array_length r1]; exact hdist,
    by rw [RamFrames.run_array_length r1]; exact hvm,
    by rw [RamFrames.run_array_length r1]; exact ha,
    by rw [RamFrames.run_array_length r1]; exact hv,
    by rw [RamFrames.run_array_length r1]; exact ho⟩
  let τ:=μ.setVar "machine.phase" 5
  have r3:Run B (go 5) μ τ 2:=Run.assign (evalB_lit (show 5< B by omega))
  have rr:Run B ((phases cfg)[4]'(by change 4<16; decide)) σ τ
      (16*(encodeProgram P).length+(36*M.size+124)*N+135+callCost+2):=by
    simpa only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,Nat.add_assoc] using r1.seq (r2.seq r3)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨4,by change 4<16; decide⟩ hphase rr,?_,by simp [τ],?_,?_⟩
  · exact (r3.frame_var _ (by decide)).trans ((r2.frame_var _
      (oracle_variable _ _ _ (by decide) (by decide) (by decide) (by decide))).trans
      ((r1.frame_var _ (by decide)).trans hr))
  · cases result <;> simpa [NativeProjectionResult.Output,τ,Prefix] using p2.1
  · simpa [τ] using p2.2

private theorem value {B x:ℕ} {s:String} {σ:Env} (h:σ.vars s=x) (hx:x< B):
    (Expr.var s).evalB B σ=some x:=by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem near_segment {N:ℕ} (B:ℕ) (cfg:Config) (x:Fin N→ ℚ) (hB:7< B)
    (σ:Env) (ho:NativeProjectionResult.Output (.near x) σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=5):
    ∃ τ,Segment B (phases cfg) 1 6 σ τ∧ τ=σ.setVar "machine.phase" 6∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=6∧ NativeProjectionResult.Output (.near x) τ:=by
  let τ:=σ.setVar "machine.phase" 6
  have rr:Run B (go 6) σ τ 2:=Run.assign (evalB_lit (show 6< B by omega))
  have ht:(Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some true:=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 0< B by omega))
  have run:Run B projectionReply σ τ 6:=
    (Run.ite_true (d:=.ite (.eq (.var "projection.kind") (.lit 1))
      (NativeOracleCut.far 13) (NativeAttemptReply.noneCommand 14)) ht rr).mono (by simp [Cond.size,Expr.size])
  refine ⟨τ,NativeMachineSegment.phase hr ⟨5,by change 5<16; decide⟩ hp run,rfl,?_,by simp [τ],?_⟩
  · simpa [τ] using hr
  · simpa [τ,NativeProjectionResult.Output,Prefix] using ho

theorem reject_segment {n N:ℕ} (B:ℕ) (cfg:Config) (hB:n+19< B)
    (σ:Env) (ho:NativeProjectionResult.Output (.reject:RationalProjection.Outcome N) σ)
    (hn:σ.vars "graph.n"=n) (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=5):
    ∃ τ,Segment B (phases cfg) 1 14 σ τ∧ NativeRoundTrace.Stopped (none:Option (Finset (Fin n))) τ:=by
  obtain ⟨τ,rr,po⟩:=NativeAttemptReply.none_spec B n 14 hB σ hn
  have ht0:(Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false:=
    evalB_condEq (value ho (by omega)) (evalB_lit (show 0< B by omega))
  have ht1:(Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some false:=
    evalB_condEq (value ho (by omega)) (evalB_lit (show 1< B by omega))
  have run:Run B projectionReply σ τ 14:=
    (Run.ite_false (c:=go 6) ht0 (Run.ite_false (c:=NativeOracleCut.far 13) ht1 rr)).mono
      (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨5,by change 5<16; decide⟩ hp run,
    (rr.frame_var _ (by decide)).trans hr,po.2.2,po.2.1⟩

theorem far_segment {N:ℕ} (B M:ℕ) (cfg:Config) (a:Fin N→ ℚ) (β:ℚ)
    (hB:M*RationalCutBuffer.denominator a+M+RationalCutBuffer.denominator a+3*N+23< B)
    (ha:∀ j,Bounded M (a j)) (σ:Env)
    (ho:NativeProjectionResult.Output (.far a β) σ) (hn:σ.vars "projection.n"=N)
    (hb:NativeArrayBounds.Bounded B σ) (hc:3*N≤(σ.arrs "cut.source").length)
    (hw:3*N<(σ.arrs "lp.word").length) (hnormal:3*N≤(σ.arrs "round.normal").length)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=5):
    ∃ τ,Segment B (phases cfg) 1 (193*N+48) σ τ∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=13∧
      Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal a)) "round.normal" τ:=by
  obtain ⟨τ,rr,po⟩:=NativeOracleCut.far_spec B M N 13 a hB ha σ ⟨hb,ho.2.1,hn,hc,hw,hnormal⟩
  have ht0:(Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false:=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 0< B by omega))
  have ht1:(Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some true:=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 1< B by omega))
  have run:Run B projectionReply σ τ (193*N+48):=
    (Run.ite_false (c:=go 6) ht0 (Run.ite_true (d:=NativeAttemptReply.noneCommand 14) ht1 rr)).mono
      (by simp [Cond.size,Expr.size]; omega)
  exact ⟨τ,NativeMachineSegment.phase hr ⟨5,by change 5<16; decide⟩ hp run,
    (rr.frame_var _ (by decide)).trans hr,po.2,po.1⟩

end Lax263307Proofs.NativeProjectionTrace

end

section

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem RootData.trans {σ ν τ:Env} (h1:RootData σ ν) (h2:RootData ν τ):RootData σ τ:=
  ⟨h2.1.trans h1.1,h2.2.trans h1.2⟩

theorem root_frame {B t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (ht:"root.target"∉c.wvars) (hf:"root.fuel"∉c.wvars):RootData σ τ:=
  ⟨rr.frame_var _ ht,rr.frame_var _ hf⟩

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

def arrays:List String:= ["catalog.mask","search.graph","catalog.card",
  "catalog.independent","moment.program","recursion.frames"]

theorem frame {n B D k r p b load F fuel S v limit t:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∈scalars):=rr.frame_var s (hv s hs)
  have a (s:String) (hs:s∈arrays):=rr.frame_arr s (ha s hs)
  refine ⟨?_,(v _ (by simp [scalars])).trans hc.target,
    (v _ (by simp [scalars])).trans hc.sparsity,
    (v _ (by simp [scalars])).trans hc.denominator,
    (v _ (by simp [scalars])).trans hc.classB,
    (v _ (by simp [scalars])).trans hc.loadValue,
    (v _ (by simp [scalars])).trans hc.nodeD,
    (v _ (by simp [scalars])).trans hc.floorPower,?_,
    (v _ (by simp [scalars])).trans hc.programLength,
    (v _ (by simp [scalars])).trans hc.roundLimit,
    (v _ (by simp [scalars])).trans hc.roundWidth,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (v _ (by simp [scalars])).trans hc.cursor,
    (v _ (by simp [scalars])).trans hc.stride,
    (v _ (by simp [scalars])).trans hc.depth,
    (v _ (by simp [scalars])).trans hc.frameLength⟩
  · refine ⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by simp [scalars]))
      (hv _ (by simp [scalars])) (ha _ (by simp [arrays])) (ha _ (by simp [arrays])) hc.moments.1,
      ?_,?_,(v _ (by simp [scalars])).trans hc.moments.2.2.2⟩
    · simpa only [Prefix,a "catalog.card" (by simp [arrays])] using hc.moments.2.1
    · simpa only [Prefix,a "catalog.independent" (by simp [arrays])] using hc.moments.2.2.1
  · simpa only [Prefix,a "moment.program" (by simp [arrays])] using hc.program
  · intro s; rw [RamFrames.run_array_length rr]; exact hc.lengths s
  · simpa only [Prefix,a "recursion.frames" (by simp [arrays])] using hc.stack

theorem collection {n B D k r p b load F fuel S v limit steps total:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {base τ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front base)
    (trace:Segment B (phases cfg) steps total base τ)
    (anchor:NativeCollectionAnchor.Anchor base τ)
    (order:τ.vars "graph.n"=n)
    (stack:Prefix front "recursion.frames" τ) (cursor:τ.vars "stack.words"=front.length):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∉NativeCollectionAnchor.workScalars):=anchor.1 s hs
  have a (s:String) (hs:s∉NativeCollectionAnchor.workArrays):=anchor.2 s hs
  refine ⟨?_,(v _ (by decide)).trans hc.target,(v _ (by decide)).trans hc.sparsity,
    (v _ (by decide)).trans hc.denominator,(v _ (by decide)).trans hc.classB,
    (v _ (by decide)).trans hc.loadValue,(v _ (by decide)).trans hc.nodeD,
    (v _ (by decide)).trans hc.floorPower,?_,(v _ (by decide)).trans hc.programLength,
    (v _ (by decide)).trans hc.roundLimit,(v _ (by decide)).trans hc.roundWidth,NativeMachineBounds.state trace hc.bounded,
    ?_,stack,cursor,(v _ (by decide)).trans hc.stride,(v _ (by decide)).trans hc.depth,
    (v _ (by decide)).trans hc.frameLength⟩
  · rcases hc.moments with ⟨⟨hn,hN,hm,hg,hbits⟩,hcard,hind,hr⟩
    refine ⟨⟨order,(v _ (by decide)).trans hN,?_,?_,?_⟩,
      ?_,?_,(v _ (by decide)).trans hr⟩
    · simpa only [Prefix,a "catalog.mask" (by decide)] using hm
    · simpa only [Prefix,a "search.graph" (by decide)] using hg
    · rw [NativeMachineFrame.array_length trace]; exact hbits
    · simpa only [Prefix,a "catalog.card" (by decide)] using hcard
    · simpa only [Prefix,a "catalog.independent" (by decide)] using hind
  · simpa only [Prefix,a "moment.program" (by decide)] using hc.program
  · intro s; rw [NativeMachineFrame.array_length trace]; exact hc.lengths s

end Lax263307Proofs.NativeOracleContext

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNearExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem stored_frame {B N j t:ℕ} {state:RoundedOracleSearch.State N}
    {σ τ:Env} {c:Com} (rr:Run B c σ τ t)
    (hs:NativeRoundedTrace.StoredState j state σ)
    (hv:"vec.n"∉c.wvars∧ "round.i"∉c.wvars)
    (ha:"round.shape"∉c.warrs∧ "round.center"∉c.warrs):
    NativeRoundedTrace.StoredState j state τ:=by
  refine ⟨?_,?_,(rr.frame_var _ hv.1).trans hs.2.2.1,(rr.frame_var _ hv.2).trans hs.2.2.2⟩
  · simpa only [Prefix,rr.frame_arr _ ha.1] using hs.1
  · simpa only [Prefix,rr.frame_arr _ ha.2] using hs.2.1

end Lax263307Proofs.NativeNearExecution

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem projection_variable (cfg:Config) (s:String)
    (hp:s∉NativeProjectionPrepare.command.wvars)
    (hd:s∉NativeDistanceInput.command.wvars) (ho:s∉NativeOracleScalars.reserved)
    (ht:s∉NativeProjectionTolerance.command.wvars) (hr:s∉NativeProjectionResult.command.wvars)
    (hs:s≠"machine.phase"):
    s∉((phases cfg)[4]'(by change 4<16; decide)).wvars:=by
  have hcall:=NativeProjectionTrace.oracle_variable cfg.lp cfg.lpWidth s hd ho ht hr
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,go,
    Com.wvars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem projection_array (cfg:Config) (s:String)
    (hp:s∉NativeProjectionPrepare.command.warrs)
    (hd:s∉NativeDistanceInput.command.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (ht:s∉NativeProjectionTolerance.command.warrs) (hr:s∉NativeProjectionResult.command.warrs):
    s∉((phases cfg)[4]'(by change 4<16; decide)).warrs:=by
  have hcall:=NativeOracleFrame.command_array cfg.lp cfg.lpWidth s ho
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,go,
    NativeProjectionOracle.command,NativeDistanceOracle.command,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true]

theorem projection_frame {n B D k r p b load F fuel S v limit t:ℕ} (cfg:Config)
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ τ:Env} (rr:Run B ((phases cfg)[4]'(by change 4<16; decide)) σ τ t)
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  apply NativeOracleContext.frame rr hc
  · intro s hs
    simp only [scalars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro s hs
    simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem oracle_segment {n r:ℕ} (D k p b load F fuel S v limit w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (front:List ℕ)
    (child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card)))
    (j:ℕ) (state:RoundedOracleSearch.State (MomentLP.dimension n r))
    (bounds:ProjectionBounds D k r F M w oracleTime G extent)
    (hcenter:∀ i,NativeSignedArithmetic.Bounded M (state.2 i))
    (hquery:(encodeProgram (DistanceProjection.distanceProgram (MomentLP.program G k r)
      (ProjectedOracle.raw state.2))).length< extent "vm.input")
    (call:Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw state.2) (NativeNodeTolerance.tolerance n D F) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth)
      (fun _ τ => NativeProjectionResult.Output (projection lp G k D F state.2) τ∧
        τ.vars "projection.n"=MomentLP.dimension n r) callCost)
    (farBounds:∀ a β,projection lp G k D F state.2=.far a β→
      (∀ i,NativeSignedArithmetic.Bounded farM (a i))∧
      farM*RationalCutBuffer.denominator a+farM+RationalCutBuffer.denominator a+
        3*MomentLP.dimension n r+23<2^w)
    (nearSetup:∀ x,projection lp G k D F state.2=.near x→
      NativeNearExecution.Setup D k p b load fuel S v nearM h T w space flowTime childSteps childTime
        cfg G flow x extent front child)
    (σ:Env) (hc:Context (2^w) D k r p b load F fuel S v limit cfg G extent front σ)
    (hs:NativeRoundedTrace.StoredState j state σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=4):
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ∧
      transitions≤(childSteps+5)*(n+1)+6∧
      total≤(16*(encodeProgram (MomentLP.program G k r)).length+(36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+
        14+(193*MomentLP.dimension n r+48)+
        NativeNearExecution.timeBound cfg n r nearM S h childTime flowTime+6∧
      Context (2^w) D k r p b load F fuel S v limit cfg G extent front τ∧
      NativeRoundedTrace.StoredState j state τ∧
      Output (reply flow G D k p b load child (projection lp G k D F state.2)) τ∧ RootData σ τ:=by
  obtain ⟨ν,first,hrν,hpν,resultν,dimensionν⟩:=NativeProjectionTrace.projection_segment
    (2^w) M n D F cfg (MomentLP.program G k r) state.2 (projection lp G k D F state.2)
    oracleTime callCost call bounds.positive bounds.denominator bounds.floorPower bounds.program
    bounds.rational bounds.shape bounds.scale hcenter bounds.tolerance σ
    ⟨hs.2.2.1,hs.2.1⟩ ⟨hc.moments.1.1,hc.nodeD,hc.floorPower⟩ hc.program hc.programLength
    hc.bounded.2.1 (by rw [hc.lengths]; exact bounds.input) (by rw [hc.lengths]; exact bounds.word)
    (by rw [hc.lengths]; exact bounds.center) (by rw [hc.lengths]; exact bounds.word3)
    (by rw [hc.lengths]; exact bounds.tolerance3) (by rw [hc.lengths]; exact bounds.distance)
    (by rw [hc.lengths]; exact hquery) (by rw [hc.lengths]; exact bounds.addresses)
    (by rw [hc.lengths]; exact bounds.values) (by rw [hc.lengths]; exact bounds.output) hr hp
  have r1:=NativeMachineFrame.single_run first ⟨4,by change 4<16; decide⟩ hp
  have hcν:=projection_frame cfg r1 hc
  have rootν:=root_frame r1
    (projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsν:=NativeNearExecution.stored_frame r1 hs
    ⟨projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
    ⟨projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  cases he:projection lp G k D F state.2 with
  | reject =>
    have result0:NativeProjectionResult.Output (.reject:RationalProjection.Outcome (MomentLP.dimension n r)) ν:=by
      simpa only [he] using resultν
    obtain ⟨τ,last,hout⟩:=NativeProjectionTrace.reject_segment (2^w) cfg bounds.reply ν result0 hcν.moments.1.1 hrν hpν
    have r2:=NativeMachineFrame.single_run last ⟨5,by change 5<16; decide⟩ hpν
    change Run (2^w) projectionReply ν τ _ at r2
    refine ⟨τ,_,_,NativeMachineSegment.append first last,by nlinarith,by omega,
      NativeOracleContext.frame r2 hcν (by decide) (by decide),
      NativeNearExecution.stored_frame r2 hsν (by decide) (by decide),?_,
      rootν.trans (root_frame r2 (by decide) (by decide))⟩
    simpa only [he,reply,Output] using hout
  | far a β =>
    obtain ⟨ha,hfar⟩:=farBounds a β he
    have resultA:NativeProjectionResult.Output (.far a β) ν:=by simpa only [he] using resultν
    obtain ⟨τ,last,runningτ,phaseτ,normalτ⟩:=NativeProjectionTrace.far_segment
      (2^w) farM cfg a β hfar ha ν resultA dimensionν hcν.bounded.2.1
      (by rw [hcν.lengths]; exact bounds.source) (by rw [hcν.lengths]; exact bounds.word)
      (by rw [hcν.lengths]; exact bounds.normal) hrν hpν
    have r2:=NativeMachineFrame.single_run last ⟨5,by change 5<16; decide⟩ hpν
    change Run (2^w) projectionReply ν τ _ at r2
    refine ⟨τ,_,_,NativeMachineSegment.append first last,by nlinarith,by omega,
      NativeOracleContext.frame r2 hcν (by decide) (by decide),
      NativeNearExecution.stored_frame r2 hsν (by decide) (by decide),?_,
      rootν.trans (root_frame r2 (by decide) (by decide))⟩
    simpa only [he,reply,Output] using And.intro runningτ (And.intro phaseτ normalτ)
  | near x =>
    have resultX:NativeProjectionResult.Output (.near x) ν:=by simpa only [he] using resultν
    obtain ⟨μ,second,eqμ,hrμ,hpμ,pointμ⟩:=NativeProjectionTrace.near_segment (2^w) cfg x
      (by have hh:=bounds.reply; omega) ν resultX hrν hpν
    have r2:=NativeMachineFrame.single_run second ⟨5,by change 5<16; decide⟩ hpν
    change Run (2^w) projectionReply ν μ _ at r2
    have hcμ:=NativeOracleContext.frame r2 hcν (by decide) (by decide)
    have hsμ:=NativeNearExecution.stored_frame r2 hsν (by decide) (by decide)
    let setup:=nearSetup x he
    obtain ⟨τ,s,t,last,hsteps,htime,hcτ,hsτ,hout,rootτ⟩:=NativeNearExecution.near_segment
      D k p b load F fuel S v limit nearM h T w space flowTime childSteps childTime cfg G flow x extent front child
      setup.bounds setup.hx setup.hselected setup.htarget setup.hspace setup.flowCall setup.recursive
      j state μ hcμ hsμ pointμ.2.1 hrμ hpμ
    refine ⟨τ,_,_,NativeMachineSegment.append first (NativeMachineSegment.append second last),
      by omega,by omega,hcτ,hsτ,?_,rootν.trans ((root_frame r2 (by decide) (by decide)).trans rootτ)⟩
    simp only [he,reply]
    cases ho:NativeNearExecution.run flow G D k p b load (MomentLP.decode x) child <;>
      simpa only [ho,NativeNearExecution.Output,Output,NativeCollectionExecution.Cut] using hout

end Lax263307Proofs.NativeOracleExecution

end

theorem solution:∀ {n r:ℕ}
  (D k p b load F fuel S v limit w M farM nearM h T space oracleTime callCost flowTime childSteps childTime:ℕ)
  (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n)) [inst:DecidableRel G.Adj]
  (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (front:List ℕ)
  (child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card))) (j:ℕ)
  (state:Lax263307.RoundedOracleSearch.State (Lax263307.MomentLP.dimension n r)),
  Lax263307Proofs.NativeOracleExecution.ProjectionBounds D k r F M w oracleTime G extent→
    (∀ (i:Fin (Lax263307.MomentLP.dimension n r)),Lax263307Proofs.NativeSignedArithmetic.Bounded M (state.2 i))→
      (Lax109476.RationalEncoding.encodeProgram
              (Lax263307.DistanceProjection.distanceProgram (Lax263307.MomentLP.program G k r)
                (Lax263307.ProjectedOracle.raw state.2))).length <
          extent "vm.input" →
        Lax808846Proofs.Reasoning.Spec (2 ^ w)
            (Lax263307Proofs.NativeProjectionTrace.InvocationInput (Lax263307.MomentLP.program G k r)
              (Lax263307.ProjectedOracle.raw state.2) (Lax263307Proofs.NativeNodeTolerance.tolerance n D F) oracleTime)
            (Lax263307Proofs.NativeProjectionOracle.command cfg.lp cfg.lpWidth)
            (fun (x τ:Lax808846Proofs.Imp.Env) =>
              Lax263307Proofs.NativeProjectionResult.Output
                  (Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2) τ∧
                τ.vars "projection.n"=Lax263307.MomentLP.dimension n r)
            callCost→
          (∀ (a:Fin (Lax263307.MomentLP.dimension n r)→ ℚ) (β:ℚ),
              Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2 =
                  Lax263307.RationalProjection.Outcome.far a β→
                (∀ (i:Fin (Lax263307.MomentLP.dimension n r)),
                    Lax263307Proofs.NativeSignedArithmetic.Bounded farM (a i))∧
                  farM * Lax263307.RationalCutBuffer.denominator a + farM + Lax263307.RationalCutBuffer.denominator a +
                        3 * Lax263307.MomentLP.dimension n r +
                      23 <
                    2 ^ w)→
            (∀ (x:Fin (Lax263307.MomentLP.dimension n r)→ ℚ),
                Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2 =
                    Lax263307.RationalProjection.Outcome.near x→
                  Lax263307Proofs.NativeNearExecution.Setup D k p b load fuel S v nearM h T w space flowTime childSteps
                    childTime cfg G flow x extent front child)→
              ∀ (σ:Lax808846Proofs.Imp.Env),
                Lax263307Proofs.NativeOracleContext.Context (2 ^ w) D k r p b load F fuel S v limit cfg G extent front
                    σ→
                  Lax263307Proofs.NativeRoundedTrace.StoredState j state σ→
                    σ.vars "machine.running"=1→
                      σ.vars "machine.phase"=4→
                        ∃ (τ:Lax808846Proofs.Imp.Env) (transitions:ℕ) (total:ℕ),
                          Lax263307Proofs.NativeMachineSegment.Segment (2 ^ w)
                              (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ τ∧
                            transitions≤ (childSteps + 5) * (n + 1) + 6∧
                              total≤
                                  16 *
                                                    (Lax109476.RationalEncoding.encodeProgram
                                                        (Lax263307.MomentLP.program G k r)).length +
                                                  (36 * M.size + 124) * Lax263307.MomentLP.dimension n r +
                                                135 +
                                              callCost +
                                            2 +
                                          14 +
                                        (193 * Lax263307.MomentLP.dimension n r + 48) +
                                      Lax263307Proofs.NativeNearExecution.timeBound cfg n r nearM S h childTime
                                        flowTime +
                                    6∧
                                Lax263307Proofs.NativeOracleContext.Context (2 ^ w) D k r p b load F fuel S v limit cfg
                                    G extent front τ∧
                                  Lax263307Proofs.NativeRoundedTrace.StoredState j state τ∧
                                    Lax263307Proofs.NativeOracleExecution.Output
                                        (Lax263307Proofs.NativeOracleExecution.reply flow G D k p b load child
                                          (Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2))
                                        τ∧
                                      Lax263307Proofs.NativeOracleContext.RootData σ τ:= @Lax263307Proofs.NativeOracleExecution.oracle_segment
