-- Prove2me | solution 1 for Lax263307Proofs.NativeNearExecution.near_segment_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:22:33.909672+00:00
-- url     : https://prove2.me/submissions/91c09d9b-91a0-439c-8513-1a28a84a8802

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Find
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native
import Theorems.Thm_Lax263307Proofs_NativeCollectionExecution_collect_segment_native

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
namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational
theorem Lax109476Proofs.RamRational.multiplyFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    LE.le s₁ ((1:Nat))→
      LE.le s₂ ((1:Nat))→
        LE.le n₁ M→
          LE.le d₁ M→
            LE.le n₂ M→
              LE.le d₂ M→
                LT.lt ((0:Nat)) d₁→
                  LT.lt ((0:Nat)) d₂→
                    Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamRational.fractionInputs s₁ n₁ d₁ s₂ n₂ d₂)
                      Lax109476Proofs.RamRational.multiplyFraction
                      (fun (x σ':Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (HAdd.hAdd
                        (HMul.hMul
                          ((36:Nat))
                          (HMul.hMul d₁ d₂).size)
                        ((64:Nat))):= @Lax109476Proofs.RamRational.multiplyFraction_spec_native
namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational
theorem Lax109476Proofs.RamRational.addFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    LE.le s₁ ((1:Nat))→
      LE.le s₂ ((1:Nat))→
        LE.le n₁ M→
          LE.le d₁ M→
            LE.le n₂ M→
              LE.le d₂ M→
                LT.lt ((0:Nat)) d₁→
                  LT.lt ((0:Nat)) d₂→
                    Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamRational.fractionInputs s₁ n₁ d₁ s₂ n₂ d₂)
                      Lax109476Proofs.RamRational.addFraction
                      (fun (x σ':Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (HAdd.hAdd
                        (HMul.hMul
                          ((36:Nat))
                          (HMul.hMul d₁ d₂).size)
                        ((96:Nat))):= @Lax109476Proofs.RamRational.addFraction_spec_native
namespace Lax263307Proofs.NativeCollectionExecution
end Lax263307Proofs.NativeCollectionExecution
theorem Lax263307Proofs.NativeCollectionExecution.collect_segment:∀ {n:Nat} {ι:Type} [inst:Fintype ι] (D k r fuel S h T childSteps childTime:Nat)
  (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n))
  [inst_1:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x:Fin n→ NNRat) (parts:ι→ Finset (Fin n))
  (order:List ι) (A:Finset (Fin n)) (extent:String→ Nat) (front:List Nat) (base:Lax808846Proofs.Imp.Env)
  (child:(C:Finset (Fin n))→ Nat→ Option (Finset (Fin (@Finset.card (Fin n) C)))),
  (∀ (i:ι), @Membership.mem ι (List ι) (@List.instMembership ι) order i)→
    LT.lt ((0:Nat)) n→
      LT.lt ((0:Nat)) D→
        (∀ (v:Fin n),
            Lax263307Proofs.NativeSignedArithmetic.Bounded
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) h)
              (@NNRat.cast Rat Rat.instNNRatCast (x v)))→
          ∀ (w:Nat),
            LE.le (Lax263307Proofs.NativeComponentDecision.wordHeight n D k h) w→
              LE.le (@List.length ι order)
                  (HAdd.hAdd n
                    ((1:Nat)))→
                LT.lt
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) n)
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  LT.lt
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
                          LE.le
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
                        LE.le
                            (HAdd.hAdd
                              (HAdd.hAdd (@List.length Nat front)
                                (HMul.hMul S
                                  (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                            (extent "recursion.frames")→
                          LE.le (HMul.hMul n n)
                              (extent "child.graph")→
                            LE.le (HMul.hMul n n)
                                (extent "search.graph")→
                              LE.le n (extent "subset.bits")→
                                LE.le n (extent "restrict.vertices")→
                                  LT.lt
                                      (HMul.hMul
                                        ((3:Nat)) n)
                                      (extent "lp.word")→
                                    LE.le
                                        (HMul.hMul
                                          ((3:Nat)) n)
                                        (extent "sum.input")→
                                      LE.le
                                          (HMul.hMul
                                            ((3:Nat))
                                            (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                          (extent "lp.input")→
                                        LE.le
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
                                                      (LE.le transitions
                                                        (HAdd.hAdd
                                                          (HMul.hMul
                                                            (HAdd.hAdd
                                                              childSteps
                                                              ((5:Nat)))
                                                            (@List.length ι order))
                                                          ((1:Nat))))
                                                      (And
                                                        (LE.le total
                                                          (HAdd.hAdd
                                                            (HMul.hMul
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
                                                          τ))):= @Lax263307Proofs.NativeCollectionExecution.collect_segment_native

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

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem size_half (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne:Nat.bit b n ≠ 0:=by omega
    rw [Nat.bit_div_two,Nat.size_bit hne]

end Lax455465Proofs.WordSize

end

section

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning

theorem candidate_complete (n r:ℕ) (A:Finset (Fin n)):
    A∈ candidates n r↔ A.card≤ r:=by
  constructor
  · intro h
    obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp h
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hm
    have hsub:=(List.mem_sublistsLen.mp hl).1
    have hlen:=(List.mem_sublistsLen.mp hl).2
    have hnd:=hsub.nodup (List.nodup_finRange n)
    rw [List.toFinset_card_of_nodup hnd,hlen]
    have:=List.mem_range.mp hj
    omega
  · intro hA
    let l:=(List.finRange n).filter fun v => decide (v∈ A)
    have hsub:List.Sublist l (List.finRange n):=List.filter_sublist
    have hnd:l.Nodup:=hsub.nodup (List.nodup_finRange n)
    have heq:l.toFinset=A:=by ext v; simp [l]
    have hlen:l.length=A.card:=by rw [← List.toFinset_card_of_nodup hnd,heq]
    apply List.mem_flatMap.mpr
    refine ⟨A.card,List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨l,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,heq⟩

end Lax263307Proofs.RationalConditioning

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

theorem fractionValue_inv (s n d:ℕ):fractionValue s d n=(fractionValue s n d)⁻¹:=by
  unfold fractionValue
  split_ifs <;> simp [inv_div,neg_div]

theorem invertFraction_spec (B s n d:ℕ) (h1:1 < B) (hs:s≤ 1)
    (hn:n < B) (hd:d < B):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧ σ.vars "left.d"=d)
      invertFraction (fun _ σ' => FractionOutput (fractionValue s n d)⁻¹ σ')
      (36 * n.size + 40):=by
  have hsB:=hs.trans_lt h1
  by_cases hz:n=0
  · subst n
    have hzero:Spec B (fun _ => True)
        (.seq (.assign "rat.n" (.lit 0))
          (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
        (fun _ σ' => FractionOutput 0 σ') 6:=by
      (expose_names;
        (refine fun (σ:Env) (a:True) => let c0:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c1:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c2:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c3:Com:=Com.seq c1 c2; let c4:Com:=Com.seq c0 c3; let c5:Env→ Nat→ Prop:=Run B c4 σ; let c6:Env→ Prop:=(fun (x σ':Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ') σ; let c7:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat)); let c9:Env:=Env.setVar c8 "rat.s" ((0:Nat)); let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c13:Nat:=c11 (Expr.size (Expr.lit ((1:Nat)))); let c14:Nat:=c10 c13 c12; @Exists.intro Env (fun (σ':Env) => And (c5 σ' ((6:Nat))) (c6 σ')) c9 (@And.intro (c5 c9 ((6:Nat))) (c6 c9) (RunStep.mono B c4 σ c9 (c10 c12 c14) ((6:Nat)) (RunStep.seq B c0 c3 σ c7 c9 c12 c14 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hn)) (RunStep.seq B c1 c2 c7 c8 c9 c13 c12 (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)) (RunStep.assign B c8 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c8 hn)))) (?nAX_g5425_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5425_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp [FractionOutput,fractionValue]
    rintro σ ⟨hσs,hσn,hσd⟩
    have hc:(Cond.eq (.var "left.n") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hσn ▸ hn)) (evalB_lit (by omega)),hσn]
      rfl
    obtain ⟨τ,hr,hτ⟩:=hzero σ True.intro
    exact ⟨τ, (Run.ite_true hc hr).mono (by simp [Nat.size]),
      by simpa [fractionValue] using hτ⟩
  · have hnorm:=normalizeFraction_output_spec B s d n hs hd hn (Nat.pos_of_ne_zero hz)
    have hv:=fractionValue_inv s n d
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "left.s") s) (And (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat:=c1 (Nat.mul ((36:Nat)) (Nat.size n)); let c3:Nat:=c2 ((40:Nat)); let c4:Env→ Prop:=FractionOutput (@Inv.inv Rat Rat.instInv (fractionValue s n d)); let c5:Env→ Prop:=(fun (x σ':Env) => c4 σ') σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B invertFraction σ σ' c3) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:= @Eq Nat (Env.vars σ "left.n") ((0:Nat)); let c9:Prop:=Not c8; let c10:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c11:Env:=Env.setVar c10 "rat.d" ((1:Nat)); let c12:Env:=Env.setVar c11 "rat.s" ((0:Nat)); let c13:Nat→ Nat:=c1 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c15:Nat→ Nat:=c1 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c18:Nat:=c1 c17 c16; let c19:Nat:=c1 c16 c18; let c20:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c22:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c23:Com:=Com.seq c21 c22; let c24:Com:=Com.seq c20 c23; let c25:Com:=Com.seq (Com.assign "rat.d" (Expr.var "left.n")) (Com.seq (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction); let c26:Com:=Com.seq (Com.assign "rat.n" (Expr.var "left.d")) c25; let c27:Nat:=Env.vars (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "left.n"; let c28:Env:=Env.setVar (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "rat.d" c27; let c29:Nat:=Env.vars c28 "left.s"; let c30:Env:=Env.setVar c28 "rat.s" c29; let c31:Env→ Nat→ Prop:=Run B normalizeFraction c30; let c32:Nat:=c2 ((16:Nat)); let c33:Env→ Prop:=fun (σ':Env) => And (c31 σ' c32) (FractionOutput (fractionValue s d n) σ'); let c34:String→ Nat:=Env.vars c30; let c35:Nat:=c13 (Expr.size (Expr.var "left.d")); let c36:Nat:=c13 (Expr.size (Expr.var "left.n")); let c37:Nat:=c13 (Expr.size (Expr.var "left.s")); let c38:Nat:=c1 c37 c32; let c39:Nat:=c1 c36 c38; let c40:Nat:=c1 c35 c39; @And.casesOn (@Eq Nat (Env.vars σ "left.s") s) c0 (fun (x:And (@Eq Nat (Env.vars σ "left.s") s) c0) => c7) a fun (left:@Eq Nat (Env.vars σ "left.s") s) (right:c0) => @And.casesOn (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d) (fun (x:c0) => c7) right fun (left_1:@Eq Nat (Env.vars σ "left.n") n) (right_1:@Eq Nat (Env.vars σ "left.d") d) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c7) (Classical.em c8) (fun (hcase:c8) => @Exists.intro Env c6 c12 (@And.intro (Run B invertFraction σ c12 c3) (c5 c12) (RunStep.mono B invertFraction σ c12 (c15 c19) c3 (RunStep.ite_true B c14 c24 c26 σ c12 c19 (RunStep.cond_eq_true B σ (Expr.var "left.n") (Expr.lit ((0:Nat))) (Env.vars σ "left.n") ((0:Nat)) (RunStep.eval_var B σ "left.n" (?nAX_g5425_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5425_1_0_1)) hcase) (RunStep.seq B c20 c23 σ c10 c12 c16 c18 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5425_1_0_2))) (RunStep.seq B c21 c22 c10 c11 c12 c17 c16 (RunStep.assign B c10 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c10 h1)) (RunStep.assign B c11 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c11 (?nAX_g5425_1_0_3)))))) (?nAX_g5425_1_0_4)) ?_)) fun (hcase:c9) => @Exists.casesOn Env c33 (fun (x:@Exists Env c33) => c7) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") d) (And (@Eq Nat (Env.vars σ_1 "rat.d") n) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => FractionOutput (fractionValue s d n) σ') c32 hnorm c30 ?_) fun (w:Env) (h:And (c31 w c32) (FractionOutput (fractionValue s d n) w)) => @And.casesOn (c31 w c32) (FractionOutput (fractionValue s d n) w) (fun (x:And (c31 w c32) (FractionOutput (fractionValue s d n) w)) => c7) h fun (left_2:c31 w c32) (right_2:FractionOutput (fractionValue s d n) w) => @Exists.intro Env c6 w (@And.intro (Run B invertFraction σ w c3) (c5 w) (RunStep.mono B invertFraction σ w (c15 c40) c3 (RunStep.ite_false B c14 c24 c26 σ w c40 (RunStep.cond_eq_false B σ (Expr.var "left.n") (Expr.lit ((0:Nat))) (Env.vars σ "left.n") ((0:Nat)) (RunStep.eval_var B σ "left.n" (?nAX_g5425_1_0_5)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5425_1_0_6)) hcase) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.d")) c25 σ (Env.setVar σ "rat.n" (Env.vars σ "left.d")) w c35 c39 (RunStep.assign B σ "rat.n" (Expr.var "left.d") (Env.vars σ "left.d") (RunStep.eval_var B σ "left.d" (?nAX_g5425_1_0_7))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "left.n")) (Com.seq (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction) (Env.setVar σ "rat.n" (Env.vars σ "left.d")) c28 w c36 c38 (RunStep.assign B (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "rat.d" (Expr.var "left.n") c27 (RunStep.eval_var B (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "left.n" (?nAX_g5425_1_0_8))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction c28 c30 w c37 c32 (RunStep.assign B c28 "rat.s" (Expr.var "left.s") c29 (RunStep.eval_var B c28 "left.s" (?nAX_g5425_1_0_9))) left_2)))) (?nAX_g5425_1_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5425_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_2))
    all_goals simp_all

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

theorem multiplyFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 64)  :=by
  exact Lax109476Proofs.RamRational.multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂ hd₁pos hd₂pos

def sumNumerator (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then n₁ * d₂ + n₂ * d₁
  else if n₁ * d₂ < n₂ * d₁ then n₂ * d₁ - n₁ * d₂ else n₁ * d₂ - n₂ * d₁

def sumSign (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then s₁ else if n₁ * d₂ < n₂ * d₁ then s₂ else s₁

theorem fractionValue_sum (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    fractionValue (sumSign s₁ n₁ d₁ s₂ n₂ d₂) (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂:=by
  have hd₁q:(d₁:ℚ) ≠ 0:=by positivity
  have hd₂q:(d₂:ℚ) ≠ 0:=by positivity
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
    by_cases h:n₁ * d₂ < n₂ * d₁
  all_goals first
    | (have hu:n₁ * d₂≤ n₂ * d₁:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hu]
       field_simp <;> ring)
    | (have hv:n₂ * d₁≤ n₁ * d₂:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hv]
       field_simp <;> ring)

set_option maxHeartbeats 0 in
theorem addFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 96)  :=by
  exact Lax109476Proofs.RamRational.addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂ hd₁pos hd₂pos

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

def Operands (a b:ℚ) (σ:Env):Prop:=Stored "left" a σ∧ Stored "right" b σ

theorem add_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (Operands a b) addFraction (fun _ τ => FractionOutput (a+b) τ)
      (36*(a.den*b.den).size+96):=by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩:=addFraction_spec B M (σ.vars "left.s") a.num.natAbs a.den
    (σ.vars "right.s") b.num.natAbs b.den hB hleft.2.2.2 hright.2.2.2
    ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl:fractionValue (σ.vars "left.s") a.num.natAbs a.den=a:=by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr:fractionValue (σ.vars "right.s") b.num.natAbs b.den=b:=by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  exact ⟨τ,rr,by simpa only [hl,hr] using ht⟩

theorem multiply_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (Operands a b) multiplyFraction (fun _ τ => FractionOutput (a*b) τ)
      (36*(a.den*b.den).size+64):=by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩:=multiplyFraction_spec B M (σ.vars "left.s") a.num.natAbs a.den
    (σ.vars "right.s") b.num.natAbs b.den hB hleft.2.2.2 hright.2.2.2
    ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl:fractionValue (σ.vars "left.s") a.num.natAbs a.den=a:=by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr:fractionValue (σ.vars "right.s") b.num.natAbs b.den=b:=by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  exact ⟨τ,rr,by simpa only [hl,hr] using ht⟩

end Lax263307Proofs.NativeSignedArithmetic

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

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem zero_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zero (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zero σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zero σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5825_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g5825_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5825_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5825_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
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

open RamVirtualState Lax759944.BinaryWordEncoding

end Lax455465Proofs.RamBitSize

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

theorem add (M:ℕ) (a b:ℚ) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (2*M^2) (a+b):=by
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn:sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*M^2:=by
    have hleft:=Nat.mul_le_mul ha.1 hb.2
    have hright:=Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd:a.den*b.den≤2*M^2:=by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd:=fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

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

namespace Lax263307Proofs.NativeSumHeight

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem weaken {A B:ℕ} {q:ℚ} (h:A≤ B) (hq:Bounded A q):Bounded B q:=
  ⟨hq.1.trans h,hq.2.trans h⟩

theorem add (A C:ℕ) (a b:ℚ) (ha:Bounded A a) (hb:Bounded C b):
    Bounded (2*A*C) (a+b):=by
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn:sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*A*C:=by
    have hleft:=Nat.mul_le_mul ha.1 hb.2
    have hright:=Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd:a.den*b.den≤2*A*C:=by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd:=fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

theorem multiply (A C:ℕ) (a b:ℚ) (ha:Bounded A a) (hb:Bounded C b):
    Bounded (A*C) (a*b):=by
  have hprod (s t u v d e:ℕ) (hs:s≤1) (ht:t≤1):
      fractionValue (if s=t then 0 else 1) (u*v) (d*e)=fractionValue s u d*fractionValue t v e:=by
    have hs':s=0∨ s=1:=by omega
    have ht':t=0∨ t=1:=by omega
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      norm_num [fractionValue,Nat.cast_mul] <;> ring
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=hprod (sign a) (sign b) a.num.natAbs b.num.natAbs a.den b.den (hs a) (hs b)
  rw [value_eq,value_eq] at he
  have hnd:=fractionValue_num_den (if sign a=sign b then 0 else 1)
    (a.num.natAbs*b.num.natAbs) (a.den*b.den) (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans (Nat.mul_le_mul ha.1 hb.1)),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans (Nat.mul_le_mul ha.2 hb.2))⟩

theorem sum (M:ℕ) (xs:List ℚ) (hx:∀ x∈xs,Bounded M x):
    Bounded ((2*M)^xs.length) xs.sum:=by
  induction xs with
  | nil => simp [Bounded]
  | cons x xs ih =>
    have hh:=add M ((2*M)^xs.length) x xs.sum (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))
    simpa only [List.sum_cons,List.length_cons,pow_succ,Nat.mul_comm,Nat.mul_assoc] using hh

theorem uniform_entry (M:ℕ) (xs:List ℚ) (hM:1≤ M) (hx:∀ x∈xs,Bounded M x)
    (x:ℚ) (hmem:x∈xs):Bounded ((2*M)^(xs.length+1)) x:=by
  apply weaken _ (hx x hmem)
  calc
    M≤ 2*M:=by omega
    _=(2*M)^1:=(pow_one _).symm
    _≤ (2*M)^(xs.length+1):=Nat.pow_le_pow_right (by omega) (by omega)

theorem uniform_partial (M:ℕ) (xs:List ℚ) (hM:1≤ M) (hx:∀ x∈xs,Bounded M x)
    (i:ℕ):Bounded ((2*M)^(xs.length+1)) (xs.take i).sum:=by
  apply weaken _ (sum M (xs.take i) (fun x h => hx x (List.mem_of_mem_take h)))
  apply Nat.pow_le_pow_right (by omega)
  simp only [List.length_take]
  omega

end Lax263307Proofs.NativeSumHeight

end

section

namespace Lax263307Proofs.NativeSignedAccumulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational NativeSignedArithmetic

theorem command_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (fun σ => Stored "sum.value" a σ∧ FractionOutput b σ) command
      (fun _ τ => Stored "sum.value" (a+b) τ∧ FractionOutput (a+b) τ)
      (36*(M^2).size+120):=by
  have h1:1< B:=by nlinarith
  have hM:M< B:=by nlinarith
  rintro σ ⟨hs,hbσ⟩
  obtain ⟨ν,r1,p1⟩:=save_spec B "right" b h1
    (hb.1.trans_lt hM) (hb.2.trans_lt hM) (by decide) σ hbσ
  have hsν:Stored "sum.value" a ν:=by
    simpa only [Stored,String.reduceAppend,r1.frame_var "sum.value.s" (by decide),
      r1.frame_var "sum.value.n" (by decide),r1.frame_var "sum.value.d" (by decide)] using hs
  obtain ⟨μ,r2,p2⟩:=load_spec B "sum.value" a h1
    (ha.1.trans_lt hM) (ha.2.trans_lt hM) (by decide) ν hsν
  obtain ⟨ξ,r3,p3⟩:=save_spec B "left" a h1
    (ha.1.trans_lt hM) (ha.2.trans_lt hM) (by decide) μ p2
  have hbξ:Stored "right" b ξ:=by
    simpa only [Stored,String.reduceAppend,(r2.seq r3).frame_var "right.s" (by decide),
      (r2.seq r3).frame_var "right.n" (by decide),(r2.seq r3).frame_var "right.d" (by decide)] using p1
  obtain ⟨υ,r4,p4⟩:=add_spec B M a b hB ha hb ξ ⟨p3,hbξ⟩
  have hab:=NativeRationalBounds.add M a b ha hb
  obtain ⟨τ,r5,p5⟩:=save_spec B "sum.value" (a+b) h1
    (hab.1.trans_lt (by omega)) (hab.2.trans_lt (by omega)) (by decide) υ p4
  have hden:(a.den*b.den).size≤(M^2).size:=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul ha.2 hb.2])
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono (by omega),p5,?_⟩
  simpa only [FractionOutput,r5.frame_var "rat.s" (by decide),
    r5.frame_var "rat.n" (by decide),r5.frame_var "rat.d" (by decide)] using p4

end Lax263307Proofs.NativeSignedAccumulate

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

theorem matrix_flat_coordinate {n:ℕ} (f:Fin n→ Fin n→ ℕ) (q:Fin (n*n)):
    (matrix f)[q.val]?=some (f (row q) (col q)):=by
  have hx:=matrix_coordinate f (row q) (col q)
  have he:(row q).val*n+(col q).val=q.val:=by
    simpa only [row,col,Nat.mul_comm] using Nat.div_add_mod q.val n
  rwa [he] at hx

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

theorem mask_injective (n:ℕ):Function.Injective (mask (n:=n)):=by
  intro I J h
  ext v
  have hh:=congrArg (fun m:ℕ => m.testBit v.val) h
  simpa only [mask_member,decide_eq_decide] using hh

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

namespace Lax263307Proofs.NativeZeroScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def prefixOK (xs:List ℕ) (i:ℕ):ℕ:=
  if (xs.take i).all (fun x => x==0) then 1 else 0

theorem prefix_ok_zero (xs:List ℕ):prefixOK xs 0=1:=by simp [prefixOK]

theorem prefix_ok_le (xs:List ℕ) (i:ℕ):prefixOK xs i≤1:=by
  unfold prefixOK
  split_ifs <;> omega

theorem prefix_ok_succ (xs:List ℕ) (i:ℕ) (hi:i< xs.length):
    prefixOK xs (i+1)=if xs[i]=0 then prefixOK xs i else 0:=by
  unfold prefixOK
  rw [List.take_succ_eq_append_getElem hi,List.all_append]
  cases h:(xs.take i).all (fun x => x==0) <;> by_cases hx:xs[i]=0 <;> simp [hx]

theorem prefix_ok_full (xs:List ℕ):prefixOK xs xs.length=1↔ ∀ x∈xs,x=0:=by
  simp [prefixOK,List.all_eq_true]

theorem update_spec (B i bit ok:ℕ) (hi:i+1< B) (hbit:bit< B) (_hok:ok≤1) (h1:1< B):
    Spec B (fun σ => σ.vars "test.i"=i∧ σ.vars "test.bit"=bit∧ σ.vars "test.ok"=ok)
      update (fun _ τ => τ.vars "test.i"=i+1∧ τ.vars "test.ok"=if bit=0 then ok else 0) 10:=by
  by_cases hbit0:bit=0
  · subst bit
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "test.i") i) (And (@Eq Nat (Env.vars σ "test.bit") ((0:Nat))) (@Eq Nat (Env.vars σ "test.ok") ok))) => let c0:Prop:= @Eq Nat (Env.vars σ "test.bit") ((0:Nat)); let c1:Prop:=And c0 (@Eq Nat (Env.vars σ "test.ok") ok); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 i ((1:Nat)); let c4:Nat:= @ite Nat (@Eq Nat ((0:Nat)) ((0:Nat))) (instDecidableEqNat ((0:Nat)) ((0:Nat))) ok ((0:Nat)); let c5:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "test.i") c3) (@Eq Nat (Env.vars τ "test.ok") c4)) σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:=Not c0; let c9:Nat:=c2 (Env.vars σ "test.i") ((1:Nat)); let c10:Env:=Env.setVar σ "test.i" c9; let c11:Nat→ Nat:=c2 ((1:Nat)); let c12:Cond:=Cond.eq (Expr.var "test.bit") (Expr.lit ((0:Nat))); let c13:Nat→ Nat:=c2 (c11 (Cond.size c12)); let c14:Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "test.i") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Com:=Com.assign "test.ok" (Expr.lit ((0:Nat))); let c18:String→ Nat:=Env.vars c10; let c19:Env:=Env.setVar σ "test.ok" ((0:Nat)); let c20:Nat:=Env.vars c19 "test.i"; let c21:Nat:=c2 c20 ((1:Nat)); let c22:Env:=Env.setVar c19 "test.i" c21; let c23:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c13 c23; let c25:String→ Nat:=Env.vars c22; @And.casesOn (@Eq Nat (Env.vars σ "test.i") i) c1 (fun (x:And (@Eq Nat (Env.vars σ "test.i") i) c1) => c7) a fun (left:@Eq Nat (Env.vars σ "test.i") i) (right:c1) => @And.casesOn c0 (@Eq Nat (Env.vars σ "test.ok") ok) (fun (x:c1) => c7) right fun (left_1:c0) (right_1:@Eq Nat (Env.vars σ "test.ok") ok) => @Or.casesOn c0 c8 (fun (x:Or c0 c8) => c7) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c6 c10 (@And.intro (Run B update σ c10 ((10:Nat))) (c5 c10) (RunStep.mono B update σ c10 (c2 c14 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ σ c10 c14 c16 (RunStep.ite_true B c12 Com.skip c17 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hbit) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "test.i" c15 c9 (RunStep.eval_add B σ (Expr.var "test.i") (Expr.lit ((1:Nat))) (Env.vars σ "test.i") ((1:Nat)) (RunStep.eval_var B σ "test.i" (?nAX_g7963_0_0_1)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g7963_0_0_2)))) (?nAX_g7963_0_0_3)) ?_)) fun (hcase:c8) => @Exists.intro Env c6 c22 (@And.intro (Run B update σ c22 ((10:Nat))) (c5 c22) (RunStep.mono B update σ c22 (c2 c24 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ c19 c22 c24 c16 (RunStep.ite_false B c12 Com.skip c17 σ c19 c23 (RunStep.cond_eq_false B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ hbit) hcase) (RunStep.assign B σ "test.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hbit))) (RunStep.assign B c19 "test.i" c15 c21 (RunStep.eval_add B c19 (Expr.var "test.i") (Expr.lit ((1:Nat))) c20 ((1:Nat)) (RunStep.eval_var B c19 "test.i" (?nAX_g7963_0_0_5)) (RunStep.eval_lit B ((1:Nat)) c19 h1) (?nAX_g7963_0_0_6)))) (?nAX_g7963_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7963_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "test.i") i) (And (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 i ((1:Nat)); let c3:Nat:= @ite Nat (@Eq Nat bit ((0:Nat))) (instDecidableEqNat bit ((0:Nat))) ok ((0:Nat)); let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "test.i") c2) (@Eq Nat (Env.vars τ "test.ok") c3)) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c4 σ'); let c6:Prop:= @Exists Env c5; let c7:Prop:= @Eq Nat (Env.vars σ "test.bit") ((0:Nat)); let c8:Prop:=Not c7; let c9:Nat:=c1 (Env.vars σ "test.i") ((1:Nat)); let c10:Env:=Env.setVar σ "test.i" c9; let c11:Nat→ Nat:=c1 ((1:Nat)); let c12:Cond:=Cond.eq (Expr.var "test.bit") (Expr.lit ((0:Nat))); let c13:Nat→ Nat:=c1 (c11 (Cond.size c12)); let c14:Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "test.i") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Com:=Com.assign "test.ok" (Expr.lit ((0:Nat))); let c18:String→ Nat:=Env.vars c10; let c19:Env:=Env.setVar σ "test.ok" ((0:Nat)); let c20:Nat:=Env.vars c19 "test.i"; let c21:Nat:=c1 c20 ((1:Nat)); let c22:Env:=Env.setVar c19 "test.i" c21; let c23:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c13 c23; let c25:String→ Nat:=Env.vars c22; @And.casesOn (@Eq Nat (Env.vars σ "test.i") i) c0 (fun (x:And (@Eq Nat (Env.vars σ "test.i") i) c0) => c6) a fun (left:@Eq Nat (Env.vars σ "test.i") i) (right:c0) => @And.casesOn (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok) (fun (x:c0) => c6) right fun (left_1:@Eq Nat (Env.vars σ "test.bit") bit) (right_1:@Eq Nat (Env.vars σ "test.ok") ok) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c6) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c5 c10 (@And.intro (Run B update σ c10 ((10:Nat))) (c4 c10) (RunStep.mono B update σ c10 (c1 c14 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ σ c10 c14 c16 (RunStep.ite_true B c12 Com.skip c17 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_1)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "test.i" c15 c9 (RunStep.eval_add B σ (Expr.var "test.i") (Expr.lit ((1:Nat))) (Env.vars σ "test.i") ((1:Nat)) (RunStep.eval_var B σ "test.i" (?nAX_g7963_1_0_2)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g7963_1_0_3)))) (?nAX_g7963_1_0_4)) ?_)) fun (hcase:c8) => @Exists.intro Env c5 c22 (@And.intro (Run B update σ c22 ((10:Nat))) (c4 c22) (RunStep.mono B update σ c22 (c1 c24 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ c19 c22 c24 c16 (RunStep.ite_false B c12 Com.skip c17 σ c19 c23 (RunStep.cond_eq_false B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_1_0_5)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_6)) hcase) (RunStep.assign B σ "test.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_7)))) (RunStep.assign B c19 "test.i" c15 c21 (RunStep.eval_add B c19 (Expr.var "test.i") (Expr.lit ((1:Nat))) c20 ((1:Nat)) (RunStep.eval_var B c19 "test.i" (?nAX_g7963_1_0_8)) (RunStep.eval_lit B ((1:Nat)) c19 h1) (?nAX_g7963_1_0_9)))) (?nAX_g7963_1_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7963_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]

def Invariant (P:Env→ Prop) (xs:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "test.limit"=xs.length∧ σ.vars "test.i"≤ xs.length∧
  σ.vars "test.ok"=prefixOK xs (σ.vars "test.i")

theorem command_spec (B:ℕ) (xs:List ℕ) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:xs.length+2< B) (hwords:∀ x∈xs,x< B)
    (hri:"test.i"∉read.wvars) (hrl:"test.limit"∉read.wvars) (hro:"test.ok"∉read.wvars)
    (hinit:∀ σ,P σ→ P ((σ.setVar "test.ok" 1).setVar "test.i" 0))
    (hupdate:∀ σ τ,Run B update σ τ 10→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "test.i"=i) read
      (fun _ τ => P τ∧ τ.vars "test.bit"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "test.limit"=xs.length) (command read)
      (fun _ τ => P τ∧ τ.vars "test.ok"=prefixOK xs xs.length)
      ((K+14)*xs.length+8):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant P xs σ∧ σ.vars "test.i"< xs.length) (body read)
      (fun σ τ => Invariant P xs τ∧ τ.vars "test.i"=σ.vars "test.i"+1) (K+10):=by
    rintro σ ⟨⟨hPσ,hlen,hle,hok⟩,hlt⟩
    let i:=σ.vars "test.i"
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hPσ,rfl⟩
    have hiν:ν.vars "test.i"=i:=r1.frame_var "test.i" hri
    have hokν:ν.vars "test.ok"=prefixOK xs i:=(r1.frame_var "test.ok" hro).trans hok
    obtain ⟨τ,r2,p2⟩:=update_spec B i xs[i] (prefixOK xs i) (by dsimp [i]; omega)
      (hwords _ (List.getElem_mem hlt)) (prefix_ok_le xs i) h1 ν ⟨hiν,p1.2,hokν⟩
    have hPτ:P τ:=hupdate ν τ r2 p1.1
    refine ⟨τ,r1.seq r2,⟨hPτ,?_,by rw [p2.1]; omega,?_⟩,p2.1⟩
    · exact (r2.frame_var "test.limit" (by decide)).trans ((r1.frame_var "test.limit" hrl).trans hlen)
    · rw [p2.1,prefix_ok_succ xs i hlt]
      exact p2.2
  have hloop:=Spec.forRangeZero "test.i" "test.limit" (Invariant P xs) xs.length (K+10)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hPσ,hlen⟩
  let ν:=σ.setVar "test.ok" 1
  have r1:Run B (.assign "test.ok" (.lit 1)) σ ν 2:=Run.assign (evalB_lit h1)
  have hi:Invariant P xs (ν.setVar "test.i" 0):=by
    refine ⟨?_,?_,by simp,?_⟩
    · exact hinit σ hPσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hlen
    · simp [ν,prefix_ok_zero]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_⟩
  simpa only [p2.2] using p2.1.2.2.2

end Lax263307Proofs.NativeZeroScan

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeIndependentTest

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

def pairValue {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):ℕ:=
  (if u∈I then 1 else 0)*(if v∈I then 1 else 0)*(if G.Adj u v then 1 else 0)

theorem pair_value_le {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):pairValue G I u v≤1:=by
  unfold pairValue
  split_ifs <;> norm_num

theorem pair_value_zero {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):pairValue G I u v=0↔ (u∈I→ v∈I→ ¬G.Adj u v):=by
  unfold pairValue
  split_ifs <;> simp_all

def values {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):List ℕ:=
  List.ofFn fun q:Fin (n*n) => pairValue G I (NativeBlowUp.row q) (NativeBlowUp.col q)

theorem values_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):(values G I).length=n*n:=List.length_ofFn

theorem values_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):
    NativeZeroScan.prefixOK (values G I) (n*n)=1↔ G.IsIndepSet (I:Set (Fin n)):=by
  rw [←values_length G I,NativeZeroScan.prefix_ok_full]
  constructor
  · intro h u hu v hv huv
    let q:Fin (n*n):= ⟨u.val*n+v.val,by nlinarith only [u.isLt,v.isLt]⟩
    have hn:0< n:=by omega
    have hrow:NativeBlowUp.row q=u:=by
      apply Fin.ext
      dsimp [NativeBlowUp.row,q]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt]
      omega
    have hcol:NativeBlowUp.col q=v:=by
      apply Fin.ext
      simp [NativeBlowUp.col,q,Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
    have hh:=h _ (List.mem_ofFn.mpr ⟨q,rfl⟩)
    rw [hrow,hcol,pair_value_zero] at hh
    exact hh hu hv
  · intro h z hz
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz
    rw [pair_value_zero]
    intro hu hv hadj
    exact h hu hv hadj.ne hadj

theorem read_spec (B n q a b e:ℕ) (graphArray membershipArray:String)
    (hB:n*n+n+3< B) (hq:q< n*n) (ha:a≤1) (hb:b≤1) (he:e≤1):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "test.i"=q∧
      (σ.arrs membershipArray)[q/n]?=some a∧ (σ.arrs membershipArray)[q%n]?=some b∧
      (σ.arrs graphArray)[q]?=some e) (read graphArray membershipArray)
      (fun _ τ => τ.vars "test.bit"=a*b*e) 24:=by
  have hn:0< n:=by nlinarith only [hq]
  have hqn:q/n< n:=(Nat.div_lt_iff_lt_mul hn).mpr hq
  have hmod:q%n< n:=Nat.mod_lt _ hn
  have hqB:q< B:=by omega
  have hdivmul:q/n*n≤ q:=Nat.div_mul_le_self _ _
  have hab:a*b≤1:=by nlinarith only [Nat.mul_le_mul ha hb]
  have habe:a*b*e≤1:=by nlinarith only [Nat.mul_le_mul hab he]
  rintro σ ⟨hnσ,hqσ,haσ,hbσ,heσ⟩
  have hrooma:q/n<(σ.arrs membershipArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at haσ
    contradiction
  have hroomb:q%n<(σ.arrs membershipArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hbσ
    contradiction
  have hroome:q<(σ.arrs graphArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at heσ
    contradiction
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (c0 a b) e; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "test.bit") c1) σ; let c3:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "test.i") (Env.vars σ "graph.n"); let c4:Env:=Env.setVar σ "test.row" c3; let c5:String→ Nat:=Env.vars c4; let c6:Nat:=c5 "test.i"; let c7:Nat:=c5 "test.row"; let c8:Nat:=c5 "graph.n"; let c9:Nat:=c0 c7 c8; let c10:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c6 c9; let c11:Env:=Env.setVar c4 "test.col" c10; let c12:String→ List Nat:=Env.arrs c11; let c13:List Nat:=c12 membershipArray; let c14:Nat→ Nat→ Nat:= @List.getD Nat c13; let c15:String→ Nat:=Env.vars c11; let c16:Nat:=c15 "test.row"; let c17:Nat:=c14 c16 ((0:Nat)); let c18:Nat:=c15 "test.col"; let c19:Nat:=c14 c18 ((0:Nat)); let c20:Nat:=c0 c17 c19; let c21:Nat:=c15 "test.i"; let c22:Nat:= @List.getD Nat (c12 graphArray) c21 ((0:Nat)); let c23:Nat:=c0 c20 c22; let c24:Env:=Env.setVar c11 "test.bit" c23; let c25:Nat→ Nat→ Nat:=Nat.add; let c26:Nat→ Nat:=c25 ((1:Nat)); let c27:Nat:=c26 (Expr.size (Expr.div (Expr.var "test.i") (Expr.var "graph.n"))); let c28:Expr:=Expr.sub (Expr.var "test.i") (Expr.mul (Expr.var "test.row") (Expr.var "graph.n")); let c29:Nat:=c26 (Expr.size c28); let c30:Expr:=Expr.mul (Expr.get membershipArray (Expr.var "test.row")) (Expr.get membershipArray (Expr.var "test.col")); let c31:Expr:=Expr.mul c30 (Expr.get graphArray (Expr.var "test.i")); let c32:Nat:=c26 (Expr.size c31); let c33:Nat:=c25 c29 c32; let c34:Com:=Com.assign "test.col" c28; let c35:Com:=Com.assign "test.bit" c31; let c36:Nat→ Prop:=Nat.lt c16; let c37:Nat:= @List.length Nat c13; @Exists.intro Env (fun (σ':Env) => And (Run B (read graphArray membershipArray) σ σ' ((24:Nat))) (c2 σ')) c24 (@And.intro (Run B (read graphArray membershipArray) σ c24 ((24:Nat))) (c2 c24) (RunStep.mono B (read graphArray membershipArray) σ c24 (c25 c27 c33) ((24:Nat)) (RunStep.seq B (Com.assign "test.row" (Expr.div (Expr.var "test.i") (Expr.var "graph.n"))) (Com.seq c34 c35) σ c4 c24 c27 c33 (RunStep.assign B σ "test.row" (Expr.div (Expr.var "test.i") (Expr.var "graph.n")) c3 (RunStep.eval_div B σ (Expr.var "test.i") (Expr.var "graph.n") (Env.vars σ "test.i") (Env.vars σ "graph.n") (RunStep.eval_var B σ "test.i" (?nAX_g7975_0_0_0)) (RunStep.eval_var B σ "graph.n" (?nAX_g7975_0_0_1)) ?_)) (RunStep.seq B c34 c35 c4 c11 c24 c29 c32 (RunStep.assign B c4 "test.col" c28 c10 (RunStep.eval_sub B c4 (Expr.var "test.i") (Expr.mul (Expr.var "test.row") (Expr.var "graph.n")) c6 c9 (RunStep.eval_var B c4 "test.i" (?nAX_g7975_0_0_2)) (RunStep.eval_mul B c4 (Expr.var "test.row") (Expr.var "graph.n") c7 c8 (RunStep.eval_var B c4 "test.row" ?_) (RunStep.eval_var B c4 "graph.n" (?nAX_g7975_0_0_3)) ?_) (?nAX_g7975_0_0_4))) (RunStep.assign B c11 "test.bit" c31 c23 (RunStep.eval_mul B c11 c30 (Expr.get graphArray (Expr.var "test.i")) c20 c22 (RunStep.eval_mul B c11 (Expr.get membershipArray (Expr.var "test.row")) (Expr.get membershipArray (Expr.var "test.col")) c17 c19 (RunStep.eval_get B c11 membershipArray (Expr.var "test.row") c16 (RunStep.eval_var B c11 "test.row" ?_) ?_ ?_) (RunStep.eval_get B c11 membershipArray (Expr.var "test.col") c18 (RunStep.eval_var B c11 "test.col" (?nAX_g7975_0_0_5)) ?_ ?_) ?_) (RunStep.eval_get B c11 graphArray (Expr.var "test.i") c21 (RunStep.eval_var B c11 "test.i" (?nAX_g7975_0_0_6)) (?nAX_g7975_0_0_7) ?_) ?_)))) (?nAX_g7975_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7975_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]
  all_goals omega

def Representation {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) graphArray σ∧
    Prefix (encodeOutput I) membershipArray σ

theorem read_graph_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (hB:n*n+n+3< B)
    (q:ℕ) (hq:q<(values G I).length):
    Spec B (fun σ => Representation G I graphArray membershipArray σ∧ σ.vars "test.i"=q)
      (read graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ∧ τ.vars "test.bit"=(values G I)[q]) 24:=by
  have hq':q< n*n:=by rwa [values_length] at hq
  let u:=NativeBlowUp.row (⟨q,hq'⟩:Fin (n*n))
  let v:=NativeBlowUp.col (⟨q,hq'⟩:Fin (n*n))
  let a:=if u∈I then 1 else 0
  let b:=if v∈I then 1 else 0
  let e:=if G.Adj u v then 1 else 0
  have ha:a≤1:=by dsimp [a]; split_ifs <;> omega
  have hb:b≤1:=by dsimp [b]; split_ifs <;> omega
  have he:e≤1:=by dsimp [e]; split_ifs <;> omega
  rintro σ ⟨⟨hn,hgraph,hmem⟩,hqi⟩
  have hua:(σ.arrs membershipArray)[q/n]?=some a:=by
    have hh:=hmem u.val (by simp [encodeOutput])
    simpa [encodeOutput,a,u,NativeBlowUp.row] using hh
  have hvb:(σ.arrs membershipArray)[q%n]?=some b:=by
    have hh:=hmem v.val (by simp [encodeOutput])
    simpa [encodeOutput,b,v,NativeBlowUp.col] using hh
  have hge:(σ.arrs graphArray)[q]?=some e:=by
    have hh:=hgraph q (by rwa [NativeWeightReduction.adjacency_length])
    have hc:=NativeBlowUp.matrix_flat_coordinate (fun u v => if G.Adj u v then 1 else 0) (⟨q,hq'⟩:Fin (n*n))
    change (NativeWeightReduction.adjacency G)[q]?=some e at hc
    rw [List.getElem?_eq_getElem (by rwa [NativeWeightReduction.adjacency_length])] at hc
    exact hh.trans hc
  obtain ⟨τ,rr,p⟩:=read_spec B n q a b e graphArray membershipArray hB hq' ha hb he σ
    ⟨hn,hqi,hua,hvb,hge⟩
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by simp [read,Com.wvars])).trans hn,?_,?_⟩,?_⟩
  · simpa only [Prefix,rr.frame_arr graphArray (by simp [read,Com.warrs])] using hgraph
  · simpa only [Prefix,rr.frame_arr membershipArray (by simp [read,Com.warrs])] using hmem
  · simpa [values,pairValue,a,b,e,u,v] using p

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (hB:n*n+n+3< B):
    Spec B (Representation G I graphArray membershipArray) (command graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ∧
        τ.vars "test.ok"≤1∧ (τ.vars "test.ok"=1↔ G.IsIndepSet (I:Set (Fin n))))
      (38*n*n+12):=by
  have hwords:∀ z∈values G I,z< B:=by
    intro z hz
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz
    exact (pair_value_le G I _ _).trans_lt (by omega)
  have hs:=NativeZeroScan.command_spec B (values G I) (Representation G I graphArray membershipArray)
    (read graphArray membershipArray) 24 (by rw [values_length]; omega) hwords
    (by simp [read,Com.wvars]) (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by
      rintro σ ⟨hn,hg,hm⟩
      exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hn,hg,hm⟩)
    (by
      rintro σ τ rr ⟨hn,hg,hm⟩
      refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩
      · simpa only [Prefix,rr.frame_arr graphArray (by simp [NativeZeroScan.update,Com.warrs])] using hg
      · simpa only [Prefix,rr.frame_arr membershipArray (by simp [NativeZeroScan.update,Com.warrs])] using hm)
    (read_graph_spec B G I graphArray membershipArray hB)
  intro σ hσ
  let ν:=σ.setVar "test.limit" (n*n)
  have hnB:n< B:=by omega
  have hnnB:n*n< B:=by omega
  have r1:Run B (.assign "test.limit" (.mul (.var "graph.n") (.var "graph.n"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩) hnnB)
  have hν:Representation G I graphArray membershipArray ν:=
    ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hσ.1,hσ.2⟩
  obtain ⟨τ,r2,p2⟩:=hs ν ⟨hν,by simp [ν,values_length]⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [values_length]; nlinarith),p2.1,?_,?_⟩
  · rw [p2.2]
    exact NativeZeroScan.prefix_ok_le _ _
  · rw [p2.2,values_length,values_correct]

end Lax263307Proofs.NativeIndependentTest

end

section

namespace Lax263307Proofs.NativeCatalogOrder

open Lax263307

theorem sublist_toFinset_injective (n:ℕ) (xs ys:List (Fin n))
    (hx:xs.Sublist (List.finRange n)) (hy:ys.Sublist (List.finRange n))
    (he:xs.toFinset=ys.toFinset):xs=ys:=by
  have hs:(List.finRange n).Pairwise (fun u v:Fin n => u< v):=by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.getElem_finRange,Fin.lt_def,Fin.val_cast] using hij
  apply (hs.sublist hx).eq_of_mem_iff (hs.sublist hy)
  intro v
  have hh:=congrArg (fun I:Finset (Fin n) => v∈I) he
  simpa only [List.mem_toFinset] using Iff.of_eq hh

theorem candidates_nodup (n k:ℕ):(ExhaustiveTargets.candidates n k).Nodup:=by
  exact List.Nodup.map_on (by
    intro xs hx ys hy he
    exact sublist_toFinset_injective n xs ys (List.mem_sublistsLen.mp hx).1
      (List.mem_sublistsLen.mp hy).1 he)
    (List.nodup_sublistsLen k (List.nodup_finRange n))

theorem candidate_card (n k:ℕ) (I:Finset (Fin n)) (hI:I∈ExhaustiveTargets.candidates n k):
    I.card=k:=by
  obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hI
  obtain ⟨hsub,hlen⟩:=List.mem_sublistsLen.mp hxs
  rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)),hlen]

theorem all_candidates_nodup (n R:ℕ):(RationalConditioning.candidates n R).Nodup:=by
  change ((List.range (R+1)).flatMap (fun k => ExhaustiveTargets.candidates n k)).Nodup
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => candidates_nodup n k,?_⟩
  apply List.nodup_range.imp
  intro k l hne I hI hJ
  exact hne ((candidate_card n k I hI).symm.trans (candidate_card n l I hJ))

theorem sets_eq (n r:ℕ):CoordinateCatalog.sets n r=RationalConditioning.candidates n (r+2):=by
  exact List.dedup_eq_self.mpr (all_candidates_nodup n (r+2))

theorem catalog_values (n r:ℕ):
    (CoordinateCatalog.catalog n r).map Subtype.val=RationalConditioning.candidates n (r+2):=by
  rw [CoordinateCatalog.catalog,List.map_map]
  simpa only [Function.comp_def,List.attach_map_subtype_val] using sets_eq n r

theorem catalog_length (n r:ℕ):
    (CoordinateCatalog.catalog n r).length=(RationalConditioning.candidates n (r+2)).length:=by
  simpa only [List.length_map] using congrArg List.length (catalog_values n r)

theorem catalog_index (n r:ℕ) (j:Fin (CoordinateCatalog.catalog n r).length):
    (RationalConditioning.candidates n (r+2))[j.val]?=some (CoordinateCatalog.indexing n r j).val:=by
  rw [←catalog_values,List.getElem?_map,List.getElem?_eq_getElem j.isLt]
  rfl

theorem all_candidates_succ (n R:ℕ):
    RationalConditioning.candidates n (R+1)=
      RationalConditioning.candidates n R++ExhaustiveTargets.candidates n (R+1):=by
  unfold RationalConditioning.candidates ExhaustiveTargets.candidates
  rw [List.range_succ,List.flatMap_append]
  simp

end Lax263307Proofs.NativeCatalogOrder

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

theorem read_mask_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readMask
      (fun _ τ => Data G r τ∧ τ.vars "unpack.mask"=NativeMasks.mask (atIndex n r i)) 3:=by
  rintro σ ⟨hd,hi⟩
  have hlen:(Lax263307.NativeCatalog.words n r).length=N n r:=by simp [Lax263307.NativeCatalog.words]
  have hget:=hd.2.2.1 i.val (by rw [hlen]; exact i.isLt)
  have hw:(Lax263307.NativeCatalog.words n r)[i.val]=NativeMasks.mask (atIndex n r i):=by
    simp only [Lax263307.NativeCatalog.words,List.getElem_map]
    rfl
  rw [hw] at hget
  let τ:=σ.setVar "unpack.mask" (NativeMasks.mask (atIndex n r i))
  have rr:Run B readMask σ τ 3:=Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ i.isLt.trans hN⟩)
      hget ((NativeMasks.mask_bound _).trans hm))
  exact ⟨τ,rr,data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,by simp [τ]⟩

theorem prepare_set_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n+2< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) prepareSet
      (fun _ τ => Data G r τ∧ Prefix (encodeOutput (atIndex n r i)) "subset.bits" τ∧
        τ.vars "unpack.card"=(atIndex n r i).card) (21*n+11):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=read_mask_spec B G r i hN hm σ ⟨hd,hi⟩
  obtain ⟨τ,r2,p2⟩:=NativeMaskUnpack.command_spec B (atIndex n r i) hB hm ν
    ⟨p1.1.1,p1.2,p1.1.2.2.2.2⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,p2⟩

theorem read_card_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n+2< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readCard
      (fun _ τ => Data G r τ∧ τ.vars "fill.value"=(atIndex n r i).card) (21*n+13):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=prepare_set_spec B G r i hB hN hm σ ⟨hd,hi⟩
  let τ:=ν.setVar "fill.value" (atIndex n r i).card
  have r2:Run B (.assign "fill.value" (.var "unpack.card")) ν τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p1.2.2.symm,p1.2.2 ▸ (NativeMaskUnpack.card_bound _).trans_lt (by omega)⟩)
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,by simp [τ]⟩

theorem read_independent_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n*n+n+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readIndependent
      (fun _ τ => Data G r τ∧ τ.vars "fill.value"=if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)
      (38*n*n+21*n+25):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=prepare_set_spec B G r i (by omega) hN hm σ ⟨hd,hi⟩
  obtain ⟨μ,r2,p2⟩:=NativeIndependentTest.command_spec B G (atIndex n r i) "search.graph" "subset.bits" hB ν
    ⟨p1.1.1,p1.1.2.2.2.1,p1.2.1⟩
  have hok:μ.vars "test.ok"=if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0:=by
    split_ifs with h
    · exact p2.2.2.mpr h
    · have hh:μ.vars "test.ok"≠1:=fun h1 => h (p2.2.2.mp h1)
      omega
  let τ:=μ.setVar "fill.value" (μ.vars "test.ok")
  have r3:Run B (.assign "fill.value" (.var "test.ok")) μ τ 2:=Run.assign (evalB_var (p2.2.1.trans_lt (by omega)))
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by omega),data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,
    by simpa only [τ,vars_setVar,if_true] using hok⟩

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (hB:n*n+n+3< B) (hN:N n r+1< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ N n r≤(σ.arrs "catalog.card").length∧ N n r≤(σ.arrs "catalog.independent").length)
      command (fun _ τ => Data G r τ∧ Prefix (cards n r) "catalog.card" τ∧ Prefix (independent G r) "catalog.independent" τ)
      ((38*n*n+42*n+60)*(N n r)+14):=by
  have hc:(cards n r).length=N n r:=List.length_ofFn
  have hi:(independent G r).length=N n r:=List.length_ofFn
  have hcards:=NativeTabulate.command_spec B (cards n r) "catalog.card" (Data G r) readCard (21*n+13)
    (by rwa [hc]) (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; exact (NativeMaskUnpack.card_bound _).trans_lt (by omega))
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i hi; simpa only [cards,List.getElem_ofFn] using read_card_spec B G r ⟨i,by rwa [hc] at hi⟩ (by omega) (by omega) hm)
  have hind:=NativeTabulate.command_spec B (independent G r) "catalog.independent" (Data G r) readIndependent (38*n*n+21*n+25)
    (by rwa [hi]) (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; split_ifs <;> omega)
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i h; simpa only [independent,List.getElem_ofFn] using read_independent_spec B G r ⟨i,by rwa [hi] at h⟩ hB (by omega) hm)
  rintro σ ⟨hd,hcr,hir⟩
  let ν:=σ.setVar "fill.length" (N n r)
  have r1:Run B (.assign "fill.length" (.var "catalog.count")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.2.1.symm,hd.2.1 ▸ (by omega)⟩)
  have d1:=data_frame G r r1 (by decide) (by decide) (by decide) (by decide) hd
  obtain ⟨μ,r2,p2⟩:=hcards ν ⟨d1,by simp [ν,hc],by simpa only [ν,arrs_setVar,hc] using hcr⟩
  have hlength:μ.vars "fill.length"=(independent G r).length:=by
    rw [r2.frame_var "fill.length" (by decide)]
    simp [ν,hi]
  obtain ⟨τ,r3,p3⟩:=hind μ ⟨p2.1,hlength,by rw [hi,Lax455465Proofs.RamFrames.run_array_length r2]; exact hir⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hc,hi]; nlinarith),p3.1,?_,p3.2⟩
  simpa only [Prefix,r3.frame_arr "catalog.card" (by decide)] using p2.2

end Lax263307Proofs.NativeCatalogMetadata

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentAccess

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeCatalogMetadata

theorem mask_word (n r:ℕ) (i:Fin (N n r)):
    (Lax263307.NativeCatalog.words n r)[i.val]?=some (NativeMasks.mask (atIndex n r i)):=by
  rw [Lax263307.NativeCatalog.words,List.getElem?_map,List.getElem?_eq_getElem i.isLt]
  rfl

end Lax263307Proofs.NativeMomentAccess

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

namespace Lax263307Proofs.NativeSignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic

def partialSum (xs:List ℚ) (i:ℕ):ℚ:=(xs.take i).sum

theorem partial_step (xs:List ℚ) (i:ℕ) (hi:i< xs.length):
    partialSum xs (i+1)=partialSum xs i+xs[i]:=by
  simp only [partialSum,List.take_succ_eq_append_getElem hi,List.sum_append,List.sum_singleton]

def Context (xs:List ℚ) (σ:Env):Prop:=
  Prefix (NativeRationalTabulate.words xs) "sum.input" σ∧ σ.vars "sum.count"=xs.length

def Invariant (xs:List ℚ) (σ:Env):Prop:=
  Context xs σ∧ σ.vars "sum.i"≤ xs.length∧ Stored "sum.value" (partialSum xs (σ.vars "sum.i")) σ

theorem setup_spec (B:ℕ) (h1:1< B):
    Spec B (fun _ => True) setup (fun _ τ => Stored "sum.value" 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=Stored "sum.value" (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "sum.value.s" ((0:Nat)); let c3:Env:=Env.setVar c2 "sum.value.n" ((0:Nat)); let c4:Env:=Env.setVar c3 "sum.value.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c8:Nat→ Nat:=c5 c7; let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Nat:=c8 c9; let c11:Com:=Com.assign "sum.value.n" (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "sum.value.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c1 σ')) c4 (@And.intro (Run B setup σ c4 ((6:Nat))) (c1 c4) (RunStep.mono B setup σ c4 (c8 c10) ((6:Nat)) (RunStep.seq B (Com.assign "sum.value.s" (Expr.lit ((0:Nat)))) (Com.seq c11 c12) σ c2 c4 c7 c10 (RunStep.assign B σ "sum.value.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8245_0_0_0))) (RunStep.seq B c11 c12 c2 c3 c4 c7 c9 (RunStep.assign B c2 "sum.value.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g8245_0_0_1))) (RunStep.assign B c3 "sum.value.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1)))) (?nAX_g8245_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8245_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8245_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8245_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored,fractionValue]

theorem read_spec (B H:ℕ) (xs:List ℚ) (i:ℕ) (hi:i< xs.length)
    (hs:3*xs.length+10< B) (hH:H< B) (hx:∀ x∈xs,Bounded H x):
    Spec B (fun σ => Context xs σ∧ σ.vars "sum.i"=i) read
      (fun _ τ => FractionOutput xs[i] τ) 21:=by
  rintro σ ⟨hc,hiσ⟩
  let ν:=σ.setVar "read.cursor" (3*i)
  have r1:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "sum.i"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega:3< B))
      (by rw [evalB_var_iff]; exact ⟨hiσ.symm,hiσ ▸ (by omega:i< B)⟩)
      (by change 3*i< B; omega))
  have hxi:=hx xs[i] (List.getElem_mem hi)
  obtain ⟨τ,r2,p2⟩:=NativeRationalRead.vector_entry_spec B "sum.input" [] [] xs i hi (by omega)
    (by simp; omega) (hxi.1.trans_lt hH) (hxi.2.trans_lt hH) ν
    ⟨by simpa only [List.nil_append,List.append_nil,Prefix,ν,arrs_setVar] using hc.1,by simp [ν]⟩
  exact ⟨τ,r1.seq r2,p2.1⟩

theorem command_spec (B H:ℕ) (xs:List ℚ) (hB:2*H^2+3< B)
    (hs:3*xs.length+10< B) (hx:∀ x∈xs,Bounded H x)
    (hp:∀ i≤ xs.length,Bounded H (partialSum xs i)):
    Spec B (Context xs) command (fun _ τ => Context xs τ∧ FractionOutput xs.sum τ)
      ((36*(H^2).size+149)*xs.length+18):=by
  have h1:1< B:=by nlinarith
  have hH:H< B:=by nlinarith
  have hbody:Spec B (fun σ => Invariant xs σ∧ σ.vars "sum.i"< xs.length) body
      (fun σ τ => Invariant xs τ∧ τ.vars "sum.i"=σ.vars "sum.i"+1)
      (36*(H^2).size+145):=by
    rintro σ ⟨⟨hc,hle,hacc⟩,hlt⟩
    let i:=σ.vars "sum.i"
    obtain ⟨ν,r1,p1⟩:=read_spec B H xs i hlt hs hH hx σ ⟨hc,rfl⟩
    have haccν:Stored "sum.value" (partialSum xs i) ν:=by
      simpa only [Stored,String.reduceAppend,r1.frame_var "sum.value.s" (by decide),
        r1.frame_var "sum.value.n" (by decide),r1.frame_var "sum.value.d" (by decide)] using hacc
    obtain ⟨μ,r2,p2⟩:=NativeSignedAccumulate.command_spec B H (partialSum xs i) xs[i] hB
      (hp i hle) (hx xs[i] (List.getElem_mem hlt)) ν ⟨haccν,p1⟩
    have hiμ:μ.vars "sum.i"=i:=(r1.seq r2).frame_var "sum.i" (by decide)
    let τ:=μ.setVar "sum.i" (i+1)
    have r3:Run B advance μ τ 4:=Run.assign
      (evalB_bin (op:=.add)
        (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i< B)⟩)
        (evalB_lit h1) (by change i+1< B; omega))
    have ht:τ.vars "sum.i"=i+1:=by simp [τ]
    have rr:=r1.seq (r2.seq r3)
    refine ⟨τ,rr.mono (by omega),⟨?_,by rw [ht]; omega,?_⟩,ht⟩
    · simpa only [Context,Prefix,rr.frame_arr "sum.input" (by decide),
        rr.frame_var "sum.count" (by decide)] using hc
    · rw [ht,partial_step xs i hlt]
      simpa only [Stored,String.reduceAppend,r3.frame_var "sum.value.s" (by decide),
        r3.frame_var "sum.value.n" (by decide),r3.frame_var "sum.value.d" (by decide)] using p2.1
  have hloop:=Spec.forRangeZero "sum.i" "sum.count" (Invariant xs) xs.length
    (36*(H^2).size+145) (by omega) (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  obtain ⟨ν,r1,p1⟩:=setup_spec B h1 σ trivial
  have hcν:Context xs ν:=by
    simpa only [Context,Prefix,r1.frame_arr "sum.input" (by decide),
      r1.frame_var "sum.count" (by decide)] using hc
  have hinit:Invariant xs (ν.setVar "sum.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hcν
    · simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false,if_true,
        partialSum,List.take_zero,List.sum_nil] using p1
  obtain ⟨μ,r2,p2⟩:=hloop ν hinit
  have hsum:Bounded H xs.sum:=by simpa only [partialSum,List.take_length] using hp xs.length le_rfl
  have hstored:Stored "sum.value" xs.sum μ:=by
    simpa only [p2.2,partialSum,List.take_length] using p2.1.2.2
  obtain ⟨τ,r3,p3⟩:=load_spec B "sum.value" xs.sum h1
    (hsum.1.trans_lt hH) (hsum.2.trans_lt hH) (by decide) μ hstored
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),?_,p3⟩
  simpa only [Context,Prefix,r3.frame_arr "sum.input" (by decide),
    r3.frame_var "sum.count" (by decide)] using p2.1.1

theorem bounded_spec (B M:ℕ) (xs:List ℚ) (hM:1≤ M)
    (hB:2*((2*M)^(xs.length+1))^2+3< B) (hs:3*xs.length+10< B)
    (hx:∀ x∈xs,Bounded M x):
    Spec B (Context xs) command (fun _ τ => Context xs τ∧ FractionOutput xs.sum τ)
      ((36*(((2*M)^(xs.length+1))^2).size+149)*xs.length+18):=by
  exact command_spec B ((2*M)^(xs.length+1)) xs hB hs
    (NativeSumHeight.uniform_entry M xs hM hx)
    (fun i _ => NativeSumHeight.uniform_partial M xs hM hx i)

end Lax263307Proofs.NativeSignedSum

end

section

namespace Lax263307Proofs.NativeNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Context (b e:ℕ) (σ:Env):Prop:=σ.vars "power.base"=b∧ σ.vars "power.exponent"=e

def Invariant (b e:ℕ) (σ:Env):Prop:=
  Context b e σ∧ σ.vars "power.i"≤ e∧ σ.vars "power.value"=b^(σ.vars "power.i")

theorem step_spec (B b e i:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B) (hi:i< e):
    Spec B (fun σ => Context b e σ∧ σ.vars "power.i"=i∧ σ.vars "power.value"=b^i) step
      (fun _ τ => Context b e τ∧ τ.vars "power.i"=i+1∧ τ.vars "power.value"=b^(i+1)) 8:=by
  have hp:b^i< B:=(Nat.pow_le_pow_right hb hi.le).trans_lt (by omega)
  have hnext:b^i*b< B:=by
    rw [←pow_succ]
    exact (Nat.pow_le_pow_right hb hi).trans_lt (by omega)
  (expose_names;
    (refine fun (σ:Env) (a:And (Context b e σ) (And (@Eq Nat (Env.vars σ "power.i") i) (@Eq Nat (Env.vars σ "power.value") (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b i)))) => let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b; let c1:Prop:= @Eq Nat (Env.vars σ "power.value") (c0 i); let c2:Prop:=And (@Eq Nat (Env.vars σ "power.i") i) c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=c3 i ((1:Nat)); let c5:Nat:=c0 c4; let c6:Env→ Prop:=(fun (x τ:Env) => And (Context b e τ) (And (@Eq Nat (Env.vars τ "power.i") c4) (@Eq Nat (Env.vars τ "power.value") c5))) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B step σ σ' ((8:Nat))) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:Nat:=Nat.mul (Env.vars σ "power.value") (Env.vars σ "power.base"); let c10:Env:=Env.setVar σ "power.value" c9; let c11:Nat:=Env.vars c10 "power.i"; let c12:Nat:=c3 c11 ((1:Nat)); let c13:Env:=Env.setVar c10 "power.i" c12; let c14:Nat→ Nat:=c3 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))); let c16:Expr:=Expr.add (Expr.var "power.i") (Expr.lit ((1:Nat))); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c13; @And.casesOn (Context b e σ) c2 (fun (x:And (Context b e σ) c2) => c8) a fun (left:Context b e σ) (right:c2) => @And.casesOn (@Eq Nat (Env.vars σ "power.i") i) c1 (fun (x:c2) => c8) right fun (left_1:@Eq Nat (Env.vars σ "power.i") i) (right_1:c1) => @Exists.intro Env c7 c13 (@And.intro (Run B step σ c13 ((8:Nat))) (c6 c13) (RunStep.mono B step σ c13 (c3 c15 c17) ((8:Nat)) (RunStep.seq B (Com.assign "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))) (Com.assign "power.i" c16) σ c10 c13 c15 c17 (RunStep.assign B σ "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base")) c9 (RunStep.eval_mul B σ (Expr.var "power.value") (Expr.var "power.base") (Env.vars σ "power.value") (Env.vars σ "power.base") (RunStep.eval_var B σ "power.value" (?nAX_g8253_0_0_0)) (RunStep.eval_var B σ "power.base" ?_) ?_)) (RunStep.assign B c10 "power.i" c16 c12 (RunStep.eval_add B c10 (Expr.var "power.i") (Expr.lit ((1:Nat))) c11 ((1:Nat)) (RunStep.eval_var B c10 "power.i" (?nAX_g8253_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g8253_0_0_2)) (?nAX_g8253_0_0_3)))) (?nAX_g8253_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8253_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,pow_succ]
  all_goals omega

theorem command_spec (B b e:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B):
    Spec B (Context b e) command
      (fun _ τ => Context b e τ∧ τ.vars "power.value"=b^e) (12*e+8):=by
  have hbody:Spec B (fun σ => Invariant b e σ∧ σ.vars "power.i"< e) step
      (fun σ τ => Invariant b e τ∧ τ.vars "power.i"=σ.vars "power.i"+1) 8:=by
    rintro σ ⟨⟨hc,hle,hv⟩,hlt⟩
    obtain ⟨τ,rr,ht⟩:=step_spec B b e (σ.vars "power.i") hb hB hlt σ ⟨hc,rfl,hv⟩
    exact ⟨τ,rr,⟨ht.1,by rw [ht.2.1]; omega,by simpa only [ht.2.1] using ht.2.2⟩,ht.2.1⟩
  have hloop:=Spec.forRangeZero "power.i" "power.exponent" (Invariant b e) e 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν:=σ.setVar "power.value" 1
  have r1:Run B (.assign "power.value" (.lit 1)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant b e (ν.setVar "power.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,ν,vars_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,by simpa only [p2.2] using p2.1.2.2⟩

end Lax263307Proofs.NativeNaturalPower

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

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeWordLookup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def Context (array:String) {N:ℕ} (keys:Fin N→ ℕ) (i:Fin N) (σ:Env):Prop:=
  Prefix (List.ofFn keys) array σ∧ σ.vars "lookup.count"=N∧ σ.vars "lookup.key"=keys i

def Invariant (array:String) {N:ℕ} (keys:Fin N→ ℕ) (i:Fin N) (σ:Env):Prop:=
  Context array keys i σ∧ σ.vars "lookup.j"≤ N∧
    σ.vars "lookup.result"=if i.val<σ.vars "lookup.j" then i.val else N

theorem update_spec (B N:ℕ) (keys:Fin N→ ℕ) (hinj:Function.Injective keys)
    (hk:∀ i,keys i< B) (hN:N+2< B) (i j:Fin N):
    Spec B (fun σ => σ.vars "lookup.j"=j.val∧ σ.vars "lookup.key"=keys i∧
      σ.vars "lookup.current"=keys j∧
      σ.vars "lookup.result"=if i.val< j.val then i.val else N) update
      (fun _ τ => τ.vars "lookup.j"=j.val+1∧
        τ.vars "lookup.result"=if i.val< j.val+1 then i.val else N) 10:=by
  have he:keys j=keys i↔ j=i:= ⟨fun h => hinj h,fun h => congrArg keys h⟩
  have hi:=i.isLt
  have hj:=j.isLt
  have hki:=hk i
  have hkj:=hk j
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "lookup.j") (@Fin.val N j)) (And (@Eq Nat (Env.vars σ "lookup.key") (keys i)) (And (@Eq Nat (Env.vars σ "lookup.current") (keys j)) (@Eq Nat (Env.vars σ "lookup.result") (@ite Nat (Nat.lt (@Fin.val N i) (@Fin.val N j)) (Nat.decLt (@Fin.val N i) (@Fin.val N j)) (@Fin.val N i) N))))) => let c0:Prop:= @Eq Nat (Env.vars σ "lookup.j") (@Fin.val N j); let c1:Prop:= @Eq Nat (Env.vars σ "lookup.key") (keys i); let c2:Prop:= @Eq Nat (Env.vars σ "lookup.current") (keys j); let c3:Prop:= @Eq Nat (Env.vars σ "lookup.result") (@ite Nat (Nat.lt (@Fin.val N i) (@Fin.val N j)) (Nat.decLt (@Fin.val N i) (@Fin.val N j)) (@Fin.val N i) N); let c4:Prop:=And c2 c3; let c5:Prop:=And c1 c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=c6 (@Fin.val N j) ((1:Nat)); let c8:Nat:= @ite Nat (Nat.lt (@Fin.val N i) c7) (Nat.decLt (@Fin.val N i) c7) (@Fin.val N i) N; let c9:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lookup.j") c7) (@Eq Nat (Env.vars τ "lookup.result") c8)) σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:Prop:= @Eq Nat (Env.vars σ "lookup.current") (Env.vars σ "lookup.key"); let c13:Prop:=Not c12; let c14:Nat:=Env.vars (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) "lookup.j"; let c15:Nat:=c6 c14 ((1:Nat)); let c16:Env:=Env.setVar (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) "lookup.j" c15; let c17:Nat→ Nat:=c6 ((1:Nat)); let c18:Nat→ Nat:=c6 (c17 (Cond.size (Cond.eq (Expr.var "lookup.current") (Expr.var "lookup.key")))); let c19:Nat:=c17 (Expr.size (Expr.var "lookup.j")); let c20:Nat:=c18 c19; let c21:Expr:=Expr.add (Expr.var "lookup.j") (Expr.lit ((1:Nat))); let c22:Nat:=c17 (Expr.size c21); let c23:String→ Nat:=Env.vars c16; let c24:Nat:=c6 (Env.vars σ "lookup.j") ((1:Nat)); let c25:Env:=Env.setVar σ "lookup.j" c24; let c26:Nat:=c18 ((1:Nat)); let c27:String→ Nat:=Env.vars c25; @And.casesOn c0 c5 (fun (x:And c0 c5) => c11) a fun (left:c0) (right:c5) => @And.casesOn c1 c4 (fun (x:c5) => c11) right fun (left_1:c1) (right_1:c4) => @And.casesOn c2 c3 (fun (x:c4) => c11) right_1 fun (left_2:c2) (right_2:c3) => @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c11) (Classical.em c12) (fun (hcase:c12) => @Exists.intro Env c10 c16 (@And.intro (Run B update σ c16 ((10:Nat))) (c9 c16) (RunStep.mono B update σ c16 (c6 c20 c22) ((10:Nat)) (RunStep.seq B (Com.ite (Cond.eq (Expr.var "lookup.current") (Expr.var "lookup.key")) (Com.assign "lookup.result" (Expr.var "lookup.j")) Com.skip) (Com.assign "lookup.j" c21) σ (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) c16 c20 c22 (RunStep.ite_true B (Cond.eq (Expr.var "lookup.current") (Expr.var "lookup.key")) (Com.assign "lookup.result" (Expr.var "lookup.j")) Com.skip σ (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) c19 (RunStep.cond_eq_true B σ (Expr.var "lookup.current") (Expr.var "lookup.key") (Env.vars σ "lookup.current") (Env.vars σ "lookup.key") (RunStep.eval_var B σ "lookup.current" (?nAX_g8583_0_0_0)) (RunStep.eval_var B σ "lookup.key" (?nAX_g8583_0_0_1)) hcase) (RunStep.assign B σ "lookup.result" (Expr.var "lookup.j") (Env.vars σ "lookup.j") (RunStep.eval_var B σ "lookup.j" (?nAX_g8583_0_0_2)))) (RunStep.assign B (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) "lookup.j" c21 c15 (RunStep.eval_add B (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) (Expr.var "lookup.j") (Expr.lit ((1:Nat))) c14 ((1:Nat)) (RunStep.eval_var B (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) "lookup.j" (?nAX_g8583_0_0_3)) (RunStep.eval_lit B ((1:Nat)) (Env.setVar σ "lookup.result" (Env.vars σ "lookup.j")) (?nAX_g8583_0_0_4)) (?nAX_g8583_0_0_5)))) (?nAX_g8583_0_0_6)) ?_)) fun (hcase:c13) => @Exists.intro Env c10 c25 (@And.intro (Run B update σ c25 ((10:Nat))) (c9 c25) (RunStep.mono B update σ c25 (c6 c26 c22) ((10:Nat)) (RunStep.seq B (Com.ite (Cond.eq (Expr.var "lookup.current") (Expr.var "lookup.key")) (Com.assign "lookup.result" (Expr.var "lookup.j")) Com.skip) (Com.assign "lookup.j" c21) σ σ c25 c26 c22 (RunStep.ite_false B (Cond.eq (Expr.var "lookup.current") (Expr.var "lookup.key")) (Com.assign "lookup.result" (Expr.var "lookup.j")) Com.skip σ σ ((1:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lookup.current") (Expr.var "lookup.key") (Env.vars σ "lookup.current") (Env.vars σ "lookup.key") (RunStep.eval_var B σ "lookup.current" (?nAX_g8583_0_0_7)) (RunStep.eval_var B σ "lookup.key" (?nAX_g8583_0_0_8)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "lookup.j" c21 c24 (RunStep.eval_add B σ (Expr.var "lookup.j") (Expr.lit ((1:Nat))) (Env.vars σ "lookup.j") ((1:Nat)) (RunStep.eval_var B σ "lookup.j" (?nAX_g8583_0_0_9)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8583_0_0_10)) (?nAX_g8583_0_0_11)))) (?nAX_g8583_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8583_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8583_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Fin.ext_iff]
  all_goals simp_all only [Fin.lt_def,Fin.le_def]
  all_goals first | omega | (split_ifs at * <;> omega)

theorem command_spec (B N:ℕ) (array:String) (keys:Fin N→ ℕ)
    (hinj:Function.Injective keys) (hk:∀ i,keys i< B) (hN:N+2< B) (i:Fin N):
    Spec B (Context array keys i) (command array)
      (fun _ τ => Context array keys i τ∧ τ.vars "lookup.result"=i.val) (17*N+8):=by
  have hbody:Spec B (fun σ => Invariant array keys i σ∧ σ.vars "lookup.j"< N) (step array)
      (fun σ τ => Invariant array keys i τ∧ τ.vars "lookup.j"=σ.vars "lookup.j"+1) 13:=by
    rintro σ ⟨⟨hc,hj,hr⟩,hlt⟩
    let j:Fin N:= ⟨σ.vars "lookup.j",hlt⟩
    have hg:(σ.arrs array)[j.val]?=some (keys j):=by
      have hh:=hc.1 j.val (by simpa using j.isLt)
      simpa only [List.getElem_ofFn] using hh
    let ν:=σ.setVar "lookup.current" (keys j)
    have r1:Run B (read array) σ ν 3:=Run.assign
      (evalB_get (by rw [evalB_var_iff]; exact ⟨rfl,by omega⟩) hg (hk j))
    obtain ⟨τ,r2,p2⟩:=update_spec B N keys hinj hk hN i j ν
      ⟨r1.frame_var "lookup.j" (by simp [read,Com.wvars]),
        (r1.frame_var "lookup.key" (by simp [read,Com.wvars])).trans hc.2.2,
        by simp [ν],(r1.frame_var "lookup.result" (by simp [read,Com.wvars])).trans hr⟩
    have rr:=r1.seq r2
    refine ⟨τ,rr,⟨?_,by rw [p2.1]; exact j.isLt,?_⟩,p2.1⟩
    · simpa only [Context,Prefix,rr.frame_arr array (by simp [read,update,Com.warrs]),
        rr.frame_var "lookup.count" (by simp [read,update,Com.wvars]),
        rr.frame_var "lookup.key" (by simp [read,update,Com.wvars])] using hc
    · simpa only [p2.1] using p2.2
  have hloop:=Spec.forRangeZero "lookup.j" "lookup.count" (Invariant array keys i) N 13
    (by omega) (fun _ h => h.2.1) (fun _ h => h.1.2.1) hbody
  intro σ hc
  let ν:=σ.setVar "lookup.result" N
  have r1:Run B (.assign "lookup.result" (.var "lookup.count")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega:N< B)⟩)
  have hinit:Invariant array keys i (ν.setVar "lookup.j" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [ν,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩:=hloop ν hinit
  refine ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,?_⟩
  simpa only [p2.2,if_pos i.isLt] using p2.1.2.2

end Lax263307Proofs.NativeWordLookup

end

section

namespace Lax263307Proofs.NativeMomentValue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic
open NativeCatalogMetadata

def keys (n r:ℕ) (i:Fin (N n r)):ℕ:=NativeMasks.mask (atIndex n r i)

def values {n r:ℕ} (y:RationalVector n r) (i:Fin (N n r)):ℚ:=
  y (CoordinateCatalog.indexing n r i)

theorem values_decode {n r:ℕ} (x:Fin (N n r)→ ℚ):values (MomentLP.decode x)=x:=by
  funext i
  simp only [values,MomentLP.decode,Equiv.symm_apply_apply]

def Context {n r:ℕ} (y:RationalVector n r) (σ:Env):Prop:=
  Prefix (Lax263307.NativeCatalog.words n r) "catalog.mask" σ∧
  Prefix (encodeVector (values y)) "near.moments" σ∧ σ.vars "catalog.count"=N n r

theorem keys_injective (n r:ℕ):Function.Injective (keys n r):=by
  intro i j h
  apply (CoordinateCatalog.indexing n r).injective
  exact Subtype.ext (NativeMasks.mask_injective n h)

theorem keys_words (n r:ℕ):List.ofFn (keys n r)=Lax263307.NativeCatalog.words n r:=by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_ofFn]
  by_cases hj:j< N n r
  · rw [dif_pos hj,NativeMomentAccess.mask_word n r ⟨j,hj⟩]
    rfl
  · rw [dif_neg hj,List.getElem?_eq_none]
    simpa only [Lax263307.NativeCatalog.words,List.length_map] using Nat.le_of_not_gt hj

theorem command_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hA:A.card≤ r+2) (hN:3*N n r+10< B) (hm:2^n< B) (hM:M< B)
    (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Context y σ∧ σ.vars "lookup.key"=NativeMasks.mask A) command
      (fun _ τ => Context y τ∧ RamRational.FractionOutput (rationalValue y A) τ)
      (17*N n r+31):=by
  let i:=(CoordinateCatalog.indexing n r).symm ⟨A,hA⟩
  have hiA:atIndex n r i=A:=congrArg Subtype.val ((CoordinateCatalog.indexing n r).apply_symm_apply ⟨A,hA⟩)
  have hiY:values y i=rationalValue y A:=by simp [values,i,rationalValue,hA]
  rintro σ ⟨hc,hkey⟩
  let ν:=σ.setVar "lookup.count" (N n r)
  have r1:Run B (.assign "lookup.count" (.var "catalog.count")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.2.2.symm,hc.2.2 ▸ (by omega:N n r< B)⟩)
  obtain ⟨μ,r2,p2⟩:=NativeWordLookup.command_spec B (N n r) "catalog.mask" (keys n r)
    (keys_injective n r) (fun j => (NativeMasks.mask_bound _).trans hm) (by omega) i ν
    ⟨by simpa only [keys_words,Prefix,ν,arrs_setVar] using hc.1,
      by simp [ν],by simpa only [keys,hiA,ν,vars_setVar,String.reduceEq,if_false] using hkey⟩
  let ξ:=μ.setVar "read.cursor" (3*i.val)
  have r3:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "lookup.result"))) μ ξ 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega:3< B))
      (by rw [evalB_var_iff]; exact ⟨p2.2.symm,p2.2 ▸ (by have hh:=i.isLt; omega:i.val< B)⟩)
      (by change 3*i.val< B; have hh:=i.isLt; omega))
  have hsource:Prefix (encodeVector (values y)) "near.moments" ξ:=by
    simpa only [Prefix,(r1.seq (r2.seq r3)).frame_arr "near.moments" (by decide)] using hc.2.1
  obtain ⟨τ,r4,p4⟩:=NativeRationalRead.vector_entry_spec B "near.moments" [] [] (List.ofFn (values y))
    i.val (by simpa using i.isLt) (by omega) (by simp; have hh:=i.isLt; omega)
    (by simpa only [List.getElem_ofFn,values] using (hy (CoordinateCatalog.indexing n r i)).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn,values] using (hy (CoordinateCatalog.indexing n r i)).2.trans_lt hM) ξ
    ⟨by simpa only [List.nil_append,List.append_nil,NativeRationalTabulate.words,encodeVector] using hsource,
      by simp [ξ]⟩
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by omega),?_,by simpa only [List.getElem_ofFn,hiY] using p4.1⟩
  simpa only [Context,Prefix,rr.frame_arr "catalog.mask" (by decide),
    rr.frame_arr "near.moments" (by decide),rr.frame_var "catalog.count" (by decide)] using hc

end Lax263307Proofs.NativeMomentValue

end

section

namespace Lax263307Proofs.NativeMomentStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic NativeCatalogMetadata

theorem command_spec (B M n r:ℕ) (x:Fin (N n r)→ ℚ)
    (hN:3*N n r+10< B) (hM:M< B) (hx:∀ i,Bounded M (x i)):
    Spec B (fun σ => Prefix (encodeVector x) "lp.word" σ∧
      Prefix (Lax263307.NativeCatalog.words n r) "catalog.mask" σ∧
      σ.vars "catalog.count"=N n r∧ 3*N n r≤(σ.arrs "near.moments").length) command
      (fun _ τ => NativeMomentValue.Context (MomentLP.decode x) τ∧ Prefix (encodeVector x) "lp.word" τ)
      (48*N n r+12):=by
  have hlen:(encodeVector x).length=3*N n r:=by
    change (RamVectorEncoding.encode (List.ofFn x)).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup:Spec B (fun σ => σ.vars "catalog.count"=N n r) setup
      (fun _ τ => τ.vars "slice.start"=0∧ τ.vars "fill.length"=3*N n r) 6:=by
    (expose_names;
      (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ "catalog.count") (N n r)) => let c0:Nat→ Nat:=Nat.mul ((3:Nat)); let c1:Nat:=c0 (N n r); let c2:Env→ Prop:=(fun (x_1 τ:Env) => And (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))) (@Eq Nat (Env.vars τ "fill.length") c1)) σ; let c3:Env:=Env.setVar σ "slice.start" ((0:Nat)); let c4:Nat:=Env.vars c3 "catalog.count"; let c5:Nat:=c0 c4; let c6:Env:=Env.setVar c3 "fill.length" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c10:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "catalog.count"); let c11:Nat:=c8 (Expr.size c10); let c12:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c2 σ')) c6 (@And.intro (Run B setup σ c6 ((6:Nat))) (c2 c6) (RunStep.mono B setup σ c6 (c7 c9 c11) ((6:Nat)) (RunStep.seq B (Com.assign "slice.start" (Expr.lit ((0:Nat)))) (Com.assign "fill.length" c10) σ c3 c6 c9 c11 (RunStep.assign B σ "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8595_0_0_0))) (RunStep.assign B c3 "fill.length" c10 c5 (RunStep.eval_mul B c3 (Expr.lit ((3:Nat))) (Expr.var "catalog.count") ((3:Nat)) c4 (RunStep.eval_lit B ((3:Nat)) c3 (?nAX_g8595_0_0_1)) (RunStep.eval_var B c3 "catalog.count" (?nAX_g8595_0_0_2)) (?nAX_g8595_0_0_3)))) (?nAX_g8595_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8595_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8595_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8595_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8595_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8595_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  rintro σ ⟨hp,hkeys,hcount,hroom⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ hcount
  have hpν:Prefix (encodeVector x) "lp.word" ν:=by
    simpa only [Prefix,r1.frame_arr "lp.word" (by decide)] using hp
  obtain ⟨τ,r2,p2⟩:=NativeSlice.command_spec B "lp.word" "near.moments" [] (encodeVector x) []
    (by decide) (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B M (N n r) x (by omega) hM hx) ν
    ⟨⟨by simpa using hpν,by simpa using p1.1⟩,by simpa only [hlen] using p1.2,
      by rw [hlen,RamFrames.run_array_length r1]; exact hroom⟩
  have rr:=r1.seq r2
  refine ⟨τ,rr.mono (by rw [hlen]; omega),⟨?_,?_,?_⟩,?_⟩
  · simpa only [Prefix,rr.frame_arr "catalog.mask" (by decide)] using hkeys
  · simpa only [NativeMomentValue.values_decode] using p2.2
  · exact (rr.frame_var "catalog.count" (by decide)).trans hcount
  · simpa only [List.nil_append,List.append_nil] using p2.1.1

end Lax263307Proofs.NativeMomentStorage

end

section

namespace Lax263307Proofs.NativeConditioningVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic
open NativeCatalogMetadata

def Data {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n)) (σ:Env):Prop:=
  NativeMomentValue.Context y σ∧ σ.vars "conditioning.mask"=NativeMasks.mask A∧ σ.vars "graph.n"=n

theorem frame {B n r K:ℕ} {y:RationalVector n r} {A:Finset (Fin n)}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K) (hd:Data y A σ)
    (h0:"catalog.mask"∉c.warrs) (h1:"near.moments"∉c.warrs)
    (h2:"catalog.count"∉c.wvars) (h3:"conditioning.mask"∉c.wvars)
    (h4:"graph.n"∉c.wvars):Data y A τ:=by
  simpa only [Data,NativeMomentValue.Context,Prefix,rr.frame_arr "catalog.mask" h0,
    rr.frame_arr "near.moments" h1,rr.frame_var "catalog.count" h2,
    rr.frame_var "conditioning.mask" h3,rr.frame_var "graph.n" h4] using hd

theorem key_spec (B n:ℕ) (A:Finset (Fin n)) (v:Fin n)
    (hn:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "conditioning.mask"=NativeMasks.mask A∧
      σ.vars "conditioning.v"=v.val) key
      (fun _ τ => τ.vars "lookup.key"=NativeMasks.mask (insert v A)) 6:=by
  rintro σ ⟨hA,hv⟩
  have hpow:2^v.val< B:=(Nat.pow_lt_pow_right (by decide) v.isLt).trans hm
  have he:(Expr.or (.var "conditioning.mask") (.shiftl (.lit 1) (.var "conditioning.v"))).evalB B σ=
      some (NativeMasks.mask (insert v A)):=by
    have hh:=evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hA.symm,hA ▸ (NativeMasks.mask_bound _).trans hm⟩)
      (evalB_bin (op:=.shiftl) (evalB_lit (by omega:1< B))
        (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ (by have hh:=v.isLt; omega:v.val< B)⟩)
        (by simpa only [Bop.apply_shiftl,one_mul] using hpow))
      (by simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←NativeMasks.mask_insert]
        using (NativeMasks.mask_bound (insert v A)).trans hm)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←NativeMasks.mask_insert] using hh
  exact ⟨σ.setVar "lookup.key" (NativeMasks.mask (insert v A)),Run.assign he,by simp⟩

theorem read_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n)) (v:Fin n)
    (hA:A.card≤ r) (hN:3*N n r+10< B) (hn:n+2< B) (hm:2^n< B) (hM:M< B)
    (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Data y A σ∧ σ.vars "conditioning.v"=v.val) read
      (fun _ τ => Data y A τ∧ RamRational.FractionOutput (rationalValue y (insert v A)) τ)
      (17*N n r+37):=by
  rintro σ ⟨hd,hv⟩
  obtain ⟨ν,r1,p1⟩:=key_spec B n A v hn hm σ ⟨hd.2.1,hv⟩
  have hdν:=frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide)
  have hiA:(insert v A).card≤ r+2:=(Finset.card_insert_le v A).trans (by omega)
  obtain ⟨τ,r2,p2⟩:=NativeMomentValue.command_spec B M n r y (insert v A) hiA hN hm hM hy ν ⟨hdν.1,p1⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    frame r2 hdν (by decide) (by decide) (by decide) (by decide) (by decide),p2.2⟩

theorem command_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hA:A.card≤ r) (hN:3*N n r+10< B) (hn:3*n+3< B) (hm:2^n< B) (hM:M< B)
    (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Data y A σ∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Data y A τ∧ Prefix (encodeVector (fun v => rationalValue y (insert v A))) "lp.word" τ∧
        τ.vars "lp.position"=3*n) ((17*N n r+72)*n+8):=by
  have hv (v:Fin n):Bounded M (rationalValue y (insert v A)):=by
    have hh:(insert v A).card≤ r+2:=(Finset.card_insert_le v A).trans (by omega)
    simpa only [rationalValue,dif_pos hh] using hy ⟨insert v A,hh⟩
  have hh:=RamVectorEncoding.command_spec B (17*N n r+37) (Data y A)
    "conditioning.v" "graph.n" (List.ofFn (fun v => rationalValue y (insert v A))) [] read (by omega)
    (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hv ⟨i,by simpa using hi⟩).1.trans_lt hM)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hv ⟨i,by simpa using hi⟩).2.trans_lt hM)
    (fun σ h => by simpa only [List.length_ofFn] using h.2.2)
    (fun σ k h => by simpa only [Data,NativeMomentValue.Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [List.getElem_ofFn] using read_spec B M n r y A ⟨i,by simpa using hi⟩ hA hN (by omega) hm hM hy)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hd,hr⟩
  have r1:Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2:=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩:=hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide),
      by simp [Prefix],by simp,by simpa only [List.length_nil,List.length_ofFn,arrs_setVar,Nat.zero_add] using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeConditioningVector

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

namespace Lax263307Proofs.NativeQuadraticProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeCutRead

theorem row_spec (B n:ℕ) (i:Fin (n*n)) (hB:n*n+n+3< B):
    Spec B (fun σ => σ.vars "quadratic.i"=i.val∧ σ.vars "projection.n"=n) row
      (fun _ τ => τ.vars "cut.i"=(NativeBlowUp.row i).val) 4:=by
  have hn:0< n:=by nlinarith only [i.isLt]
  have hi:=i.isLt
  have hd:i.val/n< n:=(Nat.div_lt_iff_lt_mul hn).mpr hi
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "quadratic.i") (@Fin.val (Nat.mul n n) i)) (@Eq Nat (Env.vars σ "projection.n") n)) => let c0:Prop:= @Eq Nat (Env.vars σ "quadratic.i") (@Fin.val (Nat.mul n n) i); let c1:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "cut.i") (@Fin.val n (@NativeBlowUp.row n i))) σ; let c2:Env→ Prop:=fun (σ':Env) => And (Run B row σ σ' ((4:Nat))) (c1 σ'); let c3:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "quadratic.i") (Env.vars σ "projection.n"); let c4:Env:=Env.setVar σ "cut.i" c3; @And.casesOn c0 (@Eq Nat (Env.vars σ "projection.n") n) (fun (x:And c0 (@Eq Nat (Env.vars σ "projection.n") n)) => @Exists Env c2) a fun (left:c0) (right:@Eq Nat (Env.vars σ "projection.n") n) => @Exists.intro Env c2 c4 (@And.intro (Run B row σ c4 ((4:Nat))) (c1 c4) (RunStep.mono B row σ c4 (Nat.add ((1:Nat)) (Expr.size (Expr.div (Expr.var "quadratic.i") (Expr.var "projection.n")))) ((4:Nat)) (RunStep.assign B σ "cut.i" (Expr.div (Expr.var "quadratic.i") (Expr.var "projection.n")) c3 (RunStep.eval_div B σ (Expr.var "quadratic.i") (Expr.var "projection.n") (Env.vars σ "quadratic.i") (Env.vars σ "projection.n") (RunStep.eval_var B σ "quadratic.i" (?nAX_g8609_0_0_0)) (RunStep.eval_var B σ "projection.n" (?nAX_g8609_0_0_1)) ?_)) (?nAX_g8609_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8609_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8609_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8609_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeBlowUp.row]
  all_goals omega

theorem col_spec (B n:ℕ) (i:Fin (n*n)) (hB:n*n+n+3< B):
    Spec B (fun σ => σ.vars "quadratic.i"=i.val∧ σ.vars "projection.n"=n) col
      (fun _ τ => τ.vars "cut.i"=(NativeBlowUp.col i).val) 8:=by
  have hn:0< n:=by nlinarith only [i.isLt]
  have hi:=i.isLt
  have hd:i.val/n< n:=(Nat.div_lt_iff_lt_mul hn).mpr hi
  have hp:=Nat.div_mul_le_self i.val n
  have hm:i.val%n=i.val-(i.val/n)*n:=by
    exact Nat.mod_eq_sub_div_mul
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "quadratic.i") (@Fin.val (Nat.mul n n) i)) (@Eq Nat (Env.vars σ "projection.n") n)) => let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Prop:= @Eq Nat (Env.vars σ "quadratic.i") (@Fin.val (c0 n n) i); let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "cut.i") (@Fin.val n (@NativeBlowUp.col n i))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B col σ σ' ((8:Nat))) (c2 σ'); let c4:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "quadratic.i") (Env.vars σ "projection.n"); let c5:Nat:=c0 c4 (Env.vars σ "projection.n"); let c6:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "quadratic.i") c5; let c7:Env:=Env.setVar σ "cut.i" c6; let c8:Expr:=Expr.mul (Expr.div (Expr.var "quadratic.i") (Expr.var "projection.n")) (Expr.var "projection.n"); let c9:Expr:=Expr.sub (Expr.var "quadratic.i") c8; @And.casesOn c1 (@Eq Nat (Env.vars σ "projection.n") n) (fun (x:And c1 (@Eq Nat (Env.vars σ "projection.n") n)) => @Exists Env c3) a fun (left:c1) (right:@Eq Nat (Env.vars σ "projection.n") n) => @Exists.intro Env c3 c7 (@And.intro (Run B col σ c7 ((8:Nat))) (c2 c7) (RunStep.mono B col σ c7 (Nat.add ((1:Nat)) (Expr.size c9)) ((8:Nat)) (RunStep.assign B σ "cut.i" c9 c6 (RunStep.eval_sub B σ (Expr.var "quadratic.i") c8 (Env.vars σ "quadratic.i") c5 (RunStep.eval_var B σ "quadratic.i" (?nAX_g8610_0_0_0)) (RunStep.eval_mul B σ (Expr.div (Expr.var "quadratic.i") (Expr.var "projection.n")) (Expr.var "projection.n") c4 (Env.vars σ "projection.n") (RunStep.eval_div B σ (Expr.var "quadratic.i") (Expr.var "projection.n") (Env.vars σ "quadratic.i") (Env.vars σ "projection.n") (RunStep.eval_var B σ "quadratic.i" (?nAX_g8610_0_0_1)) (RunStep.eval_var B σ "projection.n" (?nAX_g8610_0_0_2)) ?_) (RunStep.eval_var B σ "projection.n" (?nAX_g8610_0_0_3)) ?_) (?nAX_g8610_0_0_4))) (?nAX_g8610_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8610_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8610_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8610_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8610_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8610_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8610_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeBlowUp.col]
  all_goals omega

theorem command_spec (B M n:ℕ) (a:Fin n→ ℚ) (i:Fin (n*n))
    (hB:2*M^2+3< B) (hs:n*n+3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Context a σ∧ σ.vars "quadratic.i"=i.val) command
      (fun _ τ => Context a τ∧ FractionOutput (a (NativeBlowUp.row i)*a (NativeBlowUp.col i)) τ)
      (36*(M^2).size+130):=by
  have h1:1< B:=by nlinarith
  have hM:M< B:=by nlinarith
  rintro σ ⟨hc,hi⟩
  obtain ⟨σ1,r1,p1⟩:=row_spec B n i (by omega) σ ⟨hi,hc.2⟩
  have hc1:Context a σ1:=by
    simpa only [Context,Prefix,r1.frame_arr "cut.source" (by decide),r1.frame_var "projection.n" (by decide)] using hc
  obtain ⟨σ2,r2,p2⟩:=NativeCutRead.command_spec B M n a (NativeBlowUp.row i) hM (by omega) ha σ1 ⟨hc1,p1⟩
  obtain ⟨σ3,r3,p3⟩:=save_spec B "left" (a (NativeBlowUp.row i)) h1
    ((ha _).1.trans_lt hM) ((ha _).2.trans_lt hM) (by decide) σ2 p2.2
  have r123:=r1.seq (r2.seq r3)
  have hc3:Context a σ3:=by
    simpa only [Context,Prefix,r123.frame_arr "cut.source" (by decide),r123.frame_var "projection.n" (by decide)] using hc
  obtain ⟨σ4,r4,p4⟩:=col_spec B n i (by omega) σ3
    ⟨(r123.frame_var "quadratic.i" (by decide)).trans hi,hc3.2⟩
  have hc4:Context a σ4:=by
    simpa only [Context,Prefix,r4.frame_arr "cut.source" (by decide),r4.frame_var "projection.n" (by decide)] using hc3
  obtain ⟨σ5,r5,p5⟩:=NativeCutRead.command_spec B M n a (NativeBlowUp.col i) hM (by omega) ha σ4 ⟨hc4,p4⟩
  obtain ⟨σ6,r6,p6⟩:=save_spec B "right" (a (NativeBlowUp.col i)) h1
    ((ha _).1.trans_lt hM) ((ha _).2.trans_lt hM) (by decide) σ5 p5.2
  have hleft:Stored "left" (a (NativeBlowUp.row i)) σ6:=by
    simpa only [Stored,String.reduceAppend,(r4.seq (r5.seq r6)).frame_var "left.s" (by decide),
      (r4.seq (r5.seq r6)).frame_var "left.n" (by decide),
      (r4.seq (r5.seq r6)).frame_var "left.d" (by decide)] using p3
  obtain ⟨τ,r7,p7⟩:=multiply_spec B M (a (NativeBlowUp.row i)) (a (NativeBlowUp.col i)) hB
    (ha _) (ha _) σ6 ⟨hleft,p6⟩
  have hden:((a (NativeBlowUp.row i)).den*(a (NativeBlowUp.col i)).den).size≤(M^2).size:=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul (ha (NativeBlowUp.row i)).2 (ha (NativeBlowUp.col i)).2])
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨τ,rr.mono (by omega),?_,p7⟩
  simpa only [Context,Prefix,rr.frame_arr "cut.source" (by decide),rr.frame_var "projection.n" (by decide)] using hc

end Lax263307Proofs.NativeQuadraticProduct

end

section

namespace Lax263307Proofs.NativeQuadraticTerms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic

def term {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a:Fin n→ ℚ) (i:Fin (n*n)):ℚ:=
  if G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i) then
    a (NativeBlowUp.row i)*a (NativeBlowUp.col i) else 0

def terms {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ):List ℚ:=
  List.ofFn (term G a)

theorem terms_sum {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ):
    (terms G a).sum=∑ u,∑ v,if G.Adj u v then a u*a v else 0:=by
  unfold terms
  rw [List.ofFn_mul,List.sum_flatten,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro u _
  dsimp only [Function.comp_def]
  rw [List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  have hn:0< n:=by have hu:=u.isLt; omega
  have hrow:NativeBlowUp.row ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=u:=by
    apply Fin.ext
    change (u.val*n+v.val)/n=u.val
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt,Nat.zero_add]
  have hcol:NativeBlowUp.col ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=v:=by
    apply Fin.ext
    simp [NativeBlowUp.col,Nat.mod_eq_of_lt v.isLt]
  simp only [term,hrow,hcol]

def Context {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ) (σ:Env):Prop:=
  NativeCutRead.Context a σ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a:Fin n→ ℚ) (i:Fin (n*n)) (hB:2*M^2+3< B) (hs:n*n+3*n+10< B)
    (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Context G a σ∧ σ.vars "quadratic.i"=i.val) command
      (fun _ τ => Context G a τ∧ FractionOutput (term G a i) τ) (36*(M^2).size+137):=by
  rintro σ ⟨hc,hi⟩
  have h1:1< B:=by nlinarith
  let edge:ℕ:=if G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i) then 1 else 0
  have heB:edge< B:=by dsimp [edge]; split_ifs <;> omega
  have hw:(NativeWeightReduction.adjacency G)[i.val]?=some edge:=
    NativeBlowUp.matrix_flat_coordinate (fun u v => if G.Adj u v then 1 else 0) i
  have hlen:i.val<(NativeWeightReduction.adjacency G).length:=by
    rw [NativeWeightReduction.adjacency_length]; exact i.isLt
  rw [List.getElem?_eq_getElem hlen] at hw
  have hg:=(hc.2 i.val hlen).trans hw
  let ν:=σ.setVar "quadratic.edge" edge
  have r1:Run B readEdge σ ν 3:=Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by have hh:=i.isLt; omega:i.val< B)⟩) hg heB)
  have hcν:NativeCutRead.Context a ν:=by
    simpa only [NativeCutRead.Context,Prefix,r1.frame_arr "cut.source" (by decide),
      r1.frame_var "projection.n" (by decide)] using hc.1
  have hiν:ν.vars "quadratic.i"=i.val:=(r1.frame_var "quadratic.i" (by decide)).trans hi
  by_cases he:G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i)
  · obtain ⟨τ,r2,p2⟩:=NativeQuadraticProduct.command_spec B M n a i hB hs ha ν ⟨hcν,hiν⟩
    have hcond:(Cond.eq (.var "quadratic.edge") (.lit 0)).evalB B ν=some false:=by
      have hval:ν.vars "quadratic.edge"=1:=by simp [ν,edge,he]
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hval.symm,hval ▸ h1⟩) (evalB_lit (by omega:0< B))]
      rfl
    have rr:=r1.seq (Run.ite_false (c:=RamFractionPrimitives.zero) hcond r2)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),⟨p2.1,?_⟩,?_⟩
    · simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hc.2
    · simpa only [term,if_pos he] using p2.2
  · obtain ⟨τ,r2,p2⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    have hcond:(Cond.eq (.var "quadratic.edge") (.lit 0)).evalB B ν=some true:=by
      have hval:ν.vars "quadratic.edge"=0:=by simp [ν,edge,he]
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hval.symm,hval ▸ (by omega:0< B)⟩) (evalB_lit (by omega:0< B))]
      rfl
    have rr:=r1.seq (Run.ite_true (d:=NativeQuadraticProduct.command) hcond r2)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,NativeCutRead.Context,Prefix,rr.frame_arr "cut.source" (by decide),
        rr.frame_arr "search.graph" (by decide),rr.frame_var "projection.n" (by decide)] using hc
    · simpa only [term,if_neg he] using p2

end Lax263307Proofs.NativeQuadraticTerms

end

section

namespace Lax263307Proofs.NativeQuadraticVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeQuadraticTerms

def Data {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ) (σ:Env):Prop:=
  Context G a σ∧ σ.vars "quadratic.count"=n*n

theorem frame {B n K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K) (hd:Data G a σ)
    (h0:"cut.source"∉c.warrs) (h1:"search.graph"∉c.warrs)
    (h2:"projection.n"∉c.wvars) (h3:"quadratic.count"∉c.wvars):Data G a τ:=by
  simpa only [Data,Context,NativeCutRead.Context,Prefix,rr.frame_arr "cut.source" h0,
    rr.frame_arr "search.graph" h1,rr.frame_var "projection.n" h2,rr.frame_var "quadratic.count" h3] using hd

theorem height (M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ)
    (hM:1≤ M) (ha:∀ j,Bounded M (a j)) (i:Fin (n*n)):Bounded (M^2) (term G a i):=by
  unfold term
  split_ifs
  · simpa only [pow_two] using NativeSumHeight.multiply M M _ _ (ha _) (ha _)
  · simp only [Bounded,Rat.num_zero,Int.natAbs_zero,Rat.den_zero]
    exact ⟨Nat.zero_le _,by nlinarith⟩

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ)
    (hM:1≤ M) (hB:2*M^2+3< B) (hs:3*(n*n)+3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Context G a σ∧ 3*(n*n)<(σ.arrs "lp.word").length) command
      (fun _ τ => Data G a τ∧ Prefix (NativeRationalTabulate.words (terms G a)) "lp.word" τ∧
        τ.vars "lp.position"=3*(n*n)) ((36*(M^2).size+172)*(n*n)+12):=by
  have h1:1< B:=by omega
  have hh:=RamVectorEncoding.command_spec B (36*(M^2).size+137) (Data G a)
    "quadratic.i" "quadratic.count" (terms G a) [] NativeQuadraticTerms.command h1
    (by simp [terms]; omega)
    (by intro i hi; simp only [terms,List.getElem_ofFn]; exact (height M n G a hM ha ⟨i,by simpa [terms] using hi⟩).1.trans_lt (by omega))
    (by intro i hi; simp only [terms,List.getElem_ofFn]; exact (height M n G a hM ha ⟨i,by simpa [terms] using hi⟩).2.trans_lt (by omega))
    (fun σ h => by simpa only [terms,List.length_ofFn] using h.2)
    (fun σ k h => by simpa only [Data,Context,NativeCutRead.Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by
      intro i hi σ hp
      obtain ⟨τ,rr,ht⟩:=NativeQuadraticTerms.command_spec B M n G a ⟨i,by simpa [terms] using hi⟩ hB (by omega) ha σ ⟨hp.1.1,hp.2⟩
      exact ⟨τ,rr,frame G a rr hp.1 (by decide) (by decide) (by decide) (by decide),
        by simpa only [terms,List.getElem_ofFn] using ht.2⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame G a rr h (by decide) (by decide) (by decide) (by decide)) (by decide)
  have hsetup:Spec B (fun σ => σ.vars "projection.n"=n) setup
      (fun _ τ => τ.vars "lp.position"=0∧ τ.vars "quadratic.count"=n*n) 6:=by
    (expose_names;
      (refine fun (σ:Env) (a_1:@Eq Nat (Env.vars σ "projection.n") n) => let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 n n; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.position") ((0:Nat))) (@Eq Nat (Env.vars τ "quadratic.count") c1)) σ; let c3:Env:=Env.setVar σ "lp.position" ((0:Nat)); let c4:Nat:=Env.vars c3 "projection.n"; let c5:Nat:=c0 c4 c4; let c6:Env:=Env.setVar c3 "quadratic.count" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c10:Nat:=c8 (Expr.size (Expr.mul (Expr.var "projection.n") (Expr.var "projection.n"))); let c11:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c2 σ')) c6 (@And.intro (Run B setup σ c6 ((6:Nat))) (c2 c6) (RunStep.mono B setup σ c6 (c7 c9 c10) ((6:Nat)) (RunStep.seq B (Com.assign "lp.position" (Expr.lit ((0:Nat)))) (Com.assign "quadratic.count" (Expr.mul (Expr.var "projection.n") (Expr.var "projection.n"))) σ c3 c6 c9 c10 (RunStep.assign B σ "lp.position" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8626_0_0_0))) (RunStep.assign B c3 "quadratic.count" (Expr.mul (Expr.var "projection.n") (Expr.var "projection.n")) c5 (RunStep.eval_mul B c3 (Expr.var "projection.n") (Expr.var "projection.n") c4 c4 (RunStep.eval_var B c3 "projection.n" (?nAX_g8626_0_0_1)) (RunStep.eval_var B c3 "projection.n" (?nAX_g8626_0_0_2)) ?_))) (?nAX_g8626_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8626_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8626_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8626_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8626_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hc,hr⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ hc.1.2
  have hdν:Data G a ν:=by
    refine ⟨?_,p1.2⟩
    simpa only [Context,NativeCutRead.Context,Prefix,r1.frame_arr "cut.source" (by decide),
      r1.frame_arr "search.graph" (by decide),r1.frame_var "projection.n" (by decide)] using hc
  obtain ⟨τ,r2,p2⟩:=hh ν ⟨hdν,by simp [Prefix],by simpa using p1.1,
    by simp only [terms,List.length_ofFn,List.length_nil,Nat.zero_add,RamFrames.run_array_length r1]; exact hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [terms,List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,NativeRationalTabulate.words] using p2.2.1
  · simpa only [List.length_nil,terms,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeQuadraticVector

end

section

namespace Lax263307Proofs.NativeQuadraticSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeQuadraticTerms

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (a:Fin n→ ℚ)
    (hM:1≤ M) (hB:2*M^2+3< B) (hH:2*(height M n)^2+3< B)
    (hs:3*(n*n)+3*n+10< B) (ha:∀ j,Bounded M (a j)):
    Spec B (fun σ => Context G a σ∧ 3*(n*n)<(σ.arrs "lp.word").length∧
      3*(n*n)≤(σ.arrs "sum.input").length) command
      (fun _ τ => Context G a τ∧
        RamRational.FractionOutput (∑ u,∑ v,if G.Adj u v then a u*a v else 0) τ)
      (cost M n):=by
  have hlen:(terms G a).length=n*n:=List.length_ofFn
  have hwlen:(NativeRationalTabulate.words (terms G a)).length=3*(n*n):=by
    rw [NativeRationalTabulate.words_length,hlen]
  have hterms:∀ x∈terms G a,Bounded (M^2) x:=by
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact NativeQuadraticVector.height M n G a hM ha i
  have hprepare:Spec B (fun σ => σ.vars "quadratic.count"=n*n) prepareSum
      (fun _ τ => τ.vars "slice.start"=0∧ τ.vars "fill.length"=3*(n*n)∧ τ.vars "sum.count"=n*n) 8:=by
    (expose_names;
      (refine fun (σ:Env) (a_1:@Eq Nat (Env.vars σ "quadratic.count") (Nat.mul n n)) => let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat→ Nat:=c0 ((3:Nat)); let c2:Nat:=c0 n n; let c3:Nat:=c1 c2; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))) (And (@Eq Nat (Env.vars τ "fill.length") c3) (@Eq Nat (Env.vars τ "sum.count") c2))) σ; let c5:Env:=Env.setVar σ "slice.start" ((0:Nat)); let c6:Nat:=Env.vars c5 "quadratic.count"; let c7:Nat:=c1 c6; let c8:Env:=Env.setVar c5 "fill.length" c7; let c9:Nat:=Env.vars c8 "quadratic.count"; let c10:Env:=Env.setVar c8 "sum.count" c9; let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c14:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "quadratic.count"); let c15:Nat:=c12 (Expr.size c14); let c16:Nat:=c12 (Expr.size (Expr.var "quadratic.count")); let c17:Nat:=c11 c15 c16; let c18:Com:=Com.assign "fill.length" c14; let c19:String→ Nat:=Env.vars c10; @Exists.intro Env (fun (σ':Env) => And (Run B prepareSum σ σ' ((8:Nat))) (c4 σ')) c10 (@And.intro (Run B prepareSum σ c10 ((8:Nat))) (c4 c10) (RunStep.mono B prepareSum σ c10 (c11 c13 c17) ((8:Nat)) (RunStep.seq B (Com.assign "slice.start" (Expr.lit ((0:Nat)))) (Com.seq c18 (Com.assign "sum.count" (Expr.var "quadratic.count"))) σ c5 c10 c13 c17 (RunStep.assign B σ "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8631_0_0_0))) (RunStep.seq B c18 (Com.assign "sum.count" (Expr.var "quadratic.count")) c5 c8 c10 c15 c16 (RunStep.assign B c5 "fill.length" c14 c7 (RunStep.eval_mul B c5 (Expr.lit ((3:Nat))) (Expr.var "quadratic.count") ((3:Nat)) c6 (RunStep.eval_lit B ((3:Nat)) c5 (?nAX_g8631_0_0_1)) (RunStep.eval_var B c5 "quadratic.count" (?nAX_g8631_0_0_2)) (?nAX_g8631_0_0_3))) (RunStep.assign B c8 "sum.count" (Expr.var "quadratic.count") c9 (RunStep.eval_var B c8 "quadratic.count" (?nAX_g8631_0_0_4))))) (?nAX_g8631_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8631_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8631_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8631_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8631_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8631_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8631_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  rintro σ ⟨hc,hO,hS⟩
  obtain ⟨ν,r1,p1⟩:=NativeQuadraticVector.command_spec B M n G a hM hB hs ha σ ⟨hc,hO⟩
  obtain ⟨μ,r2,p2⟩:=hprepare ν p1.1.2
  have hp:Prefix (NativeRationalTabulate.words (terms G a)) "lp.word" μ:=by
    simpa only [Prefix,r2.frame_arr "lp.word" (by decide)] using p1.2.1
  have hwords:∀ v∈NativeRationalTabulate.words (terms G a),v< B:=by
    simpa only [terms,NativeRationalTabulate.words,Lax109476.RationalEncoding.encodeVector] using
      NativeRationalBounds.vector_words B (M^2) (n*n) (term G a) (by omega) (by omega)
        (NativeQuadraticVector.height M n G a hM ha)
  obtain ⟨ξ,r3,p3⟩:=NativeSlice.command_spec B "lp.word" "sum.input" []
    (NativeRationalTabulate.words (terms G a)) [] (by decide)
    (by rw [List.length_nil,hwlen]; omega) hwords μ
    ⟨⟨by simpa using hp,by simpa using p2.1⟩,by simpa only [hwlen] using p2.2.1,
      by rw [hwlen,RamFrames.run_array_length (r1.seq r2)]; exact hS⟩
  have hcount:ξ.vars "sum.count"=(terms G a).length:=by
    rw [hlen]
    exact (r3.frame_var "sum.count" (by decide)).trans p2.2.2
  obtain ⟨τ,r4,p4⟩:=NativeSignedSum.bounded_spec B (M^2) (terms G a) (by nlinarith)
    (by simpa only [hlen,height] using hH) (by rw [hlen]; omega) hterms ξ ⟨p3.2,hcount⟩
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by rw [hwlen,hlen]; dsimp [cost,height]; nlinarith),?_,?_⟩
  · simpa only [Context,NativeCutRead.Context,Prefix,rr.frame_arr "cut.source" (by decide),
      rr.frame_arr "search.graph" (by decide),rr.frame_var "projection.n" (by decide)] using hc
  · simpa only [terms_sum] using p4.2

end Lax263307Proofs.NativeQuadraticSum

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeConditioningNumerator

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def extensions {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n)) (v:Fin n):ℚ:=
  rationalValue y (insert v A)

def Context {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (σ:Env):Prop:=
  NativeConditioningVector.Data y A σ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ

theorem frame {B n r K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hc:Context G y A σ)
    (h0:"catalog.mask"∉c.warrs) (h1:"near.moments"∉c.warrs) (h2:"search.graph"∉c.warrs)
    (h3:"catalog.count"∉c.wvars) (h4:"conditioning.mask"∉c.wvars) (h5:"graph.n"∉c.wvars):
    Context G y A τ:=by
  exact ⟨NativeConditioningVector.frame rr hc.1 h0 h1 h3 h4 h5,
    by simpa only [Prefix,rr.frame_arr "search.graph" h2] using hc.2⟩

theorem extensions_bounded (M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hA:A.card≤ r) (hy:∀ T,Bounded M (y T)) (v:Fin n):Bounded M (extensions y A v):=by
  have hh:(insert v A).card≤ r+2:=(Finset.card_insert_le v A).trans (by omega)
  simpa only [extensions,rationalValue,dif_pos hh] using hy ⟨insert v A,hh⟩

theorem prepare_spec (B M n r:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hA:A.card≤ r)
    (hN:3*N n r+10< B) (hn:3*n+3< B) (hm:2^n< B) (hM:M< B)
    (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Context G y A σ∧ 3*n<(σ.arrs "lp.word").length∧
      3*n≤(σ.arrs "cut.source").length) prepare
      (fun _ τ => Context G y A τ∧ NativeQuadraticTerms.Context G (extensions y A) τ)
      ((17*N n r+120)*n+22):=by
  have hlen:(encodeVector (extensions y A)).length=3*n:=by
    change (RamVectorEncoding.encode (List.ofFn (extensions y A))).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hprepare:Spec B (fun σ => σ.vars "graph.n"=n) prepareCopy
      (fun _ τ => τ.vars "projection.n"=n∧ τ.vars "slice.start"=0∧ τ.vars "fill.length"=3*n) 8:=by
    (expose_names;
      (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ "graph.n") n) => let c0:Nat→ Nat:=Nat.mul ((3:Nat)); let c1:Nat:=c0 n; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "projection.n") n) (And (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))) (@Eq Nat (Env.vars τ "fill.length") c1))) σ; let c3:Env:=Env.setVar (Env.setVar σ "projection.n" (Env.vars σ "graph.n")) "slice.start" ((0:Nat)); let c4:Nat:=Env.vars c3 "graph.n"; let c5:Nat:=c0 c4; let c6:Env:=Env.setVar c3 "fill.length" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.var "graph.n")); let c10:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c11:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "graph.n"); let c12:Nat:=c8 (Expr.size c11); let c13:Nat:=c7 c10 c12; let c14:Com:=Com.assign "slice.start" (Expr.lit ((0:Nat))); let c15:Com:=Com.assign "fill.length" c11; let c16:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (Run B prepareCopy σ σ' ((8:Nat))) (c2 σ')) c6 (@And.intro (Run B prepareCopy σ c6 ((8:Nat))) (c2 c6) (RunStep.mono B prepareCopy σ c6 (c7 c9 c13) ((8:Nat)) (RunStep.seq B (Com.assign "projection.n" (Expr.var "graph.n")) (Com.seq c14 c15) σ (Env.setVar σ "projection.n" (Env.vars σ "graph.n")) c6 c9 c13 (RunStep.assign B σ "projection.n" (Expr.var "graph.n") (Env.vars σ "graph.n") (RunStep.eval_var B σ "graph.n" (?nAX_g8640_0_0_0))) (RunStep.seq B c14 c15 (Env.setVar σ "projection.n" (Env.vars σ "graph.n")) c3 c6 c10 c12 (RunStep.assign B (Env.setVar σ "projection.n" (Env.vars σ "graph.n")) "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) (Env.setVar σ "projection.n" (Env.vars σ "graph.n")) (?nAX_g8640_0_0_1))) (RunStep.assign B c3 "fill.length" c11 c5 (RunStep.eval_mul B c3 (Expr.lit ((3:Nat))) (Expr.var "graph.n") ((3:Nat)) c4 (RunStep.eval_lit B ((3:Nat)) c3 (?nAX_g8640_0_0_2)) (RunStep.eval_var B c3 "graph.n" (?nAX_g8640_0_0_3)) (?nAX_g8640_0_0_4))))) (?nAX_g8640_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8640_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8640_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8640_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8640_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8640_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8640_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  rintro σ ⟨hc,hO,hC⟩
  obtain ⟨ν,r1,p1⟩:=NativeConditioningVector.command_spec B M n r y A hA hN hn hm hM hy σ ⟨hc.1,hO⟩
  obtain ⟨μ,r2,p2⟩:=hprepare ν p1.1.2.2
  have hp:Prefix (encodeVector (extensions y A)) "lp.word" μ:=by
    change Prefix (encodeVector (fun v => rationalValue y (insert v A))) "lp.word" μ
    simpa only [Prefix,r2.frame_arr "lp.word" (by decide)] using p1.2.1
  obtain ⟨τ,r3,p3⟩:=NativeSlice.command_spec B "lp.word" "cut.source" [] (encodeVector (extensions y A)) []
    (by decide) (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B M n (extensions y A) (by omega) hM (extensions_bounded M n r y A hA hy)) μ
    ⟨⟨by simpa using hp,by simpa using p2.2.1⟩,by simpa only [hlen] using p2.2.2,
      by rw [hlen,RamFrames.run_array_length (r1.seq r2)]; exact hC⟩
  have rr:=r1.seq (r2.seq r3)
  have ht:=frame G y A rr hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨τ,rr.mono (by rw [hlen]; nlinarith),ht,
    ⟨p3.2,(r3.frame_var "projection.n" (by decide)).trans p2.1⟩,ht.2⟩

theorem command_spec (B M n r:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hA:A.card≤ r) (hM:1≤ M)
    (hN:3*N n r+10< B) (hn:3*(n*n)+3*n+10< B) (hm:2^n< B)
    (hB:2*M^2+3< B) (hH:2*(NativeQuadraticSum.height M n)^2+3< B)
    (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Context G y A σ∧ 3*n+3*(n*n)<(σ.arrs "lp.word").length∧
      3*n≤(σ.arrs "cut.source").length∧ 3*(n*n)≤(σ.arrs "sum.input").length) command
      (fun _ τ => Context G y A τ∧ RamRational.FractionOutput (edgeNumerator G y A) τ)
      (cost M n r):=by
  rintro σ ⟨hc,hO,hC,hS⟩
  obtain ⟨ν,r1,p1⟩:=prepare_spec B M n r G y A hA hN (by omega) hm (by nlinarith) hy σ ⟨hc,by omega,hC⟩
  obtain ⟨τ,r2,p2⟩:=NativeQuadraticSum.command_spec B M n G (extensions y A) hM hB hH hn
    (extensions_bounded M n r y A hA hy) ν
    ⟨p1.2,by rw [RamFrames.run_array_length r1]; omega,by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,r1.seq r2,frame G y A r2 p1.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by simpa only [edgeNumerator,extensions] using p2.2⟩

end Lax263307Proofs.NativeConditioningNumerator

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

theorem command_spec (B n p r:ℕ) (hn:0< n) (hp:0< p)
    (hB:base n p+base n p^r+n+p+r+10< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "conditioning.p"=p∧ σ.vars "moment.r"=r) command
      (fun _ τ => τ.vars "conditioning.floorDen"=base n p^r) (12*n.size+12*r+28):=by
  have hb:1≤ base n p:=by change 0< base n p; dsimp [base]; positivity
  have hlog:1≤ n.size:=by rw [size_log n hn]; omega
  have hsize:n.size≤ n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hnp:2*n*p≤ base n p:=by
    dsimp [base]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hn2:2*n≤ base n p:=(Nat.le_mul_of_pos_right _ hp).trans hnp
  have hprep:Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "conditioning.p"=p∧
      σ.vars "moment.r"=r∧ σ.vars "size.count"=n.size) preparePower
      (fun _ τ => NativeNaturalPower.Context (base n p) r τ) 10:=by
    have hval:2*n*p*n.size=base n p:=by rw [size_log n hn]; rfl
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (And (@Eq Nat (Env.vars σ "conditioning.p") p) (And (@Eq Nat (Env.vars σ "moment.r") r) (@Eq Nat (Env.vars σ "size.count") (Nat.size n))))) => let c0:Prop:= @Eq Nat (Env.vars σ "size.count") (Nat.size n); let c1:Prop:=And (@Eq Nat (Env.vars σ "moment.r") r) c0; let c2:Prop:=And (@Eq Nat (Env.vars σ "conditioning.p") p) c1; let c3:Env→ Prop:=(fun (x τ:Env) => NativeNaturalPower.Context (base n p) r τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B preparePower σ σ' ((10:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat:=c6 ((2:Nat)) (Env.vars σ "graph.n"); let c8:Nat:=c6 c7 (Env.vars σ "conditioning.p"); let c9:Nat:=c6 c8 (Env.vars σ "size.count"); let c10:Env:=Env.setVar σ "power.base" c9; let c11:Nat:=Env.vars c10 "moment.r"; let c12:Env:=Env.setVar c10 "power.exponent" c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "graph.n"); let c16:Expr:=Expr.mul c15 (Expr.var "conditioning.p"); let c17:Expr:=Expr.mul c16 (Expr.var "size.count"); let c18:Nat:=c14 (Expr.size c17); let c19:Nat:=c14 (Expr.size (Expr.var "moment.r")); @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c2 (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c2) => c5) a fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c2) => @And.casesOn (@Eq Nat (Env.vars σ "conditioning.p") p) c1 (fun (x:c2) => c5) right fun (left_1:@Eq Nat (Env.vars σ "conditioning.p") p) (right_1:c1) => @And.casesOn (@Eq Nat (Env.vars σ "moment.r") r) c0 (fun (x:c1) => c5) right_1 fun (left_2:@Eq Nat (Env.vars σ "moment.r") r) (right_2:c0) => @Exists.intro Env c4 c12 (@And.intro (Run B preparePower σ c12 ((10:Nat))) (c3 c12) (RunStep.mono B preparePower σ c12 (c13 c18 c19) ((10:Nat)) (RunStep.seq B (Com.assign "power.base" c17) (Com.assign "power.exponent" (Expr.var "moment.r")) σ c10 c12 c18 c19 (RunStep.assign B σ "power.base" c17 c9 (RunStep.eval_mul B σ c16 (Expr.var "size.count") c8 (Env.vars σ "size.count") (RunStep.eval_mul B σ c15 (Expr.var "conditioning.p") c7 (Env.vars σ "conditioning.p") (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "graph.n") ((2:Nat)) (Env.vars σ "graph.n") (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8646_0_0_0)) (RunStep.eval_var B σ "graph.n" (?nAX_g8646_0_0_1)) (?nAX_g8646_0_0_2)) (RunStep.eval_var B σ "conditioning.p" (?nAX_g8646_0_0_3)) ?_) (RunStep.eval_var B σ "size.count" (?nAX_g8646_0_0_4)) ?_)) (RunStep.assign B c10 "power.exponent" (Expr.var "moment.r") c11 (RunStep.eval_var B c10 "moment.r" (?nAX_g8646_0_0_5)))) (?nAX_g8646_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8646_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8646_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8646_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8646_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8646_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8646_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8646_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [NativeNaturalPower.Context]
    all_goals omega
  rintro σ ⟨hN,hP,hR⟩
  let ν:=σ.setVar "size.value" n
  have r1:Run B (.assign "size.value" (.var "graph.n")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ (by omega:n< B)⟩)
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B n (by omega) (by omega) ν (by simp [ν])
  have r12:=r1.seq r2
  obtain ⟨ξ,r3,p3⟩:=hprep μ ⟨(r12.frame_var "graph.n" (by decide)).trans hN,
    (r12.frame_var "conditioning.p" (by decide)).trans hP,(r12.frame_var "moment.r" (by decide)).trans hR,p2.2⟩
  obtain ⟨υ,r4,p4⟩:=NativeNaturalPower.command_spec B (base n p) r hb (by omega) ξ p3
  let τ:=υ.setVar "conditioning.floorDen" (base n p^r)
  have r5:Run B (.assign "conditioning.floorDen" (.var "power.value")) υ τ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨p4.2.symm,p4.2 ▸ (by omega:base n p^r< B)⟩)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega),by simp [τ]⟩

theorem floor_value (n p r:ℕ):Lax263307.HeavyRationalConditioning.rationalFloor n p^r=
    1/(base n p^r:ℕ):=by
  simp only [Lax263307.HeavyRationalConditioning.rationalFloor,base,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one,Nat.cast_pow,one_div_pow]

end Lax263307Proofs.NativeConditioningFloor

end

section

namespace Lax263307Proofs.NativeConditioningPredicate

open Lax455465Proofs.RamRational

def Test (k p D:ℕ) (q e:ℚ):Prop:=
  0< q∧ (p:ℚ)*e≤2*(k:ℚ)^2*q^2∧ 1/(D:ℚ)≤ q

instance (k p D:ℕ) (q e:ℚ):Decidable (Test k p D q e):=
  inferInstanceAs (Decidable (0< q∧ (p:ℚ)*e≤2*(k:ℚ)^2*q^2∧ 1/(D:ℚ)≤ q))

def Numeric (k p D s n d t m e:ℕ):Prop:=
  s=0∧ 0< n∧ (t=1∨ p*m*d*d≤2*k*k*n*n*e)∧ d≤ D*n

instance (k p D s n d t m e:ℕ):Decidable (Numeric k p D s n d t m e):=
  inferInstanceAs (Decidable (s=0∧ 0< n∧ (t=1∨ p*m*d*d≤2*k*k*n*n*e)∧ d≤ D*n))

theorem positive (s n d:ℕ) (hs:s≤1) (hd:0< d):
    0< fractionValue s n d↔ s=0∧ 0< n:=by
  have hdq:(0:ℚ)< d:=by exact_mod_cast hd
  have hnq:(0:ℚ)≤ n:=Nat.cast_nonneg n
  have hc:s=0∨ s=1:=by omega
  rcases hc with rfl | rfl
  · simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false,true_and]
    rw [div_pos_iff_of_pos_right hdq]
    exact_mod_cast Iff.rfl
  · have hh:-(n:ℚ)/(d:ℚ)≤0:=div_nonpos_of_nonpos_of_nonneg (by linarith) hdq.le
    simp only [fractionValue,if_true,show ¬(1:ℕ)=0 by decide,false_and]
    exact iff_false_intro (not_lt_of_ge hh)

theorem numeric_iff (k p D s n d t m e:ℕ) (hs:s≤1) (ht:t≤1)
    (hd:0< d) (he:0< e) (hD:0< D):
    Numeric k p D s n d t m e↔ Test k p D (fractionValue s n d) (fractionValue t m e):=by
  have hdq:(0:ℚ)< d:=by exact_mod_cast hd
  have heq:(0:ℚ)< e:=by exact_mod_cast he
  have hDq:(0:ℚ)< D:=by exact_mod_cast hD
  by_cases hs0:s=0
  · subst s
    have hfloor:1/(D:ℚ)≤(n:ℚ)/d↔ d≤ D*n:=by
      rw [div_le_div_iff₀ hDq hdq]
      norm_cast
      simp [Nat.mul_comm]
    have hedge:(p:ℚ)*fractionValue t m e≤2*(k:ℚ)^2*((n:ℚ)/d)^2↔
        t=1∨ p*m*d*d≤2*k*k*n*n*e:=by
      have hc:t=0∨ t=1:=by omega
      rcases hc with rfl | rfl
      · simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false,false_or]
        rw [←mul_div_assoc,div_pow,←mul_div_assoc,div_le_div_iff₀ heq (sq_pos_of_pos hdq)]
        norm_cast
        simp only [pow_two,Nat.mul_assoc]
      · have hl:(p:ℚ)*fractionValue 1 m e≤0:=by
          simp only [fractionValue,if_true]
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p)
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) heq.le)
        have hr:(0:ℚ)≤2*(k:ℚ)^2*((n:ℚ)/d)^2:=by positivity
        simp only [true_or]
        exact iff_true_intro (hl.trans hr)
    simp only [Numeric,Test,positive 0 n d (by decide) hd,show (0:ℕ)=0 from rfl,true_and]
    rw [show fractionValue 0 n d=(n:ℚ)/d by simp [fractionValue],hedge,hfloor]
  · have hq:¬0< fractionValue s n d:=by rw [positive s n d hs hd]; simp [hs0]
    simp only [Numeric,Test,hs0,hq,false_and]

end Lax263307Proofs.NativeConditioningPredicate

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeConditioningTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational NativeSignedArithmetic NativeConditioningPredicate

def Input (k p D s n d t m e:ℕ) (σ:Env):Prop:=
  σ.vars "conditioning.k"=k∧ σ.vars "conditioning.p"=p∧ σ.vars "conditioning.floorDen"=D∧
  σ.vars "conditioning.a.s"=s∧ σ.vars "conditioning.a.n"=n∧ σ.vars "conditioning.a.d"=d∧
  σ.vars "conditioning.edge.s"=t∧ σ.vars "conditioning.edge.n"=m∧ σ.vars "conditioning.edge.d"=e

theorem command_spec (B k p D s n d t m e:ℕ) (hs:s≤1) (ht:t≤1)
    (hB:resource k p D n d m e< B):
    Spec B (Input k p D s n d t m e) command
      (fun _ τ => τ.vars "conditioning.passes"=if Numeric k p D s n d t m e then 1 else 0) 46:=by
  dsimp [resource] at hB
  (expose_names;
    (refine fun (σ:Env) (a:Input k p D s n d t m e σ) => let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n"); let c2:Nat:=c0 c1 (Env.vars σ "conditioning.a.d"); let c3:Nat:=c0 c2 (Env.vars σ "conditioning.a.d"); let c4:Env:=Env.setVar σ "conditioning.left" c3; let c5:String→ Nat:=Env.vars c4; let c6:Nat:=c5 "conditioning.k"; let c7:Nat:=c0 ((2:Nat)) c6; let c8:Nat:=c0 c7 c6; let c9:Nat:=c5 "conditioning.a.n"; let c10:Nat:=c0 c8 c9; let c11:Nat:=c0 c10 c9; let c12:Nat:=c5 "conditioning.edge.d"; let c13:Nat:=c0 c11 c12; let c14:Env:=Env.setVar c4 "conditioning.right" c13; let c15:String→ Nat:=Env.vars c14; let c16:Nat:=c15 "conditioning.floorDen"; let c17:Nat:=c15 "conditioning.a.n"; let c18:Nat:=c0 c16 c17; let c19:Env:=Env.setVar c14 "conditioning.floorProduct" c18; let c20:String→ Nat:=Env.vars c19; let c21:Nat:=c20 "conditioning.a.s"; let c22:Prop:= @Eq Nat c21 ((0:Nat)); let c23:Prop:=Not c22; let c24:Nat:= @ite Nat (Numeric k p D s n d t m e) (instDecidableNumeric k p D s n d t m e) ((1:Nat)) ((0:Nat)); let c25:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "conditioning.passes") c24) σ; let c26:Env→ Prop:=fun (σ':Env) => And (Run B command σ σ' ((46:Nat))) (c25 σ'); let c27:Prop:= @Exists Env c26; let c28:Nat:=c20 "conditioning.a.n"; let c29:Prop:=Nat.lt ((0:Nat)) c28; let c30:Prop:=Not c29; let c31:Nat:=c20 "conditioning.floorProduct"; let c32:Nat→ Prop:=Nat.lt c31; let c33:Nat:=c20 "conditioning.a.d"; let c34:Prop:=c32 c33; let c35:Prop:=Not c34; let c36:Nat→ Env:=Env.setVar c19 "conditioning.passes"; let c37:Env:=c36 ((0:Nat)); let c38:Nat→ Nat→ Nat:=Nat.add; let c39:Nat→ Nat:=c38 ((1:Nat)); let c40:Expr:=Expr.mul (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d"); let c41:Expr:=Expr.mul c40 (Expr.var "conditioning.a.d"); let c42:Nat:=c39 (Expr.size c41); let c43:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "conditioning.k"); let c44:Expr:=Expr.mul c43 (Expr.var "conditioning.k"); let c45:Expr:=Expr.mul c44 (Expr.var "conditioning.a.n"); let c46:Expr:=Expr.mul c45 (Expr.var "conditioning.a.n"); let c47:Expr:=Expr.mul c46 (Expr.var "conditioning.edge.d"); let c48:Nat:=c39 (Expr.size c47); let c49:Nat:=c39 (Expr.size (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n"))); let c50:Nat:=c38 c48 c49; let c51:Nat:=c38 c42 c50; let c52:Nat→ Nat:=c38 c51; let c53:Cond:=Cond.eq (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))); let c54:Nat→ Nat:=c38 (c39 (Cond.size c53)); let c55:Cond:=Cond.lt (Expr.lit ((0:Nat))) (Expr.var "conditioning.a.n"); let c56:Nat→ Nat:=c38 (c39 (Cond.size c55)); let c57:Nat→ Nat:=c38 (c39 (Cond.size (Cond.lt (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d")))); let c58:Nat:=c39 (Expr.size (Expr.lit ((0:Nat)))); let c59:Nat:=c57 c58; let c60:Nat:=c56 c59; let c61:Nat:=c54 c60; let c62:Com:=Com.assign "conditioning.right" c47; let c63:Com:=Com.assign "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")); let c64:Cond:=Cond.eq (Expr.var "conditioning.edge.s") (Expr.lit ((1:Nat))); let c65:Com:=Com.ite (Cond.lt (Expr.var "conditioning.right") (Expr.var "conditioning.left")) (answer ((0:Nat))) (answer ((1:Nat))); let c66:Com:=Com.ite c64 (answer ((1:Nat))) c65; let c67:Com:=Com.ite (Cond.lt (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d")) (answer ((0:Nat))) c66; let c68:Com:=Com.ite c55 c67 (answer ((0:Nat))); let c69:Nat:=c20 "conditioning.edge.s"; let c70:Prop:= @Eq Nat c69 ((1:Nat)); let c71:Prop:=Not c70; let c72:Env:=c36 ((1:Nat)); let c73:Nat→ Nat:=c38 (c39 (Cond.size c64)); let c74:Nat:=c39 (Expr.size (Expr.lit ((1:Nat)))); let c75:Nat:=c73 c74; let c76:Nat:=c57 c75; let c77:Nat:=c56 c76; let c78:Nat:=c54 c77; let c79:Nat:=c20 "conditioning.right"; let c80:Nat→ Prop:=Nat.lt c79; let c81:Nat:=c20 "conditioning.left"; let c82:Prop:=c80 c81; let c83:Prop:=Not c82; let c84:Nat→ Nat:=c38 (c39 (Cond.size (Cond.lt (Expr.var "conditioning.right") (Expr.var "conditioning.left")))); let c85:Nat:=c84 c58; let c86:Nat:=c73 c85; let c87:Nat:=c57 c86; let c88:Nat:=c56 c87; let c89:Nat:=c54 c88; let c90:Nat:=c84 c74; let c91:Nat:=c73 c90; let c92:Nat:=c57 c91; let c93:Nat:=c56 c92; let c94:Nat:=c54 c93; let c95:Nat:=c56 c58; let c96:Nat:=c54 c95; let c97:Nat:=c54 c58; @Or.casesOn c22 c23 (fun (x:Or c22 c23) => c27) (Classical.em c22) (fun (hcase:c22) => @Or.casesOn c29 c30 (fun (x:Or c29 c30) => c27) (Classical.em c29) (fun (hcase_1:c29) => @Or.casesOn c34 c35 (fun (x:Or c34 c35) => c27) (Classical.em c34) (fun (hcase_2:c34) => @Exists.intro Env c26 c37 (@And.intro (Run B command σ c37 ((46:Nat))) (c25 c37) (RunStep.mono B command σ c37 (c52 c61) ((46:Nat)) (RunStep.seq B products decideCommand σ c19 c37 c51 c61 (RunStep.seq B (Com.assign "conditioning.left" c41) (Com.seq c62 c63) σ c4 c19 c42 c50 (RunStep.assign B σ "conditioning.left" c41 c3 (RunStep.eval_mul B σ c40 (Expr.var "conditioning.a.d") c2 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d") c1 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n") (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n") (RunStep.eval_var B σ "conditioning.p" ?_) (RunStep.eval_var B σ "conditioning.edge.n" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_)) (RunStep.seq B c62 c63 c4 c14 c19 c48 c49 (RunStep.assign B c4 "conditioning.right" c47 c13 (RunStep.eval_mul B c4 c46 (Expr.var "conditioning.edge.d") c11 c12 (RunStep.eval_mul B c4 c45 (Expr.var "conditioning.a.n") c10 c9 (RunStep.eval_mul B c4 c44 (Expr.var "conditioning.a.n") c8 c9 (RunStep.eval_mul B c4 c43 (Expr.var "conditioning.k") c7 c6 (RunStep.eval_mul B c4 (Expr.lit ((2:Nat))) (Expr.var "conditioning.k") ((2:Nat)) c6 (RunStep.eval_lit B ((2:Nat)) c4 (?nAX_g8660_0_0_0)) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.edge.d" ?_) ?_)) (RunStep.assign B c14 "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")) c18 (RunStep.eval_mul B c14 (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n") c16 c17 (RunStep.eval_var B c14 "conditioning.floorDen" ?_) (RunStep.eval_var B c14 "conditioning.a.n" ?_) ?_)))) (RunStep.ite_true B c53 c68 (answer ((0:Nat))) c19 c37 c60 (RunStep.cond_eq_true B c19 (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))) c21 ((0:Nat)) (RunStep.eval_var B c19 "conditioning.a.s" ?_) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_1)) hcase) (RunStep.ite_true B c55 c67 (answer ((0:Nat))) c19 c37 c59 (RunStep.cond_lt_true B c19 (Expr.lit ((0:Nat))) (Expr.var "conditioning.a.n") ((0:Nat)) c28 (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_2)) (RunStep.eval_var B c19 "conditioning.a.n" ?_) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d")) (answer ((0:Nat))) c66 c19 c37 c58 (RunStep.cond_lt_true B c19 (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d") c31 c33 (RunStep.eval_var B c19 "conditioning.floorProduct" ?_) (RunStep.eval_var B c19 "conditioning.a.d" ?_) hcase_2) (RunStep.assign B c19 "conditioning.passes" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_3))))))) (?nAX_g8660_0_0_4)) ?_)) fun (hcase_2:c35) => @Or.casesOn c70 c71 (fun (x:Or c70 c71) => c27) (Classical.em c70) (fun (hcase_3:c70) => @Exists.intro Env c26 c72 (@And.intro (Run B command σ c72 ((46:Nat))) (c25 c72) (RunStep.mono B command σ c72 (c52 c78) ((46:Nat)) (RunStep.seq B products decideCommand σ c19 c72 c51 c78 (RunStep.seq B (Com.assign "conditioning.left" c41) (Com.seq c62 c63) σ c4 c19 c42 c50 (RunStep.assign B σ "conditioning.left" c41 c3 (RunStep.eval_mul B σ c40 (Expr.var "conditioning.a.d") c2 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d") c1 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n") (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n") (RunStep.eval_var B σ "conditioning.p" ?_) (RunStep.eval_var B σ "conditioning.edge.n" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_)) (RunStep.seq B c62 c63 c4 c14 c19 c48 c49 (RunStep.assign B c4 "conditioning.right" c47 c13 (RunStep.eval_mul B c4 c46 (Expr.var "conditioning.edge.d") c11 c12 (RunStep.eval_mul B c4 c45 (Expr.var "conditioning.a.n") c10 c9 (RunStep.eval_mul B c4 c44 (Expr.var "conditioning.a.n") c8 c9 (RunStep.eval_mul B c4 c43 (Expr.var "conditioning.k") c7 c6 (RunStep.eval_mul B c4 (Expr.lit ((2:Nat))) (Expr.var "conditioning.k") ((2:Nat)) c6 (RunStep.eval_lit B ((2:Nat)) c4 (?nAX_g8660_0_0_5)) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.edge.d" ?_) ?_)) (RunStep.assign B c14 "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")) c18 (RunStep.eval_mul B c14 (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n") c16 c17 (RunStep.eval_var B c14 "conditioning.floorDen" ?_) (RunStep.eval_var B c14 "conditioning.a.n" ?_) ?_)))) (RunStep.ite_true B c53 c68 (answer ((0:Nat))) c19 c72 c77 (RunStep.cond_eq_true B c19 (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))) c21 ((0:Nat)) (RunStep.eval_var B c19 "conditioning.a.s" ?_) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_6)) hcase) (RunStep.ite_true B c55 c67 (answer ((0:Nat))) c19 c72 c76 (RunStep.cond_lt_true B c19 (Expr.lit ((0:Nat))) (Expr.var "conditioning.a.n") ((0:Nat)) c28 (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_7)) (RunStep.eval_var B c19 "conditioning.a.n" ?_) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d")) (answer ((0:Nat))) c66 c19 c72 c75 (RunStep.cond_lt_false B c19 (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d") c31 c33 (RunStep.eval_var B c19 "conditioning.floorProduct" ?_) (RunStep.eval_var B c19 "conditioning.a.d" ?_) hcase_2) (RunStep.ite_true B c64 (answer ((1:Nat))) c65 c19 c72 c74 (RunStep.cond_eq_true B c19 (Expr.var "conditioning.edge.s") (Expr.lit ((1:Nat))) c69 ((1:Nat)) (RunStep.eval_var B c19 "conditioning.edge.s" ?_) (RunStep.eval_lit B ((1:Nat)) c19 (?nAX_g8660_0_0_8)) hcase_3) (RunStep.assign B c19 "conditioning.passes" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c19 (?nAX_g8660_0_0_9)))))))) (?nAX_g8660_0_0_10)) ?_)) fun (hcase_3:c71) => @Or.casesOn c82 c83 (fun (x:Or c82 c83) => c27) (Classical.em c82) (fun (hcase_4:c82) => @Exists.intro Env c26 c37 (@And.intro (Run B command σ c37 ((46:Nat))) (c25 c37) (RunStep.mono B command σ c37 (c52 c89) ((46:Nat)) (RunStep.seq B products decideCommand σ c19 c37 c51 c89 (RunStep.seq B (Com.assign "conditioning.left" c41) (Com.seq c62 c63) σ c4 c19 c42 c50 (RunStep.assign B σ "conditioning.left" c41 c3 (RunStep.eval_mul B σ c40 (Expr.var "conditioning.a.d") c2 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d") c1 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n") (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n") (RunStep.eval_var B σ "conditioning.p" ?_) (RunStep.eval_var B σ "conditioning.edge.n" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_)) (RunStep.seq B c62 c63 c4 c14 c19 c48 c49 (RunStep.assign B c4 "conditioning.right" c47 c13 (RunStep.eval_mul B c4 c46 (Expr.var "conditioning.edge.d") c11 c12 (RunStep.eval_mul B c4 c45 (Expr.var "conditioning.a.n") c10 c9 (RunStep.eval_mul B c4 c44 (Expr.var "conditioning.a.n") c8 c9 (RunStep.eval_mul B c4 c43 (Expr.var "conditioning.k") c7 c6 (RunStep.eval_mul B c4 (Expr.lit ((2:Nat))) (Expr.var "conditioning.k") ((2:Nat)) c6 (RunStep.eval_lit B ((2:Nat)) c4 (?nAX_g8660_0_0_11)) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.edge.d" ?_) ?_)) (RunStep.assign B c14 "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")) c18 (RunStep.eval_mul B c14 (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n") c16 c17 (RunStep.eval_var B c14 "conditioning.floorDen" ?_) (RunStep.eval_var B c14 "conditioning.a.n" ?_) ?_)))) (RunStep.ite_true B c53 c68 (answer ((0:Nat))) c19 c37 c88 (RunStep.cond_eq_true B c19 (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))) c21 ((0:Nat)) (RunStep.eval_var B c19 "conditioning.a.s" ?_) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_12)) hcase) (RunStep.ite_true B c55 c67 (answer ((0:Nat))) c19 c37 c87 (RunStep.cond_lt_true B c19 (Expr.lit ((0:Nat))) (Expr.var "conditioning.a.n") ((0:Nat)) c28 (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_13)) (RunStep.eval_var B c19 "conditioning.a.n" ?_) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d")) (answer ((0:Nat))) c66 c19 c37 c86 (RunStep.cond_lt_false B c19 (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d") c31 c33 (RunStep.eval_var B c19 "conditioning.floorProduct" ?_) (RunStep.eval_var B c19 "conditioning.a.d" ?_) hcase_2) (RunStep.ite_false B c64 (answer ((1:Nat))) c65 c19 c37 c85 (RunStep.cond_eq_false B c19 (Expr.var "conditioning.edge.s") (Expr.lit ((1:Nat))) c69 ((1:Nat)) (RunStep.eval_var B c19 "conditioning.edge.s" ?_) (RunStep.eval_lit B ((1:Nat)) c19 (?nAX_g8660_0_0_14)) hcase_3) (RunStep.ite_true B (Cond.lt (Expr.var "conditioning.right") (Expr.var "conditioning.left")) (answer ((0:Nat))) (answer ((1:Nat))) c19 c37 c58 (RunStep.cond_lt_true B c19 (Expr.var "conditioning.right") (Expr.var "conditioning.left") c79 c81 (RunStep.eval_var B c19 "conditioning.right" ?_) (RunStep.eval_var B c19 "conditioning.left" ?_) hcase_4) (RunStep.assign B c19 "conditioning.passes" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_15))))))))) (?nAX_g8660_0_0_16)) ?_)) fun (hcase_4:c83) => @Exists.intro Env c26 c72 (@And.intro (Run B command σ c72 ((46:Nat))) (c25 c72) (RunStep.mono B command σ c72 (c52 c94) ((46:Nat)) (RunStep.seq B products decideCommand σ c19 c72 c51 c94 (RunStep.seq B (Com.assign "conditioning.left" c41) (Com.seq c62 c63) σ c4 c19 c42 c50 (RunStep.assign B σ "conditioning.left" c41 c3 (RunStep.eval_mul B σ c40 (Expr.var "conditioning.a.d") c2 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d") c1 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n") (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n") (RunStep.eval_var B σ "conditioning.p" ?_) (RunStep.eval_var B σ "conditioning.edge.n" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_)) (RunStep.seq B c62 c63 c4 c14 c19 c48 c49 (RunStep.assign B c4 "conditioning.right" c47 c13 (RunStep.eval_mul B c4 c46 (Expr.var "conditioning.edge.d") c11 c12 (RunStep.eval_mul B c4 c45 (Expr.var "conditioning.a.n") c10 c9 (RunStep.eval_mul B c4 c44 (Expr.var "conditioning.a.n") c8 c9 (RunStep.eval_mul B c4 c43 (Expr.var "conditioning.k") c7 c6 (RunStep.eval_mul B c4 (Expr.lit ((2:Nat))) (Expr.var "conditioning.k") ((2:Nat)) c6 (RunStep.eval_lit B ((2:Nat)) c4 (?nAX_g8660_0_0_17)) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.edge.d" ?_) ?_)) (RunStep.assign B c14 "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")) c18 (RunStep.eval_mul B c14 (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n") c16 c17 (RunStep.eval_var B c14 "conditioning.floorDen" ?_) (RunStep.eval_var B c14 "conditioning.a.n" ?_) ?_)))) (RunStep.ite_true B c53 c68 (answer ((0:Nat))) c19 c72 c93 (RunStep.cond_eq_true B c19 (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))) c21 ((0:Nat)) (RunStep.eval_var B c19 "conditioning.a.s" ?_) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_18)) hcase) (RunStep.ite_true B c55 c67 (answer ((0:Nat))) c19 c72 c92 (RunStep.cond_lt_true B c19 (Expr.lit ((0:Nat))) (Expr.var "conditioning.a.n") ((0:Nat)) c28 (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_19)) (RunStep.eval_var B c19 "conditioning.a.n" ?_) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d")) (answer ((0:Nat))) c66 c19 c72 c91 (RunStep.cond_lt_false B c19 (Expr.var "conditioning.floorProduct") (Expr.var "conditioning.a.d") c31 c33 (RunStep.eval_var B c19 "conditioning.floorProduct" ?_) (RunStep.eval_var B c19 "conditioning.a.d" ?_) hcase_2) (RunStep.ite_false B c64 (answer ((1:Nat))) c65 c19 c72 c90 (RunStep.cond_eq_false B c19 (Expr.var "conditioning.edge.s") (Expr.lit ((1:Nat))) c69 ((1:Nat)) (RunStep.eval_var B c19 "conditioning.edge.s" ?_) (RunStep.eval_lit B ((1:Nat)) c19 (?nAX_g8660_0_0_20)) hcase_3) (RunStep.ite_false B (Cond.lt (Expr.var "conditioning.right") (Expr.var "conditioning.left")) (answer ((0:Nat))) (answer ((1:Nat))) c19 c72 c74 (RunStep.cond_lt_false B c19 (Expr.var "conditioning.right") (Expr.var "conditioning.left") c79 c81 (RunStep.eval_var B c19 "conditioning.right" ?_) (RunStep.eval_var B c19 "conditioning.left" ?_) hcase_4) (RunStep.assign B c19 "conditioning.passes" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c19 (?nAX_g8660_0_0_21))))))))) (?nAX_g8660_0_0_22)) ?_)) fun (hcase_1:c30) => @Exists.intro Env c26 c37 (@And.intro (Run B command σ c37 ((46:Nat))) (c25 c37) (RunStep.mono B command σ c37 (c52 c96) ((46:Nat)) (RunStep.seq B products decideCommand σ c19 c37 c51 c96 (RunStep.seq B (Com.assign "conditioning.left" c41) (Com.seq c62 c63) σ c4 c19 c42 c50 (RunStep.assign B σ "conditioning.left" c41 c3 (RunStep.eval_mul B σ c40 (Expr.var "conditioning.a.d") c2 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d") c1 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n") (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n") (RunStep.eval_var B σ "conditioning.p" ?_) (RunStep.eval_var B σ "conditioning.edge.n" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_)) (RunStep.seq B c62 c63 c4 c14 c19 c48 c49 (RunStep.assign B c4 "conditioning.right" c47 c13 (RunStep.eval_mul B c4 c46 (Expr.var "conditioning.edge.d") c11 c12 (RunStep.eval_mul B c4 c45 (Expr.var "conditioning.a.n") c10 c9 (RunStep.eval_mul B c4 c44 (Expr.var "conditioning.a.n") c8 c9 (RunStep.eval_mul B c4 c43 (Expr.var "conditioning.k") c7 c6 (RunStep.eval_mul B c4 (Expr.lit ((2:Nat))) (Expr.var "conditioning.k") ((2:Nat)) c6 (RunStep.eval_lit B ((2:Nat)) c4 (?nAX_g8660_0_0_23)) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.edge.d" ?_) ?_)) (RunStep.assign B c14 "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")) c18 (RunStep.eval_mul B c14 (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n") c16 c17 (RunStep.eval_var B c14 "conditioning.floorDen" ?_) (RunStep.eval_var B c14 "conditioning.a.n" ?_) ?_)))) (RunStep.ite_true B c53 c68 (answer ((0:Nat))) c19 c37 c95 (RunStep.cond_eq_true B c19 (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))) c21 ((0:Nat)) (RunStep.eval_var B c19 "conditioning.a.s" ?_) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_24)) hcase) (RunStep.ite_false B c55 c67 (answer ((0:Nat))) c19 c37 c58 (RunStep.cond_lt_false B c19 (Expr.lit ((0:Nat))) (Expr.var "conditioning.a.n") ((0:Nat)) c28 (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_25)) (RunStep.eval_var B c19 "conditioning.a.n" ?_) hcase_1) (RunStep.assign B c19 "conditioning.passes" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_26)))))) (?nAX_g8660_0_0_27)) ?_)) fun (hcase:c23) => @Exists.intro Env c26 c37 (@And.intro (Run B command σ c37 ((46:Nat))) (c25 c37) (RunStep.mono B command σ c37 (c52 c97) ((46:Nat)) (RunStep.seq B products decideCommand σ c19 c37 c51 c97 (RunStep.seq B (Com.assign "conditioning.left" c41) (Com.seq c62 c63) σ c4 c19 c42 c50 (RunStep.assign B σ "conditioning.left" c41 c3 (RunStep.eval_mul B σ c40 (Expr.var "conditioning.a.d") c2 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.mul (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n")) (Expr.var "conditioning.a.d") c1 (Env.vars σ "conditioning.a.d") (RunStep.eval_mul B σ (Expr.var "conditioning.p") (Expr.var "conditioning.edge.n") (Env.vars σ "conditioning.p") (Env.vars σ "conditioning.edge.n") (RunStep.eval_var B σ "conditioning.p" ?_) (RunStep.eval_var B σ "conditioning.edge.n" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_) (RunStep.eval_var B σ "conditioning.a.d" ?_) ?_)) (RunStep.seq B c62 c63 c4 c14 c19 c48 c49 (RunStep.assign B c4 "conditioning.right" c47 c13 (RunStep.eval_mul B c4 c46 (Expr.var "conditioning.edge.d") c11 c12 (RunStep.eval_mul B c4 c45 (Expr.var "conditioning.a.n") c10 c9 (RunStep.eval_mul B c4 c44 (Expr.var "conditioning.a.n") c8 c9 (RunStep.eval_mul B c4 c43 (Expr.var "conditioning.k") c7 c6 (RunStep.eval_mul B c4 (Expr.lit ((2:Nat))) (Expr.var "conditioning.k") ((2:Nat)) c6 (RunStep.eval_lit B ((2:Nat)) c4 (?nAX_g8660_0_0_28)) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.k" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.a.n" ?_) ?_) (RunStep.eval_var B c4 "conditioning.edge.d" ?_) ?_)) (RunStep.assign B c14 "conditioning.floorProduct" (Expr.mul (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n")) c18 (RunStep.eval_mul B c14 (Expr.var "conditioning.floorDen") (Expr.var "conditioning.a.n") c16 c17 (RunStep.eval_var B c14 "conditioning.floorDen" ?_) (RunStep.eval_var B c14 "conditioning.a.n" ?_) ?_)))) (RunStep.ite_false B c53 c68 (answer ((0:Nat))) c19 c37 c58 (RunStep.cond_eq_false B c19 (Expr.var "conditioning.a.s") (Expr.lit ((0:Nat))) c21 ((0:Nat)) (RunStep.eval_var B c19 "conditioning.a.s" ?_) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_29)) hcase) (RunStep.assign B c19 "conditioning.passes" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g8660_0_0_30))))) (?nAX_g8660_0_0_31)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8660_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8660_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Input,Numeric]
  all_goals first | omega | (split_ifs at * <;> omega)

theorem stored_spec (B k p D:ℕ) (q e:ℚ) (hD:0< D)
    (hB:resource k p D q.num.natAbs q.den e.num.natAbs e.den< B):
    Spec B (fun σ => σ.vars "conditioning.k"=k∧ σ.vars "conditioning.p"=p∧
      σ.vars "conditioning.floorDen"=D∧ Stored "conditioning.a" q σ∧ Stored "conditioning.edge" e σ)
      command (fun _ τ => τ.vars "conditioning.passes"=if Test k p D q e then 1 else 0) 46:=by
  rintro σ ⟨hk,hp,hd,hq,he⟩
  have hq':=hq
  have he':=he
  simp only [Stored,String.reduceAppend] at hq' he'
  obtain ⟨τ,rr,ht⟩:=command_spec B k p D (σ.vars "conditioning.a.s") q.num.natAbs q.den
    (σ.vars "conditioning.edge.s") e.num.natAbs e.den hq'.2.2.2 he'.2.2.2 hB σ
    ⟨hk,hp,hd,rfl,hq'.2.1,hq'.2.2.1,rfl,he'.2.1,he'.2.2.1⟩
  have hi:=numeric_iff k p D (σ.vars "conditioning.a.s") q.num.natAbs q.den
    (σ.vars "conditioning.edge.s") e.num.natAbs e.den hq'.2.2.2 he'.2.2.2 q.den_pos e.den_pos hD
  have hvq:fractionValue (σ.vars "conditioning.a.s") q.num.natAbs q.den=q:=by
    simpa only [←hq'.2.1,←hq'.2.2.1] using hq'.1
  have hve:fractionValue (σ.vars "conditioning.edge.s") e.num.natAbs e.den=e:=by
    simpa only [←he'.2.1,←he'.2.2.1] using he'.1
  rw [hvq,hve] at hi
  exact ⟨τ,rr,by simpa only [hi] using ht⟩

end Lax263307Proofs.NativeConditioningTest

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeHeavyCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata NativeConditioningNumerator

theorem edge_bounded (M n r:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hM:1≤ M) (hA:A.card≤ r)
    (hy:∀ T,Bounded M (y T)):Bounded (NativeQuadraticSum.height M n) (edgeNumerator G y A):=by
  have hext:=extensions_bounded M n r y A hA hy
  have hterms:∀ q∈NativeQuadraticTerms.terms G (extensions y A),Bounded (M^2) q:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact NativeQuadraticVector.height M n G (extensions y A) hM hext i
  have hlen:(NativeQuadraticTerms.terms G (extensions y A)).length=n*n:=List.length_ofFn
  have hh:=NativeSumHeight.uniform_partial (M^2) (NativeQuadraticTerms.terms G (extensions y A))
    (by nlinarith) hterms (NativeQuadraticTerms.terms G (extensions y A)).length
  rw [List.take_length] at hh
  simpa only [hlen,NativeQuadraticTerms.terms_sum,NativeQuadraticSum.height,
    extensions,edgeNumerator] using hh

theorem command_spec (B M n r k p:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hn:0< n) (hp:0< p)
    (hA:A.card≤ r) (hM:1≤ M) (hN:3*N n r+10< B) (hs:3*(n*n)+3*n+10< B)
    (hm:2^n< B) (hB:2*M^2+3< B) (hH:2*(NativeQuadraticSum.height M n)^2+3< B)
    (hy:∀ T,Bounded M (y T))
    (htest:NativeConditioningTest.resource k p (NativeConditioningFloor.base n p^r)
      (rationalValue y A).num.natAbs (rationalValue y A).den
      (edgeNumerator G y A).num.natAbs (edgeNumerator G y A).den< B):
    Spec B (fun σ => Context G y A σ∧ σ.vars "conditioning.k"=k∧ σ.vars "conditioning.p"=p∧
      σ.vars "conditioning.floorDen"=NativeConditioningFloor.base n p^r∧
      3*n+3*(n*n)<(σ.arrs "lp.word").length∧ 3*n≤(σ.arrs "cut.source").length∧
      3*(n*n)≤(σ.arrs "sum.input").length) command
      (fun _ τ => Context G y A τ∧
        τ.vars "conditioning.passes"=if HeavyPasses G k p y A then 1 else 0) (cost M n r):=by
  have h1:1< B:=by nlinarith
  have hMB:M< B:=by nlinarith
  have hHB:NativeQuadraticSum.height M n< B:=by nlinarith
  have hq:Bounded M (rationalValue y A):=by
    have hh:A.card≤ r+2:=by omega
    simpa only [rationalValue,dif_pos hh] using hy ⟨A,hh⟩
  have he:=edge_bounded M n r G y A hM hA hy
  have hD:0< NativeConditioningFloor.base n p^r:=by dsimp [NativeConditioningFloor.base]; positivity
  rintro σ ⟨hc,hk,hpσ,hDσ,hO,hC,hS⟩
  let σ1:=σ.setVar "lookup.key" (NativeMasks.mask A)
  have r1:Run B (.assign "lookup.key" (.var "conditioning.mask")) σ σ1 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.1.2.1.symm,hc.1.2.1 ▸ (NativeMasks.mask_bound A).trans hm⟩)
  have hc1:=frame G y A r1 hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩:=NativeMomentValue.command_spec B M n r y A (by omega) hN hm hMB hy σ1
    ⟨hc1.1.1,by simp [σ1]⟩
  obtain ⟨σ3,r3,p3⟩:=save_spec B "conditioning.a" (rationalValue y A) h1
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) (by decide) σ2 p2.2
  have r123:=r1.seq (r2.seq r3)
  have hc3:=frame G y A r123 hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ4,r4,p4⟩:=NativeConditioningNumerator.command_spec B M n r G y A hA hM hN hs hm hB hH hy σ3
    ⟨hc3,by rwa [RamFrames.run_array_length r123],by rwa [RamFrames.run_array_length r123],
      by rwa [RamFrames.run_array_length r123]⟩
  obtain ⟨σ5,r5,p5⟩:=save_spec B "conditioning.edge" (edgeNumerator G y A) h1
    (he.1.trans_lt hHB) (he.2.trans_lt hHB) (by decide) σ4 p4.2
  have hq5:Stored "conditioning.a" (rationalValue y A) σ5:=by
    simpa only [Stored,String.reduceAppend,(r4.seq r5).frame_var "conditioning.a.s" (by decide),
      (r4.seq r5).frame_var "conditioning.a.n" (by decide),
      (r4.seq r5).frame_var "conditioning.a.d" (by decide)] using p3
  have r12345:=r123.seq (r4.seq r5)
  obtain ⟨τ,r6,p6⟩:=NativeConditioningTest.stored_spec B k p (NativeConditioningFloor.base n p^r)
    (rationalValue y A) (edgeNumerator G y A) hD htest σ5
    ⟨(r12345.frame_var "conditioning.k" (by decide)).trans hk,
      (r12345.frame_var "conditioning.p" (by decide)).trans hpσ,
      (r12345.frame_var "conditioning.floorDen" (by decide)).trans hDσ,hq5,p5⟩
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have hpred:NativeConditioningPredicate.Test k p (NativeConditioningFloor.base n p^r)
      (rationalValue y A) (edgeNumerator G y A)↔ HeavyPasses G k p y A:=by
    simp only [NativeConditioningPredicate.Test,HeavyPasses,Passes,NativeConditioningFloor.floor_value]
    tauto
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),
    frame G y A rr hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by simpa only [hpred] using p6⟩

end Lax263307Proofs.NativeHeavyCandidate

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeConditioningResources

open Lax263307 RationalConditioning NativeSignedArithmetic

theorem test_le (k p D M H:ℕ) (q e:ℚ) (hq:Bounded M q) (he:Bounded H e):
    NativeConditioningTest.resource k p D q.num.natAbs q.den e.num.natAbs e.den≤ testBound k p D M H:=by
  dsimp [testBound,NativeConditioningTest.resource]
  gcongr <;> first | exact hq.1 | exact hq.2 | exact he.1 | exact he.2

theorem candidate_test (M n r k p:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hM:1≤ M) (hA:A.card≤ r)
    (hy:∀ T,Bounded M (y T)):
    NativeConditioningTest.resource k p (NativeConditioningFloor.base n p^r)
      (rationalValue y A).num.natAbs (rationalValue y A).den
      (edgeNumerator G y A).num.natAbs (edgeNumerator G y A).den≤
      testBound k p (NativeConditioningFloor.base n p^r) M (NativeQuadraticSum.height M n):=by
  apply test_le
  · have hh:A.card≤ r+2:=by omega
    simpa only [rationalValue,dif_pos hh] using hy ⟨A,hh⟩
  · exact NativeHeavyCandidate.edge_bounded M n r G y A hM hA hy

end Lax263307Proofs.NativeConditioningResources

end

section

namespace Lax263307Proofs.NativeConditioningOrder

open Lax263307 RationalConditioning HeavyRationalConditioning NativeCatalogMetadata

def test {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k p:ℕ)
    (y:RationalVector n r) (A:Finset (Fin n)):Bool:=decide (A.card≤ r∧ HeavyPasses G k p y A)

def accepted {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k p:ℕ)
    (y:RationalVector n r) (i:Fin (N n r)):Bool:=test G k p y (atIndex n r i)

def first {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k p:ℕ)
    (y:RationalVector n r):ℕ:=(List.finRange (N n r)).findIdx (accepted G k p y)

theorem sequence (n r:ℕ):(List.finRange (N n r)).map (atIndex n r)=candidates n (r+2):=by
  apply List.ext_getElem?
  intro i
  by_cases hi:i< N n r
  · rw [List.getElem?_eq_getElem (by simpa using hi),List.getElem_map,List.getElem_finRange,
      NativeCatalogOrder.catalog_index n r ⟨i,hi⟩]
    rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi),List.getElem?_eq_none]
    rw [←NativeCatalogOrder.catalog_length]
    exact Nat.le_of_not_gt hi

theorem filtered_find {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r):
    (candidates n (r+2)).find? (test G k p y)=findHeavyConditioning G k p y:=by
  have htail (s:ℕ) (hr:r< s):(ExhaustiveTargets.candidates n s).find? (test G k p y)=none:=by
    apply List.find?_eq_none.mpr
    intro A hA
    have hc:=NativeCatalogOrder.candidate_card n s A hA
    simp only [test,decide_eq_true_eq]
    intro h
    omega
  have hfront:(candidates n r).find? (test G k p y)=findHeavyConditioning G k p y:=by
    apply List.find?_congr
    intro A hA
    have hc:=(Lax263307Proofs.RationalConditioning.candidate_complete n r A).mp hA
    simp only [test,hc,true_and]
  have hsplit:candidates n (r+2)=(candidates n r++ExhaustiveTargets.candidates n (r+1))++ExhaustiveTargets.candidates n (r+2):=by
    exact (NativeCatalogOrder.all_candidates_succ n (r+1)).trans
      (congrArg (fun xs => xs++ExhaustiveTargets.candidates n (r+2)) (NativeCatalogOrder.all_candidates_succ n r))
  rw [hsplit,List.find?_append,List.find?_append,htail (r+1) (by omega),htail (r+2) (by omega),hfront]
  simp

theorem selected {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r):
    ((List.finRange (N n r)).find? (accepted G k p y)).map (atIndex n r)=findHeavyConditioning G k p y:=by
  change ((List.finRange (N n r)).find? ((test G k p y) ∘ atIndex n r)).map (atIndex n r)=_
  rw [←List.find?_map,sequence,filtered_find]

theorem first_le {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r):first G k p y≤ N n r:=by
  simpa only [first,List.length_finRange] using
    (List.findIdx_le_length (p:=accepted G k p y) (xs:=List.finRange (N n r)))

theorem before {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r) (i:Fin (N n r)) (hi:i.val< first G k p y):
    accepted G k p y i=false:=by
  simpa only [List.getElem_finRange,Fin.cast_mk,Fin.eta] using List.not_of_lt_findIdx hi

theorem at_first {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r) (hf:first G k p y< N n r):
    accepted G k p y ⟨first G k p y,hf⟩=true:=by
  have hh:=List.findIdx_getElem (p:=accepted G k p y) (xs:=List.finRange (N n r))
    (w:=by simpa only [first,List.length_finRange] using hf)
  simpa only [first,List.getElem_finRange,Fin.cast_mk] using hh

end Lax263307Proofs.NativeConditioningOrder

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeConditioningEntry

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata

structure Data {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (σ:Env):Prop where
  moments:NativeMomentValue.Context y σ
  cards:Prefix (NativeCatalogMetadata.cards n r) "catalog.card" σ
  graph:Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  order:σ.vars "graph.n"=n
  level:σ.vars "moment.r"=r
  outputRoom:3*n+3*(n*n)<(σ.arrs "lp.word").length
  copyRoom:3*n≤(σ.arrs "cut.source").length
  sumRoom:3*(n*n)≤(σ.arrs "sum.input").length

def Parameters (k p D:ℕ) (σ:Env):Prop:=
  σ.vars "conditioning.k"=k∧ σ.vars "conditioning.p"=p∧ σ.vars "conditioning.floorDen"=D

theorem frame {B n r K:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {y:RationalVector n r} {c:Com} {σ τ:Env} (rr:Run B c σ τ K) (hc:Data G y σ)
    (ha:∀ s∈["catalog.mask","near.moments","catalog.card","search.graph"],s∉c.warrs)
    (hv:∀ s∈["catalog.count","graph.n","moment.r"],s∉c.wvars):Data G y τ:=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [NativeMomentValue.Context,Prefix,
      rr.frame_arr "catalog.mask" (ha _ (by simp)),rr.frame_arr "near.moments" (ha _ (by simp)),
      rr.frame_var "catalog.count" (hv _ (by simp))] using hc.moments
  · simpa only [Prefix,rr.frame_arr "catalog.card" (ha _ (by simp))] using hc.cards
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp))] using hc.graph
  · exact (rr.frame_var "graph.n" (hv _ (by simp))).trans hc.order
  · exact (rr.frame_var "moment.r" (hv _ (by simp))).trans hc.level
  · simpa only [RamFrames.run_array_length rr] using hc.outputRoom
  · simpa only [RamFrames.run_array_length rr] using hc.copyRoom
  · simpa only [RamFrames.run_array_length rr] using hc.sumRoom

theorem parameters_frame {B K k p D:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hc:Parameters k p D σ)
    (hv:∀ s∈["conditioning.k","conditioning.p","conditioning.floorDen"],s∉c.wvars):
    Parameters k p D τ:=by
  simpa only [Parameters,rr.frame_var "conditioning.k" (hv _ (by simp)),
    rr.frame_var "conditioning.p" (hv _ (by simp)),rr.frame_var "conditioning.floorDen" (hv _ (by simp))] using hc

theorem read_spec (B n r:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (i:Fin (N n r)) (hN:N n r< B) (hn:n< B) (hm:2^n< B):
    Spec B (fun σ => Data G y σ∧ σ.vars "scan.i"=i.val) read
      (fun _ τ => Data G y τ∧ τ.vars "conditioning.mask"=NativeMasks.mask (atIndex n r i)∧
        τ.vars "conditioning.card"=(atIndex n r i).card) 6:=by
  rintro σ ⟨hc,hi⟩
  have hilen:i.val<(Lax263307.NativeCatalog.words n r).length:=by
    simpa only [Lax263307.NativeCatalog.words,List.length_map] using i.isLt
  have hg:=hc.moments.1 i.val hilen
  have hw:=NativeMomentAccess.mask_word n r i
  rw [List.getElem?_eq_getElem (by simpa only [Lax263307.NativeCatalog.words,List.length_map] using i.isLt)] at hw
  have he:(Lax263307.NativeCatalog.words n r)[i.val]=NativeMasks.mask (atIndex n r i):=Option.some.inj hw
  rw [he] at hg
  let ν:=σ.setVar "conditioning.mask" (NativeMasks.mask (atIndex n r i))
  have r1:Run B (.assign "conditioning.mask" (.get "catalog.mask" (.var "scan.i"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ i.isLt.trans hN⟩)
      hg ((NativeMasks.mask_bound _).trans hm))
  have hcard:=hc.cards i.val (by simpa only [NativeCatalogMetadata.cards,List.length_ofFn] using i.isLt)
  simp only [NativeCatalogMetadata.cards,List.getElem_ofFn] at hcard
  let τ:=ν.setVar "conditioning.card" (atIndex n r i).card
  have r2:Run B (.assign "conditioning.card" (.get "catalog.card" (.var "scan.i"))) ν τ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using
      (show i.val=σ.vars "scan.i" ∧ σ.vars "scan.i"< B from ⟨hi.symm,hi ▸ i.isLt.trans hN⟩))
      hcard ((NativeMaskUnpack.card_bound _).trans_lt hn))
  exact ⟨τ,r1.seq r2,frame (r1.seq r2) hc (by decide) (by decide),by simp [τ,ν],by simp [τ]⟩

theorem command_spec (B M n r k p:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (i:Fin (N n r)) (hn:0< n) (hp:0< p)
    (hM:1≤ M) (hN:3*N n r+10< B) (hs:3*(n*n)+3*n+r+10< B)
    (hm:2^n< B) (hB:2*M^2+3< B) (hH:2*(NativeQuadraticSum.height M n)^2+3< B)
    (hy:∀ T,Bounded M (y T))
    (htest:NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      M (NativeQuadraticSum.height M n)< B):
    Spec B (fun σ => Data G y σ∧ Parameters k p (NativeConditioningFloor.base n p^r) σ∧ σ.vars "scan.i"=i.val)
      command (fun _ τ => Data G y τ∧ Parameters k p (NativeConditioningFloor.base n p^r) τ∧
        τ.vars "scan.accepted"=if NativeConditioningOrder.accepted G k p y i then 1 else 0) (cost M n r):=by
  rintro σ ⟨hc,hparams,hi⟩
  obtain ⟨ν,r1,d1,hmν,hcardν⟩:=read_spec B n r G y i (by omega) (by omega) hm σ ⟨hc,hi⟩
  have hcardB:(atIndex n r i).card< B:=(NativeMaskUnpack.card_bound _).trans_lt (by omega)
  have hv:(Cond.lt (.var "moment.r") (.var "conditioning.card")).evalB B ν=
      some (decide (r<(atIndex n r i).card)):=
    evalB_condLt
      (by rw [evalB_var_iff]; exact ⟨d1.level.symm,d1.level ▸ (by omega:r< B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hcardν.symm,hcardν ▸ hcardB⟩)
  have hpar1:=parameters_frame r1 hparams (by decide)
  have hcand:∃ μ,Run B choose ν μ (NativeHeavyCandidate.cost M n r+4)∧
      μ.vars "conditioning.passes"=if NativeConditioningOrder.accepted G k p y i then 1 else 0:=by
    by_cases hA:(atIndex n r i).card≤ r
    · obtain ⟨μ,rr,pp⟩:=NativeHeavyCandidate.command_spec B M n r k p G y (atIndex n r i)
        hn hp hA hM hN (by omega) hm hB hH hy
        ((NativeConditioningResources.candidate_test M n r k p G y (atIndex n r i) hM hA hy).trans_lt htest) ν
        ⟨⟨⟨d1.moments,hmν,d1.order⟩,d1.graph⟩,
          hpar1.1,hpar1.2.1,hpar1.2.2,d1.outputRoom,d1.copyRoom,d1.sumRoom⟩
      refine ⟨μ,(Run.ite_false (by simpa only [not_lt.mpr hA,decide_false] using hv) rr).mono
        (by simp only [Cond.size,Expr.size]; omega),?_⟩
      simpa [NativeConditioningOrder.accepted,NativeConditioningOrder.test,hA] using pp.2
    · let μ:=ν.setVar "conditioning.passes" 0
      have rr:Run B (.assign "conditioning.passes" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (by omega))
      refine ⟨μ,(Run.ite_true (by simpa only [Nat.lt_of_not_ge hA,decide_true] using hv) rr).mono
        (by dsimp [Cond.size,Expr.size,NativeHeavyCandidate.cost]; omega),?_⟩
      simp [μ,NativeConditioningOrder.accepted,NativeConditioningOrder.test,hA]
  obtain ⟨μ,r2,hpass⟩:=hcand
  let τ:=μ.setVar "scan.accepted" (if NativeConditioningOrder.accepted G k p y i then 1 else 0)
  have r3:Run B (.assign "scan.accepted" (.var "conditioning.passes")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hpass.symm,hpass ▸ (by split_ifs <;> omega)⟩)
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),frame rr hc (by decide) (by decide),
    parameters_frame rr hparams (by decide),by simp [τ]⟩

end Lax263307Proofs.NativeConditioningEntry

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeFirstScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Invariant (N f:ℕ) (P:Env→ Prop) (σ:Env):Prop:=
  P σ∧ σ.vars "scan.i"≤ N∧ σ.vars "scan.result"=if f<σ.vars "scan.i" then f else N

theorem update_spec (B N f i:ℕ) (b:Bool) (hB:N+3< B) (hf:f≤ N) (hi:i< N)
    (hbefore:i< f→ b=false) (hat:i=f→ b=true):
    Spec B (fun σ => σ.vars "scan.count"=N∧ σ.vars "scan.i"=i∧
      σ.vars "scan.result"=(if f < i then f else N)∧ σ.vars "scan.accepted"=(if b then 1 else 0)) update
      (fun _ τ => τ.vars "scan.i"=i+1∧ τ.vars "scan.result"=if f < i+1 then f else N) 14:=by
  cases b <;> (first
               | (expose_names;
                   (refine
                       fun (σ:Env)
                         (a:
                           And (@Eq Nat (Env.vars σ "scan.count") N)
                             (And (@Eq Nat (Env.vars σ "scan.i") i)
                               (And (@Eq Nat (Env.vars σ "scan.result") (@ite Nat (Nat.lt f i) (Nat.decLt f i) f N))
                                 (@Eq Nat (Env.vars σ "scan.accepted")
                                   (@ite Nat (@Eq Bool false true) (instDecidableEqBool false true)
                                     ((1:Nat))
                                     ((0:Nat))))))) =>
                       let c0:Prop:= @Eq Nat (Env.vars σ "scan.result") (@ite Nat (Nat.lt f i) (Nat.decLt f i) f N);
                       let c1:Prop:=
                         @Eq Nat (Env.vars σ "scan.accepted")
                           (@ite Nat (@Eq Bool false true) (instDecidableEqBool false true)
                             ((1:Nat))
                             ((0:Nat)));
                       let c2:Prop:=And c0 c1;
                       let c3:Prop:=And (@Eq Nat (Env.vars σ "scan.i") i) c2;
                       let c4:Nat→ Nat→ Nat:=Nat.add;
                       let c5:Nat:=c4 i ((1:Nat));
                       let c6:Nat:= @ite Nat (Nat.lt f c5) (Nat.decLt f c5) f N;
                       let c7:Env→ Prop:=
                         (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "scan.i") c5) (@Eq Nat (Env.vars τ "scan.result") c6)) σ;
                       let c8:Env→ Prop:=fun (σ':Env) =>
                         And (Run B update σ σ' ((14:Nat))) (c7 σ');
                       let c9:Prop:= @Exists Env c8;
                       let c10:Prop:= @Eq Nat (Env.vars σ "scan.accepted") ((1:Nat));
                       let c11:Prop:=Not c10;
                       let c12:Prop:= @Eq Nat (Env.vars σ "scan.result") (Env.vars σ "scan.count");
                       let c13:Prop:=Not c12;
                       let c14:Nat:=Env.vars (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i";
                       let c15:Nat:=c4 c14 ((1:Nat));
                       let c16:Env:=Env.setVar (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i" c15;
                       let c17:Nat→ Nat:=c4 ((1:Nat));
                       let c18:Cond:=
                         Cond.eq (Expr.var "scan.accepted") (Expr.lit ((1:Nat)));
                       let c19:Nat→ Nat:=c4 (c17 (Cond.size c18));
                       let c20:Nat→ Nat:=c4 (c17 (Cond.size (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))));
                       let c21:Nat:=c17 (Expr.size (Expr.var "scan.i"));
                       let c22:Nat:=c20 c21;
                       let c23:Nat:=c19 c22;
                       let c24:Expr:=
                         Expr.add (Expr.var "scan.i") (Expr.lit ((1:Nat)));
                       let c25:Nat:=c17 (Expr.size c24);
                       let c26:Com:=
                         Com.ite (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))
                           (Com.assign "scan.result" (Expr.var "scan.i")) Com.skip;
                       let c27:String→ Nat:=Env.vars c16;
                       let c28:Nat:=c4 (Env.vars σ "scan.i") ((1:Nat));
                       let c29:Env:=Env.setVar σ "scan.i" c28;
                       let c30:Nat:=c20 ((1:Nat));
                       let c31:Nat:=c19 c30;
                       let c32:String→ Nat:=Env.vars c29;
                       let c33:Nat:=c19 ((1:Nat));
                       @And.casesOn (@Eq Nat (Env.vars σ "scan.count") N) c3
                         (fun (x:And (@Eq Nat (Env.vars σ "scan.count") N) c3) => c9) a
                         fun (left:@Eq Nat (Env.vars σ "scan.count") N) (right:c3) =>
                         @And.casesOn (@Eq Nat (Env.vars σ "scan.i") i) c2 (fun (x:c3) => c9) right
                           fun (left_1:@Eq Nat (Env.vars σ "scan.i") i) (right_1:c2) =>
                           @And.casesOn c0 c1 (fun (x:c2) => c9) right_1 fun (left_2:c0) (right_2:c1) =>
                             @Or.casesOn c10 c11 (fun (x:Or c10 c11) => c9) (Classical.em c10)
                               (fun (hcase:c10) =>
                                 @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c9) (Classical.em c12)
                                   (fun (hcase_1:c12) =>
                                     @Exists.intro Env c8 c16
                                       (@And.intro (Run B update σ c16 ((14:Nat)))
                                         (c7 c16)
                                         (RunStep.mono B update σ c16 (c4 c23 c25)
                                           ((14:Nat))
                                           (RunStep.seq B (Com.ite c18 c26 Com.skip) (Com.assign "scan.i" c24) σ
                                             (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) c16 c23 c25
                                             (RunStep.ite_true B c18 c26 Com.skip σ (Env.setVar σ "scan.result" (Env.vars σ "scan.i"))
                                               c22
                                               (RunStep.cond_eq_true B σ (Expr.var "scan.accepted")
                                                 (Expr.lit ((1:Nat)))
                                                 (Env.vars σ "scan.accepted") ((1:Nat))
                                                 (RunStep.eval_var B σ "scan.accepted" ?_)
                                                 (RunStep.eval_lit B ((1:Nat)) σ
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 hcase)
                                               (RunStep.ite_true B (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))
                                                 (Com.assign "scan.result" (Expr.var "scan.i")) Com.skip σ
                                                 (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) c21
                                                 (RunStep.cond_eq_true B σ (Expr.var "scan.result") (Expr.var "scan.count")
                                                   (Env.vars σ "scan.result") (Env.vars σ "scan.count")
                                                   (RunStep.eval_var B σ "scan.result" ?_)
                                                   (RunStep.eval_var B σ "scan.count"
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   hcase_1)
                                                 (RunStep.assign B σ "scan.result" (Expr.var "scan.i") (Env.vars σ "scan.i")
                                                   (RunStep.eval_var B σ "scan.i"
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                             (RunStep.assign B (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i" c24 c15
                                               (RunStep.eval_add B (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) (Expr.var "scan.i")
                                                 (Expr.lit ((1:Nat))) c14
                                                 ((1:Nat))
                                                 (RunStep.eval_var B (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 (RunStep.eval_lit B ((1:Nat))
                                                   (Env.setVar σ "scan.result" (Env.vars σ "scan.i"))
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         ?_))
                                   fun (hcase_1:c13) =>
                                   @Exists.intro Env c8 c29
                                     (@And.intro (Run B update σ c29 ((14:Nat)))
                                       (c7 c29)
                                       (RunStep.mono B update σ c29 (c4 c31 c25)
                                         ((14:Nat))
                                         (RunStep.seq B (Com.ite c18 c26 Com.skip) (Com.assign "scan.i" c24) σ σ c29 c31 c25
                                           (RunStep.ite_true B c18 c26 Com.skip σ σ c30
                                             (RunStep.cond_eq_true B σ (Expr.var "scan.accepted")
                                               (Expr.lit ((1:Nat)))
                                               (Env.vars σ "scan.accepted") ((1:Nat))
                                               (RunStep.eval_var B σ "scan.accepted" ?_)
                                               (RunStep.eval_lit B ((1:Nat)) σ
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               hcase)
                                             (RunStep.ite_false B (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))
                                               (Com.assign "scan.result" (Expr.var "scan.i")) Com.skip σ σ
                                               ((1:Nat))
                                               (RunStep.cond_eq_false B σ (Expr.var "scan.result") (Expr.var "scan.count")
                                                 (Env.vars σ "scan.result") (Env.vars σ "scan.count")
                                                 (RunStep.eval_var B σ "scan.result" ?_)
                                                 (RunStep.eval_var B σ "scan.count"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 hcase_1)
                                               (RunStep.skip B σ)))
                                           (RunStep.assign B σ "scan.i" c24 c28
                                             (RunStep.eval_add B σ (Expr.var "scan.i")
                                               (Expr.lit ((1:Nat))) (Env.vars σ "scan.i")
                                               ((1:Nat))
                                               (RunStep.eval_var B σ "scan.i"
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               (RunStep.eval_lit B ((1:Nat)) σ
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ?_))
                               fun (hcase:c11) =>
                               @Exists.intro Env c8 c29
                                 (@And.intro (Run B update σ c29 ((14:Nat))) (c7 c29)
                                   (RunStep.mono B update σ c29 (c4 c33 c25) ((14:Nat))
                                     (RunStep.seq B (Com.ite c18 c26 Com.skip) (Com.assign "scan.i" c24) σ σ c29 c33 c25
                                       (RunStep.ite_false B c18 c26 Com.skip σ σ
                                         ((1:Nat))
                                         (RunStep.cond_eq_false B σ (Expr.var "scan.accepted")
                                           (Expr.lit ((1:Nat)))
                                           (Env.vars σ "scan.accepted") ((1:Nat))
                                           (RunStep.eval_var B σ "scan.accepted" ?_)
                                           (RunStep.eval_lit B ((1:Nat)) σ
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           hcase)
                                         (RunStep.skip B σ))
                                       (RunStep.assign B σ "scan.i" c24 c28
                                         (RunStep.eval_add B σ (Expr.var "scan.i")
                                           (Expr.lit ((1:Nat))) (Env.vars σ "scan.i")
                                           ((1:Nat))
                                           (RunStep.eval_var B σ "scan.i"
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           (RunStep.eval_lit B ((1:Nat)) σ
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
               | (expose_names;
                   (refine
                       fun (σ:Env)
                         (a:
                           And (@Eq Nat (Env.vars σ "scan.count") N)
                             (And (@Eq Nat (Env.vars σ "scan.i") i)
                               (And (@Eq Nat (Env.vars σ "scan.result") (@ite Nat (Nat.lt f i) (Nat.decLt f i) f N))
                                 (@Eq Nat (Env.vars σ "scan.accepted")
                                   (@ite Nat (@Eq Bool true true) (instDecidableEqBool true true)
                                     ((1:Nat))
                                     ((0:Nat))))))) =>
                       let c0:Prop:= @Eq Nat (Env.vars σ "scan.result") (@ite Nat (Nat.lt f i) (Nat.decLt f i) f N);
                       let c1:Prop:=
                         @Eq Nat (Env.vars σ "scan.accepted")
                           (@ite Nat (@Eq Bool true true) (instDecidableEqBool true true)
                             ((1:Nat))
                             ((0:Nat)));
                       let c2:Prop:=And c0 c1;
                       let c3:Prop:=And (@Eq Nat (Env.vars σ "scan.i") i) c2;
                       let c4:Nat→ Nat→ Nat:=Nat.add;
                       let c5:Nat:=c4 i ((1:Nat));
                       let c6:Nat:= @ite Nat (Nat.lt f c5) (Nat.decLt f c5) f N;
                       let c7:Env→ Prop:=
                         (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "scan.i") c5) (@Eq Nat (Env.vars τ "scan.result") c6)) σ;
                       let c8:Env→ Prop:=fun (σ':Env) =>
                         And (Run B update σ σ' ((14:Nat))) (c7 σ');
                       let c9:Prop:= @Exists Env c8;
                       let c10:Prop:= @Eq Nat (Env.vars σ "scan.accepted") ((1:Nat));
                       let c11:Prop:=Not c10;
                       let c12:Prop:= @Eq Nat (Env.vars σ "scan.result") (Env.vars σ "scan.count");
                       let c13:Prop:=Not c12;
                       let c14:Nat:=Env.vars (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i";
                       let c15:Nat:=c4 c14 ((1:Nat));
                       let c16:Env:=Env.setVar (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i" c15;
                       let c17:Nat→ Nat:=c4 ((1:Nat));
                       let c18:Cond:=
                         Cond.eq (Expr.var "scan.accepted") (Expr.lit ((1:Nat)));
                       let c19:Nat→ Nat:=c4 (c17 (Cond.size c18));
                       let c20:Nat→ Nat:=c4 (c17 (Cond.size (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))));
                       let c21:Nat:=c17 (Expr.size (Expr.var "scan.i"));
                       let c22:Nat:=c20 c21;
                       let c23:Nat:=c19 c22;
                       let c24:Expr:=
                         Expr.add (Expr.var "scan.i") (Expr.lit ((1:Nat)));
                       let c25:Nat:=c17 (Expr.size c24);
                       let c26:Com:=
                         Com.ite (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))
                           (Com.assign "scan.result" (Expr.var "scan.i")) Com.skip;
                       let c27:String→ Nat:=Env.vars c16;
                       let c28:Nat:=c4 (Env.vars σ "scan.i") ((1:Nat));
                       let c29:Env:=Env.setVar σ "scan.i" c28;
                       let c30:Nat:=c20 ((1:Nat));
                       let c31:Nat:=c19 c30;
                       let c32:String→ Nat:=Env.vars c29;
                       let c33:Nat:=c19 ((1:Nat));
                       @And.casesOn (@Eq Nat (Env.vars σ "scan.count") N) c3
                         (fun (x:And (@Eq Nat (Env.vars σ "scan.count") N) c3) => c9) a
                         fun (left:@Eq Nat (Env.vars σ "scan.count") N) (right:c3) =>
                         @And.casesOn (@Eq Nat (Env.vars σ "scan.i") i) c2 (fun (x:c3) => c9) right
                           fun (left_1:@Eq Nat (Env.vars σ "scan.i") i) (right_1:c2) =>
                           @And.casesOn c0 c1 (fun (x:c2) => c9) right_1 fun (left_2:c0) (right_2:c1) =>
                             @Or.casesOn c10 c11 (fun (x:Or c10 c11) => c9) (Classical.em c10)
                               (fun (hcase:c10) =>
                                 @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c9) (Classical.em c12)
                                   (fun (hcase_1:c12) =>
                                     @Exists.intro Env c8 c16
                                       (@And.intro (Run B update σ c16 ((14:Nat)))
                                         (c7 c16)
                                         (RunStep.mono B update σ c16 (c4 c23 c25)
                                           ((14:Nat))
                                           (RunStep.seq B (Com.ite c18 c26 Com.skip) (Com.assign "scan.i" c24) σ
                                             (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) c16 c23 c25
                                             (RunStep.ite_true B c18 c26 Com.skip σ (Env.setVar σ "scan.result" (Env.vars σ "scan.i"))
                                               c22
                                               (RunStep.cond_eq_true B σ (Expr.var "scan.accepted")
                                                 (Expr.lit ((1:Nat)))
                                                 (Env.vars σ "scan.accepted") ((1:Nat))
                                                 (RunStep.eval_var B σ "scan.accepted" ?_)
                                                 (RunStep.eval_lit B ((1:Nat)) σ
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 hcase)
                                               (RunStep.ite_true B (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))
                                                 (Com.assign "scan.result" (Expr.var "scan.i")) Com.skip σ
                                                 (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) c21
                                                 (RunStep.cond_eq_true B σ (Expr.var "scan.result") (Expr.var "scan.count")
                                                   (Env.vars σ "scan.result") (Env.vars σ "scan.count")
                                                   (RunStep.eval_var B σ "scan.result" ?_)
                                                   (RunStep.eval_var B σ "scan.count"
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   hcase_1)
                                                 (RunStep.assign B σ "scan.result" (Expr.var "scan.i") (Env.vars σ "scan.i")
                                                   (RunStep.eval_var B σ "scan.i"
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))))
                                             (RunStep.assign B (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i" c24 c15
                                               (RunStep.eval_add B (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) (Expr.var "scan.i")
                                                 (Expr.lit ((1:Nat))) c14
                                                 ((1:Nat))
                                                 (RunStep.eval_var B (Env.setVar σ "scan.result" (Env.vars σ "scan.i")) "scan.i"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 (RunStep.eval_lit B ((1:Nat))
                                                   (Env.setVar σ "scan.result" (Env.vars σ "scan.i"))
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         ?_))
                                   fun (hcase_1:c13) =>
                                   @Exists.intro Env c8 c29
                                     (@And.intro (Run B update σ c29 ((14:Nat)))
                                       (c7 c29)
                                       (RunStep.mono B update σ c29 (c4 c31 c25)
                                         ((14:Nat))
                                         (RunStep.seq B (Com.ite c18 c26 Com.skip) (Com.assign "scan.i" c24) σ σ c29 c31 c25
                                           (RunStep.ite_true B c18 c26 Com.skip σ σ c30
                                             (RunStep.cond_eq_true B σ (Expr.var "scan.accepted")
                                               (Expr.lit ((1:Nat)))
                                               (Env.vars σ "scan.accepted") ((1:Nat))
                                               (RunStep.eval_var B σ "scan.accepted" ?_)
                                               (RunStep.eval_lit B ((1:Nat)) σ
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               hcase)
                                             (RunStep.ite_false B (Cond.eq (Expr.var "scan.result") (Expr.var "scan.count"))
                                               (Com.assign "scan.result" (Expr.var "scan.i")) Com.skip σ σ
                                               ((1:Nat))
                                               (RunStep.cond_eq_false B σ (Expr.var "scan.result") (Expr.var "scan.count")
                                                 (Env.vars σ "scan.result") (Env.vars σ "scan.count")
                                                 (RunStep.eval_var B σ "scan.result" ?_)
                                                 (RunStep.eval_var B σ "scan.count"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 hcase_1)
                                               (RunStep.skip B σ)))
                                           (RunStep.assign B σ "scan.i" c24 c28
                                             (RunStep.eval_add B σ (Expr.var "scan.i")
                                               (Expr.lit ((1:Nat))) (Env.vars σ "scan.i")
                                               ((1:Nat))
                                               (RunStep.eval_var B σ "scan.i"
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               (RunStep.eval_lit B ((1:Nat)) σ
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ?_))
                               fun (hcase:c11) =>
                               @Exists.intro Env c8 c29
                                 (@And.intro (Run B update σ c29 ((14:Nat))) (c7 c29)
                                   (RunStep.mono B update σ c29 (c4 c33 c25) ((14:Nat))
                                     (RunStep.seq B (Com.ite c18 c26 Com.skip) (Com.assign "scan.i" c24) σ σ c29 c33 c25
                                       (RunStep.ite_false B c18 c26 Com.skip σ σ
                                         ((1:Nat))
                                         (RunStep.cond_eq_false B σ (Expr.var "scan.accepted")
                                           (Expr.lit ((1:Nat)))
                                           (Env.vars σ "scan.accepted") ((1:Nat))
                                           (RunStep.eval_var B σ "scan.accepted" ?_)
                                           (RunStep.eval_lit B ((1:Nat)) σ
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           hcase)
                                         (RunStep.skip B σ))
                                       (RunStep.assign B σ "scan.i" c24 c28
                                         (RunStep.eval_add B σ (Expr.var "scan.i")
                                           (Expr.lit ((1:Nat))) (Env.vars σ "scan.i")
                                           ((1:Nat))
                                           (RunStep.eval_var B σ "scan.i"
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           (RunStep.eval_lit B ((1:Nat)) σ
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
              )
  all_goals simp_all
  all_goals first | omega | (split_ifs at * <;> omega)

theorem command_spec (B N f K:ℕ) (P:Env→ Prop) (read:Com) (accepted:Fin N→ Bool)
    (hB:N+3< B) (hf:f≤ N)
    (hbefore:∀ i:Fin N,i.val< f→ accepted i=false)
    (hat:∀ h:f< N,accepted ⟨f,h⟩=true)
    (hcount:∀ σ,P σ→ σ.vars "scan.count"=N)
    (hinit:∀ σ k,P σ→ P (σ.setVar "scan.i" k))
    (hresult:∀ σ k,P σ→ P (σ.setVar "scan.result" k))
    (hwrite:∀ σ τ,Run B update σ τ 14→ P σ→ P τ)
    (hri:"scan.i"∉read.wvars) (hrr:"scan.result"∉read.wvars)
    (hread:∀ i:Fin N,Spec B (fun σ => P σ∧ σ.vars "scan.i"=i.val) read
      (fun _ τ => P τ∧ τ.vars "scan.accepted"=if accepted i then 1 else 0) K):
    Spec B P (command read) (fun _ τ => P τ∧ τ.vars "scan.result"=f) ((K+18)*N+8):=by
  have hbody:Spec B (fun σ => Invariant N f P σ∧ σ.vars "scan.i"< N) (.seq read update)
      (fun σ τ => Invariant N f P τ∧ τ.vars "scan.i"=σ.vars "scan.i"+1) (K+14):=by
    rintro σ ⟨⟨hP,hle,hres⟩,hlt⟩
    let i:Fin N:= ⟨σ.vars "scan.i",hlt⟩
    obtain ⟨ν,r1,p1⟩:=hread i σ ⟨hP,rfl⟩
    have hiν:ν.vars "scan.i"=i.val:=r1.frame_var "scan.i" hri
    obtain ⟨τ,r2,p2⟩:=update_spec B N f i.val (accepted i) hB hf i.isLt (hbefore i)
      (by intro he; have hh:=hat (by omega); simpa only [←he] using hh) ν
      ⟨hcount ν p1.1,hiν,(r1.frame_var "scan.result" hrr).trans hres,p1.2⟩
    exact ⟨τ,r1.seq r2,⟨hwrite ν τ r2 p1.1,by rw [p2.1]; exact i.isLt,
      by simpa only [p2.1] using p2.2⟩,p2.1⟩
  have hloop:=Spec.forRangeZero "scan.i" "scan.count" (Invariant N f P) N (K+14) (by omega)
    (fun _ h => h.2.1) (fun σ h => hcount σ h.1) hbody
  intro σ hP
  have hc:=hcount σ hP
  let ν:=σ.setVar "scan.result" N
  have r1:Run B (.assign "scan.result" (.var "scan.count")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.symm,hc ▸ (by omega:N< B)⟩)
  have hinit':Invariant N f P (ν.setVar "scan.i" 0):=by
    exact ⟨hinit ν 0 (hresult σ N hP),by simp,by simp [ν]⟩
  obtain ⟨τ,r2,p2⟩:=hloop ν hinit'
  have he:(if f< N then f else N)=f:=by split_ifs <;> omega
  exact ⟨τ,(r1.seq r2).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),p2.1.1,
    by simpa only [p2.2,he] using p2.1.2.2⟩

end Lax263307Proofs.NativeFirstScan

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeHeavySearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata NativeConditioningEntry

def Output {n:ℕ}:Option (Finset (Fin n))→ Env→ Prop
  | none,τ => τ.vars "conditioning.found"=0
  | some A,τ => τ.vars "conditioning.found"=1∧ τ.vars "conditioning.choice"=NativeMasks.mask A

theorem selection (n r k p:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r):findHeavyConditioning G k p y=
    if h:NativeConditioningOrder.first G k p y< N n r then
      some (atIndex n r ⟨NativeConditioningOrder.first G k p y,h⟩) else none:=by
  rw [←NativeConditioningOrder.selected,List.find?_eq_getElem?_findIdx]
  change ((List.finRange (N n r))[NativeConditioningOrder.first G k p y]?).map (atIndex n r)=_
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h),List.getElem_finRange]
    rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)]
    rfl

theorem finish_spec (B n r k p:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (hN:N n r+2< B) (hm:2^n< B):
    Spec B (fun σ => Data G y σ∧ σ.vars "scan.result"=NativeConditioningOrder.first G k p y)
      finish (fun _ τ => Data G y τ∧ Output (findHeavyConditioning G k p y) τ) 12:=by
  rintro σ ⟨hc,hf⟩
  have hfB:NativeConditioningOrder.first G k p y< B:=(NativeConditioningOrder.first_le G k p y).trans_lt (by omega)
  have hv:(Cond.lt (.var "scan.result") (.var "catalog.count")).evalB B σ=
      some (decide (NativeConditioningOrder.first G k p y< N n r)):=evalB_condLt
    (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hfB⟩)
    (by rw [evalB_var_iff]; exact ⟨hc.moments.2.2.symm,hc.moments.2.2 ▸ (by omega:N n r< B)⟩)
  by_cases h:NativeConditioningOrder.first G k p y< N n r
  · let i:Fin (N n r):= ⟨NativeConditioningOrder.first G k p y,h⟩
    have hilen:i.val<(Lax263307.NativeCatalog.words n r).length:=by
      simpa only [Lax263307.NativeCatalog.words,List.length_map] using i.isLt
    have hg:=hc.moments.1 i.val hilen
    have hw:=NativeMomentAccess.mask_word n r i
    rw [List.getElem?_eq_getElem hilen] at hw
    rw [Option.some.inj hw] at hg
    let ν:=σ.setVar "conditioning.choice" (NativeMasks.mask (atIndex n r i))
    have r1:Run B (.assign "conditioning.choice" (.get "catalog.mask" (.var "scan.result"))) σ ν 3:=
      Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hfB⟩) hg ((NativeMasks.mask_bound _).trans hm))
    let τ:=ν.setVar "conditioning.found" 1
    have r2:Run B (.assign "conditioning.found" (.lit 1)) ν τ 2:=Run.assign (evalB_lit (by omega))
    have rr:Run B finish σ τ 12:=(Run.ite_true (by simpa only [h,decide_true] using hv) (r1.seq r2)).mono (by decide)
    exact ⟨τ,rr,frame rr hc (by decide) (by decide),by rw [selection,dif_pos h]; simp [Output,τ,ν,i]⟩
  · let τ:=σ.setVar "conditioning.found" 0
    have r1:Run B (.assign "conditioning.found" (.lit 0)) σ τ 2:=Run.assign (evalB_lit (by omega))
    have rr:Run B finish σ τ 12:=(Run.ite_false (by simpa only [h,decide_false] using hv) r1).mono (by decide)
    exact ⟨τ,rr,frame rr hc (by decide) (by decide),by rw [selection,dif_neg h]; simp [Output,τ]⟩

theorem command_spec (B M n r k p:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (hn:0< n) (hp:0< p) (hM:1≤ M)
    (hN:3*N n r+10< B) (hs:3*(n*n)+3*n+r+10< B) (hm:2^n< B)
    (hB:2*M^2+3< B) (hH:2*(NativeQuadraticSum.height M n)^2+3< B)
    (hy:∀ T,Bounded M (y T))
    (htest:NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      M (NativeQuadraticSum.height M n)< B)
    (hfloor:NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10< B):
    Spec B (fun σ => Data G y σ∧ σ.vars "conditioning.k"=k∧ σ.vars "conditioning.p"=p)
      command (fun _ τ => Data G y τ∧ Output (findHeavyConditioning G k p y) τ) (cost M n r):=by
  let P:Env→ Prop:=fun σ => Data G y σ∧ Parameters k p (NativeConditioningFloor.base n p^r) σ∧ σ.vars "scan.count"=N n r
  have hi:∀ σ t,P σ→ P (σ.setVar "scan.i" t):=by
    rintro σ t ⟨d,hp,hc⟩
    refine ⟨?_,by simpa only [Parameters,vars_setVar,String.reduceEq,if_false] using hp,by simpa using hc⟩
    rcases d with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    constructor <;> simp_all [NativeMomentValue.Context,Prefix]
  have hr:∀ σ t,P σ→ P (σ.setVar "scan.result" t):=by
    rintro σ t ⟨d,hp,hc⟩
    refine ⟨?_,by simpa only [Parameters,vars_setVar,String.reduceEq,if_false] using hp,by simpa using hc⟩
    rcases d with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    constructor <;> simp_all [NativeMomentValue.Context,Prefix]
  have hscan:=NativeFirstScan.command_spec B (N n r) (NativeConditioningOrder.first G k p y)
    (NativeConditioningEntry.cost M n r) P NativeConditioningEntry.command (NativeConditioningOrder.accepted G k p y)
    (by omega) (NativeConditioningOrder.first_le G k p y) (NativeConditioningOrder.before G k p y)
    (NativeConditioningOrder.at_first G k p y) (fun _ h => h.2.2) hi hr
    (by rintro σ τ rr ⟨hd,hp,hc⟩; exact ⟨frame rr hd (by decide) (by decide),
      parameters_frame rr hp (by decide),(rr.frame_var "scan.count" (by decide)).trans hc⟩)
    (by decide) (by decide)
    (by
      rintro i σ ⟨⟨hd,hparams,hc⟩,hi⟩
      obtain ⟨τ,rr,d,pp,ha⟩:=NativeConditioningEntry.command_spec B M n r k p G y i hn hp hM hN hs hm hB hH hy htest σ ⟨hd,hparams,hi⟩
      exact ⟨τ,rr,⟨d,pp,(rr.frame_var "scan.count" (by decide)).trans hc⟩,ha⟩)
  rintro σ ⟨hc,hk,hpσ⟩
  obtain ⟨ν,r1,p1⟩:=NativeConditioningFloor.command_spec B n p r hn hp hfloor σ ⟨hc.order,hpσ,hc.level⟩
  have d1:=frame r1 hc (by decide) (by decide)
  let μ:=ν.setVar "scan.count" (N n r)
  have r2:Run B (.assign "scan.count" (.var "catalog.count")) ν μ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨d1.moments.2.2.symm,d1.moments.2.2 ▸ (by omega:N n r< B)⟩)
  have r12:=r1.seq r2
  have hmP:P μ:= ⟨frame r12 hc (by decide) (by decide),
    ⟨(r12.frame_var "conditioning.k" (by decide)).trans hk,
      (r12.frame_var "conditioning.p" (by decide)).trans hpσ,
      (r2.frame_var "conditioning.floorDen" (by decide)).trans p1⟩,by simp [μ]⟩
  obtain ⟨ξ,r3,p3⟩:=hscan μ hmP
  obtain ⟨τ,r4,p4⟩:=finish_spec B n r k p G y (by omega) hm ξ ⟨p3.1.1,p3.2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by dsimp [cost]; omega),p4⟩

end Lax263307Proofs.NativeHeavySearch

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativePositiveQuotient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic

theorem inverse_bounded (M:ℕ) (q:ℚ) (hM:1≤ M) (hq:Bounded M q):Bounded M q⁻¹:=by
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hs:q.num.sign.natAbs≤1:=by
      rcases lt_trichotomy q.num 0 with h | h | h
      · simp [Int.sign_eq_neg_one_of_neg h]
      · simp [h]
      · simp [Int.sign_eq_one_of_pos h]
    exact (Nat.mul_le_mul_right q.den hs).trans (by simpa using hq.2)
  · rw [Rat.den_inv]
    split_ifs <;> first | exact hM | exact hq.1

theorem inverse_spec (B M:ℕ) (q:ℚ) (hB:M+2< B) (hq:Bounded M q):
    Spec B (Stored "left" q) invertFraction (fun _ τ => FractionOutput q⁻¹ τ) (36*M.size+40):=by
  intro σ h
  have hh:=h
  simp only [Stored,String.reduceAppend] at hh
  obtain ⟨τ,rr,ht⟩:=invertFraction_spec B (σ.vars "left.s") q.num.natAbs q.den (by omega)
    hh.2.2.2 (hq.1.trans_lt (by omega)) (hq.2.trans_lt (by omega)) σ ⟨rfl,hh.2.1,hh.2.2.1⟩
  have he:fractionValue (σ.vars "left.s") q.num.natAbs q.den=q:=by
    simpa only [←hh.2.1,←hh.2.2.1] using hh.1
  exact ⟨τ,rr.mono (by have hsize:=Nat.size_le_size hq.1; omega),by simpa only [he] using ht⟩

theorem positive_spec (B M:ℕ) (q:ℚ) (hB:M+2< B) (hq:Bounded M q):
    Spec B (FractionOutput q) positive (fun _ τ => FractionOutput (max 0 q) τ) 10:=by
  intro σ h
  have hsign:=h.2.2.2
  by_cases hs:σ.vars "rat.s"=1
  · have hq0:q≤0:=by
      rw [←h.1]
      simp only [fractionValue,hs,if_true]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    obtain ⟨τ,rr,ht⟩:=RamFractionPrimitives.zero_spec B (by omega) σ trivial
    have hc:(Cond.eq (.var "rat.s") (.lit 1)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hs ▸ (by omega:1< B))) (evalB_lit (by omega:1< B)),hs]
      rfl
    exact ⟨τ,(Run.ite_true (d:=.skip) hc rr).mono (by decide),by simpa only [max_eq_left hq0] using ht⟩
  · have hq0:0≤ q:=by
      rw [←h.1]
      simp only [fractionValue,hs,if_false]
      positivity
    have hc:(Cond.eq (.var "rat.s") (.lit 1)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hsign.trans_lt (by omega:1< B))) (evalB_lit (by omega:1< B))]
      simp [hs]
    exact ⟨σ,(Run.ite_false (c:=RamFractionPrimitives.zero) hc Run.skip).mono (by decide),
      by simpa only [max_eq_right hq0] using h⟩

theorem positive_bounded (M:ℕ) (q:ℚ) (hM:1≤ M) (hq:Bounded M q):
    Bounded M (max 0 q):=by
  rcases le_total q 0 with h | h
  · simp only [max_eq_left h]
    exact ⟨by simp,by simpa using hM⟩
  · simpa only [max_eq_right h] using hq

theorem command_spec (B M:ℕ) (a b:ℚ) (hM:1≤ M) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (fun σ => Stored "quotient.numerator" a σ∧ Stored "quotient.denominator" b σ)
      command (fun _ τ => FractionOutput (max 0 (a/b)) τ) (72*(M^2).size+144):=by
  have hsmall:M+2< B:=by nlinarith
  have h1:1< B:=by nlinarith
  have hMB:M< B:=by omega
  have hbi:=inverse_bounded M b hM hb
  rintro σ ⟨haσ,hbσ⟩
  obtain ⟨σ1,r1,p1⟩:=load_spec B "quotient.denominator" b h1 (hb.1.trans_lt hMB) (hb.2.trans_lt hMB) (by decide) σ hbσ
  obtain ⟨σ2,r2,p2⟩:=save_spec B "left" b h1 (hb.1.trans_lt hMB) (hb.2.trans_lt hMB) (by decide) σ1 p1
  obtain ⟨σ3,r3,p3⟩:=inverse_spec B M b hsmall hb σ2 p2
  obtain ⟨σ4,r4,p4⟩:=save_spec B "right" b⁻¹ h1 (hbi.1.trans_lt hMB) (hbi.2.trans_lt hMB) (by decide) σ3 p3
  have ha4:Stored "quotient.numerator" a σ4:=by
    have rr:=r1.seq (r2.seq (r3.seq r4))
    simpa only [Stored,String.reduceAppend,rr.frame_var "quotient.numerator.s" (by decide),
      rr.frame_var "quotient.numerator.n" (by decide),rr.frame_var "quotient.numerator.d" (by decide)] using haσ
  obtain ⟨σ5,r5,p5⟩:=load_spec B "quotient.numerator" a h1 (ha.1.trans_lt hMB) (ha.2.trans_lt hMB) (by decide) σ4 ha4
  obtain ⟨σ6,r6,p6⟩:=save_spec B "left" a h1 (ha.1.trans_lt hMB) (ha.2.trans_lt hMB) (by decide) σ5 p5
  have hb6:Stored "right" b⁻¹ σ6:=by
    simpa only [Stored,String.reduceAppend,(r5.seq r6).frame_var "right.s" (by decide),
      (r5.seq r6).frame_var "right.n" (by decide),(r5.seq r6).frame_var "right.d" (by decide)] using p4
  obtain ⟨σ7,r7,p7⟩:=multiply_spec B M a b⁻¹ hB ha hbi σ6 ⟨p6,hb6⟩
  have hab:Bounded (M^2) (a*b⁻¹):=by simpa only [pow_two] using NativeSumHeight.multiply M M a b⁻¹ ha hbi
  obtain ⟨τ,r8,p8⟩:=positive_spec B (M^2) (a*b⁻¹) (by nlinarith) hab σ7 p7
  have hsize:(a.den*(b⁻¹).den).size≤(M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul ha.2 hbi.2])
  have hsizeM:M.size≤(M^2).size:=Nat.size_le_size (by nlinarith)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))).mono (by omega),
    by simpa only [div_eq_mul_inv] using p8⟩

theorem height (M:ℕ) (a b:ℚ) (hM:1≤ M) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (M^2) (max 0 (a/b)):=by
  apply positive_bounded (M^2) (a/b) (by nlinarith)
  simpa only [div_eq_mul_inv,pow_two] using NativeSumHeight.multiply M M a b⁻¹ ha (inverse_bounded M b hM hb)

end Lax263307Proofs.NativePositiveQuotient

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNearCosts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def values {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n)) (v:Fin n):ℚ:=NearOracle.costs y A v

def Data {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n)) (σ:Env):Prop:=
  NativeConditioningVector.Data y A σ∧ Stored "quotient.denominator" (rationalValue y A) σ

theorem frame {B n r K:ℕ} {y:RationalVector n r} {A:Finset (Fin n)}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K) (hd:Data y A σ)
    (ha:∀ s∈["catalog.mask","near.moments"],s∉c.warrs)
    (hv:∀ s∈["catalog.count","conditioning.mask","graph.n","quotient.denominator.s",
      "quotient.denominator.n","quotient.denominator.d"],s∉c.wvars):Data y A τ:=by
  refine ⟨NativeConditioningVector.frame rr hd.1 (ha _ (by simp)) (ha _ (by simp))
    (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp)),?_⟩
  simpa only [Stored,String.reduceAppend,rr.frame_var "quotient.denominator.s" (hv _ (by simp)),
    rr.frame_var "quotient.denominator.n" (hv _ (by simp)),
    rr.frame_var "quotient.denominator.d" (hv _ (by simp))] using hd.2

theorem moment_bound (M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hA:A.card≤ r) (hy:∀ T,Bounded M (y T)):Bounded M (rationalValue y A):=by
  have hh:A.card≤ r+2:=by omega
  simpa only [rationalValue,dif_pos hh] using hy ⟨A,hh⟩

theorem extension_bound (M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hA:A.card≤ r) (hy:∀ T,Bounded M (y T)) (v:Fin n):Bounded M (rationalValue y (insert v A)):=by
  have hh:(insert v A).card≤ r+2:=(Finset.card_insert_le v A).trans (by omega)
  simpa only [rationalValue,dif_pos hh] using hy ⟨insert v A,hh⟩

theorem height (M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hM:1≤ M) (hA:A.card≤ r) (hy:∀ T,Bounded M (y T)) (v:Fin n):
    Bounded (M^2) (values y A v):=
  NativePositiveQuotient.height M _ _ hM (extension_bound M n r y A hA hy v) (moment_bound M n r y A hA hy)

theorem read_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n)) (v:Fin n)
    (hM:1≤ M) (hA:A.card≤ r) (hN:3*N n r+10< B) (hn:n+2< B) (hm:2^n< B)
    (hB:2*M^2+3< B) (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Data y A σ∧ σ.vars "conditioning.v"=v.val) read
      (fun _ τ => Data y A τ∧ RamRational.FractionOutput (values y A v) τ)
      (17*N n r+72*(M^2).size+187):=by
  have h1:1< B:=by nlinarith
  have hMB:M< B:=by nlinarith
  have hv:=extension_bound M n r y A hA hy v
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=NativeConditioningVector.read_spec B M n r y A v hA hN hn hm hMB hy σ ⟨hd.1,hi⟩
  obtain ⟨μ,r2,p2⟩:=save_spec B "quotient.numerator" (rationalValue y (insert v A)) h1
    (hv.1.trans_lt hMB) (hv.2.trans_lt hMB) (by decide) ν p1.2
  have hdμ:=frame (r1.seq r2) hd (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩:=NativePositiveQuotient.command_spec B M (rationalValue y (insert v A)) (rationalValue y A)
    hM hB hv (moment_bound M n r y A hA hy) μ ⟨p2,hdμ.2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),frame r3 hdμ (by decide) (by decide),p3⟩

theorem vector_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hM:1≤ M) (hA:A.card≤ r) (hN:3*N n r+10< B) (hn:3*n+3< B) (hm:2^n< B)
    (hB:2*M^2+3< B) (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => Data y A σ∧ 3*n<(σ.arrs "lp.word").length) vector
      (fun _ τ => Data y A τ∧ Prefix (encodeVector (values y A)) "lp.word" τ∧ τ.vars "lp.position"=3*n)
      ((17*N n r+72*(M^2).size+222)*n+8):=by
  have hMB:M^2< B:=by nlinarith
  have hh:=RamVectorEncoding.command_spec B (17*N n r+72*(M^2).size+187) (Data y A)
    "conditioning.v" "graph.n" (List.ofFn (values y A)) [] read (by omega)
    (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (height M n r y A hM hA hy ⟨i,by simpa using hi⟩).1.trans_lt hMB)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (height M n r y A hM hA hy ⟨i,by simpa using hi⟩).2.trans_lt hMB)
    (fun σ h => by simpa only [List.length_ofFn] using h.1.2.2)
    (fun σ k h => by simpa only [Data,NativeConditioningVector.Data,NativeMomentValue.Context,
      Prefix,Stored,String.reduceAppend,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [List.getElem_ofFn] using read_spec B M n r y A ⟨i,by simpa using hi⟩ hM hA hN (by omega) hm hB hy)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide)) (by decide)
  rintro σ ⟨hd,hr⟩
  have r1:Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2:=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩:=hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hd (by decide) (by decide),by simp [Prefix],by simp,
      by simpa only [List.length_nil,List.length_ofFn,arrs_setVar,Nat.zero_add] using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

theorem prepare_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hA:A.card≤ r) (hN:3*N n r+10< B) (hm:2^n< B) (hM:M< B)
    (hy:∀ T,Bounded M (y T)):
    Spec B (NativeConditioningVector.Data y A) prepare (fun _ τ => Data y A τ) (17*N n r+39):=by
  intro σ hd
  let ν:=σ.setVar "lookup.key" (NativeMasks.mask A)
  have r1:Run B (.assign "lookup.key" (.var "conditioning.mask")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.2.1.symm,hd.2.1 ▸ (NativeMasks.mask_bound A).trans hm⟩)
  have hdν:=NativeConditioningVector.frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨μ,r2,p2⟩:=NativeMomentValue.command_spec B M n r y A (by omega) hN hm hM hy ν ⟨hdν.1,by simp [ν]⟩
  have hq:=moment_bound M n r y A hA hy
  obtain ⟨τ,r3,p3⟩:=save_spec B "quotient.denominator" (rationalValue y A) (by omega)
    (hq.1.trans_lt hM) (hq.2.trans_lt hM) (by decide) μ p2.2
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by omega),NativeConditioningVector.frame rr hd (by decide) (by decide) (by decide) (by decide) (by decide),p3⟩

theorem command_spec (B M n r:ℕ) (y:RationalVector n r) (A:Finset (Fin n))
    (hM:1≤ M) (hA:A.card≤ r) (hN:3*N n r+10< B) (hn:3*n+3< B) (hm:2^n< B)
    (hB:2*M^2+3< B) (hy:∀ T,Bounded M (y T)):
    Spec B (fun σ => NativeConditioningVector.Data y A σ∧ 3*n<(σ.arrs "lp.word").length∧
      3*n≤(σ.arrs "near.costs").length) command
      (fun _ τ => Data y A τ∧ Prefix (encodeVector (values y A)) "near.costs" τ)
      ((17*N n r+72*(M^2).size+270)*n+17*N n r+59):=by
  have hlen:(encodeVector (values y A)).length=3*n:=by
    change (RamVectorEncoding.encode (List.ofFn (values y A))).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup:Spec B (fun σ => σ.vars "graph.n"=n) copySetup
      (fun _ τ => τ.vars "slice.start"=0∧ τ.vars "fill.length"=3*n) 6:=by
    (expose_names;
      (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ "graph.n") n) => let c0:Nat→ Nat:=Nat.mul ((3:Nat)); let c1:Nat:=c0 n; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))) (@Eq Nat (Env.vars τ "fill.length") c1)) σ; let c3:Env:=Env.setVar σ "slice.start" ((0:Nat)); let c4:Nat:=Env.vars c3 "graph.n"; let c5:Nat:=c0 c4; let c6:Env:=Env.setVar c3 "fill.length" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c10:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "graph.n"); let c11:Nat:=c8 (Expr.size c10); let c12:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (Run B copySetup σ σ' ((6:Nat))) (c2 σ')) c6 (@And.intro (Run B copySetup σ c6 ((6:Nat))) (c2 c6) (RunStep.mono B copySetup σ c6 (c7 c9 c11) ((6:Nat)) (RunStep.seq B (Com.assign "slice.start" (Expr.lit ((0:Nat)))) (Com.assign "fill.length" c10) σ c3 c6 c9 c11 (RunStep.assign B σ "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8723_0_0_0))) (RunStep.assign B c3 "fill.length" c10 c5 (RunStep.eval_mul B c3 (Expr.lit ((3:Nat))) (Expr.var "graph.n") ((3:Nat)) c4 (RunStep.eval_lit B ((3:Nat)) c3 (?nAX_g8723_0_0_1)) (RunStep.eval_var B c3 "graph.n" (?nAX_g8723_0_0_2)) (?nAX_g8723_0_0_3)))) (?nAX_g8723_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8723_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8723_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8723_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8723_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8723_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  rintro σ ⟨hd,hO,hC⟩
  obtain ⟨ν,r1,p1⟩:=prepare_spec B M n r y A hA hN hm (by nlinarith) hy σ hd
  obtain ⟨μ,r2,p2⟩:=vector_spec B M n r y A hM hA hN hn hm hB hy ν
    ⟨p1,by rwa [RamFrames.run_array_length r1]⟩
  obtain ⟨ξ,r3,p3⟩:=hsetup μ p2.1.1.2.2
  have hp:Prefix (encodeVector (values y A)) "lp.word" ξ:=by
    simpa only [Prefix,r3.frame_arr "lp.word" (by decide)] using p2.2.1
  obtain ⟨τ,r4,p4⟩:=NativeSlice.command_spec B "lp.word" "near.costs" [] (encodeVector (values y A)) []
    (by decide) (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B (M^2) n (values y A) (by omega) (by nlinarith) (height M n r y A hM hA hy)) ξ
    ⟨⟨by simpa using hp,by simpa using p3.1⟩,by simpa only [hlen] using p3.2,
      by rw [hlen,RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hC⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hlen]; nlinarith),
    frame (r3.seq r4) p2.1 (by decide) (by decide),p4.2⟩

end Lax263307Proofs.NativeNearCosts

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

end Lax263307Proofs.NativeSeparatorContext

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

end Lax263307Proofs.NativeSeparatorOutput

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeComponentControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks ComputedSeparators

theorem start_spec (B q next:ℕ) (hB:q+next+3< B):
    Spec B (fun σ => σ.vars "separator.count"=q) (start next)
      (fun _ τ => τ.vars "component.count"=q+1∧ τ.vars "component.i"=0∧
        τ.vars "component.union"=0∧ τ.vars "machine.phase"=next) 10:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 q ((1:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "component.count") c1) (And (@Eq Nat (Env.vars τ "component.i") ((0:Nat))) (And (@Eq Nat (Env.vars τ "component.union") ((0:Nat))) (@Eq Nat (Env.vars τ "machine.phase") next)))) σ; let c3:Nat:=c0 (Env.vars σ "separator.count") ((1:Nat)); let c4:Env:=Env.setVar σ "component.count" c3; let c5:Env:=Env.setVar c4 "component.i" ((0:Nat)); let c6:Env:=Env.setVar c5 "component.union" ((0:Nat)); let c7:Env:=Env.setVar c6 "machine.phase" next; let c8:Nat→ Nat:=c0 ((1:Nat)); let c9:Expr:=Expr.add (Expr.var "separator.count") (Expr.lit ((1:Nat))); let c10:Nat:=c8 (Expr.size c9); let c11:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c12:Nat→ Nat:=c0 c11; let c13:Nat:=c8 (Expr.size (Expr.lit next)); let c14:Nat:=c12 c13; let c15:Nat:=c12 c14; let c16:Com:=Com.assign "component.i" (Expr.lit ((0:Nat))); let c17:Com:=Com.assign "component.union" (Expr.lit ((0:Nat))); let c18:Com:=Com.seq c17 (Com.assign "machine.phase" (Expr.lit next)); let c19:String→ Nat:=Env.vars c7; @Exists.intro Env (fun (σ':Env) => And (Run B (start next) σ σ' ((10:Nat))) (c2 σ')) c7 (@And.intro (Run B (start next) σ c7 ((10:Nat))) (c2 c7) (RunStep.mono B (start next) σ c7 (c0 c10 c15) ((10:Nat)) (RunStep.seq B (Com.assign "component.count" c9) (Com.seq c16 c18) σ c4 c7 c10 c15 (RunStep.assign B σ "component.count" c9 c3 (RunStep.eval_add B σ (Expr.var "separator.count") (Expr.lit ((1:Nat))) (Env.vars σ "separator.count") ((1:Nat)) (RunStep.eval_var B σ "separator.count" (?nAX_g9025_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9025_0_0_1)) (?nAX_g9025_0_0_2))) (RunStep.seq B c16 c18 c4 c5 c7 c11 c14 (RunStep.assign B c4 "component.i" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c4 (?nAX_g9025_0_0_3))) (RunStep.seq B c17 (Com.assign "machine.phase" (Expr.lit next)) c5 c6 c7 c11 c13 (RunStep.assign B c5 "component.union" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g9025_0_0_4))) (RunStep.assign B c6 "machine.phase" (Expr.lit next) next (RunStep.eval_lit B next c6 (?nAX_g9025_0_0_5)))))) (?nAX_g9025_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9025_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9025_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9025_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9025_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9025_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9025_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9025_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeComponentControl

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

theorem order_complete (q:ℕ) (i:Option (Fin q)):i∈NearOracle.order q:=by
  cases i <;> simp [NearOracle.order]

theorem piece_words {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))):
    NativeCutPieces.words cs=(NearOracle.order cs.length).map
      (fun i => NativeMasks.mask (ComputedSeparators.pieces cs i)):=by
  simp only [NativeCutPieces.words,NearOracle.order,List.map_cons,List.map_map,ComputedSeparators.pieces]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

end Lax263307Proofs.NativeCollectionSemantics

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

namespace Lax263307Proofs.NativeCollectionAnchor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine

theorem refl (σ:Env):Anchor σ σ:= ⟨fun _ _ => rfl,fun _ _ => rfl⟩

theorem trans {base σ τ:Env} (h:Anchor base σ) (hnext:Anchor σ τ):Anchor base τ:=
  ⟨fun s hs => (hnext.1 s hs).trans (h.1 s hs),
    fun a ha => (hnext.2 a ha).trans (h.2 a ha)⟩

theorem stored_state {n:ℕ} {j:ℕ} {state:RoundedOracleSearch.State n}
    {base σ:Env} (hc:Anchor base σ) (hs:NativeRoundedTrace.StoredState j state base):
    NativeRoundedTrace.StoredState j state σ:=by
  refine ⟨?_,?_,(hc.1 _ (by decide)).trans hs.2.2.1,(hc.1 _ (by decide)).trans hs.2.2.2⟩
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,hc.2 "round.shape" (by decide)] using hs.1
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,hc.2 "round.center" (by decide)] using hs.2.1

end Lax263307Proofs.NativeCollectionAnchor

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNearTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeCoreMachine NativeMachineSegment NativeSignedArithmetic NativeCatalogMetadata

theorem conditioning_segment (B M n r k p:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin (N n r)→ ℚ)
    (hn:0< n) (hp:0< p) (hM:1≤ M)
    (hN:3*N n r+10< B) (hs:3*(n*n)+3*n+r+10< B) (hm:2^n< B)
    (hB:2*M^2+3< B) (hH:2*(NativeQuadraticSum.height M n)^2+3< B)
    (hx:∀ i,Bounded M (x i))
    (htest:NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      M (NativeQuadraticSum.height M n)< B)
    (hfloor:NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10< B)
    (σ:Env) (hd:NativeMomentAccess.Data G r σ)
    (hpoint:Prefix (encodeVector x) "lp.word" σ)
    (hkσ:σ.vars "conditioning.k"=k) (hpσ:σ.vars "conditioning.p"=p)
    (hroom:3*n+3*(n*n)<(σ.arrs "lp.word").length)
    (hcopy:3*n≤(σ.arrs "cut.source").length) (hsum:3*(n*n)≤(σ.arrs "sum.input").length)
    (hstore:3*N n r≤(σ.arrs "near.moments").length)
    (hr:σ.vars "machine.running"=1) (hphase:σ.vars "machine.phase"=6):
    ∃ τ,Segment B (phases cfg) 1 (48*N n r+NativeHeavySearch.cost M n r+14) σ τ∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=7∧
      NativeConditioningEntry.Data G (MomentLP.decode x) τ∧
      NativeHeavySearch.Output (findHeavyConditioning G k p (MomentLP.decode x)) τ:=by
  obtain ⟨ν,r1,p1⟩:=NativeMomentStorage.command_spec B M n r x hN (by nlinarith) hx σ
    ⟨hpoint,hd.1.2.2.1,hd.1.2.1,hstore⟩
  have data:NativeConditioningEntry.Data G (MomentLP.decode x) ν:=
    ⟨p1.1,by simpa only [Prefix,r1.frame_arr "catalog.card" (by decide)] using hd.2.1,
      by simpa only [Prefix,r1.frame_arr "search.graph" (by decide)] using hd.1.2.2.2.1,
      (r1.frame_var _ (by decide)).trans hd.1.1,(r1.frame_var _ (by decide)).trans hd.2.2.2,
      by simpa only [RamFrames.run_array_length r1] using hroom,
      by simpa only [RamFrames.run_array_length r1] using hcopy,
      by simpa only [RamFrames.run_array_length r1] using hsum⟩
  have hy:∀ T,Bounded M (MomentLP.decode x T):=fun T => hx ((CoordinateCatalog.indexing n r).symm T)
  obtain ⟨μ,r2,p2⟩:=NativeHeavySearch.command_spec B M n r k p G (MomentLP.decode x)
    hn hp hM hN hs hm hB hH hy htest hfloor ν
    ⟨data,(r1.frame_var _ (by decide)).trans hkσ,(r1.frame_var _ (by decide)).trans hpσ⟩
  let τ:=μ.setVar "machine.phase" 7
  have r3:Run B (go 7) μ τ 2:=Run.assign (evalB_lit (show 7< B by omega))
  have run:Run B (Com.seq NativeMomentStorage.command (Com.seq NativeHeavySearch.command (go 7))) σ τ
      (48*N n r+NativeHeavySearch.cost M n r+14):=(r1.seq (r2.seq r3)).mono (by omega)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨6,by change 6<16; decide⟩ hphase run,?_,by simp [τ],?_,?_⟩
  · exact (run.frame_var _ (by decide)).trans hr
  · exact NativeConditioningEntry.frame r3 p2.1 (by intro s hs; simp [go,Com.warrs])
      (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl|rfl|rfl <;> decide)
  · cases hsel:findHeavyConditioning G k p (MomentLP.decode x) <;>
      simpa [hsel,NativeHeavySearch.Output,τ] using p2.2

private theorem value {B x:ℕ} {s:String} {σ:Env} (h:σ.vars s=x) (hx:x< B):
    (Expr.var s).evalB B σ=some x:=by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem none_segment (B n:ℕ) (cfg:Config) (hB:n+19< B)
    (σ:Env) (hn:σ.vars "graph.n"=n)
    (ho:NativeHeavySearch.Output (none:Option (Finset (Fin n))) σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=7):
    ∃ τ,Segment B (phases cfg) 1 10 σ τ∧ NativeRoundTrace.Stopped (none:Option (Finset (Fin n))) τ:=by
  obtain ⟨τ,rr,po⟩:=NativeAttemptReply.none_spec B n 14 hB σ hn
  have ht:(Cond.eq (.var "conditioning.found") (.lit 1)).evalB B σ=some false:=
    evalB_condEq (value ho (by omega)) (evalB_lit (show 1< B by omega))
  have run:Run B conditioningReply σ τ 10:=
    (Run.ite_false (c:=.seq (.assign "conditioning.mask" (.var "conditioning.choice"))
      (.seq NativeNearCosts.command (go 8))) ht rr).mono (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨7,by change 7<16; decide⟩ hp run,
    (rr.frame_var _ (by decide)).trans hr,po.2.2,po.2.1⟩

theorem some_segment (B M n r:ℕ) (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hM:1≤ M) (hA:A.card≤ r)
    (hN:3*N n r+10< B) (hn:3*n+3< B) (hm:2^n< B) (hB:2*M^2+3< B)
    (hy:∀ T,Bounded M (y T)) (σ:Env) (hd:NativeConditioningEntry.Data G y σ)
    (ho:NativeHeavySearch.Output (some A) σ)
    (hroom:3*n<(σ.arrs "lp.word").length) (hcosts:3*n≤(σ.arrs "near.costs").length)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=7):
    ∃ τ,Segment B (phases cfg) 1 ((17*N n r+72*(M^2).size+270)*n+17*N n r+67) σ τ∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=8∧
      NativeNearCosts.Data y A τ∧ Prefix (encodeVector (NativeNearCosts.values y A)) "near.costs" τ:=by
  let ν:=σ.setVar "conditioning.mask" (NativeMasks.mask A)
  have r1:Run B (.assign "conditioning.mask" (.var "conditioning.choice")) σ ν 2:=
    Run.assign (value ho.2 ((NativeMasks.mask_bound A).trans hm))
  obtain ⟨μ,r2,p2⟩:=NativeNearCosts.command_spec B M n r y A hM hA hN hn hm hB hy ν
    ⟨⟨by simpa [NativeMomentValue.Context,Prefix,ν] using hd.moments,by simp [ν],by simpa [ν] using hd.order⟩,
      hroom,hcosts⟩
  let τ:=μ.setVar "machine.phase" 8
  have r3:Run B (go 8) μ τ 2:=Run.assign (evalB_lit (show 8< B by omega))
  have ht:(Cond.eq (.var "conditioning.found") (.lit 1)).evalB B σ=some true:=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 1< B by omega))
  have run:Run B conditioningReply σ τ ((17*N n r+72*(M^2).size+270)*n+17*N n r+67):=
    (Run.ite_true (d:=NativeAttemptReply.noneCommand 14) ht (r1.seq (r2.seq r3))).mono
      (by simp [Cond.size,Expr.size]; omega)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨7,by change 7<16; decide⟩ hp run,
    (run.frame_var _ (by decide)).trans hr,by simp [τ],?_,p2.2⟩
  exact NativeNearCosts.frame r3 p2.1 (by intro s hs; simp [go,Com.warrs])
    (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)

end Lax263307Proofs.NativeNearTrace

end

section

namespace Lax263307Proofs.NativeSeparatorTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment

theorem running_unwritten (p:Lax808846.Ram.Program) (coeff:List ℕ):
    "machine.running"∉(NativeSeparatorOutput.command p coeff).wvars:=by
  have hc:=NativeSeparatorContext.callback_variable p coeff "machine.running"
    (by decide) (by decide) (by decide) (by decide)
  simp only [NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,not_or]
  simp only [hc,and_true,true_and]
  decide

theorem separator_segment {n:ℕ} (B b load k space callCost:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0)
    (cs:List (Finset (Fin n) × Finset (Fin n)))
    (call:Spec B (fun σ => NativeSeparatorContext.Context G x b load k space σ∧
        n+1≤(σ.arrs "separator.pieces").length)
      (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
      (fun _ τ => NativeSeparatorContext.Context G x b load k space τ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs)∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs)∧ τ.vars "separator.count"=cs.length∧
        Prefix (NativeCutRecords.words cs) "separator.cuts" τ∧ τ.vars "separator.position"=2*cs.length∧
        Prefix (NativeCutPieces.words cs) "separator.pieces" τ) callCost)
    (hB:cs.length+12< B) (σ:Env)
    (hd:NativeSeparatorContext.Context G x b load k space σ)
    (hroom:n+1≤(σ.arrs "separator.pieces").length)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=8):
    ∃ τ,Segment B (phases cfg) 1 (callCost+10) σ τ∧
      NativeSeparatorContext.Context G x b load k space τ∧
      Prefix ((NearOracle.order cs.length).map (fun i => NativeMasks.mask (pieces cs i))) "separator.pieces" τ∧
      τ.vars "component.count"=cs.length+1∧ τ.vars "component.i"=0∧ τ.vars "component.union"=0∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=9:=by
  obtain ⟨ν,r1,p1⟩:=call σ ⟨hd,hroom⟩
  obtain ⟨τ,r2,p2⟩:=NativeComponentControl.start_spec B cs.length 9 hB ν p1.2.2.2.1
  refine ⟨τ,NativeMachineSegment.phase hr ⟨8,by change 8<16; decide⟩ hp (r1.seq r2),?_,?_,
    p2.1,p2.2.1,p2.2.2.1,?_,p2.2.2.2⟩
  · exact NativeSeparatorContext.frame r2 p1.1
      (by intro s hs; simp only [NativeSeparatorContext.protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl|rfl|rfl|rfl <;> decide) (by decide) (by decide)
  · have he:=NativeCollectionSemantics.piece_words cs
    simpa only [←he,Prefix,r2.frame_arr "separator.pieces" (by decide)] using p1.2.2.2.2.2.2
  · exact (r2.frame_var _ (by decide)).trans ((r1.frame_var _ (running_unwritten _ _)).trans hr)

end Lax263307Proofs.NativeSeparatorTrace

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

theorem root_collection {σ τ:Env} (ha:NativeCollectionAnchor.Anchor σ τ):RootData σ τ:=
  ⟨ha.1 _ (by decide),ha.1 _ (by decide)⟩

theorem collection_protocol {n B D k r p b load F fuel S v limit:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {base σ:Env} {x:Fin n→ ℚ≥0} {parts:List (Finset (Fin n))} {A:Finset (Fin n)}
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front base)
    (hi:NativeCollectionExecution.Invariant B D k r fuel S G x parts A extent front base σ):
    Protocol B D S v cfg extent front σ:=
  ⟨hi.1.bounded,hi.1.lengths,hi.1.stack,hi.1.cursor,hi.1.width,
    (hi.2.1 _ (by decide)).trans hc.frameLength,
    (hi.2.1 _ (by decide)).trans hc.roundWidth,(hi.2.1 _ (by decide)).trans hc.nodeD⟩

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

theorem separator_variable (cfg:Config) (s:String)
    (hf:s∉NativeFullSetMask.command.wvars)
    (ht:s∉NativeCutTest.command.wvars) (hr:s∉NativeCutRecords.command.wvars)
    (hi:s∉["separator.i","separator.count","separator.position","separator.value"])
    (hc:s∉(NativeSeparatorContext.callback cfg.flow cfg.flowWidth).wvars)
    (hp:s∉NativeCutPieces.command.wvars) (he:s∉(NativeComponentControl.start 9).wvars):
    s∉((phases cfg)[8]'(by change 8<16; decide)).wvars:=by
  simpa only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or] using
    (show s∉(Com.seq (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
      (NativeComponentControl.start 9)).wvars from by
        simp only [NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
          NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,not_or]
        simp_all)

theorem separator_array (cfg:Config) (s:String)
    (hf:s∉NativeFullSetMask.command.warrs)
    (ht:s∉NativeCutTest.command.warrs) (hr:s∉NativeCutRecords.command.warrs)
    (hc:s∉(NativeSeparatorContext.callback cfg.flow cfg.flowWidth).warrs)
    (hp:s∉NativeCutPieces.command.warrs):
    s∉((phases cfg)[8]'(by change 8<16; decide)).warrs:=by
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,NativeComponentControl.start,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

theorem separator_frame {n B D k r p b load F fuel S v limit t:ℕ} (cfg:Config)
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ τ:Env} (rr:Run B ((phases cfg)[8]'(by change 8<16; decide)) σ τ t)
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  apply NativeOracleContext.frame rr hc
  · intro s hs
    simp only [scalars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply separator_variable <;> first | decide |
        exact NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)
  · intro s hs
    simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply separator_array <;> first | decide |
        exact NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem near_segment {n r:ℕ} (D k p b load F fuel S v limit M h T w space flowTime childSteps childTime:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (flow:List ℕ→ List ℕ) (x:Fin (NativeCatalogMetadata.N n r)→ ℚ)
    (extent:String→ ℕ) (front:List ℕ)
    (child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card)))
    (bounds:Bounds n r D k p M h T fuel S w cfg extent front)
    (hx:∀ i,NativeSignedArithmetic.Bounded M (x i))
    (hselected:∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A→ A.card≤ r)
    (htarget:∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A→
      ∀ C,ComputedRounding.target (1/(D:ℚ)) (∑ v∈C,(NearOracle.costs (MomentLP.decode x) A v:ℚ))≤ T)
    (hspace:∀ a∈NativeSeparatorContext.workspace,space≤ extent a)
    (flowCall:∀ A,let costs:=NearOracle.costs (MomentLP.decode x) A
      let cs:=cuts (step flow G costs b load k) n Finset.univ
      Spec (2^w) (fun σ => NativeSeparatorContext.Context G costs b load k space σ∧
          n+1≤(σ.arrs "separator.pieces").length)
        (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
        (fun _ τ => NativeSeparatorContext.Context G costs b load k space τ∧
          τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs)∧
          τ.vars "separator.value"=NativeMasks.mask (separator cs)∧ τ.vars "separator.count"=cs.length∧
          Prefix (NativeCutRecords.words cs) "separator.cuts" τ∧ τ.vars "separator.position"=2*cs.length∧
          Prefix (NativeCutPieces.words cs) "separator.pieces" τ) flowTime)
    (recursive:∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A→
      let costs:=NearOracle.costs (MomentLP.decode x) A
      let cs:=cuts (step flow G costs b load k) n Finset.univ
      ∀ i∈NearOracle.order cs.length,
      (1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈pieces cs i,(costs v:ℚ))→ ∀ base σ,
      Protocol (2^w) D S v cfg extent front σ→
      NativeCollectionExecution.Invariant (2^w) D k r fuel S G costs
        ((NearOracle.order cs.length).map (pieces cs)) A extent front base σ→
      NativeRestrictionRead.Data G (fun v => (costs v:ℚ)) (pieces cs i) σ→
      σ.vars "component.mask"=NativeMasks.mask (pieces cs i)→
      σ.vars "component.target"=ComputedRounding.target (1/(D:ℚ)) (∑ v∈pieces cs i,(costs v:ℚ))→
      σ.vars "machine.running"=1→ σ.vars "machine.phase"=11→
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (pieces cs i)
        (ComputedRounding.target (1/(D:ℚ)) (∑ v∈pieces cs i,(costs v:ℚ))) front σ
        (child (pieces cs i) (ComputedRounding.target (1/(D:ℚ)) (∑ v∈pieces cs i,(costs v:ℚ)))))
    (j:ℕ) (state:RoundedOracleSearch.State (NativeCatalogMetadata.N n r)) (σ:Env)
    (hc:Context (2^w) D k r p b load F fuel S v limit cfg G extent front σ)
    (hs:NativeRoundedTrace.StoredState j state σ)
    (hpoint:Prefix (encodeVector x) "lp.word" σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=6):
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ∧
      transitions≤(childSteps+5)*(n+1)+4∧ total≤ timeBound cfg n r M S h childTime flowTime∧
      Context (2^w) D k r p b load F fuel S v limit cfg G extent front τ∧
      NativeRoundedTrace.StoredState j state τ∧
      Output r (run flow G D k p b load (MomentLP.decode x) child) τ∧ RootData σ τ:=by
  obtain ⟨ν,first,hrν,hpν,dataν,choiceν⟩:=NativeNearTrace.conditioning_segment
    (2^w) M n r k p cfg G x bounds.positive bounds.sparsity bounds.height bounds.moment
    bounds.search bounds.masks bounds.rational bounds.quadratic hx bounds.test bounds.floor σ
    hc.moments hpoint hc.target hc.sparsity
    (by rw [hc.lengths]; exact bounds.word) (by rw [hc.lengths]; exact bounds.copy)
    (by rw [hc.lengths]; exact bounds.sum) (by rw [hc.lengths]; exact bounds.moments) hr hp
  have r1:=NativeMachineFrame.single_run first ⟨6,by change 6<16; decide⟩ hp
  change Run (2^w) (.seq NativeMomentStorage.command (.seq NativeHeavySearch.command (go 7))) σ ν _ at r1
  have hcν:=NativeOracleContext.frame r1 hc (by decide) (by decide)
  have hsν:=stored_frame r1 hs (by decide) (by decide)
  cases choice:findHeavyConditioning G k p (MomentLP.decode x) with
  | none =>
    have choice0:NativeHeavySearch.Output (none:Option (Finset (Fin n))) ν:=by simpa [choice] using choiceν
    obtain ⟨τ,last,hout⟩:=NativeNearTrace.none_segment (2^w) n cfg bounds.reply ν hcν.moments.1.1 choice0 hrν hpν
    have r2:=NativeMachineFrame.single_run last ⟨7,by change 7<16; decide⟩ hpν
    change Run (2^w) conditioningReply ν τ _ at r2
    refine ⟨τ,2,_,NativeMachineSegment.append first last,by nlinarith,?_,
      NativeOracleContext.frame r2 hcν (by decide) (by decide),stored_frame r2 hsν (by decide) (by decide),?_,
      root_frame (r1.seq r2) (by decide) (by decide)⟩
    · dsimp only [timeBound]; omega
    · simpa only [run,choice,Output] using hout
  | some A =>
    have choiceA:NativeHeavySearch.Output (some A) ν:=by simpa [choice] using choiceν
    have hA:=hselected A choice
    let costs:=NearOracle.costs (MomentLP.decode x) A
    let cs:=cuts (step flow G costs b load k) n Finset.univ
    have hcs:cs.length≤ n:=NativeSeparatorOutput.cuts_length _ _ _
    obtain ⟨μ,second,hrμ,hpμ,dataμ,costsμ⟩:=NativeNearTrace.some_segment (2^w) M n r cfg G
      (MomentLP.decode x) A bounds.height hA bounds.moment (by have hh:=bounds.search; omega) bounds.masks bounds.rational
      (fun T => hx ((CoordinateCatalog.indexing n r).symm T)) ν dataν choiceA
      (by rw [hcν.lengths]; have hh:=bounds.word; omega) (by rw [hcν.lengths]; exact bounds.costs) hrν hpν
    have r2:=NativeMachineFrame.single_run second ⟨7,by change 7<16; decide⟩ hpν
    change Run (2^w) conditioningReply ν μ _ at r2
    have hcμ:=NativeOracleContext.frame r2 hcν (by decide) (by decide)
    have hsμ:=stored_frame r2 hsν (by decide) (by decide)
    have sepInput:NativeSeparatorContext.Context G costs b load k space μ:=
      ⟨hcμ.moments.1.2.2.2.1,costsμ,hcμ.moments.1.1,hcμ.classB,hcμ.loadValue,hcμ.target,
        fun a ha => by rw [hcμ.lengths]; exact hspace a ha⟩
    obtain ⟨ρ,third,sepρ,piecesρ,countρ,indexρ,unionρ,hrρ,hpρ⟩:=NativeSeparatorTrace.separator_segment
      (2^w) b load k space flowTime cfg G costs cs (flowCall A) (by have hh:=bounds.reply; omega) μ sepInput
      (by rw [hcμ.lengths]; exact bounds.pieces) hrμ hpμ
    have r3:=NativeMachineFrame.single_run third ⟨8,by change 8<16; decide⟩ hpμ
    have hcρ:=separator_frame cfg r3 hcμ
    have hsρ:=stored_frame r3 hsμ
      ⟨separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide),
        separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)⟩
      ⟨separator_array cfg _ (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide),
        separator_array cfg _ (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)⟩
    have conditioningρ:ρ.vars "conditioning.choice"=NativeMasks.mask A:=by
      apply (r3.frame_var _ (separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
        (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide))).trans
      exact (r2.frame_var _ (by decide)).trans choiceA.2
    have collectionInput:NativeCollectionContext.Context (2^w) D k r fuel S G costs
        ((NearOracle.order cs.length).map (pieces cs)) A extent front ρ:=by
      refine ⟨hcρ.moments.1.1,hcρ.moments.1.2.2.2.1,sepρ.costs,?_,?_,hcρ.denominator,
        hcρ.target,hcρ.moments.1.2.1,hcρ.moments.1.2.2.1,conditioningρ,
        hcρ.bounded,hcρ.lengths,hcρ.stack,hcρ.cursor,hcρ.stride,hcρ.depth⟩
      · simpa only [List.map_map,Function.comp_def] using piecesρ
      · simpa [NearOracle.order] using countρ
    have hcost:∀ v,NativeSignedArithmetic.Bounded (2^h) (costs v:ℚ):=by
      intro v
      have hh:=NativeNearCosts.height M n r (MomentLP.decode x) A bounds.height hA
        (fun T => hx ((CoordinateCatalog.indexing n r).symm T)) v
      exact ⟨hh.1.trans bounds.costHeight,hh.2.trans bounds.costHeight⟩
    obtain ⟨τ,s,t,last,hsLast,htLast,out⟩:=NativeCollectionExecution.collect_segment
      D k r fuel S h T childSteps childTime cfg G costs (pieces cs) (NearOracle.order cs.length) A
      extent front ρ child (NativeCollectionSemantics.order_complete _) bounds.positive bounds.denominator
      hcost w bounds.component (by simp [NearOracle.order]; omega) bounds.masks
      (by have hb:=bounds.collection; simp only [NearOracle.order,List.length_cons,List.length_map,List.length_finRange]; omega)
      (fun i _ => htarget A choice (pieces cs i)) bounds.frameExtents bounds.stack bounds.child bounds.graph
      bounds.bits bounds.labels (by have hh:=bounds.word; omega) (by have hn:=bounds.positive; have hh:=bounds.sum; nlinarith)
      bounds.input bounds.normal
      (fun i hi heavy σ hσ hd hm ht hr hp => recursive A choice i hi heavy ρ σ
        (NativeOracleContext.collection_protocol hcρ hσ) hσ hd hm ht hr hp)
      ρ ⟨⟨collectionInput,NativeCollectionAnchor.refl ρ⟩,indexρ,by simpa [NativeMasks.mask,NativeCatalog.subsetMask] using unionρ,hrρ,hpρ⟩
    have hcτ:=NativeOracleContext.collection hcρ last out.1.2 out.1.1.order out.1.1.stack out.1.1.cursor
    have hsτ:=NativeCollectionAnchor.stored_state out.1.2 hsρ
    refine ⟨τ,_,_,NativeMachineSegment.append first (NativeMachineSegment.append second
        (NativeMachineSegment.append third last)),?_,?_,hcτ,hsτ,?_,?_⟩
    · simp only [NearOracle.order,List.length_cons,List.length_map,List.length_finRange] at hsLast
      nlinarith only [hsLast,hcs]
    · dsimp only [timeBound]
      have ht:=Nat.mul_le_mul_left (NativeCollectionExecution.partCost cfg n r S h childTime)
        (Nat.add_le_add_right hcs 1)
      simp only [NearOracle.order,List.length_cons,List.length_map,List.length_finRange] at htLast
      omega
    · dsimp only [run]
      rw [choice]
      change Output r (match ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D:ℚ)) k
        (fun i => ∑ v∈pieces cs i,(costs v:ℚ))
        (fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))) with
        | .found I => .found I | .cut C u => .cut A C u) τ
      cases he:ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D:ℚ)) k
        (fun i => ∑ v∈pieces cs i,(costs v:ℚ))
        (fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))) <;>
        simpa only [NativeCollectionTrace.ResultOutput,he,Output] using out.2
    · apply RootData.trans (root_frame (r1.seq r2) (by decide) (by decide))
      apply RootData.trans (root_frame r3 ?_ ?_) (root_collection out.1.2)
      all_goals
        exact separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)

end Lax263307Proofs.NativeNearExecution

end

theorem solution:∀ {n r:Nat} (D k p b load F fuel S v limit M h T w space flowTime childSteps childTime:Nat)
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
            Nat.le (@Finset.card (Fin n) A) r)→
        (∀ (A:Finset (Fin n)),
            @Eq (Option (Finset (Fin n)))
                (@Lax263307.HeavyRationalConditioning.findHeavyConditioning n r G inst k p
                  (@Lax263307.MomentLP.decode Rat n r x))
                (@Option.some (Finset (Fin n)) A)→
              ∀ (C:Finset (Fin n)),
                Nat.le
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
                Nat.le space (extent a))→
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
                      (Nat.le
                        (Nat.add n
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
                                  (Nat.mul
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
                                  (Nat.le transitions
                                    (Nat.add
                                      (Nat.mul
                                        (Nat.add childSteps
                                          ((5:Nat)))
                                        (Nat.add n
                                          ((1:Nat))))
                                      ((4:Nat))))
                                  (And
                                    (Nat.le total
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
                                          (Lax263307Proofs.NativeOracleContext.RootData σ τ)))))):= @Lax263307Proofs.NativeNearExecution.near_segment
