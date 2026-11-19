-- Prove2me | solution 1 for Lax455465Proofs.RamUniformRounding.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:18:08.388835+00:00
-- url     : https://prove2.me/submissions/e033db02-1d7a-40d1-be2a-f0f0f3b2d006

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.List.FinRange
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native
import Theorems.Thm_Lax455465Proofs_RamRegionBoundedLoop_command_spec_native
import Theorems.Thm_Lax455465Proofs_RamRegionCut_command_spec_native

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
namespace Lax455465Proofs.RamRegionBoundedLoop
end Lax455465Proofs.RamRegionBoundedLoop
theorem Lax455465Proofs.RamRegionBoundedLoop.command_spec:∀ (B M H:Nat) {n:Nat} (I:Lax455465.RationalEncoding.RationalInstance n)
  (length:Lax455465Proofs.MetricMatrix.Matrix n) (seed beta delta threshold:NNRat) (p:Nat),
  LE.le ((1:Nat)) M→
    LE.le (Lax455465Proofs.RegionBudget.steps p) M→
      LT.lt
          (HAdd.hAdd
            (HMul.hMul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                ((2:Nat))))
            ((3:Nat)))
          B→
        LT.lt
            (HAdd.hAdd
              (HMul.hMul
                ((2:Nat))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) H)
                  ((2:Nat))))
              ((3:Nat)))
            B→
          LT.lt
              (HAdd.hAdd
                (HMul.hMul
                  ((2:Nat))
                  (HMul.hMul n n))
                ((2:Nat)))
              B→
            LT.lt
                (HAdd.hAdd
                  (HMul.hMul
                    ((2:Nat)) n)
                  ((2:Nat)))
                B→
              LT.lt
                  (HAdd.hAdd
                    (HMul.hMul
                      ((2:Nat))
                      (HAdd.hAdd
                        (HAdd.hAdd (Lax455465Proofs.RegionBudget.steps p)
                          ((1:Nat)))
                        (HMul.hMul
                          ((2:Nat)) n)))
                    ((2:Nat)))
                  B→
                LT.lt
                    (HAdd.hAdd
                      (HMul.hMul
                        ((4:Nat)) p)
                      ((4:Nat)))
                    B→
                  Lax455465Proofs.LpInputSize.Height
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) H)
                      (@NNRat.cast Rat Rat.instNNRatCast threshold)→
                    (∀ (v:Fin n),
                        LE.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).num M)→
                      (∀ (v:Fin n),
                          LE.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).den M)→
                        (∀ (u v:Fin n),
                            LE.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).num
                              M)→
                          (∀ (u v:Fin n),
                              LE.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).den
                                M)→
                            (∀ (u v:Fin n),
                                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v)))→
                              Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                Lax455465Proofs.LpInputSize.Height M
                                    (@NNRat.cast Rat Rat.instNNRatCast
                                      (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                                        (@Nat.cast NNRat
                                          (@AddMonoidWithOne.toNatCast NNRat
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                              (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                                (@Semiring.toNonAssocSemiring NNRat
                                                  (@DivisionSemiring.toSemiring NNRat
                                                    (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                                          (Lax455465Proofs.RegionBudget.steps p))))→
                                  (∀ (active:Finset (Fin n)) (root:Fin n) (i:Nat)
                                      (hi:
                                        LT.lt i
                                          (@List.length NNRat
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta))),
                                      @Lax455465Proofs.RegionQueryHeight.Bounds n
                                        (@Lax455465Proofs.RadiusSearchData.atRadius n
                                          (@Lax455465Proofs.RegionExecutionData.query n I length active root seed beta)
                                          (@GetElem.getElem (List NNRat) Nat NNRat
                                            (fun (as:List NNRat) (i:Nat) =>
                                              LT.lt i (@List.length NNRat as))
                                            (@List.instGetElemNatLtLength NNRat)
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta)
                                            i hi))
                                        H)→
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast beta)
                                        (Lax455465Proofs.RegionSearch.slope (Lax455465Proofs.RegionBudget.steps p)
                                          (@NNRat.cast Rat Rat.instNNRatCast delta))→
                                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                          (@NNRat.cast Rat Rat.instNNRatCast seed)→
                                        @LT.lt Rat Rat.instLT
                                            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                            (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                          LT.lt ((0:Nat))
                                              p→
                                            (∀ (v:Fin n),
                                                @Eq NNRat (length v v)
                                                  (@OfNat.ofNat NNRat (nat_lit 0)
                                                    (@Zero.toOfNat0 NNRat
                                                      (@MulZeroClass.toZero NNRat
                                                        (@instMulZeroClassOfSemiring NNRat
                                                          (@DivisionSemiring.toSemiring NNRat
                                                            (@Semifield.toDivisionSemiring NNRat
                                                              NNRat.instSemifield)))))))→
                                              (∀ (u v w:Fin n),
                                                  @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (length u w))
                                                    (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                                      (@NNRat.cast Rat Rat.instNNRatCast (length u v))
                                                      (@NNRat.cast Rat Rat.instNNRatCast (length v w))))→
                                                @LE.le Rat Rat.instLE
                                                    (@Lax455465Proofs.RegionRounding.metricCost n I
                                                      (@Lax455465Proofs.MetricMatrix.rational n length))
                                                    (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                      (@Nat.cast Rat Rat.instNatCast p)
                                                      (@NNRat.cast Rat Rat.instNNRatCast seed))→
                                                  LE.le
                                                      (@Finset.card (Fin n)
                                                        (@Lax455465Proofs.RegionSelection.support n
                                                          (@Lax455465Proofs.RegionLoop.weights n I
                                                            (@Finset.univ (Fin n) (Fin.fintype n)))))
                                                      p→
                                                    Lax808846Proofs.Reasoning.Spec B
                                                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                                                        And
                                                          (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed
                                                            beta delta threshold p σ)
                                                          (And (Lax455465Proofs.RamRegionInvariant.Room n p σ)
                                                            (And
                                                              (@Eq Nat (σ.vars "loop.limit")
                                                                (HAdd.hAdd p
                                                                  ((1:Nat))))
                                                              (@Lax455465Proofs.RamRegionState.View n I length seed beta
                                                                (Lax455465Proofs.RamRegionBoundedLoop.initial n) σ))))
                                                      Lax455465Proofs.RamRegionScan.command
                                                      (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                                        And
                                                          (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed
                                                            beta delta threshold p τ)
                                                          (And (Lax455465Proofs.RamRegionInvariant.Room n p τ)
                                                            (@Lax455465Proofs.RamRegionState.View n I length seed beta
                                                              (@Nat.iterate (Lax455465Proofs.RegionRuntimeState.State n)
                                                                (@Lax455465Proofs.RegionRuntimeState.advance n I length
                                                                  seed beta delta threshold p)
                                                                (HAdd.hAdd p
                                                                  ((1:Nat)))
                                                                (Lax455465Proofs.RamRegionBoundedLoop.initial n))
                                                              τ)))
                                                      (Lax455465Proofs.RamRegionBoundedLoop.cost n p M H):= @Lax455465Proofs.RamRegionBoundedLoop.command_spec_native
namespace Lax455465Proofs.RamRegionCut
end Lax455465Proofs.RamRegionCut
theorem Lax455465Proofs.RamRegionCut.command_spec:∀ (B M:Nat) {n:Nat} (I:Lax455465.RationalEncoding.RationalInstance n) (d:Lax455465Proofs.MetricMatrix.Matrix n)
  (seed beta delta threshold:NNRat) (p:Nat) (s:Lax455465Proofs.RegionRuntimeState.State n),
  LE.le ((1:Nat)) M→
    LE.le
        (HMul.hMul ((2:Nat)) p)
        M→
      LT.lt
          (HAdd.hAdd
            (HMul.hMul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                ((2:Nat))))
            ((3:Nat)))
          B→
        LT.lt ((4:Nat)) B→
          LT.lt
              (HAdd.hAdd
                (HMul.hMul
                  ((4:Nat)) p)
                ((4:Nat)))
              B→
            LT.lt
                (HAdd.hAdd
                  (HMul.hMul
                    ((2:Nat))
                    (HMul.hMul n n))
                  ((2:Nat)))
                B→
              LT.lt
                  (HAdd.hAdd
                    (HMul.hMul
                      ((2:Nat)) n)
                    ((2:Nat)))
                  B→
                (∀ (u w:Fin n),Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (d u w)))→
                  (∀ (e:Lax455465Proofs.RamRegionRecord.Entry n),
                      @Membership.mem (Lax455465Proofs.RamRegionRecord.Entry n)
                          (List (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@List.instMembership (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@Lax455465Proofs.RegionRuntimeState.State.history n s) e→
                        Lax455465Proofs.LpInputSize.Height M
                          (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465Proofs.RamRegionRecord.Entry.radius n e)))→
                    (∀ (Tin Tout:Finset (Fin n)) (hin:@Finset.Nonempty (Fin n) Tin)
                        (hout:@Finset.Nonempty (Fin n) Tout),
                        @Lax455465Proofs.LargePotentialData.Bounds n I d Tin Tout hin hout M)→
                      (∀ (S:Finset (Fin n)), @Lax455465Proofs.CutScoreHeight.Bounds n I S M)→
                        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                            (@Lax455465Proofs.LargeBallRounding.total n I)→
                          LT.lt ((0:Nat)) p→
                            (∀ (v:Fin n),
                                @Eq NNRat (d v v)
                                  (@OfNat.ofNat NNRat (nat_lit 0)
                                    (@Zero.toOfNat0 NNRat
                                      (@MulZeroClass.toZero NNRat
                                        (@instMulZeroClassOfSemiring NNRat
                                          (@DivisionSemiring.toSemiring NNRat
                                            (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))→
                              @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                  (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                                    (@Lax455465Proofs.MetricMatrix.rational n d))→
                                (∀ (u v w:Fin n),
                                    @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u w))
                                      (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                        (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                                        (@NNRat.cast Rat Rat.instNNRatCast (d v w))))→
                                  @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast seed)
                                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                        (@Lax455465Proofs.RegionRounding.metricCost n I
                                          (@Lax455465Proofs.MetricMatrix.rational n d))
                                        (@Nat.cast Rat Rat.instNatCast p))→
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast delta)
                                        (@Lax455465Proofs.RegionRounding.radiusBudget n I)→
                                      @Lax455465Proofs.RegionRuntimeCorrespondence.ValidFinal n I d seed delta p s→
                                        Lax808846Proofs.Reasoning.Spec B
                                          (fun (σ:Lax808846Proofs.Imp.Env) =>
                                            And
                                              (@Lax455465Proofs.RamRegionInvariant.Fixed n I d seed beta delta threshold
                                                p σ)
                                              (And (@Lax455465Proofs.RamRegionState.View n I d seed beta s σ)
                                                (And
                                                  (Lax455465Proofs.RamUnsignedScalar.Stored "round.total"
                                                    (@Lax455465Proofs.RamRoundingInit.total n
                                                      (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                                    σ)
                                                  (Lax455465Proofs.RamRegionCut.Room n σ))))
                                          Lax455465Proofs.RamRegionCut.command
                                          (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                            @Lax455465Proofs.RamRegionCut.Output n I d p τ)
                                          (Lax455465Proofs.RamRegionCut.cost n p M):= @Lax455465Proofs.RamRegionCut.command_spec_native

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

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem member_bound (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x < 2 ^ bitSize xs:=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have:=member_size xs x hx; omega))

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

namespace Lax455465Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def leFlag (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then
    if s₁=1 then (if n₁ * d₂ < n₂ * d₁ then 0 else 1)
    else (if n₂ * d₁ < n₁ * d₂ then 0 else 1)
  else if s₁=1 then 1
  else if n₁=0 then (if n₂=0 then 1 else 0) else 0

theorem leFlag_le_one (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):leFlag s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by
  unfold leFlag
  split_ifs <;> omega

theorem leFlag_correct (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    leFlag s₁ n₁ d₁ s₂ n₂ d₂=1↔
      fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂:=by
  have hd₁q:(0:ℚ) < d₁:=by exact_mod_cast hd₁
  have hd₂q:(0:ℚ) < d₂:=by exact_mod_cast hd₂
  have hpos₁:(0:ℚ)≤ (n₁:ℚ) / d₁:=by positivity
  have hpos₂:(0:ℚ)≤ (n₂:ℚ) / d₂:=by positivity
  have hcross:(n₁:ℚ) / d₁≤ (n₂:ℚ) / d₂↔ n₁ * d₂≤ n₂ * d₁:=by
    rw [div_le_div_iff₀ hd₁q hd₂q]
    exact_mod_cast Iff.rfl
  have hcrossRev:(n₂:ℚ) / d₂≤ (n₁:ℚ) / d₁↔ n₂ * d₁≤ n₁ * d₂:=by
    rw [div_le_div_iff₀ hd₂q hd₁q]
    exact_mod_cast Iff.rfl
  have hzero:(n₁:ℚ) / d₁≤ -((n₂:ℚ) / d₂)↔ n₁=0∧ n₂=0:=by
    constructor
    · intro h
      have hz₁:(n₁:ℚ) / d₁=0:=by linarith
      have hz₂:(n₂:ℚ) / d₂=0:=by linarith
      simpa [div_eq_zero_iff,ne_of_gt hd₁q,ne_of_gt hd₂q] using And.intro hz₁ hz₂
    · rintro ⟨rfl,rfl⟩; simp
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl
  · simp [leFlag,fractionValue,hcross]
  · simp [leFlag,fractionValue,neg_div,hzero]
    split_ifs <;> simp_all
  · simp [leFlag,fractionValue,neg_div]
    linarith
  · simp [leFlag,fractionValue,neg_div,hcrossRev]

set_option maxHeartbeats 0 in
theorem compareFraction_flag_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le"=leFlag s₁ n₁ d₁ s₂ n₂ d₂) 40:=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have huB:n₁ * d₂ < B:=(Nat.mul_le_mul hn₁ hd₂).trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=(Nat.mul_le_mul hn₂ hd₁).trans_lt (by nlinarith)
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "cmp.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "cmp.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat→ Prop:= @Eq Nat c9; let c11:Nat:=c8 "right.s"; let c12:Prop:=c10 c11; let c13:Prop:=Not c12; let c14:Nat:=leFlag s₁ n₁ d₁ s₂ n₂ d₂; let c15:Env→ Prop:=(fun (x σ':Env) => @Eq Nat (Env.vars σ' "cmp.le") c14) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B compareFraction σ σ' ((40:Nat))) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Prop:=c10 ((1:Nat)); let c19:Prop:=Not c18; let c20:Nat:=c8 "cmp.u"; let c21:Nat→ Prop:=Nat.lt c20; let c22:Nat:=c8 "cmp.v"; let c23:Prop:=c21 c22; let c24:Prop:=Not c23; let c25:Nat→ Env:=Env.setVar c7 "cmp.le"; let c26:Env:=c25 ((0:Nat)); let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Nat→ Nat:=c27 ((1:Nat)); let c29:Nat:=c28 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c30:Nat→ Nat:=c27 c29; let c31:Nat:=c28 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c32:Nat→ Nat:=c27 c31; let c33:Nat→ Nat:=c27 (c28 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c34:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c35:Nat→ Nat:=c27 (c28 (Cond.size c34)); let c36:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")))); let c37:Nat:=c28 (Expr.size (Expr.lit ((0:Nat)))); let c38:Nat:=c36 c37; let c39:Nat:=c35 c38; let c40:Nat:=c33 c39; let c41:Nat:=c32 c40; let c42:Com:=Com.assign "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c43:Com→ Com→ Com:=Com.ite c34; let c44:Com:=Com.assign "cmp.le" (Expr.lit ((0:Nat))); let c45:Com:=Com.assign "cmp.le" (Expr.lit ((1:Nat))); let c46:Com:=Com.ite (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45; let c47:Com:=Com.ite (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45; let c48:Com:=c43 c46 c47; let c49:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c50:Cond:=Cond.eq (Expr.var "right.n") (Expr.lit ((0:Nat))); let c51:Com:=Com.ite c50 c45 c44; let c52:Com:=Com.ite c49 c51 c44; let c53:Com:=c43 c45 c52; let c54:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53; let c55:Nat→ Prop:=Nat.lt c22; let c56:Env:=c25 ((1:Nat)); let c57:Nat:=c28 (Expr.size (Expr.lit ((1:Nat)))); let c58:Nat:=c36 c57; let c59:Nat:=c35 c58; let c60:Nat:=c33 c59; let c61:Nat:=c32 c60; let c62:Prop:=c55 c20; let c63:Prop:=Not c62; let c64:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")))); let c65:Nat:=c64 c37; let c66:Nat:=c35 c65; let c67:Nat:=c33 c66; let c68:Nat:=c32 c67; let c69:Nat:=c64 c57; let c70:Nat:=c35 c69; let c71:Nat:=c33 c70; let c72:Nat:=c32 c71; let c73:Nat:=c35 c57; let c74:Nat:=c33 c73; let c75:Nat:=c32 c74; let c76:Nat:=c8 "left.n"; let c77:Prop:= @Eq Nat c76 ((0:Nat)); let c78:Prop:=Not c77; let c79:Nat:=c8 "right.n"; let c80:Prop:= @Eq Nat c79 ((0:Nat)); let c81:Prop:=Not c80; let c82:Nat→ Nat:=c27 (c28 (Cond.size c49)); let c83:Nat→ Nat:=c27 (c28 (Cond.size c50)); let c84:Nat:=c83 c57; let c85:Nat:=c82 c84; let c86:Nat:=c35 c85; let c87:Nat:=c33 c86; let c88:Nat:=c32 c87; let c89:Nat:=c83 c37; let c90:Nat:=c82 c89; let c91:Nat:=c35 c90; let c92:Nat:=c33 c91; let c93:Nat:=c32 c92; let c94:Nat:=c82 c37; let c95:Nat:=c35 c94; let c96:Nat:=c33 c95; let c97:Nat:=c32 c96; @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c17) (Classical.em c12) (fun (hcase:c12) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Or.casesOn c23 c24 (fun (x:Or c23 c24) => c17) (Classical.em c23) (fun (hcase_2:c23) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c41) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c41 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_1)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c40 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_3)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c39 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_5)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c26 c38 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_7)))))))) (?nAX_g5438_0_0_8)) ?_)) fun (hcase_2:c24) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c61) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c61 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_9)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_10)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c60 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_11)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_12)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c59 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_13)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_14)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c56 c58 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_15)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_16)) ?_)) fun (hcase_1:c19) => @Or.casesOn c62 c63 (fun (x:Or c62 c63) => c17) (Classical.em c62) (fun (hcase_2:c62) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c68) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c68 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_17)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_18)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c67 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_19)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_20)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c66 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_21)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_22)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c26 c65 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_23)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_24)))))))) (?nAX_g5438_0_0_25)) ?_)) fun (hcase_2:c63) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c72) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c72 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_26)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_27)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c71 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_28)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_29)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c70 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_30)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_31)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c56 c69 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_33)) ?_)) fun (hcase:c13) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c75) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c75 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_34)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_35)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c74 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_36)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_37)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c73 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_38)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_39)) hcase) (RunStep.ite_true B c34 c45 c52 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))) (?nAX_g5438_0_0_41)) ?_)) fun (hcase_1:c19) => @Or.casesOn c77 c78 (fun (x:Or c77 c78) => c17) (Classical.em c77) (fun (hcase_2:c77) => @Or.casesOn c80 c81 (fun (x:Or c80 c81) => c17) (Classical.em c80) (fun (hcase_3:c80) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c88) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c88 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_42)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_43)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c87 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_44)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_45)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c86 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_46)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_47)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c56 c85 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_48)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c56 c84 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_49)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_50)) hcase_2) (RunStep.ite_true B c50 c45 c44 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_51)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_52)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))))) (?nAX_g5438_0_0_53)) ?_)) fun (hcase_3:c81) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c93) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c93 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_54)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_55)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c92 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_56)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_57)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c91 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_58)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_59)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c90 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_60)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c26 c89 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_61)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_62)) hcase_2) (RunStep.ite_false B c50 c45 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_63)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_64)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_65))))))))) (?nAX_g5438_0_0_66)) ?_)) fun (hcase_2:c78) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c97) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c97 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_67)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_68)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c96 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_69)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_70)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c95 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_71)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_72)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c94 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_73)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B c49 c51 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_74)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_75)) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_76)))))))) (?nAX_g5438_0_0_77)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5438_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [leFlag]

theorem compareFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le" ≤ 1∧
        (σ'.vars "cmp.le"=1↔ fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂)) 40:=by
  apply (compareFraction_flag_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂).post
  intro σ τ _ ht
  rw [ht]
  exact ⟨leFlag_le_one _ _ _ _ _ _,leFlag_correct _ _ _ _ _ _ hs₁ hs₂ hd₁pos hd₂pos⟩

end Lax455465Proofs.RamComparison

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

theorem numerator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i]?=some qs[i].num:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)=Nat.succ (Nat.succ (2*i)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem denominator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i+1]?=some qs[i].den:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)+1=Nat.succ (Nat.succ (2*i+1)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem read_spec (B:ℕ) (array index:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s"):
    Spec B (fun σ => Prefix (encode qs) array σ∧ σ.vars index=i) (read array index)
      (fun _ τ => FractionOutput (qs[i]:ℚ) τ∧ τ.vars "rat.s"=0) 14:=by
  have hnum:=numerator_at qs i hi
  have hden:=denominator_at qs i hi
  rintro σ ⟨hp,hv⟩
  have hni:2*i < (encode qs).length:=by simp only [length_encode]; omega
  have hdi:2*i+1 < (encode qs).length:=by simp only [length_encode]; omega
  have hnumval:(encode qs)[2*i]=qs[i].num:=by simpa only [List.getElem?_eq_getElem hni,Option.some.injEq] using hnum
  have hdenval:(encode qs)[2*i+1]=qs[i].den:=by simpa only [List.getElem?_eq_getElem hdi,Option.some.injEq] using hden
  have hgN:=(hp (2*i) hni).trans (congrArg some hnumval)
  have hgD:=(hp (2*i+1) hdi).trans (congrArg some hdenval)
  have hN:2*i < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgN; cases hgN
  have hD:2*i+1 < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgD; cases hgD
  have hni':i < B:=by omega
  have hmul:2*i < B:=by omega
  have hvalue:fractionValue 0 qs[i].num qs[i].den=(qs[i]:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den qs[i])
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (@getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i_1:Nat) => Nat.lt i_1 (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) qs i hi)); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (@Eq Nat (Env.vars τ "rat.s") ((0:Nat)))) σ; let c2:Nat→ Nat:=Nat.mul ((2:Nat)); let c3:Nat:=c2 (Env.vars σ index); let c4:Nat:= @List.getD Nat (Env.arrs σ array) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "rat.n" c4; let c6:List Nat:=Env.arrs c5 array; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Env.vars c5 index; let c9:Nat:=c2 c8; let c10:Nat:=c7 c9 ((1:Nat)); let c11:Nat:= @List.getD Nat c6 c10 ((0:Nat)); let c12:Env:=Env.setVar c5 "rat.d" c11; let c13:Env:=Env.setVar c12 "rat.s" ((0:Nat)); let c14:Nat→ Nat:=c7 ((1:Nat)); let c15:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var index); let c16:Expr:=Expr.get array c15; let c17:Nat:=c14 (Expr.size c16); let c18:Expr:=Expr.add c15 (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c14 (Expr.size c19); let c21:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c22:Nat:=c7 c20 c21; let c23:Com:=Com.assign "rat.d" c19; let c24:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c25:Nat→ Prop:=Nat.lt c10; @Exists.intro Env (fun (σ':Env) => And (Run B (read array index) σ σ' ((14:Nat))) (c1 σ')) c13 (@And.intro (Run B (read array index) σ c13 ((14:Nat))) (c1 c13) (RunStep.mono B (read array index) σ c13 (c7 c17 c22) ((14:Nat)) (RunStep.seq B (Com.assign "rat.n" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "rat.n" c16 c4 (RunStep.eval_get B σ array c15 c3 (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) (Env.vars σ index) (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_var B σ index (?nAX_g5778_0_0_0)) (?nAX_g5778_0_0_1)) (?nAX_g5778_0_0_2) ?_)) (RunStep.seq B c23 c24 c5 c12 c13 c20 c21 (RunStep.assign B c5 "rat.d" c19 c11 (RunStep.eval_get B c5 array c18 c10 (RunStep.eval_add B c5 c15 (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_mul B c5 (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) c8 (RunStep.eval_lit B ((2:Nat)) c5 h2) (RunStep.eval_var B c5 index ?_) ?_) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g5778_0_0_3)) ?_) ?_ ?_)) (RunStep.assign B c12 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c12 (?nAX_g5778_0_0_4))))) (?nAX_g5778_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5778_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

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

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowLP

open Lax455465.RationalEncoding Lax109476.LinearProgram

def vector {n:ℕ} (f:ℚ) (x:CommodityArc n→ ℚ):
    Fin (1 + (n * n) * (n * n))→ ℚ:=
  fun j => match (variableIndex n).symm j with
    | .inl _ => f
    | .inr a => x a

end Lax455465Proofs.DirectedFlowLP

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

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem edge_value {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val=s.val * n + t.val:=by
  simp [edgeIndex,finProdFinEquiv]
  ring

private theorem code_div (a b n:ℕ) (hn:0 < n) (hb:b < n):
    (a * n + b) / n=a:=by
  rw [Nat.add_comm,Nat.add_mul_div_right b a hn,Nat.div_eq_of_lt hb,Nat.zero_add]

private theorem code_mod (a b n:ℕ) (hb:b < n):(a * n + b) % n=b:=by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem edge_div {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val / n=s.val:=by
  rw [edge_value]
  exact code_div _ _ _ ((Nat.zero_le t.val).trans_lt t.isLt) t.isLt

theorem edge_mod {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val % n=t.val:=by
  rw [edge_value]
  exact code_mod _ _ _ t.isLt

end Lax455465Proofs.FlowLpIndices

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

open scoped NNRat

namespace Lax455465Proofs.InstanceParser

open Lax455465.RationalEncoding Lax455465.ProductNetwork

theorem encoded_length (qs:List ℚ≥0):(qs.flatMap encodeRational).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [List.flatMap_cons,encodeRational,ih]; omega

end Lax455465Proofs.InstanceParser

end

section

namespace Lax455465Proofs.LpInputSize

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding DirectedFlowLP
open scoped NNRat

theorem height_zero {M:ℕ} (hM:1≤ M):Height M 0:=by simp [Height]; omega

theorem height_one {M:ℕ} (hM:1≤ M):Height M 1:=by simp [Height]; omega

theorem height_neg {M:ℕ} {q:ℚ} (h:Height M q):Height M (-q):=by simpa [Height] using h

theorem height_mono {M N:ℕ} {q:ℚ} (h:Height M q) (hmn:M≤ N):Height N q:=
  ⟨h.1.trans hmn,h.2.trans hmn⟩

theorem height_mul {M N:ℕ} {q r:ℚ} (hq:Height M q) (hr:Height N r):
    Height (M * N) (q * r):=by
  constructor
  · rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1)
  · rw [Rat.mul_den]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hq.2 hr.2)

theorem input_dimension {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    n≤ bitSize (encodeInput kind I):=by
  apply le_trans (b:=(encodeInput kind I).length) _ (WordSize.length_le _)
  simp only [encodeInput,List.length_append,InstanceParser.encoded_length,List.length_ofFn,
    List.length_cons,List.length_nil]
  omega

theorem weight_members {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u:Fin n)
    (x:ℕ) (hx:x∈ encodeRational (I.weight u)):x∈ encodeInput kind I:=by
  simp only [encodeInput,List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  exact ⟨I.weight u,List.mem_ofFn.mpr ⟨u,rfl⟩,hx⟩

theorem capacity_members {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u v:Fin n)
    (x:ℕ) (hx:x∈ encodeRational (I.capacity u v)):x∈ encodeInput kind I:=by
  simp only [encodeInput,List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨I.capacity u v, ?_,hx⟩
  apply List.mem_flatten.mpr
  exact ⟨List.ofFn (I.capacity u),List.mem_ofFn.mpr ⟨u,rfl⟩,List.mem_ofFn.mpr ⟨v,rfl⟩⟩

theorem weight_height {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u:Fin n):
    Height (2 ^ bitSize (encodeInput kind I)) (I.weight u:ℚ):=by
  have hn:=WordSize.member_bound (encodeInput kind I) (I.weight u).num
    (weight_members kind I u _ (by simp [encodeRational]))
  have hd:=WordSize.member_bound (encodeInput kind I) (I.weight u).den
    (weight_members kind I u _ (by simp [encodeRational]))
  exact ⟨by simpa only [NNRat.natAbs_num_coe] using hn.le,by simpa only [NNRat.den_coe] using hd.le⟩

theorem capacity_height {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u v:Fin n):
    Height (2 ^ bitSize (encodeInput kind I)) (I.capacity u v:ℚ):=by
  have hn:=WordSize.member_bound (encodeInput kind I) (I.capacity u v).num
    (capacity_members kind I u v _ (by simp [encodeRational]))
  have hd:=WordSize.member_bound (encodeInput kind I) (I.capacity u v).den
    (capacity_members kind I u v _ (by simp [encodeRational]))
  exact ⟨by simpa only [NNRat.natAbs_num_coe] using hn.le,by simpa only [NNRat.den_coe] using hd.le⟩

theorem divergence_height {n:ℕ} (I:RationalInstance n) (M:ℕ) (hM:1≤ M)
    (hw:∀ u,Height M (I.weight u:ℚ)) (s t u:Fin n):
    Height (M * M) (divergence I s t u):=by
  have hMM:1≤ M * M:=by nlinarith
  have hm:=height_mul (hw s) (hw t)
  by_cases hst:s=t
  · simpa only [divergence,if_pos hst] using height_zero hMM
  by_cases hus:u=s
  · have hut:u ≠ t:=by intro he; exact hst (hus.symm.trans he)
    simpa [divergence,hst,hus,hut,Ne.symm hst] using hm
  · by_cases hut:u=t
    · simpa [divergence,hst,hus,hut,Ne.symm hst] using height_neg hm
    · simpa [divergence,hst,hus,hut,Ne.symm hst] using height_zero hMM

theorem balance_height {n:ℕ} (I:RationalInstance n) (M:ℕ) (hM:1≤ M)
    (hw:∀ u,Height M (I.weight u:ℚ)) (b:Balance n) (v:Variable n):
    Height (M * M) (balanceCoefficient I b v):=by
  have hMM:1≤ M * M:=by nlinarith
  cases v with
  | inl _ => exact height_neg (divergence_height I M hM hw _ _ _)
  | inr a =>
    simp only [balanceCoefficient]
    split_ifs <;>
      first | simpa only [sub_self,sub_zero,zero_sub] using height_zero hMM
            | simpa only [sub_self,sub_zero,zero_sub] using height_one hMM
            | simpa only [sub_self,sub_zero,zero_sub] using height_neg (height_one hMM)

theorem coefficient_height {n:ℕ} (I:RationalInstance n) (M:ℕ) (hM:1≤ M)
    (hw:∀ u,Height M (I.weight u:ℚ)) (r:Row n) (v:Variable n):
    Height (M * M) (coefficient I r v):=by
  have hMM:1≤ M * M:=by nlinarith
  cases r with
  | inl e =>
    cases v with
    | inl _ => exact height_zero hMM
    | inr a =>
      simp only [coefficient]
      split_ifs <;> first | exact height_one hMM | exact height_zero hMM
  | inr sb =>
    simp only [coefficient]
    split_ifs
    · exact balance_height I M hM hw _ _
    · exact height_neg (balance_height I M hM hw _ _)

end Lax455465Proofs.LpInputSize

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

namespace Lax455465Proofs.RamHostBounds

def sufficient (w time allowance inputLength:ℕ):ℕ:=
  2 * w + time + allowance + inputLength + 8

theorem sufficient_bounds (w time allowance inputLength W:ℕ)
    (hW:sufficient w time allowance inputLength≤ W):
    2 * (2 ^ w) ^ 2 + 3 < 2 ^ W∧ time + 1 < 2 ^ W∧
      allowance < 2 ^ W∧ inputLength + 1 < 2 ^ W:=by
  have hshift:2 * w + 4≤ W:=by unfold sufficient at hW; omega
  have hpow:=Nat.pow_le_pow_right (show 1≤ 2 by decide) hshift
  have heq:2 ^ (2 * w + 4)=16 * (2 ^ w) ^ 2:=by
    rw [pow_add,show 2 * w=w + w by omega,pow_add]
    ring
  rw [heq] at hpow
  have hpos:=Nat.two_pow_pos w
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · have ht:time + 1≤ W:=by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) ht)
  · have hc:allowance≤ W:=by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hc)
  · have hl:inputLength + 1≤ W:=by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hl)

end Lax455465Proofs.RamHostBounds

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

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances

def Nonnegative {n:ℕ} (d:Distance n):Prop:= ∀ u v,0≤ d u v

end Lax455465Proofs.RationalDistances

end

section

namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat

@[simp] theorem length_values {n:ℕ} (d:Matrix n):(values d).length=n*n:=List.length_ofFn

theorem value_at {n:ℕ} (d:Matrix n) (u v:Fin n):
    (values d)[(edgeIndex n (u,v)).val]'(by simpa only [length_values] using (edgeIndex n (u,v)).isLt)=d u v:=by
  simp only [values,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

end Lax455465Proofs.MetricMatrix

end

section

namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

theorem indices_spec (B:ℕ) {n:ℕ} (u v:Fin n) (hn:n < B) (hn2:n*n < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val) indices
      (fun _ τ => τ.vars "metric.u"=u.val∧ τ.vars "metric.v"=v.val) 10:=by
  have he:(edgeIndex n (u,v)).val < B:=(edgeIndex n (u,v)).isLt.trans hn2
  have hu:u.val < B:=u.isLt.trans hn
  have hv:v.val < B:=v.isLt.trans hn
  have hmul:u.val*n < B:=by rw [FlowLpIndices.edge_value] at he; omega
  have hdiv:=FlowLpIndices.edge_div u v
  have hmod:=FlowLpIndices.edge_mod u v
  rw [Nat.mod_def] at hmod
  rintro σ ⟨hnσ,heσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "metric.u") (@Fin.val n u)) (@Eq Nat (Env.vars τ "metric.v") (@Fin.val n v))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "metric.entry") (Env.vars σ "metric.n"); let c2:Env:=Env.setVar σ "metric.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "metric.entry"; let c5:Nat:=c3 "metric.u"; let c6:Nat:=c3 "metric.n"; let c7:Nat:=Nat.mul c5 c6; let c8:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c4 c7; let c9:Env:=Env.setVar c2 "metric.v" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))); let c13:Expr:=Expr.sub (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")); let c14:Nat:=c11 (Expr.size c13); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B indices σ σ' ((10:Nat))) (c0 σ')) c9 (@And.intro (Run B indices σ c9 ((10:Nat))) (c0 c9) (RunStep.mono B indices σ c9 (c10 c12 c14) ((10:Nat)) (RunStep.seq B (Com.assign "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))) (Com.assign "metric.v" c13) σ c2 c9 c12 c14 (RunStep.assign B σ "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n")) c1 (RunStep.eval_div B σ (Expr.var "metric.entry") (Expr.var "metric.n") (Env.vars σ "metric.entry") (Env.vars σ "metric.n") (RunStep.eval_var B σ "metric.entry" (?nAX_g6217_0_0_0)) (RunStep.eval_var B σ "metric.n" (?nAX_g6217_0_0_1)) ?_)) (RunStep.assign B c2 "metric.v" c13 c8 (RunStep.eval_sub B c2 (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")) c4 c7 (RunStep.eval_var B c2 "metric.entry" (?nAX_g6217_0_0_2)) (RunStep.eval_mul B c2 (Expr.var "metric.u") (Expr.var "metric.n") c5 c6 (RunStep.eval_var B c2 "metric.u" ?_) (RunStep.eval_var B c2 "metric.n" (?nAX_g6217_0_0_3)) ?_) (?nAX_g6217_0_0_4)))) (?nAX_g6217_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6217_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FlowLpIndices.edge_value]

end Lax455465Proofs.RamDualDistancesInit

end

section

namespace Lax455465Proofs.RamUnsignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem copy_spec (B:ℕ) (q:ℚ≥0) (side:String) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B)
    (hfresh:side ++ ".s" ≠ "rat.n" ∧ side ++ ".s" ≠ "rat.d" ∧ side ++ ".n" ≠ "rat.d"):
    Spec B (FractionOutput (q:ℚ)) (copy side)
      (fun _ τ => τ.vars (side ++ ".s")=0∧ τ.vars (side ++ ".n")=q.num∧
        τ.vars (side ++ ".d")=q.den) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  have hsN:=Ne.symm hfresh.1
  have hsD:=Ne.symm hfresh.2.1
  have hnD:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) side; let c1:String:=c0 ".s"; let c2:String:=c0 ".n"; let c3:String:=c0 ".d"; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ c1) ((0:Nat))) (And (@Eq Nat (Env.vars τ c2) (NNRat.num q)) (@Eq Nat (Env.vars τ c3) (NNRat.den q)))) σ; let c5:Env:=Env.setVar σ c1 ((0:Nat)); let c6:Nat:=Env.vars c5 "rat.n"; let c7:Env:=Env.setVar c5 c2 c6; let c8:Nat:=Env.vars c7 "rat.d"; let c9:Env:=Env.setVar c7 c3 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c2 (Expr.var "rat.n"); let c17:Com:=Com.assign c3 (Expr.var "rat.d"); let c18:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B (copy side) σ σ' ((6:Nat))) (c4 σ')) c9 (@And.intro (Run B (copy side) σ c9 ((6:Nat))) (c4 c9) (RunStep.mono B (copy side) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c1 (Expr.lit ((0:Nat)))) (Com.seq c16 c17) σ c5 c9 c12 c15 (RunStep.assign B σ c1 (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6226_0_0_0))) (RunStep.seq B c16 c17 c5 c7 c9 c13 c14 (RunStep.assign B c5 c2 (Expr.var "rat.n") c6 (RunStep.eval_var B c5 "rat.n" ?_)) (RunStep.assign B c7 c3 (Expr.var "rat.d") c8 (RunStep.eval_var B c7 "rat.d" ?_)))) (?nAX_g6226_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6226_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6226_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem value (q:ℚ≥0):fractionValue 0 q.num q.den=(q:ℚ):=by
  simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
  exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)

theorem add_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) addFraction
      (fun _ τ => FractionOutput ((a+b:ℚ≥0):ℚ) τ) (36*(a.den*b.den).size+96):=by
  simpa only [value,NNRat.coe_add] using addFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos

end Lax455465Proofs.RamUnsignedArithmetic

end

section

namespace Lax455465Proofs.RamArrayCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Invariant (xs:List ℕ) (source target count:String) (σ:Env):Prop:=
  Prefix xs source σ∧ σ.vars count=xs.length∧ σ.vars "copy.i" ≤ xs.length∧
    xs.length≤ (σ.arrs target).length∧ Prefix (xs.take (σ.vars "copy.i")) target σ

theorem step_spec (B:ℕ) (xs:List ℕ) (source target count:String)
    (h1:1 < B) (hlen:xs.length < B) (hwords:∀ x∈ xs,x < B)
    (harray:source ≠ target) (hcount:count ≠ "copy.i"):
    Spec B (fun σ => Invariant xs source target count σ∧ σ.vars "copy.i" < xs.length)
      (step source target) (fun σ τ => Invariant xs source target count τ∧
        τ.vars "copy.i"=σ.vars "copy.i"+1) 8:=by
  rintro σ ⟨⟨hp,hc,hi,hroom,ht⟩,hlt⟩
  let i:=σ.vars "copy.i"
  have hi':i < xs.length:=hlt
  have hget:(σ.arrs source)[i]?=some xs[i]:=hp i hi'
  have hiB:i < B:=hi'.trans hlen
  have hvB:xs[i] < B:=hwords _ (List.getElem_mem hi')
  have rstore:Run B (.store target (.var "copy.i") (.get source (.var "copy.i"))) σ
      (σ.setArr target i xs[i]) 4:=Run.store (evalB_var hiB)
        (evalB_get (evalB_var hiB) hget hvB) (by omega)
  let ν:=σ.setArr target i xs[i]
  have rinc:Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) ν
      (ν.setVar "copy.i" (i+1)) 4:=Run.assign
    (evalB_bin (op:=.add) (evalB_var (by simpa [ν] using hiB)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  have hprefix:Prefix (xs.take (i+1)) target ν:=by
    intro j hj
    have hj':j < i+1:=by simp only [List.length_take] at hj; omega
    have hxj:j < xs.length:=by omega
    have htake:(xs.take (i+1))[j]=xs[j]:=List.getElem_take
    simp only [ν,arrs_setArr,if_true]
    by_cases he:i=j
    · subst j
      rw [List.getElem?_set_self (by omega)]
      exact congrArg some htake.symm
    · rw [List.getElem?_set_ne he]
      have hji:j < i:=by omega
      have hjtake:j < (xs.take i).length:=by simp only [List.length_take]; omega
      exact (ht j hjtake).trans (congrArg some (by simp only [List.getElem_take,htake]))
  refine ⟨ν.setVar "copy.i" (i+1),rstore.seq rinc,?_,?_⟩
  · refine ⟨?_,?_,by simp; omega,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_neg harray] using hp
    · simpa only [ν,vars_setVar,vars_setArr,if_neg hcount] using hc
    · simpa only [ν,length_arrs_setArr,arrs_setVar] using hroom
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hprefix
  · simp [i]

theorem command_spec (B:ℕ) (xs:List ℕ) (source target count:String)
    (h1:1 < B) (hlen:xs.length < B) (hwords:∀ x∈ xs,x < B)
    (harray:source ≠ target) (hcount:count ≠ "copy.i"):
    Spec B (fun σ => Prefix xs source σ∧ σ.vars count=xs.length∧
      xs.length≤ (σ.arrs target).length) (command source target count)
      (fun _ τ => Prefix xs source τ∧ Prefix xs target τ) (12*xs.length+6):=by
  have hloop:=Spec.forRangeZero "copy.i" count (Invariant xs source target count) xs.length 8 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B xs source target count h1 hlen hwords harray hcount)
  rintro σ ⟨hp,hc,hroom⟩
  have hinit:Invariant xs source target count (σ.setVar "copy.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hp
    · simpa only [vars_setVar,if_neg hcount] using hc
    · simpa only [arrs_setVar] using hroom
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,List.length_nil] at hi
      omega
  obtain ⟨τ,hr,hpost⟩:=hloop σ hinit
  exact ⟨τ,by simpa only [command] using hr,hpost.1.1,
    by simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2⟩

end Lax455465Proofs.RamArrayCopy

end

section

namespace Lax455465Proofs.MetricHeight

open scoped BigOperators
open RationalDistances DirectedFlowLP

theorem value_bound (q:ℚ) (hq:0≤ q) (M:ℕ) (hnum:q.num.natAbs≤ M):q≤ M:=by
  have hn:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnQ:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) hn
  have hd:(1:ℚ)≤ q.den:=by exact_mod_cast (Rat.den_pos q)
  rw [←q.num_div_den,←hnQ]
  exact (div_le_self (by positivity) hd).trans (by exact_mod_cast hnum)

theorem height_of_denominator (q:ℚ) (hq:0≤ q) (M D:ℕ)
    (hM:1≤ M) (hD:0 < D) (hden:q.den ∣ D) (hval:q≤ M):
    LpInputSize.Height (M*D) q:=by
  have hd:q.den≤ D:=Nat.le_of_dvd hD hden
  have hn:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnQ:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) hn
  have hdenQ:(0:ℚ) < q.den:=by exact_mod_cast Rat.den_pos q
  have hrepr:(q.num.natAbs:ℚ)=q*(q.den:ℚ):=by
    rw [hnQ]
    exact ((eq_div_iff (ne_of_gt hdenQ)).mp q.num_div_den.symm).symm
  have hbound:(q.num.natAbs:ℚ)≤ (M*D:ℕ):=by
    rw [hrepr,Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hval (le_of_lt hdenQ)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hd) (by positivity))
  exact ⟨by exact_mod_cast hbound,hd.trans (by nlinarith)⟩

end Lax455465Proofs.MetricHeight

end

section

namespace Lax455465Proofs.RamUnsignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def Stored (q:ℚ≥0) (σ:Env):Prop:=σ.vars "fold.n"=q.num∧ σ.vars "fold.d"=q.den

theorem load_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (Stored q) load (fun _ τ => τ.vars "right.s"=0∧ τ.vars "right.n"=q.num∧ τ.vars "right.d"=q.den) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "right.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "right.n") (NNRat.num q)) (@Eq Nat (Env.vars τ "right.d") (NNRat.den q)))) σ; let c1:Env:=Env.setVar σ "right.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "fold.n"; let c3:Env:=Env.setVar c1 "right.n" c2; let c4:Nat:=Env.vars c3 "fold.d"; let c5:Env:=Env.setVar c3 "right.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "fold.n")); let c10:Nat:=c7 (Expr.size (Expr.var "fold.d")); let c11:Nat:=c6 c9 c10; let c12:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B load σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B load σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B load σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "fold.n")) (Com.assign "right.d" (Expr.var "fold.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6296_0_0_0))) (RunStep.seq B (Com.assign "right.n" (Expr.var "fold.n")) (Com.assign "right.d" (Expr.var "fold.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "right.n" (Expr.var "fold.n") c2 (RunStep.eval_var B c1 "fold.n" (?nAX_g6296_0_0_1))) (RunStep.assign B c3 "right.d" (Expr.var "fold.d") c4 (RunStep.eval_var B c3 "fold.d" (?nAX_g6296_0_0_2))))) (?nAX_g6296_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6296_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem save_spec (B:ℕ) (q:ℚ≥0) (hn:q.num < B) (hd:q.den < B):
    Spec B (FractionOutput (q:ℚ)) save (fun _ τ => Stored q τ) 4:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "rat.d"; let c1:Env:=Env.setVar (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "fold.d" c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 ((1:Nat)); let c4:Nat:=c3 (Expr.size (Expr.var "rat.n")); let c5:Nat:=c3 (Expr.size (Expr.var "rat.d")); @Exists.intro Env (fun (σ':Env) => And (Run B save σ σ' ((4:Nat))) ((fun (x τ:Env) => Stored q τ) σ σ')) c1 (@And.intro (Run B save σ c1 ((4:Nat))) ((fun (x τ:Env) => Stored q τ) σ c1) (RunStep.mono B save σ c1 (c2 c4 c5) ((4:Nat)) (RunStep.seq B (Com.assign "fold.n" (Expr.var "rat.n")) (Com.assign "fold.d" (Expr.var "rat.d")) σ (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) c1 c4 c5 (RunStep.assign B σ "fold.n" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g6297_0_0_0))) (RunStep.assign B (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "fold.d" (Expr.var "rat.d") c0 (RunStep.eval_var B (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "rat.d" (?nAX_g6297_0_0_1)))) (?nAX_g6297_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6297_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6297_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6297_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem finish_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (Stored q) finish (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  have hv:=RamUnsignedArithmetic.value q
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "fold.n"; let c3:Env:=Env.setVar c1 "rat.n" c2; let c4:Nat:=Env.vars c3 "fold.d"; let c5:Env:=Env.setVar c3 "rat.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "fold.n")); let c10:Nat:=c7 (Expr.size (Expr.var "fold.d")); let c11:Nat:=c6 c9 c10; @Exists.intro Env (fun (σ':Env) => And (Run B finish σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B finish σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B finish σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "fold.n")) (Com.assign "rat.d" (Expr.var "fold.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6298_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "fold.n")) (Com.assign "rat.d" (Expr.var "fold.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "rat.n" (Expr.var "fold.n") c2 (RunStep.eval_var B c1 "fold.n" (?nAX_g6298_0_0_1))) (RunStep.assign B c3 "rat.d" (Expr.var "fold.d") c4 (RunStep.eval_var B c3 "fold.d" (?nAX_g6298_0_0_2))))) (?nAX_g6298_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6298_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored,FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem combine_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hsn:(a+b).num < B) (hsd:(a+b).den < B):
    Spec B (fun σ => FractionOutput (a:ℚ) σ∧ Stored b σ) combine
      (fun _ τ => Stored (a+b) τ) (36*(M^2).size+112):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,rleft,pleft⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) σ ha
  have hbν:Stored b ν:=by
    simpa only [Stored,rleft.frame_var "fold.n" (by decide),rleft.frame_var "fold.d" (by decide)] using hb
  obtain ⟨μ,rright,pright⟩:=load_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hbν
  have paμ:μ.vars "left.s"=0∧ μ.vars "left.n"=a.num∧ μ.vars "left.d"=a.den:=by
    simpa only [rright.frame_var "left.s" (by decide),rright.frame_var "left.n" (by decide),rright.frame_var "left.d" (by decide),String.reduceAppend] using pleft
  obtain ⟨ξ,radd,padd⟩:=RamUnsignedArithmetic.add_spec B M a b hB han had hbn hbd μ
    ⟨paμ.1,paμ.2.1,paμ.2.2,pright⟩
  obtain ⟨τ,rsave,psave⟩:=save_spec B (a+b) hsn hsd ξ padd
  refine ⟨τ,(rleft.seq (rright.seq (radd.seq rsave))).mono ?_,psave⟩
  have hprod:a.den*b.den≤ M^2:=by nlinarith [Nat.mul_le_mul had hbd]
  have hsize:=Nat.size_le_size hprod
  omega

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧ Stored (qs.take (σ.vars index)).sum σ

set_option maxHeartbeats 0 in

theorem command_spec (B M K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ≥0) (body:Com) (hB:2*M^2+3 < B) (hlen:qs.length < B)
    (hnum:∀ q∈ qs,q.num≤ M) (hden:∀ q∈ qs,q.den≤ M)
    (hprefixNum:∀ i, (qs.take i).sum.num≤ M) (hprefixDen:∀ i, (qs.take i).sum.den≤ M)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k name,R σ→ name=index∨ name="fold.n" ∨ name="fold.d" → R (σ.setVar name k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ FractionOutput (qs[i]:ℚ) τ) K)
    (hfresh:index ≠ "fold.n" ∧ index ≠ "fold.d" ∧ index∉ combine.wvars)
    (hbodyIndex:index∉ body.wvars) (hbodySum:"fold.n" ∉ body.wvars∧ "fold.d" ∉ body.wvars)
    (hcombineFrame:∀ {σ τ:Env} {k:ℕ},Run B combine σ τ k→ R σ→ R τ)
    (hfinishFrame:∀ {σ τ:Env} {k:ℕ},Run B finish σ τ k→ R σ→ R τ):
    Spec B R (command index limit body)
      (fun _ τ => R τ∧ FractionOutput ((qs.sum:ℚ≥0):ℚ) τ)
      ((K+36*(M^2).size+120)*qs.length+16):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hstep:Spec B (fun σ => Invariant R index qs σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs τ∧ τ.vars index=σ.vars index+1)
      (K+36*(M^2).size+116):=by
    rintro σ ⟨⟨hR,hi,hstored⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    obtain ⟨ν,rbody,pbody⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(rbody.frame_var index hbodyIndex).trans rfl
    have hstoredν:Stored (qs.take i).sum ν:=by
      simpa only [Stored,rbody.frame_var "fold.n" hbodySum.1,rbody.frame_var "fold.d" hbodySum.2] using hstored
    have hq:qs[i]∈ qs:=List.getElem_mem hi'
    have hsum:qs[i]+(qs.take i).sum=(qs.take (i+1)).sum:=by
      rw [List.take_succ_eq_append_getElem hi',List.sum_append,List.sum_singleton,add_comm]
    obtain ⟨μ,rcombine,pcombine⟩:=combine_spec B M qs[i] (qs.take i).sum hB
      (hnum _ hq) (hden _ hq) (hprefixNum i) (hprefixDen i)
      (by rw [hsum]; exact (hprefixNum (i+1)).trans_lt hM)
      (by rw [hsum]; exact (hprefixDen (i+1)).trans_lt hM) ν ⟨pbody.2,hstoredν⟩
    have hiμ:μ.vars index=i:=(rcombine.frame_var index hfresh.2.2).trans hiν
    have hRμ:=hcombineFrame rcombine pbody.1
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨μ.setVar index (i+1),(rbody.seq (rcombine.seq hinc)).mono (by omega),?_,?_⟩
    · refine ⟨hset μ (i+1) index hRμ (Or.inl rfl),by simp; omega,?_⟩
      simpa only [Stored,vars_setVar,if_neg (Ne.symm hfresh.1),if_neg (Ne.symm hfresh.2.1),if_pos rfl,if_true,hsum] using pcombine
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs) qs.length
    (K+36*(M^2).size+116) hlen (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν:=(σ.setVar "fold.n" 0).setVar "fold.d" 1
  have rinit:Run B init σ ν 4:=by
    exact (Run.assign (evalB_lit (by omega:0 < B))).seq (Run.assign (evalB_lit h1))
  have hRν:R ν:=hset _ 1 "fold.d" (hset σ 0 "fold.n" hR (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have hinvariant:Invariant R index qs (ν.setVar index 0):=by
    refine ⟨hset ν 0 index hRν (Or.inl rfl),by simp,?_⟩
    simp [Stored,ν,Ne.symm hfresh.1,Ne.symm hfresh.2.1]
  obtain ⟨μ,rscan,pscan⟩:=hscan ν hinvariant
  have hstoredμ:Stored qs.sum μ:=by simpa only [pscan.2,List.take_length] using pscan.1.2.2
  have hfinalNum:qs.sum.num≤ M:=by simpa only [List.take_length] using hprefixNum qs.length
  have hfinalDen:qs.sum.den≤ M:=by simpa only [List.take_length] using hprefixDen qs.length
  obtain ⟨τ,rfinish,pfinish⟩:=finish_spec B qs.sum h1 (hfinalNum.trans_lt hM) (hfinalDen.trans_lt hM) μ hstoredμ
  refine ⟨τ,(rinit.seq (rscan.seq rfinish)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hfinishFrame rfinish pscan.1.1,pfinish⟩

end Lax455465Proofs.RamUnsignedSum

end

section

namespace Lax455465Proofs.RamProductSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem value_at (xs ys:List ℚ≥0) (hlen:ys.length=xs.length) (i:ℕ) (hi:i < xs.length):
    (products xs ys)[i]'(by simpa only [products,List.length_ofFn] using hi) =
      xs[i]*ys[i]'(by omega):=by
  simp only [products,List.getElem_ofFn,List.getD_eq_get ys 0 (⟨i,by omega⟩:Fin ys.length)]
  rfl

end Lax455465Proofs.RamProductSum

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionVolume

def NoEvent {n:ℕ} (distance:Fin n→ ℚ) (a b:ℚ):Prop:=
  ∀ v, ¬ (a < distance v∧ distance v < b)

theorem edgePortion_nonneg (length base radius:ℚ) (hl:0≤ length):
    0≤ edgePortion length base radius:=le_min hl (le_max_right _ _)

theorem edgePortion_le (length base radius:ℚ):edgePortion length base radius≤ length:=
  min_le_left _ _

theorem edgePortion_monotone (length base a b:ℚ) (hab:a≤ b):
    edgePortion length base a≤ edgePortion length base b:=by
  exact min_le_min_left length (max_le_max_right 0 (sub_le_sub_right hab base))

theorem bounds {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed radius:ℚ) (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v):
    seed≤ volume capacity length distance seed radius∧
    volume capacity length distance seed radius≤ seed + weight capacity length:=by
  constructor
  · unfold volume
    have h:0≤ ∑ u, ∑ v,
        capacity u v * edgePortion (length u v) (distance u) radius:=
      Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
        mul_nonneg (hc u v) (edgePortion_nonneg _ _ _ (hl u v))))
    linarith
  · unfold volume weight
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (edgePortion_le _ _ _) (hc u v)

theorem monotone {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed a b:ℚ) (hc:∀ u v,0≤ capacity u v) (hab:a≤ b):
    volume capacity length distance seed a≤ volume capacity length distance seed b:=by
  unfold volume
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (edgePortion_monotone _ _ _ _ hab) (hc u v)

private theorem crossing_gain (length tail head a b:ℚ)
    (hab:a≤ b) (htail:tail≤ a) (hhead:b≤ head)
    (hlip:head - tail≤ length):
    edgePortion length tail b - edgePortion length tail a=b - a:=by
  have hba:0≤ b - tail:=by linarith
  have haa:0≤ a - tail:=by linarith
  have hbl:b - tail≤ length:=by linarith
  have hal:a - tail≤ length:=by linarith
  simp only [edgePortion,max_eq_left hba,max_eq_left haa,
    min_eq_right hbl,min_eq_right hal]
  ring

theorem gain {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed a b:ℚ) (hc:∀ u v,0≤ capacity u v) (hab:a≤ b)
    (hevent:NoEvent distance a b)
    (hlip:∀ u v,distance v - distance u≤ length u v):
    (b - a) * boundary capacity distance b≤
      volume capacity length distance seed b - volume capacity length distance seed a:=by
  unfold volume boundary
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hcross:distance u < b∧ b≤ distance v
  · rw [if_pos hcross]
    have htail:distance u≤ a:=by
      by_contra h
      exact hevent u ⟨lt_of_not_ge h,hcross.1⟩
    have hgain:=crossing_gain (length u v) (distance u) (distance v)
      a b hab htail hcross.2 (hlip u v)
    have heq:capacity u v * edgePortion (length u v) (distance u) b -
        capacity u v * edgePortion (length u v) (distance u) a =
        (b - a) * capacity u v:=by
      rw [← mul_sub,hgain]
      ring
    exact le_of_eq heq.symm
  · rw [if_neg hcross,mul_zero]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (edgePortion_monotone _ _ _ _ hab) (hc u v))

end Lax455465Proofs.RegionVolume

end

section

open scoped BigOperators

namespace Lax455465Proofs.FiniteRegionGrowth

theorem product_gain_left (a b A B width beta cut:ℚ)
    (ha:0≤ a) (hb:0≤ b) (hA:a≤ A) (hB:b≤ B)
    (hw:0≤ width) (hbeta:0≤ beta)
    (hcut:beta * A≤ cut) (hgain:width * cut≤ A - a):
    width * beta * (a * b)≤ A * B - a * b:=by
  have hfirst:width * beta * a≤ A - a:=by
    calc
      width * beta * a≤ width * beta * A:=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hw hbeta)
      _=width * (beta * A):=by ring
      _≤ width * cut:=mul_le_mul_of_nonneg_left hcut hw
      _≤ A - a:=hgain
  have hsecond:=mul_le_mul_of_nonneg_right hfirst hb
  have hthird:=mul_le_mul_of_nonneg_left hB (ha.trans hA)
  nlinarith

theorem product_gain_right (a b A B width beta cut:ℚ)
    (ha:0≤ a) (hb:0≤ b) (hA:a≤ A) (hB:b≤ B)
    (hw:0≤ width) (hbeta:0≤ beta)
    (hcut:beta * B≤ cut) (hgain:width * cut≤ B - b):
    width * beta * (a * b)≤ A * B - a * b:=by
  simpa only [mul_comm b a,mul_comm B A] using
    product_gain_left b a B A width beta cut hb ha hB hA hw hbeta hcut hgain

theorem subdivided_gain (product radius:ℕ→ ℚ) (beta:ℚ) (k:ℕ)
    (hbeta:0≤ beta)
    (hwidth:∀ i < k,radius i≤ radius (i + 1))
    (hbase:∀ i < k,product 0≤ product i)
    (hgain:∀ i < k,
      (radius (i + 1) - radius i) * beta * product i≤
        product (i + 1) - product i):
    (radius k - radius 0) * beta * product 0≤ product k - product 0:=by
  have hsum:∑ i∈ Finset.range k,
      (radius (i + 1) - radius i) * beta * product 0≤
      ∑ i∈ Finset.range k, (product (i + 1) - product i):=by
    apply Finset.sum_le_sum
    intro i hi
    have hik:=Finset.mem_range.mp hi
    exact (mul_le_mul_of_nonneg_left (hbase i hik)
      (mul_nonneg (sub_nonneg.mpr (hwidth i hik)) hbeta)).trans (hgain i hik)
  simpa only [← Finset.sum_mul,Finset.sum_range_sub] using hsum

theorem doubled_cell (product radius:ℕ→ ℚ) (beta:ℚ) (k:ℕ)
    (hbeta:0≤ beta) (hproduct:0≤ product 0)
    (hwidth:∀ i < k,radius i≤ radius (i + 1))
    (hbase:∀ i < k,product 0≤ product i)
    (hgain:∀ i < k,
      (radius (i + 1) - radius i) * beta * product i≤
        product (i + 1) - product i)
    (hcell:1≤ (radius k - radius 0) * beta):
    2 * product 0≤ product k:=by
  have hgrowth:=subdivided_gain product radius beta k hbeta hwidth hbase hgain
  have hminimum:=mul_le_mul_of_nonneg_right hcell hproduct
  nlinarith

theorem exists_not_doubling (product:ℕ→ ℚ) (k:ℕ) (seed p:ℚ)
    (hseed:0 < seed) (hstart:seed ^ 2≤ product 0)
    (hbudget:product k≤ 4 * p ^ 2 * seed ^ 2)
    (hsteps:4 * p ^ 2 < (2:ℚ) ^ k):
    ∃ j < k,product (j + 1) < 2 * product j:=by
  by_contra h
  have hdouble:∀ j < k,2 * product j≤ product (j + 1):=by
    intro j hj
    exact le_of_not_gt (fun hlt => h ⟨j,hj,hlt⟩)
  have hgrowth:∀ j:ℕ,j≤ k→ (2:ℚ) ^ j * product 0≤ product j:=by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      calc
        (2:ℚ) ^ (j + 1) * product 0=2 * ((2:ℚ) ^ j * product 0):=by
          rw [pow_succ]
          ring
        _≤ 2 * product j:=mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
        _≤ product (j + 1):=hdouble j (by omega)
  have hpow:=hgrowth k le_rfl
  have hstart':=mul_le_mul_of_nonneg_left hstart (pow_nonneg (show (0:ℚ)≤ 2 by norm_num) k)
  have hexcess:=mul_lt_mul_of_pos_right hsteps (sq_pos_of_pos hseed)
  linarith

end Lax455465Proofs.FiniteRegionGrowth

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionInterval

open RegionVolume

def productVolume {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed radius:ℚ):ℚ:=
  volume capacity length outDistance seed radius *
    volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed radius

private theorem transpose_weight {n:ℕ} (capacity length:Matrix n):
    weight (fun u v => capacity v u) (fun u v => length v u)=weight capacity length:=by
  unfold weight
  rw [Finset.sum_comm]

theorem budget {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed radius:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed):
    seed ^ 2≤ productVolume capacity length outDistance inDistance seed radius∧
    productVolume capacity length outDistance inDistance seed radius≤
      (seed + weight capacity length) ^ 2:=by
  obtain ⟨houtLo,houtHi⟩:=bounds capacity length outDistance seed radius hc hl
  obtain ⟨hinLo,hinHi⟩:=bounds (fun u v => capacity v u)
    (fun u v => length v u) inDistance seed radius (fun u v => hc v u) (fun u v => hl v u)
  rw [transpose_weight] at hinHi
  unfold productVolume
  constructor
  · simpa only [pow_two] using mul_le_mul houtLo hinLo hseed (hseed.trans houtLo)
  · simpa only [pow_two] using mul_le_mul houtHi hinHi
      (hseed.trans hinLo) (hseed.trans houtLo |>.trans houtHi)

theorem normalized_budget {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed radius p:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (hp:1≤ p) (hweight:weight capacity length≤ p * seed):
    productVolume capacity length outDistance inDistance seed radius≤ 4 * p ^ 2 * seed ^ 2:=by
  have hweightNN:0≤ weight capacity length:=by
    exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
      mul_nonneg (hc u v) (hl u v)))
  have hseedLe:seed≤ p * seed:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hseed
  have htotal:seed + weight capacity length≤ 2 * p * seed:=by linarith
  have hsq:=mul_self_le_mul_self (add_nonneg hseed hweightNN) htotal
  calc
    productVolume capacity length outDistance inDistance seed radius≤
        (seed + weight capacity length) ^ 2:=(budget _ _ _ _ _ _ hc hl hseed).2
    _≤ (2 * p * seed) ^ 2:=by simpa only [pow_two] using hsq
    _=4 * p ^ 2 * seed ^ 2:=by ring

theorem monotone {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed a b:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (hab:a≤ b):
    productVolume capacity length outDistance inDistance seed a≤
      productVolume capacity length outDistance inDistance seed b:=by
  have hout:=RegionVolume.monotone capacity length outDistance seed a b hc hab
  have hin:=RegionVolume.monotone (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a b (fun u v => hc v u) hab
  have hinLo:=(bounds (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a (fun u v => hc v u) (fun u v => hl v u)).1
  have houtLo:=(bounds capacity length outDistance seed b hc hl).1
  exact mul_le_mul hout hin (hseed.trans hinLo) (hseed.trans houtLo)

theorem gain {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed a b beta:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (hab:a≤ b) (hbeta:0≤ beta)
    (houtEvent:NoEvent outDistance a b) (hinEvent:NoEvent inDistance a b)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u)
    (hbad:beta * volume capacity length outDistance seed b≤
        boundary capacity outDistance b∨
      beta * volume (fun u v => capacity v u) (fun u v => length v u)
        inDistance seed b≤ boundary (fun u v => capacity v u) inDistance b):
    (b - a) * beta * productVolume capacity length outDistance inDistance seed a≤
      productVolume capacity length outDistance inDistance seed b -
        productVolume capacity length outDistance inDistance seed a:=by
  have houtLo:=(bounds capacity length outDistance seed a hc hl).1
  have hinLo:=(bounds (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a (fun u v => hc v u) (fun u v => hl v u)).1
  have houtMono:=RegionVolume.monotone capacity length outDistance seed a b hc hab
  have hinMono:=RegionVolume.monotone (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a b (fun u v => hc v u) hab
  unfold productVolume
  rcases hbad with houtBad | hinBad
  · exact FiniteRegionGrowth.product_gain_left _ _ _ _ _ _ _
      (hseed.trans houtLo) (hseed.trans hinLo) houtMono hinMono
      (sub_nonneg.mpr hab) hbeta houtBad
      (RegionVolume.gain capacity length outDistance seed a b hc hab houtEvent houtLip)
  · exact FiniteRegionGrowth.product_gain_right _ _ _ _ _ _ _
      (hseed.trans houtLo) (hseed.trans hinLo) houtMono hinMono
      (sub_nonneg.mpr hab) hbeta hinBad
      (RegionVolume.gain (fun u v => capacity v u) (fun u v => length v u)
        inDistance seed a b (fun u v => hc v u) hab hinEvent hinLip)

end Lax455465Proofs.RegionInterval

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.RegionThresholds

def events {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):Finset ℚ:=
  insert a (insert b ((Finset.univ.image outDistance ∪ Finset.univ.image inDistance).filter
    (fun r => a≤ r∧ r≤ b)))

def candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):List ℚ:=
  (events outDistance inDistance a b).sort

theorem left_mem {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):
    a∈ events outDistance inDistance a b:=by simp [events]

theorem right_mem {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):
    b∈ events outDistance inDistance a b:=by simp [events]

theorem bounds {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (hab:a≤ b):
    ∀ r∈ events outDistance inDistance a b,a≤ r∧ r≤ b:=by
  intro r hr
  simp only [events,Finset.mem_insert,Finset.mem_filter] at hr
  rcases hr with rfl | rfl | ⟨_,h⟩
  · exact ⟨le_rfl,hab⟩
  · exact ⟨hab,le_rfl⟩
  · exact h

private theorem no_member_between (s:Finset ℚ) (j:ℕ) (hj:j + 1 < s.sort.length)
    (r:ℚ) (hr:r∈ s):
    ¬ (s.sort.get ⟨j,by omega⟩ < r∧ r < s.sort.get ⟨j + 1,hj⟩):=by
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp ((Finset.mem_sort (·≤ ·)).mpr hr)
  have hmono:=(Finset.sortedLT_sort s).monotone
  rintro ⟨hlow,hhigh⟩
  by_cases hle:i.val≤ j
  · have h:=hmono (show i≤ ⟨j,by omega⟩ from hle)
    rw [hi] at h
    exact (not_lt_of_ge h) hlow
  · have h:=hmono (show (⟨j + 1,hj⟩:Fin s.sort.length)≤ i by
      change j + 1≤ i.val
      omega)
    rw [hi] at h
    exact (not_lt_of_ge h) hhigh

theorem no_event {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ)
    (hab:a≤ b) (j:ℕ) (hj:j + 1 < (candidates outDistance inDistance a b).length):
    (∀ v, ¬ ((candidates outDistance inDistance a b).get ⟨j,by omega⟩ < outDistance v∧
      outDistance v < (candidates outDistance inDistance a b).get ⟨j + 1,hj⟩))∧
    (∀ v, ¬ ((candidates outDistance inDistance a b).get ⟨j,by omega⟩ < inDistance v∧
      inDistance v < (candidates outDistance inDistance a b).get ⟨j + 1,hj⟩)):=by
  change j + 1 < (events outDistance inDistance a b).sort.length at hj
  have hstart:=(bounds outDistance inDistance a b hab _
    ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ ⟨j,by omega⟩))).1
  have hend:=(bounds outDistance inDistance a b hab _
    ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ ⟨j + 1,hj⟩))).2
  constructor
  · intro v h
    apply no_member_between (events outDistance inDistance a b) j hj (outDistance v) ?_ h
    simp only [events,Finset.mem_insert,Finset.mem_filter]
    right; right
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),
      ⟨hstart.trans h.1.le,h.2.le.trans hend⟩⟩
  · intro v h
    apply no_member_between (events outDistance inDistance a b) j hj (inDistance v) ?_ h
    simp only [events,Finset.mem_insert,Finset.mem_filter]
    right; right
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),
      ⟨hstart.trans h.1.le,h.2.le.trans hend⟩⟩

def radius {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (i:ℕ):ℚ:=
  (candidates outDistance inDistance a b).getD i b

theorem length_pos {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):
    0 < (candidates outDistance inDistance a b).length:=by
  unfold candidates
  rw [Finset.length_sort]
  exact Finset.card_pos.mpr ⟨a,left_mem outDistance inDistance a b⟩

theorem radius_eq_get {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ)
    (i:Fin (candidates outDistance inDistance a b).length):
    radius outDistance inDistance a b i.val =
      (candidates outDistance inDistance a b).get i:=
  List.getD_eq_get _ _ i

theorem radius_first {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (hab:a≤ b):
    radius outDistance inDistance a b 0=a:=by
  let i:Fin (candidates outDistance inDistance a b).length:=
    ⟨0,length_pos outDistance inDistance a b⟩
  change radius outDistance inDistance a b i.val=a
  rw [radius_eq_get]
  obtain ⟨j,hj⟩:=List.mem_iff_get.mp
    ((Finset.mem_sort (·≤ ·)).mpr (left_mem outDistance inDistance a b))
  apply le_antisymm
  · have h:=(Finset.sortedLT_sort (events outDistance inDistance a b)).monotone
      (show i≤ j by exact Nat.zero_le _)
    exact h.trans_eq hj
  · exact (bounds outDistance inDistance a b hab _
      ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ i))).1

theorem radius_last {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (hab:a≤ b):
    radius outDistance inDistance a b ((candidates outDistance inDistance a b).length - 1)=b:=by
  have hpos:=length_pos outDistance inDistance a b
  let i:Fin (candidates outDistance inDistance a b).length:=
    ⟨(candidates outDistance inDistance a b).length - 1,by omega⟩
  change radius outDistance inDistance a b i.val=b
  rw [radius_eq_get]
  obtain ⟨j,hj⟩:=List.mem_iff_get.mp
    ((Finset.mem_sort (·≤ ·)).mpr (right_mem outDistance inDistance a b))
  apply le_antisymm
  · exact (bounds outDistance inDistance a b hab _
      ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ i))).2
  · have h:=(Finset.sortedLT_sort (events outDistance inDistance a b)).monotone
      (show j≤ i by change j.val≤ _; exact Nat.le_sub_one_of_lt j.isLt)
    exact (le_of_eq hj.symm).trans h

theorem radius_monotone {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ)
    (j:ℕ) (hj:j + 1 < (candidates outDistance inDistance a b).length):
    radius outDistance inDistance a b j≤ radius outDistance inDistance a b (j + 1):=by
  rw [radius_eq_get outDistance inDistance a b ⟨j,by omega⟩,
    radius_eq_get outDistance inDistance a b ⟨j + 1,hj⟩]
  exact (Finset.sortedLT_sort _).monotone (show (⟨j,by omega⟩:Fin _)≤ ⟨j + 1,hj⟩ by
    change j≤ j + 1
    omega)

end Lax455465Proofs.RegionThresholds

end

section

namespace Lax455465Proofs.RegionCell

open RegionVolume RegionInterval

theorem doubles {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed a b beta:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (ha:0≤ a) (hab:a≤ b) (hbeta:0≤ beta)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u)
    (hbad:∀ r∈ RegionThresholds.events outDistance inDistance a b,0 < r→
      beta * volume capacity length outDistance seed r≤ boundary capacity outDistance r∨
      beta * volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r≤
        boundary (fun u v => capacity v u) inDistance r)
    (hcell:1≤ (b - a) * beta):
    2 * productVolume capacity length outDistance inDistance seed a≤
      productVolume capacity length outDistance inDistance seed b:=by
  let radii:=RegionThresholds.radius outDistance inDistance a b
  let candidates:=RegionThresholds.candidates outDistance inDistance a b
  let k:=candidates.length - 1
  let values:=fun i => productVolume capacity length outDistance inDistance seed (radii i)
  have hpos:0 < candidates.length:=RegionThresholds.length_pos outDistance inDistance a b
  have hindex:∀ i < k,i + 1 < candidates.length:=by
    intro i hi
    dsimp [k] at hi
    omega
  have hfirst:radii 0=a:=RegionThresholds.radius_first outDistance inDistance a b hab
  have hlast:radii k=b:=RegionThresholds.radius_last outDistance inDistance a b hab
  have hwidth:∀ i < k,radii i≤ radii (i + 1):=by
    intro i hi
    exact RegionThresholds.radius_monotone outDistance inDistance a b i (hindex i hi)
  have hbase:∀ i < k,values 0≤ values i:=by
    intro i hi
    have hii:i < candidates.length:=by have h:=hindex i hi; omega
    have haRi:a≤ radii i:=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i,hii⟩]
      exact (RegionThresholds.bounds outDistance inDistance a b hab _
        ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ ⟨i,hii⟩))).1
    dsimp [values]
    rw [hfirst]
    exact RegionInterval.monotone capacity length outDistance inDistance seed a _ hc hl hseed haRi
  have hgain:∀ i < k,
      (radii (i + 1) - radii i) * beta * values i≤ values (i + 1) - values i:=by
    intro i hi
    have hinext:=hindex i hi
    have hii:i < candidates.length:=by omega
    have houtIn:=RegionThresholds.no_event outDistance inDistance a b hab i hinext
    have houtEvent:NoEvent outDistance (radii i) (radii (i + 1)):=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i,hii⟩,
        RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩]
      exact houtIn.1
    have hinEvent:NoEvent inDistance (radii i) (radii (i + 1)):=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i,hii⟩,
        RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩]
      exact houtIn.2
    have hmem:radii (i + 1)∈ RegionThresholds.events outDistance inDistance a b:=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩]
      exact (Finset.mem_sort (·≤ ·)).mp (List.get_mem _ _)
    have hpositive:0 < radii (i + 1):=by
      have hstrict:=(Finset.sortedLT_sort (RegionThresholds.events outDistance inDistance a b))
        (show (⟨0,hpos⟩:Fin _) < ⟨i + 1,hinext⟩ by change 0 < i + 1; omega)
      have hr0:=RegionThresholds.radius_eq_get outDistance inDistance a b ⟨0,hpos⟩
      have hr1:=RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩
      have haR:a < radii (i + 1):=by
        calc
          a=radii 0:=hfirst.symm
          _=(RegionThresholds.candidates outDistance inDistance a b).get ⟨0,hpos⟩:=hr0
          _ < (RegionThresholds.candidates outDistance inDistance a b).get ⟨i + 1,hinext⟩:=hstrict
          _=radii (i + 1):=hr1.symm
      exact ha.trans_lt haR
    exact RegionInterval.gain capacity length outDistance inDistance seed (radii i) (radii (i + 1))
      beta hc hl hseed (hwidth i hi) hbeta houtEvent hinEvent houtLip hinLip
      (hbad _ hmem hpositive)
  have hvalues:0≤ values 0:=by
    have hlow:=(RegionInterval.budget capacity length outDistance inDistance seed (radii 0)
      hc hl hseed).1
    exact (sq_nonneg seed).trans hlow
  have h:=FiniteRegionGrowth.doubled_cell values radii beta k hbeta hvalues hwidth hbase hgain
    (by simpa only [hfirst,hlast] using hcell)
  simpa only [values,hfirst,hlast] using h

end Lax455465Proofs.RegionCell

end

section

namespace Lax455465Proofs.RegionBudget

theorem steps_pos (p:ℕ):0 < steps p:=by unfold steps; omega

theorem exceeds_budget (p:ℕ) (hp:0 < p):
    4 * (p:ℚ) ^ 2 < (2:ℚ) ^ steps p:=by
  have hupperNat:p < 2 ^ (Nat.log2 p + 1):=by
    simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two p
  have hupper:(p:ℚ) < (2:ℚ) ^ (Nat.log2 p + 1):=by exact_mod_cast hupperNat
  have hpq:0 < (p:ℚ):=by exact_mod_cast hp
  have hpow:0 < (2:ℚ) ^ (Nat.log2 p + 1):=pow_pos (by norm_num) _
  have hsquare:(p:ℚ) ^ 2 < ((2:ℚ) ^ (Nat.log2 p + 1)) ^ 2:=by nlinarith
  have hid:(2:ℚ) ^ steps p=4 * ((2:ℚ) ^ (Nat.log2 p + 1)) ^ 2:=by
    rw [show steps p=(Nat.log2 p + 1) * 2 + 2 by unfold steps; omega,
      pow_add,pow_mul]
    norm_num
    ring
  rw [hid]
  nlinarith

end Lax455465Proofs.RegionBudget

end

section

namespace Lax455465Proofs.RegionSearch

open RegionVolume RegionInterval

private theorem grid_last (k:ℕ) (delta:ℚ) (hk:0 < k):grid k delta k=delta:=by
  have hkq:(k:ℚ) ≠ 0:=by exact_mod_cast (Nat.ne_of_gt hk)
  simp [grid,hkq]

private theorem grid_nonneg (k:ℕ) (delta:ℚ) (j:ℕ) (hd:0≤ delta):
    0≤ grid k delta j:=by unfold grid; positivity

private theorem grid_mono (k:ℕ) (delta:ℚ) (j:ℕ) (hd:0≤ delta):
    grid k delta j≤ grid k delta (j + 1):=by
  unfold grid
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ j) hd

private theorem grid_width (k:ℕ) (delta:ℚ) (j:ℕ)
    (hk:0 < k) (hd:0 < delta):
    (grid k delta (j + 1) - grid k delta j) * slope k delta=1:=by
  have hkq:(k:ℚ) ≠ 0:=by exact_mod_cast (Nat.ne_of_gt hk)
  unfold grid slope
  push_cast
  field_simp [hkq,ne_of_gt hd]
  ring

private theorem grid_le (k:ℕ) (delta:ℚ) (j:ℕ)
    (hk:0 < k) (hd:0≤ delta) (hj:j≤ k):grid k delta j≤ delta:=by
  calc
    grid k delta j≤ grid k delta k:=by
      unfold grid
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hd
    _=delta:=grid_last k delta hk

theorem candidates_bound {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (k:ℕ) (delta r:ℚ) (hk:0 < k) (hd:0≤ delta)
    (hr:r∈ candidates outDistance inDistance k delta):0≤ r∧ r≤ delta:=by
  simp only [candidates,List.mem_append,List.mem_map,List.mem_ofFn] at hr
  rcases hr with (⟨j,hj,rfl⟩ | ⟨v,rfl⟩) | ⟨v,rfl⟩
  · exact ⟨grid_nonneg k delta j hd,grid_le k delta j hk hd (by have hh:=List.mem_range.mp hj; omega)⟩
  · exact ⟨le_min hd (le_max_right _ _),min_le_left _ _⟩
  · exact ⟨le_min hd (le_max_right _ _),min_le_left _ _⟩

theorem event_mem_candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (k:ℕ) (delta:ℚ) (j:ℕ) (r:ℚ) (hk:0 < k) (hd:0≤ delta) (hj:j < k)
    (hr:r∈ RegionThresholds.events outDistance inDistance (grid k delta j) (grid k delta (j+1))):
    r∈ candidates outDistance inDistance k delta:=by
  have hb:=RegionThresholds.bounds outDistance inDistance _ _ (grid_mono k delta j hd) r hr
  have hnonnegative:0≤ r:=(grid_nonneg k delta j hd).trans hb.1
  have hdelta:r≤ delta:=hb.2.trans (grid_le k delta (j+1) hk hd (by omega))
  simp only [RegionThresholds.events,Finset.mem_insert,Finset.mem_filter,Finset.mem_union,Finset.mem_image] at hr
  simp only [candidates,List.mem_append,List.mem_map,List.mem_ofFn]
  rcases hr with rfl | rfl | ⟨(⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩),hcell⟩
  · exact Or.inl (Or.inl ⟨j,List.mem_range.mpr (by omega),rfl⟩)
  · exact Or.inl (Or.inl ⟨j+1,List.mem_range.mpr (by omega),rfl⟩)
  · exact Or.inl (Or.inr ⟨v,by rw [max_eq_left hnonnegative,min_eq_right hdelta]⟩)
  · exact Or.inr ⟨v,by rw [max_eq_left hnonnegative,min_eq_right hdelta]⟩

theorem exists_good {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (direction:ℚ→ Bool)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0 < seed) (hd:0 < delta) (hp:0 < p)
    (hweight:weight capacity length≤ (p:ℚ) * seed)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u):
    ∃ r∈ candidates outDistance inDistance (RegionBudget.steps p) delta,
      0 < r∧ Good capacity length outDistance inDistance seed
        (slope (RegionBudget.steps p) delta) direction r:=by
  let k:=RegionBudget.steps p
  let values:=fun j => productVolume capacity length outDistance inDistance seed (grid k delta j)
  have hk:0 < k:=RegionBudget.steps_pos p
  have hpq:(1:ℚ)≤ p:=by exact_mod_cast hp
  have hstart:seed ^ 2≤ values 0:=
    (RegionInterval.budget capacity length outDistance inDistance seed _ hc hl hseed.le).1
  have hbudget:values k≤ 4 * (p:ℚ) ^ 2 * seed ^ 2:=
    RegionInterval.normalized_budget capacity length outDistance inDistance seed _ p
      hc hl hseed.le hpq hweight
  obtain ⟨j,hj,hnotDouble⟩:=FiniteRegionGrowth.exists_not_doubling values k seed p
    hseed hstart hbudget (RegionBudget.exceeds_budget p hp)
  by_contra h
  have hbad:∀ r∈ RegionThresholds.events outDistance inDistance
      (grid k delta j) (grid k delta (j + 1)),0 < r→
      slope k delta * volume capacity length outDistance seed r≤ boundary capacity outDistance r∨
      slope k delta * volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r≤
        boundary (fun u v => capacity v u) inDistance r:=by
    intro r hr hpos
    have hmem:r∈ candidates outDistance inDistance k delta:=by
      exact event_mem_candidates outDistance inDistance k delta j r hk hd.le hj hr
    have hfail:¬ Good capacity length outDistance inDistance seed (slope k delta) direction r:=by
      intro hg
      exact h ⟨r,hmem,hpos,hg⟩
    cases hdir:direction r with
    | false =>
      right
      exact le_of_not_ge (by simpa [Good,selectedBoundary,selectedVolume,hdir] using hfail)
    | true =>
      left
      exact le_of_not_ge (by simpa [Good,selectedBoundary,selectedVolume,hdir] using hfail)
  have hdoubled:=RegionCell.doubles capacity length outDistance inDistance seed
    (grid k delta j) (grid k delta (j + 1)) (slope k delta) hc hl hseed.le
    (grid_nonneg k delta j hd.le) (grid_mono k delta j hd.le)
    (by unfold slope; positivity) houtLip hinLip hbad
    (by rw [grid_width k delta j hk hd])
  exact (not_le_of_gt hnotDouble) hdoubled

theorem search_correct {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (direction:ℚ→ Bool)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0 < seed) (hd:0 < delta) (hp:0 < p)
    (hweight:weight capacity length≤ (p:ℚ) * seed)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u):
    ∃ r,search capacity length outDistance inDistance seed delta p direction=some r∧
      r∈ candidates outDistance inDistance (RegionBudget.steps p) delta∧
      0 < r∧ Good capacity length outDistance inDistance seed
        (slope (RegionBudget.steps p) delta) direction r:=by
  obtain ⟨r,hr,hpositive,hgood⟩:=exists_good capacity length outDistance inDistance
    seed delta p direction hc hl hseed hd hp hweight houtLip hinLip
  cases hs:search capacity length outDistance inDistance seed delta p direction with
  | none =>
    unfold search at hs
    have hnone:=List.find?_eq_none.mp hs r hr
    simp only [decide_eq_true_eq] at hnone
    exact False.elim (hnone ⟨hpositive,hgood⟩)
  | some result =>
    refine ⟨result,rfl,List.mem_of_find?_eq_some hs, ?_⟩
    have hfound:=List.find?_some hs
    simpa only [decide_eq_true_eq] using hfound

theorem search_radius {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (direction:ℚ→ Bool) (r:ℚ) (hd:0≤ delta)
    (hs:search capacity length outDistance inDistance seed delta p direction=some r):
    0 < r∧ r≤ delta:=by
  have hfound:0 < r∧ Good capacity length outDistance inDistance seed
      (slope (RegionBudget.steps p) delta) direction r:=by
    simpa only [decide_eq_true_eq] using List.find?_some hs
  exact ⟨hfound.1, (candidates_bound outDistance inDistance (RegionBudget.steps p) delta r
    (RegionBudget.steps_pos p) hd (List.mem_of_find?_eq_some hs)).2⟩

end Lax455465Proofs.RegionSearch

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionCharging

open RegionVolume

def chosenBall {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (direction:ℚ→ Bool) (r:ℚ):Finset (Fin n):=
  if direction r then ball outDistance r else ball inDistance r

end Lax455465Proofs.RegionCharging

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionSelection

open RegionCharging

theorem chosen_mass {n:ℕ} (weights outDistance inDistance:Fin n→ ℚ) (r:ℚ):
    (∑ v∈ chosenBall outDistance inDistance (direction weights outDistance inDistance) r,
      weights v)=min (ballMass weights outDistance r) (ballMass weights inDistance r):=by
  by_cases h:ballMass weights outDistance r≤ ballMass weights inDistance r
  · simp only [chosenBall,direction,decide_eq_true_eq,if_pos h,min_eq_left h]
    rfl
  · simp only [chosenBall,direction,decide_eq_true_eq,if_neg h,min_eq_right (le_of_not_ge h)]
    rfl

def eraseWeights {n:ℕ} (weights:Fin n→ ℚ) (S:Finset (Fin n)):Fin n→ ℚ:=
  fun v => if v∈ S then 0 else weights v

theorem root_correct {n:ℕ} (weights:Fin n→ ℚ)
    (hp:0 < (support weights).card):∃ root,chooseRoot weights=some root∧ 0 < weights root:=by
  obtain ⟨v,hv⟩:=Finset.card_pos.mp hp
  have hpositive:0 < weights v:=(Finset.mem_filter.mp hv).2
  cases hs:chooseRoot weights with
  | none =>
    unfold chooseRoot at hs
    have hfail:=List.find?_eq_none.mp hs v (List.mem_finRange v)
    simp only [decide_eq_true_eq] at hfail
    exact False.elim (hfail hpositive)
  | some root =>
    refine ⟨root,rfl, ?_⟩
    simpa only [decide_eq_true_eq] using List.find?_some hs

theorem support_erase {n:ℕ} (weights:Fin n→ ℚ) (S:Finset (Fin n)):
    support (eraseWeights weights S)=support weights \ S:=by
  ext v
  simp only [support,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,eraseWeights]
  split_ifs <;> simp_all

theorem support_decreases {n:ℕ} (weights:Fin n→ ℚ) (S:Finset (Fin n))
    (root:Fin n) (hroot:0 < weights root) (hmem:root∈ S):
    (support (eraseWeights weights S)).card < (support weights).card:=by
  rw [support_erase]
  apply Finset.card_lt_card
  have hsub:support weights \ S ⊆ support weights:=Finset.sdiff_subset
  exact (Finset.ssubset_iff_of_subset hsub).mpr
    ⟨root,by simp [support,hroot],by simp [hmem]⟩

theorem root_mem_chosen {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (chooseDirection:ℚ→ Bool) (r:ℚ) (root:Fin n)
    (hout:outDistance root=0) (hin:inDistance root=0) (hr:0 < r):
    root∈ chosenBall outDistance inDistance chooseDirection r:=by
  unfold chosenBall
  split_ifs <;> simp [ball,hout,hin,hr]

end Lax455465Proofs.RegionSelection

end

section

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.CutSweeps

open Lax455465.ProductNetwork Lax455465.RationalEncoding

instance {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    Decidable (admissibleQ I S):=inferInstanceAs (Decidable (_∧ _))

theorem massQ_nonneg {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    0≤ massQ I S:=by
  exact Finset.sum_nonneg (fun v _ => NNRat.coe_nonneg (I.weight v))

theorem capacityQ_nonneg {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    0≤ capacityQ I S:=by
  exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg
    (fun v _ => NNRat.coe_nonneg (I.capacity u v)))

theorem admissibleQ_iff_product_pos {n:ℕ} (I:RationalInstance n)
    (S:Finset (Fin n)):
    admissibleQ I S↔ 0 < massQ I S * massQ I Sᶜ:=by
  constructor
  · rintro ⟨hS,hSc⟩
    exact mul_pos hS hSc
  · intro h
    have hS:=massQ_nonneg I S
    have hSc:=massQ_nonneg I Sᶜ
    constructor <;> nlinarith

theorem demand_zero_of_not_admissible {n:ℕ} (I:RationalInstance n)
    (S:Finset (Fin n)) (h:¬ admissibleQ I S):
    massQ I S * massQ I Sᶜ=0:=by
  have hnonneg:=mul_nonneg (massQ_nonneg I S) (massQ_nonneg I Sᶜ)
  have hnot:¬ 0 < massQ I S * massQ I Sᶜ:=by
    simpa only [admissibleQ_iff_product_pos] using h
  exact le_antisymm (le_of_not_gt hnot) hnonneg

def choose {n:ℕ} (I:RationalInstance n):List (Finset (Fin n))→ Option (Finset (Fin n))
  | [] => none
  | S::rest =>
    match choose I rest with
    | none => if admissibleQ I S then some S else none
    | some T =>
      if admissibleQ I S∧ ratioQ I S≤ ratioQ I T then some S else some T

theorem choose_sound {n:ℕ} (I:RationalInstance n)
    (candidates:List (Finset (Fin n))) (S:Finset (Fin n))
    (h:choose I candidates=some S):S∈ candidates∧ admissibleQ I S:=by
  induction candidates with
  | nil => simp [choose] at h
  | cons T rest ih =>
    simp only [choose] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst S
        exact ⟨List.mem_cons_self,by assumption⟩
      · simp at h
    · rename_i U hU
      split at h
      · simp only [Option.some.injEq] at h
        subst S
        exact ⟨List.mem_cons_self, (by assumption:admissibleQ I T∧ _).1⟩
      · simp only [Option.some.injEq] at h
        subst S
        obtain ⟨hmem,hadm⟩:=ih hU
        exact ⟨List.mem_cons_of_mem _ hmem,hadm⟩

theorem choose_exists {n:ℕ} (I:RationalInstance n)
    (candidates:List (Finset (Fin n)))
    (hex:∃ S∈ candidates,admissibleQ I S):∃ S,choose I candidates=some S:=by
  induction candidates with
  | nil => simp at hex
  | cons T rest ih =>
    by_cases hrest:∃ S∈ rest,admissibleQ I S
    · obtain ⟨U,hU⟩:=ih hrest
      simp only [choose,hU]
      split <;> exact ⟨_,rfl⟩
    · have hnone:choose I rest=none:=by
        cases h:choose I rest with
        | none => rfl
        | some U =>
          obtain ⟨hmem,hadm⟩:=choose_sound I rest U h
          exact False.elim (hrest ⟨U,hmem,hadm⟩)
      obtain ⟨S,hmem,hadm⟩:=hex
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨S,by simp [choose,hnone,hadm]⟩
      · exact False.elim (hrest ⟨S,hmem,hadm⟩)

theorem choose_minimal {n:ℕ} (I:RationalInstance n)
    (candidates:List (Finset (Fin n))) (S T:Finset (Fin n))
    (h:choose I candidates=some S) (hT:T∈ candidates)
    (hvalid:admissibleQ I T):ratioQ I S≤ ratioQ I T:=by
  induction candidates generalizing S with
  | nil => simp at hT
  | cons U rest ih =>
    simp only [choose] at h
    split at h
    · rename_i hnone
      split at h
      · simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_rfl
        · obtain ⟨V,hV⟩:=choose_exists I rest ⟨T,hT,hvalid⟩
          rw [hnone] at hV
          cases hV
      · simp at h
    · rename_i V hV
      split at h
      · rename_i hbetter
        simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_rfl
        · exact hbetter.2.trans (ih V hV hT)
      · rename_i hnot
        simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_of_not_ge (fun hle => hnot ⟨hvalid,hle⟩)
        · exact ih V hV hT

def candidates {n:ℕ} (potential:Fin n→ ℚ):List (Finset (Fin n)):=
  (List.finRange n).map fun v => Finset.univ.filter fun u => potential u≤ potential v

end Lax455465Proofs.CutSweeps

end

section

open scoped BigOperators

namespace Lax455465Proofs.CutLayers

open Lax455465.RationalEncoding Lax455465Proofs.CutSweeps

structure Layers (n k:ℕ) where
  rank:Fin n→ Fin (k + 1)
  gap:Fin k→ ℚ
  gap_nonneg:∀ i,0≤ gap i

def potential {n k:ℕ} (L:Layers n k) (v:Fin n):ℚ:=
  ∑ i:Fin k,if i.val < (L.rank v).val then L.gap i else 0

def shore {n k:ℕ} (L:Layers n k) (i:Fin k):Finset (Fin n):=
  Finset.univ.filter fun v => (L.rank v).val≤ i.val

theorem difference {n k:ℕ} (L:Layers n k) (u v:Fin n)
    (h:(L.rank u).val≤ (L.rank v).val):
    potential L v - potential L u =
      ∑ i:Fin k,if (L.rank u).val≤ i.val∧ i.val < (L.rank v).val
        then L.gap i else 0:=by
  rw [potential,potential, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all <;> omega

theorem monotone {n k:ℕ} (L:Layers n k) (u v:Fin n)
    (h:(L.rank u).val≤ (L.rank v).val):potential L u≤ potential L v:=by
  have hd:=difference L u v h
  have hnonneg:0≤ ∑ i:Fin k,
      if (L.rank u).val≤ i.val∧ i.val < (L.rank v).val then L.gap i else 0:=
    Finset.sum_nonneg (fun i _ => by split_ifs; exact L.gap_nonneg i; exact le_rfl)
  linarith

theorem positive_difference {n k:ℕ} (L:Layers n k) (u v:Fin n):
    max (potential L v - potential L u) 0 =
      ∑ i:Fin k,if u∈ shore L i∧ v∉ shore L i then L.gap i else 0:=by
  simp only [shore,Finset.mem_filter,Finset.mem_univ,true_and,not_le]
  by_cases h:(L.rank u).val≤ (L.rank v).val
  · rw [max_eq_left (sub_nonneg.mpr (monotone L u v h)),difference L u v h]
  · have hrev:(L.rank v).val≤ (L.rank u).val:=by omega
    rw [max_eq_right (sub_nonpos.mpr (monotone L v u hrev))]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

private theorem complement_filter {n:ℕ} (S:Finset (Fin n)):
    (Finset.univ.filter fun v => v∉ S)=Sᶜ:=by
  ext v
  simp

theorem mass_product {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    massQ I S * massQ I Sᶜ =
      ∑ u:Fin n, ∑ v:Fin n,
        if u∈ S∧ v∉ S then (I.weight u:ℚ) * I.weight v else 0:=by
  simp only [massQ]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  symm
  simp_rw [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [← Finset.sum_filter]
  simp [complement_filter]

theorem capacity_expansion {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    capacityQ I S =
      ∑ u:Fin n, ∑ v:Fin n,
        if u∈ S∧ v∉ S then (I.capacity u v:ℚ) else 0:=by
  simp only [capacityQ]
  symm
  simp_rw [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [← Finset.sum_filter]
  simp [complement_filter]

theorem demand_identity {n k:ℕ} (I:RationalInstance n) (L:Layers n k):
    (∑ u:Fin n, ∑ v:Fin n,
      (I.weight u:ℚ) * I.weight v * max (potential L v - potential L u) 0) =
      ∑ i:Fin k,L.gap i * (massQ I (shore L i) * massQ I (shore L i)ᶜ):=by
  simp_rw [positive_difference,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [mass_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

theorem capacity_identity {n k:ℕ} (I:RationalInstance n) (L:Layers n k):
    (∑ u:Fin n, ∑ v:Fin n,
      (I.capacity u v:ℚ) * max (potential L v - potential L u) 0) =
      ∑ i:Fin k,L.gap i * capacityQ I (shore L i):=by
  simp_rw [positive_difference,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [capacity_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

end Lax455465Proofs.CutLayers

end

section

open scoped BigOperators

namespace Lax455465Proofs.ThresholdRounding

open Lax455465.RationalEncoding Lax455465Proofs.CutSweeps Lax455465Proofs.CutLayers

def separation {n k:ℕ} (I:RationalInstance n) (L:Layers n k):ℚ:=
  ∑ u:Fin n, ∑ v:Fin n,
    (I.weight u:ℚ) * I.weight v * max (potential L v - potential L u) 0

def edgeCost {n k:ℕ} (I:RationalInstance n) (L:Layers n k):ℚ:=
  ∑ u:Fin n, ∑ v:Fin n,
    (I.capacity u v:ℚ) * max (potential L v - potential L u) 0

def layerCandidates {n k:ℕ} (L:Layers n k):List (Finset (Fin n)):=
  List.ofFn (shore L)

def round {n k:ℕ} (I:RationalInstance n) (L:Layers n k):
    Option (Finset (Fin n)):=choose I (layerCandidates L)

private theorem admissible_layer {n k:ℕ} (I:RationalInstance n) (L:Layers n k)
    (hsep:0 < separation I L):∃ i:Fin k,admissibleQ I (shore L i):=by
  by_contra h
  have hzero:∀ i:Fin k,massQ I (shore L i) * massQ I (shore L i)ᶜ=0:=by
    intro i
    apply demand_zero_of_not_admissible
    exact fun hi => h ⟨i,hi⟩
  have hid:=demand_identity I L
  change separation I L=_ at hid
  simp only [hzero,mul_zero,Finset.sum_const_zero] at hid
  exact (ne_of_gt hsep) hid

theorem round_spec {n k:ℕ} (I:RationalInstance n) (L:Layers n k)
    (hsep:0 < separation I L):
    ∃ S,round I L=some S∧ admissibleQ I S∧
      ratioQ I S≤ edgeCost I L / separation I L:=by
  obtain ⟨i,hi⟩:=admissible_layer I L hsep
  have himem:shore L i∈ layerCandidates L:=List.mem_ofFn.mpr ⟨i,rfl⟩
  obtain ⟨S,hS⟩:=choose_exists I (layerCandidates L) ⟨_,himem,hi⟩
  have hvalid:=(choose_sound I _ _ hS).2
  refine ⟨S,hS,hvalid, (le_div_iff₀ hsep).mpr ?_⟩
  have hcut:∀ j:Fin k,
      ratioQ I S * (massQ I (shore L j) * massQ I (shore L j)ᶜ)≤
        capacityQ I (shore L j):=by
    intro j
    by_cases hj:admissibleQ I (shore L j)
    · have hjmem:shore L j∈ layerCandidates L:=List.mem_ofFn.mpr ⟨j,rfl⟩
      have hmin:=choose_minimal I _ S (shore L j) hS hjmem hj
      unfold ratioQ at hmin
      exact (le_div_iff₀ ((admissibleQ_iff_product_pos I _).mp hj)).mp hmin
    · rw [demand_zero_of_not_admissible I _ hj,mul_zero]
      exact capacityQ_nonneg I _
  change ratioQ I S * (∑ u, ∑ v,_)≤ ∑ u, ∑ v,_
  rw [demand_identity,capacity_identity,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hbound:=mul_le_mul_of_nonneg_left (hcut j) (L.gap_nonneg j)
  nlinarith

theorem edgeCost_le {n k:ℕ} (I:RationalInstance n) (L:Layers n k)
    (length:Fin n→ Fin n→ ℚ)
    (hnonneg:∀ u v,0≤ length u v)
    (hlip:∀ u v,potential L v - potential L u≤ length u v):
    edgeCost I L≤ ∑ u, ∑ v, (I.capacity u v:ℚ) * length u v:=by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (max_le (hlip u v) (hnonneg u v))
    (NNRat.coe_nonneg (I.capacity u v))

end Lax455465Proofs.ThresholdRounding

end

section

open scoped BigOperators

namespace Lax455465Proofs.PotentialLayers

open CutLayers

def values {n:ℕ} (a:Fin n→ ℚ):List ℚ:=
  (List.ofFn a).mergeSort (·≤ ·)

theorem values_length {n:ℕ} (a:Fin n→ ℚ):(values a).length=n:=by
  simp [values]

theorem value_mem {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):a v∈ values a:=by
  exact List.mem_mergeSort.mpr (List.mem_ofFn.mpr ⟨v,rfl⟩)

def level (xs:List ℚ) (i:ℕ):ℚ:=xs.getD (min i (xs.length - 1)) 0

theorem level_monotone (xs:List ℚ) (hs:xs.SortedLE):Monotone (level xs):=by
  intro i j hij
  cases xs with
  | nil => simp [level]
  | cons x xs =>
    have hi:min i ((x::xs).length - 1) < (x::xs).length:=by
      simp only [List.length_cons]
      omega
    have hj:min j ((x::xs).length - 1) < (x::xs).length:=by
      simp only [List.length_cons]
      omega
    unfold level
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
    exact hs.monotone_get (min_le_min_right _ hij)

def rank {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):Fin (n + 1):=
  ⟨(values a).idxOf (a v),by
    have h:=List.idxOf_lt_length_of_mem (value_mem a v)
    rw [values_length] at h
    omega⟩

theorem level_rank {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):
    level (values a) (rank a v).val=a v:=by
  have h:=List.idxOf_lt_length_of_mem (value_mem a v)
  have hle:(values a).idxOf (a v)≤ (values a).length - 1:=by omega
  unfold level rank
  rw [min_eq_left hle,List.getD_eq_getElem _ _ h]
  exact List.getElem_idxOf h

def build {n:ℕ} (a:Fin n→ ℚ):Layers n n where
  rank:=rank a
  gap i:=level (values a) i.succ.val - level (values a) i.castSucc.val
  gap_nonneg i:=sub_nonneg.mpr
    (level_monotone _ List.sortedLE_mergeSort (by simp))

private theorem prefix_step {k:ℕ} (f:Fin k→ ℚ) (r:Fin k):
    (∑ i:Fin k,if i.val < r.succ.val then f i else 0) =
      (∑ i:Fin k,if i.val < r.castSucc.val then f i else 0) + f r:=by
  have hterm:∀ i:Fin k,
      (if i.val < r.succ.val then f i else 0) =
        (if i.val < r.castSucc.val then f i else 0) + (if i=r then f i else 0):=by
    intro i
    by_cases hir:i=r
    · subst i
      simp
    · have hval:i.val ≠ r.val:=fun h => hir (Fin.ext h)
      simp only [Fin.val_succ,Fin.val_castSucc,if_neg hir,add_zero]
      have hpred:i.val < r.val + 1↔ i.val < r.val:=by omega
      simp only [hpred]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

theorem telescope {k:ℕ} (a:Fin (k + 1)→ ℚ) (r:Fin (k + 1)):
    (∑ i:Fin k,if i.val < r.val then a i.succ - a i.castSucc else 0)=a r - a 0:=by
  refine Fin.induction ?_ ?_ r
  · simp
  · intro i ih
    rw [prefix_step,ih]
    ring

theorem potential_eq {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):
    potential (build a) v=a v - level (values a) 0:=by
  change (∑ i:Fin n,if i.val < (rank a v).val then
    level (values a) i.succ.val - level (values a) i.castSucc.val else 0)=_
  rw [telescope (fun i:Fin (n + 1) => level (values a) i.val) (rank a v),level_rank]
  rfl

theorem difference_eq {n:ℕ} (a:Fin n→ ℚ) (u v:Fin n):
    potential (build a) v - potential (build a) u=a v - a u:=by
  rw [potential_eq,potential_eq]
  ring

open Lax455465.RationalEncoding CutSweeps

def separation {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):ℚ:=
  ∑ u, ∑ v, (I.weight u:ℚ) * I.weight v * max (a v - a u) 0

def edgeCost {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):ℚ:=
  ∑ u, ∑ v, (I.capacity u v:ℚ) * max (a v - a u) 0

private theorem separation_build {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):
    ThresholdRounding.separation I (build a)=separation I a:=by
  simp only [ThresholdRounding.separation,separation,difference_eq]

private theorem edgeCost_build {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):
    ThresholdRounding.edgeCost I (build a)=edgeCost I a:=by
  simp only [ThresholdRounding.edgeCost,edgeCost,difference_eq]

def round {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):Option (Finset (Fin n)):=
  ThresholdRounding.round I (build a)

theorem round_spec {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ)
    (hsep:0 < separation I a):
    ∃ S,round I a=some S∧ admissibleQ I S∧ ratioQ I S≤ edgeCost I a / separation I a:=by
  simpa only [round,separation_build,edgeCost_build] using
    ThresholdRounding.round_spec I (build a) (by simpa only [separation_build] using hsep)

theorem edgeCost_le {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ)
    (length:Fin n→ Fin n→ ℚ) (hnonneg:∀ u v,0≤ length u v)
    (hlip:∀ u v,a v - a u≤ length u v):
    edgeCost I a≤ ∑ u, ∑ v, (I.capacity u v:ℚ) * length u v:=by
  rw [← edgeCost_build]
  exact ThresholdRounding.edgeCost_le I (build a) length hnonneg
    (by simpa only [difference_eq] using hlip)

end Lax455465Proofs.PotentialLayers

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

inductive Result (n:ℕ) where
  | large:Region n→ Result n
  | regions:List (Region n)→ Result n

def run {n:ℕ} (I:RationalInstance n) (d:Distance n) (seed delta:ℚ) (p:ℕ):
    ℕ→ Finset (Fin n)→ Option (Result n)
  | 0,active =>
    if chooseRoot (weights I active)=none then some (.regions []) else none
  | fuel + 1,active =>
    match chooseRoot (weights I active) with
    | none => some (.regions [])
    | some root =>
      match RegionSearch.search (capacity I active) d (d root) (fun v => d v root)
        seed delta p (chooseDirection I d active root) with
      | none => none
      | some r =>
        let R:Region n:= ⟨root,r,chooseDirection I d active root r⟩
        if (2 / 3:ℚ) * LargeBallRounding.total I≤ ∑ v∈ R.ball d,weights I active v then
          some (.large R)
        else
          (run I d seed delta p fuel (active \ R.ball d)).map fun result =>
            match result with
            | .large T => .large T
            | .regions rest => .regions (R::rest)

theorem weights_le {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)) (v:Fin n):
    weights I active v≤ (I.weight v:ℚ):=by
  unfold weights
  split_ifs
  · exact le_rfl
  · exact NNRat.coe_nonneg _

theorem capacity_nonnegative {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    ∀ u v,0≤ capacity I active u v:=by
  intro u v
  unfold capacity
  split_ifs <;> positivity

theorem residual_cost_le {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (active:Finset (Fin n)) (hd:Nonnegative d):
    weight (capacity I active) d≤ weight (fun u v => (I.capacity u v:ℚ)) d:=by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (hd u v)
  unfold capacity
  split_ifs
  · exact le_rfl
  · exact NNRat.coe_nonneg _

theorem weights_remove {n:ℕ} (I:RationalInstance n) (active S:Finset (Fin n)):
    weights I (active \ S)=eraseWeights (weights I active) S:=by
  funext v
  simp only [weights,eraseWeights,Finset.mem_sdiff]
  split_ifs <;> (try simp_all)

theorem root_none_iff {n:ℕ} (w:Fin n→ ℚ):
    chooseRoot w=none↔ (support w).card=0:=by
  constructor
  · intro h
    by_contra hn
    obtain ⟨root,hr,_⟩:=root_correct w (by omega)
    rw [h] at hr
    cases hr
  · intro h
    unfold chooseRoot
    apply List.find?_eq_none.mpr
    intro v _
    simp only [decide_eq_true_eq]
    intro hv
    have hmem:v∈ support w:=by simp [support,hv]
    have hpos:=Finset.card_pos.mpr ⟨v,hmem⟩
    omega

theorem run_correct {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (seed delta:ℚ) (p fuel:ℕ)
    (hd:Nonnegative d) (hdiag:∀ v,d v v=0)
    (htri:∀ u v w,d u w≤ d u v + d v w)
    (hseed:0 < seed) (hdelta:0 < delta) (hp:0 < p)
    (hcost:weight (fun u v => (I.capacity u v:ℚ)) d≤ (p:ℚ) * seed)
    (active:Finset (Fin n)) (hfuel:(support (weights I active)).card≤ fuel):
    ∃ result,run I d seed delta p fuel active=some result∧
      match result with
      | .large R => LargeGood I d delta R
      | .regions history => ValidHistory I d seed delta p active history∧
          history.length≤ (support (weights I active)).card:=by
  induction fuel generalizing active with
  | zero =>
    have hz:(support (weights I active)).card=0:=by omega
    have hn:=(root_none_iff _).mpr hz
    refine ⟨.regions [], ?_,hz, ?_⟩
    · simp only [run,hn, ↓reduceIte]
    · simp
  | succ fuel ih =>
    cases hr:chooseRoot (weights I active) with
    | none =>
      refine ⟨.regions [], ?_, (root_none_iff _).mp hr, ?_⟩
      · simp only [run,hr]
      · simp
    | some root =>
      have hroot:0 < weights I active root:=by
        simpa only [decide_eq_true_eq] using List.find?_some hr
      obtain ⟨r,hs,_,_,hgood⟩:=RegionSearch.search_correct (capacity I active) d
        (d root) (fun v => d v root) seed delta p (chooseDirection I d active root)
        (capacity_nonnegative I active) hd hseed hdelta hp
        ((residual_cost_le I d active hd).trans hcost)
        (fun u v => by linarith [htri root u v])
        (fun u v => by linarith [htri v u root])
      let R:Region n:= ⟨root,r,chooseDirection I d active root r⟩
      have hball:R.ball d=chosenBall (d root) (fun v => d v root)
          (chooseDirection I d active root) r:=rfl
      have hrad:=RegionSearch.search_radius (capacity I active) d (d root) (fun v => d v root)
        seed delta p (chooseDirection I d active root) r hdelta.le hs
      by_cases hlarge:(2 / 3:ℚ) * LargeBallRounding.total I≤ ∑ v∈ R.ball d,weights I active v
      · have hmin:(2 / 3:ℚ) * LargeBallRounding.total I≤
            min (ballMass (weights I active) (d root) r)
              (ballMass (weights I active) (fun v => d v root) r):=by
          rw [← chosen_mass]
          simpa only [chooseDirection,hball] using hlarge
        have hout:=(le_min_iff.mp hmin).1
        have hin:=(le_min_iff.mp hmin).2
        have hmassOut:ballMass (weights I active) (d root) r≤
            LargeBallRounding.mass I (RegionCharging.ball (d root) r):=
          Finset.sum_le_sum fun v _ => weights_le I active v
        have hmassIn:ballMass (weights I active) (fun v => d v root) r≤
            LargeBallRounding.mass I (RegionCharging.ball (fun v => d v root) r):=
          Finset.sum_le_sum fun v _ => weights_le I active v
        refine ⟨.large R, ?_,hrad.1,hrad.2,hout.trans hmassOut,hin.trans hmassIn⟩
        dsimp only [R] at hlarge ⊢
        simp only [run,hr,hs,if_pos hlarge]
      · have hmem:root∈ R.ball d:=by
          rw [hball]
          exact root_mem_chosen _ _ _ r root (hdiag root) (hdiag root) hrad.1
        have hprogress:(support (weights I (active \ R.ball d))).card <
            (support (weights I active)).card:=by
          rw [weights_remove]
          exact support_decreases _ _ root hroot hmem
        have hstep:StepGood I d seed delta p active R:=
          ⟨hroot,hrad.1,hrad.2,rfl,hgood,lt_of_not_ge hlarge⟩
        obtain ⟨result,hrun,hvalid⟩:=ih (active \ R.ball d) (by omega)
        cases result with
        | large T =>
          refine ⟨.large T, ?_,hvalid⟩
          dsimp only [R] at hlarge hrun ⊢
          simp only [run,hr,hs,if_neg hlarge,hrun,Option.map_some]
        | regions rest =>
          refine ⟨.regions (R::rest), ?_, ⟨hstep,hvalid.1⟩, ?_⟩
          · dsimp only [R] at hlarge hrun ⊢
            simp only [run,hr,hs,if_neg hlarge,hrun,Option.map_some]
          · have hlen:=hvalid.2
            simp only [List.length_cons]
            omega

end Lax455465Proofs.RegionLoop

end

section

namespace Lax455465Proofs.MetricCostData

open Lax455465.RationalEncoding DirectedFlowLP MetricMatrix
open scoped BigOperators NNRat

theorem products_eq {n:ℕ} (a b:Matrix n):
    RamProductSum.products (values a) (values b)=values (fun u v => a u v*b u v):=by
  apply List.ext_getElem
  · simp only [RamProductSum.products,List.length_ofFn,length_values]
  · intro i hi hj
    have he:i < n*n:=by simpa only [RamProductSum.products,List.length_ofFn,length_values] using hi
    rw [RamProductSum.value_at (values a) (values b) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

theorem coe_cost {n:ℕ} (I:RationalInstance n) (d:Matrix n):
    (cost I d:ℚ)=RegionRounding.metricCost I (rational d):=by
  unfold cost
  rw [products_eq]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
  simp only [NNRat.cast_sum,NNRat.coe_mul,RegionRounding.metricCost,RegionVolume.weight,rational]

end Lax455465Proofs.MetricCostData

end

section

namespace Lax455465Proofs.RationalSumHeight

open scoped NNRat

def denominator (qs:List ℚ≥0):ℕ:=(qs.map NNRat.den).prod

theorem denominator_pos (qs:List ℚ≥0):0 < denominator qs:=by
  induction qs with
  | nil => simp [denominator]
  | cons a qs ih => simpa only [denominator,List.map_cons,List.prod_cons] using Nat.mul_pos a.den_pos ih

theorem denominator_dvd (qs:List ℚ≥0) (q:ℚ≥0) (hq:q∈ qs):
    q.den ∣ denominator qs:=by
  exact List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩)

theorem sum_denominator (qs:List ℚ≥0) (D:ℕ) (h:∀ q∈ qs,q.den ∣ D):
    ((qs.sum:ℚ≥0):ℚ).den ∣ D:=by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.sum_cons,NNRat.coe_add]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (h q (by simp))
      (ih (fun a ha => h a (by simp [ha]))))

theorem sum_value (qs:List ℚ≥0) (M:ℕ) (hnum:∀ q∈ qs,q.num≤ M):
    ((qs.sum:ℚ≥0):ℚ)≤ qs.length*M:=by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hq:=MetricHeight.value_bound (q:ℚ) q.coe_nonneg M (by simpa only [NNRat.natAbs_num_coe] using hnum q (by simp))
    have hi:=ih (fun a ha => hnum a (by simp [ha]))
    simp only [List.sum_cons,NNRat.coe_add,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem prefix_height (qs:List ℚ≥0) (M:ℕ) (hM:1≤ M)
    (hnum:∀ q∈ qs,q.num≤ M) (k:ℕ):
    LpInputSize.Height ((qs.length+1)*M*denominator qs) (((qs.take k).sum:ℚ≥0):ℚ):=by
  apply MetricHeight.height_of_denominator _ (NNRat.coe_nonneg _) ((qs.length+1)*M) (denominator qs)
    (by nlinarith) (denominator_pos qs)
    (sum_denominator (qs.take k) _ (fun q hq => denominator_dvd qs q (List.mem_of_mem_take hq)))
  have hval:=sum_value (qs.take k) M (fun q hq => hnum q (List.mem_of_mem_take hq))
  have hlen:(qs.take k).length≤ qs.length+1:=by simp only [List.length_take]; omega
  push_cast
  have hlenq:((qs.take k).length:ℚ)≤ (qs.length:ℚ)+1:=by exact_mod_cast hlen
  simpa only [NNRat.cast_listSum] using hval.trans (mul_le_mul_of_nonneg_right hlenq (Nat.cast_nonneg M))

theorem denominator_bound (qs:List ℚ≥0) (w:ℕ) (hden:∀ q∈ qs,q.den≤ 2^w):
    denominator qs≤ 2^(w*qs.length):=by
  induction qs with
  | nil => simp [denominator]
  | cons q qs ih =>
    have hd:=hden q (by simp)
    have hi:=ih (fun a ha => hden a (by simp [ha]))
    calc
      denominator (q::qs)=q.den*denominator qs:=by simp [denominator]
      _≤ 2^w*2^(w*qs.length):=Nat.mul_le_mul hd hi
      _=2^(w*(q::qs).length):=by simp only [List.length_cons]; rw [←Nat.pow_add]; congr 1; ring

theorem prefix_word_height (qs:List ℚ≥0) (w:ℕ)
    (hnum:∀ q∈ qs,q.num≤ 2^w) (hden:∀ q∈ qs,q.den≤ 2^w) (k:ℕ):
    LpInputSize.Height ((qs.length+1)*2^(w*(qs.length+1))) (((qs.take k).sum:ℚ≥0):ℚ):=by
  apply LpInputSize.height_mono (prefix_height qs (2^w) (by have:=Nat.two_pow_pos w; omega) hnum k)
  calc
    (qs.length+1)*2^w*denominator qs≤ (qs.length+1)*2^w*2^(w*qs.length):=
      Nat.mul_le_mul_left _ (denominator_bound qs w hden)
    _=_:=by rw [Nat.mul_assoc,←Nat.pow_add]; congr 2; ring

theorem prefix_dyadic_height (qs:List ℚ≥0) (w:ℕ)
    (hnum:∀ q∈ qs,q.num≤ 2^w) (hden:∀ q∈ qs,q.den≤ 2^w) (k:ℕ):
    LpInputSize.Height (2^(w*(qs.length+1)+qs.length+1)) (((qs.take k).sum:ℚ≥0):ℚ):=by
  apply LpInputSize.height_mono (prefix_word_height qs w hnum hden k)
  calc
    (qs.length+1)*2^(w*(qs.length+1))≤ 2^(qs.length+1)*2^(w*(qs.length+1)):=
      Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
    _=_:=by rw [←Nat.pow_add]; congr 1; omega

end Lax455465Proofs.RationalSumHeight

end

section

namespace Lax455465Proofs.MetricCostHeight

open Lax455465.RationalEncoding LpInputSize MetricMatrix
open scoped NNRat

def exponent (n L K:ℕ):ℕ:=(L+K)*(n*n+1)+n*n+1

theorem products_height {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind) (I:RationalInstance n)
    (d:Matrix n) (K:ℕ) (hd:∀ u v,Height (2^K) (d u v:ℚ)):
    ∀ q∈ RamProductSum.products (values I.capacity) (values d),
      Height (2^(Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)+K)) (q:ℚ):=by
  rw [MetricCostData.products_eq]
  intro q hq
  obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
  let uv:=(DirectedFlowLP.edgeIndex n).symm e
  have h:=height_mul (capacity_height kind I uv.1 uv.2) (hd uv.1 uv.2)
  rw [←Nat.pow_add] at h
  exact h

theorem prefix_height {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind) (I:RationalInstance n)
    (d:Matrix n) (K:ℕ) (hd:∀ u v,Height (2^K) (d u v:ℚ)) (i:ℕ):
    Height (2^(exponent n (Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)) K))
      ((((RamProductSum.products (values I.capacity) (values d)).take i).sum:ℚ≥0):ℚ):=by
  have hh:=products_height kind I d K hd
  have hnum:∀ q∈ RamProductSum.products (values I.capacity) (values d),
      q.num≤ 2^(Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)+K):=by
    intro q hq
    simpa only [NNRat.natAbs_num_coe] using (hh q hq).1
  have hden:∀ q∈ RamProductSum.products (values I.capacity) (values d),
      q.den≤ 2^(Lax759944.BinaryWordEncoding.bitSize (encodeInput kind I)+K):=by
    intro q hq
    simpa only [NNRat.den_coe] using (hh q hq).2
  simpa only [RamProductSum.products,List.length_ofFn,length_values,exponent] using
    RationalSumHeight.prefix_dyadic_height _ _ hnum hden i

end Lax455465Proofs.MetricCostHeight

end

section

namespace Lax455465Proofs.RamUnsignedScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem load_spec (B:ℕ) (name:String) (q:ℚ≥0) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B)
    (hfresh:name ++ ".n" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.n"):
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  have hv:=RamUnsignedArithmetic.value q
  have hns:=Ne.symm hfresh.1
  have hds:=Ne.symm hfresh.2.1
  have hdn:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c3:String:=c2 ".n"; let c4:Nat:=Env.vars c1 c3; let c5:Env:=Env.setVar c1 "rat.n" c4; let c6:String:=c2 ".d"; let c7:Nat:=Env.vars c5 c6; let c8:Env:=Env.setVar c5 "rat.d" c7; let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); let c12:Expr:=Expr.var c3; let c13:Nat:=c10 (Expr.size c12); let c14:Expr:=Expr.var c6; let c15:Nat:=c10 (Expr.size c14); let c16:Nat:=c9 c13 c15; let c17:Com:=Com.assign "rat.n" c12; let c18:Com:=Com.assign "rat.d" c14; @Exists.intro Env (fun (σ':Env) => And (Run B (load name) σ σ' ((6:Nat))) (c0 σ')) c8 (@And.intro (Run B (load name) σ c8 ((6:Nat))) (c0 c8) (RunStep.mono B (load name) σ c8 (c9 c11 c16) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c17 c18) σ c1 c8 c11 c16 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6578_0_0_0))) (RunStep.seq B c17 c18 c1 c5 c8 c13 c15 (RunStep.assign B c1 "rat.n" c12 c4 (RunStep.eval_var B c1 c3 ?_)) (RunStep.assign B c5 "rat.d" c14 c7 (RunStep.eval_var B c5 c6 ?_)))) (?nAX_g6578_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6578_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6578_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem save_spec (B:ℕ) (name:String) (q:ℚ≥0)
    (hn:q.num < B) (hd:q.den < B) (hfresh:name ++ ".n" ≠ "rat.d"):
    Spec B (FractionOutput (q:ℚ)) (save name) (fun _ τ => Stored name q τ) 4:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  have hdn:=Ne.symm hfresh
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Stored name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".n"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.n"); let c4:String:=c1 ".d"; let c5:Nat:=Env.vars c3 "rat.d"; let c6:Env:=Env.setVar c3 c4 c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.var "rat.n")); let c10:Nat:=c8 (Expr.size (Expr.var "rat.d")); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((4:Nat))) (c0 σ')) c6 (@And.intro (Run B (save name) σ c6 ((4:Nat))) (c0 c6) (RunStep.mono B (save name) σ c6 (c7 c9 c10) ((4:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.n")) (Com.assign c4 (Expr.var "rat.d")) σ c3 c6 c9 c10 (RunStep.assign B σ c2 (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g6579_0_0_0))) (RunStep.assign B c3 c4 (Expr.var "rat.d") c5 (RunStep.eval_var B c3 "rat.d" ?_))) (?nAX_g6579_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6579_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6579_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

end Lax455465Proofs.RamUnsignedScalar

end

section

namespace Lax455465Proofs.RamMetricCostResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding

theorem height_bound (metricWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    MetricCostHeight.exponent n (bitSize (encodeInput kind I)) (metricWord.eval (bitSize (encodeInput kind I)))≤
      (heightBound metricWord).eval (bitSize (encodeInput kind I)):=by
  let L:=bitSize (encodeInput kind I)
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hnn:n*n+1≤ L^2+1:=by nlinarith
  simp only [heightBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow]
  dsimp only [MetricCostHeight.exponent]
  have hh:=Nat.mul_le_mul_left (L+metricWord.eval L+1) hnn
  dsimp only [L] at hh
  nlinarith

end Lax455465Proofs.RamMetricCostResources

end

section

namespace Lax455465Proofs.RamBooleanArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem command_spec (B:ℕ) (mode:Option Bool) (a b:Bool) (h1:1 < B):
    Spec B (fractionInputs 0 (bit a).num 1 0 (bit b).num 1) (command mode)
      (fun _ τ => FractionOutput (bit (flag mode a b):ℚ) τ) 10:=by
  cases mode with
  | none =>
    cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> (first
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) false false)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) false true)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) true false)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) true true)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                )
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega
  | some mode =>
    cases mode <;> cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> (first
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) false false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) false true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) true false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) true true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) false false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) false true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) true false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) true true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                               )
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega

end Lax455465Proofs.RamBooleanArithmetic

end

section

namespace Lax455465Proofs.RamArraySum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def Context (array:String) (qs:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "sum.count"=qs.length∧ Prefix (RamUnsignedBuffer.encode qs) array σ

theorem command_spec (B M:ℕ) (array:String) (qs:List ℚ≥0) (hB:2*M^2+3 < B)
    (hindex:2*qs.length+2 < B)
    (hnum:∀ q∈ qs,q.num≤ M) (hden:∀ q∈ qs,q.den≤ M)
    (hprefixNum:∀ i, (qs.take i).sum.num≤ M) (hprefixDen:∀ i, (qs.take i).sum.den≤ M):
    Spec B (Context array qs) (command array)
      (fun _ τ => Context array qs τ∧ FractionOutput ((qs.sum:ℚ≥0):ℚ) τ)
      ((36*(M^2).size+134)*qs.length+16):=by
  have hM:M < B:=by nlinarith
  have hread:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => Context array qs σ∧ σ.vars "sum.i"=i)
        (RamUnsignedBuffer.read array "sum.i")
        (fun _ τ => Context array qs τ∧ FractionOutput (qs[i]:ℚ) τ) 14:=by
    intro i hi σ hσ
    have hq:qs[i]∈ qs:=List.getElem_mem hi
    obtain ⟨τ,rr,pr⟩:=RamUnsignedBuffer.read_spec B array "sum.i" qs i hi (by nlinarith)
      (by omega) ((hnum _ hq).trans_lt hM) ((hden _ hq).trans_lt hM) (by decide) σ ⟨hσ.1.2,hσ.2⟩
    refine ⟨τ,rr,?_,pr.1⟩
    simpa only [Context,Prefix,rr.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
      rr.frame_arr array (by simp [RamUnsignedBuffer.read,Com.warrs])] using hσ.1
  have hf:=RamUnsignedSum.command_spec B M 14 (Context array qs) "sum.i" "sum.count" qs
    (RamUnsignedBuffer.read array "sum.i") hB (by omega) hnum hden hprefixNum hprefixDen
    (fun _ h => h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hread (by decide) (by simp [RamUnsignedBuffer.read,Com.wvars])
    (by simp [RamUnsignedBuffer.read,Com.wvars])
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),rr.frame_arr array (by change array∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),rr.frame_arr array (by change array∉ ([]:List String); simp)] using h)
  unfold command
  convert hf using 1 <;> ring

end Lax455465Proofs.RamArraySum

end

section

namespace Lax455465Proofs.RamMaskedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

@[simp] theorem length_coefficients (qs ms:List ℚ≥0):(coefficients qs ms).length=qs.length:=List.length_ofFn

def Context (source mask:String) (qs ms:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "sum.count"=qs.length∧ Prefix (RamUnsignedBuffer.encode qs) source σ∧
    Prefix (RamUnsignedBuffer.encode ms) mask σ

theorem coefficient_at (qs ms:List ℚ≥0) (hlen:ms.length=qs.length) (i:ℕ) (hi:i < qs.length):
    (coefficients qs ms)[i]'(by simpa only [coefficients,List.length_ofFn] using hi) =
      if (ms[i]'(by omega)).num=1 then qs[i] else 0:=by
  simp only [coefficients,List.getElem_ofFn,List.getD_eq_get ms 0 (⟨i,by omega⟩:Fin ms.length)]
  rfl

theorem entry_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (i:ℕ) (hi:i < qs.length) (hB:2*M^2+3 < B)
    (hindex:2*i+1 < B) (hqn:qs[i].num≤ M) (hqd:qs[i].den≤ M)
    (hmn:(ms[i]'(by omega)).num≤ M) (hmd:(ms[i]'(by omega)).den≤ M):
    Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "sum.i"=i) (entry source mask)
      (fun _ τ => Context source mask qs ms τ∧ FractionOutput ((coefficients qs ms)[i]'(by simpa only [length_coefficients] using hi):ℚ) τ) 32:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hmi:i < ms.length:=by omega
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rm,pm⟩:=RamUnsignedBuffer.read_spec B mask "sum.i" ms i hmi (by nlinarith) hindex
    (hmn.trans_lt hM) (hmd.trans_lt hM) (by decide) σ ⟨hctx.2.2,hidx⟩
  have hnum:ν.vars "rat.n"=ms[i].num:=by simpa only [NNRat.natAbs_num_coe] using pm.1.2.1
  have hctxν:Context source mask qs ms ν:=by
    simpa only [Context,Prefix,rm.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
      rm.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
      rm.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctx
  have hidxν:ν.vars "sum.i"=i:=(rm.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hidx
  have hc:(Cond.eq (.var "rat.n") (.lit 1)).evalB B ν=some (decide (ms[i].num=1)):=by
    rw [evalB_condEq (evalB_var (hnum ▸ hmn.trans_lt hM)) (evalB_lit h1),hnum]
    congr 1
  by_cases hm:ms[i].num=1
  · obtain ⟨τ,rq,pq⟩:=RamUnsignedBuffer.read_spec B source "sum.i" qs i hi (by nlinarith) hindex
      (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) ν ⟨hctxν.2.1,hidxν⟩
    have rr:=rm.seq (Run.ite_true (d:=RamFractionPrimitives.zero) (by simpa only [hm,decide_true] using hc) rq)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rq.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
        rq.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
        rq.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_pos hm] using pq.1
  · obtain ⟨τ,rz,pz⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    have rr:=rm.seq (Run.ite_false (c:=RamUnsignedBuffer.read source "sum.i") (by simpa only [hm,decide_false] using hc) rz)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rz.frame_var "sum.count" (by decide),rz.frame_arr source (by change source∉ ([]:List String); simp),
        rz.frame_arr mask (by change mask∉ ([]:List String); simp)] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_neg hm,NNRat.coe_zero] using pz

theorem command_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (hB:2*M^2+3 < B) (hindex:2*qs.length+2 < B)
    (hqn:∀ q∈ qs,q.num≤ M) (hqd:∀ q∈ qs,q.den≤ M)
    (hmn:∀ q∈ ms,q.num≤ M) (hmd:∀ q∈ ms,q.den≤ M)
    (hprefixNum:∀ i, ((coefficients qs ms).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((coefficients qs ms).take i).sum.den≤ M):
    Spec B (Context source mask qs ms) (command source mask)
      (fun _ τ => Context source mask qs ms τ∧ FractionOutput (((coefficients qs ms).sum:ℚ≥0):ℚ) τ)
      ((36*(M^2).size+152)*qs.length+16):=by
  have hM1:1≤ M:=by simpa only [List.take_zero,List.sum_nil,NNRat.den_zero] using hprefixDen 0
  have hnum:∀ q∈ coefficients qs ms,q.num≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    split_ifs
    · exact hqn _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.num_zero] using Nat.zero_le M
  have hden:∀ q∈ coefficients qs ms,q.den≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    split_ifs
    · exact hqd _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.den_zero] using hM1
  have hbody:∀ i, ∀ hi:i < (coefficients qs ms).length,
      Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "sum.i"=i) (entry source mask)
        (fun _ τ => Context source mask qs ms τ∧ FractionOutput ((coefficients qs ms)[i]:ℚ) τ) 32:=by
    intro i hi
    have hq:i < qs.length:=by simpa only [length_coefficients] using hi
    have hm:i < ms.length:=by omega
    exact entry_spec B M source mask qs ms hlen i hq hB (by omega)
      (hqn _ (List.getElem_mem hq)) (hqd _ (List.getElem_mem hq))
      (hmn _ (List.getElem_mem hm)) (hmd _ (List.getElem_mem hm))
  have hf:=RamUnsignedSum.command_spec B M 32 (Context source mask qs ms)
    "sum.i" "sum.count" (coefficients qs ms) (entry source mask) hB
    (by rw [length_coefficients]; omega) hnum hden hprefixNum hprefixDen
    (fun _ h => by simpa only [length_coefficients] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source∉ ([]:List String); simp),
        rr.frame_arr mask (by change mask∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source∉ ([]:List String); simp),
        rr.frame_arr mask (by change mask∉ ([]:List String); simp)] using h)
  unfold command
  rw [length_coefficients] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamMaskedSum

end

section

namespace Lax455465Proofs.MaskedMassData

open LpInputSize
open scoped BigOperators NNRat

theorem coefficients_ofFn {n:ℕ} (weights:Fin n→ ℚ≥0) (mask:Fin n→ Bool):
    RamMaskedSum.coefficients (List.ofFn weights) (flags mask) =
      List.ofFn (fun v => if mask v then weights v else 0):=by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,List.length_ofFn]
  · intro i hi hj
    have hn:i < n:=by simpa only [RamMaskedSum.length_coefficients,List.length_ofFn] using hi
    rw [RamMaskedSum.coefficient_at (List.ofFn weights) (flags mask) (by simp [flags]) i (by simpa using hn)]
    simp only [flags,List.getElem_ofFn]
    cases h:mask ⟨i,hn⟩ <;> simp [h]

theorem coe_sum {n:ℕ} (weights:Fin n→ ℚ≥0) (mask:Fin n→ Bool):
    (((RamMaskedSum.coefficients (List.ofFn weights) (flags mask)).sum:ℚ≥0):ℚ) =
      ∑ v,if mask v then (weights v:ℚ) else 0:=by
  rw [coefficients_ofFn,List.sum_ofFn,NNRat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  cases mask v <;> rfl

theorem coefficient_height (qs ms:List ℚ≥0) (w:ℕ)
    (h:∀ q∈ qs,Height (2^w) (q:ℚ)):
    ∀ q∈ RamMaskedSum.coefficients qs ms,Height (2^w) (q:ℚ):=by
  intro q hq
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
  split_ifs
  · exact h _ (List.getElem_mem i.isLt)
  · exact height_zero (by have:=Nat.two_pow_pos w; omega)

theorem prefix_height (qs ms:List ℚ≥0) (w:ℕ)
    (h:∀ q∈ qs,Height (2^w) (q:ℚ)) (i:ℕ):
    Height (2^(w*(qs.length+1)+qs.length+1))
      ((((RamMaskedSum.coefficients qs ms).take i).sum:ℚ≥0):ℚ):=by
  have hh:=coefficient_height qs ms w h
  have hn:∀ q∈ RamMaskedSum.coefficients qs ms,q.num≤ 2^w:=by
    intro q hq
    simpa only [NNRat.natAbs_num_coe] using (hh q hq).1
  have hd:∀ q∈ RamMaskedSum.coefficients qs ms,q.den≤ 2^w:=by
    intro q hq
    simpa only [NNRat.den_coe] using (hh q hq).2
  simpa only [RamMaskedSum.length_coefficients] using RationalSumHeight.prefix_dyadic_height _ _ hn hd i

end Lax455465Proofs.MaskedMassData

end

section

namespace Lax455465Proofs.RamArcMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def Context {n:ℕ} (source:String) (mask:Fin n→ Bool) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags mask)) source σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {source:String} {mask:Fin n→ Bool} (h:Context source mask σ)
    (ha:source∉ cmd.warrs) (hx:∀ x∈ ["metric.n","metric.n2"],x∉ cmd.wvars):
    Context source mask τ:=by
  simpa only [Context,Prefix,hr.frame_arr source ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp))] using h

theorem coefficient_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (source:String)
    (mask:Fin n→ Bool) (u v:Fin n) (h2:2 < B) (hn:n < B) (hn2:n*n < B)
    (hindex:2*n+2 < B):
    Spec B (fun σ => Context source mask σ∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val)
      (coefficient mode source)
      (fun _ τ => Context source mask τ∧ FractionOutput ((matrix mode mask u v:ℚ≥0):ℚ) τ) 60:=by
  let qs:=MaskedMassData.flags mask
  have hlen:qs.length=n:=List.length_ofFn
  have hvalue (t:Fin n):qs[t.val]=RamBooleanArithmetic.bit (mask t):=by
    simp only [qs,MaskedMassData.flags,List.getElem_ofFn,RamBooleanArithmetic.bit]
  have hnum (t:Fin n):qs[t.val].num < B:=by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hden (t:Fin n):qs[t.val].den < B:=by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨σ₁,r₁,p₁⟩:=RamDualDistancesInit.indices_spec B u v hn hn2 σ ⟨hctx.1,hentry⟩
  have hctx₁:=frame r₁ hctx (by simp [RamDualDistancesInit.indices,Com.warrs]) (by decide)
  obtain ⟨σ₂,r₂,p₂⟩:=RamUnsignedBuffer.read_spec B source "metric.u" qs u.val
    (by simpa only [hlen] using u.isLt) h2 (by omega) (hnum u) (hden u) (by decide) σ₁ ⟨hctx₁.2.2,p₁.1⟩
  obtain ⟨σ₃,r₃,p₃⟩:=RamUnsignedArithmetic.copy_spec B qs[u.val] "left" (by omega)
    (hnum u) (hden u) (by decide) σ₂ p₂.1
  have hctx₃:=frame r₃ (frame r₂ hctx₁ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hv₃:σ₃.vars "metric.v"=v.val:=
    (r₃.frame_var _ (by decide)).trans ((r₂.frame_var _ (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)).trans p₁.2)
  obtain ⟨σ₄,r₄,p₄⟩:=RamUnsignedBuffer.read_spec B source "metric.v" qs v.val
    (by simpa only [hlen] using v.isLt) h2 (by omega) (hnum v) (hden v) (by decide) σ₃ ⟨hctx₃.2.2,hv₃⟩
  obtain ⟨σ₅,r₅,p₅⟩:=RamUnsignedArithmetic.copy_spec B qs[v.val] "right" (by omega)
    (hnum v) (hden v) (by decide) σ₄ p₄.1
  have hctx₅:=frame r₅ (frame r₄ hctx₃ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hleft:σ₅.vars "left.s"=0∧ σ₅.vars "left.n"=(RamBooleanArithmetic.bit (mask u)).num∧ σ₅.vars "left.d"=1:=by
    rw [r₅.frame_var "left.s" (by decide),r₅.frame_var "left.n" (by decide),r₅.frame_var "left.d" (by decide),
      r₄.frame_var "left.s" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.n" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.d" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)]
    have hp:=p₃
    rw [hvalue u] at hp
    cases hu:mask u <;> simpa [RamBooleanArithmetic.bit,hu] using hp
  have hright:σ₅.vars "right.s"=0∧ σ₅.vars "right.n"=(RamBooleanArithmetic.bit (mask v)).num∧ σ₅.vars "right.d"=1:=by
    have hp:=p₅
    rw [hvalue v] at hp
    cases hv:mask v <;> simpa [RamBooleanArithmetic.bit,hv] using hp
  obtain ⟨τ,r₆,p₆⟩:=RamBooleanArithmetic.command_spec B mode (mask u) (mask v) (by omega) σ₅
    ⟨hleft.1,hleft.2.1,hleft.2.2,hright.1,hright.2.1,hright.2.2⟩
  refine ⟨τ,r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆)))),
    frame r₆ hctx₅ (by cases mode with | none => simp [RamBooleanArithmetic.command,Com.warrs] | some b => cases b <;> simp [RamBooleanArithmetic.command,Com.warrs])
      (by cases mode with | none => decide | some b => cases b <;> decide),p₆⟩

theorem command_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (source target:String)
    (mask:Fin n→ Bool) (hneq:source ≠ target) (h2:2 < B) (hn:n < B)
    (hn2:n*n < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B):
    Spec B (fun σ => Context source mask σ∧ 2*(n*n) < (σ.arrs target).length)
      (command mode source target)
      (fun _ τ => Context source mask τ∧ Prefix (RamUnsignedBuffer.encode (values (matrix mode mask))) target τ)
      (82*(n*n)+8):=by
  let qs:=values (matrix mode mask)
  have hlen:qs.length=n*n:=length_values _
  have hwords:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    simp only [qs,values,matrix,List.getElem_ofFn]
    cases RamBooleanArithmetic.flag mode (mask _) (mask _) <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => Context source mask σ∧ σ.vars "metric.entry"=i)
        (coefficient mode source) (fun _ τ => Context source mask τ∧ FractionOutput (qs[i]:ℚ) τ) 60:=by
    intro i hi
    have he:i < n*n:=by rwa [hlen] at hi
    let uv:=(edgeIndex n).symm (⟨i,he⟩:Fin (n*n))
    have hidx:edgeIndex n uv=(⟨i,he⟩:Fin (n*n)):=(edgeIndex n).apply_symm_apply _
    simpa only [hidx,qs,values,List.getElem_ofFn,uv,Fin.eta] using
      coefficient_spec B mode source mask uv.1 uv.2 h2 hn hn2 hvertex
  have hfresh (x:String) (h:x∈ ["metric.entry","mask.position"]):
      x∉ (coefficient mode source).wvars:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
  have hloop:=RamUnsignedVector.command_spec B 60 (Context source mask)
    "metric.entry" "metric.n2" target "mask.position" qs [] (coefficient mode source) (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun _ h => by simpa only [hlen] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (hfresh _ (by simp)) (hfresh _ (by simp))
    (by cases mode with
      | none => simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs]
      | some b => cases b <;> simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs])
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => frame rr h (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq])
      (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "mask.position" 0
  have rzero:Run B (.assign "mask.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:=frame rzero hctx (by simp [Com.warrs]) (by decide)
  obtain ⟨τ,rr,pr⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamArcMask

end

section

namespace Lax455465Proofs.BallMassData

open scoped BigOperators NNRat

theorem mask_eq {n:ℕ} (distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    mask distance radius=MaskedMassData.flags (fun v => decide ((distance v:ℚ) < (radius:ℚ))):=by
  simp only [mask,List.map_ofFn,MaskedMassData.flags]
  congr 1
  funext v
  simp [RamBallMask.flag]

theorem coe_mass {n:ℕ} (weights distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    (mass weights distance radius:ℚ) =
      RegionSelection.ballMass (fun v => (weights v:ℚ)) (fun v => (distance v:ℚ)) radius:=by
  unfold mass
  rw [mask_eq,MaskedMassData.coe_sum]
  simp only [RegionSelection.ballMass,RegionCharging.ball,Finset.sum_filter,decide_eq_true_eq]

end Lax455465Proofs.BallMassData

end

section

namespace Lax455465Proofs.BoundaryData

open MetricMatrix
open scoped BigOperators NNRat

theorem masked_matrix {n:ℕ} (capacity flags:Matrix n):
    RamMaskedSum.coefficients (values capacity) (values flags) =
      values (fun u v => if (flags u v).num=1 then capacity u v else 0):=by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,length_values]
  · intro i hi hj
    have he:i < n*n:=by simpa only [RamMaskedSum.length_coefficients,length_values] using hi
    rw [RamMaskedSum.coefficient_at (values capacity) (values flags) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

end Lax455465Proofs.BoundaryData

end

section

namespace Lax455465Proofs.RamTruncatedSubtract

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (value a b:ℚ) τ) (36*(a.den*b.den).size+142):=by
  have h1:1 < B:=by nlinarith
  have ha:=RamUnsignedArithmetic.value a
  have hb:=RamUnsignedArithmetic.value b
  rintro σ hinputs
  obtain ⟨ν,hcompare,hpost⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den
    hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos σ hinputs
  have hinputsν:fractionInputs 0 a.num a.den 0 b.num b.den ν:=by
    simpa only [fractionInputs,hcompare.frame_var "left.s" (by decide),hcompare.frame_var "left.n" (by decide),
      hcompare.frame_var "left.d" (by decide),hcompare.frame_var "right.s" (by decide),
      hcompare.frame_var "right.n" (by decide),hcompare.frame_var "right.d" (by decide)] using hinputs
  have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some (decide (ν.vars "cmp.le"=1)):=by
    rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1)]
    congr 1
  by_cases hab:(a:ℚ)≤ (b:ℚ)
  · have hflag:ν.vars "cmp.le"=1:=hpost.2.mpr (by rwa [ha,hb])
    obtain ⟨τ,hr,ht⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    refine ⟨τ,(hcompare.seq (Run.ite_true (d:=difference) (by simpa only [hflag,decide_true] using hc) hr)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simpa only [value,NNRat.coe_mk,max_eq_right (sub_nonpos.mpr hab)] using ht
  · have hflag:¬ν.vars "cmp.le"=1:=fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    let μ:=ν.setVar "right.s" 1
    have hr:Run B (.assign "right.s" (.lit 1)) ν μ 2:=Run.assign (evalB_lit h1)
    have hμ:fractionInputs 0 a.num a.den 1 b.num b.den μ:=by
      simpa [μ,fractionInputs,vars_setVar] using
        And.intro hinputsν.1 (And.intro hinputsν.2.1 (And.intro hinputsν.2.2.1 (And.intro (rfl:(1:ℕ)=1) hinputsν.2.2.2.2)))
    obtain ⟨τ,haRun,haPost⟩:=addFraction_spec B M 0 a.num a.den 1 b.num b.den hB
      (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos μ hμ
    have hdifference:Run B difference ν τ (36*(a.den*b.den).size+98):=by
      have hh:=hr.seq haRun
      unfold difference
      convert hh using 1 <;> omega
    refine ⟨τ,(hcompare.seq (Run.ite_false (c:=RamFractionPrimitives.zero) (by simpa only [hflag,decide_false] using hc) hdifference)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    have hnegative:fractionValue 1 b.num b.den=-(b:ℚ):=by
      simpa [fractionValue,neg_div] using congrArg Neg.neg hb
    change FractionOutput (max ((a:ℚ)-(b:ℚ)) 0) τ
    rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hab)),sub_eq_add_neg]
    simpa only [ha,hnegative] using haPost

end Lax455465Proofs.RamTruncatedSubtract

end

section

namespace Lax455465Proofs.UnsignedHeight

open LpInputSize
open scoped NNRat

abbrev Bounded (M:ℕ) (q:ℚ≥0):=Height M (q:ℚ)

theorem min_bound {M:ℕ} {a b:ℚ≥0} (ha:Bounded M a) (hb:Bounded M b):
    Bounded M (min a b):=by
  by_cases hab:a≤ b
  · simpa only [min_eq_left hab] using ha
  · simpa only [min_eq_right (le_of_not_ge hab)] using hb

theorem clipped_bound {M:ℕ} {a b:ℚ≥0} (hM:1≤ M) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (M^3) (RamTruncatedSubtract.value a b):=by
  by_cases hab:(b:ℚ)≤ (a:ℚ)
  · have hden:((a:ℚ)-(b:ℚ)).den ∣ a.den*b.den:=by
      simpa only [NNRat.den_coe] using Rat.sub_den_dvd (a:ℚ) (b:ℚ)
    have hval:(a:ℚ)-(b:ℚ)≤ (M:ℚ):=by
      have hv:=MetricHeight.value_bound (a:ℚ) a.coe_nonneg M ha.1
      linarith [b.coe_nonneg]
    have hh:=MetricHeight.height_of_denominator _ (sub_nonneg.mpr hab) M (a.den*b.den) hM
      (Nat.mul_pos a.den_pos b.den_pos) hden hval
    have hp:a.den*b.den≤ M*M:=Nat.mul_le_mul ha.2 hb.2
    have hm:M*(a.den*b.den)≤ M^3:=by nlinarith [Nat.mul_le_mul_left M hp]
    have hheight:=height_mono hh hm
    simpa only [Bounded,RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_left (sub_nonneg.mpr hab)] using hheight
  · have hm:1≤ M^3:=by simpa using (Nat.pow_le_pow_left hM 3)
    simpa only [Bounded,RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_right (sub_nonpos.mpr (le_of_not_ge hab))] using height_zero hm

theorem add_bound {M:ℕ} {a b:ℚ≥0} (hM:1≤ M) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (2*M^3) (a+b):=by
  have hden:((a:ℚ)+(b:ℚ)).den ∣ a.den*b.den:=by
    simpa only [NNRat.den_coe] using Rat.add_den_dvd (a:ℚ) (b:ℚ)
  have hval:(a:ℚ)+(b:ℚ)≤ (2*M:ℕ):=by
    have hva:=MetricHeight.value_bound (a:ℚ) a.coe_nonneg M ha.1
    have hvb:=MetricHeight.value_bound (b:ℚ) b.coe_nonneg M hb.1
    push_cast
    linarith
  have hh:=MetricHeight.height_of_denominator _ (add_nonneg a.coe_nonneg b.coe_nonneg) (2*M)
    (a.den*b.den) (by omega) (Nat.mul_pos a.den_pos b.den_pos) hden hval
  have hp:a.den*b.den≤ M*M:=Nat.mul_le_mul ha.2 hb.2
  exact height_mono hh (by nlinarith [Nat.mul_le_mul_left (2*M) hp])

end Lax455465Proofs.UnsignedHeight

end

section

namespace Lax455465Proofs.RoundingConstants
open scoped NNRat

def seed (cost:ℚ≥0) (p:ℕ):ℚ≥0:=cost/(p:ℚ≥0)
def delta (total:ℚ≥0):ℚ≥0:=(4*total^2)⁻¹
def beta (total:ℚ≥0) (p:ℕ):ℚ≥0:=(RegionBudget.steps p:ℚ≥0)/(delta total)
def gridStep (total:ℚ≥0) (p:ℕ):ℚ≥0:=delta total/(RegionBudget.steps p:ℚ≥0)

theorem coe_delta (total:ℚ≥0):(delta total:ℚ)=1/(4*(total:ℚ)^2):=by
  simp [delta]

theorem coe_beta (total:ℚ≥0) (p:ℕ):
    (beta total p:ℚ)=RegionSearch.slope (RegionBudget.steps p) (delta total):=by
  simp [beta,RegionSearch.slope]

theorem inverse_height {M:ℕ} {q:ℚ≥0} (hM:1≤ M) (hq:LpInputSize.Height M (q:ℚ)):
    LpInputSize.Height M ((q⁻¹:ℚ≥0):ℚ):=by
  simp only [LpInputSize.Height,NNRat.coe_inv,Rat.num_inv,Rat.den_inv]
  have habs:(q:ℚ).num.sign.natAbs≤1:=by
    rw [Int.natAbs_sign]; split_ifs <;> omega
  constructor
  · simpa only [Int.natAbs_mul,Int.natAbs_natCast,Nat.one_mul] using
      (Nat.mul_le_mul habs hq.2)
  · split_ifs
    · exact hM
    · exact hq.1

end Lax455465Proofs.RoundingConstants

end

section

namespace Lax455465Proofs.RoundingConstantHeight
open LpInputSize RoundingConstants
open scoped NNRat

structure Bounds (cost total:ℚ≥0) (p M:ℕ):Prop where
  costBound:Height M (cost:ℚ)
  totalBound:Height M (total:ℚ)
  supportBound:Height M ((p:ℚ≥0):ℚ)
  stepsBound:Height M ((RegionBudget.steps p:ℚ≥0):ℚ)
  fourBound:Height M ((4:ℚ≥0):ℚ)
  seedBound:Height M (seed cost p:ℚ)
  squareBound:Height M ((total*total:ℚ≥0):ℚ)
  denominatorBound:Height M ((4*(total*total):ℚ≥0):ℚ)
  deltaBound:Height M (delta total:ℚ)
  betaBound:Height M (beta total p:ℚ)
  stepBound:Height M (gridStep total p:ℚ)

theorem bounds (cost total:ℚ≥0) (p M:ℕ) (hM:4≤ M)
    (hc:Height M (cost:ℚ)) (ht:Height M (total:ℚ))
    (hp:p≤ M) (hk:RegionBudget.steps p≤ M):Bounds cost total p (4*M^3):=by
  have hM1:1≤ M:=by omega
  have hN:M≤4*M^3:=by nlinarith [Nat.le_mul_of_pos_right M (by positivity:0< M*M)]
  have hNN:M*M≤4*M^3:=by nlinarith [Nat.le_mul_of_pos_right (M*M) (by omega:0< M)]
  have hfourSq:4*(M*M)≤4*M^3:=by nlinarith [Nat.le_mul_of_pos_right (M*M) (by omega:0< M)]
  have natHeight (k:ℕ) (h:k≤ M):Height M ((k:ℚ≥0):ℚ):=by
    simp only [Height,NNRat.coe_natCast,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
    exact ⟨h,hM1⟩
  have hpn:=natHeight p hp
  have hkn:=natHeight (RegionBudget.steps p) hk
  have hf:Height 4 ((4:ℚ≥0):ℚ):=by norm_num [Height]
  have hsq:Height (M*M) ((total*total:ℚ≥0):ℚ):=by simpa only [NNRat.coe_mul] using height_mul ht ht
  have hden:Height (4*(M*M)) ((4*(total*total):ℚ≥0):ℚ):=by simpa only [NNRat.coe_mul] using height_mul hf hsq
  have hdelta:Height (4*(M*M)) (delta total:ℚ):=by
    have hh:=inverse_height (by nlinarith:1≤4*(M*M)) hden
    simpa only [delta,pow_two] using hh
  have hs:Height (M*M) (seed cost p:ℚ):=by
    simpa only [seed,div_eq_mul_inv,NNRat.coe_mul] using height_mul hc (inverse_height hM1 hpn)
  have hb:Height (M*(4*(M*M))) (beta total p:ℚ):=by
    simpa only [beta,delta,pow_two,div_eq_mul_inv,inv_inv,NNRat.coe_mul] using height_mul hkn hden
  have hg:Height ((4*(M*M))*M) (gridStep total p:ℚ):=by
    simpa only [gridStep,div_eq_mul_inv,NNRat.coe_mul] using height_mul hdelta (inverse_height hM1 hkn)
  exact ⟨height_mono hc hN,height_mono ht hN,height_mono hpn hN,height_mono hkn hN,
    height_mono hf (by nlinarith),height_mono hs hNN,height_mono hsq hNN,height_mono hden hfourSq,
    height_mono hdelta hfourSq,height_mono hb (by ring_nf; rfl),height_mono hg (by ring_nf; rfl)⟩

end Lax455465Proofs.RoundingConstantHeight

end

section

namespace Lax455465Proofs.RamScalarInverse
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B:ℕ) (name:String) (q:ℚ≥0) (h1:1< B)
    (hn:q.num< B) (hd:q.den< B)
    (hfresh:name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n"):
    Spec B (Stored name q) (command name)
      (fun _ τ => FractionOutput ((q⁻¹:ℚ≥0):ℚ) τ) (36*q.num.size+52):=by
  rintro σ hσ
  obtain ⟨ν,rl,pl⟩:=load_spec B name q h1 hn hd hfresh σ hσ
  obtain ⟨μ,rc,pc⟩:=RamUnsignedArithmetic.copy_spec B q "left" h1 hn hd (by decide) ν pl
  obtain ⟨τ,ri,pi⟩:=invertFraction_spec B 0 q.num q.den h1 (by omega) hn hd μ pc
  exact ⟨τ,(rl.seq (rc.seq ri)).mono (by omega),by simpa only [RamUnsignedArithmetic.value,NNRat.coe_inv] using pi⟩

end Lax455465Proofs.RamScalarInverse

end

section

namespace Lax455465Proofs.RamScalarBinary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M K:ℕ) (a b:ℚ≥0) (leftName rightName:String)
    (operation:Com) (q:ℚ) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh:rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain:rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (hop:Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) operation
      (fun _ τ => FractionOutput q τ) K):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (command leftName rightName operation) (fun _ τ => FractionOutput q τ) (K+24):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩:=load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rleft,pleft⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ:Stored rightName b μ:=by
    have rr:=ra.seq rleft
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,
      rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩:=load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rright,pright⟩:=RamUnsignedArithmetic.copy_spec B b "right" h1
    (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have pleftη:η.vars "left.s"=0∧ η.vars "left.n"=a.num∧ η.vars "left.d"=a.den:=by
    have rr:=rb.seq rright
    simpa only [rr.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),rr.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      rr.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pleft
  obtain ⟨τ,rop,pop⟩:=hop η ⟨pleftη.1,pleftη.2.1,pleftη.2.2,by simpa only [String.reduceAppend] using pright⟩
  refine ⟨τ,(ra.seq (rleft.seq (rb.seq (rright.seq rop)))).mono (by omega),pop⟩

end Lax455465Proofs.RamScalarBinary

end

section

namespace Lax455465Proofs.VolumeData

open MetricMatrix LpInputSize
open scoped BigOperators NNRat

theorem coefficient_height {n:ℕ} (outward:Bool) (capacity length:Matrix n)
    (distance:Fin n→ ℚ≥0) (radius:ℚ≥0) (w:ℕ)
    (hc:∀ u v,Height (2^w) (capacity u v:ℚ))
    (hl:∀ u v,Height (2^w) (length u v:ℚ))
    (hd:∀ v,Height (2^w) (distance v:ℚ)) (hr:Height (2^w) (radius:ℚ)):
    ∀ q∈ coefficients outward capacity length distance radius,Height (2^(4*w)) (q:ℚ):=by
  intro q hq
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
  let uv:=(DirectedFlowLP.edgeIndex n).symm i
  have hb:Height (2^w) (base outward distance uv.1 uv.2:ℚ):=by
    cases outward <;> exact hd _
  have hm:1≤ 2^w:=by have:=Nat.two_pow_pos w; omega
  have hpow:2^w≤ (2^w)^3:=by simpa using Nat.pow_le_pow_right hm (show 1≤ 3 by decide)
  have hp:=UnsignedHeight.min_bound (height_mono (hl uv.1 uv.2) hpow) (UnsignedHeight.clipped_bound hm hr hb)
  have hh:=height_mul (hc uv.1 uv.2) hp
  simpa only [uv,RamEdgePortion.value,NNRat.coe_mul,←Nat.pow_mul,←Nat.pow_add,
    show w+w*3=4*w by omega] using hh

theorem prefix_height {n:ℕ} (outward:Bool) (capacity length:Matrix n)
    (distance:Fin n→ ℚ≥0) (radius:ℚ≥0) (w:ℕ)
    (hc:∀ u v,Height (2^w) (capacity u v:ℚ))
    (hl:∀ u v,Height (2^w) (length u v:ℚ))
    (hd:∀ v,Height (2^w) (distance v:ℚ)) (hr:Height (2^w) (radius:ℚ)) (i:ℕ):
    Height (2^(4*w*(n*n+1)+n*n+1))
      ((((coefficients outward capacity length distance radius).take i).sum:ℚ≥0):ℚ):=by
  have hh:=coefficient_height outward capacity length distance radius w hc hl hd hr
  have hn:∀ q∈ coefficients outward capacity length distance radius,q.num≤ 2^(4*w):=by
    intro q hq; simpa only [NNRat.natAbs_num_coe] using (hh q hq).1
  have hd:∀ q∈ coefficients outward capacity length distance radius,q.den≤ 2^(4*w):=by
    intro q hq; simpa only [NNRat.den_coe] using (hh q hq).2
  simpa only [coefficients,length_values] using RationalSumHeight.prefix_dyadic_height _ _ hn hd i

end Lax455465Proofs.VolumeData

end

section

namespace Lax455465Proofs.VolumeHeight

open LpInputSize MetricMatrix
open scoped NNRat

def sumExponent (n w:ℕ):ℕ:=4*w*(n*n+1)+n*n+1
def exponent (n w:ℕ):ℕ:=3*sumExponent n w+1

theorem bounds {n:ℕ} (outward:Bool) (capacity length:Matrix n)
    (distance:Fin n→ ℚ≥0) (seed radius:ℚ≥0) (w:ℕ)
    (hc:∀ u v,Height (2^w) (capacity u v:ℚ))
    (hl:∀ u v,Height (2^w) (length u v:ℚ))
    (hd:∀ v,Height (2^w) (distance v:ℚ))
    (hs:Height (2^w) (seed:ℚ)) (hr:Height (2^w) (radius:ℚ)):
    Bounds outward capacity length distance seed radius (exponent n w):=by
  have h4:4*w≤ sumExponent n w:=by dsimp [sumExponent]; nlinarith
  have hE:sumExponent n w≤ exponent n w:=by dsimp [exponent]; omega
  have hwE:w≤ sumExponent n w:=by omega
  have hwH:w≤ exponent n w:=hwE.trans hE
  have h3H:3*w≤ exponent n w:=by omega
  have h4H:4*w≤ exponent n w:=h4.trans hE
  have hpow (a b:ℕ) (h:a≤ b):2^a≤ 2^b:=Nat.pow_le_pow_right (by decide) h
  have hM:1≤ 2^w:=by have:=Nat.two_pow_pos w; omega
  have hdiff (v:Fin n):Height (2^(3*w)) (RamTruncatedSubtract.value radius (distance v):ℚ):=by
    simpa only [←Nat.pow_mul,show w*3=3*w by omega] using UnsignedHeight.clipped_bound hM hr (hd v)
  have hportion (u v:Fin n):Height (2^(3*w)) (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius:ℚ):=by
    have hb:Height (2^w) (VolumeData.base outward distance u v:ℚ):=by cases outward <;> exact hd _
    have ht:=UnsignedHeight.clipped_bound hM hr hb
    have hh:=UnsignedHeight.min_bound (height_mono (hl u v) (by simpa using Nat.pow_le_pow_right hM (show 1≤3 by decide))) ht
    simpa only [RamEdgePortion.value,←Nat.pow_mul,show w*3=3*w by omega] using hh
  have hsum (i:ℕ):Height (2^(sumExponent n w)) ((((VolumeData.coefficients outward capacity length distance radius).take i).sum:ℚ≥0):ℚ):=
    VolumeData.prefix_height outward capacity length distance radius w hc hl hd hr i
  have hfull:Height (2^(sumExponent n w)) (((VolumeData.coefficients outward capacity length distance radius).sum:ℚ≥0):ℚ):=by
    simpa only [List.take_length] using hsum (VolumeData.coefficients outward capacity length distance radius).length
  refine ⟨fun u v => height_mono (hc u v) (hpow _ _ hwH),
    fun u v => height_mono (hl u v) (hpow _ _ hwH),fun v => height_mono (hd v) (hpow _ _ hwH),
    height_mono hs (hpow _ _ hwH),height_mono hr (hpow _ _ hwH),
    fun v => height_mono (hdiff v) (hpow _ _ h3H),
    fun u v => height_mono (hportion u v) (hpow _ _ h3H),
    fun q hq => height_mono (VolumeData.coefficient_height outward capacity length distance radius w hc hl hd hr q hq) (hpow _ _ h4H),
    fun i => height_mono (hsum i) (hpow _ _ hE),?_⟩
  have hh:=UnsignedHeight.add_bound (by have:=Nat.two_pow_pos (sumExponent n w); omega)
    (height_mono hs (hpow _ _ hwE)) hfull
  have heq:2*(2^(sumExponent n w))^3=2^(exponent n w):=by
    rw [←Nat.pow_mul,show exponent n w=1+sumExponent n w*3 by dsimp [exponent]; omega,Nat.pow_add]
  simpa only [heq,VolumeData.value] using hh

end Lax455465Proofs.VolumeHeight

end

section

namespace Lax455465Proofs.RegionQueryHeight

open RegionQueryData LpInputSize
open scoped NNRat

def exponent (n w:ℕ):ℕ:=2*VolumeHeight.exponent n w+w+1

theorem bounds {n:ℕ} (q:Query n) (w:ℕ)
    (hw:∀ v,Height (2^w) (q.weights v:ℚ))
    (hc:∀ u v,Height (2^w) (q.capacity u v:ℚ))
    (hl:∀ u v,Height (2^w) (q.length u v:ℚ))
    (hd:∀ b v,Height (2^w) (distance q b v:ℚ))
    (hs:Height (2^w) (q.seed:ℚ)) (hb:Height (2^w) (q.beta:ℚ))
    (hr:Height (2^w) (q.radius:ℚ)):Bounds q (exponent n w):=by
  let V:=VolumeHeight.exponent n w
  let J:=exponent n w
  have hwV:w≤ V:=by dsimp [V,VolumeHeight.exponent,VolumeHeight.sumExponent]; nlinarith
  have hVJ:V≤ J:=by dsimp [J,exponent,V]; omega
  have hwJ:w≤ J:=hwV.trans hVJ
  have hpow (a b:ℕ) (h:a≤ b):2^a≤ 2^b:=Nat.pow_le_pow_right (by decide) h
  have widen {q:ℚ≥0} (h:Height (2^V) (q:ℚ)):Height (2^J) (q:ℚ):=height_mono h (hpow _ _ hVJ)
  have vols (b:Bool):=VolumeHeight.bounds b q.capacity q.length (distance q b) q.seed q.radius w hc hl (hd b) hs hr
  have hvb (b:Bool):VolumeHeight.Bounds b q.capacity q.length (distance q b) q.seed q.radius J:=by
    have hv:=vols b
    exact ⟨fun u v => widen (hv.capacityBound u v),fun u v => widen (hv.lengthBound u v),
      fun v => widen (hv.distanceBound v),widen hv.seedBound,widen hv.radiusBound,
      fun v => widen (hv.differenceBound v),fun u v => widen (hv.portionBound u v),
      fun a ha => widen (hv.coefficientBound a ha),fun i => widen (hv.prefixBound i),widen hv.valueBound⟩
  have hnn:n≤ n*n:=by
    by_cases hn:n=0
    · simp [hn]
    · have hn1:1≤ n:=by omega
      nlinarith
  have hmJ:w*(n+1)+n+1≤ J:=by
    dsimp [J,exponent,V,VolumeHeight.exponent,VolumeHeight.sumExponent]
    nlinarith [Nat.mul_le_mul_left w hnn]
  have hcJ:w*(n*n+1)+n*n+1≤ J:=by
    dsimp [J,exponent,V,VolumeHeight.exponent,VolumeHeight.sumExponent]
    nlinarith
  have hm (b:Bool) (i:ℕ):Height (2^J)
      ((((RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).take i).sum:ℚ≥0):ℚ):=by
    have hh:=MaskedMassData.prefix_height (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius) w
      (by intro a ha; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha; exact hw v) i
    exact height_mono hh (by simpa only [List.length_ofFn] using hpow _ _ hmJ)
  have hbc (b:Bool) (i:ℕ):Height (2^J)
      ((((RamMaskedSum.coefficients (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs b (distance q b) q.radius))).take i).sum:ℚ≥0):ℚ):=by
    have hh:=MaskedMassData.prefix_height (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs b (distance q b) q.radius)) w
      (by intro a ha; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha; exact hc _ _) i
    exact height_mono hh (by simpa only [MetricMatrix.length_values] using hpow _ _ hcJ)
  refine ⟨fun v => height_mono (hw v) (hpow _ _ hwJ),fun u v => height_mono (hc u v) (hpow _ _ hwJ),
    fun u v => height_mono (hl u v) (hpow _ _ hwJ),fun b v => height_mono (hd b v) (hpow _ _ hwJ),
    height_mono hs (hpow _ _ hwJ),height_mono hb (hpow _ _ hwJ),height_mono hr (hpow _ _ hwJ),hvb,hm,hbc,?_⟩
  have hvol:Height (2^V) (volume q:ℚ):=(vols (direction q q.radius)).valueBound
  have hh:=height_mul hb hvol
  have he:2^w*2^V=2^(w+V):=(Nat.pow_add 2 w V).symm
  have hsum:w+V≤ J:=by dsimp [J,exponent,V]; omega
  exact height_mono (by simpa only [bound,NNRat.coe_mul,he] using hh) (hpow _ _ hsum)

end Lax455465Proofs.RegionQueryHeight

end

section

namespace Lax455465Proofs.RamArrayScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

theorem command_spec (B:ℕ) (array index name:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s")
    (hname:name ++ ".n" ≠ "rat.d"):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode qs) array σ∧ σ.vars index=i)
      (command array index name) (fun _ τ => Stored name qs[i] τ) 18:=by
  intro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamUnsignedBuffer.read_spec B array index qs i hi h2 hindex hn hd hfresh σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B name qs[i] hn hd hname ν pr.1
  exact ⟨τ,rr.seq rs,ps⟩

end Lax455465Proofs.RamArrayScalar

end

section

namespace Lax455465Proofs.RamRootDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def vector {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n):List ℚ≥0:=
  List.ofFn fun v => if outward then d root v else d v root

@[simp] theorem length_vector {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n):
    (vector outward root d).length=n:=List.length_ofFn

def Context {n:ℕ} (root:Fin n) (d:Matrix n) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "region.root"=root.val∧
    Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {root:Fin n} {d:Matrix n} (h:Context root d σ)
    (ha:"metric.old" ∉ cmd.warrs) (hn:"metric.n" ∉ cmd.wvars)
    (hroot:"region.root" ∉ cmd.wvars):Context root d τ:=by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.n" hn,hr.frame_var "region.root" hroot] using h

theorem entry_spec (B H:ℕ) {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n) (v:Fin n)
    (hH:H < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ u v, (d u v).num≤ H) (hden:∀ u v, (d u v).den≤ H):
    Spec B (fun σ => Context root d σ∧ σ.vars "region.i"=v.val) (entry outward)
      (fun _ τ => Context root d τ∧ FractionOutput ((vector outward root d)[v.val]:ℚ) τ) 20:=by
  let u:=if outward then root else v
  let t:=if outward then v else root
  let address:=(edgeIndex n (u,t)).val
  have ha:address < n*n:=(edgeIndex n (u,t)).isLt
  have hval:(values d)[address]=d u t:=value_at d u t
  have hvector:(vector outward root d)[v.val]=d u t:=by
    simp only [vector,List.getElem_ofFn,u,t]
    cases outward <;> rfl
  rintro σ ⟨hctx,hi⟩
  let ν:=σ.setVar "region.address" address
  have haddr:Run B (.assign "region.address" (if outward then .add (.mul (.var "region.root") (.var "metric.n")) (.var "region.i")
      else .add (.mul (.var "region.i") (.var "metric.n")) (.var "region.root"))) σ ν 6:=by
    have hroot:root.val < B:=root.isLt.trans hn
    have hv:v.val < B:=v.isLt.trans hn
    have hprodR:root.val*n < B:=(by nlinarith [root.isLt]:root.val*n < n*n).trans hn2
    have hprodV:v.val*n < B:=(by nlinarith [v.isLt]:v.val*n < n*n).trans hn2
    cases outward with
    | false =>
      have heq:address=v.val*n+root.val:=by simp [address,u,t,FlowLpIndices.edge_value]
      have hm:=evalB_bin (op:=.mul) (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hv⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ hn⟩) hprodV
      simpa only [Bool.false_eq_true,if_false,if_pos rfl,ν,heq,Expr.size,Bop.apply,Nat.reduceAdd,if_true] using (Run.assign (evalB_bin (op:=.add) hm
        (by rw [evalB_var_iff]; exact ⟨hctx.2.1.symm,hctx.2.1 ▸ hroot⟩) (by change v.val*n+root.val < B; rw [←heq]; exact ha.trans hn2)):Run B _ _ _ 6)
    | true =>
      have heq:address=root.val*n+v.val:=by simp [address,u,t,FlowLpIndices.edge_value]
      have hm:=evalB_bin (op:=.mul) (by rw [evalB_var_iff]; exact ⟨hctx.2.1.symm,hctx.2.1 ▸ hroot⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ hn⟩) hprodR
      simpa only [Bool.false_eq_true,if_false,if_pos rfl,ν,heq,Expr.size,Bop.apply,Nat.reduceAdd,if_true] using (Run.assign (evalB_bin (op:=.add) hm
        (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hv⟩) (by change root.val*n+v.val < B; rw [←heq]; exact ha.trans hn2)):Run B _ _ _ 6)
  have hctxν:=frame haddr hctx (by simp [Com.warrs]) (by simp [Com.wvars]) (by simp [Com.wvars])
  obtain ⟨τ,rr,pr⟩:=RamUnsignedBuffer.read_spec B "metric.old" "region.address" (values d) address
    (by simpa only [length_values] using ha) (by omega) (by omega)
    (by rw [hval]; exact (hnum u t).trans_lt hH) (by rw [hval]; exact (hden u t).trans_lt hH)
    (by decide) ν ⟨hctxν.2.2,by simp [ν]⟩
  refine ⟨τ,haddr.seq rr,frame rr hctxν (by decide) (by decide) (by decide),?_⟩
  simpa only [hval,hvector] using pr.1

theorem command_spec (B H:ℕ) {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n)
    (hH:H < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ u v, (d u v).num≤ H) (hden:∀ u v, (d u v).den≤ H):
    Spec B (fun σ => Context root d σ∧ 2*n < (σ.arrs (array outward)).length) (command outward)
      (fun _ τ => Context root d τ∧ Prefix (RamUnsignedBuffer.encode (vector outward root d)) (array outward) τ)
      (42*n+8):=by
  let qs:=vector outward root d
  have hlen:qs.length=n:=List.length_ofFn
  have hwords:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    have hv:i < n:=by rwa [hlen] at hi
    have heq:qs[i]=if outward then d root ⟨i,hv⟩ else d ⟨i,hv⟩ root:=by
      dsimp only [qs,vector]
      erw [List.getElem_ofFn]
    rw [heq]
    cases outward <;> exact ⟨(hnum _ _).trans_lt hH,(hden _ _).trans_lt hH⟩
  have hloop:=RamUnsignedVector.command_spec B 20 (Context root d)
    "region.i" "metric.n" (array outward) "region.pos" qs [] (entry outward) (by omega)
    (by have hnpositive:=root.isLt; simp only [List.length_nil,hlen]; nlinarith)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun σ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have hv:i < n:=by rwa [hlen] at hi
      exact entry_spec B H outward root d ⟨i,hv⟩ hH hn hn2 hindex hnum hden)
    (by cases outward <;> decide) (by cases outward <;> decide) (by cases outward <;> decide)
    (by cases outward <;> decide)
    (fun rr h => frame rr h (by cases outward <;> decide) (by cases outward <;> decide) (by cases outward <;> decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "region.pos" 0
  have rzero:Run B (.assign "region.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:=frame rzero hctx (by decide) (by decide) (by decide)
  obtain ⟨τ,rr,pr⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamRootDistances

end

section

namespace Lax455465Proofs.RamRegionContext

open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def sourceVariables:List String:= ["metric.n","metric.n2","region.radius.n","region.radius.d",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d"]
def arrays:List String:= ["region.weights","region.capacities","metric.old","region.out","region.in"]

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {q:Query n} (h:Input q σ)
    (hx:∀ x∈ sourceVariables,x∉ cmd.wvars) (ha:∀ a∈ arrays,a∉ cmd.warrs):Input q τ:=by
  refine ⟨(hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.nValue,
    (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.n2Value,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "region.radius.n" (hx _ (by simp [sourceVariables])),hr.frame_var "region.radius.d" (hx _ (by simp [sourceVariables]))] using h.radiusData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.seed.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.seed.d" (hx _ (by simp [sourceVariables]))] using h.seedData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.slope.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.slope.d" (hx _ (by simp [sourceVariables]))] using h.betaData
  · simpa only [Prefix,hr.frame_arr "region.weights" (ha _ (by simp [arrays]))] using h.weightsData
  · simpa only [Prefix,hr.frame_arr "region.capacities" (ha _ (by simp [arrays]))] using h.capacityData
  · simpa only [Prefix,hr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData
  · simpa only [Prefix,hr.frame_arr "region.out" (ha _ (by simp [arrays]))] using h.outData
  · simpa only [Prefix,hr.frame_arr "region.in" (ha _ (by simp [arrays]))] using h.inData

theorem num_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.num≤ M:=by
  simpa only [NNRat.natAbs_num_coe] using h.1

theorem den_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.den≤ M:=by
  simpa only [NNRat.den_coe] using h.2

end Lax455465Proofs.RamRegionContext

end

section

namespace Lax455465Proofs.RamScalarReciprocal
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar RamRegionContext
open scoped NNRat

theorem command_spec (B M:ℕ) (q:ℚ≥0) (source target:String) (hM:1≤ M) (hB:M< B)
    (hq:LpInputSize.Height M (q:ℚ))
    (hsource:source++".n"≠"rat.s" ∧ source++".d"≠"rat.s" ∧ source++".d"≠"rat.n")
    (htarget:target++".n"≠"rat.d"):
    Spec B (Stored source q) (command source target) (fun _ τ => Stored target q⁻¹ τ)
      (36*q.num.size+56):=by
  have hi:=RoundingConstants.inverse_height hM hq
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamScalarInverse.command_spec B source q (by omega)
    ((num_bound hq).trans_lt hB) ((den_bound hq).trans_lt hB) hsource σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B target q⁻¹ ((num_bound hi).trans_lt hB) ((den_bound hi).trans_lt hB) htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarReciprocal

end

section

namespace Lax455465Proofs.RamScalarProduct
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName target:String)
    (hB:2*M^2+3< B) (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hrfresh:rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hrretain:rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (htarget:target++".n"≠"rat.d"):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ) (command leftName rightName target)
      (fun _ τ => Stored target (a*b) τ) (36*(a.den*b.den).size+92):=by
  have ha:LpInputSize.Height M (a:ℚ):= ⟨by simpa only [NNRat.natAbs_num_coe] using han,by simpa only [NNRat.den_coe] using had⟩
  have hb:LpInputSize.Height M (b:ℚ):= ⟨by simpa only [NNRat.natAbs_num_coe] using hbn,by simpa only [NNRat.den_coe] using hbd⟩
  have hp:=LpInputSize.height_mul ha hb
  have hpnum:(a*b).num< B:=(show (a*b).num≤ M*M by simpa only [←NNRat.coe_mul,NNRat.natAbs_num_coe] using hp.1).trans_lt (by nlinarith)
  have hpden:(a*b).den< B:=(show (a*b).den≤ M*M by simpa only [←NNRat.coe_mul,NNRat.den_coe] using hp.2).trans_lt (by nlinarith)
  have hop:=multiplyFraction_spec B M 0 a.num a.den 0 b.num b.den hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamScalarBinary.command_spec B M (36*(a.den*b.den).size+64) a b leftName rightName multiplyFraction ((a*b:ℚ≥0):ℚ)
    hB han had hbn hbd hlfresh hrfresh hrretain (by simpa only [RamUnsignedArithmetic.value,NNRat.coe_mul] using hop) σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B target (a*b) hpnum hpden htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarProduct

end

section

namespace Lax455465Proofs.RamNatScalar
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

theorem command_spec (B v:ℕ) (source target:String) (hv:v< B) (h1:1< B):
    Spec B (fun σ => σ.vars source=v) (command source target)
      (fun _ τ => Stored target (v:ℚ≥0) τ) 4:=by
  (expose_names;
    (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ source) v) => let c0:Env→ Prop:=Stored target (@Nat.cast NNRat (@AddMonoidWithOne.toNatCast NNRat (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat (@NonAssocSemiring.toAddCommMonoidWithOne NNRat (@Semiring.toNonAssocSemiring NNRat (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))) v); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) target; let c3:String:=c2 ".n"; let c4:Env:=Env.setVar σ c3 (Env.vars σ source); let c5:String:=c2 ".d"; let c6:Env:=Env.setVar c4 c5 ((1:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.var source)); let c10:Nat:=c8 (Expr.size (Expr.lit ((1:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B (command source target) σ σ' ((4:Nat))) (c1 σ')) c6 (@And.intro (Run B (command source target) σ c6 ((4:Nat))) (c1 c6) (RunStep.mono B (command source target) σ c6 (c7 c9 c10) ((4:Nat)) (RunStep.seq B (Com.assign c3 (Expr.var source)) (Com.assign c5 (Expr.lit ((1:Nat)))) σ c4 c6 c9 c10 (RunStep.assign B σ c3 (Expr.var source) (Env.vars σ source) (RunStep.eval_var B σ source (?nAX_g6733_0_0_0))) (RunStep.assign B c4 c5 (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4 h1))) (?nAX_g6733_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6733_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6733_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored,NNRat.num_natCast,NNRat.den_natCast]

end Lax455465Proofs.RamNatScalar

end

section

namespace Lax455465Proofs.RamRoundingConstants
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext RoundingConstants
open scoped NNRat

def unitCost (M:ℕ):ℕ:=36*(M^2).size+100

theorem storedFrame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {name:String} {q:ℚ≥0} (h:Stored name q σ)
    (hn:name++".n"∉cmd.wvars) (hd:name++".d"∉cmd.wvars):Stored name q τ:=by
  simpa only [Stored,rr.frame_var (name++".n") hn,rr.frame_var (name++".d") hd] using h

theorem product_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName target:String)
    (hM:1≤ M) (hB:2*M^2+3< B) (ha:LpInputSize.Height M (a:ℚ)) (hb:LpInputSize.Height M (b:ℚ))
    (hl:leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hr:rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hf:rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (ht:target++".n"≠"rat.d"):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (RamScalarProduct.command leftName rightName target) (fun _ τ => Stored target (a*b) τ) (unitCost M):=by
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩:=RamScalarProduct.command_spec B M a b leftName rightName target hB
    (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb) hl hr hf ht σ hσ
  have hs:(a.den*b.den).size≤(M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound ha) (den_bound hb)])
  exact ⟨τ,rr.mono (by dsimp [unitCost]; omega),pr⟩

theorem reciprocal_spec (B M:ℕ) (q:ℚ≥0) (source target:String)
    (hM:1≤ M) (hB:2*M^2+3< B) (hq:LpInputSize.Height M (q:ℚ))
    (hs:source++".n"≠"rat.s" ∧ source++".d"≠"rat.s" ∧ source++".d"≠"rat.n")
    (ht:target++".n"≠"rat.d"):
    Spec B (Stored source q) (RamScalarReciprocal.command source target)
      (fun _ τ => Stored target q⁻¹ τ) (unitCost M):=by
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩:=RamScalarReciprocal.command_spec B M q source target hM (by nlinarith) hq hs ht σ hσ
  have hsize:q.num.size≤(M^2).size:=Nat.size_le_size (by nlinarith [num_bound hq])
  exact ⟨τ,rr.mono (by dsimp [unitCost]; omega),pr⟩

structure Input (cost total:ℚ≥0) (p:ℕ) (σ:Env):Prop where
  costData:Stored "round.cost" cost σ
  totalData:Stored "round.total" total σ
  supportValue:σ.vars "round.support"=p
  stepsValue:σ.vars "round.steps"=RegionBudget.steps p

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) (cost total:ℚ≥0) (p:ℕ)
    (hb:RoundingConstantHeight.Bounds cost total p M) (hM:4≤ M) (hB:2*M^2+3< B):
    Spec B (Input cost total p) command (fun _ τ => Input cost total p τ∧
      Stored "round.seed" (seed cost p) τ∧ Stored "round.delta" (delta total) τ∧
      Stored "round.slope" (beta total p) τ∧ Stored "round.gridStep" (gridStep total p) τ)
      (12*unitCost M+1):=by
  have hM1:1≤ M:=by omega
  have hMB:M< B:=by nlinarith
  have hp:p< B:=by
    have h:=num_bound hb.supportBound
    simpa only [NNRat.num_natCast] using h.trans_lt hMB
  have hk:RegionBudget.steps p< B:=by
    have h:=num_bound hb.stepsBound
    simpa only [NNRat.num_natCast] using h.trans_lt hMB
  have hpnInv:=inverse_height hM1 hb.supportBound
  have hkInv:=inverse_height hM1 hb.stepsBound
  have hdelta:LpInputSize.Height M (((4*(total*total))⁻¹:ℚ≥0):ℚ):=by simpa only [delta,pow_two] using hb.deltaBound
  have hdeltaInv:=inverse_height hM1 hdelta
  rintro σ hσ
  obtain ⟨σ1,raw1,p1⟩:=RamNatScalar.command_spec B (p) "round.support" "round.supportRat" hp (by omega) σ (hσ.supportValue)
  have r1:Run B stage1 σ σ1 (unitCost M):=raw1.mono (by dsimp [unitCost]; omega)
  obtain ⟨σ2,r2,p2⟩:=reciprocal_spec B M ((p:ℚ≥0)) "round.supportRat" "round.inverseSupport" hM1 hB hb.supportBound (by decide) (by decide) σ1 p1
  obtain ⟨σ3,r3,p3⟩:=product_spec B M (cost) ((p:ℚ≥0)⁻¹) "round.cost" "round.inverseSupport" "round.seed" hM1 hB hb.costBound hpnInv (by decide) (by decide) (by decide) (by decide) σ2
    ⟨(storedFrame (r1.seq (r2)) hσ.costData (by decide) (by decide)),p2⟩
  obtain ⟨σ4,r4,p4⟩:=product_spec B M (total) (total) "round.total" "round.total" "round.square" hM1 hB hb.totalBound hb.totalBound (by decide) (by decide) (by decide) (by decide) σ3
    ⟨(storedFrame (r1.seq (r2.seq (r3))) hσ.totalData (by decide) (by decide)),(storedFrame (r1.seq (r2.seq (r3))) hσ.totalData (by decide) (by decide))⟩
  have hfour:Spec B (fun _ => True) stage5 (fun _ τ => Stored "round.four" 4 τ) 4:=by
    (expose_names;
      (refine fun (σ_1:Env) (a:True) => let c0:Env→ Prop:=Stored "round.four" (@OfNat.ofNat NNRat (nat_lit 4) (@instOfNatAtLeastTwo NNRat (nat_lit 4) (@AddMonoidWithOne.toNatCast NNRat (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat (@NonAssocSemiring.toAddCommMonoidWithOne NNRat (@Semiring.toNonAssocSemiring NNRat (@DivisionSemiring.toSemiring NNRat (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))) (@Nat.instAtLeastTwoHAddOfNat ((3:Nat)) (@Nat.instNeZeroSucc ((2:Nat)))))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ_1; let c2:Env:=Env.setVar σ_1 "round.four.n" ((4:Nat)); let c3:Env:=Env.setVar c2 "round.four.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((4:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B stage5 σ_1 σ' ((4:Nat))) (c1 σ')) c3 (@And.intro (Run B stage5 σ_1 c3 ((4:Nat))) (c1 c3) (RunStep.mono B stage5 σ_1 c3 (c4 c6 c7) ((4:Nat)) (RunStep.seq B (Com.assign "round.four.n" (Expr.lit ((4:Nat)))) (Com.assign "round.four.d" (Expr.lit ((1:Nat)))) σ_1 c2 c3 c6 c7 (RunStep.assign B σ_1 "round.four.n" (Expr.lit ((4:Nat))) ((4:Nat)) (RunStep.eval_lit B ((4:Nat)) σ_1 (?nAX_g6752_0_0_0))) (RunStep.assign B c2 "round.four.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 (?nAX_g6752_0_0_1)))) (?nAX_g6752_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6752_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6752_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6752_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear raw1); (all_goals try clear r1); (all_goals try clear r2); (all_goals try clear r3); (all_goals try clear r4))
    all_goals simp [Stored]
  obtain ⟨σ5,raw5,p5⟩:=hfour σ4 True.intro
  have r5:Run B stage5 σ4 σ5 (unitCost M):=raw5.mono (by dsimp [unitCost]; omega)
  obtain ⟨σ6,r6,p6⟩:=product_spec B M ((4:ℚ≥0)) (total*total) "round.four" "round.square" "round.denominator" hM1 hB hb.fourBound hb.squareBound (by decide) (by decide) (by decide) (by decide) σ5
    ⟨p5,(storedFrame (r5) p4 (by decide) (by decide))⟩
  obtain ⟨σ7,r7,p7⟩:=reciprocal_spec B M (4*(total*total)) "round.denominator" "round.delta" hM1 hB hb.denominatorBound (by decide) (by decide) σ6 p6
  obtain ⟨σ8,raw8,p8⟩:=RamNatScalar.command_spec B (RegionBudget.steps p) "round.steps" "round.stepsRat" hk (by omega) σ7 (((r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7))))))).frame_var "round.steps" (by decide)).trans hσ.stepsValue)
  have r8:Run B stage8 σ7 σ8 (unitCost M):=raw8.mono (by dsimp [unitCost]; omega)
  obtain ⟨σ9,r9,p9⟩:=reciprocal_spec B M ((4*(total*total))⁻¹) "round.delta" "round.inverseDelta" hM1 hB hdelta (by decide) (by decide) σ8 (storedFrame (r8) p7 (by decide) (by decide))
  obtain ⟨σ10,r10,p10⟩:=product_spec B M ((RegionBudget.steps p:ℚ≥0)) (((4*(total*total))⁻¹)⁻¹) "round.stepsRat" "round.inverseDelta" "round.slope" hM1 hB hb.stepsBound hdeltaInv (by decide) (by decide) (by decide) (by decide) σ9
    ⟨(storedFrame (r9) p8 (by decide) (by decide)),p9⟩
  obtain ⟨σ11,r11,p11⟩:=reciprocal_spec B M ((RegionBudget.steps p:ℚ≥0)) "round.stepsRat" "round.inverseSteps" hM1 hB hb.stepsBound (by decide) (by decide) σ10 (storedFrame (r9.seq (r10)) p8 (by decide) (by decide))
  obtain ⟨σ12,r12,p12⟩:=product_spec B M ((4*(total*total))⁻¹) ((RegionBudget.steps p:ℚ≥0)⁻¹) "round.delta" "round.inverseSteps" "round.gridStep" hM1 hB hdelta hkInv (by decide) (by decide) (by decide) (by decide) σ11
    ⟨(storedFrame (r8.seq (r9.seq (r10.seq (r11)))) p7 (by decide) (by decide)),p11⟩
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq Run.skip)))))))))))
  refine ⟨σ12,rr.mono (by omega),?_,?_,?_,?_,?_⟩
  · refine ⟨storedFrame rr hσ.costData (by decide) (by decide),storedFrame rr hσ.totalData (by decide) (by decide),
      (rr.frame_var "round.support" (by decide)).trans hσ.supportValue,(rr.frame_var "round.steps" (by decide)).trans hσ.stepsValue⟩
  · simpa only [seed,div_eq_mul_inv] using (storedFrame (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12))))))))) p3 (by decide) (by decide))
  · simpa only [delta,pow_two] using (storedFrame (r8.seq (r9.seq (r10.seq (r11.seq (r12))))) p7 (by decide) (by decide))
  · simpa only [beta,delta,pow_two,div_eq_mul_inv] using (storedFrame (r11.seq (r12)) p10 (by decide) (by decide))
  · simpa only [gridStep,delta,pow_two,div_eq_mul_inv] using p12

end Lax455465Proofs.RamRoundingConstants

end

section

namespace Lax455465Proofs.RadiusData

open LpInputSize
open scoped NNRat

theorem coe_candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0):
    (candidates outDistance inDistance k delta).map (fun q:ℚ≥0 => (q:ℚ)) =
      RegionSearch.candidates (fun v => (outDistance v:ℚ)) (fun v => (inDistance v:ℚ)) k delta:=by
  simp only [candidates,List.map_append,List.map_map,List.map_ofFn,RegionSearch.candidates,Function.comp_apply,NNRat.coe_min]
  congr 2
  · apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply,NNRat.coe_mul,NNRat.coe_div,NNRat.coe_natCast,RegionSearch.grid]
    ring
  · congr 1
    funext v
    simp [max_eq_left (outDistance v).coe_nonneg]
  · funext v
    simp [max_eq_left (inDistance v).coe_nonneg]

theorem height {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k M:ℕ) (delta:ℚ≥0)
    (hM:1≤ M) (hk:k≤ M) (hu:Height M ((delta/(k:ℚ≥0):ℚ≥0):ℚ))
    (hd:Height M (delta:ℚ))
    (ho:∀ v,Height M (outDistance v:ℚ)) (hi:∀ v,Height M (inDistance v:ℚ)):
    ∀ q∈ candidates outDistance inDistance k delta,Height (M*M) (q:ℚ):=by
  intro q hq
  simp only [candidates,List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hq
    have hjk:j≤ k:=by have:=List.mem_range.mp hj; omega
    have hjh:Height M ((j:ℚ≥0):ℚ):=by
      simp only [NNRat.coe_natCast,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
      exact ⟨hjk.trans hk,hM⟩
    simpa only [NNRat.coe_mul] using height_mul hu hjh
  · obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact height_mono (UnsignedHeight.min_bound hd (ho v)) (by nlinarith)
  · obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact height_mono (UnsignedHeight.min_bound hd (hi v)) (by nlinarith)

end Lax455465Proofs.RadiusData

end

section

namespace Lax455465Proofs.RamFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem first_succ (predicate:ℕ→ Bool) (i:ℕ):
    first predicate (i+1)=match first predicate i with
      | some j => some j
      | none => if predicate i then some i else none:=by
  simp only [first,List.range_succ,List.find?_append,List.find?_cons,List.find?_nil]
  cases h:(List.range i).find? predicate <;> cases predicate i <;> rfl

def Invariant (R:Env→ Prop) (predicate:ℕ→ Bool) (count:ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars "find.i" ≤ count∧ Matches (first predicate (σ.vars "find.i")) σ

set_option maxHeartbeats 0 in

theorem command_spec (B count K:ℕ) (R:Env→ Prop) (predicate:ℕ→ Bool) (body:Com)
    (h1:1 < B) (hcount:count < B)
    (hlimit:∀ σ,R σ→ σ.vars "find.count"=count)
    (hset:∀ σ k name,R σ→ name∈ ["find.i","find.found","find.result"]→ R (σ.setVar name k))
    (hbody:∀ i,i < count→ Spec B (fun σ => R σ∧ σ.vars "find.i"=i) body
      (fun _ τ => R τ∧ τ.vars "find.ok"=if predicate i then 1 else 0) K)
    (hfresh:"find.i" ∉ body.wvars∧ "find.found" ∉ body.wvars∧ "find.result" ∉ body.wvars):
    Spec B R (command body) (fun _ τ => R τ∧ Matches (first predicate count) τ)
      ((K+20)*count+10):=by
  have hprocess:∀ i,i < count→
      Spec B (fun σ => R σ∧ σ.vars "find.i"=i∧ Matches (first predicate i) σ)
        (process body) (fun _ τ => R τ∧ τ.vars "find.i"=i∧ Matches (first predicate (i+1)) τ) (K+12):=by
    intro i hi σ ⟨hR,hindex,hmatch⟩
    have hiB:i < B:=hi.trans hcount
    cases hs:first predicate i with
    | some j =>
      have hm:σ.vars "find.found"=1∧ σ.vars "find.result"=j:=by simpa only [hs,Matches] using hmatch
      have hc:(Cond.eq (.var "find.found") (.lit 0)).evalB B σ=some false:=by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit (by omega)),hm.1]
        rfl
      refine ⟨σ,(Run.ite_false (c:=.seq body (.ite (.eq (.var "find.ok") (.lit 1)) record .skip)) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hR,hindex,?_⟩
      rw [first_succ,hs]
      exact hm
    | none =>
      have hm:σ.vars "find.found"=0:=by simpa only [hs,Matches] using hmatch
      have hc:(Cond.eq (.var "find.found") (.lit 0)).evalB B σ=some true:=by
        rw [evalB_condEq (evalB_var (hm ▸ (by omega:0 < B))) (evalB_lit (by omega)),hm]
        rfl
      obtain ⟨ν,rb,pb⟩:=hbody i hi σ ⟨hR,hindex⟩
      have hiν:ν.vars "find.i"=i:=(rb.frame_var "find.i" hfresh.1).trans hindex
      have hmν:ν.vars "find.found"=0:=(rb.frame_var "find.found" hfresh.2.1).trans hm
      cases hp:predicate i with
      | false =>
        have hok:ν.vars "find.ok"=0:=by simpa only [hp,Bool.false_eq_true,if_false] using pb.2
        have hcok:(Cond.eq (.var "find.ok") (.lit 1)).evalB B ν=some false:=by
          rw [evalB_condEq (evalB_var (hok ▸ (by omega:0 < B))) (evalB_lit h1),hok]
          rfl
        have rr:=Run.ite_true (d:=Com.skip) hc (rb.seq (Run.ite_false (c:=record) hcok Run.skip))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pb.1,hiν,?_⟩
        rw [first_succ,hs,hp]
        exact hmν
      | true =>
        have hok:ν.vars "find.ok"=1:=by simpa only [hp,if_true] using pb.2
        have hcok:(Cond.eq (.var "find.ok") (.lit 1)).evalB B ν=some true:=by
          rw [evalB_condEq (evalB_var (hok ▸ h1)) (evalB_lit h1),hok]
          rfl
        let τ:=(ν.setVar "find.found" 1).setVar "find.result" i
        have rrecord:Run B record ν τ 4:=(Run.assign (evalB_lit h1)).seq
          (Run.assign (by rw [evalB_var_iff]; exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hiν.symm,
            by simpa only [vars_setVar,String.reduceEq,if_false] using hiν ▸ hiB⟩))
        have rr:=Run.ite_true (d:=Com.skip) hc (rb.seq (Run.ite_true (d:=Com.skip) hcok rrecord))
        refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_,?_⟩
        · exact hset _ i "find.result" (hset ν 1 "find.found" pb.1 (by simp)) (by simp)
        · simpa only [τ,vars_setVar,String.reduceEq,if_false] using hiν
        · rw [first_succ,hs,hp]
          simp [Matches,τ]
  have hstep:Spec B (fun σ => Invariant R predicate count σ∧ σ.vars "find.i" < count)
      (step body) (fun σ τ => Invariant R predicate count τ∧ τ.vars "find.i"=σ.vars "find.i"+1) (K+16):=by
    rintro σ ⟨⟨hR,hi,hmatch⟩,hlt⟩
    let i:=σ.vars "find.i"
    obtain ⟨ν,rr,pr⟩:=hprocess i hlt σ ⟨hR,rfl,hmatch⟩
    have hiν:ν.vars "find.i"=i:=pr.2.1
    have rinc:Run B (.assign "find.i" (.add (.var "find.i") (.lit 1))) ν (ν.setVar "find.i" (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨ν.setVar "find.i" (i+1),(rr.seq rinc).mono (by omega),?_,by simp [i]⟩
    refine ⟨hset ν (i+1) "find.i" pr.1 (by simp),by simp; omega,?_⟩
    change Matches (first predicate (i+1)) (ν.setVar "find.i" (i+1))
    cases h:first predicate (i+1) <;>
      simpa only [h,Matches,vars_setVar,String.reduceEq,if_false] using pr.2.2
  have hscan:=Spec.forRangeZero "find.i" "find.count" (Invariant R predicate count) count (K+16)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν:=(σ.setVar "find.found" 0).setVar "find.result" 0
  have rinit:Run B init σ ν 4:=(Run.assign (evalB_lit (by omega:0 < B))).seq (Run.assign (evalB_lit (by omega)))
  have hRν:R ν:=hset _ 0 "find.result" (hset σ 0 "find.found" hR (by simp)) (by simp)
  have hinvariant:Invariant R predicate count (ν.setVar "find.i" 0):=by
    refine ⟨hset ν 0 "find.i" hRν (by simp),by simp,?_⟩
    simp [first,Matches,ν]
  obtain ⟨τ,rr,pr⟩:=hscan ν hinvariant
  refine ⟨τ,(rinit.seq rr).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,?_⟩
  simpa only [pr.2] using pr.1.2.2

end Lax455465Proofs.RamFind

end

section

namespace Lax455465Proofs.RadiusSearchData
open RegionQueryData
open scoped NNRat

theorem search_value {n:ℕ} (q:Query n) (delta:ℚ≥0) (p:ℕ)
    (hb:(q.beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta):
    ((RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta).find?
      (fun r => accepted (atRadius q r))).map (fun r:ℚ≥0 => (r:ℚ)) =
      RegionSearch.search (MetricMatrix.rational q.capacity) (MetricMatrix.rational q.length)
        (fun v => (q.outDistance v:ℚ)) (fun v => (q.inDistance v:ℚ)) q.seed delta p (direction q):=by
  unfold RegionSearch.search
  rw [← RadiusData.coe_candidates,List.find?_map]
  congr 2
  funext r
  simp only [Function.comp_def,accepted,atRadius,hb]
  rfl

end Lax455465Proofs.RadiusSearchData

end

section

namespace Lax455465Proofs.RamScalarComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName:String)
    (hB:2*M^2+3 < B) (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh:rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain:rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (command leftName rightName) (fun _ τ => τ.vars "cmp.le"=if (a:ℚ)≤ (b:ℚ) then 1 else 0) 64:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩:=load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1 (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ:Stored rightName b μ:=by
    have rr:=ra.seq rl
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩:=load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B b "right" h1 (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have plη:η.vars "left.s"=0∧ η.vars "left.n"=a.num∧ η.vars "left.d"=a.den:=by
    have r:=rb.seq rr
    simpa only [r.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),r.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rc,pc⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,ra.seq (rl.seq (rb.seq (rr.seq rc))),?_⟩
  have hp:τ.vars "cmp.le"=1↔ (a:ℚ)≤(b:ℚ):=by simpa only [RamUnsignedArithmetic.value] using pc.2
  by_cases h:(a:ℚ)≤(b:ℚ)
  · simpa only [if_pos h] using hp.mpr h
  · have hz:τ.vars "cmp.le"=0:=by have hn:=mt hp.mp h; omega
    simpa only [if_neg h] using hz

end Lax455465Proofs.RamScalarComparison

end

section

namespace Lax455465Proofs.ResidualData

open Lax455465.RationalEncoding MetricMatrix LpInputSize
open scoped NNRat

theorem rational_weights {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    (fun v => (weights I active v:ℚ))=RegionLoop.weights I active:=by
  funext v
  unfold weights RegionLoop.weights
  split_ifs <;> rfl

theorem rational_capacity {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    rational (capacity I active)=RegionLoop.capacity I active:=by
  funext u v
  dsimp only [capacity,rational,RegionLoop.capacity]
  split_ifs <;> rfl

theorem weights_height {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)) (w:ℕ)
    (h:∀ v,Height (2^w) (I.weight v:ℚ)):
    ∀ v,Height (2^w) (weights I active v:ℚ):=by
  intro v
  unfold weights
  split_ifs
  · exact h v
  · exact height_zero (by have:=Nat.two_pow_pos w; omega)

theorem capacity_height {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)) (w:ℕ)
    (h:∀ u v,Height (2^w) (I.capacity u v:ℚ)):
    ∀ u v,Height (2^w) (capacity I active u v:ℚ):=by
  intro u v
  unfold capacity
  split_ifs
  · exact h u v
  · exact height_zero (by have:=Nat.two_pow_pos w; omega)

end Lax455465Proofs.ResidualData

end

section

namespace Lax455465Proofs.RamRegionRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

structure Input {n:ℕ} (history:List (Entry n)) (e:Entry n) (σ:Env):Prop where
  data:Prefix (words history) "region.history" σ
  position:σ.vars "history.pos"=(words history).length
  root:σ.vars "region.root"=e.root.val
  radius:Stored "region.radius" e.radius σ
  outward:σ.vars "region.outward"=(if e.outward then 1 else 0)

end Lax455465Proofs.RamRegionRecord

end

section

namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat

def names:List String:= ["metric.n","metric.n2","round.support","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d",
  "round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d",
  "round.largeThreshold.n","round.largeThreshold.d"]
def arrays:List String:= ["flow.weights","flow.capacities","metric.old"]

theorem Fixed.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {length:MetricMatrix.Matrix n} {seed beta delta threshold:ℚ≥0} {p:ℕ}
    (h:Fixed I length seed beta delta threshold p σ)
    (hx:∀ x∈names,x∉cmd.wvars) (ha:∀ a∈arrays,a∉cmd.warrs):
    Fixed I length seed beta delta threshold p τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.supportValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.stepsValue,
    RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.thresholdData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData⟩

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n p:ℕ} (h:Room n p σ):Room n p τ:=by
  intro a count hm
  rw [RamFrames.run_array_length rr a]
  exact h a count hm

end Lax455465Proofs.RamRegionInvariant

end

section

namespace Lax455465Proofs.RamLargeThreshold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext
open scoped NNRat

def threshold (total:ℚ≥0):ℚ≥0:=total*(2/3:ℚ≥0)

theorem coe_threshold (total:ℚ≥0):(threshold total:ℚ)=2*(total:ℚ)/3:=by
  rw [threshold,NNRat.coe_mul]
  change (total:ℚ)*(2/3:ℚ)=2*(total:ℚ)/3
  ring

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) (total:ℚ≥0) (hM:3≤ M) (hB:2*M^2+3< B)
    (ht:LpInputSize.Height M (total:ℚ)):
    Spec B (Stored "round.total" total) command (fun _ τ => Stored "round.total" total τ∧
      Stored "round.largeThreshold" (threshold total) τ) (36*(total.den*3).size+96):=by
  have hfn:(2/3:ℚ≥0).num=2:=by
    rw [← NNRat.natAbs_num_coe]
    have hc:((2/3:ℚ≥0):ℚ)=(2/3:ℚ):=by norm_num
    rw [hc]
    norm_num
  have hfd:(2/3:ℚ≥0).den=3:=by
    rw [← NNRat.den_coe]
    have hc:((2/3:ℚ≥0):ℚ)=(2/3:ℚ):=by norm_num
    rw [hc]
    norm_num
  have h2:2< B:=by nlinarith
  have h3:3< B:=by nlinarith
  have hfac:Spec B (fun _ => True) factor (fun _ τ => Stored "round.largeFactor" (2/3:ℚ≥0) τ) 4:=by
    intro σ _
    let ν:=σ.setVar "round.largeFactor.n" 2
    let τ:=ν.setVar "round.largeFactor.d" 3
    have rn:Run B (.assign "round.largeFactor.n" (.lit 2)) σ ν 2:=Run.assign (evalB_lit h2)
    have rd:Run B (.assign "round.largeFactor.d" (.lit 3)) ν τ 2:=Run.assign (evalB_lit h3)
    refine ⟨τ,rn.seq rd,?_⟩
    exact ⟨(show τ.vars "round.largeFactor.n"=2 by rfl).trans hfn.symm,
      (show τ.vars "round.largeFactor.d"=3 by rfl).trans hfd.symm⟩
  have hb:LpInputSize.Height M ((2/3:ℚ≥0):ℚ):=
    LpInputSize.height_mono (show LpInputSize.Height 3 ((2/3:ℚ≥0):ℚ) by norm_num [LpInputSize.Height]) hM
  rintro σ hσ
  obtain ⟨ν,rf,pf⟩:=hfac σ True.intro
  obtain ⟨τ,rp,pp⟩:=RamScalarProduct.command_spec B M total (2/3) "round.total" "round.largeFactor" "round.largeThreshold" hB
    (num_bound ht) (den_bound ht) (num_bound hb) (den_bound hb) (by decide) (by decide) (by decide) (by decide) ν
    ⟨by simpa only [Stored,String.reduceAppend,rf.frame_var "round.total.n" (by decide),rf.frame_var "round.total.d" (by decide)] using hσ,pf⟩
  have rr:=rf.seq rp
  refine ⟨τ,rr.mono (by rw [hfd]; omega),?_,pp⟩
  simpa only [Stored,String.reduceAppend,rr.frame_var "round.total.n" (by decide),rr.frame_var "round.total.d" (by decide)] using hσ

end Lax455465Proofs.RamLargeThreshold

end

section

namespace Lax455465Proofs.RamActiveInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

theorem command_spec (B n:ℕ) (h2:2 < B) (hindex:2*n+2 < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ 2*n < (σ.arrs "region.active").length)
      command (fun _ τ => τ.vars "metric.n"=n∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun _:Fin n => true))) "region.active" τ)
      (28*n+8):=by
  let qs:=MaskedMassData.flags (fun _:Fin n => true)
  have hlen:qs.length=n:=List.length_ofFn
  have hv:∀ i, ∀ hi:i < qs.length,qs[i]=1:=by
    intro i hi
    simp [qs,MaskedMassData.flags]
  have hloop:=RamUnsignedVector.command_spec B 6 (fun σ => σ.vars "metric.n"=n)
    "active.i" "metric.n" "region.active" "active.position" qs [] RamFractionPrimitives.one (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => by rw [hv i hi]; simp; omega) (fun i hi => by rw [hv i hi]; simp; omega)
    (fun _ h => by simpa only [hlen] using h)
    (fun σ k h => by simpa only [vars_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ h => by
      obtain ⟨τ,rr,pr⟩:=RamFractionPrimitives.one_spec B (by omega) σ True.intro
      exact ⟨τ,rr,by simpa only [rr.frame_var "metric.n" (by decide)] using h.1,by simpa only [hv i hi,NNRat.coe_one] using pr⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => by simpa only [rr.frame_var "metric.n" (by decide)] using h)
    (by decide) (by decide)
  rintro σ ⟨hn,hroom⟩
  let ν:=σ.setVar "active.position" 0
  have rzero:Run B (.assign "active.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rr,pr⟩:=hloop ν ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [qs,List.nil_append] using pr.2.1⟩

end Lax455465Proofs.RamActiveInit

end

section

open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionExecutionData
open Lax455465.RationalEncoding RegionQueryData

def region {n:ℕ} (q:Query n) (root:Fin n):RegionLoop.Region n:=
  ⟨root,q.radius,direction q q.radius⟩

theorem large_iff {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (active:Finset (Fin n)) (root:Fin n) (seed beta r total:ℚ≥0):
    RamRegionBranch.large (RadiusSearchData.atRadius (query I length active root seed beta) r)
      (RamLargeThreshold.threshold total)↔
      (2/3:ℚ)*(total:ℚ)≤∑ v∈(region (RadiusSearchData.atRadius (query I length active root seed beta) r) root).ball
        (MetricMatrix.rational length),RegionLoop.weights I active v:=by
  let q:=RadiusSearchData.atRadius (query I length active root seed beta) r
  have hmass:=RegionSelection.chosen_mass (RegionLoop.weights I active)
    (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) (r:ℚ)
  have hball:(region q root).ball (MetricMatrix.rational length)=RegionCharging.chosenBall
      (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ))
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root) r:=by
    unfold region RegionLoop.Region.ball RegionCharging.chosenBall
    simp only [q,query,RamRegionSetup.query,RadiusSearchData.atRadius,direction,
      ResidualData.rational_weights,RegionLoop.chooseDirection,MetricMatrix.rational]
    rfl
  change _↔ _≤∑ v∈(region q root).ball (MetricMatrix.rational length),_
  rw [hball]
  change _↔ _≤∑ v∈RegionCharging.chosenBall (fun v => (length root v:ℚ))
    (fun v => (length v root:ℚ)) (RegionSelection.direction (RegionLoop.weights I active)
      (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ))) r,RegionLoop.weights I active v
  rw [hmass]
  unfold RamRegionBranch.large
  rw [RamLargeThreshold.coe_threshold]
  have hout:(BallMassData.mass q.weights q.outDistance q.radius:ℚ)=
      RegionSelection.ballMass (RegionLoop.weights I active) (fun v => (length root v:ℚ)) r:=by
    rw [BallMassData.coe_mass]
    simp only [q,query,RamRegionSetup.query,RadiusSearchData.atRadius,ResidualData.rational_weights]
  have hin:(BallMassData.mass q.weights q.inDistance q.radius:ℚ)=
      RegionSelection.ballMass (RegionLoop.weights I active) (fun v => (length v root:ℚ)) r:=by
    rw [BallMassData.coe_mass]
    simp only [q,query,RamRegionSetup.query,RadiusSearchData.atRadius,ResidualData.rational_weights]
  rw [hout,hin,le_min_iff]
  have he:2*(total:ℚ)/3=(2/3:ℚ)*(total:ℚ):=by ring
  rw [he]

theorem search_exists {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (active:Finset (Fin n)) (root:Fin n) (seed delta:ℚ≥0) (p:ℕ)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ)):
    ∃ r,RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
      (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some r:=by
  have hd:RationalDistances.Nonnegative (MetricMatrix.rational length):=fun u v => (length u v).coe_nonneg
  obtain ⟨r,hr,_,_,_⟩:=RegionSearch.search_correct (RegionLoop.capacity I active) (MetricMatrix.rational length)
    (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
    (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)
    (RegionLoop.capacity_nonnegative I active) hd hseed hdelta hp
    ((RegionLoop.residual_cost_le I _ active hd).trans hcost)
    (fun u v => by dsimp only [MetricMatrix.rational]; linarith [htri root u v])
    (fun u v => by dsimp only [MetricMatrix.rational]; linarith [htri v u root])
  exact ⟨r,hr⟩

end Lax455465Proofs.RegionExecutionData

end

section

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RegionRuntimeState
open Lax455465.RationalEncoding RegionQueryData RamRegionRecord
open scoped NNRat

theorem radius_coe {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ) (active:Finset (Fin n)) (root:Fin n)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta):
    (radius I length seed beta delta p active root).map (fun r:ℚ≥0 => (r:ℚ))=
      RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
        (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
        (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root):=by
  have h:=RadiusSearchData.search_value (RegionExecutionData.query I length active root seed beta) delta p hbeta
  dsimp only [RegionExecutionData.query,RamRegionSetup.query,RegionQueryData.direction] at h
  unfold RegionQueryData.direction at h
  simp only [ResidualData.rational_capacity,ResidualData.rational_weights] at h
  dsimp only [radius,RegionExecutionData.query,RamRegionSetup.query,RegionLoop.chooseDirection,MetricMatrix.rational] at h ⊢
  unfold MetricMatrix.rational
  exact h

end Lax455465Proofs.RegionRuntimeState

end

section

namespace Lax455465Proofs.SupportData
open scoped NNRat

def positive (q:ℚ≥0):Bool:=decide (0< q.num)
def count (qs:List ℚ≥0):ℕ:=qs.countP positive

theorem count_le (qs:List ℚ≥0):count qs≤ qs.length:=List.countP_le_length

theorem count_step (qs:List ℚ≥0) (i:ℕ) (hi:i< qs.length):
    count (qs.take (i+1))=count (qs.take i) + if 0< qs[i].num then 1 else 0:=by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [count,List.countP_append,List.countP_cons,List.countP_nil,Nat.zero_add,positive,decide_eq_true_eq]

theorem count_support {n:ℕ} (weights:Fin n→ ℚ≥0):
    count (List.ofFn weights)=(RegionSelection.support (fun v => (weights v:ℚ))).card:=by
  have hmap:(List.finRange n).map weights=List.ofFn weights:=by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [count,←hmap,List.countP_map]
  have hp:(fun v => positive (weights v))=(fun v => decide (0<(weights v:ℚ))):=by
    funext v
    simp only [positive,NNRat.num_pos]
    congr 1
  simp only [Function.comp_def]
  rw [hp,← List.Nodup.card_eq_countP (List.nodup_finRange n)]
  simp [RegionSelection.support]

theorem size_log (p:ℕ) (hp:0< p):p.size=Nat.log2 p+1:=by
  have hu:p<2^(Nat.log2 p+1):=by
    simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two p
  have hupper:p.size≤ Nat.log2 p+1:=Nat.size_le.mpr hu
  have hlow:2^Nat.log2 p≤ p:=by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (ne_of_gt hp)
  have hsize:p<2^p.size:=Nat.size_le.mp le_rfl
  have hnot:¬p.size≤ Nat.log2 p:=by
    intro h
    exact (not_le_of_gt hsize) ((Nat.pow_le_pow_right (by decide:1≤2) h).trans hlow)
  omega

end Lax455465Proofs.SupportData

end

section

namespace Lax455465Proofs.RamSupport
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def Invariant {n:ℕ} (weights:Fin n→ ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" σ∧
    σ.vars "support.i"≤ n∧ σ.vars "round.support"=SupportData.count ((List.ofFn weights).take (σ.vars "support.i"))

set_option maxHeartbeats 0 in
theorem step_spec (B M:ℕ) {n:ℕ} (weights:Fin n→ ℚ≥0) (h2:2< B)
    (hM:M< B) (hindex:2*n+2< B)
    (hn:∀ v, (weights v).num≤ M) (hd:∀ v, (weights v).den≤ M):
    Spec B (fun σ => Invariant weights σ∧ σ.vars "support.i"< n) step
      (fun σ τ => Invariant weights τ∧ τ.vars "support.i"=σ.vars "support.i"+1) 28:=by
  rintro σ ⟨⟨horder,hprefix,hile,hcount⟩,hi⟩
  let i:=σ.vars "support.i"
  let qs:=List.ofFn weights
  have hqi:i< qs.length:=by simpa only [qs,List.length_ofFn] using hi
  have he:qs[i]=weights ⟨i,hi⟩:=by simp only [qs,List.getElem_ofFn]
  have hnB:qs[i].num< B:=by rw [he]; exact (hn _).trans_lt hM
  have hdB:qs[i].den< B:=by rw [he]; exact (hd _).trans_lt hM
  have hcounter:σ.vars "round.support" ≤ i:=by
    rw [hcount]
    exact (SupportData.count_le _).trans (by simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hile]; rfl)
  obtain ⟨ν,rr,pr⟩:=RamUnsignedBuffer.read_spec B "flow.weights" "support.i" qs i hqi h2 (by omega) hnB hdB (by decide) σ ⟨hprefix,rfl⟩
  have hrat:ν.vars "rat.n"=qs[i].num:=by simpa only [NNRat.natAbs_num_coe] using pr.1.2.1
  have hcv:ν.vars "round.support"=SupportData.count (qs.take i):=
    (rr.frame_var "round.support" (by decide)).trans hcount
  have hci:ν.vars "support.i"=i:=(rr.frame_var _ (by decide)).trans rfl
  have hc:(Cond.eq (.var "rat.n") (.lit 0)).evalB B ν=some (decide (qs[i].num=0)):=by
    rw [evalB_condEq (evalB_var (hrat ▸ hnB)) (evalB_lit (by omega)),hrat]
    rfl
  have hf:∃ μ,Run B (.ite (.eq (.var "rat.n") (.lit 0)) .skip
      (.assign "round.support" (.add (.var "round.support") (.lit 1)))) ν μ 8∧
      μ.vars "round.support"=SupportData.count (qs.take (i+1)):=by
    by_cases hz:qs[i].num=0
    · refine ⟨ν,(Run.ite_true (d:=.assign "round.support" (.add (.var "round.support") (.lit 1)))
        (by simpa only [hz,decide_true] using hc) Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      rw [SupportData.count_step qs i hqi]
      simpa only [hz,Nat.lt_irrefl,if_false,Nat.add_zero] using hcv
    · let μ:=ν.setVar "round.support" (SupportData.count (qs.take i)+1)
      have hcB:ν.vars "round.support"+1< B:=by rw [rr.frame_var "round.support" (by decide)]; omega
      have rc:Run B (.assign "round.support" (.add (.var "round.support") (.lit 1))) ν μ 4:=
        Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hcv.symm,by omega⟩)
          (evalB_lit (by omega)) (by dsimp [Bop.apply]; rw [←hcv]; exact hcB))
      refine ⟨μ,(Run.ite_false (c:=Com.skip) (by simpa only [hz,decide_false] using hc) rc).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      simp only [μ,vars_setVar,if_true,SupportData.count_step qs i hqi,if_pos (Nat.pos_of_ne_zero hz)]
  obtain ⟨μ,rf,pf⟩:=hf
  have hmi:μ.vars "support.i"=i:=(rf.frame_var _ (by decide)).trans hci
  have rinc:Run B (.assign "support.i" (.add (.var "support.i") (.lit 1))) μ (μ.setVar "support.i" (i+1)) 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hmi.symm,by rw [hmi]; omega⟩)
      (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  have run:=(rr.seq rf).seq rinc
  refine ⟨μ.setVar "support.i" (i+1),run.mono (by omega),?_,by simp [i]⟩
  refine ⟨(run.frame_var _ (by decide)).trans horder,?_,by simp; omega,?_⟩
  · simpa only [Prefix,run.frame_arr "flow.weights" (by decide)] using hprefix
  · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using pf

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (weights:Fin n→ ℚ≥0) (h2:2< B)
    (hM:M< B) (hindex:2*n+2< B)
    (hn:∀ v, (weights v).num≤ M) (hd:∀ v, (weights v).den≤ M):
    Spec B (fun σ => σ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" σ)
      command (fun _ τ => τ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" τ∧
        τ.vars "round.support"=(RegionSelection.support (fun v => (weights v:ℚ))).card)
      (32*n+8):=by
  have hloop:=Spec.forRangeZero "support.i" "metric.n" (Invariant weights) n 28 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.1) (step_spec B M weights h2 hM hindex hn hd)
  rintro σ ⟨horder,hprefix⟩
  let ν:=σ.setVar "round.support" 0
  have rzero:Run B (.assign "round.support" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hinit:Invariant weights (ν.setVar "support.i" 0):=by
    refine ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using horder,
      by simpa only [Prefix,ν,arrs_setVar] using hprefix,by simp,?_⟩
    simp [ν,SupportData.count]
  obtain ⟨τ,rr,pr⟩:=hloop ν hinit
  refine ⟨τ,(rzero.seq rr).mono (by omega),pr.1.1,pr.1.2.1,?_⟩
  have ht:(List.ofFn weights).take n=List.ofFn weights:=by simp
  simpa only [pr.2,ht,SupportData.count_support] using pr.1.2.2.2

end Lax455465Proofs.RamSupport

end

section

namespace Lax455465Proofs.RamGridBudget
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem command_spec (B p:ℕ) (hp:0< p) (hB:2*p+4< B):
    Spec B (fun σ => σ.vars "round.support"=p) command
      (fun _ τ => τ.vars "round.support"=p∧ τ.vars "round.steps"=RegionBudget.steps p)
      (12*p.size+14):=by
  have hsize:p.size≤ p:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hk:2*p.size+2=RegionBudget.steps p:=by rw [SupportData.size_log p hp]; unfold RegionBudget.steps; omega
  rintro σ hσ
  let ν:=σ.setVar "size.value" p
  have rstart:Run B (.assign "size.value" (.var "round.support")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.symm,hσ ▸ (by omega:p< B)⟩)
  obtain ⟨μ,rw,pw⟩:=RamBitSize.word_spec B p (by omega) (by omega) ν (by simp [ν])
  let τ:=μ.setVar "round.steps" (RegionBudget.steps p)
  have rsave:Run B finish μ τ 6:=by
    change Run B finish μ (μ.setVar "round.steps" (RegionBudget.steps p)) 6
    rw [←hk]
    exact Run.assign (evalB_bin (op:=.add) (m:=2*p.size) (n:=2)
      (evalB_bin (op:=.mul) (m:=2) (n:=p.size) (evalB_lit (by omega))
        (by rw [evalB_var_iff]; exact ⟨pw.2.symm,pw.2 ▸ (by omega:p.size< B)⟩) (by dsimp [Bop.apply]; omega))
      (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  have rr:=rstart.seq (rw.seq rsave)
  exact ⟨τ,rr.mono (by omega),(rr.frame_var _ (by decide)).trans hσ,by simp [τ]⟩

end Lax455465Proofs.RamGridBudget

end

section

namespace Lax455465Proofs.RamRoundingInit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext RamVirtualState RoundingConstants
open scoped NNRat

structure Input {n:ℕ} (weights:Fin n→ ℚ≥0) (cost:ℚ≥0) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  weightsData:Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "flow.weights" σ
  costData:Stored "round.cost" cost σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (weights:Fin n→ ℚ≥0) (cost:ℚ≥0)
    (hb:RoundingConstantHeight.Bounds cost (total weights) (support weights) M)
    (hM:4≤ M) (hB:2*M^2+3< B) (hindex:2*n+4< B) (hp:0< support weights)
    (hw:∀ v,LpInputSize.Height M (weights v:ℚ))
    (hs:∀ i,LpInputSize.Height M (((List.ofFn weights).take i).sum:ℚ)):
    Spec B (Input weights cost) command (fun _ τ => Input weights cost τ∧
      RamRoundingConstants.Input cost (total weights) (support weights) τ∧
      Stored "round.seed" (seed cost (support weights)) τ∧
      Stored "round.delta" (delta (total weights)) τ∧
      Stored "round.slope" (beta (total weights) (support weights)) τ∧
      Stored "round.gridStep" (gridStep (total weights) (support weights)) τ)
      ((36*(M^2).size+200)*(n+1)+600*(M^2).size+2000):=by
  have hMB:M< B:=by nlinarith
  have hpN:support weights≤ n:=by
    rw [support,←SupportData.count_support]
    exact (SupportData.count_le _).trans (by simp)
  have hsize:(support weights).size≤ n:=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hpN
  rintro σ hσ
  let ν:=σ.setVar "sum.count" n
  have rstart:Run B (.assign "sum.count" (.var "metric.n")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.nValue.symm,hσ.nValue ▸ (by omega:n< B)⟩)
  obtain ⟨σ1,r1,p1⟩:=RamArraySum.command_spec B M "flow.weights" (List.ofFn weights) hB
    (by simp only [List.length_ofFn]; omega)
    (by intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact num_bound (hw v))
    (by intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact den_bound (hw v))
    (fun i => num_bound (hs i)) (fun i => den_bound (hs i)) ν
    ⟨by simp [ν],by simpa only [Prefix,ν,arrs_setVar] using hσ.weightsData⟩
  obtain ⟨σ2,r2,p2⟩:=save_spec B "round.total" (total weights)
    ((num_bound hb.totalBound).trans_lt hMB) ((den_bound hb.totalBound).trans_lt hMB) (by decide) σ1 p1.2
  have rprior:=rstart.seq (r1.seq r2)
  obtain ⟨σ3,r3,p3⟩:=RamSupport.command_spec B M weights (by omega) hMB (by omega)
    (fun v => num_bound (hw v)) (fun v => den_bound (hw v)) σ2
    ⟨(rprior.frame_var "metric.n" (by decide)).trans hσ.nValue,
      by simpa only [Prefix,rprior.frame_arr "flow.weights" (by decide)] using hσ.weightsData⟩
  obtain ⟨σ4,r4,p4⟩:=RamGridBudget.command_spec B (support weights) hp (by omega) σ3 p3.2.2
  have rafter:=r3.seq r4
  have rbefore:=rstart.seq (r1.seq (r2.seq (r3.seq r4)))
  have hconstants:RamRoundingConstants.Input cost (total weights) (support weights) σ4:=
    ⟨RamRoundingConstants.storedFrame rbefore hσ.costData (by decide) (by decide),
      RamRoundingConstants.storedFrame rafter p2 (by decide) (by decide),p4.1,p4.2⟩
  obtain ⟨τ,r5,p5⟩:=RamRoundingConstants.command_spec B M cost (total weights) (support weights) hb hM hB σ4 hconstants
  have rr:=rstart.seq (r1.seq (r2.seq (r3.seq (r4.seq r5))))
  refine ⟨τ,rr.mono ?_,?_,p5⟩
  · simp only [List.length_ofFn,RamRoundingConstants.unitCost]
    nlinarith
  · exact ⟨(rr.frame_var _ (by decide)).trans hσ.nValue,
      by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      RamRoundingConstants.storedFrame rr hσ.costData (by decide) (by decide)⟩

end Lax455465Proofs.RamRoundingInit

end

section

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionRuntimeCorrespondence
open Lax455465.RationalEncoding RegionRuntimeState RamRegionRecord RegionLoop

def outcome {n:ℕ} (s:State n):Option (Result n):=
  match s.status with
  | .large e => some (.large e.region)
  | .exhausted => some (.regions (s.history.map Entry.region))
  | _ => none

def finish {n:ℕ} (history:List (Entry n)) (result:Result n):Result n:=
  match result with
  | .large R => .large R
  | .regions rest => .regions (history.map Entry.region++rest)

theorem coe_total {n:ℕ} (I:RationalInstance n):
    (RamRoundingInit.total I.weight:ℚ)=LargeBallRounding.total I:=by
  simp [RamRoundingInit.total,LargeBallRounding.total,List.sum_ofFn,NNRat.cast_sum]

theorem entry_region {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (active:Finset (Fin n)) (root:Fin n) (seed beta r:ℚ≥0):
    (RamSmallRegion.selected (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) r) root).region=
      ⟨root,(r:ℚ),chooseDirection I (MetricMatrix.rational length) active root r⟩:=by
  unfold RamSmallRegion.selected Entry.region
  simp only [RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,
    RegionQueryData.direction,ResidualData.rational_weights,chooseDirection]
  rfl

theorem frozen_iterate {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p k:ℕ) (s:State n) (h:s.status≠.running):
    (advance I length seed beta delta threshold p)^[k] s=s:=by
  have hf:advance I length seed beta delta threshold p s=s:=by
    cases hs:s.status <;> simp_all [advance]
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,hf]

set_option maxHeartbeats 0 in

theorem run_eq {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p fuel:ℕ) (active:Finset (Fin n)) (history:List (Entry n))
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hfuel:(RegionSelection.support (weights I active)).card≤ fuel):
    outcome ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[fuel+1]
      ⟨active,history,.running⟩)=
      (run I (MetricMatrix.rational length) seed delta p fuel active).map (finish history):=by
  let threshold:=RamLargeThreshold.threshold (RamRoundingInit.total I.weight)
  let f:=advance I length seed beta delta threshold p
  induction fuel generalizing active history with
  | zero =>
    have hn:RegionSelection.chooseRoot (weights I active)=none:=
      (root_none_iff _).mpr (by omega)
    simp only [Nat.zero_add,Function.iterate_one,advance,hn,run,outcome,finish,
      Option.map_some,List.nil_append,List.append_nil,if_true]
  | succ fuel ih =>
    cases hroot:RegionSelection.chooseRoot (weights I active) with
    | none =>
      have ha:f ⟨active,history,.running⟩=⟨active,history,.exhausted⟩:=by simp [f,advance,hroot]
      dsimp only [f,threshold] at ha
      rw [Function.iterate_succ_apply,ha]
      rw [frozen_iterate I length seed beta delta threshold p (fuel+1) ⟨active,history,.exhausted⟩ (by intro h; cases h)]
      simp only [run,hroot,outcome,finish,Option.map_some,List.append_nil]
    | some root =>
      obtain ⟨rQ,hsQ⟩:=RegionExecutionData.search_exists I length active root seed delta p hseed hdelta hp htri hcost
      have hc:=radius_coe I length seed beta delta p active root hbeta
      cases hr:radius I length seed beta delta p active root with
      | none => rw [hr,Option.map_none,hsQ] at hc; cases hc
      | some r =>
        have hs:RegionSearch.search (capacity I active) (MetricMatrix.rational length)
            (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
            (chooseDirection I (MetricMatrix.rational length) active root)=some (r:ℚ):=by
          simpa only [hr,Option.map_some] using hc.symm
        have hsRun:RegionSearch.search (capacity I active) (MetricMatrix.rational length)
            (MetricMatrix.rational length root) (fun v => MetricMatrix.rational length v root) seed delta p
            (chooseDirection I (MetricMatrix.rational length) active root)=some (r:ℚ):=by
          dsimp only [MetricMatrix.rational] at hs ⊢
          exact hs
        let q:=RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) r
        let e:=RamSmallRegion.selected q root
        let R:Region n:= ⟨root,(r:ℚ),chooseDirection I (MetricMatrix.rational length) active root r⟩
        have he:e.region=R:=entry_region I length active root seed beta r
        have hlarge:RamRegionBranch.large q threshold↔
            (2/3:ℚ)*LargeBallRounding.total I≤∑ v∈R.ball (MetricMatrix.rational length),weights I active v:=by
          have h:=RegionExecutionData.large_iff I length active root seed beta r (RamRoundingInit.total I.weight)
          rw [coe_total] at h
          have heR:RegionExecutionData.region q root=R:=by
            exact (show RegionExecutionData.region q root=e.region from rfl).trans he
          change RamRegionBranch.large q threshold↔
            (2/3:ℚ)*LargeBallRounding.total I≤∑ v∈(RegionExecutionData.region q root).ball (MetricMatrix.rational length),weights I active v at h
          rw [heR] at h
          exact h
        have hrun:run I (MetricMatrix.rational length) seed delta p (fuel+1) active=
            if (2/3:ℚ)*LargeBallRounding.total I≤∑ v∈R.ball (MetricMatrix.rational length),weights I active v then
              some (.large R)
            else (run I (MetricMatrix.rational length) seed delta p fuel (active \ R.ball (MetricMatrix.rational length))).map
              (fun result => match result with
                | .large T => .large T
                | .regions rest => .regions (R::rest)):=by
          simp only [run,hroot,hsRun]
          rfl
        by_cases hl:RamRegionBranch.large q threshold
        · have ha:f ⟨active,history,.running⟩=⟨active,history,.large e⟩:=by
            simp only [f,advance,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_pos hl]
          dsimp only [f,threshold] at ha
          rw [Function.iterate_succ_apply,ha]
          rw [frozen_iterate I length seed beta delta threshold p (fuel+1) ⟨active,history,.large e⟩ (by intro h; cases h)]
          have hlQ:=hlarge.mp hl
          rw [hrun,if_pos hlQ]
          simp only [outcome,finish,Option.map_some,he]
        · have hsmall:¬(2/3:ℚ)*LargeBallRounding.total I≤∑ v∈R.ball (MetricMatrix.rational length),weights I active v:=
            mt hlarge.mpr hl
          have ha:f ⟨active,history,.running⟩=
              ⟨active \ R.ball (MetricMatrix.rational length),history++[e],.running⟩:=by
            simp only [f,advance,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_neg hl,he]
          have hrootPos:0< weights I active root:=by simpa only [decide_eq_true_eq] using List.find?_some hroot
          have hprogress:(RegionSelection.support (weights I (active \ R.ball (MetricMatrix.rational length)))).card<
              (RegionSelection.support (weights I active)).card:=by
            rw [weights_remove]
            apply RegionSelection.support_decreases _ _ root hrootPos
            have hrad:=RegionSearch.search_radius (capacity I active) (MetricMatrix.rational length)
              (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
              (chooseDirection I (MetricMatrix.rational length) active root) r hdelta.le hs
            have hrpos:0< r:=by exact_mod_cast hrad.1
            unfold R Region.ball
            cases hd:chooseDirection I (MetricMatrix.rational length) active root r <;>
              simp [RegionCharging.ball,hd,MetricMatrix.rational,hdiag,hrad.1,hrpos]
          dsimp only [f,threshold] at ha
          rw [Function.iterate_succ_apply,ha]
          rw [ih (active \ R.ball (MetricMatrix.rational length)) (history++[e]) (by omega)]
          rw [hrun,if_neg hsmall]
          simp only [Option.map_map]
          apply congrArg (fun g => (run I (MetricMatrix.rational length) seed delta p fuel (active \ R.ball (MetricMatrix.rational length))).map g)
          funext result
          cases result <;> simp [finish,Function.comp_def,List.map_append,he,List.append_assoc]

theorem final_correct {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hsupport:(RegionSelection.support (weights I Finset.univ)).card≤ p):
    ValidFinal I length seed delta p
      ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
        (RamRegionBoundedLoop.initial n)):=by
  let final:=(advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
    (RamRegionBoundedLoop.initial n)
  change ValidFinal I length seed delta p final
  have hd:RationalDistances.Nonnegative (MetricMatrix.rational length):=fun u v => (length u v).coe_nonneg
  obtain ⟨result,hr,hvalid⟩:=run_correct I (MetricMatrix.rational length) seed delta p p hd
    (fun v => by simp [MetricMatrix.rational,hdiag]) htri hseed hdelta hp hcost Finset.univ hsupport
  have heq:=run_eq I length seed beta delta p p Finset.univ [] hbeta hseed hdelta hp hdiag htri hcost hsupport
  rw [hr,Option.map_some] at heq
  have heq':outcome final=some result:=by
    cases result <;> simpa only [final,RamRegionBoundedLoop.initial,finish,List.map_nil,List.nil_append] using heq
  cases hs:final.status with
  | running => simp only [outcome,hs] at heq'; cases heq'
  | failed => simp only [outcome,hs] at heq'; cases heq'
  | large e =>
    have he:result=.large e.region:=by simpa only [outcome,hs,Option.some.injEq] using heq'.symm
    subst result
    simpa only [ValidFinal,hs] using hvalid
  | exhausted =>
    have he:result=.regions (final.history.map Entry.region):=by simpa only [outcome,hs,Option.some.injEq] using heq'.symm
    subst result
    simp only [ValidFinal,hs]
    exact ⟨hvalid.1,(by simpa only [List.length_map] using hvalid.2.trans hsupport)⟩

end Lax455465Proofs.RegionRuntimeCorrespondence

end

section

namespace Lax455465Proofs.CutScoreData
open Lax455465.RationalEncoding MetricMatrix
open scoped BigOperators NNRat

theorem coe_mass {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):(mass I S:ℚ)=CutSweeps.massQ I S:=by
  unfold mass vertexFlags
  rw [MaskedMassData.coe_sum]
  simp only [ResidualData.mask,decide_eq_true_eq,CutSweeps.massQ,←Finset.sum_filter]
  simp

theorem mass_add_complement {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    mass I S+mass I Sᶜ=RamRoundingInit.total I.weight:=by
  apply NNRat.coe_injective
  rw [NNRat.coe_add,coe_mass,coe_mass,RegionRuntimeCorrespondence.coe_total]
  unfold CutSweeps.massQ LargeBallRounding.total
  exact Finset.sum_add_sum_compl S _

theorem otherMass_eq {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):otherMass I S=mass I Sᶜ:=by
  rw [otherMass,←mass_add_complement I S,add_tsub_cancel_left]

theorem arc_condition {n:ℕ} (S:Finset (Fin n)) (u v:Fin n):(arcFlags S u v).num=1↔ u∈S∧ v∉S:=by
  by_cases hu:u∈S <;> by_cases hv:v∈S <;>
    simp [arcFlags,RamArcMask.matrix,RamBooleanArithmetic.bit,RamBooleanArithmetic.flag,ResidualData.mask,hu,hv]

theorem coe_capacity {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):(capacity I S:ℚ)=CutSweeps.capacityQ I S:=by
  unfold capacity
  rw [BoundaryData.masked_matrix]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,NNRat.cast_sum]
  have hsum (T:Finset (Fin n)) (g:Fin n→ ℚ):(∑ v∈T,g v)=∑ v,if v∈T then g v else 0:=by
    have ht:Finset.univ.filter (fun v => v∈T)=T:=by ext v; simp
    have h:=Finset.sum_filter (s:=Finset.univ) (p:=fun v => v∈T) (f:=g)
    rwa [ht] at h
  rw [CutSweeps.capacityQ,hsum S]
  simp_rw [hsum Sᶜ]
  simp only [Finset.mem_compl]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hus:u∈S
  · simp only [hus,if_true]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvs:v∈S <;> simp [arc_condition,hus,hvs]
  · simp [arc_condition,hus]

theorem coe_demand {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    (demand I S:ℚ)=CutSweeps.massQ I S*CutSweeps.massQ I Sᶜ:=by
  rw [demand,NNRat.coe_mul,otherMass_eq,coe_mass,coe_mass]

theorem coe_ratio {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):(ratio I S:ℚ)=CutSweeps.ratioQ I S:=by
  rw [ratio,NNRat.coe_div,coe_capacity,coe_demand]
  rfl

theorem admissible_iff {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    CutSweeps.admissibleQ I S↔ 0<(demand I S).num:=by
  rw [CutSweeps.admissibleQ_iff_product_pos,←coe_demand]
  exact ⟨fun h => NNRat.num_pos.mpr (by exact_mod_cast h),fun h => by exact_mod_cast NNRat.num_pos.mp h⟩

end Lax455465Proofs.CutScoreData

end

section

namespace Lax455465Proofs.BestCutIndex
open scoped NNRat

def next (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i:ℕ):Option ℕ→ Option ℕ
  | none => if valid i then some i else none
  | some j => if valid i∧ value i< value j then some i else some j

def best (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0):ℕ→ Option ℕ
  | 0 => none
  | i+1 => next valid value i (best valid value i)

theorem best_none (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i:ℕ):
    best valid value i=none↔ ∀ j < i, ¬valid j:=by
  induction i with
  | zero => simp [best]
  | succ i ih =>
    cases hb:best valid value i with
    | none =>
      have hn:=ih.mp hb
      simp only [best,hb,next]
      by_cases hv:valid i
      · simp only [if_pos hv,Option.some_ne_none,false_iff]
        intro h
        exact h i (by omega) hv
      · simp only [if_neg hv,true_iff]
        intro j hj
        by_cases he:j=i
        · simpa only [he] using hv
        · exact hn j (by omega)
    | some j =>
      have hex:∃ k < i,valid k:=by
        by_contra hn
        have hall:∀ k < i, ¬valid k:=by
          intro k hk hv
          exact hn ⟨k,hk,hv⟩
        have hnone:=ih.mpr hall
        rw [hb] at hnone
        cases hnone
      simp only [best,hb,next]
      constructor
      · split_ifs <;> intro h <;> cases h
      · intro h
        obtain ⟨k,hk,hv⟩:=hex
        exact False.elim (h k (by omega) hv)

theorem best_sound (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i j:ℕ)
    (h:best valid value i=some j):j < i∧ valid j:=by
  induction i generalizing j with
  | zero => simp [best] at h
  | succ i ih =>
    simp only [best] at h
    cases hb:best valid value i with
    | none =>
      simp only [hb,next] at h
      split_ifs at h with hv
      · have he:i=j:=Option.some.inj h
        subst j
        exact ⟨by omega,hv⟩
    | some k =>
      simp only [hb,next] at h
      split_ifs at h with hv
      · have he:i=j:=Option.some.inj h
        subst j
        exact ⟨by omega,hv.1⟩
      · have he:k=j:=Option.some.inj h
        subst j
        have hs:=ih k hb
        exact ⟨by omega,hs.2⟩

theorem best_minimal (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i j k:ℕ)
    (h:best valid value i=some j) (hk:k < i) (hvalid:valid k):value j≤ value k:=by
  induction i generalizing j with
  | zero => omega
  | succ i ih =>
    simp only [best] at h
    cases hb:best valid value i with
    | none =>
      have hn:=(best_none valid value i).mp hb
      have he:k=i:=by
        by_contra he
        exact hn k (by omega) hvalid
      subst k
      simp only [hb,next,if_pos hvalid,Option.some.injEq] at h
      subst j
      exact le_rfl
    | some old =>
      simp only [hb,next] at h
      by_cases hv:valid i∧ value i< value old
      · rw [if_pos hv] at h
        have he:i=j:=Option.some.inj h
        subst j
        by_cases he:k=i
        · subst k; exact le_rfl
        · exact hv.2.le.trans (ih old hb (by omega))
      · rw [if_neg hv] at h
        have he:old=j:=Option.some.inj h
        subst j
        by_cases he:k=i
        · subst k
          exact le_of_not_gt (fun hlt => hv ⟨hvalid,hlt⟩)
        · exact ih old hb (by omega)

end Lax455465Proofs.BestCutIndex

end

section

namespace Lax455465Proofs.RamBestUpdate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open scoped NNRat

def Matches (value:ℕ→ ℚ≥0):Option ℕ→ Env→ Prop
  | none,σ => σ.vars "best.found"=0
  | some j,σ => σ.vars "best.found"=1∧ σ.vars "best.index"=j∧ Stored "best.value" (value j) σ

def Current (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i:ℕ) (σ:Env):Prop:=
  σ.vars "cut.candidate"=i∧ σ.vars "cut.valid"=(if valid i then 1 else 0)∧ Stored "cut.ratio" (value i) σ

theorem update_spec (B:ℕ) (i:ℕ) (q:ℚ≥0) (hi:i< B) (hn:q.num< B) (hd:q.den< B) (h1:1< B):
    Spec B (fun σ => σ.vars "cut.candidate"=i∧ Stored "cut.ratio" q σ) update
      (fun _ τ => τ.vars "best.found"=1∧ τ.vars "best.index"=i∧ Stored "best.value" q τ) 8:=by
  rintro σ ⟨hidx,hq⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "best.found") ((1:Nat))) (And (@Eq Nat (Env.vars τ "best.index") i) (Stored "best.value" q τ))) σ; let c1:Nat:=Env.vars (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "cut.ratio.n"; let c2:Env:=Env.setVar (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "best.value.n" c1; let c3:Nat:=Env.vars c2 "cut.ratio.d"; let c4:Env:=Env.setVar c2 "best.value.d" c3; let c5:Env:=Env.setVar c4 "best.found" ((1:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.var "cut.candidate")); let c9:Nat:=c7 (Expr.size (Expr.var "cut.ratio.n")); let c10:Nat:=c7 (Expr.size (Expr.var "cut.ratio.d")); let c11:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c12:Nat:=c6 c10 c11; let c13:Nat:=c6 c9 c12; let c14:Com:=Com.assign "best.found" (Expr.lit ((1:Nat))); let c15:Com:=Com.seq (Com.assign "best.value.d" (Expr.var "cut.ratio.d")) c14; let c16:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B update σ σ' ((8:Nat))) (c0 σ')) c5 (@And.intro (Run B update σ c5 ((8:Nat))) (c0 c5) (RunStep.mono B update σ c5 (c6 c8 c13) ((8:Nat)) (RunStep.seq B (Com.assign "best.index" (Expr.var "cut.candidate")) (Com.seq (Com.assign "best.value.n" (Expr.var "cut.ratio.n")) c15) σ (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) c5 c8 c13 (RunStep.assign B σ "best.index" (Expr.var "cut.candidate") (Env.vars σ "cut.candidate") (RunStep.eval_var B σ "cut.candidate" (?nAX_g7010_0_0_0))) (RunStep.seq B (Com.assign "best.value.n" (Expr.var "cut.ratio.n")) c15 (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) c2 c5 c9 c12 (RunStep.assign B (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "best.value.n" (Expr.var "cut.ratio.n") c1 (RunStep.eval_var B (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "cut.ratio.n" ?_)) (RunStep.seq B (Com.assign "best.value.d" (Expr.var "cut.ratio.d")) c14 c2 c4 c5 c10 c11 (RunStep.assign B c2 "best.value.d" (Expr.var "cut.ratio.d") c3 (RunStep.eval_var B c2 "cut.ratio.d" ?_)) (RunStep.assign B c4 "best.found" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4 h1))))) (?nAX_g7010_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7010_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7010_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0)
    (i:ℕ) (old:Option ℕ) (hB:2*M^2+3< B) (hi:i< B)
    (hcur:LpInputSize.Height M (value i:ℚ))
    (hold:∀ j,old=some j→ LpInputSize.Height M (value j:ℚ)):
    Spec B (fun σ => Current valid value i σ∧ Matches value old σ) command
      (fun _ τ => Current valid value i τ∧ Matches value (BestCutIndex.next valid value i old) τ) 84:=by
  have hMB:M< B:=by nlinarith
  have h1:1< B:=by nlinarith
  have currentFrame {cmd:Com} {σ τ:Env} {K:ℕ} (rr:Run B cmd σ τ K) (h:Current valid value i σ)
      (hx:∀ x∈["cut.candidate","cut.valid","cut.ratio.n","cut.ratio.d"],x∉cmd.wvars):Current valid value i τ:=by
    exact ⟨(rr.frame_var _ (hx _ (by simp))).trans h.1,(rr.frame_var _ (hx _ (by simp))).trans h.2.1,
      RamRoundingConstants.storedFrame rr h.2.2 (hx _ (by simp)) (hx _ (by simp))⟩
  rintro σ ⟨hσ,holdσ⟩
  by_cases hv:valid i
  · have hvalid:σ.vars "cut.valid"=1:=by simpa only [if_pos hv] using hσ.2.1
    have hc:(Cond.eq (.var "cut.valid") (.lit 1)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hvalid ▸ h1)) (evalB_lit h1),hvalid]
      rfl
    cases old with
    | none =>
      have hf:σ.vars "best.found"=0:=holdσ
      have hfound:(Cond.eq (.var "best.found") (.lit 0)).evalB B σ=some true:=by
        rw [evalB_condEq (evalB_var (hf ▸ (by omega:0< B))) (evalB_lit (by omega)),hf]
        rfl
      obtain ⟨τ,ru,pu⟩:=update_spec B i (value i) hi ((num_bound hcur).trans_lt hMB) ((den_bound hcur).trans_lt hMB) h1 σ ⟨hσ.1,hσ.2.2⟩
      have rr:=Run.ite_true (d:=.skip) hc (Run.ite_true (d:=compare) hfound ru)
      exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),
        by simpa only [BestCutIndex.next,if_pos hv,Matches] using pu⟩
    | some j =>
      have hj:LpInputSize.Height M (value j:ℚ):=hold j rfl
      have hf:σ.vars "best.found"=1:=holdσ.1
      have hfound:(Cond.eq (.var "best.found") (.lit 0)).evalB B σ=some false:=by
        rw [evalB_condEq (evalB_var (hf ▸ h1)) (evalB_lit (by omega)),hf]
        rfl
      obtain ⟨ν,rc,pc⟩:=RamScalarComparison.command_spec B M (value j) (value i) "best.value" "cut.ratio" hB
        (num_bound hj) (den_bound hj) (num_bound hcur) (den_bound hcur) (by decide) (by decide) (by decide) σ ⟨holdσ.2.2,hσ.2.2⟩
      have hν:=currentFrame rc hσ (by decide)
      by_cases hbetter:value i< value j
      · have hcmp:ν.vars "cmp.le"=0:=by
          simpa only [NNRat.coe_le_coe,if_neg (not_le.mpr hbetter)] using pc
        have htest:(Cond.eq (.var "cmp.le") (.lit 0)).evalB B ν=some true:=by
          rw [evalB_condEq (evalB_var (hcmp ▸ (by omega:0< B))) (evalB_lit (by omega)),hcmp]
          rfl
        obtain ⟨τ,ru,pu⟩:=update_spec B i (value i) hi ((num_bound hcur).trans_lt hMB) ((den_bound hcur).trans_lt hMB) h1 ν ⟨hν.1,hν.2.2⟩
        have rr:=Run.ite_true (d:=.skip) hc (Run.ite_false (c:=update) hfound
          (rc.seq (Run.ite_true (d:=.skip) htest ru)))
        exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),
          by simpa only [BestCutIndex.next,if_pos (And.intro hv hbetter),Matches] using pu⟩
      · have hcmp:ν.vars "cmp.le"=1:=by
          simpa only [NNRat.coe_le_coe,if_pos (le_of_not_gt hbetter)] using pc
        have htest:(Cond.eq (.var "cmp.le") (.lit 0)).evalB B ν=some false:=by
          rw [evalB_condEq (evalB_var (hcmp ▸ h1)) (evalB_lit (by omega)),hcmp]
          rfl
        have rr:=Run.ite_true (d:=.skip) hc (Run.ite_false (c:=update) hfound
          (rc.seq (Run.ite_false (c:=update) htest Run.skip)))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),?_⟩
        simp only [BestCutIndex.next,if_neg (show ¬(valid i∧ value i< value j) from fun h => hbetter h.2),Matches]
        exact ⟨(rc.frame_var _ (by decide)).trans holdσ.1,(rc.frame_var _ (by decide)).trans holdσ.2.1,
          RamRoundingConstants.storedFrame rc holdσ.2.2 (by decide) (by decide)⟩
  · have hvalid:σ.vars "cut.valid"=0:=by simpa only [if_neg hv] using hσ.2.1
    have hc:(Cond.eq (.var "cut.valid") (.lit 1)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hvalid ▸ (by omega:0< B))) (evalB_lit h1),hvalid]
      rfl
    refine ⟨σ,(Run.ite_false (c:=choose) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hσ,?_⟩
    cases old <;> simpa only [BestCutIndex.next,hv,if_false,false_and] using holdσ

end Lax455465Proofs.RamBestUpdate

end

section

namespace Lax455465Proofs.RamBestFold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamBestUpdate
open scoped NNRat

def bestNames:List String:= ["best.found","best.index","best.value.n","best.value.d"]

theorem Matches.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {value:ℕ→ ℚ≥0} {old:Option ℕ} (h:Matches value old σ)
    (hx:∀ x∈bestNames,x∉cmd.wvars):Matches value old τ:=by
  cases old with
  | none => exact (rr.frame_var _ (hx _ (by simp [bestNames]))).trans h
  | some j =>
    exact ⟨(rr.frame_var _ (hx _ (by simp [bestNames]))).trans h.1,
      (rr.frame_var _ (hx _ (by simp [bestNames]))).trans h.2.1,
      RamRoundingConstants.storedFrame rr h.2.2 (hx _ (by simp [bestNames])) (hx _ (by simp [bestNames]))⟩

def Invariant (R:Env→ Prop) (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (count:ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars "cut.candidate"≤ count∧ Matches value (BestCutIndex.best valid value (σ.vars "cut.candidate")) σ

set_option maxHeartbeats 0 in

theorem command_spec (B M K:ℕ) (R:Env→ Prop) (valid:ℕ→ Prop) [DecidablePred valid]
    (value:ℕ→ ℚ≥0) (count:ℕ) (producer:Com) (hB:2*M^2+3< B) (hcount:count< B)
    (hvalue:∀ i< count,LpInputSize.Height M (value i:ℚ))
    (hlimit:∀ σ,R σ→σ.vars "cut.count"=count)
    (hset:∀ σ k name,name∈["cut.candidate","best.found","best.index"]→ R σ→R (σ.setVar name k))
    (hproducer:∀ i< count,Spec B (fun σ => R σ∧ σ.vars "cut.candidate"=i) producer
      (fun _ τ => R τ∧ Current valid value i τ) K)
    (hproducerFrame:∀ x∈bestNames,x∉producer.wvars)
    (hupdateFrame:∀ {σ τ:Env} {k:ℕ},Run B RamBestUpdate.command σ τ k→R σ→R τ):
    Spec B R (command producer) (fun _ τ => R τ∧ Matches value (BestCutIndex.best valid value count) τ)
      ((K+92)*count+10):=by
  have h1:1< B:=by nlinarith
  have hstep:Spec B (fun σ => Invariant R valid value count σ∧ σ.vars "cut.candidate"< count)
      (step producer) (fun σ τ => Invariant R valid value count τ∧ τ.vars "cut.candidate"=σ.vars "cut.candidate"+1)
      (K+88):=by
    rintro σ ⟨⟨hR,hle,hmatch⟩,hlt⟩
    let i:=σ.vars "cut.candidate"
    obtain ⟨ν,rp,pp⟩:=hproducer i hlt σ ⟨hR,rfl⟩
    have hm:=Matches.frame rp hmatch hproducerFrame
    obtain ⟨μ,ru,pu⟩:=RamBestUpdate.command_spec B M valid value i (BestCutIndex.best valid value i) hB (hlt.trans hcount)
      (hvalue i hlt) (fun j hj => hvalue j ((BestCutIndex.best_sound valid value i j hj).1.trans hlt)) ν ⟨pp.2,hm⟩
    have hμ:μ.vars "cut.candidate"=i:=pu.1.1
    have hnext:i+1< B:=by dsimp [i]; omega
    let τ:=μ.setVar "cut.candidate" (i+1)
    have ri:Run B (.assign "cut.candidate" (.add (.var "cut.candidate") (.lit 1))) μ τ 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hμ.symm,hμ ▸ (by omega:i< B)⟩)
        (evalB_lit h1) hnext)
    have hmatchτ:=Matches.frame ri pu.2 (by dsimp [bestNames,Com.wvars]; decide)
    refine ⟨τ,rp.seq (ru.seq ri),?_,by simp [τ,i]⟩
    refine ⟨hset μ (i+1) "cut.candidate" (by simp) (hupdateFrame ru pp.1),by simp [τ]; dsimp [i]; omega,?_⟩
    simpa only [τ,vars_setVar,if_true,BestCutIndex.best] using hmatchτ
  have hs:=Spec.forRangeZero "cut.candidate" "cut.count" (Invariant R valid value count) count (K+88)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hσ
  let ν:=σ.setVar "best.found" 0
  let μ:=ν.setVar "best.index" 0
  have rf:Run B (.assign "best.found" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have rix:Run B (.assign "best.index" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (by omega))
  have hRμ:=hset ν 0 "best.index" (by simp) (hset σ 0 "best.found" (by simp) hσ)
  have hinit:Invariant R valid value count (μ.setVar "cut.candidate" 0):=by
    refine ⟨hset μ 0 "cut.candidate" (by simp) hRμ,by simp,?_⟩
    simp [BestCutIndex.best,Matches,μ,ν,vars_setVar]
  obtain ⟨τ,rr,pr⟩:=hs μ hinit
  exact ⟨τ,(rf.seq (rix.seq rr)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,by simpa only [pr.2] using pr.1.2.2⟩

end Lax455465Proofs.RamBestFold

end

section

namespace Lax455465Proofs.SetDistanceData
open scoped NNRat

theorem height {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n) (S:Finset (Fin n))
    (hS:S.Nonempty) (M:ℕ) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)) (v:Fin n):
    LpInputSize.Height M (distance toSet d S hS v:ℚ):=by
  obtain ⟨j,hj,hmin⟩:=Finset.exists_mem_eq_inf' hS (fun u => if toSet then d v u else d u v)
  unfold distance
  rw [hmin]
  cases toSet <;> exact hd _ _

end Lax455465Proofs.SetDistanceData

end

section

namespace Lax455465Proofs.RamThresholdMask
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRational RamBooleanArithmetic
open scoped NNRat

def chosen (reversed:Bool) (a threshold:ℚ≥0):Bool:=
  decide (if reversed then (threshold:ℚ)≤ a else (a:ℚ)≤ threshold)
def Context {n:ℕ} (potential:Fin n→ ℚ≥0) (threshold:ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ Stored "cut.threshold" threshold σ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn potential)) "cut.potential" σ

theorem emit_spec (B:ℕ) (b:Bool) (h1:1< B):
    Spec B (fun σ => σ.vars "cmp.le"=if b then 1 else 0) emit
      (fun _ τ => FractionOutput (bit b:ℚ) τ) 6:=by
  cases b <;> intro σ hσ <;> (first
                              | (expose_names;
                                  (refine
                                      let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit false)) τ) σ;
                                      let c1:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                      let c2:Nat:=Env.vars c1 "cmp.le";
                                      let c3:Env:=Env.setVar c1 "rat.n" c2;
                                      let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat));
                                      let c5:Nat→ Nat→ Nat:=Nat.add;
                                      let c6:Nat→ Nat:=c5 ((1:Nat));
                                      let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat))));
                                      let c8:Nat:=c6 (Expr.size (Expr.var "cmp.le"));
                                      let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat))));
                                      let c10:Nat:=c5 c8 c9;
                                      let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                      @Exists.intro Env
                                        (fun (σ':Env) => And (Run B emit σ σ' ((6:Nat))) (c0 σ')) c4
                                        (@And.intro (Run B emit σ c4 ((6:Nat))) (c0 c4)
                                          (RunStep.mono B emit σ c4 (c5 c7 c10) ((6:Nat))
                                            (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                              (Com.seq (Com.assign "rat.n" (Expr.var "cmp.le")) c11) σ c1 c4 c7 c10
                                              (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                ((0:Nat))
                                                (RunStep.eval_lit B ((0:Nat)) σ
                                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                              (RunStep.seq B (Com.assign "rat.n" (Expr.var "cmp.le")) c11 c1 c3 c4 c8 c9
                                                (RunStep.assign B c1 "rat.n" (Expr.var "cmp.le") c2 (RunStep.eval_var B c1 "cmp.le" ?_))
                                                (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat)))
                                                  ((1:Nat))
                                                  (RunStep.eval_lit B ((1:Nat)) c3 h1))))
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                              | (expose_names;
                                  (refine
                                      let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit true)) τ) σ;
                                      let c1:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                      let c2:Nat:=Env.vars c1 "cmp.le";
                                      let c3:Env:=Env.setVar c1 "rat.n" c2;
                                      let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat));
                                      let c5:Nat→ Nat→ Nat:=Nat.add;
                                      let c6:Nat→ Nat:=c5 ((1:Nat));
                                      let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat))));
                                      let c8:Nat:=c6 (Expr.size (Expr.var "cmp.le"));
                                      let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat))));
                                      let c10:Nat:=c5 c8 c9;
                                      let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                      @Exists.intro Env
                                        (fun (σ':Env) => And (Run B emit σ σ' ((6:Nat))) (c0 σ')) c4
                                        (@And.intro (Run B emit σ c4 ((6:Nat))) (c0 c4)
                                          (RunStep.mono B emit σ c4 (c5 c7 c10) ((6:Nat))
                                            (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                              (Com.seq (Com.assign "rat.n" (Expr.var "cmp.le")) c11) σ c1 c4 c7 c10
                                              (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                ((0:Nat))
                                                (RunStep.eval_lit B ((0:Nat)) σ
                                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                              (RunStep.seq B (Com.assign "rat.n" (Expr.var "cmp.le")) c11 c1 c3 c4 c8 c9
                                                (RunStep.assign B c1 "rat.n" (Expr.var "cmp.le") c2 (RunStep.eval_var B c1 "cmp.le" ?_))
                                                (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat)))
                                                  ((1:Nat))
                                                  (RunStep.eval_lit B ((1:Nat)) c3 h1))))
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                             )
  all_goals simp_all [FractionOutput,fractionValue,bit] <;> omega

theorem compare_spec (B M:ℕ) (reversed:Bool) (a threshold:ℚ≥0) (hB:2*M^2+3< B)
    (han:a.num≤ M) (had:a.den≤ M) (htn:threshold.num≤ M) (htd:threshold.den≤ M):
    Spec B (fun σ => Stored "cut.value" a σ∧ Stored "cut.threshold" threshold σ) (compare reversed)
      (fun _ τ => τ.vars "cmp.le"=if chosen reversed a threshold then 1 else 0) 64:=by
  cases reversed
  · simpa only [compare,Bool.false_eq_true,if_false,chosen,decide_eq_true_eq] using
      RamScalarComparison.command_spec B M a threshold "cut.value" "cut.threshold" hB han had htn htd (by decide) (by decide) (by decide)
  · intro σ hσ
    obtain ⟨τ,rr,pr⟩:=RamScalarComparison.command_spec B M threshold a "cut.threshold" "cut.value" hB htn htd han had
      (by decide) (by decide) (by decide) σ ⟨hσ.2,hσ.1⟩
    exact ⟨τ,rr,by simpa only [chosen,if_true,decide_eq_true_eq] using pr⟩

theorem entry_spec (B M:ℕ) {n:ℕ} (reversed:Bool) (potential:Fin n→ ℚ≥0) (threshold:ℚ≥0)
    (v:Fin n) (hB:2*M^2+3< B) (hindex:2*n+2< B)
    (hpn:∀ v, (potential v).num≤ M) (hpd:∀ v, (potential v).den≤ M)
    (htn:threshold.num≤ M) (htd:threshold.den≤ M):
    Spec B (fun σ => Context potential threshold σ∧ σ.vars "cut.i"=v.val) (entry reversed)
      (fun _ τ => Context potential threshold τ∧ FractionOutput (bit (chosen reversed (potential v) threshold):ℚ) τ) 88:=by
  have hMB:M< B:=by nlinarith
  rintro σ ⟨hσ,hidx⟩
  have hi:v.val<(List.ofFn potential).length:=by simpa only [List.length_ofFn] using v.isLt
  have he:(List.ofFn potential)[v.val]=potential v:=by simp
  obtain ⟨ν,rr,pr⟩:=RamArrayScalar.command_spec B "cut.potential" "cut.i" "cut.value" (List.ofFn potential) v.val hi
    (by nlinarith) (by omega) (by rw [he]; exact (hpn v).trans_lt hMB) (by rw [he]; exact (hpd v).trans_lt hMB)
    (by decide) (by decide) σ ⟨hσ.2.2,hidx⟩
  obtain ⟨μ,rc,pc⟩:=compare_spec B M reversed (potential v) threshold hB (hpn v) (hpd v) htn htd ν
    ⟨by simpa only [he] using pr,
      RamRoundingConstants.storedFrame rr hσ.2.1 (by decide) (by decide)⟩
  obtain ⟨τ,re,pe⟩:=emit_spec B (chosen reversed (potential v) threshold) (by nlinarith) μ pc
  have run:=rr.seq (rc.seq re)
  refine ⟨τ,run,?_,pe⟩
  exact ⟨(run.frame_var _ (by cases reversed <;> decide)).trans hσ.1,
    RamRoundingConstants.storedFrame run hσ.2.1 (by cases reversed <;> decide) (by cases reversed <;> decide),
    by simpa only [Prefix,run.frame_arr "cut.potential" (by cases reversed <;> decide)] using hσ.2.2⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (reversed:Bool) (potential:Fin n→ ℚ≥0) (threshold:ℚ≥0)
    (hB:2*M^2+3< B) (hindex:2*n+2< B)
    (hpn:∀ v, (potential v).num≤ M) (hpd:∀ v, (potential v).den≤ M)
    (htn:threshold.num≤ M) (htd:threshold.den≤ M):
    Spec B (fun σ => Context potential threshold σ∧ 2*n<(σ.arrs "cut.flags").length) (command reversed)
      (fun _ τ => Context potential threshold τ∧ Prefix (RamUnsignedBuffer.encode
        (MaskedMassData.flags (fun v => chosen reversed (potential v) threshold))) "cut.flags" τ) (110*n+8):=by
  let qs:=MaskedMassData.flags (fun v => chosen reversed (potential v) threshold)
  have hlen:qs.length=n:=List.length_ofFn
  have hv:∀ i, ∀ hi:i< qs.length,qs[i]=bit (chosen reversed (potential ⟨i,by simpa only [hlen] using hi⟩) threshold):=by
    intro i hi; simp [qs,MaskedMassData.flags,bit]
  have hwords:∀ i, ∀ hi:i< qs.length,qs[i].num< B∧ qs[i].den< B:=by
    intro i hi; rw [hv i hi]
    cases chosen reversed (potential _) threshold <;> simp [bit] <;> omega
  have body:∀ i, ∀ hi:i< qs.length,
      Spec B (fun σ => Context potential threshold σ∧ σ.vars "cut.i"=i) (entry reversed)
        (fun _ τ => Context potential threshold τ∧ FractionOutput (qs[i]:ℚ) τ) 88:=by
    intro i hi
    simpa only [hv i hi] using entry_spec B M reversed potential threshold ⟨i,by simpa only [hlen] using hi⟩ hB hindex hpn hpd htn htd
  have hf:=RamUnsignedVector.command_spec B 88 (Context potential threshold) "cut.i" "metric.n" "cut.flags" "cut.pos" qs []
    (entry reversed) (by nlinarith) (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2) (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using h)
    body (by cases reversed <;> decide) (by cases reversed <;> decide) (by cases reversed <;> decide)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "cut.threshold.n" (by decide),rr.frame_var "cut.threshold.d" (by decide),
        rr.frame_arr "cut.potential" (by decide)] using h)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν:=σ.setVar "cut.pos" 0
  have rz:Run B (.assign "cut.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by nlinarith))
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨by simpa only [Context,Stored,Prefix,ν,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using hσ,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rz.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamThresholdMask

end

section

namespace Lax455465Proofs.ThresholdCutData
open Lax455465.RationalEncoding
open scoped NNRat

def potential {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):Fin n→ ℚ:=
  fun v => if reversed then -(values v:ℚ) else (values v:ℚ)
def shore {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (threshold:ℚ≥0):Finset (Fin n):=
  Finset.univ.filter fun v => RamThresholdMask.chosen reversed (values v) threshold

def candidates {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):List (Finset (Fin n)):=
  (List.finRange n).map fun v => shore reversed values (values v)

theorem mask_eq {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (threshold:ℚ≥0):
    MaskedMassData.flags (fun v => RamThresholdMask.chosen reversed (values v) threshold)=
      CutScoreData.vertexFlags (shore reversed values threshold):=by
  unfold CutScoreData.vertexFlags
  congr 1
  funext v
  simp [shore,ResidualData.mask]

theorem candidates_eq {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):
    candidates reversed values=CutSweeps.candidates (potential reversed values):=by
  apply List.map_congr_left
  intro v hv
  ext u
  cases reversed <;> simp [shore,potential,RamThresholdMask.chosen]

@[simp] theorem length_candidates {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):
    (candidates reversed values).length=n:=by simp [candidates]

def candidate {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ):Finset (Fin n):=
  (candidates reversed values).getD i ∅

theorem at_eq {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ) (hi:i< n):
    candidate reversed values i=shore reversed values (values ⟨i,hi⟩):=by
  rw [candidate,List.getD_eq_get (candidates reversed values) ∅ (⟨i,by simpa only [length_candidates] using hi⟩:Fin (candidates reversed values).length)]
  simp [candidates]

def valid {n:ℕ} (I:RationalInstance n) (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ):Prop:=
  CutSweeps.admissibleQ I (candidate reversed values i)
instance {n:ℕ} (I:RationalInstance n) (reversed:Bool) (values:Fin n→ ℚ≥0):DecidablePred (valid I reversed values):=
  fun i => inferInstanceAs (Decidable (CutSweeps.admissibleQ I (candidate reversed values i)))
def score {n:ℕ} (I:RationalInstance n) (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ):ℚ≥0:=
  CutScoreData.ratio I (candidate reversed values i)

end Lax455465Proofs.ThresholdCutData

end

section

namespace Lax455465Proofs.LargePotentialData
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def exponent (n w:ℕ):ℕ:=2*w*(n+1)+n+1

theorem bounds {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty) (w:ℕ)
    (hw:∀ v,Height (2^w) (I.weight v:ℚ)) (hd:∀ u v,Height (2^w) (d u v:ℚ)):
    Bounds I d Tin Tout hin hout (2^(exponent n w)):=by
  have hdom:2*w≤ exponent n w:=by dsimp [exponent]; nlinarith
  have hpow:2^w≤2^(exponent n w):=Nat.pow_le_pow_right (by decide) (by omega)
  have hp (toSet:Bool) (S:Finset (Fin n)) (hS:S.Nonempty):
      ∀ q∈products I toSet d S hS,Height (2^(2*w)) (q:ℚ):=by
    intro q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hq
    have hi':i< n:=by simpa [products,RamProductSum.products] using hi
    change Height (2^(2*w)) ((RamProductSum.products (List.ofFn I.weight) (vector toSet d S hS))[i]:ℚ)
    erw [RamProductSum.value_at (List.ofFn I.weight) (vector toSet d S hS) (by simp [vector]) i (by simpa using hi')]
    simp only [vector,List.getElem_ofFn,NNRat.coe_mul]
    have hh:=height_mul (hw ⟨i,hi'⟩) (SetDistanceData.height toSet d S hS (2^w) hd ⟨i,hi'⟩)
    simpa only [←Nat.pow_add,two_mul] using hh
  have hprod (toSet:Bool) (S:Finset (Fin n)) (hS:S.Nonempty):
      ∀ q∈products I toSet d S hS,Height (2^(exponent n w)) (q:ℚ):=
    fun q hq => height_mono (hp toSet S hS q hq) (Nat.pow_le_pow_right (by decide) hdom)
  have hprefix (toSet:Bool) (S:Finset (Fin n)) (hS:S.Nonempty) (i:ℕ):
      Height (2^(exponent n w)) ((((products I toSet d S hS).take i).sum:ℚ≥0):ℚ):=by
    have hh:=RationalSumHeight.prefix_dyadic_height (products I toSet d S hS) (2*w)
      (fun q hq => RamRegionContext.num_bound (hp toSet S hS q hq))
      (fun q hq => RamRegionContext.den_bound (hp toSet S hS q hq)) i
    simpa only [products,RamProductSum.products,List.length_ofFn,exponent] using hh
  exact ⟨fun v => height_mono (hw v) hpow,fun u v => height_mono (hd u v) hpow,
    hprod false Tout hout,hprod true Tin hin,hprefix false Tout hout,hprefix true Tin hin⟩

end Lax455465Proofs.LargePotentialData

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamSetPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat

theorem encoded_bound (B M:ℕ) (qs:List ℚ≥0) (hMB:M< B)
    (hq:∀ q∈qs,LpInputSize.Height M (q:ℚ)):∀ x∈RamUnsignedBuffer.encode qs,x< B:=by
  intro x hx
  simp only [RamUnsignedBuffer.encode,List.mem_flatMap] at hx
  obtain ⟨q,hq',hx⟩:=hx
  simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact (num_bound (hq q hq')).trans_lt hMB
  · exact (den_bound (hq q hq')).trans_lt hMB

end Lax455465Proofs.RamSetPotential

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamLargePotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} (h:Room n σ):Room n τ:=by
  intro a ha
  rw [RamFrames.run_array_length rr]
  exact h a ha

end Lax455465Proofs.RamLargePotential

end

section

namespace Lax455465Proofs.RamScalarDifference
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar RamRegionContext
open scoped NNRat

theorem value_eq (a b:ℚ≥0):RamTruncatedSubtract.value a b=a-b:=by
  apply NNRat.coe_injective
  by_cases h:b≤ a
  · rw [NNRat.coe_sub h]
    simp only [RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_left (sub_nonneg.mpr (NNRat.coe_le_coe.mpr h))]
  · rw [tsub_eq_zero_of_le (le_of_not_ge h)]
    simp only [RamTruncatedSubtract.value,NNRat.coe_mk,NNRat.coe_zero,max_eq_right (sub_nonpos.mpr (NNRat.coe_le_coe.mpr (le_of_not_ge h)))]

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName target:String)
    (hB:2*M^2+3< B) (ha:LpInputSize.Height M (a:ℚ)) (hb:LpInputSize.Height M (b:ℚ))
    (hout:LpInputSize.Height M ((a-b:ℚ≥0):ℚ))
    (hlfresh:leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hrfresh:rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hrretain:rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (htarget:target++".n"≠"rat.d"):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ) (command leftName rightName target)
      (fun _ τ => Stored target (a-b) τ) (36*(a.den*b.den).size+170):=by
  have hMB:M< B:=by nlinarith
  have hop:=RamTruncatedSubtract.command_spec B M a b hB (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb)
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamScalarBinary.command_spec B M (36*(a.den*b.den).size+142) a b leftName rightName
    RamTruncatedSubtract.command ((a-b:ℚ≥0):ℚ) hB (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb)
    hlfresh hrfresh hrretain (by simpa only [value_eq] using hop) σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B target (a-b) ((num_bound hout).trans_lt hMB) ((den_bound hout).trans_lt hMB) htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarDifference

end

section

namespace Lax455465Proofs.CutScoreHeight
open Lax455465.RationalEncoding LpInputSize CutScoreData
open scoped NNRat

def sumExponent (n w:ℕ):ℕ:=w*(n*n+1)+n*n+1
def exponent (n w:ℕ):ℕ:=3*sumExponent n w

theorem bounds {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (w:ℕ)
    (hw:∀ v,Height (2^w) (I.weight v:ℚ))
    (hc:∀ u v,Height (2^w) (I.capacity u v:ℚ)):Bounds I S (2^(exponent n w)):=by
  let V:=sumExponent n w
  let H:=exponent n w
  have hn:n≤ n*n:=by
    by_cases hz:n=0
    · simp [hz]
    · have hn1:1≤ n:=by omega
      nlinarith
  have hmV:w*(n+1)+n+1≤ V:=by
    dsimp [V,sumExponent]
    nlinarith [Nat.mul_le_mul_left w hn]
  have hwV:w≤ V:=by dsimp [V,sumExponent]; nlinarith
  have hVH:V≤ H:=by dsimp [V,H,exponent]; omega
  have widen {q:ℚ} (h:Height (2^V) q):Height (2^H) q:=height_mono h (Nat.pow_le_pow_right (by decide) hVH)
  have massPre (T:Finset (Fin n)) (i:ℕ):Height (2^V)
      ((((RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags T)).take i).sum:ℚ≥0):ℚ):=by
    have h:=MaskedMassData.prefix_height (List.ofFn I.weight) (vertexFlags T) w
      (by intro a ha; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha; exact hw v) i
    exact height_mono h (by simpa only [List.length_ofFn] using Nat.pow_le_pow_right (by decide:1≤2) hmV)
  have capPre (i:ℕ):Height (2^V)
      ((((RamMaskedSum.coefficients (MetricMatrix.values I.capacity) (MetricMatrix.values (arcFlags S))).take i).sum:ℚ≥0):ℚ):=by
    simpa only [MetricMatrix.length_values,V,sumExponent] using MaskedMassData.prefix_height (MetricMatrix.values I.capacity)
      (MetricMatrix.values (arcFlags S)) w
      (by intro a ha; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha; exact hc _ _) i
  have hmass (T:Finset (Fin n)):Height (2^V) (mass I T:ℚ):=by
    simpa only [List.take_length,mass] using massPre T (RamMaskedSum.coefficients (List.ofFn I.weight) (vertexFlags T)).length
  have hcap:Height (2^V) (capacity I S:ℚ):=by
    simpa only [List.take_length,capacity] using capPre (RamMaskedSum.coefficients (MetricMatrix.values I.capacity) (MetricMatrix.values (arcFlags S))).length
  have hother:Height (2^V) (otherMass I S:ℚ):=by rw [otherMass_eq]; exact hmass _
  have htotal:Height (2^V) (RamRoundingInit.total I.weight:ℚ):=by
    have h:=RationalSumHeight.prefix_dyadic_height (List.ofFn I.weight) w
      (by intro a ha; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha; simpa only [NNRat.natAbs_num_coe] using (hw v).1)
      (by intro a ha; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha; simpa only [NNRat.den_coe] using (hw v).2) n
    have htake:(List.ofFn I.weight).take n=List.ofFn I.weight:=by simp
    apply height_mono (by simpa only [htake,RamRoundingInit.total] using h)
    simpa only [List.length_ofFn] using Nat.pow_le_pow_right (by decide:1≤2) hmV
  have hd:Height (2^(2*V)) (demand I S:ℚ):=by
    have hh:=height_mul (hmass S) hother
    simpa only [demand,NNRat.coe_mul,←Nat.pow_add,show V+V=2*V by omega] using hh
  have hi:Height (2^(2*V)) (((demand I S)⁻¹:ℚ≥0):ℚ):=RoundingConstants.inverse_height Nat.one_le_two_pow hd
  have hratio:Height (2^H) (ratio I S:ℚ):=by
    have hh:=height_mul hcap hi
    simpa only [ratio,div_eq_mul_inv,NNRat.coe_mul,NNRat.coe_inv,←Nat.pow_add,H,exponent,V,show sumExponent n w+2*sumExponent n w=3*sumExponent n w by omega] using hh
  have widen2 {q:ℚ} (h:Height (2^(2*V)) q):Height (2^H) q:=
    height_mono h (Nat.pow_le_pow_right (by decide) (by dsimp [H,exponent,V]; omega))
  exact ⟨fun v => height_mono (hw v) (Nat.pow_le_pow_right (by decide) (hwV.trans hVH)),
    fun u v => height_mono (hc u v) (Nat.pow_le_pow_right (by decide) (hwV.trans hVH)),
    fun i => widen (massPre S i),fun i => widen (capPre i),widen htotal,widen (hmass S),widen hother,
    widen2 hd,widen2 hi,widen hcap,hratio⟩

end Lax455465Proofs.CutScoreHeight

end

section

namespace Lax455465Proofs.RamCutMeasures
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding CutScoreData MetricMatrix
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData:Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ
  maskData:Prefix (RamUnsignedBuffer.encode (vertexFlags S)) "cut.flags" σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (hM:1≤ M)
    (hb:CutScoreHeight.Bounds I S M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B):
    Spec B (fun σ => Input I S σ∧ 2*(n*n)<(σ.arrs "cut.crossing").length) command
      (fun _ τ => Input I S τ∧ Stored "cut.capacity" (capacity I S) τ∧ Stored "cut.mass" (mass I S) τ)
      ((36*(M^2).size+234)*(n*n)+(36*(M^2).size+152)*n+52):=by
  have hMB:M< B:=by nlinarith
  let ws:=List.ofFn I.weight
  let vs:=vertexFlags S
  let cs:=values I.capacity
  let es:=values (arcFlags S)
  have hws:ws.length=n:=List.length_ofFn
  have hvs:vs.length=n:=List.length_ofFn
  have hcs:cs.length=n*n:=length_values _
  have hes:es.length=n*n:=length_values _
  have hwn:∀ q∈ws,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact num_bound (hb.weightsBound v)
  have hwd:∀ q∈ws,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact den_bound (hb.weightsBound v)
  have hcn:∀ q∈cs,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact num_bound (hb.capacityBound _ _)
  have hcd:∀ q∈cs,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact den_bound (hb.capacityBound _ _)
  have hvn:∀ q∈vs,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈S <;> simp [vertexFlags,MaskedMassData.flags,ResidualData.mask,hv] <;> omega
  have hvd:∀ q∈vs,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈S <;> simp [vertexFlags,MaskedMassData.flags,ResidualData.mask,hv] <;> omega
  have hen:∀ q∈es,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [arcFlags,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some true) (ResidualData.mask S _) (ResidualData.mask S _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hed:∀ q∈es,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [arcFlags,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some true) (ResidualData.mask S _) (ResidualData.mask S _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamArcMask.command_spec B (some true) "cut.flags" "cut.crossing" (ResidualData.mask S)
    (by decide) (by nlinarith) (by omega) (by omega) hindex hvertex σ
    ⟨⟨hσ.nValue,hσ.n2Value,hσ.maskData⟩,hroom⟩
  let σ2:=σ1.setVar "sum.count" (n*n)
  have r2:Run B (.assign "sum.count" (.var "metric.n2")) σ1 σ2 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨p1.1.2.1.symm,p1.1.2.1 ▸ (by omega:n*n< B)⟩)
  have r12:=r1.seq r2
  obtain ⟨σ3,r3,p3⟩:=RamMaskedSum.command_spec B M "flow.capacities" "cut.crossing" cs es
    (by rw [hes,hcs]) hB (by rwa [hcs]) hcn hcd hen hed
    (fun i => num_bound (hb.capacityPrefix i)) (fun i => den_bound (hb.capacityPrefix i)) σ2
    ⟨by simp [σ2,hcs],by simpa only [cs,Prefix,r12.frame_arr "flow.capacities" (by decide)] using hσ.capacityData,
      by simpa only [es,arcFlags,Prefix,σ2,arrs_setVar] using p1.2⟩
  obtain ⟨σ4,r4,p4⟩:=save_spec B "cut.capacity" (capacity I S)
    ((num_bound hb.cutCapacityBound).trans_lt hMB) ((den_bound hb.cutCapacityBound).trans_lt hMB) (by decide) σ3 p3.2
  have rbefore:=r1.seq (r2.seq (r3.seq r4))
  have hn:σ4.vars "metric.n"=n:=(rbefore.frame_var _ (by decide)).trans hσ.nValue
  let σ5:=σ4.setVar "sum.count" n
  have r5:Run B (.assign "sum.count" (.var "metric.n")) σ4 σ5 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n< B)⟩)
  have rprior:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  obtain ⟨σ6,r6,p6⟩:=RamMaskedSum.command_spec B M "flow.weights" "cut.flags" ws vs
    (by rw [hvs,hws]) hB (by rwa [hws]) hwn hwd hvn hvd
    (fun i => num_bound (hb.massPrefix i)) (fun i => den_bound (hb.massPrefix i)) σ5
    ⟨by simp [σ5,hws],by simpa only [ws,Prefix,rprior.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      by simpa only [vs,Prefix,rprior.frame_arr "cut.flags" (by decide)] using hσ.maskData⟩
  obtain ⟨τ,r7,p7⟩:=save_spec B "cut.mass" (mass I S)
    ((num_bound hb.massBound).trans_lt hMB) ((den_bound hb.massBound).trans_lt hMB) (by decide) σ6 p6.2
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨τ,rr.mono (by simp only [hws,hcs]; nlinarith),?_,?_,p7⟩
  · exact ⟨(rr.frame_var _ (by decide)).trans hσ.nValue,(rr.frame_var _ (by decide)).trans hσ.n2Value,
      RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide),
      by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using hσ.capacityData,
      by simpa only [Prefix,rr.frame_arr "cut.flags" (by decide)] using hσ.maskData⟩
  · exact RamRoundingConstants.storedFrame (r5.seq (r6.seq r7)) p4 (by decide) (by decide)

end Lax455465Proofs.RamCutMeasures

end

section

namespace Lax455465Proofs.RamCutRatio
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (σ:Env):Prop where
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  capacityData:Stored "cut.capacity" (capacity I S) σ
  massData:Stored "cut.mass" (mass I S) σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (hM:1≤ M)
    (hb:CutScoreHeight.Bounds I S M) (hB:2*M^2+3< B):
    Spec B (Input I S) command (fun _ τ => Input I S τ∧ Stored "cut.other" (otherMass I S) τ∧
      Stored "cut.demand" (demand I S) τ∧ Stored "cut.ratio" (ratio I S) τ∧
      τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0) (144*(M^2).size+416):=by
  have hsize {a b:ℚ≥0} (ha:LpInputSize.Height M (a:ℚ)) (hb:LpInputSize.Height M (b:ℚ)):
      (a.den*b.den).size≤(M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound ha) (den_bound hb)])
  have hnumsize:(demand I S).num.size≤(M^2).size:=Nat.size_le_size (by nlinarith [num_bound hb.demandBound])
  have h2:2< B:=by nlinarith
  rintro σ hσ
  obtain ⟨σ1,r1,p1⟩:=RamScalarDifference.command_spec B M (RamRoundingInit.total I.weight) (mass I S)
    "round.total" "cut.mass" "cut.other" hB hb.totalBound hb.massBound hb.otherBound
    (by decide) (by decide) (by decide) (by decide) σ ⟨hσ.totalData,hσ.massData⟩
  obtain ⟨σ2,r2,p2⟩:=RamScalarProduct.command_spec B M (mass I S) (otherMass I S)
    "cut.mass" "cut.other" "cut.demand" hB (num_bound hb.massBound) (den_bound hb.massBound)
    (num_bound hb.otherBound) (den_bound hb.otherBound) (by decide) (by decide) (by decide) (by decide) σ1
    ⟨RamRoundingConstants.storedFrame r1 hσ.massData (by decide) (by decide),p1⟩
  obtain ⟨σ3,r3,p3⟩:=RamScalarReciprocal.command_spec B M (demand I S) "cut.demand" "cut.inverseDemand" hM (by nlinarith) hb.demandBound
    (by decide) (by decide) σ2 p2
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩:=RamScalarProduct.command_spec B M (capacity I S) (demand I S)⁻¹
    "cut.capacity" "cut.inverseDemand" "cut.ratio" hB (num_bound hb.cutCapacityBound) (den_bound hb.cutCapacityBound)
    (num_bound hb.inverseBound) (den_bound hb.inverseBound) (by decide) (by decide) (by decide) (by decide) σ3
    ⟨RamRoundingConstants.storedFrame r123 hσ.capacityData (by decide) (by decide),p3⟩
  have hd:σ4.vars "cut.demand.n"=(demand I S).num:=
    ((r3.seq r4).frame_var _ (by decide)).trans p2.1
  have hdB:σ4.vars "cut.demand.n"< B:=by rw [hd]; exact (num_bound hb.demandBound).trans_lt (by nlinarith)
  have hv:∃ τ,Run B valid σ4 τ 6∧ τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0:=by
    by_cases hz:(demand I S).num=0
    · have hc:(Cond.eq (.var "cut.demand.n") (.lit 0)).evalB B σ4=some true:=by
        rw [evalB_condEq (evalB_var hdB) (evalB_lit (by omega)),hd,hz]
        rfl
      have rr:Run B (.assign "cut.valid" (.lit 0)) σ4 (σ4.setVar "cut.valid" 0) 2:=Run.assign (evalB_lit (by omega))
      refine ⟨σ4.setVar "cut.valid" 0,Run.ite_true (d:=.assign "cut.valid" (.lit 1)) hc rr,?_⟩
      simp only [vars_setVar,if_true,admissible_iff,hz,lt_self_iff_false,if_false]
    · have hc:(Cond.eq (.var "cut.demand.n") (.lit 0)).evalB B σ4=some false:=by
        rw [evalB_condEq (evalB_var hdB) (evalB_lit (by omega)),hd]
        simp [hz]
      have rr:Run B (.assign "cut.valid" (.lit 1)) σ4 (σ4.setVar "cut.valid" 1) 2:=Run.assign (evalB_lit (by omega))
      refine ⟨σ4.setVar "cut.valid" 1,Run.ite_false (c:=.assign "cut.valid" (.lit 0)) hc rr,?_⟩
      simp only [vars_setVar,if_true,admissible_iff,Nat.pos_of_ne_zero hz,if_true]
  obtain ⟨τ,r5,p5⟩:=hv
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono ?_,?_,?_,?_,?_,p5⟩
  · have hs1:=hsize hb.totalBound hb.massBound
    have hs2:=hsize hb.massBound hb.otherBound
    have hs4:=hsize hb.cutCapacityBound hb.inverseBound
    nlinarith
  · exact ⟨RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide),
      RamRoundingConstants.storedFrame rr hσ.capacityData (by decide) (by decide),
      RamRoundingConstants.storedFrame rr hσ.massData (by decide) (by decide)⟩
  · exact RamRoundingConstants.storedFrame (r2.seq (r3.seq (r4.seq r5))) p1 (by decide) (by decide)
  · exact RamRoundingConstants.storedFrame (r3.seq (r4.seq r5)) p2 (by decide) (by decide)
  · have hp:=RamRoundingConstants.storedFrame r5 p4 (by decide) (by decide)
    simpa only [ratio,div_eq_mul_inv] using hp

end Lax455465Proofs.RamCutRatio

end

section

namespace Lax455465Proofs.RamCutScore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (hM:1≤ M)
    (hb:CutScoreHeight.Bounds I S M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B):
    Spec B (fun σ => RamCutMeasures.Input I S σ∧ 2*(n*n)<(σ.arrs "cut.crossing").length) command
      (fun _ τ => RamCutMeasures.Input I S τ∧ Stored "cut.ratio" (ratio I S) τ∧
        τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0) (cost n M):=by
  rintro σ hσ
  obtain ⟨ν,rm,pm⟩:=RamCutMeasures.command_spec B M I S hM hb hB hindex hvertex σ hσ
  obtain ⟨τ,rr,pr⟩:=RamCutRatio.command_spec B M I S hM hb hB ν
    ⟨pm.1.totalData,pm.2.1,pm.2.2⟩
  refine ⟨τ,(rm.seq rr).mono (by dsimp [cost]; omega),?_,pr.2.2.2.1,pr.2.2.2.2⟩
  exact ⟨(rr.frame_var _ (by decide)).trans pm.1.nValue,(rr.frame_var _ (by decide)).trans pm.1.n2Value,
    pr.1.totalData,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using pm.1.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using pm.1.capacityData,
    by simpa only [Prefix,rr.frame_arr "cut.flags" (by decide)] using pm.1.maskData⟩

end Lax455465Proofs.RamCutScore

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamThresholdCandidate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  count:σ.vars "cut.count"=n
  reversedValue:σ.vars "cut.reversed"=(if reversed then 1 else 0)
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  potentialData:Prefix (RamUnsignedBuffer.encode (List.ofFn potential)) "cut.potential" σ
  maskRoom:2*n<(σ.arrs "cut.flags").length
  crossingRoom:2*(n*n)<(σ.arrs "cut.crossing").length

def names:List String:= ["metric.n","metric.n2","cut.count","cut.reversed","round.total.n","round.total.d"]
def arrays:List String:= ["flow.weights","flow.capacities","cut.potential"]

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {potential:Fin n→ ℚ≥0} {reversed:Bool} (h:Input I potential reversed σ)
    (hx:∀ x∈names,x∉cmd.wvars) (ha:∀ a∈arrays,a∉cmd.warrs):Input I potential reversed τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.count,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.reversedValue,
    RamRoundingConstants.storedFrame rr h.totalData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "cut.potential" (ha _ (by simp [arrays]))] using h.potentialData,
    by rw [RamFrames.run_array_length rr "cut.flags"]; exact h.maskRoom,
    by rw [RamFrames.run_array_length rr "cut.crossing"]; exact h.crossingRoom⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool)
    (i:ℕ) (hi:i< n) (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hp:∀ v,LpInputSize.Height M (potential v:ℚ))
    (hb:CutScoreHeight.Bounds I (ThresholdCutData.candidate reversed potential i) M):
    Spec B (fun σ => Input I potential reversed σ∧ σ.vars "cut.candidate"=i) command
      (fun _ τ => Input I potential reversed τ∧
        RamBestUpdate.Current (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) i τ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed potential i))) "cut.flags" τ)
      (cost n M):=by
  have hMB:M< B:=by nlinarith
  let v:Fin n:= ⟨i,hi⟩
  let S:=ThresholdCutData.candidate reversed potential i
  have hS:S=ThresholdCutData.shore reversed potential (potential v):=ThresholdCutData.at_eq reversed potential i hi
  have hmask:MaskedMassData.flags (fun u => RamThresholdMask.chosen reversed (potential u) (potential v))=CutScoreData.vertexFlags S:=by
    rw [hS]
    exact ThresholdCutData.mask_eq reversed potential (potential v)
  rintro σ ⟨hσ,hidx⟩
  have hi':i<(List.ofFn potential).length:=by simpa only [List.length_ofFn] using hi
  have he:(List.ofFn potential)[i]=potential v:=by simp [v]
  obtain ⟨σ1,r1,p1⟩:=RamArrayScalar.command_spec B "cut.potential" "cut.candidate" "cut.threshold" (List.ofFn potential) i hi'
    (by nlinarith) (by omega) (by rw [he]; exact (num_bound (hp v)).trans_lt hMB)
    (by rw [he]; exact (den_bound (hp v)).trans_lt hMB) (by decide) (by decide) σ ⟨hσ.potentialData,hidx⟩
  have h1:=Input.frame r1 hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have maskSpec:∃ σ2,Run B mask σ1 σ2 (110*n+12)∧ Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ2:=by
    have applyMask (b:Bool):∃ σ2,Run B (RamThresholdMask.command b) σ1 σ2 (110*n+8)∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun u => RamThresholdMask.chosen b (potential u) (potential v)))) "cut.flags" σ2:=by
      obtain ⟨σ2,rr,pr⟩:=RamThresholdMask.command_spec B M b potential (potential v) hB hvertex
        (fun u => num_bound (hp u)) (fun u => den_bound (hp u)) (num_bound (hp v)) (den_bound (hp v)) σ1
        ⟨⟨h1.nValue,by simpa only [he] using p1,h1.potentialData⟩,h1.maskRoom⟩
      exact ⟨σ2,rr,pr.2⟩
    cases hr:reversed
    · have hv:σ1.vars "cut.reversed"=0:=by simpa only [hr,Bool.false_eq_true,if_false] using h1.reversedValue
      have hc:(Cond.eq (.var "cut.reversed") (.lit 1)).evalB B σ1=some false:=by
        rw [evalB_condEq (evalB_var (hv ▸ (by omega:0< B))) (evalB_lit (by nlinarith)),hv]
        rfl
      obtain ⟨σ2,rr,pr⟩:=applyMask false
      exact ⟨σ2,(Run.ite_false (c:=RamThresholdMask.command true) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),
        by rw [←hmask,hr]; exact pr⟩
    · have hv:σ1.vars "cut.reversed"=1:=by simpa only [hr,if_true] using h1.reversedValue
      have hc:(Cond.eq (.var "cut.reversed") (.lit 1)).evalB B σ1=some true:=by
        rw [evalB_condEq (evalB_var (hv ▸ (by nlinarith:1< B))) (evalB_lit (by nlinarith)),hv]
        rfl
      obtain ⟨σ2,rr,pr⟩:=applyMask true
      exact ⟨σ2,(Run.ite_true (d:=RamThresholdMask.command false) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),
        by rw [←hmask,hr]; exact pr⟩
  obtain ⟨σ2,r2,p2⟩:=maskSpec
  have h2:=Input.frame r2 h1 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  obtain ⟨τ,r3,p3⟩:=RamCutScore.command_spec B M I S hM hb hB hindex hvertex σ2
    ⟨⟨h2.nValue,h2.n2Value,h2.totalData,h2.weightsData,h2.capacityData,p2⟩,h2.crossingRoom⟩
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),Input.frame rr hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide),
    ⟨(rr.frame_var _ (by decide)).trans hidx,p3.2.2,p3.2.1⟩,p3.1.maskData⟩

end Lax455465Proofs.RamThresholdCandidate

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamPotentialSweep
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding RamThresholdCandidate
open scoped NNRat

def Selected {n:ℕ} (reversed:Bool) (potential:Fin n→ ℚ≥0):Option ℕ→ Env→ Prop
  | none,_ => True
  | some j,σ => Prefix (RamUnsignedBuffer.encode
      (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed potential j))) "cut.flags" σ

theorem input_set {n:ℕ} {I:RationalInstance n} {potential:Fin n→ ℚ≥0} {reversed:Bool}
    (σ:Env) (k:ℕ) (name:String) (hn:name∈["cut.candidate","best.found","best.index"])
    (h:Input I potential reversed σ):Input I potential reversed (σ.setVar name k):=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals
    exact ⟨by simpa using h.nValue,by simpa using h.n2Value,by simpa using h.count,
      by simpa using h.reversedValue,by simpa [Stored] using h.totalData,
      h.weightsData,h.capacityData,h.potentialData,h.maskRoom,h.crossingRoom⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool)
    (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hp:∀ v,LpInputSize.Height M (potential v:ℚ))
    (hb:∀ i< n,CutScoreHeight.Bounds I (ThresholdCutData.candidate reversed potential i) M):
    Spec B (Input I potential reversed) command
      (fun _ τ => Input I potential reversed τ∧
        RamBestUpdate.Matches (ThresholdCutData.score I reversed potential)
          (BestCutIndex.best (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) n) τ∧
        Selected reversed potential
          (BestCutIndex.best (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) n) τ)
      (cost n M):=by
  let valid:=ThresholdCutData.valid I reversed potential
  let value:=ThresholdCutData.score I reversed potential
  let best:=BestCutIndex.best valid value n
  have producer (i:ℕ) (hi:i< n):=RamThresholdCandidate.command_spec B M I potential reversed i hi hM hB hindex hvertex hp (hb i hi)
  have scan:=RamBestFold.command_spec B M (RamThresholdCandidate.cost n M) (Input I potential reversed)
    valid value n RamThresholdCandidate.command hB (by omega)
    (fun i hi => (hb i hi).ratioBound) (fun _ h => h.count) input_set
    (fun i hi σ h => by obtain ⟨τ,rr,pr⟩:=producer i hi σ h; exact ⟨τ,rr,pr.1,pr.2.1⟩)
    (by dsimp [RamBestFold.bestNames]; decide)
    (fun rr h => Input.frame rr h (by dsimp [RamThresholdCandidate.names]; decide) (by dsimp [RamThresholdCandidate.arrays]; decide))
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩:=scan σ hσ
  change Input I potential reversed ν∧ RamBestUpdate.Matches value best ν at ps
  have h1:1< B:=by nlinarith
  have hf:∃ τ,Run B finish ν τ (RamThresholdCandidate.cost n M+6)∧
      Input I potential reversed τ∧ RamBestUpdate.Matches value best τ∧ Selected reversed potential best τ:=by
    cases he:best with
    | none =>
      have hv:ν.vars "best.found"=0:=by simpa only [he,RamBestUpdate.Matches] using ps.2
      have hc:(Cond.eq (.var "best.found") (.lit 1)).evalB B ν=some false:=by
        rw [evalB_condEq (evalB_var (hv ▸ (by omega:0< B))) (evalB_lit h1),hv]
        rfl
      exact ⟨ν,(Run.ite_false (c:=restore) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),
        ps.1,hv,trivial⟩
    | some j =>
      have hj:j< n:=(BestCutIndex.best_sound valid value n j he).1
      have hm:RamBestUpdate.Matches value (some j) ν:=by simpa only [he] using ps.2
      have hc:(Cond.eq (.var "best.found") (.lit 1)).evalB B ν=some true:=by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit h1),hm.1]
        rfl
      let μ:=ν.setVar "cut.candidate" j
      have ri:Run B (.assign "cut.candidate" (.var "best.index")) ν μ 2:=
        Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.1.symm,by rw [hm.2.1]; omega⟩)
      obtain ⟨τ,rp,pp⟩:=producer j hj μ ⟨input_set ν j "cut.candidate" (by simp) ps.1,by simp [μ]⟩
      have rr:=Run.ite_true (d:=.skip) hc (ri.seq rp)
      exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pp.1,
        RamBestFold.Matches.frame rr hm (by dsimp [RamBestFold.bestNames]; decide),pp.2.2⟩
  obtain ⟨τ,rf,pf⟩:=hf
  exact ⟨τ,(rs.seq rf).mono (by dsimp [cost]; omega),pf⟩

theorem selected_le {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool)
    (S:Finset (Fin n)) (hS:S∈CutSweeps.candidates (ThresholdCutData.potential reversed potential))
    (hvalid:CutSweeps.admissibleQ I S):
    ∃ j,BestCutIndex.best (ThresholdCutData.valid I reversed potential)
        (ThresholdCutData.score I reversed potential) n=some j∧ j< n∧
      CutSweeps.admissibleQ I (ThresholdCutData.candidate reversed potential j)∧
      CutSweeps.ratioQ I (ThresholdCutData.candidate reversed potential j)≤ CutSweeps.ratioQ I S:=by
  rw [←ThresholdCutData.candidates_eq] at hS
  obtain ⟨k,hk,hget⟩:=List.mem_iff_getElem.mp hS
  have hkn:k< n:=by simpa only [ThresholdCutData.length_candidates] using hk
  have hcan:ThresholdCutData.candidate reversed potential k=S:=by
    rw [ThresholdCutData.candidate,List.getD_eq_get _ ∅ ⟨k,hk⟩]
    exact hget
  have hv:ThresholdCutData.valid I reversed potential k:=by
    simpa only [ThresholdCutData.valid,hcan] using hvalid
  cases he:BestCutIndex.best (ThresholdCutData.valid I reversed potential)
      (ThresholdCutData.score I reversed potential) n with
  | none => exact False.elim ((BestCutIndex.best_none _ _ _).mp he k hkn hv)
  | some j =>
    have hs:=BestCutIndex.best_sound _ _ n j he
    refine ⟨j,rfl,hs.1,hs.2,?_⟩
    have hm:=BestCutIndex.best_minimal _ _ n j k he hkn hv
    have hq:=NNRat.coe_le_coe.mpr hm
    simpa only [ThresholdCutData.score,CutScoreData.coe_ratio,hcan] using hq

end Lax455465Proofs.RamPotentialSweep

end

section

namespace Lax455465Proofs.PotentialCandidates
open PotentialLayers

theorem layer_shore {n:ℕ} (a:Fin n→ ℚ) (i:Fin n):
    CutLayers.shore (build a) i=Finset.univ.filter (fun v => a v≤(values a)[i.val]'(by simpa [values_length] using i.isLt)):=by
  let xs:=values a
  have hi:i.val< xs.length:=by simpa only [xs,values_length] using i.isLt
  ext v
  simp only [CutLayers.shore,Finset.mem_filter,Finset.mem_univ,true_and]
  have hv:xs.idxOf (a v)< xs.length:=List.idxOf_lt_length_of_mem (value_mem a v)
  have sorted:xs.SortedLE:=List.sortedLE_mergeSort
  change xs.idxOf (a v)≤ i.val↔ a v≤ xs[i.val]
  constructor
  · intro h
    have hm:=sorted.monotone_get (show (⟨xs.idxOf (a v),hv⟩:Fin xs.length)≤⟨i.val,hi⟩ from h)
    simpa only [List.get_eq_getElem,List.getElem_idxOf] using hm
  · intro h
    by_contra hn
    have hlt:i.val< xs.idxOf (a v):=by omega
    have hm:=sorted.monotone_get (show (⟨i.val,hi⟩:Fin xs.length)≤⟨xs.idxOf (a v),hv⟩ from hlt.le)
    have hrev:xs[i.val]≤ a v:=by simpa only [List.get_eq_getElem,List.getElem_idxOf] using hm
    have he:xs[i.val]=a v:=le_antisymm hrev h
    have hnot:=List.not_of_lt_findIdx (p:=fun q:ℚ => q==a v) (xs:=xs) hlt
    simp [he] at hnot

theorem layer_mem {n:ℕ} (a:Fin n→ ℚ) (i:Fin n):
    CutLayers.shore (build a) i∈CutSweeps.candidates a:=by
  have hi:i.val<(values a).length:=by simpa only [values_length] using i.isLt
  have hm:(values a)[i.val]∈values a:=List.getElem_mem hi
  obtain ⟨v,hv⟩:=List.mem_ofFn.mp (List.mem_mergeSort.mp hm)
  rw [layer_shore,←hv]
  exact List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩

theorem round_mem {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (a:Fin n→ ℚ)
    (S:Finset (Fin n)) (hS:PotentialLayers.round I a=some S):S∈CutSweeps.candidates a:=by
  have hm:=(CutSweeps.choose_sound I (ThresholdRounding.layerCandidates (build a)) S hS).1
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hm
  exact layer_mem a i

end Lax455465Proofs.PotentialCandidates

end

section

namespace Lax455465Proofs.RamRegionBegin
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionInvariant
open Lax455465.RationalEncoding
open scoped NNRat

structure Source {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  supportValue:σ.vars "round.support"=p
  stepsValue:σ.vars "round.steps"=RegionBudget.steps p
  seedData:Stored "round.seed" seed σ
  betaData:Stored "round.slope" beta σ
  deltaData:Stored "round.delta" delta σ
  unitData:Stored "round.gridStep" (delta/(RegionBudget.steps p:ℚ≥0)) σ
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  lengthData:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ

def setup:Com:=.seq (.assign "history.pos" (.lit 0))
  (.seq (.assign "region.phase" (.lit 0)) (.assign "loop.limit" (.add (.var "round.support") (.lit 1))))
def command:Com:=.seq RamLargeThreshold.command (.seq RamActiveInit.command setup)

def sourceNames:List String:= ["metric.n","metric.n2","round.support","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d","round.delta.n","round.delta.d",
  "round.gridStep.n","round.gridStep.d","round.total.n","round.total.d"]

theorem Source.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {length:MetricMatrix.Matrix n} {seed beta delta:ℚ≥0} {p:ℕ}
    (h:Source I length seed beta delta p σ)
    (hx:∀ x∈sourceNames,x∉cmd.wvars) (ha:∀ a∈RamRegionInvariant.arrays,a∉cmd.warrs):
    Source I length seed beta delta p τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.supportValue,
    (rr.frame_var _ (hx _ (by simp [sourceNames]))).trans h.stepsValue,
    RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    RamRoundingConstants.storedFrame rr h.totalData (hx _ (by simp [sourceNames])) (hx _ (by simp [sourceNames])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [RamRegionInvariant.arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [RamRegionInvariant.arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [RamRegionInvariant.arrays]))] using h.lengthData⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ) (hM:3≤ M) (hB:2*M^2+3< B)
    (ht:LpInputSize.Height M (RamRoundingInit.total I.weight:ℚ)) (hindex:2*n+2< B) (hcount:p+1< B):
    Spec B (fun σ => Source I length seed beta delta p σ∧ Room n p σ) command
      (fun _ τ => Fixed I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p τ∧
        Room n p τ∧ τ.vars "loop.limit"=p+1∧ RamRegionState.View I length seed beta (RamRegionBoundedLoop.initial n) τ)
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+112):=by
  have h2:2< B:=by nlinarith
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamLargeThreshold.command_spec B M (RamRoundingInit.total I.weight) hM hB ht σ hσ.totalData
  have hs1:=Source.frame r1 hσ (by dsimp [sourceNames]; decide) (by dsimp [RamRegionInvariant.arrays]; decide)
  have room1:=Room.frame r1 hroom
  have hf1:Fixed I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p σ1:=
    ⟨hs1.nValue,hs1.n2Value,hs1.supportValue,hs1.stepsValue,hs1.seedData,hs1.betaData,hs1.deltaData,hs1.unitData,
      p1.2,hs1.weightsData,hs1.capacityData,hs1.lengthData⟩
  obtain ⟨σ2,r2,p2⟩:=RamActiveInit.command_spec B n h2 hindex σ1
    ⟨hf1.nValue,room1 "region.active" (2*n) (by simp [extents])⟩
  have hf2:=Fixed.frame r2 hf1 (by dsimp [names]; decide) (by dsimp [RamRegionInvariant.arrays]; decide)
  have room2:=Room.frame r2 room1
  let σ3:=σ2.setVar "history.pos" 0
  let σ4:=σ3.setVar "region.phase" 0
  let τ:=σ4.setVar "loop.limit" (p+1)
  have r3:Run B (.assign "history.pos" (.lit 0)) σ2 σ3 2:=Run.assign (evalB_lit (by omega))
  have r4:Run B (.assign "region.phase" (.lit 0)) σ3 σ4 2:=Run.assign (evalB_lit (by omega))
  have hsupp:σ4.vars "round.support"=p:=((r3.seq r4).frame_var _ (by decide)).trans hf2.supportValue
  have r5:Run B (.assign "loop.limit" (.add (.var "round.support") (.lit 1))) σ4 τ 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hsupp.symm,hsupp ▸ (by omega:p< B)⟩)
      (evalB_lit (by omega)) hcount)
  have rsetup:=r3.seq (r4.seq r5)
  have rr:=r1.seq (r2.seq rsetup)
  refine ⟨τ,rr.mono (by omega),Fixed.frame rsetup hf2 (by dsimp [names]; decide)
    (by dsimp [RamRegionInvariant.arrays]; decide),Room.frame rsetup room2,by simp [τ],?_⟩
  change RamRegionInvariant.Dynamic Finset.univ [] τ
  refine ⟨by simp [τ,σ4],?_,?_,by simp [τ,σ4,σ3]⟩
  · have hm:ResidualData.mask (Finset.univ:Finset (Fin n))=(fun _:Fin n => true):=by funext v; simp [ResidualData.mask]
    simpa only [hm,Prefix,rsetup.frame_arr "region.active" (by decide)] using p2.2
  · simp [RamRegionRecord.words,Prefix]

end Lax455465Proofs.RamRegionBegin

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionWhole
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionInvariant RegionRuntimeState RamRegionState
open Lax455465.RationalEncoding
open scoped NNRat

theorem combine {B KI KS:ℕ} {σ ν τ:Env}
    (hi:Run B RamRegionBegin.command σ ν KI) (hs:Run B RamRegionScan.command ν τ KS):
    Run B RamRegionLoop.command σ τ (KI+KS):=by
  obtain ⟨ki,hki,hbi⟩:=hi
  obtain ⟨ks,hks,hbs⟩:=hs
  cases hbi with
  | seq ht haSetup =>
    cases haSetup with
    | seq ha hsetup =>
      cases hsetup with
      | seq hpos hphaseLimit =>
        cases hphaseLimit with
        | seq hphase hlimit =>
          exact ⟨_,by omega,.seq ht (.seq ha (.seq hpos (.seq hphase (.seq hlimit hbs))))⟩

set_option maxHeartbeats 0 in
theorem command_spec (B M H:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ)
    (hM:3≤ M) (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hlen:4*p+4< B) (hthreshold:LpInputSize.Height (2^H) (RamLargeThreshold.threshold (RamRoundingInit.total I.weight):ℚ))
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ active:Finset (Fin n), ∀ root:Fin n, ∀ i,
      ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hsupport:(RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤ p)
    (htotal:LpInputSize.Height M (RamRoundingInit.total I.weight:ℚ)):
    Spec B (fun σ => RamRegionBegin.Source I length seed beta delta p σ∧ Room n p σ) RamRegionLoop.command
      (fun _ τ => Fixed I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p τ∧ Room n p τ∧
        View I length seed beta ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
          (RamRegionBoundedLoop.initial n)) τ∧
        RegionRuntimeCorrespondence.ValidFinal I length seed delta p
          ((advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
            (RamRegionBoundedLoop.initial n)))
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+112+RamRegionBoundedLoop.cost n p M H):=by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rb,pb⟩:=RamRegionBegin.command_spec B M I length seed beta delta p hM hB htotal hvertex (by omega) σ ⟨hσ,hroom⟩
  obtain ⟨τ,rs,ps⟩:=RamRegionBoundedLoop.command_spec B M H I length seed beta delta
    (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p (by omega) hk hB hquery hindex hvertex hradius hlen
    hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hseed hdelta hp hdiag htri hcost hsupport ν pb
  exact ⟨τ,combine rb rs,ps.1,ps.2.1,ps.2.2,
    RegionRuntimeCorrespondence.final_correct I length seed beta delta p hbeta hseed hdelta hp hdiag htri hcost hsupport⟩

end Lax455465Proofs.RamRegionWhole

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding RegionRuntimeState
open scoped BigOperators NNRat

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K) {n:ℕ} (h:Room n σ):Room n τ:=
  ⟨h.potential.frame rr,by rw [RamFrames.run_array_length rr]; exact h.mask,
    by rw [RamFrames.run_array_length rr]; exact h.crossing⟩

end Lax455465Proofs.RamRegionCut

end

section

namespace Lax455465Proofs.RegionRuntimeBounds
open Lax455465.RationalEncoding RegionRuntimeState RamRegionRecord LpInputSize
open scoped NNRat

def HistoryHeight {n:ℕ} (M:ℕ) (s:State n):Prop:= ∀ e∈s.history,Height M (e.radius:ℚ)

theorem advance_height {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p M:ℕ) (s:State n)
    (hM:1≤ M) (hk:RegionBudget.steps p≤ M)
    (hd:∀ u v,Height M (d u v:ℚ)) (hdelta:Height M (delta:ℚ))
    (hunit:Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hh:HistoryHeight (M*M) s):HistoryHeight (M*M) (advance I d seed beta delta threshold p s):=by
  cases hs:s.status with
  | large e => simpa only [advance,hs] using hh
  | exhausted => simpa only [advance,hs] using hh
  | failed => simpa only [advance,hs] using hh
  | running =>
    cases hroot:RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => simpa only [advance,hs,hroot,HistoryHeight] using hh
    | some root =>
      cases hr:radius I d seed beta delta p s.active root with
      | none => simpa only [advance,hs,hroot,hr,HistoryHeight] using hh
      | some r =>
        have hrmem:=List.mem_of_find?_eq_some hr
        have hrheight:=RadiusData.height (d root) (fun v => d v root) (RegionBudget.steps p) M delta
          hM hk hunit hdelta (hd root) (fun v => hd v root) r hrmem
        simp only [advance,hs,hroot,hr]
        split_ifs
        · exact hh
        · intro e he
          simp only [List.mem_append,List.mem_singleton] at he
          rcases he with he | rfl
          · exact hh e he
          · exact hrheight

theorem iterate_height {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p M iterations:ℕ)
    (hM:1≤ M) (hk:RegionBudget.steps p≤ M)
    (hd:∀ u v,Height M (d u v:ℚ)) (hdelta:Height M (delta:ℚ))
    (hunit:Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ)):
    HistoryHeight (M*M) ((advance I d seed beta delta threshold p)^[iterations] (RamRegionBoundedLoop.initial n)):=by
  induction iterations with
  | zero => simp [HistoryHeight,RamRegionBoundedLoop.initial]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact advance_height I d seed beta delta threshold p M _ hM hk hd hdelta hunit ih

end Lax455465Proofs.RegionRuntimeBounds

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamPositiveRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RegionRuntimeState
open Lax455465.RationalEncoding
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B M H N:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ)
    (hM:3≤ M) (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hlen:4*p+4< B) (hthreshold:LpInputSize.Height (2^H) (RamLargeThreshold.threshold (RamRoundingInit.total I.weight):ℚ))
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ active:Finset (Fin n), ∀ root:Fin n, ∀ i,
      ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hsupport:(RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤ p)
    (htotal:LpInputSize.Height M (RamRoundingInit.total I.weight:ℚ))
    (hN:1≤ N) (hMN:M*M≤ N) (hpN:2*p≤ N) (hNB:2*N^2+3 < B)
    (hlargeBounds:∀ Tin Tout:Finset (Fin n),∀ hin:Tin.Nonempty,∀ hout:Tout.Nonempty,
      LargePotentialData.Bounds I length Tin Tout hin hout N)
    (hcuts:∀ S,CutScoreHeight.Bounds I S N)
    (htotalPos:0 < LargeBallRounding.total I)
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational length))
    (hseedEq:(seed:ℚ)=RegionRounding.metricCost I (MetricMatrix.rational length)/p)
    (hdeltaEq:(delta:ℚ)=RegionRounding.radiusBudget I):
    Spec B (fun σ => RamRegionBegin.Source I length seed beta delta p σ∧ Room n p σ∧ RamRegionCut.Room n σ)
      command (fun _ τ => RamRegionCut.Output I length p τ)
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+112+
        RamRegionBoundedLoop.cost n p M H+RamRegionCut.cost n p N):=by
  rintro σ ⟨hσ,hregionRoom,hcutRoom⟩
  obtain ⟨ν,rr,pr⟩:=RamRegionWhole.command_spec B M H I length seed beta delta p hM hk hB hquery hindex hvertex
    hradius hlen hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hseed hdelta hp hdiag htri hcost hsupport htotal σ ⟨hσ,hregionRoom⟩
  let s:=(advance I length seed beta delta (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p)^[p+1]
    (RamRegionBoundedLoop.initial n)
  have hh:=RegionRuntimeBounds.iterate_height I length seed beta delta
    (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p M (p+1) (by omega) hk hl hd hu
  have hMN':M≤ N:=by nlinarith
  have htotalν:=RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide)
  obtain ⟨τ,rc,pc⟩:=RamRegionCut.command_spec B N I length seed beta delta
    (RamLargeThreshold.threshold (RamRoundingInit.total I.weight)) p s hN hpN hNB (by nlinarith) hlen hindex hvertex
    (fun u v => LpInputSize.height_mono (hl u v) hMN')
    (fun e he => LpInputSize.height_mono (hh e he) hMN)
    hlargeBounds hcuts htotalPos hp hdiag hsep htri hseedEq hdeltaEq pr.2.2.2 ν
    ⟨pr.1,pr.2.2.1,htotalν,hcutRoom.frame rr⟩
  exact ⟨τ,rr.seq rc,pc⟩

end Lax455465Proofs.RamPositiveRounding

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamPositivePair
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP FlowLpIndices
open scoped NNRat

def predicate {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (i:ℕ):Bool:=
  if hi:i< n*n then
    let uv:=(edgeIndex n).symm ⟨i,hi⟩
    decide (0<(I.weight uv.1).num∧ 0<(I.weight uv.2).num∧ 0<(d uv.1 uv.2).num)
  else false

def Context {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧ σ.vars "find.count"=n*n∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {d:MetricMatrix.Matrix n} (h:Context I d σ)
    (hx:∀ x∈["metric.n","metric.n2","find.count"],x∉cmd.wvars)
    (ha:∀ a∈["flow.weights","metric.old"],a∉cmd.warrs):Context I d τ:=by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "metric.n2" (hx _ (by simp)),
    rr.frame_var "find.count" (hx _ (by simp)),rr.frame_arr "flow.weights" (ha _ (by simp)),
    rr.frame_arr "metric.old" (ha _ (by simp))] using h

theorem indices_spec (B:ℕ) {n:ℕ} (u v:Fin n) (hn:n< B) (hn2:n*n< B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "find.i"=(edgeIndex n (u,v)).val) indices
      (fun _ τ => τ.vars "pair.u"=u.val∧ τ.vars "pair.v"=v.val) 10:=by
  have hidx:(edgeIndex n (u,v)).val< B:=(edgeIndex n (u,v)).isLt.trans hn2
  have hu:u.val< B:=u.isLt.trans hn
  have hv:v.val< B:=v.isLt.trans hn
  have hprod:u.val*n< B:=by rw [edge_value] at hidx; omega
  have hdiv:=edge_div u v
  have hmod:=edge_mod u v
  rw [Nat.mod_def] at hmod
  rintro σ ⟨hnσ,hiσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "pair.u") (@Fin.val n u)) (@Eq Nat (Env.vars τ "pair.v") (@Fin.val n v))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "find.i") (Env.vars σ "metric.n"); let c2:Env:=Env.setVar σ "pair.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "find.i"; let c5:Nat:=c3 "pair.u"; let c6:Nat:=c3 "metric.n"; let c7:Nat:=Nat.mul c5 c6; let c8:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c4 c7; let c9:Env:=Env.setVar c2 "pair.v" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.div (Expr.var "find.i") (Expr.var "metric.n"))); let c13:Expr:=Expr.sub (Expr.var "find.i") (Expr.mul (Expr.var "pair.u") (Expr.var "metric.n")); let c14:Nat:=c11 (Expr.size c13); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B indices σ σ' ((10:Nat))) (c0 σ')) c9 (@And.intro (Run B indices σ c9 ((10:Nat))) (c0 c9) (RunStep.mono B indices σ c9 (c10 c12 c14) ((10:Nat)) (RunStep.seq B (Com.assign "pair.u" (Expr.div (Expr.var "find.i") (Expr.var "metric.n"))) (Com.assign "pair.v" c13) σ c2 c9 c12 c14 (RunStep.assign B σ "pair.u" (Expr.div (Expr.var "find.i") (Expr.var "metric.n")) c1 (RunStep.eval_div B σ (Expr.var "find.i") (Expr.var "metric.n") (Env.vars σ "find.i") (Env.vars σ "metric.n") (RunStep.eval_var B σ "find.i" (?nAX_g7217_0_0_0)) (RunStep.eval_var B σ "metric.n" (?nAX_g7217_0_0_1)) ?_)) (RunStep.assign B c2 "pair.v" c13 c8 (RunStep.eval_sub B c2 (Expr.var "find.i") (Expr.mul (Expr.var "pair.u") (Expr.var "metric.n")) c4 c7 (RunStep.eval_var B c2 "find.i" (?nAX_g7217_0_0_2)) (RunStep.eval_mul B c2 (Expr.var "pair.u") (Expr.var "metric.n") c5 c6 (RunStep.eval_var B c2 "pair.u" ?_) (RunStep.eval_var B c2 "metric.n" (?nAX_g7217_0_0_3)) ?_) (?nAX_g7217_0_0_4)))) (?nAX_g7217_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7217_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7217_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7217_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7217_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7217_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7217_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [edge_value]

theorem flags_spec (B a b c:ℕ) (h1:1< B) (ha:a< B) (hb:b< B) (hc:c< B):
    Spec B (fun σ => σ.vars "pair.left.n"=a∧ σ.vars "pair.right.n"=b∧ σ.vars "pair.distance.n"=c) flags
      (fun _ τ => τ.vars "find.ok"=(if 0< a∧ 0< b∧ 0< c then 1 else 0)) 14:=by
  rintro σ ⟨haσ,hbσ,hcσ⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "pair.left.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Prop:=Nat.lt ((0:Nat)); let c3:Prop:=c2 a; let c4:Prop:=c2 b; let c5:Prop:=c2 c; let c6:Prop:=And c4 c5; let c7:Nat:= @ite Nat (And c3 c6) (@instDecidableAnd c3 c6 (Nat.decLt ((0:Nat)) a) (@instDecidableAnd c4 c5 (Nat.decLt ((0:Nat)) b) (Nat.decLt ((0:Nat)) c))) ((1:Nat)) ((0:Nat)); let c8:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "find.ok") c7) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B flags σ σ' ((14:Nat))) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:Env:=Env.setVar σ "find.ok" ((0:Nat)); let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.var "pair.left.n") (Expr.lit ((0:Nat))); let c15:Nat→ Nat:=c12 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c17:Com:=Com.assign "find.ok" (Expr.lit ((0:Nat))); let c18:Cond:=Cond.eq (Expr.var "pair.right.n") (Expr.lit ((0:Nat))); let c19:Cond:=Cond.eq (Expr.var "pair.distance.n") (Expr.lit ((0:Nat))); let c20:Com:=Com.assign "find.ok" (Expr.lit ((1:Nat))); let c21:Com:=Com.ite c19 c17 c20; let c22:Com:=Com.ite c18 c17 c21; let c23:Prop:= @Eq Nat (Env.vars σ "pair.right.n") ((0:Nat)); let c24:Prop:=Not c23; let c25:Nat→ Nat:=c12 (c13 (Cond.size c18)); let c26:Nat:=c25 c16; let c27:Prop:= @Eq Nat (Env.vars σ "pair.distance.n") ((0:Nat)); let c28:Prop:=Not c27; let c29:Nat→ Nat:=c12 (c13 (Cond.size c19)); let c30:Nat:=c29 c16; let c31:Nat:=c25 c30; let c32:Env:=Env.setVar σ "find.ok" ((1:Nat)); let c33:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c34:Nat:=c29 c33; let c35:Nat:=c25 c34; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c10) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c9 c11 (@And.intro (Run B flags σ c11 ((14:Nat))) (c8 c11) (RunStep.mono B flags σ c11 (c15 c16) ((14:Nat)) (RunStep.ite_true B c14 c17 c22 σ c11 c16 (RunStep.cond_eq_true B σ (Expr.var "pair.left.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.left.n") ((0:Nat)) (RunStep.eval_var B σ "pair.left.n" (?nAX_g7218_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_1)) hcase) (RunStep.assign B σ "find.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_2)))) (?nAX_g7218_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c23 c24 (fun (x:Or c23 c24) => c10) (Classical.em c23) (fun (hcase_1:c23) => @Exists.intro Env c9 c11 (@And.intro (Run B flags σ c11 ((14:Nat))) (c8 c11) (RunStep.mono B flags σ c11 (c15 c26) ((14:Nat)) (RunStep.ite_false B c14 c17 c22 σ c11 c26 (RunStep.cond_eq_false B σ (Expr.var "pair.left.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.left.n") ((0:Nat)) (RunStep.eval_var B σ "pair.left.n" (?nAX_g7218_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_5)) hcase) (RunStep.ite_true B c18 c17 c21 σ c11 c16 (RunStep.cond_eq_true B σ (Expr.var "pair.right.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.right.n") ((0:Nat)) (RunStep.eval_var B σ "pair.right.n" (?nAX_g7218_0_0_6)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_7)) hcase_1) (RunStep.assign B σ "find.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_8))))) (?nAX_g7218_0_0_9)) ?_)) fun (hcase_1:c24) => @Or.casesOn c27 c28 (fun (x:Or c27 c28) => c10) (Classical.em c27) (fun (hcase_2:c27) => @Exists.intro Env c9 c11 (@And.intro (Run B flags σ c11 ((14:Nat))) (c8 c11) (RunStep.mono B flags σ c11 (c15 c31) ((14:Nat)) (RunStep.ite_false B c14 c17 c22 σ c11 c31 (RunStep.cond_eq_false B σ (Expr.var "pair.left.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.left.n") ((0:Nat)) (RunStep.eval_var B σ "pair.left.n" (?nAX_g7218_0_0_10)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_11)) hcase) (RunStep.ite_false B c18 c17 c21 σ c11 c30 (RunStep.cond_eq_false B σ (Expr.var "pair.right.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.right.n") ((0:Nat)) (RunStep.eval_var B σ "pair.right.n" (?nAX_g7218_0_0_12)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_13)) hcase_1) (RunStep.ite_true B c19 c17 c20 σ c11 c16 (RunStep.cond_eq_true B σ (Expr.var "pair.distance.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.distance.n") ((0:Nat)) (RunStep.eval_var B σ "pair.distance.n" (?nAX_g7218_0_0_14)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_15)) hcase_2) (RunStep.assign B σ "find.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_16)))))) (?nAX_g7218_0_0_17)) ?_)) fun (hcase_2:c28) => @Exists.intro Env c9 c32 (@And.intro (Run B flags σ c32 ((14:Nat))) (c8 c32) (RunStep.mono B flags σ c32 (c15 c35) ((14:Nat)) (RunStep.ite_false B c14 c17 c22 σ c32 c35 (RunStep.cond_eq_false B σ (Expr.var "pair.left.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.left.n") ((0:Nat)) (RunStep.eval_var B σ "pair.left.n" (?nAX_g7218_0_0_18)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_19)) hcase) (RunStep.ite_false B c18 c17 c21 σ c32 c34 (RunStep.cond_eq_false B σ (Expr.var "pair.right.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.right.n") ((0:Nat)) (RunStep.eval_var B σ "pair.right.n" (?nAX_g7218_0_0_20)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_21)) hcase_1) (RunStep.ite_false B c19 c17 c20 σ c32 c33 (RunStep.cond_eq_false B σ (Expr.var "pair.distance.n") (Expr.lit ((0:Nat))) (Env.vars σ "pair.distance.n") ((0:Nat)) (RunStep.eval_var B σ "pair.distance.n" (?nAX_g7218_0_0_22)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7218_0_0_23)) hcase_2) (RunStep.assign B σ "find.ok" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1))))) (?nAX_g7218_0_0_24)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7218_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7218_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem test_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (i:ℕ) (hi:i< n*n) (hMB:M< B) (h2:2< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hw:∀ v,LpInputSize.Height M (I.weight v:ℚ)) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)):
    Spec B (fun σ => Context I d σ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context I d τ∧ τ.vars "find.ok"=(if predicate I d i then 1 else 0)) 78:=by
  let uv:=(edgeIndex n).symm ⟨i,hi⟩
  have he:(edgeIndex n uv).val=i:=congrArg Fin.val ((edgeIndex n).apply_symm_apply ⟨i,hi⟩)
  have hdist:(MetricMatrix.values d)[i]'(by simpa only [MetricMatrix.length_values] using hi)=d uv.1 uv.2:=by
    simpa only [he] using MetricMatrix.value_at d uv.1 uv.2
  rintro σ ⟨hσ,hidx⟩
  obtain ⟨σ1,r1,p1⟩:=indices_spec B uv.1 uv.2 (by omega) (by omega) σ ⟨hσ.1,by simpa only [he] using hidx⟩
  have h1:=frame r1 hσ (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩:=RamArrayScalar.command_spec B "flow.weights" "pair.u" "pair.left" (List.ofFn I.weight) uv.1.val
    (by simpa using uv.1.isLt) h2 (by have:=uv.1.isLt; omega)
    (by simpa only [List.getElem_ofFn] using (num_bound (hw uv.1)).trans_lt hMB)
    (by simpa only [List.getElem_ofFn] using (den_bound (hw uv.1)).trans_lt hMB) (by decide) (by decide) σ1 ⟨h1.2.2.2.1,p1.1⟩
  have h2σ:=frame r2 h1 (by decide) (by decide)
  have hv:σ2.vars "pair.v"=uv.2.val:=(r2.frame_var _ (by decide)).trans p1.2
  obtain ⟨σ3,r3,p3⟩:=RamArrayScalar.command_spec B "flow.weights" "pair.v" "pair.right" (List.ofFn I.weight) uv.2.val
    (by simpa using uv.2.isLt) h2 (by have:=uv.2.isLt; omega)
    (by simpa only [List.getElem_ofFn] using (num_bound (hw uv.2)).trans_lt hMB)
    (by simpa only [List.getElem_ofFn] using (den_bound (hw uv.2)).trans_lt hMB) (by decide) (by decide) σ2 ⟨h2σ.2.2.2.1,hv⟩
  have h3:=frame r3 h2σ (by decide) (by decide)
  have hidx3:σ3.vars "find.i"=i:=((r1.seq (r2.seq r3)).frame_var _ (by decide)).trans hidx
  obtain ⟨σ4,r4,p4⟩:=RamArrayScalar.command_spec B "metric.old" "find.i" "pair.distance" (MetricMatrix.values d) i
    (by simpa only [MetricMatrix.length_values] using hi) h2 (by omega)
    (by rw [hdist]; exact (num_bound (hd uv.1 uv.2)).trans_lt hMB)
    (by rw [hdist]; exact (den_bound (hd uv.1 uv.2)).trans_lt hMB) (by decide) (by decide) σ3 ⟨h3.2.2.2.2,hidx3⟩
  have hleft:=RamRoundingConstants.storedFrame (r3.seq r4) p2 (by decide) (by decide)
  have hright:=RamRoundingConstants.storedFrame r4 p3 (by decide) (by decide)
  obtain ⟨τ,r5,p5⟩:=flags_spec B (I.weight uv.1).num (I.weight uv.2).num (d uv.1 uv.2).num (by omega)
    ((num_bound (hw uv.1)).trans_lt hMB) ((num_bound (hw uv.2)).trans_lt hMB)
    ((num_bound (hd uv.1 uv.2)).trans_lt hMB) σ4
    ⟨by simpa only [Stored,List.getElem_ofFn,Fin.eta,String.reduceAppend] using hleft.1,
      by simpa only [Stored,List.getElem_ofFn,Fin.eta,String.reduceAppend] using hright.1,
      by simpa only [hdist,String.reduceAppend] using p4.1⟩
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr,frame rr hσ (by decide) (by decide),by simpa only [predicate,dif_pos hi,decide_eq_true_eq,uv] using p5⟩

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (hMB:M< B) (h2:2< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hw:∀ v,LpInputSize.Height M (I.weight v:ℚ)) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
      Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ∧
      Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ) command
      (fun _ τ => Context I d τ∧ RamFind.Matches (RamFind.first (predicate I d) (n*n)) τ) (98*(n*n)+12):=by
  have hscan:=RamFind.command_spec B (n*n) 78 (Context I d) (predicate I d) test (by omega) (by omega)
    (fun _ h => h.2.2.1)
    (fun σ k name h hn => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => test_spec B M I d i hi hMB h2 hindex hvertex hw hd) (by decide)
  rintro σ ⟨hn,hn2,hwσ,hdσ⟩
  let ν:=σ.setVar "find.count" (n*n)
  have rc:Run B (.assign "find.count" (.var "metric.n2")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn2.symm,hn2 ▸ (by omega:n*n< B)⟩)
  obtain ⟨τ,rs,ps⟩:=hscan ν ⟨by simpa [ν] using hn,by simpa [ν] using hn2,by simp [ν],hwσ,hdσ⟩
  exact ⟨τ,(rc.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamPositivePair

end

section

open scoped BigOperators

namespace Lax455465Proofs.ZeroCostRounding

open Lax455465.RationalEncoding CutSweeps RationalDistances

def pairs (n:ℕ):List (Fin n × Fin n):=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u,v)

def pairTerm {n:ℕ} (I:RationalInstance n) (d:Distance n) (uv:Fin n × Fin n):ℚ:=
  (I.weight uv.1:ℚ) * I.weight uv.2 * d uv.1 uv.2

def choosePair {n:ℕ} (I:RationalInstance n) (d:Distance n):Option (Fin n × Fin n):=
  (pairs n).find? fun uv => decide (0 < pairTerm I d uv)

theorem pair_correct {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (hsep:1≤ LargeBallRounding.distanceSeparation I d):
    ∃ uv,choosePair I d=some uv∧ 0 < pairTerm I d uv:=by
  have hex:∃ u v,0 < pairTerm I d (u,v):=by
    by_contra hn
    push Not at hn
    have hnonpos:LargeBallRounding.distanceSeparation I d≤ 0:=
      Finset.sum_nonpos fun u _ => Finset.sum_nonpos fun v _ => hn u v
    linarith
  cases hs:choosePair I d with
  | none =>
    obtain ⟨u,v,hpos⟩:=hex
    have hmem:(u,v)∈ pairs n:=by
      unfold pairs
      apply List.mem_flatMap.mpr
      exact ⟨u,List.mem_finRange u,List.mem_map.mpr ⟨v,List.mem_finRange v,rfl⟩⟩
    have hfail:=List.find?_eq_none.mp hs (u,v) hmem
    simp only [decide_eq_true_eq] at hfail
    exact False.elim (hfail hpos)
  | some uv =>
    exact ⟨uv,rfl,by simpa only [decide_eq_true_eq] using List.find?_some hs⟩

theorem potential_separation {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (uv:Fin n × Fin n) (hd:Nonnegative d) (hdiag:∀ v,d v v=0)
    (hpair:0 < pairTerm I d uv):
    0 < PotentialLayers.separation I (d uv.1):=by
  have hterm:pairTerm I d uv =
      (I.weight uv.1:ℚ) * I.weight uv.2 * max (d uv.1 uv.2 - d uv.1 uv.1) 0:=by
    rw [hdiag,sub_zero,max_eq_left (hd _ _)]
    rfl
  have hnn:∀ u v,0≤ (I.weight u:ℚ) * I.weight v * max (d uv.1 v - d uv.1 u) 0:=
    fun u v => mul_nonneg (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (le_max_right _ _)
  have hinner:=Finset.single_le_sum (fun v _ => hnn uv.1 v) (Finset.mem_univ uv.2)
  have houter:(∑ v, (I.weight uv.1:ℚ) * I.weight v * max (d uv.1 v - d uv.1 uv.1) 0)≤
      PotentialLayers.separation I (d uv.1):=
    Finset.single_le_sum (fun u _ => Finset.sum_nonneg fun v _ => hnn u v) (Finset.mem_univ uv.1)
  rw [hterm] at hpair
  exact hpair.trans_le (hinner.trans houter)

end Lax455465Proofs.ZeroCostRounding

end

section

namespace Lax455465Proofs.PositivePairData
open Lax455465.RationalEncoding DirectedFlowLP
open scoped NNRat

theorem term_pos {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (u v:Fin n):
    0< ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v)↔
      0<(I.weight u).num∧ 0<(I.weight v).num∧ 0<(d u v).num:=by
  have hmul (a b:ℚ) (ha:0≤ a) (hb:0≤ b):0< a*b↔ 0< a∧ 0< b:=by
    constructor
    · intro h; constructor <;> by_contra hn <;> push Not at hn <;> nlinarith
    · exact fun h => mul_pos h.1 h.2
  change 0<(I.weight u:ℚ)*(I.weight v:ℚ)*(d u v:ℚ)↔ _
  rw [hmul _ _ (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (NNRat.coe_nonneg _),
    hmul _ _ (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)]
  simp only [NNRat.num_pos,NNRat.coe_pos,and_assoc]

theorem predicate_at {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (u v:Fin n):
    RamPositivePair.predicate I d (edgeIndex n (u,v)).val=
      decide (0< ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v)):=by
  simp only [RamPositivePair.predicate,dif_pos (edgeIndex n (u,v)).isLt,Fin.eta,Equiv.symm_apply_apply,term_pos]

theorem first_correct {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d)):
    ∃ u v,RamFind.first (RamPositivePair.predicate I d) (n*n)=some (edgeIndex n (u,v)).val∧
      0< ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v):=by
  cases he:RamFind.first (RamPositivePair.predicate I d) (n*n) with
  | none =>
    obtain ⟨uv,huv,hpos⟩:=ZeroCostRounding.pair_correct I (MetricMatrix.rational d) hsep
    have hfail:=List.find?_eq_none.mp he (edgeIndex n uv).val (List.mem_range.mpr (edgeIndex n uv).isLt)
    rw [predicate_at I d uv.1 uv.2] at hfail
    simp [hpos] at hfail
  | some i =>
    have hi:i< n*n:=List.mem_range.mp (List.mem_of_find?_eq_some he)
    let uv:=(edgeIndex n).symm ⟨i,hi⟩
    have hidx:(edgeIndex n uv).val=i:=congrArg Fin.val ((edgeIndex n).apply_symm_apply ⟨i,hi⟩)
    have hp:=List.find?_some he
    rw [←hidx,predicate_at I d uv.1 uv.2] at hp
    exact ⟨uv.1,uv.2,by simp only [hidx],by simpa only [decide_eq_true_eq] using hp⟩

end Lax455465Proofs.PositivePairData

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamZeroCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP
open scoped BigOperators NNRat

structure Input {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  weights:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  distances:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  total:Stored "round.total" (RamRoundingInit.total I.weight) σ

def names:List String:= ["metric.n","metric.n2","round.total.n","round.total.d"]
def arrays:List String:= ["flow.weights","flow.capacities","metric.old"]
def Room (n:ℕ) (σ:Env):Prop:=
  (∀ a∈["region.out","cut.potential","cut.flags"],2*n<(σ.arrs a).length)∧
    2*(n*n)<(σ.arrs "cut.crossing").length

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {d:MetricMatrix.Matrix n} (h:Input I d σ)
    (hx:∀ x∈names,x∉cmd.wvars) (ha:∀ a∈RamZeroCut.arrays,a∉cmd.warrs):Input I d τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [RamZeroCut.arrays]))] using h.weights,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [RamZeroCut.arrays]))] using h.capacities,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [RamZeroCut.arrays]))] using h.distances,
    RamRoundingConstants.storedFrame rr h.total (hx _ (by simp [names])) (hx _ (by simp [names]))⟩

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} (h:Room n σ):Room n τ:=by
  exact ⟨fun a ha => by rw [RamFrames.run_array_length rr]; exact h.1 a ha,
    by rw [RamFrames.run_array_length rr]; exact h.2⟩

def prepareCost (n:ℕ):ℕ:=98*(n*n)+66*n+38

def cost (n M:ℕ):ℕ:=prepareCost n+RamPotentialSweep.cost n M

set_option maxHeartbeats 0 in
theorem prepare_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (hMB:M< B) (h2:2< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hw:∀ v,LpInputSize.Height M (I.weight v:ℚ)) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ))
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d)):
    Spec B (fun σ => Input I d σ∧ Room n σ) prepare
      (fun _ τ => Input I d τ∧ ∃ u v,
        0< ZeroCostRounding.pairTerm I (MetricMatrix.rational d) (u,v)∧
        τ.vars "cut.count"=n∧ τ.vars "cut.reversed"=0∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (d u))) "cut.potential" τ) (prepareCost n):=by
  obtain ⟨u,v,hfirst,hpair⟩:=PositivePairData.first_correct I d hsep
  let edge:=(edgeIndex n (u,v)).val
  have heB:edge< B:=(edgeIndex n (u,v)).isLt.trans (by omega)
  have huB:u.val< B:=u.isLt.trans (by omega)
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamPositivePair.command_spec B M I d hMB h2 hindex hvertex hw hd σ
    ⟨hσ.nValue,hσ.n2Value,hσ.weights,hσ.distances⟩
  have h1:=Input.frame r1 hσ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  have hm:RamFind.Matches (some edge) σ1:=by simpa only [hfirst,edge] using p1.2
  let σ2:=σ1.setVar "region.root" u.val
  have r2:Run B (.assign "region.root" (.div (.var "find.result") (.var "metric.n"))) σ1 σ2 4:=by
    have hdiv:edge/n=u.val:=FlowLpIndices.edge_div u v
    have hh:=evalB_bin (op:=.div)
      (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ heB⟩)
      (by rw [evalB_var_iff]; exact ⟨h1.nValue.symm,h1.nValue ▸ (by omega:n< B)⟩)
      (by change edge/n< B; rw [hdiv]; exact huB)
    simpa only [σ2,Bop.apply,hdiv,Expr.size,Nat.reduceAdd] using (Run.assign hh:Run B _ _ _ 4)
  have h2σ:=Input.frame r2 h1 (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  obtain ⟨σ3,r3,p3⟩:=RamRootDistances.command_spec B M true u d hMB (by omega) (by omega) hindex
    (fun u v => num_bound (hd u v)) (fun u v => den_bound (hd u v)) σ2
    ⟨⟨h2σ.nValue,by simp [σ2],h2σ.distances⟩,((hroom.frame (r1.seq r2)).1 _ (by simp [RamRootDistances.array]))⟩
  have h3:=Input.frame r3 h2σ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  let σ4:=σ3.setVar "copy.count" (2*n)
  have r4:Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) σ3 σ4 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit h2)
      (by rw [evalB_var_iff]; exact ⟨h3.nValue.symm,h3.nValue ▸ (by omega:n< B)⟩)
      (by dsimp [Bop.apply]; omega))
  let xs:=RamUnsignedBuffer.encode (List.ofFn (d u))
  have hxlen:xs.length=2*n:=by simp [xs]
  have hwords:∀ x∈xs,x< B:=RamSetPotential.encoded_bound B M (List.ofFn (d u)) hMB
    (by intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hd u v)
  have rr4:=r1.seq (r2.seq (r3.seq r4))
  obtain ⟨σ5,r5,p5⟩:=RamArrayCopy.command_spec B xs "region.out" "cut.potential" "copy.count" (by omega)
    (by rw [hxlen]; omega) hwords (by decide) (by decide) σ4
    ⟨by simpa only [Prefix,σ4,arrs_setVar,RamRootDistances.vector,RamRootDistances.array,if_true] using p3.2,
      by simp [σ4,hxlen],by rw [hxlen]; exact ((hroom.frame rr4).1 _ (by simp)).le⟩
  let σ6:=σ5.setVar "cut.reversed" 0
  have r6:Run B (.assign "cut.reversed" (.lit 0)) σ5 σ6 2:=Run.assign (evalB_lit (by omega))
  have h5:=Input.frame (rr4.seq r5) hσ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide)
  let τ:=σ6.setVar "cut.count" n
  have hn6:σ6.vars "metric.n"=n:=by simpa [σ6] using h5.nValue
  have r7:Run B (.assign "cut.count" (.var "metric.n")) σ6 τ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn6.symm,hn6 ▸ (by omega:n< B)⟩)
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  exact ⟨τ,rr.mono (by rw [hxlen]; dsimp [prepareCost]; omega),
    Input.frame rr hσ (by dsimp [names]; decide) (by dsimp [RamZeroCut.arrays]; decide),u,v,hpair,
    by simp [τ],by simp [τ,σ6],p5.2⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hw:∀ v,LpInputSize.Height M (I.weight v:ℚ)) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ))
    (hcuts:∀ S,CutScoreHeight.Bounds I S M) (hdiag:∀ v,d v v=0)
    (htri:∀ u v w,(d u w:ℚ)≤(d u v:ℚ)+(d v w:ℚ))
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (hzero:(∑ u,∑ v,(I.capacity u v:ℚ)*(d u v:ℚ))=0):
    Spec B (fun σ => Input I d σ∧ Room n σ) command
      (fun _ τ => ∃ S:Finset (Fin n),CutSweeps.admissibleQ I S∧ CutSweeps.ratioQ I S≤0∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n M):=by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rp,hν,u,v,hpair,hcount,hrev,hpotential⟩:=prepare_spec B M I d (by nlinarith) (by nlinarith)
    hindex hvertex hw hd hsep σ ⟨hσ,hroom⟩
  have hpositive:=ZeroCostRounding.potential_separation I (MetricMatrix.rational d) (u,v)
    (fun _ _ => NNRat.coe_nonneg _) (by intro v; simp [MetricMatrix.rational,hdiag]) hpair
  obtain ⟨S,hS,hvalid,hratio⟩:=PotentialLayers.round_spec I (MetricMatrix.rational d u) hpositive
  have hzeroRatio:CutSweeps.ratioQ I S≤0:=hratio.trans (by
    have hc:=PotentialLayers.edgeCost_le I (MetricMatrix.rational d u) (MetricMatrix.rational d)
      (fun _ _ => NNRat.coe_nonneg _) (by intro v w; have ht:=htri u v w; dsimp [MetricMatrix.rational]; linarith)
    dsimp only [MetricMatrix.rational] at hc
    rw [hzero] at hc
    exact div_nonpos_of_nonpos_of_nonneg hc hpositive.le)
  have hSmem:S∈CutSweeps.candidates (ThresholdCutData.potential false (d u)):=
    PotentialCandidates.round_mem I _ S hS
  obtain ⟨j,hj,hjn,hjvalid,hjratio⟩:=RamPotentialSweep.selected_le I (d u) false S hSmem hvalid
  obtain ⟨τ,rs,ps⟩:=RamPotentialSweep.command_spec B M I (d u) false hM hB hindex hvertex (hd u)
    (fun i hi => hcuts _) ν ⟨hν.nValue,hν.n2Value,hcount,hrev,hν.total,hν.weights,hν.capacities,hpotential,
      (hroom.frame rp).1 _ (by simp),(hroom.frame rp).2⟩
  exact ⟨τ,rp.seq rs,ThresholdCutData.candidate false (d u) j,hjvalid,hjratio.trans hzeroRatio,
    by simpa only [hj,RamPotentialSweep.Selected] using ps.2.2⟩

end Lax455465Proofs.RamZeroCut

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRoundingDispatch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

set_option maxHeartbeats 0 in

theorem command_spec (B M H N:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ)
    (hM:3≤ M) (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hlen:4*p+4< B) (hthreshold:LpInputSize.Height (2^H) (RamLargeThreshold.threshold (RamRoundingInit.total I.weight):ℚ))
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ active:Finset (Fin n), ∀ root:Fin n, ∀ i,
      ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
     (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hsupport:(RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤ p)
    (htotal:LpInputSize.Height M (RamRoundingInit.total I.weight:ℚ))
    (hN:1≤ N) (hMN:M*M≤ N) (hpN:2*p≤ N) (hNB:2*N^2+3 < B)
    (hlargeBounds:∀ Tin Tout:Finset (Fin n),∀ hin:Tin.Nonempty,∀ hout:Tout.Nonempty,
      LargePotentialData.Bounds I length Tin Tout hin hout N)
    (hcuts:∀ S,CutScoreHeight.Bounds I S N)
    (htotalPos:0 < LargeBallRounding.total I)
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational length))
    (hseedEq:(seed:ℚ)=RegionRounding.metricCost I (MetricMatrix.rational length)/p)
    (hdeltaEq:(delta:ℚ)=RegionRounding.radiusBudget I)
    (hcostHeight:LpInputSize.Height N (MetricCostData.cost I length:ℚ)):
    Spec B (fun σ => RamRegionBegin.Source I length seed beta delta p σ∧ Room n p σ∧ RamRegionCut.Room n σ∧
      Stored "round.cost" (MetricCostData.cost I length) σ)
      command (fun _ τ => RamRegionCut.Output I length p τ)
      (36*((RamRoundingInit.total I.weight).den*3).size+28*n+116+
        RamRegionBoundedLoop.cost n p M H+RamRegionCut.cost n p N+RamZeroCut.cost n N):=by
  rintro σ ⟨hσ,hregionRoom,hcutRoom,hcostσ⟩
  have hNB':N < B:=by nlinarith
  have hMN':M≤ N:=by nlinarith
  have hnσ:σ.vars "round.cost.n"=(MetricCostData.cost I length).num:=hcostσ.1
  have hnum:(MetricCostData.cost I length).num < B:=(num_bound hcostHeight).trans_lt hNB'
  by_cases hz:(MetricCostData.cost I length).num=0
  · have hcost0:MetricCostData.cost I length=0:=by
      rw [←NNRat.num_div_den (MetricCostData.cost I length),hz]
      simp
    have hW0:RegionRounding.metricCost I (MetricMatrix.rational length)=0:=by
      rw [←MetricCostData.coe_cost,hcost0]; rfl
    have hc:(Cond.eq (.var "round.cost.n") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hnσ ▸ hnum)) (evalB_lit (by omega)),hnσ,hz]
      rfl
    have hwN:∀ v,LpInputSize.Height N (I.weight v:ℚ):=by
      intro v
      exact ⟨by simpa only [NNRat.natAbs_num_coe] using (hwn v).trans hMN',
        by simpa only [NNRat.den_coe] using (hwd v).trans hMN'⟩
    have hdN:=fun u v => LpInputSize.height_mono (hl u v) hMN'
    have room0:RamZeroCut.Room n σ:=by
      refine ⟨?_,hcutRoom.crossing⟩
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hcutRoom.potential _ (by simp [RamLargePotential.scratchArrays])
      · exact hcutRoom.potential _ (by simp [RamLargePotential.scratchArrays])
      · exact hcutRoom.mask
    obtain ⟨τ,rr,S,hadm,hratio,hmask⟩:=RamZeroCut.command_spec B N I length hN hNB hindex hvertex hwN hdN hcuts
      hdiag htri hsep hW0 σ
      ⟨⟨hσ.nValue,hσ.n2Value,hσ.weightsData,hσ.capacityData,hσ.lengthData,hσ.totalData⟩,room0⟩
    refine ⟨τ,(Run.ite_true (d:=RamPositiveRounding.command) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),S,hadm,?_,hmask⟩
    simpa only [hW0,mul_zero] using hratio
  · have hWpos:0 < RegionRounding.metricCost I (MetricMatrix.rational length):=by
      rw [←MetricCostData.coe_cost]
      have hcostNe:MetricCostData.cost I length ≠ 0:=by
        intro h; apply hz; rw [h]; rfl
      exact NNRat.coe_pos.mpr (lt_of_le_of_ne zero_le (Ne.symm hcostNe))
    have hseedPos:0 < (seed:ℚ):=by rw [hseedEq]; exact div_pos hWpos (by exact_mod_cast hp)
    have hc:(Cond.eq (.var "round.cost.n") (.lit 0)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hnσ ▸ hnum)) (evalB_lit (by omega)),hnσ]
      simp [hz]
    obtain ⟨τ,rr,pr⟩:=RamPositiveRounding.command_spec B M H N I length seed beta delta p hM hk hB hquery hindex hvertex
      hradius hlen hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hseedPos hdelta hp hdiag htri hcost hsupport htotal
      hN hMN hpN hNB hlargeBounds hcuts htotalPos hsep hseedEq hdeltaEq σ ⟨hσ,hregionRoom,hcutRoom⟩
    exact ⟨τ,(Run.ite_false (c:=RamZeroCut.command) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),pr⟩

end Lax455465Proofs.RamRoundingDispatch

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamMetricRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RamRegionContext RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

set_option maxHeartbeats 0 in

theorem command_spec (B M H N:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ)
    (hM:4≤ M) (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+4< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hlen:4*p+4< B) (hthreshold:LpInputSize.Height (2^H) (RamLargeThreshold.threshold (RamRoundingInit.total I.weight):ℚ))
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ active:Finset (Fin n), ∀ root:Fin n, ∀ i,
      ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
     (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hsupport:(RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤ p)
    (htotal:LpInputSize.Height M (RamRoundingInit.total I.weight:ℚ))
    (hN:1≤ N) (hMN:M*M≤ N) (hpN:2*p≤ N) (hNB:2*N^2+3 < B)
    (hlargeBounds:∀ Tin Tout:Finset (Fin n),∀ hin:Tin.Nonempty,∀ hout:Tout.Nonempty,
      LargePotentialData.Bounds I length Tin Tout hin hout N)
    (hcuts:∀ S,CutScoreHeight.Bounds I S N)
    (htotalPos:0 < LargeBallRounding.total I)
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational length))
    (hseedEq:(seed:ℚ)=RegionRounding.metricCost I (MetricMatrix.rational length)/p)
    (hdeltaEq:(delta:ℚ)=RegionRounding.radiusBudget I)
    (hpEq:p=RamRoundingInit.support I.weight)
    (hconstants:RoundingConstantHeight.Bounds (MetricCostData.cost I length) (RamRoundingInit.total I.weight) p M)
    (hprefix:∀ i,LpInputSize.Height M (((List.ofFn I.weight).take i).sum:ℚ)):
    Spec B (fun σ => Input I length σ∧ Room n p σ∧ RamRegionCut.Room n σ)
      command (fun _ τ => RamRegionCut.Output I length p τ)
      (((36*(M^2).size+200)*(n+1)+600*(M^2).size+2000)+
        (36*((RamRoundingInit.total I.weight).den*3).size+28*n+116+
          RamRegionBoundedLoop.cost n p M H+RamRegionCut.cost n p N+RamZeroCut.cost n N)):=by
  have htotalCoe:(RamRoundingInit.total I.weight:ℚ)=LargeBallRounding.total I:=by
    simp [RamRoundingInit.total,LargeBallRounding.total,List.sum_ofFn,NNRat.cast_sum]
  have hseedVal:RoundingConstants.seed (MetricCostData.cost I length) p=seed:=by
    apply NNRat.coe_injective
    simp only [RoundingConstants.seed,NNRat.coe_div,NNRat.coe_natCast,MetricCostData.coe_cost,hseedEq]
  have hdeltaVal:RoundingConstants.delta (RamRoundingInit.total I.weight)=delta:=by
    apply NNRat.coe_injective
    rw [RoundingConstants.coe_delta,htotalCoe,hdeltaEq]
    rfl
  have hbetaVal:RoundingConstants.beta (RamRoundingInit.total I.weight) p=beta:=by
    apply NNRat.coe_injective
    rw [RoundingConstants.coe_beta,hdeltaVal,hbeta]
  have hw:∀ v,LpInputSize.Height M (I.weight v:ℚ):=by
    intro v
    exact ⟨by simpa only [NNRat.natAbs_num_coe] using hwn v,by simpa only [NNRat.den_coe] using hwd v⟩
  rintro σ ⟨hσ,hregionRoom,hcutRoom⟩
  obtain ⟨ν,rr,hin,hconst,hseedν,hdeltaν,hbetaν,hunitν⟩:=RamRoundingInit.command_spec B M I.weight
    (MetricCostData.cost I length) (by simpa only [←hpEq] using hconstants) hM hB hvertex
    (by simpa only [←hpEq] using hp) hw hprefix σ ⟨hσ.nValue,hσ.weights,hσ.costData⟩
  have hsource:RamRegionBegin.Source I length seed beta delta p ν:=by
    exact ⟨hin.nValue,(rr.frame_var _ (by decide)).trans hσ.n2Value,
      by simpa only [←hpEq] using hconst.supportValue,
      by simpa only [←hpEq] using hconst.stepsValue,
      by simpa only [←hpEq,hseedVal] using hseedν,
      by simpa only [←hpEq,hbetaVal] using hbetaν,
      by simpa only [hdeltaVal] using hdeltaν,
      by simpa only [←hpEq,RoundingConstants.gridStep,hdeltaVal] using hunitν,
      hconst.totalData,hin.weightsData,
      by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using hσ.capacities,
      by simpa only [Prefix,rr.frame_arr "metric.old" (by decide)] using hσ.distances⟩
  have hMN':M≤ N:=by nlinarith
  obtain ⟨τ,rd,pd⟩:=RamRoundingDispatch.command_spec B M H N I length seed beta delta p (by omega) hk hB hquery hindex (by omega)
    hradius hlen hthreshold hwn hwd hcn hcd hl hd hu hb hbeta hdelta hp hdiag htri hcost hsupport htotal
    hN hMN hpN hNB hlargeBounds hcuts htotalPos hsep hseedEq hdeltaEq
    (LpInputSize.height_mono hconstants.costBound hMN') ν ⟨hsource,hregionRoom.frame rr,hcutRoom.frame rr,hin.costData⟩
  exact ⟨τ,rr.seq rd,pd⟩

end Lax455465Proofs.RamMetricRounding

end

section

namespace Lax455465Proofs.RegionIterationHeight
open LpInputSize Lax455465.RationalEncoding
open scoped NNRat

def exponent (n w:ℕ):ℕ:=RegionQueryHeight.exponent n (2*w)

theorem bounds {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (k w:ℕ)
    (hw:∀ v,Height (2^w) (I.weight v:ℚ))
    (hc:∀ u v,Height (2^w) (I.capacity u v:ℚ))
    (hl:∀ u v,Height (2^w) (length u v:ℚ))
    (hs:Height (2^w) (seed:ℚ)) (hb:Height (2^w) (beta:ℚ))
    (hd:Height (2^w) (delta:ℚ)) (hu:Height (2^w) ((delta/(k:ℚ≥0):ℚ≥0):ℚ))
    (hk:k≤2^w) (active:Finset (Fin n)) (root:Fin n) (r:ℚ≥0)
    (hr:r∈RadiusData.candidates (length root) (fun v => length v root) k delta):
    RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RamRegionSetup.query
      (ResidualData.weights I active) (ResidualData.capacity I active) length root seed beta) r) (exponent n w):=by
  have hp:2^w≤2^(2*w):=Nat.pow_le_pow_right (by decide) (by omega)
  have widen {q:ℚ} (h:Height (2^w) q):Height (2^(2*w)) q:=height_mono h hp
  have hrad:Height (2^(2*w)) (r:ℚ):=by
    have h:=RadiusData.height (length root) (fun v => length v root) k (2^w) delta
      Nat.one_le_two_pow hk hu hd (hl root) (fun v => hl v root) r hr
    simpa only [←Nat.pow_add,show w+w=2*w by omega] using h
  apply RegionQueryHeight.bounds _ (2*w)
  · exact fun v => widen (ResidualData.weights_height I active w hw v)
  · exact fun u v => widen (ResidualData.capacity_height I active w hc u v)
  · exact fun u v => widen (hl u v)
  · intro b v
    cases b
    · exact widen (hl v root)
    · exact widen (hl root v)
  · exact widen hs
  · exact widen hb
  · exact hrad

end Lax455465Proofs.RegionIterationHeight

end

section

namespace Lax455465Proofs.RoundingHeight
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

theorem cut_mono {n M N:ℕ} {I:RationalInstance n} {S:Finset (Fin n)}
    (h:CutScoreHeight.Bounds I S M) (hMN:M≤ N):CutScoreHeight.Bounds I S N:=by
  exact ⟨fun v => height_mono (h.weightsBound v) hMN,fun u v => height_mono (h.capacityBound u v) hMN,
    fun i => height_mono (h.massPrefix i) hMN,fun i => height_mono (h.capacityPrefix i) hMN,
    height_mono h.totalBound hMN,height_mono h.massBound hMN,height_mono h.otherBound hMN,
    height_mono h.demandBound hMN,height_mono h.inverseBound hMN,height_mono h.cutCapacityBound hMN,
    height_mono h.ratioBound hMN⟩

theorem large_mono {n M N:ℕ} {I:RationalInstance n} {d:MetricMatrix.Matrix n}
    {Tin Tout:Finset (Fin n)} {hin:Tin.Nonempty} {hout:Tout.Nonempty}
    (h:LargePotentialData.Bounds I d Tin Tout hin hout M) (hMN:M≤ N):
    LargePotentialData.Bounds I d Tin Tout hin hout N:=by
  exact ⟨fun v => height_mono (h.weights v) hMN,fun u v => height_mono (h.distances u v) hMN,
    fun q hq => height_mono (h.fromProducts q hq) hMN,fun q hq => height_mono (h.toProducts q hq) hMN,
    fun i => height_mono (h.fromPrefix i) hMN,fun i => height_mono (h.toPrefix i) hMN⟩

def cutExponent (n w:ℕ):ℕ:=
  2*w+CutScoreHeight.exponent n w+LargePotentialData.exponent n w+2*n+4

theorem cut_bounds {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (w p:ℕ) (hp:p≤ n)
    (hw:∀ v,Height (2^w) (I.weight v:ℚ)) (hc:∀ u v,Height (2^w) (I.capacity u v:ℚ))
    (hd:∀ u v,Height (2^w) (d u v:ℚ)):
    (2^w)*(2^w)≤ 2^(cutExponent n w)∧ 2*p≤ 2^(cutExponent n w)∧
    (∀ S,CutScoreHeight.Bounds I S (2^(cutExponent n w)))∧
    (∀ Tin Tout:Finset (Fin n),∀ hin:Tin.Nonempty,∀ hout:Tout.Nonempty,
      LargePotentialData.Bounds I d Tin Tout hin hout (2^(cutExponent n w))):=by
  have hpow (a:ℕ) (h:a≤ cutExponent n w):2^a≤ 2^(cutExponent n w):=Nat.pow_le_pow_right (by decide) h
  refine ⟨?_,?_,?_,?_⟩
  · rw [←Nat.pow_add]
    exact hpow _ (by dsimp [cutExponent]; omega)
  · calc
      2*p≤ 2*n:=by omega
      _≤ 2^(2*n):=Nat.lt_two_pow_self.le
      _≤ _:=hpow _ (by dsimp [cutExponent]; omega)
  · intro S
    exact cut_mono (CutScoreHeight.bounds I S w hw hc) (hpow _ (by dsimp [cutExponent]; omega))
  · intro Tin Tout hin hout
    exact large_mono (LargePotentialData.bounds I d Tin Tout hin hout w hw hd) (hpow _ (by dsimp [cutExponent]; omega))

def constantExponent (w:ℕ):ℕ:=3*w+2

theorem constant_bounds (cost total:ℚ≥0) (p w:ℕ) (hw:2≤ w)
    (hc:Height (2^w) (cost:ℚ)) (ht:Height (2^w) (total:ℚ))
    (hp:p≤ 2^w) (hk:RegionBudget.steps p≤ 2^w):
    RoundingConstantHeight.Bounds cost total p (2^(constantExponent w)):=by
  have h4:4≤ 2^w:=(by norm_num:4≤ 2^2).trans (Nat.pow_le_pow_right (by decide) hw)
  have he:4*(2^w)^3=2^(constantExponent w):=by
    rw [constantExponent,Nat.mul_comm 3 w,pow_add,pow_mul]
    norm_num
    ring
  simpa only [he] using RoundingConstantHeight.bounds cost total p (2^w) h4 hc ht hp hk

end Lax455465Proofs.RoundingHeight

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRoundingBudget
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionContext
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def constants (w:ℕ):ℕ:=RoundingHeight.constantExponent w
def queries (n w:ℕ):ℕ:=RegionIterationHeight.exponent n (constants w)
def cuts (n w:ℕ):ℕ:=RoundingHeight.cutExponent n (constants w)
def width (n w:ℕ):ℕ:=RamHostBounds.sufficient (constants w+queries n w+cuts n w) 0 0 (2*n*n+12*n+20)

def cost (n p w:ℕ) (total:ℚ≥0):ℕ:=
  ((36*((2^(constants w))^2).size+200)*(n+1)+600*((2^(constants w))^2).size+2000)+
    (36*(total.den*3).size+28*n+116+RamRegionBoundedLoop.cost n p (2^(constants w)) (queries n w)+
      RamRegionCut.cost n p (2^(cuts n w))+RamZeroCut.cost n (2^(cuts n w)))

theorem support_le {n:ℕ} (I:RationalInstance n):RamRoundingInit.support I.weight≤ n:=by
  unfold RamRoundingInit.support RegionSelection.support
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

theorem steps_le {n p:ℕ} (hp:p≤ n):RegionBudget.steps p≤ 2*n+4:=by
  have:=Nat.log2_le_self p
  unfold RegionBudget.steps
  omega

theorem host_bounds (n w W:ℕ) (hW:width n w≤ W):
    2*(2^(constants w))^2+3 < 2^W∧ 2*(2^(queries n w))^2+3 < 2^W∧
      2*(2^(cuts n w))^2+3 < 2^W∧ 2*n*n+12*n+21 < 2^W:=by
  obtain ⟨hb,_,_,hi⟩:=RamHostBounds.sufficient_bounds _ 0 0 _ W hW
  have hw:=Nat.pow_le_pow_right (show 1≤ 2 by decide)
    (show constants w≤ constants w+queries n w+cuts n w by omega)
  have hq:=Nat.pow_le_pow_right (show 1≤ 2 by decide)
    (show queries n w≤ constants w+queries n w+cuts n w by omega)
  have hc:=Nat.pow_le_pow_right (show 1≤ 2 by decide)
    (show cuts n w≤ constants w+queries n w+cuts n w by omega)
  refine ⟨?_,?_,?_,hi⟩
  all_goals
    apply lt_of_le_of_lt _ hb
    gcongr

set_option maxHeartbeats 0 in

theorem command_spec (W w:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (hw:2*n+4≤ w) (hW:width n w≤ W)
    (hweights:∀ v,Height (2^w) (I.weight v:ℚ))
    (hcapacities:∀ u v,Height (2^w) (I.capacity u v:ℚ))
    (hdistances:∀ u v,Height (2^w) (d u v:ℚ))
    (hcost:Height (2^w) (MetricCostData.cost I d:ℚ))
    (hprefix:∀ i,Height (2^w) (((List.ofFn I.weight).take i).sum:ℚ))
    (hp:0 < RamRoundingInit.support I.weight) (htotal:0 < LargeBallRounding.total I)
    (hdiag:∀ v,d v v=0)
    (htri:∀ u v t,(d u t:ℚ)≤ (d u v:ℚ)+(d v t:ℚ))
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d)):
    Spec (2^W) (fun σ => RamMetricRounding.Input I d σ∧
      RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ∧ RamRegionCut.Room n σ)
      RamMetricRounding.command (fun _ τ => RamRegionCut.Output I d (RamRoundingInit.support I.weight) τ)
      (cost n (RamRoundingInit.support I.weight) w (RamRoundingInit.total I.weight)):=by
  let p:=RamRoundingInit.support I.weight
  let total:=RamRoundingInit.total I.weight
  let seed:=RoundingConstants.seed (MetricCostData.cost I d) p
  let delta:=RoundingConstants.delta total
  let beta:=RoundingConstants.beta total p
  have hpN:p≤ n:=support_le I
  have hk:RegionBudget.steps p≤ 2*n+4:=steps_le hpN
  have hpow:2^w≤ 2^(constants w):=Nat.pow_le_pow_right (by decide) (by
    dsimp [constants,RoundingHeight.constantExponent]; omega)
  have widen {q:ℚ} (h:Height (2^w) q):Height (2^(constants w)) q:=height_mono h hpow
  have ht:Height (2^w) (total:ℚ):=by
    have h:=hprefix (List.ofFn I.weight).length
    simpa only [List.take_length,total,RamRoundingInit.total,List.sum_ofFn] using h
  have hconstants:=RoundingHeight.constant_bounds (MetricCostData.cost I d) total p w (by omega) hcost ht
    (by have:=Nat.lt_two_pow_self (n:=w); omega) (by have:=Nat.lt_two_pow_self (n:=w); omega)
  have hM:4≤ 2^(constants w):=(by norm_num:4≤ 2^2).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [constants,RoundingHeight.constantExponent]; omega))
  have hkM:RegionBudget.steps p≤ 2^(constants w):=by
    have:=Nat.lt_two_pow_self (n:=w); omega
  obtain ⟨hB,hquery,hNB,hindex⟩:=host_bounds n w W hW
  obtain ⟨hMN,hpN',hcuts,hlarge⟩:=RoundingHeight.cut_bounds I d (constants w) p hpN
    (fun v => widen (hweights v)) (fun u v => widen (hcapacities u v)) (fun u v => widen (hdistances u v))
  have hthreshold:Height (2^(queries n w)) (RamLargeThreshold.threshold total:ℚ):=by
    have hh:=height_mul ht (show Height 3 ((2/3:ℚ≥0):ℚ) from by norm_num [Height])
    have hmul:2^w*3≤ 2^(w+2):=by rw [pow_add]; norm_num
    have hexp:w+2≤ queries n w:=by
      dsimp [queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,VolumeHeight.exponent,
        constants,RoundingHeight.constantExponent]
      omega
    exact height_mono (by simpa only [RamLargeThreshold.threshold,NNRat.coe_mul] using hh)
      (hmul.trans (Nat.pow_le_pow_right (by decide) hexp))
  have htCoe:(total:ℚ)=LargeBallRounding.total I:=RegionRuntimeCorrespondence.coe_total I
  have hdCoe:(delta:ℚ)=RegionRounding.radiusBudget I:=by
    dsimp only [delta]
    rw [RoundingConstants.coe_delta,htCoe]
    rfl
  have hdelta:0 < (delta:ℚ):=by rw [hdCoe,RegionRounding.radiusBudget]; positivity
  have hseed:(seed:ℚ)=RegionRounding.metricCost I (MetricMatrix.rational d)/(p:ℚ):=by
    simp only [seed,RoundingConstants.seed,NNRat.coe_div,NNRat.coe_natCast,MetricCostData.coe_cost]
  have hcostSeed:RegionRounding.metricCost I (MetricMatrix.rational d)≤ (p:ℚ)*(seed:ℚ):=by
    rw [hseed,mul_div_cancel₀ _ (by exact_mod_cast (show p ≠ 0 by omega))]
  have hsupport:(RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤ p:=by
    change (RegionSelection.support (fun v => if v∈ (Finset.univ:Finset (Fin n)) then (I.weight v:ℚ) else 0)).card≤ p
    simp only [Finset.mem_univ,if_true]
    exact Nat.le_refl _
  apply RamMetricRounding.command_spec (2^W) (2^(constants w)) (queries n w) (2^(cuts n w)) I d seed beta delta p
    hM hkM hB hquery (by nlinarith) (by omega) (by omega) (by omega) hthreshold
    (fun v => num_bound (widen (hweights v))) (fun v => den_bound (widen (hweights v)))
    (fun u v => num_bound (widen (hcapacities u v))) (fun u v => den_bound (widen (hcapacities u v)))
    (fun u v => widen (hdistances u v)) hconstants.deltaBound hconstants.stepBound
    _ (RoundingConstants.coe_beta total p) hdelta hp hdiag htri hcostSeed hsupport (widen ht)
    Nat.one_le_two_pow (by simpa only [constants,cuts] using hMN) (by simpa only [constants,cuts] using hpN') hNB
    hlarge hcuts htotal hsep hseed hdCoe rfl hconstants (fun i => widen (hprefix i))
  intro active root i hi
  exact RegionIterationHeight.bounds I d seed beta delta (RegionBudget.steps p) (constants w)
    (fun v => widen (hweights v)) (fun u v => widen (hcapacities u v)) (fun u v => widen (hdistances u v))
    hconstants.seedBound hconstants.betaBound hconstants.deltaBound hconstants.stepBound hkM active root _
    (List.getElem_mem hi)

end Lax455465Proofs.RamRoundingBudget

end

section

namespace Lax455465Proofs.RamRoundingResources
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open LpInputSize RamRoundingBudget
open scoped NNRat

theorem time_bound (n p w:ℕ) (total:ℚ≥0) (hp:p≤ n) (ht:total.den≤ 2^w):
    RamRoundingBudget.cost n p w total≤ timeExpression n w (constants w) (queries n w) (cuts n w):=by
  have hk:=RamRoundingBudget.steps_le hp
  have hs:(total.den*3).size≤ w+3:=by
    apply Nat.size_le.mpr
    calc
      total.den*3≤ 2^w*3:=Nat.mul_le_mul_right 3 ht
      _ < 2^(w+3):=by rw [pow_add]; have:=Nat.two_pow_pos w; norm_num
  simp only [RamRoundingBudget.cost,RamRegionBoundedLoop.cost,RamRegionCore.cost,RamRegionPrelude.cost,
    RamRegionSetup.cost,RamRadiusSearch.queryCost,RamRegionCut.cost,RamLargeCut.cost,RamLargePotential.cost,
    RamSetPotential.cost,RamSetDistances.cost,RamPotentialAverage.cost,RamHistoryCut.cost,RamHistoryPotential.cost,
    RamZeroCut.cost,RamZeroCut.prepareCost,RamPotentialSweep.cost,RamThresholdCandidate.cost,RamCutScore.cost,
    ←pow_mul,Nat.size_pow,timeExpression]
  gcongr

theorem eval_constants (base:Polynomial ℕ) (L:ℕ):
    (constantsBound base).eval L=constants (base.eval L):=by
  simp [constantsBound,constants,RoundingHeight.constantExponent]
theorem eval_queries (base:Polynomial ℕ) (L:ℕ):
    (queriesBound base).eval L=queries L (base.eval L):=by
  simp [queriesBound,eval_constants,queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,
    VolumeHeight.exponent,VolumeHeight.sumExponent]
theorem eval_cuts (base:Polynomial ℕ) (L:ℕ):
    (cutsBound base).eval L=cuts L (base.eval L):=by
  simp [cutsBound,eval_constants,cuts,RoundingHeight.cutExponent,CutScoreHeight.exponent,
    CutScoreHeight.sumExponent,LargePotentialData.exponent]
theorem eval_word (base:Polynomial ℕ) (L:ℕ):
    (wordBound base).eval L=width L (base.eval L):=by
  simp [wordBound,eval_constants,eval_queries,eval_cuts,width,RamHostBounds.sufficient]
  omega
theorem eval_time (base:Polynomial ℕ) (L:ℕ):
    (timeBound base).eval L=timeExpression L (base.eval L) (constants (base.eval L))
      (queries L (base.eval L)) (cuts L (base.eval L)):=by
  simp only [timeBound,timeExpression,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_one,eval_constants,eval_queries,eval_cuts]

theorem width_mono {n m w:ℕ} (hn:n≤ m):width n w≤ width m w:=by
  dsimp [width,RamHostBounds.sufficient,queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,
    VolumeHeight.exponent,VolumeHeight.sumExponent,cuts,RoundingHeight.cutExponent,CutScoreHeight.exponent,
    CutScoreHeight.sumExponent,LargePotentialData.exponent]
  gcongr

theorem time_mono {n m w:ℕ} (hn:n≤ m):
    timeExpression n w (constants w) (queries n w) (cuts n w)≤
      timeExpression m w (constants w) (queries m w) (cuts m w):=by
  dsimp [timeExpression,queries,RegionIterationHeight.exponent,RegionQueryHeight.exponent,
    VolumeHeight.exponent,VolumeHeight.sumExponent,cuts,RoundingHeight.cutExponent,CutScoreHeight.exponent,
    CutScoreHeight.sumExponent,LargePotentialData.exponent]
  gcongr

end Lax455465Proofs.RamRoundingResources

end

section

namespace Lax455465Proofs.RamUniformRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open LpInputSize RamRoundingResources
open scoped NNRat

theorem data_bounds (P:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n)
    (d:MetricMatrix.Matrix n)
    (hd:∀ u v,Height (2^(P.eval (bitSize (encodeInput kind I)))) (d u v:ℚ)):
    let w:=(baseBound P).eval (bitSize (encodeInput kind I))
    2*n+4≤ w∧ (∀ v,Height (2^w) (I.weight v:ℚ))∧
      (∀ u v,Height (2^w) (I.capacity u v:ℚ))∧ (∀ u v,Height (2^w) (d u v:ℚ))∧
      Height (2^w) (MetricCostData.cost I d:ℚ)∧
      ∀ i,Height (2^w) (((List.ofFn I.weight).take i).sum:ℚ):=by
  let L:=bitSize (encodeInput kind I)
  let w:=(baseBound P).eval L
  have hn:n≤ L:=input_dimension kind I
  have he:w=(RamMetricCostResources.heightBound P).eval L+L*(L+1)+L+1+P.eval L+3*L+8:=by
    simp [w,baseBound]
  have hL:L≤ w:=by omega
  have hP:P.eval L≤ w:=by omega
  have widen {k:ℕ} {q:ℚ} (h:Height (2^k) q) (hk:k≤ w):Height (2^w) q:=
    height_mono h (Nat.pow_le_pow_right (by decide) hk)
  refine ⟨show 2*n+4≤ w from by omega,fun v => widen (weight_height kind I v) hL,
    fun u v => widen (capacity_height kind I u v) hL,fun u v => widen (hd u v) hP,?_,?_⟩
  · have hc:=MetricCostHeight.prefix_height kind I d (P.eval L) hd
      (RamProductSum.products (MetricMatrix.values I.capacity) (MetricMatrix.values d)).length
    have hc':Height (2^(MetricCostHeight.exponent n L (P.eval L))) (MetricCostData.cost I d:ℚ):=by
      simpa only [List.take_length,MetricCostData.cost] using hc
    apply widen hc'
    have hh:=RamMetricCostResources.height_bound P kind I
    change MetricCostHeight.exponent n L (P.eval L)≤ (RamMetricCostResources.heightBound P).eval L at hh
    omega
  · intro i
    have hw:∀ q∈List.ofFn I.weight,Height (2^L) (q:ℚ):=by
      intro q hq
      obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
      exact weight_height kind I v
    have hs:=RationalSumHeight.prefix_dyadic_height (List.ofFn I.weight) L
      (fun q hq => num_bound (hw q hq)) (fun q hq => den_bound (hw q hq)) i
    have hs':Height (2^(L*(n+1)+n+1)) (((List.ofFn I.weight).take i).sum:ℚ):=by
      simpa only [List.length_ofFn] using hs
    apply widen hs'
    have hm:=Nat.mul_le_mul_left L (show n+1≤ L+1 by omega)
    omega

theorem command_spec (P:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n)
    (d:MetricMatrix.Matrix n)
    (hd:∀ u v,Height (2^(P.eval (bitSize (encodeInput kind I)))) (d u v:ℚ))
    (hp:0 < RamRoundingInit.support I.weight) (htotal:0 < LargeBallRounding.total I)
    (hdiag:∀ v,d v v=0)
    (htri:∀ u v t,(d u t:ℚ)≤ (d u v:ℚ)+(d v t:ℚ))
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (W:ℕ) (hW:(wordBound (baseBound P)).eval (bitSize (encodeInput kind I))≤ W):
    Spec (2^W) (fun σ => RamMetricRounding.Input I d σ∧
      RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ∧ RamRegionCut.Room n σ)
      RamMetricRounding.command (fun _ τ => RamRegionCut.Output I d (RamRoundingInit.support I.weight) τ)
      ((timeBound (baseBound P)).eval (bitSize (encodeInput kind I))):=by
  let L:=bitSize (encodeInput kind I)
  let w:=(baseBound P).eval L
  have hn:n≤ L:=input_dimension kind I
  obtain ⟨hw,hwg,hcg,hdg,hcost,hprefix⟩:=data_bounds P kind I d hd
  have hW':RamRoundingBudget.width n w≤ W:=by
    rw [eval_word] at hW
    exact (width_mono hn).trans hW
  have hb:=RamRoundingBudget.command_spec W w I d hw hW' hwg hcg hdg hcost hprefix hp htotal hdiag htri hsep
  have htotalHeight:Height (2^w) (RamRoundingInit.total I.weight:ℚ):=by
    simpa only [List.take_length,RamRoundingInit.total] using hprefix (List.ofFn I.weight).length
  have ht:=(time_bound n (RamRoundingInit.support I.weight) w (RamRoundingInit.total I.weight)
    (RamRoundingBudget.support_le I) (den_bound htotalHeight)).trans (time_mono hn)
  intro σ hσ
  obtain ⟨τ,rr,pr⟩:=hb σ hσ
  exact ⟨τ,rr.mono (by simpa only [eval_time] using ht),pr⟩

end Lax455465Proofs.RamUniformRounding

end

theorem solution:∀ (P:@Polynomial Nat Nat.instSemiring) {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind)
  (I:Lax455465.RationalEncoding.RationalInstance n) (d:Lax455465Proofs.MetricMatrix.Matrix n),
  (∀ (u v:Fin n),
      Lax455465Proofs.LpInputSize.Height
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) P))
        (@NNRat.cast Rat Rat.instNNRatCast (d u v)))→
    Nat.lt ((0:Nat))
        (@Lax455465Proofs.RamRoundingInit.support n (@Lax455465.RationalEncoding.RationalInstance.weight n I))→
      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@Lax455465Proofs.LargeBallRounding.total n I)→
        (∀ (v:Fin n),
            @Eq NNRat (d v v)
              (@OfNat.ofNat NNRat (nat_lit 0)
                (@Zero.toOfNat0 NNRat
                  (@MulZeroClass.toZero NNRat
                    (@instMulZeroClassOfSemiring NNRat
                      (@DivisionSemiring.toSemiring NNRat
                        (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))→
          (∀ (u v t:Fin n),
              @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u t))
                (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                  (@NNRat.cast Rat Rat.instNNRatCast (d v t))))→
            @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                  (@Lax455465Proofs.MetricMatrix.rational n d))→
              ∀ (W:Nat),
                Nat.le
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (Lax455465Proofs.RamRoundingResources.wordBound
                        (Lax455465Proofs.RamRoundingResources.baseBound P)))
                    W→
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) W)
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamMetricRounding.Input n I d σ)
                        (And
                          (Lax455465Proofs.RamRegionInvariant.Room n
                            (@Lax455465Proofs.RamRoundingInit.support n
                              (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                            σ)
                          (Lax455465Proofs.RamRegionCut.Room n σ)))
                    Lax455465Proofs.RamMetricRounding.command
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      @Lax455465Proofs.RamRegionCut.Output n I d
                        (@Lax455465Proofs.RamRoundingInit.support n
                          (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                        τ)
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (Lax455465Proofs.RamRoundingResources.timeBound
                        (Lax455465Proofs.RamRoundingResources.baseBound P))):= @Lax455465Proofs.RamUniformRounding.command_spec
