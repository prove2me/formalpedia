-- Prove2me | solution 1 for Lax263307Proofs.NativeSelectedRounds.rounds_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:52.302727+00:00
-- url     : https://prove2.me/submissions/67c30139-faf6-48b4-bbfe-648c91ce3171

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax263307Proofs_NativeSelectedOracle_setup_native
import Theorems.Thm_Lax263307Proofs_NativeRecursiveOracle_trajectory_guards_native
import Theorems.Thm_Lax263307Proofs_NativeOracleCutHeight_normal_height_native

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

namespace Lax263307Proofs.NativeSelectedOracle
end Lax263307Proofs.NativeSelectedOracle
theorem Lax263307Proofs.NativeSelectedOracle.setup:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} (lpProgram:Lax263307Proofs.NativeSelectedLP.Program lp)
      (flowProgram:Lax263307Proofs.NativeSelectedNear.Program flow) (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp lpProgram) cfg.lp→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp lpProgram) cfg.lpWidth→
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow flowProgram) cfg.flow→
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow flowProgram) cfg.flowWidth→
              Lax263307Proofs.NativeEncodedLP.Encoded lp→
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
                  LT.lt ((0:Nat)) cfg.K→
                    LT.lt ((0:Nat)) cfg.b→
                      ∀ {n:Nat} (G:SimpleGraph (Fin n))
                        [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                        (D k fuel S v R F w rootN capacity childSteps childTime:Nat) (extent:String→ Nat)
                        (front:List Nat),
                        Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                            (HAdd.hAdd
                              (HMul.hMul S
                                (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                            capacity
                            (HAdd.hAdd fuel
                              ((1:Nat)))
                            n G k (@List.length Nat front)→
                          LT.lt ((1:Nat)) n→
                            LE.le ((4:Nat)) D→
                              LT.lt ((0:Nat)) F→
                                LT.lt (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k→
                                  LE.le n R→
                                    LE.le k R→
                                      LE.le (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                          R→
                                        LE.le D R→
                                          LE.le F R→
                                            LE.le
                                                (Lax263307.MomentLP.dimension n
                                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                                                R→
                                              ∀
                                                (state:
                                                  Lax263307.RoundedOracleSearch.State
                                                    (Lax263307.MomentLP.dimension n
                                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                                (∀
                                                    (i:
                                                      Fin
                                                        (Lax263307.MomentLP.dimension n
                                                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                                    Lax263307.NativeRoundedStep.height
                                                      (@Prod.snd
                                                        (Matrix
                                                          (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)))
                                                          (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)))
                                                          Rat)
                                                        (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D))→
                                                          Rat)
                                                        state i)
                                                      (HMul.hMul
                                                        ((80:Nat))
                                                        (HAdd.hAdd R
                                                          ((1:Nat)))))→
                                                  @Lax263307Proofs.NativeOracleExecution.ProjectionBounds n D k
                                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) F
                                                      (@HPow.hPow Nat Nat Nat
                                                        (@instHPow Nat Nat
                                                          (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                        ((2:Nat))
                                                        (HMul.hMul
                                                          ((100:Nat))
                                                          (HAdd.hAdd R
                                                            ((1:Nat)))))
                                                      w (@Lax263307Proofs.NativeSelectedLP.oracleTime lp lpProgram R) G
                                                      inst extent→
                                                    Lax263307Proofs.NativeNearExecution.Bounds n
                                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D)
                                                        (@HPow.hPow Nat Nat Nat
                                                          (@instHPow Nat Nat
                                                            (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                          ((2:Nat))
                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight lp
                                                            lpProgram R))
                                                        (HMul.hMul
                                                          ((2:Nat))
                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight lp
                                                            lpProgram R))
                                                        (HAdd.hAdd R
                                                          ((1:Nat)))
                                                        fuel S w cfg extent front→
                                                      LE.le
                                                          (@Lax263307Proofs.NativeSelectedLP.wordHeight lp lpProgram R)
                                                          w→
                                                        LE.le
                                                            (HAdd.hAdd
                                                              (Lax263307Proofs.NativeCutResources.wordExponent
                                                                (Lax263307.MomentLP.dimension n
                                                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b
                                                                    n D))
                                                                (HAdd.hAdd
                                                                  (HMul.hMul
                                                                    ((2:Nat))
                                                                    (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                      lp lpProgram R))
                                                                  ((1:Nat))))
                                                              ((4:Nat)))
                                                            w→
                                                          LT.lt
                                                              (Lax263307Proofs.NativeSelectedLP.queryBound R)
                                                              (extent "vm.input")→
                                                            LE.le
                                                                (Lax263307Proofs.NativeUniformFlow.wordHeight n
                                                                  (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                    cfg.b n
                                                                    (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                    (HMul.hMul
                                                                      ((2:Nat))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R)))
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.code flow
                                                                    flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.width
                                                                    flow flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.time flow
                                                                    flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.output
                                                                    flow flowProgram))
                                                                w→
                                                              (∀ (a:String),
                                                                  @Membership.mem String (List String)
                                                                      (@List.instMembership String)
                                                                      Lax263307Proofs.NativeSeparatorContext.workspace
                                                                      a→
                                                                    LE.le
                                                                      (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                                        (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                          cfg.b n
                                                                          (Lax263307.AlgorithmParameters.load cfg.b n D)
                                                                          k
                                                                          (@HMul.hMul Nat Nat Nat
                                                                            (@instHMul Nat instMulNat)
                                                                            ((2:Nat))
                                                                            (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                              lp lpProgram R)))
                                                                        (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                          flow flowProgram))
                                                                      (extent a))→
                                                                ∀
                                                                  (child:
                                                                    (A:Finset (Fin n))→
                                                                      Nat→
                                                                        Option (Finset (Fin (@Finset.card (Fin n) A)))),
                                                                  @Lax263307Proofs.NativeRecursiveSetup.Oracle n
                                                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K
                                                                      cfg.b n D)
                                                                    D k
                                                                    (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K
                                                                      cfg.b n D)
                                                                    cfg.b (Lax263307.AlgorithmParameters.load cfg.b n D)
                                                                    F fuel S v w
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      ((2:Nat))
                                                                      (HMul.hMul
                                                                        ((100:Nat))
                                                                        (@HAdd.hAdd Nat Nat Nat
                                                                          (@instHAdd Nat instAddNat) R
                                                                          ((1:Nat)))))
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      ((2:Nat))
                                                                      (HAdd.hAdd
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          ((2:Nat))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R))
                                                                        ((1:Nat))))
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      ((2:Nat))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R))
                                                                    (HMul.hMul
                                                                      ((2:Nat))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R))
                                                                    (HAdd.hAdd R
                                                                      ((1:Nat)))
                                                                    (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                                      (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                        cfg.b n
                                                                        (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          ((2:Nat))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R)))
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                        flow flowProgram))
                                                                    (@Lax263307Proofs.NativeSelectedLP.oracleTime lp
                                                                      lpProgram R)
                                                                    (@Lax263307Proofs.NativeSelectedLP.callCost lp
                                                                      lpProgram R)
                                                                    (Lax263307Proofs.NativeSeparatorOutput.timeBound n
                                                                      (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                        cfg.b n
                                                                        (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          ((2:Nat))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R)))
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.code
                                                                        flow flowProgram)
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.coeff
                                                                        flow flowProgram)
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                        flow flowProgram))
                                                                    childSteps childTime cfg G inst lp flow extent front
                                                                    child state
                                                                    (Lax263307Proofs.NativeRecursiveDomain.eligible C
                                                                      rootN
                                                                      (HAdd.hAdd
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat) S
                                                                          (@List.length String
                                                                            (Lax263307Proofs.NativeCoreMachine.frameArrays
                                                                              cfg)))
                                                                        (@List.length String
                                                                          (Lax263307Proofs.NativeCoreMachine.frameScalars
                                                                            cfg)))
                                                                      capacity):= @Lax263307Proofs.NativeSelectedOracle.setup_native
namespace Lax263307Proofs.NativeRecursiveOracle
end Lax263307Proofs.NativeRecursiveOracle
theorem Lax263307Proofs.NativeRecursiveOracle.trajectory_guards:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} {a K b:Nat},
      Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow a K b→
        ∀ {n:Nat} (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
          @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n))) (@Set.instMembership (SimpleGraph (Fin n)))
              (C n) G→
            LT.lt ((1:Nat)) n→
              ∀ (D k fuel R j:Nat),
                LE.le ((4:Nat)) D→
                  LT.lt (Lax263307.AlgorithmParameters.cutoff a K b n D) k→
                    LE.le (Lax263307.RecursionDepth.depth n)
                        (HAdd.hAdd fuel
                          ((1:Nat)))→
                      LE.le
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) R→
                        LE.le j R→
                          have oracle:=
                            fun (x:Nat)
                              (center:
                                Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D)→ Rat) =>
                            @Lax263307.ProjectedOracle.run n lp flow a K b D G inst k
                              (@Lax263307Proofs.NativeRecursiveOracle.child n lp flow a K b D fuel G inst) center;
                          And
                            (∀
                              (i l:
                                Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))),
                              Lax263307.NativeRoundedStep.height
                                (@Prod.fst
                                  (Matrix
                                    (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)))
                                    (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)))
                                    Rat)
                                  (Fin
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))→
                                    Rat)
                                  (@Lax263307.RoundedOracleSearch.trajectory
                                    (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                    (Finset (Fin n)) oracle j)
                                  i l)
                                (HMul.hMul
                                  ((80:Nat))
                                  (HAdd.hAdd R
                                    ((1:Nat)))))
                            (And
                              (∀
                                (i:
                                  Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))),
                                Lax263307.NativeRoundedStep.height
                                  (@Prod.snd
                                    (Matrix
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat)
                                    (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D))→
                                      Rat)
                                    (@Lax263307.RoundedOracleSearch.trajectory
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)) oracle j)
                                    i)
                                  (HMul.hMul
                                    ((80:Nat))
                                    (HAdd.hAdd R
                                      ((1:Nat)))))
                              (∀
                                (normal:
                                  Fin (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))→
                                    Int),
                                @Eq
                                    (Lax263307.RoundedOracleSearch.Reply
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)))
                                    (oracle j
                                      (@Prod.snd
                                        (Matrix
                                          (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)))
                                          (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D)))
                                          Rat)
                                        (Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))→
                                          Rat)
                                        (@Lax263307.RoundedOracleSearch.trajectory
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)) oracle j)))
                                    (@Lax263307.RoundedOracleSearch.Reply.cut
                                      (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                      (Finset (Fin n)) normal)→
                                  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                    (@dotProduct
                                      (Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat
                                      (Fin.fintype
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level a K b n D)))
                                      Rat.instMul Rat.addCommMonoid
                                      (@Lax263307.RoundedOracleSearch.rationalNormal
                                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D))
                                        normal)
                                      (@Matrix.mulVec
                                        (Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        (Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        Rat
                                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                                              (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                                        (Fin.fintype
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D)))
                                        (@Prod.fst
                                          (Matrix
                                            (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)))
                                            (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D)))
                                            Rat)
                                          (Fin
                                              (Lax263307.MomentLP.dimension n
                                                (Lax263307.AlgorithmParameters.level a K b n D))→
                                            Rat)
                                          (@Lax263307.RoundedOracleSearch.trajectory
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))
                                            (Finset (Fin n)) oracle j))
                                        (@Lax263307.RoundedOracleSearch.rationalNormal
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          normal))))):= @Lax263307Proofs.NativeRecursiveOracle.trajectory_guards_native
namespace Lax263307Proofs.NativeOracleCutHeight
end Lax263307Proofs.NativeOracleCutHeight
theorem Lax263307Proofs.NativeOracleCutHeight.normal_height:∀ {C:Lax263307.GraphClasses.GraphClass} {lp flow:List Nat→ List Nat} {a K b:Nat},
  Lax263307Proofs.NearOracle.SeparatorCorrect C flow a K b→
    LT.lt ((0:Nat)) K→
      LT.lt ((0:Nat)) b→
        Lax263307Proofs.NativeEncodedLP.Encoded lp→
          ∀ (selected:Lax263307Proofs.NativeSelectedLP.Program lp) {n:Nat} (G:SimpleGraph (Fin n))
            [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
            @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                (@Set.instMembership (SimpleGraph (Fin n))) (C n) G→
              ∀ (D k R F j:Nat),
                LT.lt ((0:Nat)) n→
                  LE.le ((4:Nat)) D→
                    LT.lt (Lax263307.AlgorithmParameters.cutoff a K b n D) k→
                      LE.le n R→
                        LE.le k R→
                          LE.le (Lax263307.AlgorithmParameters.level a K b n D) R→
                            LE.le
                                (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level a K b n D)) R→
                              ∀
                                (center:
                                  Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D)→ Rat),
                                (∀ (i:Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K b n D)),
                                    Lax263307.NativeRoundedStep.height (center i)
                                      (HMul.hMul
                                        ((80:Nat))
                                        (HAdd.hAdd R
                                          ((1:Nat)))))→
                                  ∀
                                    (child:
                                      (A:Finset (Fin n))→ Nat→ Option (Finset (Fin (@Finset.card (Fin n) A))))
                                    (normal:
                                      Fin
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))→
                                        Int),
                                    @Eq
                                        (Lax263307.RoundedOracleSearch.Reply
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)))
                                        (@Lax263307Proofs.NativeOracleRounds.oracle n
                                          (Lax263307.AlgorithmParameters.level a K b n D) lp flow G inst D k
                                          (Lax263307.AlgorithmParameters.sparsity a K b n D) b
                                          (Lax263307.AlgorithmParameters.load b n D) F child j center)
                                        (@Lax263307.RoundedOracleSearch.Reply.cut
                                          (Lax263307.MomentLP.dimension n
                                            (Lax263307.AlgorithmParameters.level a K b n D))
                                          (Finset (Fin n)) normal)→
                                      ∀
                                        (i:
                                          Fin
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))),
                                        Lax263307.NativeRoundedStep.height
                                          (@Lax263307.RoundedOracleSearch.rationalNormal
                                            (Lax263307.MomentLP.dimension n
                                              (Lax263307.AlgorithmParameters.level a K b n D))
                                            normal i)
                                          (Lax263307Proofs.NativeOraclePrecision.roundedHeight
                                            (@Lax263307Proofs.NativeSelectedLP.Program.width lp selected) R):= @Lax263307Proofs.NativeOracleCutHeight.normal_height_native

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

end Lax808846Proofs.Reasoning

end

section

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open EntropyDecrease

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

namespace Lax263307Proofs.CoordinateCatalog

open Lax263307.LinearRelaxation Lax263307.RationalConditioning Lax263307.CoordinateCatalog

theorem catalog_complete (n r:ℕ) (A:Coordinate n r):A∈ catalog n r:=by
  have hmem:A.val∈ sets n r:=
    List.mem_dedup.mpr ((Lax263307Proofs.RationalConditioning.candidate_complete n (r + 2) A.val).mpr A.property)
  apply List.mem_map.mpr
  exact ⟨⟨A.val,hmem⟩,List.mem_attach _ _,Subtype.ext rfl⟩

theorem catalog_two (n r:ℕ) (positive:0 < n):2≤ (catalog n r).length:=by
  let v:Fin n:= ⟨0,positive⟩
  let A:Coordinate n r:= ⟨∅,by simp⟩
  let B:Coordinate n r:= ⟨{v},by simp⟩
  have hne:A ≠ B:=by
    intro h
    have heq:(∅:Finset (Fin n))={v}:=congrArg Subtype.val h
    have hv:v∈ (∅:Finset (Fin n)):=heq.symm ▸ Finset.mem_singleton_self v
    exact Finset.notMem_empty v hv
  have hsub:({A,B}:Finset (Coordinate n r)) ⊆ (catalog n r).toFinset:=by
    intro C hC
    simp only [Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact List.mem_toFinset.mpr (Lax263307Proofs.CoordinateCatalog.catalog_complete n r A)
    · exact List.mem_toFinset.mpr (Lax263307Proofs.CoordinateCatalog.catalog_complete n r B)
  have hcard:=Finset.card_le_card hsub
  have hpair:({A,B}:Finset (Coordinate n r)).card=2:=by simp [hne]
  rw [hpair] at hcard
  exact hcard.trans (List.toFinset_card_le _)

end Lax263307Proofs.CoordinateCatalog

end

section

namespace Lax808846Proofs.Imp

@[simp] theorem Com.wvars_skip:Com.skip.wvars=[]:=by simp [Com.wvars]

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

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

end Lax808846Proofs.Reasoning

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open DistanceProjection

def Correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ):
    Outcome n→ Prop
  | .near y => PrimalFeasible (toReal P) (realVector y)∧
      ∀ j, |(y j:ℝ) - (center j:ℝ)|≤ (ρ:ℝ)
  | .far a α => (∑ j, |(a j:ℝ)|)≤ 1∧
      (∀ y,PrimalFeasible (toReal P) y→ (∑ j, (a j:ℝ) * y j)≤ (α:ℝ))∧
      (ρ:ℝ) < (∑ j, (a j:ℝ) * (center j:ℝ)) - (α:ℝ)
  | .reject => ¬ IsFeasible (toReal P)

end Lax263307.RationalProjection

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

end Lax263307Proofs.NativeMasks

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

theorem words_append (xs ys:List ℚ):words (xs++ys)=words xs++words ys:=List.flatMap_append

end Lax263307Proofs.NativeRationalTabulate

end

section

namespace Lax263307Proofs.NativeMomentAssembly

open Lax263307 Lax109476.RationalEncoding
open MomentLP CoordinateCatalog

def matrixWords {m n:ℕ} (A:Fin m→ Fin n→ ℚ):List ℕ:=
  (List.ofFn fun i => List.ofFn (A i)).flatten.flatMap encodeRational

theorem ofFn_addCases {α:Type*} {m n:ℕ} (f:Fin m→ α) (g:Fin n→ α):
    List.ofFn (Fin.addCases f g)=List.ofFn f++List.ofFn g:=by
  simpa only [Fin.append] using List.ofFn_fin_append f g

def normalization (n r:ℕ):Fin 2→ Index n r→ ℚ:=
  fun i j => if i=0 then singleRow ∅ j else -singleRow ∅ j

def upper (n r:ℕ):Index n r→ Index n r→ ℚ:=fun i => singleRow (indexing n r i).val

def nonindependent {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i j => if G.IsIndepSet ((indexing n r i).val:Set (Fin n)) then 0 else singleRow (indexing n r i).val j

def monotone (n r:ℕ):Fin (dimension n r*n)→ Index n r→ ℚ:=
  fun i => let uv:=finProdFinEquiv.symm i
    if (indexing n r uv.1).val.card≤ r+1 then monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0

def massPositive (n k r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i => if (indexing n r i).val.card≤ r+1 then massRow (indexing n r i).val k else fun _ => 0

def massNegative (n k r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i j => if (indexing n r i).val.card≤ r+1 then -massRow (indexing n r i).val k j else 0

theorem matrix_length {m n:ℕ} (A:Fin m→ Fin n→ ℚ):(matrixWords A).length=3*m*n:=by
  change (NativeRationalTabulate.words ((List.ofFn fun i => List.ofFn (A i)).flatten)).length=3*m*n
  rw [NativeRationalTabulate.words_length]
  simp [List.length_flatten,List.map_ofFn,List.sum_ofFn,Nat.mul_assoc]

end Lax263307Proofs.NativeMomentAssembly

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentFamily

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP

def rowCount (kind:Kind) (n r:ℕ):ℕ:=match kind with
  | .normalization => 2
  | .monotone => dimension n r*n
  | _ => dimension n r

def matrix (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    Fin (rowCount kind n r)→ Index n r→ ℚ:=match kind with
  | .normalization => NativeMomentAssembly.normalization n r
  | .upper => NativeMomentAssembly.upper n r
  | .nonindependent => NativeMomentAssembly.nonindependent G r
  | .monotone => NativeMomentAssembly.monotone n r
  | .massPositive => NativeMomentAssembly.massPositive n k r
  | .massNegative => NativeMomentAssembly.massNegative n k r

def entries (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):List ℚ:=
  (List.ofFn fun i => List.ofFn (matrix kind G k r i)).flatten

theorem entries_length (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    (entries kind G k r).length=rowCount kind n r*dimension n r:=by
  simp [entries,List.length_flatten,List.map_ofFn,List.sum_ofFn]

open NativeCatalogMetadata NativeMomentProduce

end Lax263307Proofs.NativeMomentFamily

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce

def entries (N zeros:ℕ):List ℚ:= [1,-1]++List.replicate N 1++List.replicate zeros 0

theorem entries_length (N zeros:ℕ):(entries N zeros).length=2+N+zeros:=by simp [entries]; omega

def size (n r:ℕ):ℕ:=2+dimension n r+dimension n r*(n+4)

theorem vector_entries {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    List.ofFn (MomentLP.program G k r).b++List.ofFn (MomentLP.program G k r).c=
      entries (dimension n r) (dimension n r*(n+4)):=by
  simp only [MomentLP.program,NativeMomentAssembly.ofFn_addCases,List.ofFn_const]
  norm_num only [List.ofFn_succ,List.ofFn_zero,Fin.isValue,Fin.succ_ne_zero,if_true,if_false]
  simp only [entries,List.append_assoc]
  have hz:dimension n r+(dimension n r*n+(dimension n r+dimension n r))+dimension n r=dimension n r*(n+4):=by ring
  rw [←List.replicate_add,hz]

theorem words_exact {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    NativeRationalTabulate.words (entries (dimension n r) (dimension n r*(n+4)))=
      Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).b++Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).c:=by
  rw [←vector_entries G k r,NativeRationalTabulate.words_append]
  rfl

end Lax263307Proofs.NativeMomentVectors

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP NativeMomentFamily
open Lax109476.RationalEncoding

theorem row_count_eq (n r:ℕ):M n r=2+dimension n r*(n+4):=by
  unfold M NativeMomentAssembly.rowCount
  ring

theorem vector_size (n r:ℕ):NativeMomentVectors.size n r=M n r+dimension n r:=by
  rw [row_count_eq]
  unfold NativeMomentVectors.size
  omega

theorem input_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    (encodeProgram (MomentLP.program G k r)).length=length n r:=by
  have hv:(encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c).length=3*(M n r+dimension n r):=by
    rw [←NativeMomentVectors.words_exact G k r,NativeRationalTabulate.words_length,NativeMomentVectors.entries_length]
    change 3*NativeMomentVectors.size n r=_
    rw [vector_size]
  change ([M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A++
    encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c).length=_
  rw [List.append_assoc ( [M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A)]
  rw [List.length_append,hv,List.length_append,NativeMomentAssembly.matrix_length]
  simp only [List.length_cons,List.length_nil,length]
  simp only [M,NativeMomentAssembly.rowCount]
  ring

end Lax263307Proofs.NativeMomentInput

end

section

namespace Lax263307Proofs.NativeRoundedQuery

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch

theorem vector_length {n:ℕ} (v:Fin n→ ℚ):(encodeVector v).length=3*n:=by
  simp [encodeVector,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const] <;> ring

theorem shape_length {n:ℕ} (state:State n):(shape state).length=3*(n*n):=by
  simp [shape,List.length_flatten,vector_length,List.sum_ofFn,Finset.sum_const] <;> ring

end Lax263307Proofs.NativeRoundedQuery

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding
open Lax263307

theorem actual_tolerance (a K b n D:ℕ):
    tolerance n D ((AlgorithmParameters.floorDenominator a K b n D)^(AlgorithmParameters.level a K b n D))=
      Lax263307.ProjectedOracle.tolerance a K b n D:=by
  unfold tolerance denominator Lax263307.ProjectedOracle.tolerance AlgorithmParameters.momentFloor
  rw [div_div]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  congr 1
  ring

end Lax263307Proofs.NativeNodeTolerance

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

namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem words_length (names:List String) (S:ℕ) (σ:Env)
    (hS:∀ a∈names,(σ.arrs a).length=S):(words names σ).length=S*names.length:=by
  induction names with
  | nil => simp [words]
  | cons a as ih =>
    have hi:=ih (fun b hb => hS b (List.mem_cons_of_mem a hb))
    change (List.flatMap σ.arrs as).length=S*as.length at hi
    simp only [words,List.flatMap_cons,List.length_append,List.length_cons]
    rw [hS a (by simp),hi]
    nlinarith only []

end Lax263307Proofs.NativeFrameBuffers

end

section

namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (names:List String) (s:String) (hs:s≠"stack.words"):s∉(save names).wvars:=by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons t ts ih => simp [save,Com.wvars,RamWordBuffer.append,hs,ih]

end Lax263307Proofs.NativeFrameScalars

end

section

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem buffers_variable (names:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):s∉(NativeFrameBuffers.save names).wvars:=by
  induction names with
  | nil => simp [NativeFrameBuffers.save,Com.wvars]
  | cons a as ih =>
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
    simp [NativeFrameBuffers.save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,
      Com.wvars,hs.1,hs.2.1,hs.2.2,ih]

end Lax263307Proofs.NativeRecursionFrame

end

section

namespace Lax263307Proofs.NativeChildCall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (arrays scalars:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉(NativeRecursionFrame.save arrays scalars).wvars:=by
  have hw:s≠"stack.words" :=fun h => hs (by simp [h])
  simpa only [NativeRecursionFrame.save,Com.wvars,List.mem_append,not_or] using
    And.intro (NativeRecursionFrame.buffers_variable arrays s hs) (NativeFrameScalars.save_variable scalars s hw)

end Lax263307Proofs.NativeChildCall

end

section

namespace Lax263307Proofs.NativeRoundedUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch
open Matrix

theorem input_length {n:ℕ} (k:ℕ) (state:State n) (a:Fin n→ ℤ):
    (Lax263307.NativeRoundedStep.encodeInput k state a).length=2+3*(n*n)+6*n:=by
  change ([n,k]++NativeRoundedQuery.shape state++NativeRoundedQuery.normal a++NativeRoundedQuery.center state).length=_
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero,NativeRoundedQuery.shape_length,
    NativeRoundedQuery.normal,NativeRoundedQuery.center,NativeRoundedQuery.vector_length]
  omega

end Lax263307Proofs.NativeRoundedUpdate

end

section

namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

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

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem protocol {n B D k r p b load F fuel S v limit:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Protocol B D S v cfg extent front σ:=
  ⟨hc.bounded,hc.lengths,hc.stack,hc.cursor,hc.stride,hc.frameLength,hc.roundWidth,hc.nodeD⟩

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

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

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem actual_reply {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b D k fuel:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (center:MomentLP.Index n (AlgorithmParameters.level a K b n D)→ ℚ):
    let r:=AlgorithmParameters.level a K b n D
    let child:=fun C t => RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t
    reply flow G D k (AlgorithmParameters.sparsity a K b n D) b (AlgorithmParameters.load b n D) child
      (projection lp G k D ((AlgorithmParameters.floorDenominator a K b n D)^r) center) =
      ProjectedOracle.run lp flow a K b D G k
        (fun C t => (child C t).map (fun I => I.image (label C))) center:=by
  dsimp only
  unfold projection
  rw [NativeNodeTolerance.actual_tolerance]
  have near_eq (x:MomentLP.Index n (AlgorithmParameters.level a K b n D)→ ℚ):
      NativeNearExecution.run flow G D k (AlgorithmParameters.sparsity a K b n D) b
        (AlgorithmParameters.load b n D) (MomentLP.decode x)
        (fun C t => RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t) =
      NearOracle.run flow a K b D G k (MomentLP.decode x)
        (fun C t => (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t).map
          (fun I => I.image (label C))):=by rfl
  cases he:RationalProjection.classify (MomentLP.program G k (AlgorithmParameters.level a K b n D))
      (ProjectedOracle.tolerance a K b n D)
      (RegisteredLP.certificate lp (DistanceProjection.distanceProgram
        (MomentLP.program G k (AlgorithmParameters.level a K b n D)) (ProjectedOracle.raw center))) <;>
    simp only [reply,ProjectedOracle.run,he,near_eq,NativeComponentNormal.normal] <;> rfl

end Lax263307Proofs.NativeOracleExecution

end

section

namespace Lax263307Proofs.NativeOraclePrecision

open Lax263307 Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime

theorem height_mono (q:ℚ) (h H:ℕ) (hq:NativeRoundedStep.height q h) (hh:h≤ H):
    NativeRoundedStep.height q H:=by
  have hp:2^h≤2^H:=Nat.pow_le_pow_right (by decide) hh
  exact ⟨hq.1.trans hp,hq.2.trans hp⟩

end Lax263307Proofs.NativeOraclePrecision

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem child_variable (cfg:Config) (s:String)
    (hg:s∉NativeChildGraph.command.wvars) (hc:s∉NativeChildActivate.command.wvars)
    (he:s∉(NativeChildCall.enter 1).wvars) (hphase:s≠"machine.phase")
    (hstack:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉((phases cfg)[11]'(by change 11<16; decide)).wvars:=by
  have hsave:=NativeChildCall.save_variable (frameArrays cfg) (frameScalars cfg) s hstack
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeChildCall.command,go,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem pushed_length {B D S v t:ℕ} {cfg:Config} {extent:String→ ℕ} {front:List ℕ}
    {σ saved:Env} {c:Com} (rr:Run B c σ saved t)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S):
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved).length=
      front.length+S*(frameArrays cfg).length+(frameScalars cfg).length:=by
  have h:(NativeFrameBuffers.words (frameArrays cfg) saved).length=S*(frameArrays cfg).length:=
    NativeFrameBuffers.words_length _ S saved (fun a ha => by rw [RamFrames.run_array_length rr,hc.lengths]; exact hext a ha)
  simp only [List.length_append,NativeRecursionFrame.words,NativeFrameScalars.words,List.length_map,h,Nat.add_assoc]

theorem child_entry {B D S v t cost:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ saved entry:Env} {c:Com} (snapshot:Run B c σ saved t)
    (call:Segment B (phases cfg) 1 cost σ entry)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S)
    (hp:σ.vars "machine.phase"=11)
    (hfront:Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry)
    (hwords:entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length):
    Protocol B D S v cfg extent
      (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry:=by
  have rr:=NativeMachineFrame.single_run call ⟨11,by change 11<16; decide⟩ hp
  refine ⟨NativeMachineBounds.state call hc.bounded,?_,hfront,?_,?_,?_,?_,?_⟩
  · intro a; rw [NativeMachineFrame.array_length call]; exact hc.lengths a
  · rw [pushed_length snapshot hc hext]; exact hwords
  all_goals apply (rr.frame_var _ (child_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide))).trans
  all_goals first | exact hc.stride | exact hc.frameLength | exact hc.roundWidth | exact hc.accuracy

theorem children {n:ℕ} (B D fuel S v childSteps childTime:ℕ) (cfg:Config)
    (lp flow:List ℕ→ List ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent:String→ ℕ) (front:List ℕ) (eligible:Eligible)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (ih:Executes B D fuel S v childSteps childTime cfg lp flow extent eligible):
    Children B D fuel S v childSteps childTime cfg G extent front eligible
      (fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (ComputedSeparators.restriction G C) t):=by
  intro C target σ hel hp phase saved entry snapshot call hfront hwords hgraph horder hk hf hr he
  have protocolEntry:=child_entry cfg snapshot call hp hext phase hfront hwords
  have hlength:=pushed_length snapshot hp hext
  obtain ⟨τ,s,t,trace,hs,ht,answer,protocolDone,rootDone,graphDone⟩:=ih C.card (ComputedSeparators.restriction G C) target
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry
    (by simpa only [hlength] using hel) ⟨protocolEntry,horder,hgraph,hk,hf⟩ hr he
  exact ⟨τ,s,t,trace,hs,ht,answer,protocolDone.stack,
    by simpa only [hlength] using protocolDone.cursor,protocolDone.frameLength,protocolDone.stride⟩

end Lax263307Proofs.NativeNodeProtocol

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRoundedResources

open Lax263307 RoundedOracleSearch Matrix

theorem input_words {N:ℕ} (j H B:ℕ) (state:State N) (a:Fin N→ ℤ)
    (hN:N< B) (hj:j< B) (h1:1< B) (hH:2^H< B)
    (hs:∀ i k,NativeRoundedStep.height (state.1 i k) H)
    (ha:∀ i,NativeRoundedStep.height (rationalNormal a i) H)
    (hc:∀ i,NativeRoundedStep.height (state.2 i) H):
    ∀ z∈NativeRoundedStep.encodeInput j state a,z< B:=by
  have vec:=NativeRationalBounds.vector_words B (2^H) N
  intro z hz
  change z∈[N,j]++NativeRoundedQuery.shape state++NativeRoundedQuery.normal a++
    NativeRoundedQuery.center state at hz
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with (((rfl|rfl)|hz)|hz)|hz
  · exact hN
  · exact hj
  · simp only [NativeRoundedQuery.shape,List.mem_flatten,List.mem_ofFn] at hz
    obtain ⟨row,⟨i,rfl⟩,hz⟩:=hz
    exact vec (state.1 i) h1 hH (hs i) z hz
  · exact vec (rationalNormal a) h1 hH ha z hz
  · exact vec state.2 h1 hH hc z hz

theorem bounds {N:ℕ} (p:Lax808846.Ram.Program) (c H v m j limit R w:ℕ)
    (extent:String→ ℕ) (state:State N) (a:Fin N→ ℤ)
    (hN:2≤ N) (hH:1≤ H) (hNR:N≤ R) (hmR:m≤ R) (hjR:j≤ R) (hlR:limit≤ R)
    (hs:∀ i k,NativeRoundedStep.height (state.1 i k) H)
    (ha:∀ i,NativeRoundedStep.height (rationalNormal a i) H)
    (hc:∀ i,NativeRoundedStep.height (state.2 i) H)
    (positive:0< dotProduct (rationalNormal a) (state.1 *ᵥ rationalNormal a))
    (hv:c*(2*R+H+1)^12≤ v) (hw:wordHeight p v R H≤ w)
    (room:∀ s∈buffers,space c R H≤ extent s):
    NativeOracleRounds.Bounds (2^w) c H v m j limit p extent state a:=by
  have hNN:N*N≤ R*R:=Nat.mul_self_le_mul_self hNR
  have ht:c*(N+H+j+1)^12≤ c*(2*R+H+1)^12:=Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) 12)
  have hsize:=NativeRoundedUpdate.input_length j state a
  have hbase:2*v+H+Lax455465Proofs.RamVirtualConstants.allowance p+3*R*R+8*R+100≤ w:=hw
  have wlt:w<2^w:=Nat.lt_two_pow_self
  have hwords:2^H<2^w:=Nat.pow_lt_pow_right (by decide) (by omega)
  have hhost:2*(2^v)^2+3<2^w:=by
    have hp:2^(2*v+4)≤2^w:=Nat.pow_le_pow_right (by decide) (by omega)
    have he:2^(2*v+4)=16*(2^v)^2:=by
      rw [pow_add,Nat.mul_comm 2 v,pow_mul]; norm_num; ring
    rw [he] at hp
    have hpos:=Nat.one_le_pow v 2 (by decide)
    nlinarith only [hp,hpos]
  have hnonneg:=Nat.zero_le (c*(2*R+H+1)^12)
  have hroom (s:String) (hs:s∈buffers):
      c*(2*R+H+1)^12+3*R*R+6*R+10≤ extent s:=room s hs
  refine ⟨hN,hH,hs,ha,hc,positive,ht.trans hv,hhost,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (by omega:c*(N+H+j+1)^12+1≤ w).trans_lt wlt
  · exact (by omega:Lax455465Proofs.RamVirtualConstants.allowance p≤ w).trans_lt wlt
  · rw [hsize]
    exact (by nlinarith only [hNN,hNR,hbase]:2+3*(N*N)+6*N+3≤ w).trans_lt wlt
  · exact (by omega:m+j+limit+4+14+10≤ w).trans_lt wlt
  · exact input_words j H (2^w) state a (by omega) (by omega) (by omega) hwords hs ha hc
  · have h:=hroom "lp.word" (by simp [buffers]); rw [hsize]; nlinarith only [h,hNN,hNR,hnonneg]
  · have h:=hroom "vm.input" (by simp [buffers]); rw [hsize]; nlinarith only [h,hNN,hNR,hnonneg]
  · have h:=hroom "vm.addresses" (by simp [buffers]); omega
  · have h:=hroom "vm.values" (by simp [buffers]); omega
  · have h:=hroom "vm.output" (by simp [buffers]); omega
  · have h:=hroom "round.shape" (by simp [buffers]); nlinarith only [h,hNN,hnonneg]
  · have h:=hroom "round.center" (by simp [buffers]); omega

end Lax263307Proofs.NativeRoundedResources

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedRounds

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch Matrix
open NativeCoreMachine

theorem rounded_cost_mono (p:Lax808846.Ram.Program) (c n N h j J:ℕ) (hn:n≤ N) (hj:j≤ J):
    NativeRoundedUpdate.timeBound p c n h j≤ NativeRoundedUpdate.timeBound p c N h J:=by
  dsimp only [NativeRoundedUpdate.timeBound,NativeRawOracle.cost]
  gcongr

theorem near_time_affine (cfg:Config) (n r M S h childTime flowTime:ℕ):
    NativeNearExecution.timeBound cfg n r M S h childTime flowTime=
      NativeNearExecution.timeBound cfg n r M S h 0 flowTime+(n+1)*childTime:=by
  dsimp only [NativeNearExecution.timeBound,NativeCollectionExecution.partCost]
  ring

theorem rounds {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} (p:NativeSelectedLP.Program lp) (q:NativeSelectedNear.Program flow)
    (cfg:Config) (hpc:p.code=cfg.lp) (hpcoeff:p.coeff=cfg.lpWidth)
    (hqc:q.code=cfg.flow) (hqcoeff:q.coeff=cfg.flowWidth)
    (encoded:NativeEncodedLP.Encoded lp) (hsep:NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b)
    (correct:NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b) (hK:0< cfg.K) (hb:0< cfg.b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v c R w rootN capacity childSteps childTime:ℕ)
    (extent:String→ ℕ) (front:List ℕ)
    (hi:NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length)
      capacity (fuel+1) n G k front.length)
    (hn:1< n) (hD:4≤ D) (hlarge:cutoff cfg.a cfg.K cfg.b n D< k)
    (program:NativeOracleRounds.Program cfg.rounded c)
    (bounds:Bounds cfg p q G D k fuel S v c R w extent front):
    NativeRecursiveSetup.Rounds (r:=level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D)
      (F cfg n D) fuel S v (limit cfg n D) w (2^(100*(R+1))) (2^(2*H p R+1)) (2^H p R) (2*H p R)
      (R+1) (space cfg p q n D k R) (NativeSelectedLP.oracleTime p R) (NativeSelectedLP.callCost p R)
      (flowTime cfg p q n D k R) childSteps childTime c (NativeOraclePrecision.roundedHeight p.width R)
      (oracleLocal cfg p q n D k R S+(n+1)*childTime) (roundCost cfg p c R)
      cfg G lp flow extent front (NativeNodeExecution.child cfg lp flow D fuel G)
      (NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length) capacity):=by
  let oracle:=NativeOracleRounds.oracle (r:=level cfg n D) lp flow G D k
    (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D) (F cfg n D)
    (NativeNodeExecution.child cfg lp flow D fuel G)
  have heq:oracle=fun (_:ℕ) center => ProjectedOracle.run lp flow cfg.a cfg.K cfg.b D G k
      (NativeRecursiveOracle.child lp flow cfg.a cfg.K cfg.b D fuel G) center:=by
    funext j center
    exact NativeOracleExecution.actual_reply lp flow cfg.a cfg.K cfg.b D k fuel G center
  have hdepth:RecursionDepth.depth n≤ fuel+1:=hi.2.2.2.2.2.1
  have hdim:2≤ N cfg n D:=Lax263307Proofs.CoordinateCatalog.catalog_two n (level cfg n D) (by omega)
  have hfloor:0< F cfg n D:=by
    apply Nat.pow_pos
    unfold floorDenominator sparsity targetThreshold load logarithm
    positivity
  have trajectory (j:ℕ) (hj:j< limit cfg n D):
      (∀ i l,NativeRoundedStep.height ((trajectory oracle j).1 i l) (80*(R+1)))∧
      (∀ i,NativeRoundedStep.height ((trajectory oracle j).2 i) (80*(R+1)))∧
      ∀ normal,oracle j (trajectory oracle j).2=.cut normal→
        0< dotProduct (rationalNormal normal) ((trajectory oracle j).1 *ᵥ rationalNormal normal):=by
    have h:=NativeRecursiveOracle.trajectory_guards hereditary correct G hi.1 hn D k fuel R j hD hlarge hdepth
      bounds.dimensionR (by have hh:=bounds.roundsR; omega)
    simpa only [heq] using h
  refine ⟨program,?_,?_,?_,?_⟩
  · intro j hj
    exact NativeSelectedOracle.setup hereditary p q cfg hpc hpcoeff hqc hqcoeff encoded hsep hK hb G
      D k fuel S v R (F cfg n D) w rootN capacity childSteps childTime extent front hi hn hD hfloor hlarge
      bounds.nR bounds.kR bounds.levelR bounds.denominatorR bounds.floorR bounds.dimensionR
      (RoundedOracleSearch.trajectory oracle j) (trajectory j hj).2.1 bounds.projection bounds.near
      bounds.lpWidth bounds.farWidth bounds.queryRoom bounds.flowWidth bounds.flowSpace _
  · intro j hj normal hnormal
    have heights:=trajectory j hj
    have hnormalHeight:=NativeOracleCutHeight.normal_height hsep hK hb encoded p G hi.1 D k R (F cfg n D) j
      (by omega) hD hlarge bounds.nR bounds.kR bounds.levelR bounds.dimensionR
      (RoundedOracleSearch.trajectory oracle j).2 heights.2.1 _ normal hnormal
    have hroundH:1≤ NativeOraclePrecision.roundedHeight p.width R:=by
      dsimp only [NativeOraclePrecision.roundedHeight]; omega
    have hheight:80*(R+1)≤ NativeOraclePrecision.roundedHeight p.width R:=by
      dsimp only [NativeOraclePrecision.roundedHeight]; omega
    exact NativeRoundedResources.bounds cfg.rounded c _ v n j (limit cfg n D) R w extent
      (RoundedOracleSearch.trajectory oracle j) normal hdim hroundH bounds.dimensionR bounds.nR
      (by have hh:=bounds.roundsR; omega) bounds.roundsR
      (fun i l => NativeOraclePrecision.height_mono _ _ _ (heights.1 i l) hheight) hnormalHeight
      (fun i => NativeOraclePrecision.height_mono _ _ _ (heights.2.1 i) hheight)
      (heights.2.2 normal hnormal) bounds.roundedWidth bounds.roundedHost bounds.roundedSpace
  · rw [NativeMomentInput.input_length,near_time_affine]
    dsimp only [oracleLocal,N]
    omega
  · intro j hj
    exact Nat.add_le_add_right (rounded_cost_mono cfg.rounded c (N cfg n D) R _ j R bounds.dimensionR
      (by have hh:=bounds.roundsR; omega)) 16

end Lax263307Proofs.NativeSelectedRounds

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} (p:Lax263307Proofs.NativeSelectedLP.Program lp)
      (q:Lax263307Proofs.NativeSelectedNear.Program flow) (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp p) cfg.lp→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp p) cfg.lpWidth→
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow q) cfg.flow→
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow q) cfg.flowWidth→
              Lax263307Proofs.NativeEncodedLP.Encoded lp→
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
                  Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b→
                    Nat.lt ((0:Nat)) cfg.K→
                      Nat.lt ((0:Nat)) cfg.b→
                        ∀ {n:Nat} (G:SimpleGraph (Fin n))
                          [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                          (D k fuel S v c R w rootN capacity childSteps childTime:Nat) (extent:String→ Nat)
                          (front:List Nat),
                          Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                              (Nat.add
                                (Nat.mul S
                                  (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                              capacity
                              (Nat.add fuel
                                ((1:Nat)))
                              n G k (@List.length Nat front)→
                            Nat.lt ((1:Nat)) n→
                              Nat.le ((4:Nat)) D→
                                Nat.lt (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k→
                                  Lax263307Proofs.NativeOracleRounds.Program cfg.rounded c→
                                    @Lax263307Proofs.NativeSelectedRounds.Bounds lp flow cfg p q n G inst D k fuel S v c
                                        R w extent front→
                                      @Lax263307Proofs.NativeRecursiveSetup.Rounds n
                                        (Lax263307Proofs.NativeSelectedRounds.level cfg n D) D k
                                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                                        (Lax263307.AlgorithmParameters.load cfg.b n D)
                                        (Lax263307Proofs.NativeSelectedRounds.F cfg n D) fuel S v
                                        (Lax263307Proofs.NativeSelectedRounds.limit cfg n D) w
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat))
                                          (Nat.mul
                                            ((100:Nat))
                                            (Nat.add R
                                              ((1:Nat)))))
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat))
                                          (Nat.add
                                            (Nat.mul
                                              ((2:Nat))
                                              (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                            ((1:Nat))))
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat))
                                          (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                        (Nat.mul
                                          ((2:Nat))
                                          (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                        (Nat.add R
                                          ((1:Nat)))
                                        (@Lax263307Proofs.NativeSelectedRounds.space lp flow cfg p q n D k R)
                                        (@Lax263307Proofs.NativeSelectedLP.oracleTime lp p R)
                                        (@Lax263307Proofs.NativeSelectedLP.callCost lp p R)
                                        (@Lax263307Proofs.NativeSelectedRounds.flowTime lp flow cfg p q n D k R)
                                        childSteps childTime c
                                        (Lax263307Proofs.NativeOraclePrecision.roundedHeight
                                          (@Lax263307Proofs.NativeSelectedLP.Program.width lp p) R)
                                        (Nat.add
                                          (@Lax263307Proofs.NativeSelectedRounds.oracleLocal lp flow cfg p q n D k R S)
                                          (Nat.mul
                                            (Nat.add n
                                              ((1:Nat)))
                                            childTime))
                                        (@Lax263307Proofs.NativeSelectedRounds.roundCost lp cfg p c R) cfg G inst lp
                                        flow extent front
                                        (@Lax263307Proofs.NativeNodeExecution.child n cfg lp flow D fuel G inst)
                                        (Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                                          (Nat.add
                                            (Nat.mul S
                                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                            (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                          capacity):= @Lax263307Proofs.NativeSelectedRounds.rounds
