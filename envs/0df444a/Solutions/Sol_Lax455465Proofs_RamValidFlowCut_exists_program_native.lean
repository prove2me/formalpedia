-- Prove2me | solution 1 for Lax455465Proofs.RamValidFlowCut.exists_program_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:30:09.161526+00:00
-- url     : https://prove2.me/submissions/6c0b49d8-023c-4423-819a-9222211bb2a5

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax455465Proofs_RamRoundAndOutput_command_spec
import Theorems.Thm_Lax455465Proofs_RamInputMetricCost_exists_program_native

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

namespace Lax455465Proofs.RamInputMetricCost
end Lax455465Proofs.RamInputMetricCost
theorem Lax455465Proofs.RamInputMetricCost.exists_program:∃ (c:Lax808846Proofs.Imp.Com) (timeBound:@Polynomial Nat Nat.instSemiring) (wordBound:
  @Polynomial Nat Nat.instSemiring) (sourceTime:@Polynomial Nat Nat.instSemiring) (sourceWord:
  @Polynomial Nat Nat.instSemiring),
  And c.NoWrite
    (∀ {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind) (I:Lax455465.RationalEncoding.RationalInstance n),
      LE.le ((2:Nat))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I))→
        ∃ (z:Fin (Lax455465Proofs.RamFlowData.columns n)→ Rat) (y:Fin (Lax455465Proofs.RamFlowData.rows n)→ Rat)
          (hz:
          @Lax109476.LinearProgram.PrimalFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
            Rat.instPartialOrder
            (HAdd.hAdd (HMul.hMul n n)
              (HMul.hMul
                ((2:Nat))
                (HMul.hMul
                  (HMul.hMul n n) n)))
            (HAdd.hAdd ((1:Nat))
              (HMul.hMul (HMul.hMul n n)
                (HMul.hMul n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) z)
          (hy:
          @Lax109476.LinearProgram.DualFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.instPartialOrder
            (HAdd.hAdd (HMul.hMul n n)
              (HMul.hMul
                ((2:Nat))
                (HMul.hMul
                  (HMul.hMul n n) n)))
            (HAdd.hAdd ((1:Nat))
              (HMul.hMul (HMul.hMul n n)
                (HMul.hMul n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) y),
          And
            (@Eq Rat
              (@Lax109476.LinearProgram.primalValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
                (HAdd.hAdd
                  (HMul.hMul n n)
                  (HMul.hMul
                    ((2:Nat))
                    (HMul.hMul
                      (HMul.hMul n n) n)))
                (HAdd.hAdd
                  ((1:Nat))
                  (HMul.hMul
                    (HMul.hMul n n)
                    (HMul.hMul n n)))
                (@Lax455465Proofs.DirectedFlowLP.program n I) z)
              (@Lax109476.LinearProgram.dualValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
                (HAdd.hAdd
                  (HMul.hMul n n)
                  (HMul.hMul
                    ((2:Nat))
                    (HMul.hMul
                      (HMul.hMul n n) n)))
                (HAdd.hAdd
                  ((1:Nat))
                  (HMul.hMul
                    (HMul.hMul n n)
                    (HMul.hMul n n)))
                (@Lax455465Proofs.DirectedFlowLP.program n I) y))
            (And
              (Lax759944.RamPolytime.FitsInWords
                (@Polynomial.eval Nat Nat.instSemiring
                  (Lax759944.BinaryWordEncoding.bitSize
                    (@Lax109476.RationalEncoding.encodeProgram
                      (HAdd.hAdd
                        (HMul.hMul n n)
                        (HMul.hMul
                          ((2:Nat))
                          (HMul.hMul
                            (HMul.hMul n n) n)))
                      (HAdd.hAdd
                        ((1:Nat))
                        (HMul.hMul
                          (HMul.hMul n n)
                          (HMul.hMul n n)))
                      (@Lax455465Proofs.DirectedFlowLP.program n I)))
                  sourceWord)
                (@Lax109476.RationalEncoding.encodeCertificate (Lax455465Proofs.RamFlowData.rows n)
                  (Lax455465Proofs.RamFlowData.columns n)
                  (@Lax109476.RationalCertificates.Certificate.optimal (Lax455465Proofs.RamFlowData.rows n)
                    (Lax455465Proofs.RamFlowData.columns n) z y)))
              (∀ (W:Nat),
                LE.le
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      wordBound)
                    W→
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) W)
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And
                        (@Eq (List Nat) σ.inp
                          (@List.cons Nat (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                            (@Lax455465.RationalEncoding.encodeInput n kind I)))
                        (And
                          (LE.le (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                            (@List.length Nat (σ.arrs "input.data")))
                          (And
                            (LT.lt
                              (HMul.hMul
                                ((2:Nat)) n)
                              (@List.length Nat (σ.arrs "flow.weights")))
                            (And
                              (LT.lt
                                (HMul.hMul
                                  ((2:Nat))
                                  (HMul.hMul n n))
                                (@List.length Nat (σ.arrs "flow.capacities")))
                              (And
                                (LT.lt (Lax455465Proofs.RamFlowLp.wordLength n)
                                  (@List.length Nat (σ.arrs "lp.word")))
                                (And
                                  (LT.lt
                                    (@List.length Nat
                                      (@Lax109476.RationalEncoding.encodeProgram
                                        (HAdd.hAdd
                                          (HMul.hMul n n)
                                          (HMul.hMul
                                            ((2:Nat))
                                            (HMul.hMul
                                              (HMul.hMul n n) n)))
                                        (HAdd.hAdd
                                          ((1:Nat))
                                          (HMul.hMul
                                            (HMul.hMul n n)
                                            (HMul.hMul n n)))
                                        (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                    (@List.length Nat (σ.arrs "vm.input")))
                                  (And
                                    (LT.lt
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (Lax759944.BinaryWordEncoding.bitSize
                                          (@Lax109476.RationalEncoding.encodeProgram
                                            (HAdd.hAdd
                                              (HMul.hMul n n)
                                              (HMul.hMul
                                                ((2:Nat))
                                                (HMul.hMul
                                                  (HMul.hMul n n) n)))
                                            (HAdd.hAdd
                                              ((1:Nat))
                                              (HMul.hMul
                                                (HMul.hMul n n)
                                                (HMul.hMul n n)))
                                            (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                        sourceTime)
                                      (@List.length Nat (σ.arrs "vm.addresses")))
                                    (And
                                      (LT.lt
                                        (@Polynomial.eval Nat Nat.instSemiring
                                          (Lax759944.BinaryWordEncoding.bitSize
                                            (@Lax109476.RationalEncoding.encodeProgram
                                              (HAdd.hAdd
                                                (HMul.hMul n n)
                                                (HMul.hMul
                                                  ((2:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n) n)))
                                              (HAdd.hAdd
                                                ((1:Nat))
                                                (HMul.hMul
                                                  (HMul.hMul n n)
                                                  (HMul.hMul n n)))
                                              (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                          sourceTime)
                                        (@List.length Nat (σ.arrs "vm.values")))
                                      (And
                                        (LT.lt
                                          (@Polynomial.eval Nat Nat.instSemiring
                                            (Lax759944.BinaryWordEncoding.bitSize
                                              (@Lax109476.RationalEncoding.encodeProgram
                                                (HAdd.hAdd
                                                  (HMul.hMul n n)
                                                  (HMul.hMul
                                                    ((2:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n) n)))
                                                (HAdd.hAdd
                                                  ((1:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n)
                                                    (HMul.hMul n n)))
                                                (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                            sourceTime)
                                          (@List.length Nat (σ.arrs "vm.output")))
                                        (And
                                          (LT.lt
                                            (HMul.hMul
                                              ((2:Nat))
                                              (Lax455465Proofs.RamFlowData.columns n))
                                            (@List.length Nat (σ.arrs "flow.primal")))
                                          (And
                                            (LT.lt
                                              (HMul.hMul
                                                ((2:Nat))
                                                (Lax455465Proofs.RamFlowData.rows n))
                                              (@List.length Nat (σ.arrs "flow.dual")))
                                            (And
                                              (LT.lt
                                                (HMul.hMul
                                                  ((2:Nat))
                                                  (HMul.hMul n n))
                                                (@List.length Nat (σ.arrs "metric.old")))
                                              (LT.lt
                                                (HMul.hMul
                                                  ((2:Nat))
                                                  (HMul.hMul n n))
                                                (@List.length Nat (σ.arrs "metric.new")))))))))))))))
                    c
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamFlowData.Data n I τ)
                        (And (@Eq Nat (τ.vars "metric.n") n)
                          (And (@Eq Nat (τ.vars "metric.n2") (HMul.hMul n n))
                            (And (@Eq Nat (τ.vars "flow.kind") (Lax455465Proofs.RamGraphHeader.tag kind))
                              (And
                                (Lax455465Proofs.RamVirtualState.Prefix
                                  (Lax455465Proofs.RamUnsignedBuffer.encode
                                    (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.columns n) z
                                      (@And.left
                                        (∀
                                          (j:
                                            Fin
                                              (HAdd.hAdd
                                                ((1:Nat))
                                                (HMul.hMul
                                                  (HMul.hMul n n)
                                                  (HMul.hMul n n)))),
                                          @LE.le Rat
                                            (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                            (@OfNat.ofNat Rat (nat_lit 0)
                                              (@Zero.toOfNat0 Rat
                                                (@MulZeroClass.toZero Rat
                                                  (@instMulZeroClassOfSemiring Rat
                                                    (@Ring.toSemiring Rat
                                                      (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                            (z j))
                                        (∀
                                          (i:
                                            Fin
                                              (HAdd.hAdd
                                                (HMul.hMul n n)
                                                (HMul.hMul
                                                  ((2:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n) n)))),
                                          @LE.le Rat
                                            (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                            (@Lax109476.LinearProgram.rowValue Rat
                                              (@DivisionRing.toRing Rat Rat.instDivisionRing)
                                              (HAdd.hAdd
                                                (HMul.hMul n n)
                                                (HMul.hMul
                                                  ((2:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n) n)))
                                              (HAdd.hAdd
                                                ((1:Nat))
                                                (HMul.hMul
                                                  (HMul.hMul n n)
                                                  (HMul.hMul n n)))
                                              (@Lax455465Proofs.DirectedFlowLP.program n I) z i)
                                            (@Lax109476.LinearProgram.Program.b Rat
                                              (HAdd.hAdd
                                                (HMul.hMul n n)
                                                (HMul.hMul
                                                  ((2:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n) n)))
                                              (HAdd.hAdd
                                                ((1:Nat))
                                                (HMul.hMul
                                                  (HMul.hMul n n)
                                                  (HMul.hMul n n)))
                                              (@Lax455465Proofs.DirectedFlowLP.program n I) i))
                                        hz)))
                                  "flow.primal" τ)
                                (And
                                  (Lax455465Proofs.RamVirtualState.Prefix
                                    (Lax455465Proofs.RamUnsignedBuffer.encode
                                      (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.rows n) y
                                        (@And.left
                                          (∀
                                            (i:
                                              Fin
                                                (HAdd.hAdd
                                                  (HMul.hMul n n)
                                                  (HMul.hMul
                                                    ((2:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n) n)))),
                                            @LE.le Rat
                                              (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                              (@OfNat.ofNat Rat (nat_lit 0)
                                                (@Zero.toOfNat0 Rat
                                                  (@MulZeroClass.toZero Rat
                                                    (@instMulZeroClassOfSemiring Rat
                                                      (@Ring.toSemiring Rat
                                                        (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                              (y i))
                                          (∀
                                            (j:
                                              Fin
                                                (HAdd.hAdd
                                                  ((1:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n)
                                                    (HMul.hMul n n)))),
                                            @LE.le Rat
                                              (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                              (@Lax109476.LinearProgram.Program.c Rat
                                                (HAdd.hAdd
                                                  (HMul.hMul n n)
                                                  (HMul.hMul
                                                    ((2:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n) n)))
                                                (HAdd.hAdd
                                                  ((1:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n)
                                                    (HMul.hMul n n)))
                                                (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                              (@Lax109476.LinearProgram.columnValue Rat
                                                (@DivisionRing.toRing Rat Rat.instDivisionRing)
                                                (HAdd.hAdd
                                                  (HMul.hMul n n)
                                                  (HMul.hMul
                                                    ((2:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n) n)))
                                                (HAdd.hAdd
                                                  ((1:Nat))
                                                  (HMul.hMul
                                                    (HMul.hMul n n)
                                                    (HMul.hMul n n)))
                                                (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                          hy)))
                                    "flow.dual" τ)
                                  (And
                                    (Lax455465Proofs.RamVirtualState.Prefix
                                      (Lax455465Proofs.RamUnsignedBuffer.encode
                                        (@Lax455465Proofs.MetricMatrix.values n
                                          (@Lax455465Proofs.RamDualDistances.result n y
                                            (@And.left
                                              (∀
                                                (i:
                                                  Fin
                                                    (HAdd.hAdd
                                                      (HMul.hMul n n)
                                                      (HMul.hMul
                                                        ((2:Nat))
                                                        (HMul.hMul
                                                          (HMul.hMul n n) n)))),
                                                @LE.le Rat
                                                  (@Preorder.toLE Rat
                                                    (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                  (@OfNat.ofNat Rat (nat_lit 0)
                                                    (@Zero.toOfNat0 Rat
                                                      (@MulZeroClass.toZero Rat
                                                        (@instMulZeroClassOfSemiring Rat
                                                          (@Ring.toSemiring Rat
                                                            (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                                  (y i))
                                              (∀
                                                (j:
                                                  Fin
                                                    (HAdd.hAdd
                                                      ((1:Nat))
                                                      (HMul.hMul
                                                        (HMul.hMul n n)
                                                        (HMul.hMul n n)))),
                                                @LE.le Rat
                                                  (@Preorder.toLE Rat
                                                    (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                  (@Lax109476.LinearProgram.Program.c Rat
                                                    (HAdd.hAdd
                                                      (HMul.hMul n n)
                                                      (HMul.hMul
                                                        ((2:Nat))
                                                        (HMul.hMul
                                                          (HMul.hMul n n) n)))
                                                    (HAdd.hAdd
                                                      ((1:Nat))
                                                      (HMul.hMul
                                                        (HMul.hMul n n)
                                                        (HMul.hMul n n)))
                                                    (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                                  (@Lax109476.LinearProgram.columnValue Rat
                                                    (@DivisionRing.toRing Rat Rat.instDivisionRing)
                                                    (HAdd.hAdd
                                                      (HMul.hMul n n)
                                                      (HMul.hMul
                                                        ((2:Nat))
                                                        (HMul.hMul
                                                          (HMul.hMul n n) n)))
                                                    (HAdd.hAdd
                                                      ((1:Nat))
                                                      (HMul.hMul
                                                        (HMul.hMul n n)
                                                        (HMul.hMul n n)))
                                                    (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                              hy))))
                                      "metric.old" τ)
                                    (Lax455465Proofs.RamUnsignedScalar.Stored "round.cost"
                                      (@Lax455465Proofs.MetricCostData.cost n I
                                        (@Lax455465Proofs.RamDualDistances.result n y
                                          (@And.left
                                            (∀
                                              (i:
                                                Fin
                                                  (HAdd.hAdd
                                                    (HMul.hMul n n)
                                                    (HMul.hMul
                                                      ((2:Nat))
                                                      (HMul.hMul
                                                        (HMul.hMul n n) n)))),
                                              @LE.le Rat
                                                (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                (@OfNat.ofNat Rat (nat_lit 0)
                                                  (@Zero.toOfNat0 Rat
                                                    (@MulZeroClass.toZero Rat
                                                      (@instMulZeroClassOfSemiring Rat
                                                        (@Ring.toSemiring Rat
                                                          (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                                (y i))
                                            (∀
                                              (j:
                                                Fin
                                                  (HAdd.hAdd
                                                    ((1:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n)
                                                      (HMul.hMul n n)))),
                                              @LE.le Rat
                                                (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                (@Lax109476.LinearProgram.Program.c Rat
                                                  (HAdd.hAdd
                                                    (HMul.hMul n n)
                                                    (HMul.hMul
                                                      ((2:Nat))
                                                      (HMul.hMul
                                                        (HMul.hMul n n) n)))
                                                  (HAdd.hAdd
                                                    ((1:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n)
                                                      (HMul.hMul n n)))
                                                  (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                                (@Lax109476.LinearProgram.columnValue Rat
                                                  (@DivisionRing.toRing Rat Rat.instDivisionRing)
                                                  (HAdd.hAdd
                                                    (HMul.hMul n n)
                                                    (HMul.hMul
                                                      ((2:Nat))
                                                      (HMul.hMul
                                                        (HMul.hMul n n) n)))
                                                  (HAdd.hAdd
                                                    ((1:Nat))
                                                    (HMul.hMul
                                                      (HMul.hMul n n)
                                                      (HMul.hMul n n)))
                                                  (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                            hy)))
                                      τ))))))))
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      timeBound)))):= @Lax455465Proofs.RamInputMetricCost.exists_program_native

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

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

theorem Run.seq {B:ℕ} {c d:Com} {σ σ' σ'':Env} {K K':ℕ}
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):Run B (.seq c d) σ σ'' (K + K'):=by
  obtain ⟨k,hk,hbs⟩:=h
  obtain ⟨k',hk',hbs'⟩:=h'
  exact ⟨k + k',by omega, .seq hbs hbs'⟩

theorem _root_.Lax808846Proofs.Imp.BigStep.out_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k):c.NoWrite→ σ'.out=σ.out:=by
  induction h with
  | skip => intro _; rfl
  | assign _ => intro _; rfl
  | store _ _ _ => intro _; rfl
  | seq _ _ ih ih' => intro hc; rw [ih' hc.2,ih hc.1]
  | ite_true _ _ ih => intro hc; exact ih hc.1
  | ite_false _ _ ih => intro hc; exact ih hc.2
  | while_true _ _ _ ih ih' => intro hc; rw [ih' hc,ih hc]
  | while_false _ => intro _; rfl
  | read _ => intro _; rfl
  | write _ => intro hc; exact absurd hc not_false

theorem Run.out_eq {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hc:c.NoWrite):σ'.out=σ.out:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.out_eq hc

end Lax808846Proofs.Reasoning

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem bitSize_append (xs ys:List ℕ):bitSize (xs ++ ys)=bitSize xs + bitSize ys:=by
  simp [bitSize,encode]

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

end Lax455465Proofs.WordSize

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

open scoped NNRat

namespace Lax455465Proofs.InstanceParser

open Lax455465.RationalEncoding Lax455465.ProductNetwork RationalParser

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

theorem program_heights {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    let M:=2 ^ bitSize (encodeInput kind I)
    (∀ i j,Height (M * M) ((program I).A i j))∧
    (∀ i,Height (M * M) ((program I).b i))∧
    (∀ j,Height (M * M) ((program I).c j)):=by
  dsimp only
  let M:=2 ^ bitSize (encodeInput kind I)
  have hM:1≤ M:=by have:=Nat.two_pow_pos (bitSize (encodeInput kind I)); omega
  have hMM:1≤ M * M:=by nlinarith
  refine ⟨fun i j => coefficient_height I M hM (weight_height kind I) _ _, ?_, ?_⟩
  · intro i
    dsimp only [program,rowBound]
    cases (rowIndex n).symm i with
    | inl e => exact height_mono (capacity_height kind I e.1 e.2) (by nlinarith)
    | inr _ => exact height_zero hMM
  · intro j
    dsimp only [program,objective]
    cases (variableIndex n).symm j with
    | inl _ => exact height_one hMM
    | inr _ => exact height_zero hMM

theorem rational_size (q:ℚ) (K:ℕ) (h:Height (2 ^ K) q):
    bitSize (Lax109476.RationalEncoding.encodeRational q)≤ 2 * K + 6:=by
  have hp:2 ^ K < 2 ^ (K + 1):=by rw [pow_succ]; have:=Nat.two_pow_pos K; omega
  have hn:=Nat.size_le.mpr (h.1.trans_lt hp)
  have hd:=Nat.size_le.mpr (h.2.trans_lt hp)
  simp only [Lax109476.RationalEncoding.encodeRational,WordSize.bitSize_cons,WordSize.bitSize_nil]
  split_ifs <;> simp only [Nat.size_one,Nat.size_zero] <;> omega

private theorem rational_list_size (qs:List ℚ) (K:ℕ)
    (h:∀ q∈ qs,Height (2 ^ K) q):
    bitSize (qs.flatMap Lax109476.RationalEncoding.encodeRational)≤ qs.length * (2 * K + 6):=by
  induction qs with
  | nil => simp [WordSize.bitSize_nil]
  | cons q qs ih =>
    have hq:=rational_size q K (h q List.mem_cons_self)
    have ht:=ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    simp only [List.flatMap_cons,WordSize.bitSize_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem encoded_program_size {m n:ℕ} (P:Lax109476.LinearProgram.Program ℚ m n) (K:ℕ)
    (hA:∀ i j,Height (2 ^ K) (P.A i j)) (hb:∀ i,Height (2 ^ K) (P.b i))
    (hc:∀ j,Height (2 ^ K) (P.c j)):
    bitSize (Lax109476.RationalEncoding.encodeProgram P)≤
      m.size + n.size + 2 + (m * n + m + n) * (2 * K + 6):=by
  have hmat:∀ q∈ (List.ofFn fun i => List.ofFn (P.A i)).flatten,Height (2 ^ K) q:=by
    intro q hq
    obtain ⟨row,hrow,hq⟩:=List.mem_flatten.mp hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hrow
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq
    exact hA i j
  have hmatrix:=rational_list_size _ K hmat
  have hrowlength:(List.ofFn fun i => List.ofFn (P.A i)).flatten.length=m * n:=by
    simp [List.length_flatten,Function.comp_def,List.ofFn_const]
  rw [hrowlength] at hmatrix
  have hbsize:=rational_list_size (List.ofFn P.b) K (by
    intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq; exact hb i)
  have hcsize:=rational_list_size (List.ofFn P.c) K (by
    intro q hq; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq; exact hc j)
  simp only [List.length_ofFn] at hbsize hcsize
  simp only [Lax109476.RationalEncoding.encodeProgram,Lax109476.RationalEncoding.encodeVector,
    WordSize.bitSize_append,WordSize.bitSize_cons,WordSize.bitSize_nil]
  nlinarith

theorem flow_program_size {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I))≤
      128 * (bitSize (encodeInput kind I) + 1) ^ 8:=by
  let L:=bitSize (encodeInput kind I)
  let A:=L + 1
  let m:=n * n + 2 * ((n * n) * n)
  let v:=1 + (n * n) * (n * n)
  have hn:n≤ L:=input_dimension kind I
  have hA:1≤ A:=by omega
  have hheights:=program_heights kind I
  have hp:2 ^ L * 2 ^ L=2 ^ (2 * L):=by rw [← pow_add]; congr 1; omega
  have hencoded:=encoded_program_size (program I) (2 * L)
    (fun i j => by simpa only [← hp] using hheights.1 i j)
    (fun i => by simpa only [← hp] using hheights.2.1 i)
    (fun j => by simpa only [← hp] using hheights.2.2 j)
  have hm:m≤ 3 * A ^ 3:=by
    have hs:m≤ 3 * (n + 1) ^ 3:=by dsimp only [m]; nlinarith
    exact hs.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega:n + 1≤ A) 3))
  have hv:v≤ 2 * A ^ 4:=by
    have hs:v≤ 2 * (n + 1) ^ 4:=by dsimp only [v]; nlinarith
    exact hs.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega:n + 1≤ A) 4))
  have hpow3:A ^ 3≤ A ^ 7:=Nat.pow_le_pow_right hA (by decide)
  have hpow4:A ^ 4≤ A ^ 7:=Nat.pow_le_pow_right hA (by decide)
  have hpow7:A ^ 7≤ A ^ 8:=Nat.pow_le_pow_right hA (by decide)
  have hpowpos:1≤ A ^ 7:=by have:=pow_pos (by omega:0 < A) 7; omega
  have hmv:m * v≤ 6 * A ^ 7:=by
    have h:=Nat.mul_le_mul hm hv
    convert h using 1 <;> ring
  have hentries:m * v + m + v≤ 11 * A ^ 7:=by nlinarith
  have hms:m.size≤ m:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hvs:v.size≤ v:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hheader:m.size + v.size + 2≤ 7 * A ^ 7:=by nlinarith
  have hq:2 * (2 * L) + 6≤ 6 * A:=by omega
  have hproduct:=Nat.mul_le_mul hentries hq
  have hprodEq:(11 * A ^ 7) * (6 * A)=66 * A ^ 8:=by ring
  rw [hprodEq] at hproduct
  change bitSize (Lax109476.RationalEncoding.encodeProgram (program I))≤
    m.size + v.size + 2 + (m * v + m + v) * (2 * (2 * L) + 6) at hencoded
  have htotal:m.size + v.size + 2 + (m * v + m + v) * (2 * (2 * L) + 6)≤
      128 * A ^ 8:=by omega
  exact hencoded.trans htotal

noncomputable def sizeBound:Polynomial ℕ:=Polynomial.C 128 * (Polynomial.X + Polynomial.C 1) ^ 8

theorem sizeBound_eval (L:ℕ):sizeBound.eval L=128 * (L + 1) ^ 8:=by simp [sizeBound]

theorem flow_program_polynomial_size {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I))≤
      sizeBound.eval (bitSize (encodeInput kind I)):=by
  rw [sizeBound_eval]
  exact flow_program_size kind I

end Lax455465Proofs.LpInputSize

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem value_mono (coefficients:List ℕ) {x y:ℕ} (h:x≤ y):
    value coefficients x≤ value coefficients y:=by
  induction coefficients with
  | nil => rfl
  | cons a rest ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

theorem exists_coefficients (p:Polynomial ℕ):∃ coefficients:List ℕ,
    ∀ x:ℕ,value coefficients x=p.eval x:=by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[],fun _ => by simp [value]⟩
  · intro q a _ _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    cases coefficients with
    | nil =>
      refine ⟨[a], ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp [value]
    | cons b rest =>
      refine ⟨(b + a)::rest, ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp only [value]
      omega
  · intro q _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    refine ⟨0::coefficients, ?_⟩
    intro x
    simp only [value,Nat.zero_add,hcoeff,Polynomial.eval_mul,Polynomial.eval_X,Nat.mul_comm]

end Lax455465Proofs.RamPolynomial

end

section

namespace Lax455465Proofs.RamFlowSolverBounds

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding DirectedFlowLP

theorem eval_mono (p:Polynomial ℕ) {x y:ℕ} (h:x≤ y):p.eval x≤ p.eval y:=by
  obtain ⟨coefficients,hcoeff⟩:=RamPolynomial.exists_coefficients p
  rw [←hcoeff x,←hcoeff y]
  exact RamPolynomial.value_mono coefficients h

end Lax455465Proofs.RamFlowSolverBounds

end

section

namespace Lax455465Proofs.RamOptimalDecode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open scoped NNRat

@[simp] theorem length_vector {k:ℕ} (x:Fin k→ ℚ) (hx:∀ i,0≤ x i):
    (vector x hx).length=k:=List.length_ofFn

end Lax455465Proofs.RamOptimalDecode

end

section

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances

theorem step_le {n:ℕ} (d:Distance n) (p u v:Fin n):step d p u v≤ d u v:=
  min_le_left _ _

theorem nonnegative_step {n:ℕ} (d:Distance n) (p:Fin n) (h:Nonnegative d):
    Nonnegative (step d p):=by
  intro u v
  exact le_min (h u v) (add_nonneg (h u p) (h p v))

theorem nonnegative_iterate {n:ℕ} (d:Distance n) (pivots:List (Fin n))
    (h:Nonnegative d):Nonnegative (iterate d pivots):=by
  induction pivots generalizing d with
  | nil => exact h
  | cons p rest ih => exact ih (step d p) (nonnegative_step d p h)

theorem iterate_le {n:ℕ} (d:Distance n) (pivots:List (Fin n)) (u v:Fin n):
    iterate d pivots u v≤ d u v:=by
  induction pivots generalizing d with
  | nil => exact le_rfl
  | cons p rest ih => exact (ih (step d p)).trans (step_le d p u v)

end Lax455465Proofs.RationalDistances

end

section

namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat

theorem rational_step {n:ℕ} (d:Matrix n) (p:Fin n):
    rational (step d p)=RationalDistances.step (rational d) p:=by
  funext u v
  simp only [rational,step,RationalDistances.step,NNRat.coe_min,NNRat.coe_add]

theorem rational_iterate {n:ℕ} (d:Matrix n) (ps:List (Fin n)):
    rational (iterate d ps)=RationalDistances.iterate (rational d) ps:=by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => simpa only [iterate,RationalDistances.iterate,rational_step] using ih (step d p)

end Lax455465Proofs.MetricMatrix

end

section

namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

theorem rational_matrix {n:ℕ} (y:Fin (RamFlowData.rows n)→ ℚ) (hy:∀ i,0≤ y i):
    rational (matrix y hy)=RationalDistances.zeroDiagonal (DirectedFlowDual.length y):=rfl

end Lax455465Proofs.RamDualDistancesInit

end

section

namespace Lax455465Proofs.MetricHeight

open scoped BigOperators
open RationalDistances DirectedFlowLP

def denominator {n:ℕ} (d:Distance n):ℕ:= ∏ e:Edge n, (d e.1 e.2).den

theorem denominator_pos {n:ℕ} (d:Distance n):0 < denominator d:=by
  apply Finset.prod_pos
  intro e he
  exact Rat.den_pos _

theorem denominator_dvd {n:ℕ} (d:Distance n) (u v:Fin n):
    (d u v).den ∣ denominator d:=Finset.dvd_prod_of_mem _ (Finset.mem_univ (u,v))

theorem step_denominator {n:ℕ} (d:Distance n) (p:Fin n) (D:ℕ)
    (h:∀ u v, (d u v).den ∣ D):∀ u v, (step d p u v).den ∣ D:=by
  intro u v
  by_cases hv:d u v≤ d u p+d p v
  · rw [step,min_eq_left hv]
    exact h u v
  · rw [step,min_eq_right (le_of_not_ge hv)]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (h u p) (h p v))

theorem iterate_denominator {n:ℕ} (d:Distance n) (ps:List (Fin n)) (D:ℕ)
    (h:∀ u v, (d u v).den ∣ D):∀ u v, (iterate d ps u v).den ∣ D:=by
  induction ps generalizing d with
  | nil => exact h
  | cons p ps ih => exact ih (step d p) (step_denominator d p D h)

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

theorem iterate_height {n:ℕ} (d:Distance n) (ps:List (Fin n)) (M:ℕ)
    (hM:1≤ M) (hnonneg:Nonnegative d)
    (hnum:∀ u v, (d u v).num.natAbs≤ M):
    ∀ u v,LpInputSize.Height (M*denominator d) (iterate d ps u v):=by
  intro u v
  apply height_of_denominator _ (nonnegative_iterate d ps hnonneg u v) M (denominator d) hM
    (denominator_pos d) (iterate_denominator d ps _ (denominator_dvd d) u v)
  exact (iterate_le d ps u v).trans (value_bound _ (hnonneg u v) M (hnum u v))

theorem denominator_bound {n:ℕ} (d:Distance n) (w:ℕ)
    (hden:∀ u v, (d u v).den≤ 2^w):denominator d≤ 2^(w*(n*n)):=by
  unfold denominator
  calc
    _≤ ∏ e:Edge n,2^w:=Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun e _ => hden e.1 e.2)
    _=_:=by simp [Edge,Finset.prod_const,Nat.pow_mul]

theorem iterate_word_height {n:ℕ} (d:Distance n) (ps:List (Fin n)) (w:ℕ)
    (hnonneg:Nonnegative d)
    (hnum:∀ u v, (d u v).num.natAbs≤ 2^w)
    (hden:∀ u v, (d u v).den≤ 2^w):
    ∀ u v,LpInputSize.Height (2^(w*(n*n+1))) (iterate d ps u v):=by
  intro u v
  have hM:1≤ 2^w:=Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
  apply LpInputSize.height_mono (iterate_height d ps (2^w) hM hnonneg hnum u v)
  calc
    2^w*denominator d≤ 2^w*2^(w*(n*n)):=Nat.mul_le_mul_left _ (denominator_bound d w hden)
    _=_:=by rw [←Nat.pow_add]; congr 1; ring

theorem dual_height {n:ℕ}
    (y:Fin (n*n+2*((n*n)*n))→ ℚ) (hy:∀ i,0≤ y i) (w:ℕ)
    (hnum:∀ i, (y i).num.natAbs≤ 2^w) (hden:∀ i, (y i).den≤ 2^w)
    (ps:List (Fin n)):
    ∀ u v,LpInputSize.Height (2^(w*(n*n+1)))
      (iterate (zeroDiagonal (DirectedFlowDual.length y)) ps u v):=by
  apply iterate_word_height
  · apply nonnegative_zeroDiagonal
    intro u v
    exact hy _
  · intro u v
    unfold zeroDiagonal
    split_ifs
    · simp
    · exact hnum _
  · intro u v
    unfold zeroDiagonal
    split_ifs
    · simpa using Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
    · exact hden _

end Lax455465Proofs.MetricHeight

end

section

namespace Lax455465Proofs.RamDualDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

theorem rational_result {n:ℕ} (y:Fin (RamFlowData.rows n)→ ℚ) (hy:∀ i,0≤ y i):
    rational (result y hy)=RationalDistances.dualDistance y:=by
  simpa only [result,RamDualDistancesInit.rational_matrix,RationalDistances.dualDistance,RationalDistances.solve]
    using rational_iterate (RamDualDistancesInit.matrix y hy) (List.finRange n)

end Lax455465Proofs.RamDualDistances

end

section

namespace Lax455465Proofs.FlowDistanceBounds

open Lax455465.RationalEncoding Lax455465.ProductNetwork DirectedFlowLP
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.RamPolytime Lax759944.BinaryWordEncoding

theorem vector_height (w:ℕ) {k:ℕ} (x:Fin k→ ℚ)
    (hwords:FitsInWords w (encodeVector x)):
    ∀ i,LpInputSize.Height (2^w) (x i):=by
  intro i
  have hn:=hwords (x i).num.natAbs (List.mem_flatMap.mpr
    ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [Lax109476.RationalEncoding.encodeRational]⟩)
  have hd:=hwords (x i).den (List.mem_flatMap.mpr
    ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [Lax109476.RationalEncoding.encodeRational]⟩)
  exact ⟨Nat.le_of_lt hn,Nat.le_of_lt hd⟩

noncomputable def widthBound (sourceWord:Polynomial ℕ):Polynomial ℕ:=
  sourceWord.comp LpInputSize.sizeBound * (Polynomial.X^2+Polynomial.C 1)

theorem dual_polynomial_height (sourceWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind)
    (I:RationalInstance n) (z:Fin (RamFlowData.columns n)→ ℚ)
    (y:Fin (RamFlowData.rows n)→ ℚ) (hy:∀ i,0≤ y i)
    (hfit:FitsInWords (sourceWord.eval (bitSize (encodeProgram (program I))))
      (encodeCertificate (.optimal z y))) (ps:List (Fin n)):
    ∀ u v,LpInputSize.Height
      (2^(widthBound sourceWord).eval (bitSize (encodeInput kind I)))
      (RationalDistances.iterate (RationalDistances.zeroDiagonal (DirectedFlowDual.length y)) ps u v):=by
  let L:=bitSize (encodeInput kind I)
  let s:=bitSize (encodeProgram (program I))
  let w:=sourceWord.eval s
  have hyfit:FitsInWords w (encodeVector y):=by
    intro word hw
    exact hfit word (by simp only [encodeCertificate,List.mem_append]; exact Or.inr hw)
  have hh:=vector_height w y hyfit
  have hs:s≤ LpInputSize.sizeBound.eval L:=LpInputSize.flow_program_polynomial_size kind I
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hw:w≤ sourceWord.eval (LpInputSize.sizeBound.eval L):=RamFlowSolverBounds.eval_mono sourceWord hs
  have hexp:w*(n*n+1)≤ (widthBound sourceWord).eval L:=by
    simp only [widthBound,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
    have hnn:n*n+1≤ L^2+1:=by nlinarith
    exact Nat.mul_le_mul hw hnn
  intro u v
  apply LpInputSize.height_mono (MetricHeight.dual_height y hy w (fun i => (hh i).1) (fun i => (hh i).2) ps u v)
  exact Nat.pow_le_pow_right (by decide) hexp

end Lax455465Proofs.FlowDistanceBounds

end

section

namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n p:ℕ} (h:Room n p σ):Room n p τ:=by
  intro a count hm
  rw [RamFrames.run_array_length rr a]
  exact h a count hm

end Lax455465Proofs.RamRegionInvariant

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

namespace Lax455465Proofs.FlowPrimalHeight
open Lax455465.RationalEncoding Lax455465.ProductNetwork DirectedFlowLP
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

noncomputable def bound (sourceWord:Polynomial ℕ):Polynomial ℕ:=sourceWord.comp LpInputSize.sizeBound

theorem polynomial_height (sourceWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind)
    (I:RationalInstance n) (z:Fin (RamFlowData.columns n)→ ℚ) (y:Fin (RamFlowData.rows n)→ ℚ)
    (hfit:FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
      (Lax109476.RationalEncoding.encodeCertificate (.optimal z y))):
    ∀ i,LpInputSize.Height (2^((bound sourceWord).eval (bitSize (encodeInput kind I)))) (z i):=by
  have hzfit:FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
      (Lax109476.RationalEncoding.encodeVector z):=by
    intro word hw
    exact hfit word (by
      simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]
      exact Or.inl (Or.inr hw))
  have hs:=LpInputSize.flow_program_polynomial_size kind I
  intro i
  apply LpInputSize.height_mono (FlowDistanceBounds.vector_height _ z hzfit i)
  apply Nat.pow_le_pow_right (by decide)
  simpa only [bound,Polynomial.eval_comp] using RamFlowSolverBounds.eval_mono sourceWord hs

end Lax455465Proofs.FlowPrimalHeight

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamValidFlowCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime Lax109476.LinearProgram
open scoped NNRat

set_option maxHeartbeats 0 in

theorem exists_program:
    ∃ (c:Com) (timeBound wordBound sourceTime:Polynomial ℕ),
      ∀ {n:ℕ} (kind:EdgeKind) (I:RationalInstance n),
        (kind=.undirected→ I.network.IsUndirected)→ 2≤ supportCount I.weights→
        ∀ W:ℕ,wordBound.eval (bitSize (encodeInput kind I))≤ W→
          Spec (2^W) (fun σ => σ.inp=(encodeInput kind I).length::encodeInput kind I∧
            (encodeInput kind I).length≤ (σ.arrs "input.data").length∧
            2*n < (σ.arrs "flow.weights").length∧ 2*(n*n) < (σ.arrs "flow.capacities").length∧
            RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
            (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)).length < (σ.arrs "vm.input").length∧
            sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I))) < (σ.arrs "vm.addresses").length∧
            sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I))) < (σ.arrs "vm.values").length∧
            sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I))) < (σ.arrs "vm.output").length∧
            2*columns n < (σ.arrs "flow.primal").length∧ 2*rows n < (σ.arrs "flow.dual").length∧
            2*(n*n) < (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length∧
            RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ∧ RamRegionCut.Room n σ∧
            2*columns n < (σ.arrs "flow.converted").length∧ σ.out=[]) c
            (fun _ τ => ∃ certificate:Lax455465.FlowCutCertificate.Certificate n,
              Lax455465.FlowCutCertificate.IsValid kind I 512 certificate∧
              τ.out=Lax455465.FlowCutCertificate.encodeCertificate certificate)
            (timeBound.eval (bitSize (encodeInput kind I))):=by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsource⟩:=RamInputMetricCost.exists_program
  let metric:=FlowDistanceBounds.widthBound sourceWord
  let primal:=FlowPrimalHeight.bound sourceWord
  refine ⟨.seq c RamRoundAndOutput.command,T+RamRoundAndOutput.timeBound metric primal,
    WB+RamRoundAndOutput.wordBound metric primal,TB,?_⟩
  intro n kind I hsym hp W hW
  obtain ⟨z,y,hz,hy,hmatch,hfit,hcorrect⟩:=hsource kind I hp
  let d:=RamDualDistances.result y hy.1
  have hmetric:MetricMatrix.rational d=RationalDistances.dualDistance y:=RamDualDistances.rational_result y hy.1
  have hd:∀ u v,LpInputSize.Height (2^(metric.eval (bitSize (encodeInput kind I)))) (d u v:ℚ):=by
    intro u v
    change LpInputSize.Height _ (MetricMatrix.rational d u v)
    rw [hmetric]
    exact FlowDistanceBounds.dual_polynomial_height sourceWord kind I z y hy.1 hfit (List.finRange n) u v
  have hzheight:=FlowPrimalHeight.polynomial_height sourceWord kind I z y hfit
  have hsum:WB.eval (bitSize (encodeInput kind I))+
      (RamRoundAndOutput.wordBound metric primal).eval (bitSize (encodeInput kind I))≤ W:=by
    simpa only [Polynomial.eval_add] using hW
  rintro σ ⟨hinp,hinput,hwroom,hcroom,hlproom,hvin,hva,hvv,hvo,hpr,hdu,hOld,hNew,hregion,hcut,hconverted,hout⟩
  obtain ⟨ν,r1,hdata,hn,hn2,hkind,hprimal,hdual,hdσ,hcost⟩:=hcorrect W (by omega) σ
    ⟨hinp,hinput,hwroom,hcroom,hlproom,hvin,hva,hvv,hvo,hpr,hdu,hOld,hNew⟩
  obtain ⟨τ,r2,pr⟩:=RamRoundAndOutput.command_spec metric primal kind I z y hz hy hmatch d hmetric hd hzheight
    hp hsym W (by omega) ν
    ⟨⟨hn,hn2,hdata.2.2.2.2.2.2.1,hdata.2.2.2.2.2.2.2,hdσ,hcost⟩,
      hregion.frame r1,hcut.frame r1,
      ⟨hkind,by simpa only [RamOptimalDecode.length_vector] using hdata.2.2.2.2.1,hprimal⟩,
      by rw [RamFrames.run_array_length r1]; exact hconverted,
      (r1.out_eq hnoWrite).trans hout⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [Polynomial.eval_add]; rfl),pr⟩

end Lax455465Proofs.RamValidFlowCut

end

theorem solution:∃ (c:Lax808846Proofs.Imp.Com) (timeBound:@Polynomial Nat Nat.instSemiring) (wordBound:
  @Polynomial Nat Nat.instSemiring) (sourceTime:@Polynomial Nat Nat.instSemiring),
  ∀ {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind) (I:Lax455465.RationalEncoding.RationalInstance n),
    (@Eq Lax455465.ProductNetwork.EdgeKind kind Lax455465.ProductNetwork.EdgeKind.undirected→
        @Lax455465.ProductNetwork.Network.IsUndirected n (@Lax455465.RationalEncoding.RationalInstance.network n I))→
      Nat.le ((2:Nat))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I))→
        ∀ (W:Nat),
          Nat.le
              (@Polynomial.eval Nat Nat.instSemiring
                (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) wordBound)
              W→
            Lax808846Proofs.Reasoning.Spec
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) W)
              (fun (σ:Lax808846Proofs.Imp.Env) =>
                And
                  (@Eq (List Nat) σ.inp
                    (@List.cons Nat (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (@Lax455465.RationalEncoding.encodeInput n kind I)))
                  (And
                    (Nat.le (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (@List.length Nat (σ.arrs "input.data")))
                    (And
                      (Nat.lt
                        (Nat.mul
                          ((2:Nat)) n)
                        (@List.length Nat (σ.arrs "flow.weights")))
                      (And
                        (Nat.lt
                          (Nat.mul
                            ((2:Nat))
                            (Nat.mul n n))
                          (@List.length Nat (σ.arrs "flow.capacities")))
                        (And
                          (Nat.lt (Lax455465Proofs.RamFlowLp.wordLength n)
                            (@List.length Nat (σ.arrs "lp.word")))
                          (And
                            (Nat.lt
                              (@List.length Nat
                                (@Lax109476.RationalEncoding.encodeProgram
                                  (Nat.add
                                    (Nat.mul n n)
                                    (Nat.mul
                                      ((2:Nat))
                                      (Nat.mul
                                        (Nat.mul n n) n)))
                                  (Nat.add
                                    ((1:Nat))
                                    (Nat.mul
                                      (Nat.mul n n)
                                      (Nat.mul n n)))
                                  (@Lax455465Proofs.DirectedFlowLP.program n I)))
                              (@List.length Nat (σ.arrs "vm.input")))
                            (And
                              (Nat.lt
                                (@Polynomial.eval Nat Nat.instSemiring
                                  (Lax759944.BinaryWordEncoding.bitSize
                                    (@Lax109476.RationalEncoding.encodeProgram
                                      (Nat.add
                                        (Nat.mul n n)
                                        (Nat.mul
                                          ((2:Nat))
                                          (Nat.mul
                                            (Nat.mul n n) n)))
                                      (Nat.add
                                        ((1:Nat))
                                        (Nat.mul
                                          (Nat.mul n n)
                                          (Nat.mul n n)))
                                      (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                  sourceTime)
                                (@List.length Nat (σ.arrs "vm.addresses")))
                              (And
                                (Nat.lt
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (Lax759944.BinaryWordEncoding.bitSize
                                      (@Lax109476.RationalEncoding.encodeProgram
                                        (Nat.add
                                          (Nat.mul n n)
                                          (Nat.mul
                                            ((2:Nat))
                                            (Nat.mul
                                              (Nat.mul n n) n)))
                                        (Nat.add
                                          ((1:Nat))
                                          (Nat.mul
                                            (Nat.mul n n)
                                            (Nat.mul n n)))
                                        (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                    sourceTime)
                                  (@List.length Nat (σ.arrs "vm.values")))
                                (And
                                  (Nat.lt
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (Lax759944.BinaryWordEncoding.bitSize
                                        (@Lax109476.RationalEncoding.encodeProgram
                                          (Nat.add
                                            (Nat.mul n n)
                                            (Nat.mul
                                              ((2:Nat))
                                              (Nat.mul
                                                (Nat.mul n n) n)))
                                          (Nat.add
                                            ((1:Nat))
                                            (Nat.mul
                                              (Nat.mul n n)
                                              (Nat.mul n n)))
                                          (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                      sourceTime)
                                    (@List.length Nat (σ.arrs "vm.output")))
                                  (And
                                    (Nat.lt
                                      (Nat.mul
                                        ((2:Nat))
                                        (Lax455465Proofs.RamFlowData.columns n))
                                      (@List.length Nat (σ.arrs "flow.primal")))
                                    (And
                                      (Nat.lt
                                        (Nat.mul
                                          ((2:Nat))
                                          (Lax455465Proofs.RamFlowData.rows n))
                                        (@List.length Nat (σ.arrs "flow.dual")))
                                      (And
                                        (Nat.lt
                                          (Nat.mul
                                            ((2:Nat))
                                            (Nat.mul n n))
                                          (@List.length Nat (σ.arrs "metric.old")))
                                        (And
                                          (Nat.lt
                                            (Nat.mul
                                              ((2:Nat))
                                              (Nat.mul n n))
                                            (@List.length Nat (σ.arrs "metric.new")))
                                          (And
                                            (Lax455465Proofs.RamRegionInvariant.Room n
                                              (@Lax455465Proofs.RamRoundingInit.support n
                                                (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                              σ)
                                            (And (Lax455465Proofs.RamRegionCut.Room n σ)
                                              (And
                                                (Nat.lt
                                                  (Nat.mul
                                                    ((2:Nat))
                                                    (Lax455465Proofs.RamFlowData.columns n))
                                                  (@List.length Nat (σ.arrs "flow.converted")))
                                                (@Eq (List Nat) σ.out (@List.nil Nat))))))))))))))))))
              c
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                ∃ (certificate:Lax455465.FlowCutCertificate.Certificate n),
                  And
                    (@Lax455465.FlowCutCertificate.IsValid n kind I
                      (@OfNat.ofNat Real (nat_lit 512)
                        (@instOfNatAtLeastTwo Real (nat_lit 512) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat ((511:Nat))
                            (@Nat.instNeZeroSucc ((510:Nat))))))
                      certificate)
                    (@Eq (List Nat) τ.out (@Lax455465.FlowCutCertificate.encodeCertificate n certificate)))
              (@Polynomial.eval Nat Nat.instSemiring
                (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) timeBound):= @Lax455465Proofs.RamValidFlowCut.exists_program
