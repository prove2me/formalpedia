-- Prove2me | solution 1 for Lax455465Proofs.RamInputMetricCost.exists_program_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:12:23.628549+00:00
-- url     : https://prove2.me/submissions/92965f9d-9b6f-42c3-8467-68c1ab78bf1a

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.List.GetD
import Mathlib.Data.NNRat.BigOperators
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native
import Theorems.Thm_Lax455465Proofs_RamInputOptimal_exists_program_native
import Theorems.Thm_Lax455465Proofs_RamDualDistances_command_spec_native

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
namespace Lax455465Proofs.RamInputOptimal
end Lax455465Proofs.RamInputOptimal
theorem Lax455465Proofs.RamInputOptimal.exists_program:∃ (c:Lax808846Proofs.Imp.Com) (timeBound:@Polynomial Nat Nat.instSemiring) (wordBound:
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
                                          (LT.lt
                                            (HMul.hMul
                                              ((2:Nat))
                                              (Lax455465Proofs.RamFlowData.rows n))
                                            (@List.length Nat (σ.arrs "flow.dual")))))))))))))
                    c
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamFlowData.Data n I τ)
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
                                  (@Lax109476.RationalEncoding.encodeCertificate (Lax455465Proofs.RamFlowData.rows n)
                                    (Lax455465Proofs.RamFlowData.columns n)
                                    (@Lax109476.RationalCertificates.Certificate.optimal
                                      (Lax455465Proofs.RamFlowData.rows n) (Lax455465Proofs.RamFlowData.columns n) z y))
                                  "vm.output" τ)
                                (@Eq Nat (τ.vars "cert.cursor")
                                  (HAdd.hAdd
                                    (HAdd.hAdd
                                      ((1:Nat))
                                      (HMul.hMul
                                        ((3:Nat))
                                        (Lax455465Proofs.RamFlowData.columns n)))
                                    (HMul.hMul
                                      ((3:Nat))
                                      (Lax455465Proofs.RamFlowData.rows n)))))))))
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      timeBound)))):= @Lax455465Proofs.RamInputOptimal.exists_program_native
namespace Lax455465Proofs.RamDualDistances
end Lax455465Proofs.RamDualDistances
theorem Lax455465Proofs.RamDualDistances.command_spec:∀ (B w:Nat) {n:Nat} (y:Fin (Lax455465Proofs.RamFlowData.rows n)→ Rat)
  (hy:
    ∀ (i:Fin (Lax455465Proofs.RamFlowData.rows n)),
      @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (y i)),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (HMul.hMul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat))
                (HMul.hMul w
                  (HAdd.hAdd
                    (HMul.hMul n n)
                    ((1:Nat))))))
            ((2:Nat))))
        ((3:Nat)))
      B→
    LT.lt n B→
      LT.lt (HMul.hMul n n) B→
        LT.lt
            (HAdd.hAdd
              (HMul.hMul
                ((2:Nat))
                (HMul.hMul n n))
              ((2:Nat)))
            B→
          (∀ (i:Fin (Lax455465Proofs.RamFlowData.rows n)),
              LE.le (y i).num.natAbs
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) w))→
            (∀ (i:Fin (Lax455465Proofs.RamFlowData.rows n)),
                LE.le (y i).den
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w))→
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And (@Eq Nat (σ.vars "lp.n") n)
                    (And (@Eq Nat (σ.vars "lp.n2") (HMul.hMul n n))
                      (And
                        (Lax455465Proofs.RamVirtualState.Prefix
                          (Lax455465Proofs.RamUnsignedBuffer.encode
                            (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.rows n) y hy))
                          "flow.dual" σ)
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
                            (@List.length Nat (σ.arrs "metric.new")))))))
                Lax455465Proofs.RamDualDistances.command
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  And (@Eq Nat (τ.vars "metric.n") n)
                    (And (@Eq Nat (τ.vars "metric.n2") (HMul.hMul n n))
                      (Lax455465Proofs.RamVirtualState.Prefix
                        (Lax455465Proofs.RamUnsignedBuffer.encode
                          (@Lax455465Proofs.MetricMatrix.values n (@Lax455465Proofs.RamDualDistances.result n y hy)))
                        "metric.old" τ)))
                (HAdd.hAdd
                  (HAdd.hAdd
                    (HMul.hMul
                      ((50:Nat))
                      (HMul.hMul n n))
                    ((12:Nat)))
                  (HAdd.hAdd
                    (HMul.hMul n
                      (HAdd.hAdd
                        (HMul.hMul
                          (HAdd.hAdd
                            (HMul.hMul
                              ((72:Nat))
                              (HMul.hMul w
                                (HAdd.hAdd
                                  (HMul.hMul n n)
                                  ((1:Nat)))))
                            ((324:Nat)))
                          (HMul.hMul n n))
                        ((22:Nat))))
                    ((10:Nat)))):= @Lax455465Proofs.RamDualDistances.command_spec_native

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

namespace Lax808846Proofs.Imp

def Com.decNoWrite:(c:Com)→ Decidable c.NoWrite
  | .skip => decidable_of_iff True (by rw [Com.NoWrite])
  | .assign _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .store _ _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .seq c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .ite _ c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .while _ c =>
      have:=c.decNoWrite
      decidable_of_iff c.NoWrite (by rw [Com.NoWrite])
  | .read _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .write _ => decidable_of_iff False (by rw [Com.NoWrite])

instance:DecidablePred Com.NoWrite:=Com.decNoWrite

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

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

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

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamFlowData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat

theorem frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (h:Data I σ)
    (ha:∀ a∈ ["flow.weights","flow.capacities"],a∉ c.warrs)
    (hx:∀ x∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"],x∉ c.wvars):
    Data I τ:=by
  have hn:=hr.frame_var "lp.n" (hx _ (by simp))
  have hn2:=hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3:=hr.frame_var "lp.n3" (hx _ (by simp))
  have hrows:=hr.frame_var "lp.rows" (hx _ (by simp))
  have hcols:=hr.frame_var "lp.columns" (hx _ (by simp))
  have htotal:=hr.frame_var "lp.matrixLength" (hx _ (by simp))
  have hw:=hr.frame_arr "flow.weights" (ha _ (by simp))
  have hc:=hr.frame_arr "flow.capacities" (ha _ (by simp))
  simpa only [Data,Prefix,hn,hn2,hn3,hrows,hcols,htotal,hw,hc] using h

end Lax455465Proofs.RamFlowData

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

end Lax455465Proofs.RamVectorEncoding

end

section

namespace Lax455465Proofs.FlowLpMatrixList

open Lax109476.LinearProgram

def entry {m n:ℕ} (P:Program ℚ m n) (k:Fin (m*n)):ℚ:=
  P.A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def values {m n:ℕ} (P:Program ℚ m n):List ℚ:=List.ofFn (entry P)

theorem values_eq {m n:ℕ} (P:Program ℚ m n):
    values P=(List.ofFn fun i => List.ofFn (P.A i)).flatten:=by
  unfold values
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij:i.val*n+j.val < m*n:=calc
    _ < (i.val+1)*n:=by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left j.isLt _
    _≤ m*n:=Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr i.isLt)
  have hpair:(⟨i.val*n+j.val,hij⟩:Fin (m*n))=finProdFinEquiv (i,j):=by
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  rw [hpair]
  simp only [entry,Equiv.symm_apply_apply]

end Lax455465Proofs.FlowLpMatrixList

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

namespace Lax455465Proofs.FlowEncodingSizes

open Lax109476.LinearProgram Lax109476.RationalEncoding

theorem program_length {m n:ℕ} (P:Program ℚ m n):
    (encodeProgram P).length=2+3*(m*n+m+n):=by
  unfold encodeProgram
  rw [←FlowLpMatrixList.values_eq]
  change ([m,n] ++ RamVectorEncoding.encode (FlowLpMatrixList.values P) ++
    RamVectorEncoding.encode (List.ofFn P.b) ++ RamVectorEncoding.encode (List.ofFn P.c)).length=_
  simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,
    FlowLpMatrixList.values,List.length_ofFn]
  ring

theorem flow_length {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n):
    (encodeProgram (DirectedFlowLP.program I)).length=RamFlowLp.wordLength n:=program_length _

end Lax455465Proofs.FlowEncodingSizes

end

section

namespace Lax455465Proofs.RamHostBounds

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

@[simp] theorem length_values {n:ℕ} (d:Matrix n):(values d).length=n*n:=List.length_ofFn

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

namespace Lax455465Proofs.RamDistanceResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding

noncomputable def timeBound (sourceWord:Polynomial ℕ):Polynomial ℕ:=
  (Polynomial.X+Polynomial.C 1)^3*(Polynomial.C 72*FlowDistanceBounds.widthBound sourceWord+Polynomial.C 400)

theorem time_bound (sourceWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    let L:=bitSize (encodeInput kind I)
    let w:=sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))
    n*((72*(w*(n*n+1))+324)*(n*n)+22)+10≤ (timeBound sourceWord).eval L:=by
  dsimp only
  let L:=bitSize (encodeInput kind I)
  let w:=sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))
  let K:=(FlowDistanceBounds.widthBound sourceWord).eval L
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hs:=LpInputSize.flow_program_polynomial_size kind I
  have hw:w≤ sourceWord.eval (LpInputSize.sizeBound.eval L):=RamFlowSolverBounds.eval_mono sourceWord hs
  have hA:w*(n*n+1)≤ K:=by
    dsimp only [K,FlowDistanceBounds.widthBound]
    simp only [Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_C]
    exact Nat.mul_le_mul hw (by nlinarith)
  have hcubed:n*n*n≤ (L+1)^3:=by
    calc
      _≤ (L+1)*(L+1)*(L+1):=Nat.mul_le_mul (Nat.mul_le_mul (by omega:n≤ L+1) (by omega:n≤ L+1)) (by omega)
      _=_:=by ring
  have hmain:=Nat.mul_le_mul hcubed (Nat.add_le_add_right (Nat.mul_le_mul_left 72 hA) 324)
  have hnCube:n≤ (L+1)^3:=(by omega:n≤ L+1).trans (Nat.le_self_pow (by decide) (L+1))
  have hCubePos:1≤ (L+1)^3:=Nat.succ_le_iff.mpr (pow_pos (by omega) 3)
  have hrem:22*n+10≤ 76*(L+1)^3:=by omega
  change n*((72*(w*(n*n+1))+324)*(n*n)+22)+10≤ _
  simp only [timeBound,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
  change n*((72*(w*(n*n+1))+324)*(n*n)+22)+10≤ (L+1)^3*(72*K+400)
  nlinarith

theorem width_bound (sourceWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))*(n*n+1)≤
      (FlowDistanceBounds.widthBound sourceWord).eval (bitSize (encodeInput kind I)):=by
  let L:=bitSize (encodeInput kind I)
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hs:=LpInputSize.flow_program_polynomial_size kind I
  have hw:=RamFlowSolverBounds.eval_mono sourceWord hs
  simp only [FlowDistanceBounds.widthBound,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C]
  exact Nat.mul_le_mul hw (by change n*n+1≤ L^2+1; nlinarith)

theorem host_bound (sourceWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (W:ℕ)
    (hW:2*(FlowDistanceBounds.widthBound sourceWord).eval (bitSize (encodeInput kind I))+
      LpInputSize.sizeBound.eval (bitSize (encodeInput kind I))+20≤ W):
    let w:=sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))
    2*(2*2^(w*(n*n+1)))^2+3 < 2^W∧ n < 2^W∧ n*n < 2^W∧ 2*(n*n)+2 < 2^W:=by
  let L:=bitSize (encodeInput kind I)
  let K:=(FlowDistanceBounds.widthBound sourceWord).eval L
  let S:=LpInputSize.sizeBound.eval L
  let A:=sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))*(n*n+1)
  have hA:A≤ K:=width_bound sourceWord kind I
  have hsuff:RamHostBounds.sufficient (K+2) 0 0 (S+3)≤ W:=by
    dsimp only [RamHostBounds.sufficient]
    change 2*(K+2)+0+0+(S+3)+8≤ W
    change 2*K+S+20≤ W at hW
    omega
  obtain ⟨hv,_,_,hlen⟩:=RamHostBounds.sufficient_bounds (K+2) 0 0 (S+3) W hsuff
  have hpow:2*2^A≤ 2^(K+2):=by
    calc
      _=2^(A+1):=by rw [Nat.pow_succ]; ring
      _≤ _:=Nat.pow_le_pow_right (by decide) (by omega)
  have hword:RamFlowLp.wordLength n≤ S:=by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size kind I)
  have hn2:n*n≤ S:=by dsimp only [RamFlowLp.wordLength,RamFlowData.rows] at hword; omega
  have hn:n≤ n*n+1:=by nlinarith
  have hindex:2*(n*n)+2≤ S+3:=by dsimp only [RamFlowLp.wordLength,RamFlowData.rows] at hword; omega
  refine ⟨(Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpow 2)) 3).trans_lt hv,?_,?_,?_⟩
  · omega
  · omega
  · omega

end Lax455465Proofs.RamDistanceResources

end

section

namespace Lax455465Proofs.RamInputMetric

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax759944.RamPolytime
open Lax759944.BinaryWordEncoding
open scoped NNRat

set_option maxHeartbeats 0 in

theorem exists_program:
    ∃ (c:Com) (timeBound wordBound sourceTime sourceWord:Polynomial ℕ),
      c.NoWrite∧ ∀ {n:ℕ} (kind:EdgeKind) (I:RationalInstance n),2≤ supportCount I.weights→
        ∃ (z:Fin (columns n)→ ℚ) (y:Fin (rows n)→ ℚ)
          (hz:PrimalFeasible (program I) z) (hy:DualFeasible (program I) y),
          primalValue (program I) z=dualValue (program I) y∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal z y))∧
          ∀ W:ℕ,wordBound.eval (bitSize (encodeInput kind I))≤ W→
            Spec (2^W) (fun σ => σ.inp=(encodeInput kind I).length::encodeInput kind I∧
              (encodeInput kind I).length≤ (σ.arrs "input.data").length∧
              2*n < (σ.arrs "flow.weights").length∧ 2*(n*n) < (σ.arrs "flow.capacities").length∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length∧
              2*columns n < (σ.arrs "flow.primal").length∧ 2*rows n < (σ.arrs "flow.dual").length∧
              2*(n*n) < (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length)
              c (fun _ τ => Data I τ∧ τ.vars "metric.n"=n∧ τ.vars "metric.n2"=n*n∧
                τ.vars "flow.kind"=RamGraphHeader.tag kind∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector z hz.1)) "flow.primal" τ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy.1)) "flow.dual" τ∧
                Prefix (RamUnsignedBuffer.encode (MetricMatrix.values (RamDualDistances.result y hy.1))) "metric.old" τ)
              (timeBound.eval (bitSize (encodeInput kind I))):=by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsolver⟩:=RamInputOptimal.exists_program
  let initTime:Polynomial ℕ:=Polynomial.C 62*(Polynomial.X+Polynomial.C 1)^3
  let words:Polynomial ℕ:=WB+Polynomial.C 2*FlowDistanceBounds.widthBound sourceWord+
    LpInputSize.sizeBound+Polynomial.C 20
  refine ⟨.seq c RamDualDistances.command,T+RamDistanceResources.timeBound sourceWord+initTime,
    words,TB,sourceWord,⟨hnoWrite,by decide⟩,?_⟩
  intro n kind I hp
  obtain ⟨z,y,hz,hy,hvalue,hfit,hcorrect⟩:=hsolver kind I hp
  refine ⟨z,y,hz,hy,hvalue,hfit,?_⟩
  intro W hW
  let L:=bitSize (encodeInput kind I)
  let S:=LpInputSize.sizeBound.eval L
  let K:=(FlowDistanceBounds.widthBound sourceWord).eval L
  let w:=sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I)))
  have hsum:WB.eval L+2*K+S+20≤ W:=by simpa [words,L,S,K] using hW
  have hWB:WB.eval L≤ W:=by omega
  obtain ⟨hB,hn,hn2,hindex⟩:=RamDistanceResources.host_bound sourceWord kind I W (by
    have hh:2*K+S+20≤ W:=by omega
    simpa only [K,S,L] using hh)
  have hyfit:FitsInWords w (Lax109476.RationalEncoding.encodeVector y):=by
    intro x hx
    exact hfit x (by simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]; exact Or.inr hx)
  have hyheight:=FlowDistanceBounds.vector_height w y hyfit
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu,hOld,hNew⟩
  obtain ⟨ν,rlp,plp⟩:=hcorrect W hWB σ
    ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu⟩
  obtain ⟨τ,rdist,pdist⟩:=RamDualDistances.command_spec (2^W) w y hy.1 hB hn hn2 hindex
    (fun i => (hyheight i).1) (fun i => (hyheight i).2) ν
    ⟨plp.1.1,plp.1.2.1,plp.2.2.2.1,
      by rwa [RamFrames.run_array_length rlp "metric.old"],
      by rwa [RamFrames.run_array_length rlp "metric.new"]⟩
  have hinitCost:50*(n*n)+12≤ initTime.eval L:=by
    have hnL:n≤ L:=LpInputSize.input_dimension kind I
    have hncube:n*n≤ (L+1)^3:=by
      calc
        _≤ (L+1)^2:=by nlinarith
        _≤ _:=Nat.pow_le_pow_right (by omega) (by decide)
    have hpositive:1≤ (L+1)^3:=Nat.succ_le_iff.mpr (pow_pos (by omega) 3)
    simp only [initTime,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X]
    omega
  have hdistCost:=RamDistanceResources.time_bound sourceWord kind I
  change n*((72*(w*(n*n+1))+324)*(n*n)+22)+10≤ (RamDistanceResources.timeBound sourceWord).eval L at hdistCost
  refine ⟨τ,(rlp.seq rdist).mono ?_,RamFlowData.frame rdist I plp.1 (by decide) (by decide),pdist.1,pdist.2.1,
    (rdist.frame_var "flow.kind" (by decide)).trans plp.2.1,?_,?_,pdist.2.2⟩
  · simp only [Polynomial.eval_add]
    dsimp only [L,w] at hinitCost hdistCost ⊢
    omega
  · simpa only [Prefix,rdist.frame_arr "flow.primal" (by decide)] using plp.2.2.1
  · simpa only [Prefix,rdist.frame_arr "flow.dual" (by decide)] using plp.2.2.2.1

end Lax455465Proofs.RamInputMetric

end

section

namespace Lax455465Proofs.RamArrayProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B M:ℕ) (leftArray rightArray:String) (xs ys:List ℚ≥0) (i:ℕ)
    (hxi:i < xs.length) (hyi:i < ys.length) (hB:2*M^2+3 < B) (hindex:2*i+1 < B)
    (hxn:xs[i].num≤ M) (hxd:xs[i].den≤ M) (hyn:ys[i].num≤ M) (hyd:ys[i].den≤ M):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode xs) leftArray σ∧
      Prefix (RamUnsignedBuffer.encode ys) rightArray σ∧ σ.vars "sum.i"=i)
      (command leftArray rightArray)
      (fun _ τ => FractionOutput ((xs[i]*ys[i]:ℚ≥0):ℚ) τ)
      (36*(xs[i].den*ys[i].den).size+104):=by
  have hM:M < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  rintro σ ⟨hxp,hyp,hi⟩
  obtain ⟨ν,rx,px⟩:=RamUnsignedBuffer.read_spec B leftArray "sum.i" xs i hxi h2 hindex
    (hxn.trans_lt hM) (hxd.trans_lt hM) (by decide) σ ⟨hxp,hi⟩
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B xs[i] "left" (by omega)
    (hxn.trans_lt hM) (hxd.trans_lt hM) (by decide) ν px.1
  have hypμ:Prefix (RamUnsignedBuffer.encode ys) rightArray μ:=by
    have rr:=rx.seq rl
    simpa only [Prefix,rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using hyp
  have hiμ:μ.vars "sum.i"=i:=by
    have rr:=rx.seq rl
    exact (rr.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars])).trans hi
  obtain ⟨ξ,ry,py⟩:=RamUnsignedBuffer.read_spec B rightArray "sum.i" ys i hyi h2 hindex
    (hyn.trans_lt hM) (hyd.trans_lt hM) (by decide) μ ⟨hypμ,hiμ⟩
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B ys[i] "right" (by omega)
    (hyn.trans_lt hM) (hyd.trans_lt hM) (by decide) ξ py.1
  have plη:η.vars "left.s"=0∧ η.vars "left.n"=xs[i].num∧ η.vars "left.d"=xs[i].den:=by
    have run:=ry.seq rr
    simpa only [run.frame_var "left.s" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      run.frame_var "left.n" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      run.frame_var "left.d" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rm,pm⟩:=multiplyFraction_spec B M 0 xs[i].num xs[i].den 0 ys[i].num ys[i].den
    hB (by omega) (by omega) hxn hxd hyn hyd xs[i].den_pos ys[i].den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,(rx.seq (rl.seq (ry.seq (rr.seq rm)))).mono (by omega),?_⟩
  simpa only [RamUnsignedArithmetic.value,NNRat.coe_mul] using pm

end Lax455465Proofs.RamArrayProduct

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

def Context (leftArray rightArray:String) (xs ys:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "sum.count"=xs.length∧ Prefix (RamUnsignedBuffer.encode xs) leftArray σ∧
    Prefix (RamUnsignedBuffer.encode ys) rightArray σ

theorem value_at (xs ys:List ℚ≥0) (hlen:ys.length=xs.length) (i:ℕ) (hi:i < xs.length):
    (products xs ys)[i]'(by simpa only [products,List.length_ofFn] using hi) =
      xs[i]*ys[i]'(by omega):=by
  simp only [products,List.getElem_ofFn,List.getD_eq_get ys 0 (⟨i,by omega⟩:Fin ys.length)]
  rfl

theorem command_spec (B M:ℕ) (leftArray rightArray:String) (xs ys:List ℚ≥0)
    (hlen:ys.length=xs.length) (hB:2*M^2+3 < B) (hindex:2*xs.length+2 < B)
    (hxn:∀ q∈ xs,q.num≤ M) (hxd:∀ q∈ xs,q.den≤ M)
    (hyn:∀ q∈ ys,q.num≤ M) (hyd:∀ q∈ ys,q.den≤ M)
    (hpn:∀ q∈ products xs ys,q.num≤ M) (hpd:∀ q∈ products xs ys,q.den≤ M)
    (hprefixNum:∀ i, ((products xs ys).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((products xs ys).take i).sum.den≤ M):
    Spec B (Context leftArray rightArray xs ys) (command leftArray rightArray)
      (fun _ τ => Context leftArray rightArray xs ys τ∧ FractionOutput (((products xs ys).sum:ℚ≥0):ℚ) τ)
      ((72*(M^2).size+224)*xs.length+16):=by
  have hlength:(products xs ys).length=xs.length:=List.length_ofFn
  have hbody:∀ i, ∀ hi:i < (products xs ys).length,
      Spec B (fun σ => Context leftArray rightArray xs ys σ∧ σ.vars "sum.i"=i)
        (RamArrayProduct.command leftArray rightArray)
        (fun _ τ => Context leftArray rightArray xs ys τ∧ FractionOutput ((products xs ys)[i]:ℚ) τ)
        (36*(M^2).size+104):=by
    intro i hi σ hσ
    have hx:i < xs.length:=by rwa [hlength] at hi
    have hy:i < ys.length:=by omega
    have hxm:xs[i]∈ xs:=List.getElem_mem hx
    have hym:ys[i]∈ ys:=List.getElem_mem hy
    obtain ⟨τ,rr,pr⟩:=RamArrayProduct.command_spec B M leftArray rightArray xs ys i hx hy hB
      (by omega) (hxn _ hxm) (hxd _ hxm) (hyn _ hym) (hyd _ hym) σ ⟨hσ.1.2.1,hσ.1.2.2,hσ.2⟩
    have hcost:(xs[i].den*ys[i].den).size≤ (M^2).size:=
      Nat.size_le_size (by nlinarith [Nat.mul_le_mul (hxd _ hxm) (hyd _ hym)])
    refine ⟨τ,rr.mono (by omega),?_,?_⟩
    · simpa only [Context,Prefix,rr.frame_var "sum.count" (by
        dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using hσ.1
    · simpa only [value_at xs ys hlen i hx] using pr
  have hf:=RamUnsignedSum.command_spec B M (36*(M^2).size+104)
    (Context leftArray rightArray xs ys) "sum.i" "sum.count" (products xs ys)
    (RamArrayProduct.command leftArray rightArray) hB (by rw [hlength]; omega) hpn hpd hprefixNum hprefixDen
    (fun σ h => by simpa only [hlength] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using h)
  unfold command
  rw [hlength] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamProductSum

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

namespace Lax455465Proofs.RamMetricCost

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding Lax759944.BinaryWordEncoding MetricMatrix LpInputSize
open scoped NNRat

def command:Com:=.seq (.assign "sum.count" (.var "metric.n2"))
  (.seq (RamProductSum.command "flow.capacities" "metric.old") (save "round.cost"))

theorem command_spec (B:ℕ) {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind)
    (I:RationalInstance n) (d:Matrix n) (K:ℕ) (hd:∀ u v,Height (2^K) (d u v:ℚ))
    (hB:2*(2^(MetricCostHeight.exponent n (bitSize (encodeInput kind I)) K))^2+3 < B)
    (hindex:2*(n*n)+2 < B):
    Spec B (fun σ => σ.vars "metric.n2"=n*n∧
      Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ∧
      Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ) command
      (fun _ τ => Stored "round.cost" (MetricCostData.cost I d) τ)
      ((144*MetricCostHeight.exponent n (bitSize (encodeInput kind I)) K+296)*(n*n)+22):=by
  let L:=bitSize (encodeInput kind I)
  let V:=MetricCostHeight.exponent n L K
  let M:=2^V
  let xs:=values I.capacity
  let ys:=values d
  let qs:=RamProductSum.products xs ys
  have hxlen:xs.length=n*n:=length_values _
  have hylen:ys.length=n*n:=length_values _
  have hqlen:qs.length=n*n:=by simp only [qs,RamProductSum.products,List.length_ofFn,xs,length_values]
  have hdom:L+K≤ V:=by
    have hh:L+K≤ (L+K)*(n*n+1):=Nat.le_mul_of_pos_right _ (by omega)
    dsimp only [V,MetricCostHeight.exponent]
    omega
  have hL:2^L≤ M:=Nat.pow_le_pow_right (by decide) (by omega)
  have hK:2^K≤ M:=Nat.pow_le_pow_right (by decide) (by omega)
  have hLK:2^(L+K)≤ M:=Nat.pow_le_pow_right (by decide) hdom
  have hM:M < B:=by dsimp only [M,V,L]; nlinarith
  have hxn:∀ q∈ xs,q.num≤ M:=by
    intro q hq
    obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
    have hh:=height_mono (capacity_height kind I ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hL
    simpa only [NNRat.natAbs_num_coe] using hh.1
  have hxd:∀ q∈ xs,q.den≤ M:=by
    intro q hq
    obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
    have hh:=height_mono (capacity_height kind I ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hL
    simpa only [NNRat.den_coe] using hh.2
  have hyn:∀ q∈ ys,q.num≤ M:=by
    intro q hq
    obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
    have hh:=height_mono (hd ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hK
    simpa only [NNRat.natAbs_num_coe] using hh.1
  have hyd:∀ q∈ ys,q.den≤ M:=by
    intro q hq
    obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
    have hh:=height_mono (hd ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2) hK
    simpa only [NNRat.den_coe] using hh.2
  have hph:=MetricCostHeight.products_height kind I d K hd
  have hpn:∀ q∈ qs,q.num≤ M:=by
    intro q hq
    simpa only [NNRat.natAbs_num_coe] using (height_mono (hph q hq) hLK).1
  have hpd:∀ q∈ qs,q.den≤ M:=by
    intro q hq
    simpa only [NNRat.den_coe] using (height_mono (hph q hq) hLK).2
  have hprefix:=MetricCostHeight.prefix_height kind I d K hd
  have hpreN:∀ i, (qs.take i).sum.num≤ M:=by
    intro i
    simpa only [NNRat.natAbs_num_coe] using (hprefix i).1
  have hpreD:∀ i, (qs.take i).sum.den≤ M:=by
    intro i
    simpa only [NNRat.den_coe] using (hprefix i).2
  have hfinal:(MetricCostData.cost I d).num≤ M∧ (MetricCostData.cost I d).den≤ M:=by
    simpa only [MetricCostData.cost,List.take_length] using And.intro (hpreN qs.length) (hpreD qs.length)
  rintro σ ⟨hn2,hxp,hyp⟩
  let ν:=σ.setVar "sum.count" (n*n)
  have rcount:Run B (.assign "sum.count" (.var "metric.n2")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn2.symm,hn2 ▸ (by omega:n*n < B)⟩)
  have hctx:RamProductSum.Context "flow.capacities" "metric.old" xs ys ν:=by
    refine ⟨by simp [ν,hxlen],?_,?_⟩
    · simpa only [ν,Prefix,arrs_setVar,xs] using hxp
    · simpa only [ν,Prefix,arrs_setVar,ys] using hyp
  obtain ⟨μ,rsum,psum⟩:=RamProductSum.command_spec B M "flow.capacities" "metric.old" xs ys
    (by omega) hB (by rwa [hxlen]) hxn hxd hyn hyd hpn hpd hpreN hpreD ν hctx
  obtain ⟨τ,rsave,psave⟩:=save_spec B "round.cost" (MetricCostData.cost I d)
    (hfinal.1.trans_lt hM) (hfinal.2.trans_lt hM) (by decide) μ psum.2
  have hsize:(M^2).size=2*V+1:=by
    dsimp only [M]
    rw [←Nat.pow_mul,Nat.size_pow]
    omega
  refine ⟨τ,(rcount.seq (rsum.seq rsave)).mono ?_,psave⟩
  rw [hxlen,hsize]
  dsimp only [V,L]
  ring_nf
  omega

end Lax455465Proofs.RamMetricCost

end

section

namespace Lax455465Proofs.RamMetricCostResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding

noncomputable def timeBound (metricWord:Polynomial ℕ):Polynomial ℕ:=
  Polynomial.C 1000*heightBound metricWord*(Polynomial.X+Polynomial.C 1)^2+Polynomial.C 24

noncomputable def wordBound (metricWord:Polynomial ℕ):Polynomial ℕ:=
  Polynomial.C 2*heightBound metricWord+Polynomial.C 2*Polynomial.X^2+Polynomial.C 20

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

theorem time_bound (metricWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    (144*MetricCostHeight.exponent n (bitSize (encodeInput kind I))
      (metricWord.eval (bitSize (encodeInput kind I)))+296)*(n*n)+22≤
      (timeBound metricWord).eval (bitSize (encodeInput kind I)):=by
  let L:=bitSize (encodeInput kind I)
  let H:=(heightBound metricWord).eval L
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hv:=height_bound metricWord kind I
  have hpos:1≤ H:=by
    simp only [H,heightBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow]
    nlinarith
  have hcoefficient:144*MetricCostHeight.exponent n L (metricWord.eval L)+296≤ 1000*H:=by
    dsimp only [L,H] at hv ⊢
    nlinarith
  have hnn:n*n≤ (L+1)^2:=by nlinarith
  have hh:=Nat.mul_le_mul hcoefficient hnn
  simp only [timeBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  dsimp only [L,H] at hh ⊢
  omega

theorem host_bound (metricWord:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (W:ℕ)
    (hW:(wordBound metricWord).eval (bitSize (encodeInput kind I))≤ W):
    2*(2^(MetricCostHeight.exponent n (bitSize (encodeInput kind I))
      (metricWord.eval (bitSize (encodeInput kind I)))))^2+3 < 2^W∧ 2*(n*n)+2 < 2^W:=by
  let L:=bitSize (encodeInput kind I)
  let V:=MetricCostHeight.exponent n L (metricWord.eval L)
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hv:=height_bound metricWord kind I
  have hwidth:RamHostBounds.sufficient V 0 0 (2*(n*n)+3)≤ W:=by
    simp only [wordBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] at hW
    dsimp only [RamHostBounds.sufficient,V,L]
    have hnn:n*n≤ L^2:=by nlinarith
    dsimp only [L] at hnn hv
    omega
  obtain ⟨hB,hT,hC,hL⟩:=RamHostBounds.sufficient_bounds V 0 0 (2*(n*n)+3) W hwidth
  exact ⟨hB,by omega⟩

end Lax455465Proofs.RamMetricCostResources

end

section

namespace Lax455465Proofs.RamInputMetricCost

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax759944.RamPolytime
open Lax759944.BinaryWordEncoding
open scoped NNRat

set_option maxHeartbeats 0 in

theorem exists_program:
    ∃ (c:Com) (timeBound wordBound sourceTime sourceWord:Polynomial ℕ),
      c.NoWrite∧ ∀ {n:ℕ} (kind:EdgeKind) (I:RationalInstance n),2≤ supportCount I.weights→
        ∃ (z:Fin (columns n)→ ℚ) (y:Fin (rows n)→ ℚ)
          (hz:PrimalFeasible (program I) z) (hy:DualFeasible (program I) y),
          primalValue (program I) z=dualValue (program I) y∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal z y))∧
          ∀ W:ℕ,wordBound.eval (bitSize (encodeInput kind I))≤ W→
            Spec (2^W) (fun σ => σ.inp=(encodeInput kind I).length::encodeInput kind I∧
              (encodeInput kind I).length≤ (σ.arrs "input.data").length∧
              2*n < (σ.arrs "flow.weights").length∧ 2*(n*n) < (σ.arrs "flow.capacities").length∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length∧
              2*columns n < (σ.arrs "flow.primal").length∧ 2*rows n < (σ.arrs "flow.dual").length∧
              2*(n*n) < (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length)
              c (fun _ τ => Data I τ∧ τ.vars "metric.n"=n∧ τ.vars "metric.n2"=n*n∧
                τ.vars "flow.kind"=RamGraphHeader.tag kind∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector z hz.1)) "flow.primal" τ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy.1)) "flow.dual" τ∧
                Prefix (RamUnsignedBuffer.encode (MetricMatrix.values (RamDualDistances.result y hy.1))) "metric.old" τ∧
                RamUnsignedScalar.Stored "round.cost" (MetricCostData.cost I (RamDualDistances.result y hy.1)) τ)
              (timeBound.eval (bitSize (encodeInput kind I))):=by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsolver⟩:=RamInputMetric.exists_program
  let P:=FlowDistanceBounds.widthBound sourceWord
  refine ⟨.seq c RamMetricCost.command,T+RamMetricCostResources.timeBound P,
    WB+RamMetricCostResources.wordBound P,TB,sourceWord,⟨hnoWrite,by decide⟩,?_⟩
  intro n kind I hp
  obtain ⟨z,y,hz,hy,hvalue,hfit,hcorrect⟩:=hsolver kind I hp
  refine ⟨z,y,hz,hy,hvalue,hfit,?_⟩
  intro W hW
  let L:=bitSize (encodeInput kind I)
  let K:=P.eval L
  let D:=RamDualDistances.result y hy.1
  have hsum:WB.eval L+(RamMetricCostResources.wordBound P).eval L≤ W:=by
    simpa only [Polynomial.eval_add,L] using hW
  have hWB:WB.eval L≤ W:=by omega
  obtain ⟨hB,hindex⟩:=RamMetricCostResources.host_bound P kind I W (by
    have hh:(RamMetricCostResources.wordBound P).eval L≤ W:=by omega
    simpa only [L] using hh)
  have hheight:∀ u v,LpInputSize.Height (2^K) (D u v:ℚ):=by
    intro u v
    change LpInputSize.Height (2^K) (MetricMatrix.rational D u v)
    rw [show MetricMatrix.rational D=RationalDistances.dualDistance y from RamDualDistances.rational_result y hy.1]
    exact FlowDistanceBounds.dual_polynomial_height sourceWord kind I z y hy.1 hfit (List.finRange n) u v
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu,hOld,hNew⟩
  obtain ⟨ν,rlp,plp⟩:=hcorrect W hWB σ
    ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu,hOld,hNew⟩
  obtain ⟨τ,rcost,pcost⟩:=RamMetricCost.command_spec (2^W) kind I D K hheight hB hindex ν
    ⟨plp.2.2.1,plp.1.2.2.2.2.2.2.2,plp.2.2.2.2.2.2⟩
  have hcostBound:=RamMetricCostResources.time_bound P kind I
  refine ⟨τ,(rlp.seq rcost).mono ?_,RamFlowData.frame rcost I plp.1 (by decide) (by decide),
    (rcost.frame_var "metric.n" (by decide)).trans plp.2.1,
    (rcost.frame_var "metric.n2" (by decide)).trans plp.2.2.1,
    (rcost.frame_var "flow.kind" (by decide)).trans plp.2.2.2.1,?_,?_,?_,pcost⟩
  · simp only [Polynomial.eval_add]
    dsimp only [K,L] at hcostBound ⊢
    omega
  · simpa only [Prefix,rcost.frame_arr "flow.primal" (by decide)] using plp.2.2.2.2.1
  · simpa only [Prefix,rcost.frame_arr "flow.dual" (by decide)] using plp.2.2.2.2.2.1
  · simpa only [Prefix,rcost.frame_arr "metric.old" (by decide)] using plp.2.2.2.2.2.2

end Lax455465Proofs.RamInputMetricCost

end

theorem solution:∃ (c:Lax808846Proofs.Imp.Com) (timeBound:@Polynomial Nat Nat.instSemiring) (wordBound:
  @Polynomial Nat Nat.instSemiring) (sourceTime:@Polynomial Nat Nat.instSemiring) (sourceWord:
  @Polynomial Nat Nat.instSemiring),
  And c.NoWrite
    (∀ {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind) (I:Lax455465.RationalEncoding.RationalInstance n),
      Nat.le ((2:Nat))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I))→
        ∃ (z:Fin (Lax455465Proofs.RamFlowData.columns n)→ Rat) (y:Fin (Lax455465Proofs.RamFlowData.rows n)→ Rat)
          (hz:
          @Lax109476.LinearProgram.PrimalFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
            Rat.instPartialOrder
            (Nat.add (Nat.mul n n)
              (Nat.mul
                ((2:Nat))
                (Nat.mul
                  (Nat.mul n n) n)))
            (Nat.add ((1:Nat))
              (Nat.mul (Nat.mul n n)
                (Nat.mul n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) z)
          (hy:
          @Lax109476.LinearProgram.DualFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.instPartialOrder
            (Nat.add (Nat.mul n n)
              (Nat.mul
                ((2:Nat))
                (Nat.mul
                  (Nat.mul n n) n)))
            (Nat.add ((1:Nat))
              (Nat.mul (Nat.mul n n)
                (Nat.mul n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) y),
          And
            (@Eq Rat
              (@Lax109476.LinearProgram.primalValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                (@Lax455465Proofs.DirectedFlowLP.program n I) z)
              (@Lax109476.LinearProgram.dualValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                (@Lax455465Proofs.DirectedFlowLP.program n I) y))
            (And
              (Lax759944.RamPolytime.FitsInWords
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
                  sourceWord)
                (@Lax109476.RationalEncoding.encodeCertificate (Lax455465Proofs.RamFlowData.rows n)
                  (Lax455465Proofs.RamFlowData.columns n)
                  (@Lax109476.RationalCertificates.Certificate.optimal (Lax455465Proofs.RamFlowData.rows n)
                    (Lax455465Proofs.RamFlowData.columns n) z y)))
              (∀ (W:Nat),
                Nat.le
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
                                              (Nat.lt
                                                (Nat.mul
                                                  ((2:Nat))
                                                  (Nat.mul n n))
                                                (@List.length Nat (σ.arrs "metric.new")))))))))))))))
                    c
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamFlowData.Data n I τ)
                        (And (@Eq Nat (τ.vars "metric.n") n)
                          (And (@Eq Nat (τ.vars "metric.n2") (Nat.mul n n))
                            (And (@Eq Nat (τ.vars "flow.kind") (Lax455465Proofs.RamGraphHeader.tag kind))
                              (And
                                (Lax455465Proofs.RamVirtualState.Prefix
                                  (Lax455465Proofs.RamUnsignedBuffer.encode
                                    (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.columns n) z
                                      (@And.left
                                        (∀
                                          (j:
                                            Fin
                                              (Nat.add
                                                ((1:Nat))
                                                (Nat.mul
                                                  (Nat.mul n n)
                                                  (Nat.mul n n)))),
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
                                              (Nat.add
                                                (Nat.mul n n)
                                                (Nat.mul
                                                  ((2:Nat))
                                                  (Nat.mul
                                                    (Nat.mul n n) n)))),
                                          @LE.le Rat
                                            (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                            (@Lax109476.LinearProgram.rowValue Rat
                                              (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                              (@Lax455465Proofs.DirectedFlowLP.program n I) z i)
                                            (@Lax109476.LinearProgram.Program.b Rat
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
                                                (Nat.add
                                                  (Nat.mul n n)
                                                  (Nat.mul
                                                    ((2:Nat))
                                                    (Nat.mul
                                                      (Nat.mul n n) n)))),
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
                                                (Nat.add
                                                  ((1:Nat))
                                                  (Nat.mul
                                                    (Nat.mul n n)
                                                    (Nat.mul n n)))),
                                            @LE.le Rat
                                              (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                              (@Lax109476.LinearProgram.Program.c Rat
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
                                                (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                              (@Lax109476.LinearProgram.columnValue Rat
                                                (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                                    (Nat.add
                                                      (Nat.mul n n)
                                                      (Nat.mul
                                                        ((2:Nat))
                                                        (Nat.mul
                                                          (Nat.mul n n) n)))),
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
                                                    (Nat.add
                                                      ((1:Nat))
                                                      (Nat.mul
                                                        (Nat.mul n n)
                                                        (Nat.mul n n)))),
                                                @LE.le Rat
                                                  (@Preorder.toLE Rat
                                                    (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                  (@Lax109476.LinearProgram.Program.c Rat
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
                                                    (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                                  (@Lax109476.LinearProgram.columnValue Rat
                                                    (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                                  (Nat.add
                                                    (Nat.mul n n)
                                                    (Nat.mul
                                                      ((2:Nat))
                                                      (Nat.mul
                                                        (Nat.mul n n) n)))),
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
                                                  (Nat.add
                                                    ((1:Nat))
                                                    (Nat.mul
                                                      (Nat.mul n n)
                                                      (Nat.mul n n)))),
                                              @LE.le Rat
                                                (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                (@Lax109476.LinearProgram.Program.c Rat
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
                                                  (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                                (@Lax109476.LinearProgram.columnValue Rat
                                                  (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                                  (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                            hy)))
                                      τ))))))))
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      timeBound)))):= @Lax455465Proofs.RamInputMetricCost.exists_program
