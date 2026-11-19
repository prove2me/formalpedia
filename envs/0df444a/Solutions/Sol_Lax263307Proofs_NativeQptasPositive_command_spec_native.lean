-- Prove2me | solution 1 for Lax263307Proofs.NativeQptasPositive.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:28:02.994227+00:00
-- url     : https://prove2.me/submissions/e9bc0f64-0165-49f7-89f8-53f9c3ac6096

import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax263307Proofs_NativeBlowUp_prepare_spec_native
import Theorems.Thm_Lax263307Proofs_NativeOriginalAccuracy_command_spec_native
import Theorems.Thm_Lax263307Proofs_NativeRootAccuracy_command_spec_native
import Theorems.Thm_Lax263307Proofs_NativeRootBudget_command_spec_native
import Theorems.Thm_Lax263307Proofs_NativeWeightedOutput_command_spec_native
import Theorems.Thm_Lax263307Proofs_NativeUnweightedExecution_command_spec_native

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

namespace Lax263307Proofs.NativeBlowUp
end Lax263307Proofs.NativeBlowUp
theorem Lax263307Proofs.NativeBlowUp.prepare_spec:∀ {n:Nat} (B M:Nat),
  LE.le ((1:Nat)) M→
    LE.le n M→
      ∀ (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (w:Fin n→ Rat)
        (ε:Rat),
        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
          (∀ (v:Fin n),And (LE.le (w v).num.natAbs M) (LE.le (w v).den M))→
            And (LE.le ε.num.natAbs M) (LE.le ε.den M)→
              LT.lt
                  (HAdd.hAdd
                    (HMul.hMul
                      ((2:Nat))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        M ((4:Nat))))
                    ((3:Nat)))
                  B→
                LT.lt
                    (HAdd.hAdd
                      (HAdd.hAdd
                        (HMul.hMul n n)
                        (HMul.hMul
                          ((3:Nat)) n))
                      ((3:Nat)))
                    B→
                  LT.lt
                      (HAdd.hAdd
                        (HAdd.hAdd
                          (HAdd.hAdd
                            (HAdd.hAdd
                              (HMul.hMul n n)
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                (∑ v:Fin n,
                                  @Lax263307.WeightRounding.copies n
                                    (fun (v:Fin n) =>
                                      @Max.max Rat Rat.instSup (w v)
                                        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                                    ε v)
                                ((2:Nat))))
                            n)
                          (∑ v:Fin n,
                            @Lax263307.WeightRounding.copies n
                              (fun (v:Fin n) =>
                                @Max.max Rat Rat.instSup (w v)
                                  (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                              ε v))
                        ((3:Nat)))
                      B→
                    have cs:=
                      @Lax263307.WeightRounding.copies n
                        (fun (v:Fin n) =>
                          @Max.max Rat Rat.instSup (w v) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                        ε;
                    have N:= ∑ v:Fin n,cs v;
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst w ε))
                          (And
                            (LE.le
                              (HAdd.hAdd
                                (HAdd.hAdd
                                  (HMul.hMul n n)
                                  (HMul.hMul
                                    ((3:Nat)) n))
                                ((3:Nat)))
                              (@List.length Nat (σ.arrs "input.data")))
                            (And (LE.le n (@List.length Nat (σ.arrs "copy.counts")))
                              (And (LE.le N (@List.length Nat (σ.arrs "blowup.owner")))
                                (LE.le (HMul.hMul N N)
                                  (@List.length Nat (σ.arrs "blowup.matrix")))))))
                      Lax263307Proofs.NativeBlowUp.prepare
                      (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                        And
                          (Lax455465Proofs.RamVirtualState.Prefix
                            (@Lax263307Proofs.NativeBlowUp.numberedMatrix n G inst cs) "blowup.matrix" τ)
                          (And
                            (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeBlowUp.owners n cs)
                              "blowup.owner" τ)
                            (And (@Eq Nat (τ.vars "blowup.length") N)
                              (And
                                (Lax455465Proofs.RamVirtualState.Prefix
                                  (@Lax263307Proofs.NativeFrontend.tailInput n G inst w ε) "input.data" τ)
                                (And (@Eq (List Nat) τ.out σ.out) (@Eq Nat (τ.vars "input.n") n))))))
                      (Lax263307Proofs.NativeBlowUp.cost n N):= @Lax263307Proofs.NativeBlowUp.prepare_spec_native
namespace Lax263307Proofs.NativeOriginalAccuracy
end Lax263307Proofs.NativeOriginalAccuracy
theorem Lax263307Proofs.NativeOriginalAccuracy.command_spec:∀ {n:Nat} (B:Nat) (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
  (weights:Fin n→ Rat) (ε:Rat),
  LT.lt
      (HAdd.hAdd
        (HAdd.hAdd (HMul.hMul n n)
          (HMul.hMul ((3:Nat))
            n))
        ((3:Nat)))
      B→
    LT.lt ε.num.natAbs B→
      LT.lt ε.den B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ.vars "input.n") n)
              (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeFrontend.tailInput n G inst weights ε)
                "input.data" σ))
          Lax263307Proofs.NativeOriginalAccuracy.command
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "accuracy.n") ε.num.natAbs) (@Eq Nat (τ.vars "accuracy.d") ε.den))
          ((18:Nat)):= @Lax263307Proofs.NativeOriginalAccuracy.command_spec_native
namespace Lax263307Proofs.NativeRootAccuracy
end Lax263307Proofs.NativeRootAccuracy
theorem Lax263307Proofs.NativeRootAccuracy.command_spec:∀ (B M n:Nat) (ε:Rat),
  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
    Lax263307Proofs.NativeSignedArithmetic.Bounded M ε→
      LT.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd
                (HAdd.hAdd
                  (HMul.hMul
                    ((3:Nat)) M)
                  (HMul.hMul
                    (HMul.hMul
                      ((8:Nat))
                      (HAdd.hAdd (Lax263307.RecursionDepth.depth n)
                        ((1:Nat))))
                    M))
                (HMul.hMul
                  ((2:Nat)) n))
              (Lax263307.RecursionDepth.depth n))
            ((40:Nat)))
          B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ.vars "graph.n") n)
              (And (@Eq Nat (σ.vars "accuracy.n") ε.num.natAbs) (@Eq Nat (σ.vars "accuracy.d") ε.den)))
          Lax263307Proofs.NativeRootAccuracy.command
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "graph.n") n)
              (And
                (@Eq Nat (τ.vars "algorithm.E")
                  (@Nat.ceil Rat Rat.semiring Rat.instPartialOrder
                    (@FloorRing.toFloorSemiring Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                      Rat.instFloorRing)
                    (@Inv.inv Rat Rat.instInv
                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε
                        (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))))))
                (And
                  (@Eq Nat (τ.vars "node.D")
                    (Lax263307.RecursiveAlgorithm.accuracyDenominator n
                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε
                        (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))))
                  (@Eq Nat (τ.vars "recursion.fuel") (Lax263307.RecursionDepth.depth n)))))
          (HAdd.hAdd
            (HMul.hMul
              ((14:Nat)) (Lax263307.RecursionDepth.depth n))
            ((28:Nat))):= @Lax263307Proofs.NativeRootAccuracy.command_spec_native
namespace Lax263307Proofs.NativeRootBudget
end Lax263307Proofs.NativeRootBudget
theorem Lax263307Proofs.NativeRootBudget.command_spec:∀ (B C d Q e n D:Nat),
  LT.lt ((0:Nat)) n→
    LT.lt ((0:Nat)) D→
      LT.lt (Lax263307Proofs.NativeRootBudget.guard C d Q e n D) B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "graph.n") n) (@Eq Nat (σ.vars "node.D") D))
          (Lax263307Proofs.NativeRootBudget.command C d Q e)
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "graph.n") n)
              (And (@Eq Nat (τ.vars "node.D") D)
                (And (@Eq Nat (τ.vars "algorithm.resource") (Lax263307Proofs.NativeRootResource.envelope C d n D))
                  (And (@Eq Nat (τ.vars "algorithm.roundWidth") (Lax263307Proofs.NativeRootResource.budget Q e C d n D))
                    (@Eq Nat (τ.vars "recursion.stride")
                      (HMul.hMul
                        ((2:Nat))
                        (HAdd.hAdd
                          (Lax263307Proofs.NativeRootResource.budget Q e C d n D)
                          ((1:Nat)))))))))
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd
                (HAdd.hAdd
                  (HAdd.hAdd
                    (HMul.hMul
                      ((12:Nat)) n.size)
                    (HMul.hMul
                      ((12:Nat))
                      (HMul.hMul
                          ((2:Nat)) n).size))
                  (HMul.hMul
                    ((12:Nat)) d))
                (HMul.hMul
                  ((12:Nat))
                  (HMul.hMul C
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (HMul.hMul D (Lax263307.AlgorithmParameters.logarithm n))
                      d))))
              (HMul.hMul
                ((12:Nat)) e))
            ((78:Nat))):= @Lax263307Proofs.NativeRootBudget.command_spec_native
namespace Lax263307Proofs.NativeWeightedOutput
end Lax263307Proofs.NativeWeightedOutput
theorem Lax263307Proofs.NativeWeightedOutput.command_spec:∀ {n:Nat} (B:Nat) (copies:Fin n→ Nat) (I:Finset (Fin (∑ v:Fin n,copies v))),
  LT.lt
      (HAdd.hAdd
        (HAdd.hAdd n (∑ v:Fin n,copies v))
        ((5:Nat)))
      B→
    LT.lt
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) (∑ v:Fin n,copies v))
        B→
      Lax808846Proofs.Reasoning.Spec B
        (fun (σ:Lax808846Proofs.Imp.Env) =>
          And (@Eq Nat (σ.vars "input.n") n)
            (And (@Eq Nat (σ.vars "blowup.length") (∑ v:Fin n,copies v))
              (And (@Eq Nat (σ.vars "root.mask") (@Lax263307Proofs.NativeMasks.mask (∑ v:Fin n,copies v) I))
                (And
                  (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeBlowUp.owners n copies) "blowup.owner"
                    σ)
                  (And (LE.le (∑ v:Fin n,copies v) (@List.length Nat (σ.arrs "image.labels")))
                    (@Eq Nat (@List.length Nat (σ.arrs "image.output")) n))))))
        Lax263307Proofs.NativeWeightedOutput.command
        (fun (σ τ:Lax808846Proofs.Imp.Env) =>
          @Eq (List Nat) τ.out
            (@HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat))
              σ.out
              (@Lax263307.IndependentSetEncoding.encodeOutput n
                (@Lax263307.IndependentBlowUp.project n copies
                  (@Finset.image (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies)
                    (fun (a b:@Lax263307.IndependentBlowUp.Vertex n copies) =>
                      @Sigma.instDecidableEqSigma (Fin n) (fun (v:Fin n) => Fin (copies v)) (instDecidableEqFin n)
                        (fun (a:Fin n) => instDecidableEqFin (copies a)) a b)
                    (@DFunLike.coe (Equiv (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies))
                      (Fin (∑ v:Fin n,copies v))
                      (fun (x:Fin (∑ v:Fin n,copies v)) => @Lax263307.IndependentBlowUp.Vertex n copies)
                      (@EquivLike.toFunLike
                        (Equiv (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies))
                        (Fin (∑ v:Fin n,copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies)
                        (@Equiv.instEquivLike (Fin (∑ v:Fin n,copies v))
                          (@Lax263307.IndependentBlowUp.Vertex n copies)))
                      (@Lax263307.WeightedAlgorithm.labeling n copies))
                    I)))))
        (HAdd.hAdd
          (HAdd.hAdd
            (HMul.hMul
              ((24:Nat)) n)
            (HMul.hMul
              ((44:Nat)) (∑ v:Fin n,copies v)))
          ((36:Nat))):= @Lax263307Proofs.NativeWeightedOutput.command_spec_native
namespace Lax263307Proofs.NativeUnweightedExecution
end Lax263307Proofs.NativeUnweightedExecution
theorem Lax263307Proofs.NativeUnweightedExecution.command_spec:∀ {C:Lax263307.GraphClasses.GraphClass},
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
                    LT.lt ((0:Nat)) cfg.K→
                      LT.lt ((0:Nat)) cfg.b→
                        ∀ {n:Nat} (G:SimpleGraph (Fin n))
                          [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
                          @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                              (@Set.instMembership (SimpleGraph (Fin n))) (C n) G→
                            LT.lt ((0:Nat)) n→
                              ∀ (D c originalN R W w:Nat),
                                LE.le ((4:Nat)) D→
                                  LE.le n R→
                                    Lax263307Proofs.NativeOracleRounds.Program cfg.rounded c→
                                      (∀ (m:Nat),
                                          LT.lt ((0:Nat))
                                              m→
                                            LE.le m n→
                                              LE.le
                                                (Lax263307.ParameterResources.resource cfg.a cfg.K cfg.b m D) R)→
                                        LE.le
                                            (@Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c R) W→
                                          LE.le (Lax263307Proofs.NativeRootWorkspace.hostHeight cfg W)
                                              w→
                                            Lax808846Proofs.Reasoning.Spec
                                              (@HPow.hPow Nat Nat Nat
                                                (@instHPow Nat Nat
                                                  (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                ((2:Nat)) w)
                                              (@Lax263307Proofs.NativeCoreExecution.Input n
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  ((2:Nat)) w)
                                                D (Lax263307.RecursionDepth.depth n)
                                                (Lax263307Proofs.NativeRootWorkspace.stride W) W G inst
                                                (Lax263307Proofs.NativeRootWorkspace.extent cfg n W originalN))
                                              (Lax263307Proofs.NativeCoreMachine.command cfg)
                                              (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                                                And
                                                  (@Lax263307Proofs.NativeCoreExecution.Root n
                                                    (@HPow.hPow Nat Nat Nat
                                                      (@instHPow Nat Nat
                                                        (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                      ((2:Nat)) w)
                                                    D (Lax263307Proofs.NativeRootWorkspace.stride W) W cfg G inst
                                                    (Lax263307Proofs.NativeRootWorkspace.extent cfg n W originalN) τ)
                                                  (And
                                                    (@Lax263307Proofs.NativeRootTrace.Answer n
                                                      (@Lax263307.RecursiveAlgorithm.solve n lp flow cfg.a cfg.K cfg.b D
                                                        G inst)
                                                      τ)
                                                    (And (@Eq Nat (τ.vars "input.n") (σ.vars "input.n"))
                                                      (And (@Eq Nat (τ.vars "blowup.length") (σ.vars "blowup.length"))
                                                        (And
                                                          (@Eq (List Nat) (τ.arrs "blowup.owner")
                                                            (σ.arrs "blowup.owner"))
                                                          (@Eq (List Nat) τ.out σ.out))))))
                                              (Lax263307Proofs.NativeUnweightedExecution.cost cfg n W):= @Lax263307Proofs.NativeUnweightedExecution.command_spec_native

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

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_condEq_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.eq e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=(m == n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

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

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_le_twice_exponent (L n:ℕ) (hn:n≤ 2 ^ L):depth n≤ 2 * L:=by
  induction L generalizing n with
  | zero =>
    have:n≤ 1:=by simpa using hn
    simp [depth,this]
  | succ L ih =>
    by_cases hn₁:n≤ 1
    · simp [depth,hn₁]
    · rw [depth.eq_def n,if_neg hn₁]
      by_cases ha:2 * n / 3≤ 1
      · rw [depth.eq_def (2 * n / 3),if_pos ha]
        omega
      · rw [depth.eq_def (2 * n / 3),if_neg ha]
        have hb:2 * (2 * n / 3) / 3≤ 2 ^ L:=by
          rw [pow_succ] at hn
          omega
        have:=ih _ hb
        omega

theorem logarithmic_bound (n:ℕ):depth n≤ 2 * (Nat.log2 n + 1):=by
  apply depth_le_twice_exponent
  rw [Nat.log2_eq_log_two]
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le

end Lax263307Proofs.RecursionDepth

end

section

namespace Lax263307Proofs.BlowUpClasses

open Lax263307.GraphClasses Lax263307.IndependentBlowUp Lax263307.BlowUpClasses

theorem hereditary_closure (C:GraphClass):IsHereditary (blowUpClass C):=by
  intro m n H K hK hembedding
  obtain ⟨embedding⟩:=hembedding
  obtain ⟨l,G,hG,projection,hAdj⟩:=hK
  refine ⟨l,G,hG,fun v => projection (embedding v), ?_⟩
  intro u v
  exact embedding.map_adj_iff.symm.trans (hAdj (embedding u) (embedding v))

theorem copy_graph_mem (C:GraphClass) {n:ℕ} (G:SimpleGraph (Fin n))
    (member:G∈ C n) (copies:Fin n→ ℕ) (m:ℕ) (labeling:Fin m ≃ Vertex copies):
    (graph G copies).comap labeling∈ blowUpClass C m:=by
  refine ⟨n,G,member,fun v => (labeling v).1, ?_⟩
  intro u v
  rfl

end Lax263307Proofs.BlowUpClasses

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

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

open Lax808846.Ram

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

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem arrays_frame (coefficients:List ℕ):(command coefficients).warrs=[]:=by
  induction coefficients with
  | nil => simp [command,Com.warrs]
  | cons a rest ih => simp [command,Com.warrs,ih]

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

namespace Lax263307Proofs.RecursiveAlgorithm

open Lax263307.RecursiveAlgorithm Lax263307.ComputedSeparators
open Lax263307.GraphClasses Lax263307.AlgorithmParameters

theorem accuracy_budget (n:ℕ) (ε:ℚ) (hε:0 < ε):
    4≤ accuracyDenominator n ε∧
      (Lax263307.RecursionDepth.depth n:ℚ) * (4 / accuracyDenominator n ε)≤ ε:=by
  let E:= ⌈ε⁻¹⌉₊
  let d:=Lax263307.RecursionDepth.depth n
  have hE:0 < E:=Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hEq:(0:ℚ) < E:=Nat.cast_pos.mpr hE
  have hdq:(0:ℚ) < (d+1:ℕ):=Nat.cast_pos.mpr (by omega)
  have hD:4≤ accuracyDenominator n ε:=by
    change 4≤ 4 * (d+1) * E
    nlinarith only [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hE)]
  refine ⟨hD, ?_⟩
  have hceil:ε⁻¹≤ (E:ℚ):=Nat.le_ceil _
  have hprod:1≤ ε * (E:ℚ):=by
    have hh:=mul_le_mul_of_nonneg_left hceil hε.le
    simpa only [mul_inv_cancel₀ hε.ne'] using hh
  have hdiv:1 / (E:ℚ)≤ ε:=(div_le_iff₀ hEq).mpr (by nlinarith only [hprod])
  apply le_trans _ hdiv
  change (d:ℚ) * (4 / (4 * (d+1) * E:ℕ))≤ 1 / (E:ℚ)
  push_cast
  apply (le_div_iff₀ hEq).mpr
  have hd:(0:ℚ) < (d:ℚ)+1:=by positivity
  field_simp
  ring_nf
  linarith

open Lax263307.PowerBagBounds

end Lax263307Proofs.RecursiveAlgorithm

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

def child {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b D fuel:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (S:Finset (Fin n)) (t:ℕ):Option (Finset (Fin n)):=
  (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t).map
    (fun I => I.image (label S))

end Lax263307Proofs.NativeRecursiveOracle

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

end Lax263307Proofs.NativeProgramCache

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

namespace Lax263307Proofs.NativeConditioningResources

open Lax263307 RationalConditioning NativeSignedArithmetic

theorem test_polynomial (k p D M H R:ℕ) (hk:k≤ R) (hp:p≤ R) (hD:D≤ R)
    (hM:M≤ R) (hH:H≤ R) (hR:1≤ R):testBound k p D M H≤32*R^5:=by
  have hmono:testBound k p D M H≤ NativeConditioningTest.resource R R R R R R R:=by
    dsimp [testBound,NativeConditioningTest.resource]
    gcongr
  have h0:1≤ R^5:=one_le_pow₀ hR
  have h1:R≤ R^5:=by simpa using (pow_le_pow_right₀ hR (by omega:1≤5))
  have h2:R^2≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have h3:R^3≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have h4:R^4≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have he:NativeConditioningTest.resource R R R R R R R=3+9*R+4*R^2+3*R^3+3*R^4+2*R^5:=by
    dsimp [NativeConditioningTest.resource]
    ring
  rw [he] at hmono
  nlinarith

end Lax263307Proofs.NativeConditioningResources

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

theorem callback_array (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hp:s∉NativeFlowPrepare.command.warrs) (hi:s∉NativeSplitInput.command.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"]) (hd:s∉NativeFlowCut.decodeCommand.warrs):
    s∉(callback p coeff).warrs:=by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.warrs,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleFrame.command_array p coeff s ho)) hd)

end Lax263307Proofs.NativeSeparatorContext

end

section

namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

theorem eval_mono (P:Polynomial ℕ) {x y:ℕ} (h:x≤ y):P.eval x≤ P.eval y:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  simpa only [hcs] using RamPolynomial.value_mono cs h

end Lax263307Proofs.NativeFlowQueryResources

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

namespace Lax263307Proofs.NativeRawFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem array (p:Lax808846.Ram.Program) (a:String)
    (hpre:a∉NativeRawOracle.prepare.warrs)
    (hvm:a∉["vm.addresses","vm.values","vm.output","vm.input"]):
    a∉(NativeRawOracle.command p).warrs:=by
  have hv:=NativeOracleFrame.command_array p [] a hvm
  simp only [NativeOracleCalls.command,Com.warrs,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.warrs,List.mem_append,not_or] using And.intro hpre hv.2

end Lax263307Proofs.NativeRawFrame

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

end Lax263307Proofs.NativeOracleExecution

end

section

namespace Lax263307Proofs.NativeProjectionQueryBounds

open Lax263307 MomentLP
open NativeSignedArithmetic Lax109476.RationalEncoding

theorem polynomial_bound (R:ℕ):queryBound R≤1000000*(R+1)^6:=by
  let S:=R+1
  have hS:1≤ S:=by dsimp [S]; omega
  have hR:R≤ S:=by dsimp [S]; omega
  have h12:S≤ S^2:=le_self_pow hS (by omega)
  have h13:S≤ S^3:=le_self_pow hS (by omega)
  have h23:S^2≤ S^3:=Nat.pow_le_pow_right hS (by omega)
  have h03:1≤ S^3:=Nat.one_le_pow _ _ hS
  have hc:100*(4*R+2)^3≤6400*S^3:=by
    calc
      _≤100*(4*S)^3:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [S]; omega) _)
      _=_:=by ring
  have hheight:rootHeight R≤7000*S^3:=by
    dsimp [rootHeight,scaleHeight]
    change 100*(4*R+2)^3+10+2*(80*S+4*R+1)+1≤7000*S^3
    nlinarith only [hc,hR,h13,h03]
  have hrows:rootRows R+2*R≤8*S^2:=by
    change 6*S^2+2*R≤8*S^2
    nlinarith only [hR,h12]
  have hprod:(rootRows R+2*R)*S≤8*S^3:=by
    simpa only [pow_succ,Nat.mul_assoc] using Nat.mul_le_mul_right S hrows
  have hwords:NativeDistanceData.wordLength (rootRows R) R≤60*S^3:=by
    have hexpr:2+3*((rootRows R+2*R)*S+(rootRows R+2*R)+S)≤60*S^3:=by
      nlinarith only [hprod,hrows,h23,h13,h03]
    simpa only [NativeDistanceData.wordLength,NativeDistanceData.rows,NativeDistanceData.columns,S,Nat.two_mul] using hexpr
  have hfactor:rootHeight R+rootRows R+2*R+4≤8000*S^3:=by
    nlinarith only [hheight,hrows,h23,h03]
  calc
    queryBound R≤(60*S^3)*(8000*S^3):=Nat.mul_le_mul hwords hfactor
    _=480000*S^6:=by ring
    _≤1000000*S^6:=Nat.mul_le_mul_right _ (by decide)

end Lax263307Proofs.NativeProjectionQueryBounds

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeProjectionResources

open Lax263307 Lax109476.RationalEncoding

def buffers:List String:= ["lp.input","lp.word","projection.center","projection.tolerance",
  "vm.addresses","vm.values","vm.output","cut.source","round.normal"]

theorem tolerance_guard (n D F R:ℕ) (hn:n≤ R) (hD:D≤ R) (hF:F≤ R):
    NativeNodeTolerance.guard n D F≤1000*(R+1)^5:=by
  have hs:NativeNodeTolerance.guard n D F≤ NativeNodeTolerance.guard R R R:=by
    dsimp only [NativeNodeTolerance.guard,NativeNodeTolerance.denominator]
    gcongr
  apply hs.trans
  dsimp only [NativeNodeTolerance.guard,NativeNodeTolerance.denominator]
  nlinarith only [Nat.zero_le (R^5),Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]

theorem bounds {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k r F R w T:ℕ) (extent:String→ ℕ)
    (hn:0< n) (hD:0< D) (hF:0< F) (hnR:n≤ R) (hDR:D≤ R) (hFR:F≤ R)
    (hN:MomentLP.dimension n r≤ R) (hw:wordHeight R≤ w)
    (room:∀ s∈buffers,space R T≤ extent s):
    NativeOracleExecution.ProjectionBounds D k r F (2^(100*(R+1))) w T G extent:=by
  let N:=MomentLP.dimension n r
  let m:=NativeMomentAssembly.rowCount n r
  have hm:m≤ NativeProjectionQueryBounds.rootRows R:=by
    have hprod:=Nat.mul_le_mul hN hnR
    dsimp only [m,NativeMomentAssembly.rowCount,NativeProjectionQueryBounds.rootRows]
    change 2+(N+(N+(N*n+(N+N))))≤6*(R+1)^2
    change N*n≤ R*R at hprod
    nlinarith only [hprod,hN]
  have hshape:NativeDistanceData.shapeSize m N≤
      NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R:=by
    dsimp only [NativeDistanceData.shapeSize,NativeDistanceData.wordLength,
      NativeDistanceData.rows,NativeDistanceData.columns]
    gcongr
  have hlen:(encodeProgram (MomentLP.program G k r)).length=
      2+3*(m*N)+3*(m+N):=NativeMomentInput.input_length G k r
  have hmain:(encodeProgram (MomentLP.program G k r)).length+
      NativeDistanceData.wordLength m N+4*N+10≤ shape R:=by
    have hpow:R+1≤(R+1)^5:=le_self_pow (by omega) (by decide)
    have hpad:2*N≤1000*(R+1)^5:=by change MomentLP.dimension n r≤ R at hN; omega
    calc
      _≤ NativeDistanceData.shapeSize m N+2*N:=by
        rw [hlen]; dsimp only [NativeDistanceData.shapeSize]; omega
      _≤ NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R+1000*(R+1)^5:=
        Nat.add_le_add hshape hpad
      _≤ shape R:=by dsimp only [shape]; omega
  have ht:=tolerance_guard n D F R hnR hDR hFR
  have hbase:200*(R+1)+shape R≤ w:=hw
  have hword:w<2^w:=Nat.lt_two_pow_self
  have hsmall:4*R+20≤ w:=by
    have hshape0:=Nat.zero_le (shape R)
    omega
  have hrat:2*(2^(100*(R+1)))^2+3<2^w:=by
    have hexp:2*(100*(R+1))+4≤ w:=by
      have hh:4≤ shape R:=by dsimp only [shape]; omega
      omega
    have hp:=Nat.pow_le_pow_right (by decide:1≤2) hexp
    have he:2^(2*(100*(R+1))+4)=16*(2^(100*(R+1)))^2:=by
      rw [pow_add,Nat.mul_comm 2 (100*(R+1)),pow_mul]; norm_num; ring
    rw [he] at hp
    have hpos:=Nat.one_le_pow (100*(R+1)) 2 (by decide)
    nlinarith only [hp,hpos]
  have scale:4*N≤2^(100*(R+1)):=
    (show 4*N≤100*(R+1) by omega).trans Nat.lt_two_pow_self.le
  have inroom (s:String) (hs:s∈buffers):shape R+T+10≤ extent s:=room s hs
  refine ⟨hn,hD,hF,?_,hrat,?_,scale,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (by omega:(encodeProgram (MomentLP.program G k r)).length+2≤ w).trans_lt hword
  · exact (by omega:4*MomentLP.dimension n r+5≤ w).trans_lt hword
  · have hs:1000*(R+1)^5≤ shape R:=by dsimp only [shape]; omega
    exact (ht.trans (by omega)).trans_lt hword
  · exact (by omega:n+19≤ w).trans_lt hword
  · have h:=inroom "lp.input" (by simp [buffers]); omega
  · have h:=inroom "lp.word" (by simp [buffers]); omega
  · have h:=inroom "projection.center" (by simp [buffers]); omega
  · have h:=inroom "lp.word" (by simp [buffers]); omega
  · have h:=inroom "projection.tolerance" (by simp [buffers]); omega
  · have h:=inroom "lp.word" (by simp [buffers]); change NativeDistanceData.wordLength m N< extent "lp.word"; omega
  · have h:=inroom "vm.addresses" (by simp [buffers]); omega
  · have h:=inroom "vm.values" (by simp [buffers]); omega
  · have h:=inroom "vm.output" (by simp [buffers]); omega
  · have h:=inroom "cut.source" (by simp [buffers]); omega
  · have h:=inroom "round.normal" (by simp [buffers]); omega

end Lax263307Proofs.NativeProjectionResources

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeOracleRounds

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem update_array (cfg:Config) (s:String)
    (hq:s∉NativeRoundedQuery.command.warrs) (hp:s∉NativeRawOracle.prepare.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (hs:s∉NativeRoundedState.command.warrs):
    s∉(NativeRoundedControl.command cfg.rounded 4 14).warrs:=by
  have hu:=NativeRawFrame.array cfg.rounded s hp ho
  simp_all only [NativeRoundedControl.command,NativeRoundedUpdate.command,
    NativeRoundedControl.finish,NativeAttemptReply.noneCommand,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

end Lax263307Proofs.NativeOracleRounds

end

section

namespace Lax263307Proofs.NativeQuadraticResources

open NativeQuadraticSum

theorem square_power (h:ℕ):(2^h)^2=2^(2*h):=by
  rw [←pow_mul,Nat.mul_comm h 2]

theorem height_bits (n h:ℕ):height (2^h) n=2^((2*h+1)*(n*n+1)):=by
  rw [height,square_power]
  have he:2*2^(2*h)=2^(2*h+1):=by rw [pow_add,pow_one]; exact Nat.mul_comm _ _
  rw [he,←pow_mul]

end Lax263307Proofs.NativeQuadraticResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeHeavyResources

open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def span (n r k p h:ℕ):ℕ:=n+r+k+p+N n r+h+20

def wordExponent (n r k p h:ℕ):ℕ:=36*(span n r k p h)^4+10

theorem guards (n r k p h w:ℕ) (hw:wordExponent n r k p h≤ w):
    3*N n r+10<2^w∧ 3*(n*n)+3*n+r+10<2^w∧ 2^n<2^w∧
    2*(2^h)^2+3<2^w∧ 2*(NativeQuadraticSum.height (2^h) n)^2+3<2^w∧
    NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      (2^h) (NativeQuadraticSum.height (2^h) n)<2^w∧
    NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<2^w:=by
  let S:=span n r k p h
  let E:=6*S^4
  let R:=2^E
  have hS:20≤ S:=by dsimp [S,span]; omega
  have hn:n+1≤ S:=by dsimp [S,span]; omega
  have hk:k≤ S:=by dsimp [S,span]; omega
  have hp:p≤ S:=by dsimp [S,span]; omega
  have hr:r≤ S:=by dsimp [S,span]; omega
  have hN:N n r≤ S:=by dsimp [S,span]; omega
  have hh:h≤ S:=by dsimp [S,span]; omega
  have hS2:S≤ S^2:=by nlinarith only [hS]
  have hS3:S^2≤ S^3:=pow_le_pow_right₀ (by omega:1≤ S) (by omega)
  have hS4:S^3≤ S^4:=pow_le_pow_right₀ (by omega:1≤ S) (by omega)
  have hSE:S≤ E:=by dsimp [E]; omega
  have hER:E≤ R:=(Nat.lt_two_pow_self).le
  have hSR:S≤ R:=hSE.trans hER
  have hR:1≤ R:=one_le_pow₀ (by decide:1≤(2:ℕ))
  have hR2:R≤ R^2:=by nlinarith only [hR]
  have hR5:R^2≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have hMR:2^h≤ R:=Nat.pow_le_pow_right (by decide) (hh.trans hSE)
  have hheight:(2*h+1)*(n*n+1)≤ E:=by
    have ht:(2*h+1)*(n*n+1)≤(2*S+1)*(S*S+1):=by gcongr <;> omega
    dsimp [E]
    nlinarith only [ht,hS,hS4,Nat.zero_le (S^2)]
  have hHR:NativeQuadraticSum.height (2^h) n≤ R:=by
    rw [NativeQuadraticResources.height_bits]
    exact Nat.pow_le_pow_right (by decide) hheight
  have hbase:NativeConditioningFloor.base n p≤2*S^3:=by
    have hlog:Nat.log2 n+1≤ S:=(Nat.add_le_add_right (Nat.log2_le_self n) 1).trans hn
    dsimp [NativeConditioningFloor.base]
    calc
      2*n*p*(Nat.log2 n+1)≤2*S*S*S:=by gcongr <;> omega
      _=2*S^3:=by ring
  have hbaseE:NativeConditioningFloor.base n p≤ E:=by dsimp [E]; omega
  have hDR:NativeConditioningFloor.base n p^r≤ R:=by
    calc
      NativeConditioningFloor.base n p^r≤(2^(2*S^3))^r:=
        Nat.pow_le_pow_left (hbase.trans (Nat.lt_two_pow_self).le) r
      _=2^((2*S^3)*r):=(pow_mul _ _ _).symm
      _≤ 2^E:=Nat.pow_le_pow_right (by decide) (by dsimp [E]; nlinarith only [Nat.mul_le_mul_left (2*S^3) hr,Nat.zero_le (S^4)])
  have hcommon:128*R^5<2^w:=by
    have heq:128*R^5=2^(5*E+7):=by
      dsimp [R]
      rw [←pow_mul,pow_add]
      norm_num
      rw [Nat.mul_comm E 5,Nat.mul_comm]
    rw [heq]
    apply Nat.pow_lt_pow_right (by decide)
    change 36*S^4+10≤ w at hw
    dsimp [E]
    omega
  have hkR:=hk.trans hSR
  have hpR:=hp.trans hSR
  have hnR:n≤ R:=(by omega:n≤ S).trans hSR
  have hrR:=hr.trans hSR
  have hNR:=hN.trans hSR
  have hbaseR:=hbaseE.trans hER
  have hM2:(2^h)^2≤ R^2:=Nat.pow_le_pow_left hMR 2
  have hH2:(NativeQuadraticSum.height (2^h) n)^2≤ R^2:=Nat.pow_le_pow_left hHR 2
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact lt_of_le_of_lt (by nlinarith only [Nat.mul_le_mul hnR hnR,hnR,hrR,hR,hR2,hR5]) hcommon
  · exact (Nat.pow_le_pow_right (by decide) ((by omega:n≤ S).trans hSE)).trans_lt
      (lt_of_le_of_lt (by omega:R≤128*R^5) hcommon)
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact (NativeConditioningResources.test_polynomial k p (NativeConditioningFloor.base n p^r)
      (2^h) (NativeQuadraticSum.height (2^h) n) R hkR hpR hDR hMR hHR hR).trans_lt
      (lt_of_le_of_lt (by omega) hcommon)
  · exact lt_of_le_of_lt (by omega) hcommon

end Lax263307Proofs.NativeHeavyResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNearResources

open Lax263307 NativeCoreMachine

def buffers:List String:= ["child.graph","search.graph","subset.bits","restrict.vertices","lp.word",
  "cut.source","sum.input","near.moments","near.costs","lp.input","round.normal","separator.pieces"]

theorem bounds (cfg:Config) (n r D k p fuel S H R w:ℕ) (extent:String→ ℕ) (front:List ℕ)
    (hn:0< n) (hD:0< D) (hp:0< p) (hnR:n≤ R) (hrR:r≤ R) (hDR:D≤ R)
    (hkR:k≤ R) (hpR:p≤ R) (hNR:NativeCatalogMetadata.N n r≤ R) (hf:fuel≤2*R+2)
    (hw:wordHeight cfg R H S front.length≤ w)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (hstack:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤ extent "recursion.frames")
    (hroom:∀ a∈buffers,space R≤ extent a):
    NativeNearExecution.Bounds n r D k p (2^H) (2*H) (R+1) fuel S w cfg extent front:=by
  have hspan:NativeHeavyResources.span n r k p H≤5*R+H+20:=by
    dsimp only [NativeHeavyResources.span]; omega
  have hheavy:NativeHeavyResources.wordExponent n r k p H≤36*(5*R+H+20)^4+10:=by
    dsimp only [NativeHeavyResources.wordExponent]
    gcongr
  have hwHeavy:NativeHeavyResources.wordExponent n r k p H≤ w:=by
    dsimp only [wordHeight] at hw
    omega
  have guards:=NativeHeavyResources.guards n r k p H w hwHeavy
  have hcomponent:NativeComponentDecision.wordHeight n D k (2*H)≤
      2*((2*H+1)*(R+1))+4*(3*R+20)+20:=by
    dsimp only [NativeComponentDecision.wordHeight,NativeComponentResources.span]
    gcongr <;> omega
  have hwComponent:NativeComponentDecision.wordHeight n D k (2*H)≤ w:=by
    dsimp only [wordHeight] at hw
    omega
  have hnn:n*n≤ R*R:=Nat.mul_self_le_mul_self hnR
  have hcollection:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
      2*(n+1)+(R+1)+fuel+3*NativeCatalogMetadata.N n r+80≤ w:=by
    dsimp only [wordHeight] at hw
    omega
  have hreply:n+19<2^w:=by
    have h:n+19≤ w:=by omega
    exact h.trans_lt Nat.lt_two_pow_self
  have hspace:n*n+3*n+3*(n*n)+3*NativeCatalogMetadata.N n r+n+1< space R:=by
    dsimp only [space]
    nlinarith only [hnn,hnR,hNR,Nat.zero_le (R^2)]
  have room (a:String) (ha:a∈buffers):
      n*n+3*n+3*(n*n)+3*NativeCatalogMetadata.N n r+n+1< extent a:=hspace.trans_le (hroom a ha)
  refine ⟨hn,hD,hp,Nat.one_le_pow _ _ (by decide),hreply,guards.1,guards.2.1,guards.2.2.1,
    guards.2.2.2.1,guards.2.2.2.2.1,guards.2.2.2.2.2.1,guards.2.2.2.2.2.2,?_,hwComponent,
    hcollection.trans_lt Nat.lt_two_pow_self,hext,hstack,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←pow_mul,Nat.mul_comm H 2]
  · have h:=room "child.graph" (by simp [buffers]); omega
  · have h:=room "search.graph" (by simp [buffers]); omega
  · have h:=room "subset.bits" (by simp [buffers]); omega
  · have h:=room "restrict.vertices" (by simp [buffers]); omega
  · have h:=room "lp.word" (by simp [buffers]); omega
  · have h:=room "cut.source" (by simp [buffers]); omega
  · have h:=room "sum.input" (by simp [buffers]); omega
  · have h:=room "near.moments" (by simp [buffers]); omega
  · have h:=room "near.costs" (by simp [buffers]); omega
  · have h:=room "lp.input" (by simp [buffers]); omega
  · have h:=room "round.normal" (by simp [buffers]); omega
  · have h:=room "separator.pieces" (by simp [buffers]); omega

end Lax263307Proofs.NativeNearResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRoundedResources

open Lax263307 RoundedOracleSearch Matrix

def buffers:List String:= ["lp.word","vm.input","vm.addresses","vm.values",
  "vm.output","round.shape","round.center"]

end Lax263307Proofs.NativeRoundedResources

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedRounds

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch Matrix
open NativeCoreMachine

abbrev level (cfg:Config) (n D:ℕ):=AlgorithmParameters.level cfg.a cfg.K cfg.b n D
abbrev F (cfg:Config) (n D:ℕ):=(floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)
abbrev N (cfg:Config) (n D:ℕ):=MomentLP.dimension n (level cfg n D)
abbrev limit (cfg:Config) (n D:ℕ):=iterations cfg.a cfg.K cfg.b n D
abbrev H {lp:List ℕ→ List ℕ} (p:NativeSelectedLP.Program lp) (R:ℕ):=NativeSelectedLP.certificateHeight p R
abbrev flowH {lp:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp) (n D k R:ℕ):=
  NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H p R)
abbrev space {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) (n D k R:ℕ):=NativeUniformFlow.spaceBound n (flowH cfg p n D k R) q.time

structure Bounds {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v c R w:ℕ) (extent:String→ ℕ) (front:List ℕ):Prop where
  nR:n≤ R
  kR:k≤ R
  levelR:level cfg n D≤ R
  denominatorR:D≤ R
  floorR:F cfg n D≤ R
  dimensionR:N cfg n D≤ R
  roundsR:limit cfg n D≤ R
  projection:NativeOracleExecution.ProjectionBounds D k (level cfg n D) (F cfg n D)
    (2^(100*(R+1))) w (NativeSelectedLP.oracleTime p R) G extent
  near:NativeNearExecution.Bounds n (level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    (2^H p R) (2*H p R) (R+1) fuel S w cfg extent front
  lpWidth:NativeSelectedLP.wordHeight p R≤ w
  farWidth:NativeCutResources.wordExponent (N cfg n D) (2*H p R+1)+4≤ w
  queryRoom:NativeSelectedLP.queryBound R< extent "vm.input"
  flowWidth:NativeUniformFlow.wordHeight n (flowH cfg p n D k R) q.code q.width q.time q.output≤ w
  flowSpace:∀ a∈NativeSeparatorContext.workspace,space cfg p q n D k R≤ extent a
  roundedWidth:c*(2*R+NativeOraclePrecision.roundedHeight p.width R+1)^12≤ v
  roundedHost:NativeRoundedResources.wordHeight cfg.rounded v R (NativeOraclePrecision.roundedHeight p.width R)≤ w
  roundedSpace:∀ a∈NativeRoundedResources.buffers,
    NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)≤ extent a

end Lax263307Proofs.NativeSelectedRounds

end

section

namespace Lax263307Proofs.NativePolynomialBudget

open Lax455465Proofs

set_option maxHeartbeats 0

theorem height_bound (wp:Polynomial ℕ) (R:ℕ):
    NativeOraclePrecision.roundedHeight wp R≤(heightPolynomial wp).eval R:=by
  have hq:=Lax263307Proofs.NativeProjectionQueryBounds.polynomial_bound R
  have hp:=Lax263307Proofs.NativeFlowQueryResources.eval_mono wp hq
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp [NativeOraclePrecision.roundedHeight,NativeOraclePrecision.certificateHeight]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1)) _) _) _

end Lax263307Proofs.NativePolynomialBudget

end

section

namespace Lax263307Proofs.NativePolynomialEnvelope

def Bounded (f:ℕ→ ℕ):Prop:= ∃ P:Polynomial ℕ,∀ R,f R≤ P.eval R

theorem eval (P:Polynomial ℕ) {f:ℕ→ ℕ} (hf:Bounded f):Bounded (fun R => P.eval (f R)):=by
  obtain ⟨Q,hQ⟩:=hf
  exact ⟨P.comp Q,fun R => by simpa only [Polynomial.eval_comp] using NativeFlowQueryResources.eval_mono P (hQ R)⟩

end Lax263307Proofs.NativePolynomialEnvelope
end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeFlowBudget

open Lax455465Proofs NativeLargeCapacity NativeLargeResources NativeUniformFlow

private theorem logarithm_bound (n R:ℕ) (hn:n≤ R):Nat.log2 (2*n)+1≤2*R+1:=by
  have h:Nat.log2 (2*n)≤2*n:=by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 (2*n)
  omega

theorem height_bound (b n load k h R:ℕ) (hp:Polynomial ℕ)
    (hn:n≤ R) (hl:load≤ R) (hk:k≤ R) (hh:h≤ hp.eval R):
    heightExponent b n load k h≤(heightPolynomial b hp).eval R:=by
  have hlog:=logarithm_bound n R hn
  have hnum:numerator b n n k≤(numeratorPolynomial b).eval R:=by
    simp only [numeratorPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [numerator]
    gcongr
  have hres:resource b n n load k≤(resourcePolynomial b).eval R:=by
    simp only [resourcePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [resource,denominator]
    gcongr
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp only [heightExponent]
  omega

theorem query_bound (b n H R:ℕ) (hp:Polynomial ℕ)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    NativeFlowQueryResources.sizeBound n H≤(queryPolynomial b hp).eval R:=by
  simp only [queryPolynomial,lengthPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp only [NativeFlowQueryResources.sizeBound,NativeSplitInput.wordLength]
  gcongr

theorem width_bound (b n H R:ℕ) (hp wp tp op:Polynomial ℕ) (p:Lax808846.Ram.Program)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    wordHeight n H p wp tp op≤(widthPolynomial b hp wp tp op p).eval R:=by
  have hS:=query_bound b n H R hp hn hH
  have hw:=NativeFlowQueryResources.eval_mono wp (Nat.add_le_add_right hS 1)
  have ht:=NativeFlowQueryResources.eval_mono tp hS
  have ho:=NativeFlowQueryResources.eval_mono op hS
  simp only [widthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp only [wordHeight,shape]
  gcongr

theorem space_bound (b n H R:ℕ) (hp tp:Polynomial ℕ)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    spaceBound n H tp≤(spacePolynomial b hp tp).eval R:=by
  have hS:=query_bound b n H R hp hn hH
  have ht:=NativeFlowQueryResources.eval_mono tp hS
  simp only [spacePolynomial,lengthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_ofNat]
  dsimp only [spaceBound,NativeSplitInput.wordLength]
  gcongr

end Lax263307Proofs.NativeFlowBudget

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedBudget

open Lax263307 NativeCoreMachine NativePolynomialEnvelope

theorem cost_height {lp:List ℕ→ List ℕ} (p:NativeSelectedLP.Program lp) (R:ℕ):
    2*NativeSelectedLP.certificateHeight p R≤ (NativePolynomialBudget.heightPolynomial p.width).eval R:=by
  have h:=NativePolynomialBudget.height_bound p.width R
  have hm:2*NativeSelectedLP.certificateHeight p R+1≤
      (R+1)*(2*NativeSelectedLP.certificateHeight p R+1):=Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [NativeOraclePrecision.roundedHeight] at h
  change 80*(R+1)+(R+1)*(2*NativeSelectedLP.certificateHeight p R+1)+2*R+1≤ _ at h
  omega

end Lax263307Proofs.NativeSelectedBudget

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSourceFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine

theorem base_blowup_owner (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "blowup.owner"∉c.warrs:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "blowup.owner"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "blowup.owner"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_image_output (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "image.output"∉c.warrs:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "image.output"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "image.output"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_weighted_output (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "weighted.output"∉c.warrs:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "weighted.output"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "weighted.output"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem array_unsaved (cfg:Config) (a:String)
    (ha:a∈["blowup.owner","image.output","weighted.output"]):a∉frameArrays cfg:=by
  intro h
  simp only [frameArrays,List.mem_filter,List.mem_dedup] at h
  obtain ⟨c,hc,hw⟩:=List.mem_flatMap.mp h.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  · exact base_blowup_owner cfg c hc hw
  · exact base_image_output cfg c hc hw
  · exact base_weighted_output cfg c hc hw

end Lax263307Proofs.NativeSourceFrame

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeRootWorkspace

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds

theorem ordinary (cfg:Config) (rootN W originalN:ℕ) (a:String)
    (ha:a∉["recursion.frames","image.output","weighted.output"]):
    extent cfg rootN W originalN a=stride W:=by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at ha
  simp only [extent,if_neg ha.1,if_neg ha.2.1,if_neg ha.2.2]

theorem buffer_room (cfg:Config) (rootN W originalN amount:ℕ) (buffers:List String)
    (clean:List.Disjoint buffers ["recursion.frames","image.output","weighted.output"])
    (hamount:amount≤ W):∀ a∈buffers,amount≤ extent cfg rootN W originalN a:=by
  intro a ha
  rw [ordinary cfg rootN W originalN a (List.disjoint_left.mp clean ha)]
  dsimp only [stride]
  omega

theorem frame_extents (cfg:Config) (rootN W originalN:ℕ):
    ∀ a∈frameArrays cfg,extent cfg rootN W originalN a=stride W:=by
  intro a ha
  apply ordinary
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rintro (rfl|rfl|rfl)
  · have h:=ha
    simp only [frameArrays,List.mem_filter,List.mem_dedup,bne_iff_ne] at h
    exact h.2 rfl
  · exact NativeSourceFrame.array_unsaved cfg _ (by simp) ha
  · exact NativeSourceFrame.array_unsaved cfg _ (by simp) ha

theorem bounds {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) (c rootN originalN R W w:ℕ)
    (hK:0< cfg.K) (hb:0< cfg.b) (hroot:rootN≤ R)
    (budget:NativeSelectedBudget.demand cfg p q c R≤ W) (host:hostHeight cfg W≤ w)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel:ℕ) (front:List ℕ)
    (hn:0< n) (hD:0< D) (hk:k≤ n) (hf:fuel≤ 2*R+2)
    (resource:ParameterResources.resource cfg.a cfg.K cfg.b n D≤ R)
    (stack:front.length+frameLength cfg W≤ capacity cfg rootN W):
    NativeSelectedRounds.Bounds cfg p q G D k fuel (stride W) W c R w (extent cfg rootN W originalN) front:=by
  have hdem:=budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hR:R≤ W:=by omega
  have hcert:H p R≤ W:=by change NativeSelectedLP.certificateHeight p R≤ W; omega
  have hroundH:NativeOraclePrecision.roundedHeight p.width R≤ W:=by omega
  have hhost:W≤ w:=by dsimp only [hostHeight] at host; omega
  have hnR:n≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hkR:k≤ R:=hk.trans hnR
  have hrR:level cfg n D≤ R:=by dsimp only [ParameterResources.resource,NativeSelectedRounds.level] at resource ⊢; omega
  have hDR:D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hpR:sparsity cfg.a cfg.K cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hNR:N cfg n D≤ R:=by dsimp only [ParameterResources.resource,N,NativeSelectedRounds.level] at resource ⊢; omega
  have hlR:load cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hiR:limit cfg n D≤ R:=by dsimp only [ParameterResources.resource,limit] at resource ⊢; omega
  have hp:0< sparsity cfg.a cfg.K cfg.b n D:=by
    unfold sparsity targetThreshold
    exact Nat.mul_pos (by decide) (Nat.mul_pos hK (Nat.pow_pos (by omega)))
  have hfloor:0< F cfg n D:=by
    apply Nat.pow_pos
    unfold floorDenominator
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hn) hp) (by omega)
  have hdim:2≤ N cfg n D:=Lax263307Proofs.CoordinateCatalog.catalog_two n (level cfg n D) hn
  have hNpos:0< N cfg n D:=lt_of_lt_of_le (by decide) hdim
  have hFR:F cfg n D≤ R:=by
    have hrad:radiusDenominator cfg.a cfg.K cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
    have hfactor:0<256*N cfg n D*n^2*D^2:=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hNpos) (Nat.pow_pos hn)) (Nat.pow_pos hD)
    have h:=Nat.le_mul_of_pos_left (F cfg n D) hfactor
    apply h.trans
    exact hrad
  have hdepth:RecursionDepth.depth rootN≤ 2*W+2:=by
    have h:=Lax263307Proofs.RecursionDepth.logarithmic_bound rootN
    have hl:Nat.log2 rootN≤ rootN:=Nat.log2_le_self rootN
    omega
  have hcursor:front.length≤ (2*W+2)*frameLength cfg W:=by
    have hcap:=Nat.mul_le_mul_right (frameLength cfg W) hdepth
    dsimp only [capacity] at stack
    omega
  have hnearWord:NativeNearResources.wordHeight cfg R (H p R) (stride W) front.length≤ w:=by
    have hm:NativeNearResources.wordHeight cfg R (H p R) (stride W) front.length≤
        NativeNearResources.wordHeight cfg W W (stride W) ((2*W+2)*frameLength cfg W):=by
      have hbase:5*R+H p R+20≤ 5*W+W+20:=by omega
      have hp:=Nat.mul_le_mul_left 36 (Nat.pow_le_pow_left hbase 4)
      have hprod:=Nat.mul_le_mul (show 2*H p R+1≤ 2*W+1 by omega) (show R+1≤ W+1 by omega)
      have hsquare:=Nat.mul_self_le_mul_self hR
      dsimp only [NativeNearResources.wordHeight]
      omega
    exact hm.trans (by dsimp only [hostHeight] at host; omega)
  have hnear:=NativeNearResources.bounds cfg n (level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    fuel (stride W) (H p R) R w (extent cfg rootN W originalN) front hn hD hp hnR hrR hDR hkR hpR hNR hf
    hnearWord (frame_extents cfg rootN W originalN) (by simpa [extent,frameLength,Nat.add_assoc] using stack)
    (buffer_room cfg rootN W originalN (NativeNearResources.space R) NativeNearResources.buffers (by simp [List.disjoint_left,NativeNearResources.buffers]) (by omega))
  have hproj:=NativeProjectionResources.bounds G D k (level cfg n D) (F cfg n D) R w (NativeSelectedLP.oracleTime p R)
    (extent cfg rootN W originalN) hn hD hfloor hnR hDR hFR hNR
    ((by omega:NativeProjectionResources.wordHeight R≤ W).trans hhost)
    (buffer_room cfg rootN W originalN (NativeProjectionResources.space R (NativeSelectedLP.oracleTime p R)) NativeProjectionResources.buffers (by simp [List.disjoint_left,NativeProjectionResources.buffers]) (by omega))
  have hheight:=NativeSelectedBudget.cost_height p R
  have flowHeight:=NativeFlowBudget.height_bound cfg.b n (load cfg.b n D) k (2*H p R) R
    (NativePolynomialBudget.heightPolynomial p.width) hnR hlR hkR hheight
  have flowWidth:=NativeFlowBudget.width_bound cfg.b n (flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.width q.time q.output q.code hnR flowHeight
  have flowSpace:=NativeFlowBudget.space_bound cfg.b n (flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.time hnR flowHeight
  have roundedHost:NativeRoundedResources.wordHeight cfg.rounded W R
      (NativeOraclePrecision.roundedHeight p.width R)≤ w:=by
    have hm:NativeRoundedResources.wordHeight cfg.rounded W R
        (NativeOraclePrecision.roundedHeight p.width R)≤ NativeRoundedResources.wordHeight cfg.rounded W W W:=by
      dsimp only [NativeRoundedResources.wordHeight]; gcongr
    exact hm.trans (by dsimp only [hostHeight] at host; omega)
  refine ⟨hnR,hkR,hrR,hDR,hFR,hNR,hiR,hproj,hnear,(by omega),?_,?_,?_,?_,?_,roundedHost,?_⟩
  · have hm:NativeCutResources.wordExponent (N cfg n D) (2*H p R+1)≤ NativeCutResources.wordExponent R (2*H p R+1):=by
      dsimp only [NativeCutResources.wordExponent]; gcongr
    have hfar:NativeCutResources.wordExponent R (2*H p R+1)+4≤ W:=by
      change NativeCutResources.wordExponent R (2*NativeSelectedLP.certificateHeight p R+1)+4≤ W
      omega
    exact (Nat.add_le_add_right hm 4).trans (hfar.trans hhost)
  · rw [ordinary cfg rootN W originalN "vm.input" (by decide)]
    dsimp only [stride]
    omega
  · exact flowWidth.trans (by omega)
  · apply buffer_room cfg rootN W originalN _ NativeSeparatorContext.workspace (by simp [List.disjoint_left,NativeSeparatorContext.workspace])
    exact flowSpace.trans (by omega)
  · have hspace:NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)≤ W:=by omega
    dsimp only [NativeRoundedResources.space] at hspace
    omega
  · exact buffer_room cfg rootN W originalN _ NativeRoundedResources.buffers (by simp [List.disjoint_left,NativeRoundedResources.buffers]) (by omega)

end Lax263307Proofs.NativeRootWorkspace

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeUnweightedExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 GraphClasses
open NativeCoreMachine NativeRootWorkspace

theorem guards (cfg:Config) (n R W w:ℕ) (hn:n≤ R) (hR:R≤ W) (hw:hostHeight cfg W≤ w):
    stride W*(frameArrays cfg).length+(frameScalars cfg).length+stride W+(frameArrays cfg).length+10<2^w∧
    n+RecursionDepth.depth n+20<2^w∧ 2^n<2^w:=by
  have hA:(frameArrays cfg).length≤ stride W*(frameArrays cfg).length:=Nat.le_mul_of_pos_left _ (by dsimp only [stride]; omega)
  have hframe:frameLength cfg W≤ (2*W+2)*frameLength cfg W:=Nat.le_mul_of_pos_left _ (by omega)
  have hdep:=Lax263307Proofs.RecursionDepth.logarithmic_bound n
  have hlog:=Nat.log2_le_self n
  have hhost:=hw
  dsimp only [hostHeight,NativeNearResources.wordHeight,frameLength,stride] at hhost hA hframe
  have hwidth:n< w:=by omega
  refine ⟨?_,?_,Nat.pow_lt_pow_right (by decide) hwidth⟩
  · exact (by dsimp only [stride]; omega:
      stride W*(frameArrays cfg).length+(frameScalars cfg).length+stride W+(frameArrays cfg).length+10≤ w).trans_lt Nat.lt_two_pow_self
  · exact (by omega:n+RecursionDepth.depth n+20≤ w).trans_lt Nat.lt_two_pow_self

end Lax263307Proofs.NativeUnweightedExecution

end

section

namespace Lax263307Proofs.NativeWeightedOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedAlgorithm IndependentBlowUp WeightedIndependentSet

theorem discard_projected {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ)
    (I:Finset (Fin (∑ v,WeightRounding.copies (PositiveWeights.positiveWeights weights) ε v))):
    PositiveWeights.discardNonpositive weights (project (I.image
      (labeling (WeightRounding.copies (PositiveWeights.positiveWeights weights) ε))))=
      project (I.image (labeling (WeightRounding.copies (PositiveWeights.positiveWeights weights) ε))):=by
  let copies:=WeightRounding.copies (PositiveWeights.positiveWeights weights) ε
  have hpositive:∀ v∈project (I.image (labeling copies)),0< weights v:=by
    intro v hv
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hv
    by_contra hnonpos
    have hw:weights u.1≤0:=by linarith
    have hz:copies u.1=0:=by
      simp [copies,WeightRounding.copies,WeightRounding.roundedCopies,PositiveWeights.positiveWeights,max_eq_right hw]
    have hh:0< copies u.1:=Nat.zero_lt_of_lt u.2.isLt
    omega
  ext v
  simp only [PositiveWeights.discardNonpositive,Finset.mem_filter]
  exact ⟨And.left,fun hv => ⟨hv,hpositive v hv⟩⟩

end Lax263307Proofs.NativeWeightedOutput

end

section

namespace Lax263307Proofs.NativeQptasProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet

theorem copy_graph_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hB:n*n+n+5< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) "blowup.matrix" σ∧
      n*n≤(σ.arrs "search.graph").length) copyGraph
      (fun _ τ => τ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" τ)
      (16*(n*n)+14):=by
  rintro σ ⟨hn,hgraph,hroom⟩
  let ν:=σ.setVar "matrix.length" (n*n)
  have hvar:(Expr.var "graph.n").evalB B σ=some n:=by
    rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega)⟩
  have r1:Run B (.assign "matrix.length" (.mul (.var "graph.n") (.var "graph.n"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul) hvar hvar (by change n*n< B; omega))
  have hlen:(NativeWeightReduction.adjacency G).length=n*n:=by
    simp [NativeWeightReduction.adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]
  have hw:∀ z∈NativeWeightReduction.adjacency G,z< B:=by
    intro z hz
    simp only [NativeWeightReduction.adjacency,List.mem_flatten,List.mem_ofFn] at hz
    obtain ⟨row,⟨i,rfl⟩,hz⟩:=hz
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz
    split_ifs <;> omega
  obtain ⟨τ,r2,p2⟩:=NativeProgramCache.copy_spec B "blowup.matrix" "search.graph" "matrix.length"
    (NativeWeightReduction.adjacency G) (by decide) (by rw [hlen]; omega) hw ν
    ⟨by simpa [Prefix,ν] using hgraph,by simp [ν,hlen],by simpa [ν,hlen] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),
    (r2.frame_var _ (by decide)).trans ((r1.frame_var _ (by decide)).trans hn),p2.2⟩

end Lax263307Proofs.NativeQptasProgram

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeQptasPositive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet
open NativeQptasImplementation NativeRootWorkspace

theorem positive_parameters {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ) (hN:0< order weights ε):
    0< n∧ 0< WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights):=by
  have hn:0< n:=by
    by_contra hn
    have hz:n=0:=by omega
    subst n
    simpa [order] using hN
  refine ⟨hn,?_⟩
  by_contra hmax
  have hmax:WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights)≤ 0:=le_of_not_gt hmax
  have hz (v:Fin n):PositiveWeights.positiveWeights weights v=0:=by
    have hle:PositiveWeights.positiveWeights weights v≤ WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights):=by
      apply Finset.le_max'; simp
    exact le_antisymm (hle.trans hmax) (le_max_right _ _)
  have hc (v:Fin n):copies weights ε v=0:=by
    simp [copies,WeightRounding.copies,WeightRounding.roundedCopies,hz v]
  have he:order weights ε=0:=by simp only [order,hc,Finset.sum_const_zero]
  omega

theorem functional_result {C:GraphClass} (i:Fixed C) {n:ℕ} (G:SimpleGraph (Fin n))
    [DecidableRel G.Adj] (weights:Fin n→ ℚ) (ε:ℚ) (hN:0< order weights ε):
    WeightedAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b G weights ε=
      IndependentBlowUp.project ((RecursiveAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b
        (denominator (order weights ε) ε) (WeightedAlgorithm.numbered G (copies weights ε))).1.image
          (WeightedAlgorithm.labeling (copies weights ε))):=by
  have hp:=positive_parameters weights ε hN
  rw [WeightedAlgorithm.solve,if_neg (by
    rintro (hz|hm)
    · exact hp.1.ne' hz
    · exact not_le_of_gt hp.2 hm)]
  exact NativeWeightedOutput.discard_projected weights ε _

theorem command_spec {C:GraphClass} (i:Fixed C) {n:ℕ} (G:SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG:G∈C n) (weights:Fin n→ ℚ) (ε:ℚ) (hε:0<ε)
    (M w:ℕ) (hM:1≤ M) (hnM:n≤ M)
    (hweights:∀ v,NativeSignedArithmetic.Bounded M (weights v))
    (haccuracy:NativeSignedArithmetic.Bounded M ε) (hN:0< order weights ε)
    (bounds:Bounds i n (order weights ε) M w ε):
    let N:=order weights ε
    let W:=workspace i N ε
    let ext:=extent i.cfg N W n
    Spec (2^w) (fun σ => σ.inp=encodeInput G weights ε∧ NativeStateBounds.Bounded (2^w) σ∧
        ∀ a,(σ.arrs a).length=ext a)
      (NativeQptasProgram.command i.cfg i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent)
      (fun σ τ => τ.out=σ.out++encodeOutput (WeightedAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b G weights ε))
      (cost i n N ε):=by
  dsimp only
  let N:=order weights ε
  let D:=denominator N ε
  let R:=resource i N ε
  let W:=workspace i N ε
  let H:=WeightedAlgorithm.numbered G (copies weights ε)
  let ext:=extent i.cfg N W n
  change 0< N at hN
  change Bounds i n N M w ε at bounds
  have allocation:n*n+N*N+3*n+N+3≤ W:=bounds.allocation
  have outputBound:n+N+5<2^w:=bounds.output
  have hD:4≤ D:=(Lax263307Proofs.RecursiveAlgorithm.accuracy_budget N (ε/2) (by positivity)).1
  have uniform:=i.uniform N D
  have hresource:=uniform N (by omega) hN (Nat.le_refl N)
  change ParameterResources.resource i.cfg.a i.cfg.K i.cfg.b N D≤ R at hresource
  have hnR:N≤ R:=by dsimp only [ParameterResources.resource] at hresource; omega
  have hclass:H∈blowUpClass C N:=Lax263307Proofs.BlowUpClasses.copy_graph_mem C G hG (copies weights ε) _ (WeightedAlgorithm.labeling _)
  have budget:NativeSelectedBudget.demand i.cfg i.projection i.separator i.roundedConstant R≤ W:=i.budget R
  have hguards:=NativeUnweightedExecution.guards i.cfg N R W w hnR (by
    have h:=budget; dsimp only [NativeSelectedBudget.demand] at h; omega) bounds.host
  have core:=NativeUnweightedExecution.command_spec (Lax263307Proofs.BlowUpClasses.hereditary_closure C) i.projection i.separator i.cfg
    i.projectionCode i.projectionCoeff i.separatorCode i.separatorCoeff i.encoded i.separatorCorrect
    i.oracleCorrect i.classK i.classB H hclass hN D i.roundedConstant n R W w hD hnR i.rounded
    (fun m hm hmn => uniform m (by omega) hm hmn) budget bounds.host
  have hMlt:M<2^w:=by
    have hm:=le_self_pow hM (by decide:4≠0)
    nlinarith only [hm,bounds.frontend]
  intro σ hi
  have room (a:String) (ha:a∉["recursion.frames","image.output","weighted.output"]):
      n*n+N*N+3*n+N+3≤ (σ.arrs a).length:=by
    rw [hi.2.2 a,ordinary i.cfg N W n a ha]
    have h:=allocation
    dsimp only [stride]
    omega
  obtain ⟨σ₁,r1,matrix₁,owners₁,order₁,data₁,out₁,input₁⟩:=NativeBlowUp.prepare_spec (2^w) M hM hnM G weights ε
    hε hweights haccuracy bounds.frontend bounds.input (by rw [pow_two]; change n*n+N*N+n+N+3<2^w; exact bounds.graph) σ
    ⟨hi.1,by have h:=room "input.data" (by decide); omega,
      by have h:=room "copy.counts" (by decide); omega,
      (show N≤ (σ.arrs "blowup.owner").length from by have h:=room "blowup.owner" (by decide); omega),
      (show N*N≤ (σ.arrs "blowup.matrix").length from by have h:=room "blowup.matrix" (by decide); omega)⟩
  change Run (2^w) NativeBlowUp.prepare σ σ₁ (NativeBlowUp.cost n N) at r1
  change σ₁.vars "blowup.length"=N at order₁
  change Prefix (NativeWeightReduction.adjacency H) "blowup.matrix" σ₁ at matrix₁
  change Prefix (NativeBlowUp.owners (copies weights ε)) "blowup.owner" σ₁ at owners₁
  let σ₂:=σ₁.setVar "graph.n" N
  have r2:Run (2^w) NativeQptasProgram.order σ₁ σ₂ 2:=Run.assign (by
    rw [evalB_var_iff]
    exact ⟨order₁.symm,order₁ ▸ (by have h:=outputBound; omega)⟩)
  obtain ⟨σ₃,r3,graph₃⟩:=NativeQptasProgram.copy_graph_spec (2^w) H bounds.copy σ₂
    ⟨(show σ₂.vars "graph.n"=N from by simp [σ₂]),by simpa only [Prefix,σ₂,arrs_setVar] using matrix₁,
      (show N*N≤ (σ₂.arrs "search.graph").length from by rw [RamFrames.run_array_length (r1.seq r2)]; have h:=room "search.graph" (by decide); omega)⟩
  change Run (2^w) NativeQptasProgram.copyGraph σ₂ σ₃ (16*(N*N)+14) at r3
  have input₃:σ₃.vars "input.n"=n:=((r2.seq r3).frame_var _ (by decide)).trans input₁
  have data₃:Prefix (NativeFrontend.tailInput G weights ε) "input.data" σ₃:=by
    simpa only [Prefix,(r2.seq r3).frame_arr "input.data" (by decide)] using data₁
  obtain ⟨σ₄,r4,accuracy₄⟩:=NativeOriginalAccuracy.command_spec (2^w) G weights ε bounds.input
    (haccuracy.1.trans_lt hMlt) (haccuracy.2.trans_lt hMlt) σ₃ ⟨input₃,data₃⟩
  obtain ⟨σ₅,r5,root₅⟩:=NativeRootAccuracy.command_spec (2^w) M N ε hε haccuracy bounds.accuracy σ₄
    ⟨(r4.frame_var _ (by decide)).trans graph₃.1,accuracy₄⟩
  obtain ⟨σ₆,r6,budget₆⟩:=NativeRootBudget.command_spec (2^w) i.envelopeCoefficient i.envelopeExponent
    i.budgetCoefficient i.budgetExponent N D hN (by omega) bounds.budget σ₅ ⟨root₅.1,root₅.2.2.1⟩
  have setup:=r4.seq (r5.seq r6)
  have before:=r2.seq (r3.seq setup)
  have graph₆:Prefix (NativeWeightReduction.adjacency H) "search.graph" σ₆:=by
    simpa only [Prefix,setup.frame_arr "search.graph" (by
      change "search.graph"∉(Com.seq NativeOriginalAccuracy.command
        (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))).warrs
      decide)] using graph₃.2
  have input₆:NativeCoreExecution.Input (2^w) D (RecursionDepth.depth N) (stride W) W H ext σ₆:=by
    refine ⟨NativeStateBounds.run (r1.seq before) hi.2.1,⟨budget₆.1,graph₆⟩,budget₆.2.1,?_,budget₆.2.2.2.2,budget₆.2.2.2.1,?_⟩
    · exact (r6.frame_var _ (by change "recursion.fuel"∉(NativeRootBudget.command 0 0 0 0).wvars; decide)).trans root₅.2.2.2
    · intro a; rw [RamFrames.run_array_length (r1.seq before)]; exact hi.2.2 a
  obtain ⟨σ₇,r7,post₇⟩:=core σ₆ input₆
  change Run (2^w) (NativeCoreMachine.command i.cfg) σ₆ σ₇ (NativeUnweightedExecution.cost i.cfg N W) at r7
  have input₇:σ₇.vars "input.n"=n:=post₇.2.2.1.trans ((before.frame_var _ (by
    change "input.n"∉(Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
      (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).wvars
    decide)).trans input₁)
  have order₇:σ₇.vars "blowup.length"=N:=post₇.2.2.2.1.trans ((before.frame_var _ (by
    change "blowup.length"∉(Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
      (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).wvars
    decide)).trans order₁)
  have owners₇:Prefix (NativeBlowUp.owners (copies weights ε)) "blowup.owner" σ₇:=by
    simpa only [Prefix,post₇.2.2.2.2.1,before.frame_arr "blowup.owner" (by
      change "blowup.owner"∉(Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
        (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).warrs
      decide)] using owners₁
  obtain ⟨τ,r8,output₈⟩:=NativeWeightedOutput.command_spec (2^w) (copies weights ε)
    (RecursiveAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b D H).1 bounds.output hguards.2.2 σ₇
    ⟨input₇,order₇,post₇.2.1.1,owners₇,
      (show N≤ (σ₇.arrs "image.labels").length from by rw [RamFrames.run_array_length ((r1.seq before).seq r7)]; have h:=room "image.labels" (by decide); omega),
      by rw [RamFrames.run_array_length ((r1.seq before).seq r7),hi.2.2]; simp [ext,extent]⟩
  change Run (2^w) NativeWeightedOutput.command σ₇ τ (24*n+44*N+36) at r8
  have test:(Cond.eq (.var "graph.n") (.lit 0)).evalB (2^w) σ₂=some false:=by
    have he:=evalB_condEq (show (Expr.var "graph.n").evalB (2^w) σ₂=some N from by
      rw [evalB_var_iff]; exact ⟨by simp [σ₂],by simp only [σ₂,vars_setVar,ite_true]; omega⟩)
      (evalB_lit (show 0<2^w by omega))
    simpa [ne_of_gt hN] using he

  have run:Run (2^w) (NativeQptasProgram.command i.cfg i.envelopeCoefficient i.envelopeExponent
      i.budgetCoefficient i.budgetExponent) σ τ _:=
    r1.seq <| r2.seq <| Run.ite_false test <| r3.seq <| r4.seq <| r5.seq <| r6.seq <| r7.seq r8
  refine ⟨τ,run.mono ?_,?_⟩
  · change _≤ cost i n N ε
    dsimp only [cost,budgetCost,D,W]
    simp only [Cond.size,Expr.size]
    omega
  · rw [functional_result i G weights ε hN]
    have out₆:σ₆.out=σ.out:=(before.out_eq (by
      change (Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
        (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).NoWrite
      decide)).trans out₁
    simpa only [post₇.2.2.2.2.2,out₆] using output₈

end Lax263307Proofs.NativeQptasPositive

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C) {n:Nat}
  (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
  @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n))) (@Set.instMembership (SimpleGraph (Fin n))) (C n)
      G→
    ∀ (weights:Fin n→ Rat) (ε:Rat),
      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
        ∀ (M w:Nat),
          Nat.le ((1:Nat)) M→
            Nat.le n M→
              (∀ (v:Fin n),Lax263307Proofs.NativeSignedArithmetic.Bounded M (weights v))→
                Lax263307Proofs.NativeSignedArithmetic.Bounded M ε→
                  Nat.lt ((0:Nat))
                      (@Lax263307Proofs.NativeQptasPositive.order n weights ε)→
                    @Lax263307Proofs.NativeQptasPositive.Bounds C i n
                        (@Lax263307Proofs.NativeQptasPositive.order n weights ε) M w ε→
                      have N:= @Lax263307Proofs.NativeQptasPositive.order n weights ε;
                      have W:= @Lax263307Proofs.NativeQptasPositive.workspace C i N ε;
                      have ext:=
                        Lax263307Proofs.NativeRootWorkspace.extent
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i) N W n;
                      Lax808846Proofs.Reasoning.Spec
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          ((2:Nat)) w)
                        (fun (σ:Lax808846Proofs.Imp.Env) =>
                          And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst weights ε))
                            (And
                              (Lax263307Proofs.NativeStateBounds.Bounded
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  ((2:Nat)) w)
                                σ)
                              (∀ (a:String), @Eq Nat (@List.length Nat (σ.arrs a)) (ext a))))
                        (Lax263307Proofs.NativeQptasProgram.command
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.envelopeCoefficient C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.envelopeExponent C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.budgetCoefficient C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.budgetExponent C i))
                        (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                          @Eq (List Nat) τ.out
                            (@HAppend.hAppend (List Nat) (List Nat) (List Nat)
                              (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) σ.out
                              (@Lax263307.IndependentSetEncoding.encodeOutput n
                                (@Lax263307.WeightedAlgorithm.solve n
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.lp C i)
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.flow C i)
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).a
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).K
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).b G inst weights ε))))
                        (@Lax263307Proofs.NativeQptasPositive.cost C i n N ε):= @Lax263307Proofs.NativeQptasPositive.command_spec
