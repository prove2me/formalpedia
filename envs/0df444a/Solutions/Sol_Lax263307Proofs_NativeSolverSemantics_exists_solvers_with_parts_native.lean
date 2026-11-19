-- Prove2me | solution 1 for Lax263307Proofs.NativeSolverSemantics.exists_solvers_with_parts_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:59:17.683085+00:00
-- url     : https://prove2.me/submissions/0c231bd1-d129-4caa-9df0-b2224fa5452a

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Logic.Equiv.Sum
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Set.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_10
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.TakeWhile
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.NNRat.BigOperators
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamUniformSolver_exists_exact_polynomial_time_solver
import Theorems.Thm_Lax455465Proofs_RamProductAlgorithm_exists_polynomial_time_flow_cut
import Theorems.Thm_Lax263307Proofs_ProjectedOracle_run_correct_native

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

namespace Lax263307Proofs.ProjectedOracle
end Lax263307Proofs.ProjectedOracle
theorem Lax263307Proofs.ProjectedOracle.run_correct:∀ {n:Nat} (lp flow:List Nat→ List Nat) (a K B D:Nat) (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (k h:Nat),
  Nat.lt ((0:Nat)) K→
    Nat.lt ((0:Nat)) n→
      Nat.le ((4:Nat)) D→
        (∀ (m N:Nat) (P:Lax109476.LinearProgram.Program Rat m N),
            @Lax109476.RationalCertificates.IsValidCertificate m N P (@Lax263307.RegisteredLP.certificate m N lp P))→
          ∀ (child:Finset (Fin n)→ Nat→ Option (Finset (Fin n))),
            (∀ (y:Lax263307.RationalConditioning.RationalVector n (Lax263307.AlgorithmParameters.level a K B n D)),
                @Lax263307.LinearRelaxation.IsFeasible n G k (Lax263307.AlgorithmParameters.level a K B n D)
                    (@Lax263307.RationalConditioning.realVector n (Lax263307.AlgorithmParameters.level a K B n D) y)→
                  ∀ (x:Lax263307.LinearRelaxation.MomentVector n (Lax263307.AlgorithmParameters.level a K B n D)),
                    (∀ (T:Lax263307.LinearRelaxation.Coordinate n (Lax263307.AlgorithmParameters.level a K B n D)),
                        @LE.le Real Real.instLE
                          (@abs Real Real.lattice Real.instAddGroup
                            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (x T)
                              (@Lax263307.RationalConditioning.realVector n
                                (Lax263307.AlgorithmParameters.level a K B n D) y T)))
                          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                              (@Rat.cast Real Real.instRatCast (Lax263307.AlgorithmParameters.momentFloor a K B n D))
                              (@HPow.hPow Real Nat Real
                                (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                                (@HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                                  (@Nat.cast Real Real.instNatCast D))
                                ((2:Nat))))
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                              (@OfNat.ofNat Real (nat_lit 32)
                                (@instOfNatAtLeastTwo Real (nat_lit 32) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    ((31:Nat))
                                    (@Nat.instNeZeroSucc ((30:Nat))))))
                              (@HPow.hPow Real Nat Real
                                (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                                (@Nat.cast Real Real.instNatCast n)
                                ((2:Nat))))))→
                      @Lax263307.NearOracle.Correct n (Lax263307.AlgorithmParameters.level a K B n D) G k h D
                        (@Rat.cast Real Real.instRatCast (Lax263307.AlgorithmParameters.momentFloor a K B n D)) x
                        (@Lax263307.NearOracle.run n flow a K B D G inst k y child))→
              ∀ (center:Lax263307.MomentLP.Index n (Lax263307.AlgorithmParameters.level a K B n D)→ Rat),
                @Lax263307.ProjectedOracle.Correct n G k h a K B D center
                  (@Lax263307.ProjectedOracle.run n lp flow a K B D G inst k child center):= @Lax263307Proofs.ProjectedOracle.run_correct_native

section

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_mono:Monotone depth:=by
  intro n m hnm
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hn:n≤ 1
    · rw [depth,if_pos hn]
      exact Nat.zero_le _
    · have hm:¬m≤ 1:=by omega
      rw [depth.eq_def n,if_neg hn,depth.eq_def m,if_neg hm]
      exact Nat.add_le_add_left (ih (2 * m / 3) (by omega)
        (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hnm))) 1

theorem balanced_decrease (n m:ℕ) (nontrivial:1 < n) (balanced:3 * m≤ 2 * n):
    depth m + 1≤ depth n:=by
  have hm:m≤ 2 * n / 3:=by omega
  have hdepth:=depth_mono hm
  rw [depth.eq_def n,if_neg (by omega)]
  omega

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

theorem approximation_transfer {n:ℕ} (G:SimpleGraph (Fin n))
    (I:Finset (Fin n)) (u levels:ℕ) (δ ε:ℚ)
    (independent:G.IsIndepSet (I:Set (Fin n)))
    (upper_bound:∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card≤ u)
    (_δ_nonnegative:0≤ δ) (δ_small:δ≤ 1)
    (ε_small:ε≤ 1) (loss:(levels:ℚ) * δ≤ ε)
    (size:(1 - δ) ^ levels * (u:ℚ)≤ I.card):
    IsApproximation G (fun _ => 1) ε I:=by
  refine ⟨independent, ?_⟩
  intro J hJ
  have hbernoulli:1 - (levels:ℚ) * δ≤ (1 - δ) ^ levels:=by
    simpa only [mul_neg,sub_eq_add_neg] using
      one_add_mul_le_pow (show (-2:ℚ)≤ -δ by linarith) levels
  have hfactor:1 - ε≤ (1 - δ) ^ levels:=by linarith
  have hu:(J.card:ℚ)≤ u:=by exact_mod_cast upper_bound J hJ
  have hunonneg:(0:ℚ)≤ u:=by positivity
  simp only [weight,Finset.sum_const,nsmul_eq_mul,mul_one]
  calc
    (1 - ε) * (J.card:ℚ)≤ (1 - ε) * u:=mul_le_mul_of_nonneg_left hu (by linarith)
    _≤ (1 - δ) ^ levels * u:=mul_le_mul_of_nonneg_right hfactor hunonneg
    _≤ I.card:=size

end Lax263307Proofs.RecursionDepth

end

section

namespace Lax263307.IndependentBlowUp

def lift {n:ℕ} (copies:Fin n→ ℕ) (I:Finset (Fin n)):Finset (Vertex copies):=
  I.sigma fun _ => Finset.univ

def IsCardinalityApproximation {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (δ:ℚ) (K:Finset (Vertex copies)):Prop:=
  (graph G copies).IsIndepSet (K:Set (Vertex copies))∧
    ∀ J:Finset (Vertex copies), (graph G copies).IsIndepSet (J:Set (Vertex copies))→
      (1 - δ) * (J.card:ℚ)≤ K.card

end Lax263307.IndependentBlowUp

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

namespace Lax263307.LinearRelaxation

noncomputable def conditioned {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (v:Fin n):ℝ:=
  value y (insert v A) / value y A

end Lax263307.LinearRelaxation

end

section

namespace Lax263307Proofs.RelaxationAlgebra

open Lax263307.LinearRelaxation

theorem value_of_size {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (hA:A.card≤ r + 2):value y A=y ⟨A,hA⟩:=by
  simp [value,hA]

theorem value_combination {n r:ℕ} (y z:MomentVector n r)
    (a b:ℝ) (A:Finset (Fin n)):
    value (a • y + b • z) A=a * value y A + b * value z A:=by
  by_cases hA:A.card≤ r + 2 <;> simp [value,hA]

theorem indicator_value {n r:ℕ} (I A:Finset (Fin n))
    (hA:A.card≤ r + 2):
    value (indicator r I) A=if A ⊆ I then 1 else 0:=by
  simp [value,indicator,hA]

theorem insert_size {n r:ℕ} (A:Finset (Fin n))
    (hA:A.card≤ r + 1) (v:Fin n):(insert v A).card≤ r + 2:=by
  have:=Finset.card_insert_le v A
  omega

theorem indicator_sum {n r:ℕ} (I A C:Finset (Fin n))
    (hA:A.card≤ r + 1):
    (∑ v∈ C,value (indicator r I) (insert v A)) =
      if A ⊆ I then ((C ∩ I).card:ℝ) else 0:=by
  simp_rw [indicator_value I _ (insert_size A hA _),Finset.insert_subset_iff]
  by_cases hAI:A ⊆ I
  · simp [hAI]
  · simp [hAI]

theorem independent_subset {n:ℕ} (G:SimpleGraph (Fin n))
    {I J:Finset (Fin n)} (hI:G.IsIndepSet (I:Set (Fin n))) (hJI:J ⊆ I):
    G.IsIndepSet (J:Set (Fin n)):=
  hI.mono (by simpa using hJI)

end Lax263307Proofs.RelaxationAlgebra

end

section

namespace Lax263307Proofs.BlowUpIndependentSets

open Lax263307.IndependentBlowUp

theorem lift_independent {n:ℕ} (G:SimpleGraph (Fin n)) (copies:Fin n→ ℕ)
    (I:Finset (Fin n)) (independent:G.IsIndepSet (I:Set (Fin n))):
    (graph G copies).IsIndepSet (lift copies I:Set (Vertex copies)):=by
  intro a ha b hb _ hab
  have haI:a.1∈ I:=(Finset.mem_sigma.mp ha).1
  have hbI:b.1∈ I:=(Finset.mem_sigma.mp hb).1
  change G.Adj a.1 b.1 at hab
  exact independent haI hbI hab.ne hab

theorem project_independent {n:ℕ} (G:SimpleGraph (Fin n)) (copies:Fin n→ ℕ)
    (K:Finset (Vertex copies)) (independent:(graph G copies).IsIndepSet (K:Set (Vertex copies))):
    G.IsIndepSet (project K:Set (Fin n)):=by
  intro u hu v hv huv hadj
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hv
  exact independent ha hb (fun h => huv (congrArg Sigma.fst h)) hadj

theorem lift_cardinality {n:ℕ} (copies:Fin n→ ℕ) (I:Finset (Fin n)):
    (lift copies I).card=∑ v∈ I,copies v:=by
  simp [lift]

theorem projection_capacity {n:ℕ} (copies:Fin n→ ℕ) (K:Finset (Vertex copies)):
    K.card≤ ∑ v∈ project K,copies v:=by
  have hsub:K ⊆ lift copies (project K):=by
    intro a ha
    simp only [lift,Finset.mem_sigma,Finset.mem_univ,and_true]
    exact Finset.mem_image_of_mem _ ha
  exact (Finset.card_le_card hsub).trans_eq
    (Lax263307Proofs.BlowUpIndependentSets.lift_cardinality copies (project K))

end Lax263307Proofs.BlowUpIndependentSets

end

section

namespace Lax228581.Treewidth

def HasTreewidthAtMost {V:Type} (G:SimpleGraph V) (w:ℕ):Prop:=
  ∃ D:TreeDecomposition G, ∀ i, (D.bag i).card≤ w + 1

noncomputable def treewidth {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V):ℕ:=
  sInf {w | HasTreewidthAtMost G w}

end Lax228581.Treewidth

end

section

namespace Lax263307Proofs.BlowUpDecompositions

open Lax263307.IndependentBlowUp Lax228581.Treewidth

def liftDecomposition {n:ℕ} {G:SimpleGraph (Fin n)} (copies:Fin n→ ℕ)
    (D:TreeDecomposition G):TreeDecomposition (graph G copies) where
  Node:=D.Node
  nodeFintype:=D.nodeFintype
  tree:=D.tree
  isTree:=D.isTree
  bag i:=lift copies (D.bag i)
  vertex_mem_bag a:=by
    obtain ⟨i,hi⟩:=D.vertex_mem_bag a.1
    exact ⟨i,by simp [lift,hi]⟩
  edge_mem_bag:=by
    intro a b hab
    obtain ⟨i,ha,hb⟩:=D.edge_mem_bag hab
    exact ⟨i,by simp [lift,ha],by simp [lift,hb]⟩
  bag_indices_connected a:=by
    have hset:{i:D.Node | a∈ lift copies (D.bag i)} =
        {i:D.Node | a.1∈ D.bag i}:=by
      ext i
      simp [lift]
    rw [hset]
    exact D.bag_indices_connected a.1

theorem bounded_blowup_decomposition {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (s w:ℕ) (bounded:∀ v,copies v≤ s)
    (width:HasTreewidthAtMost G w):
    ∃ D:TreeDecomposition (graph G copies), ∀ i, (D.bag i).card≤ s * (w + 1):=by
  obtain ⟨D,hD⟩:=width
  refine ⟨liftDecomposition copies D, ?_⟩
  intro i
  change (lift copies (D.bag i)).card≤ s * (w + 1)
  rw [Lax263307Proofs.BlowUpIndependentSets.lift_cardinality]
  calc
    (∑ v∈ D.bag i,copies v)≤ ∑ _v∈ D.bag i,s:=
      Finset.sum_le_sum fun v _ => bounded v
    _=s * (D.bag i).card:=by simp [Nat.mul_comm]
    _≤ s * (w + 1):=Nat.mul_le_mul_left s (hD i)

end Lax263307Proofs.BlowUpDecompositions

end

section

namespace Lax263307.BlowUpDeletion

open scoped Classical

open IndependentBlowUp Lax228581.Treewidth

noncomputable def highDegree {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (s:ℕ):Finset (Vertex copies):=
  Finset.univ.filter fun v => s < (graph G copies).degree v

end Lax263307.BlowUpDeletion

end

section

namespace Lax263307Proofs.TreeExtensions

open Lax228581.Treewidth

def attachLeaves {α β:Type} (T:SimpleGraph α) (root:α):
    SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inl b => T.Adj a b
    | .inl a, .inr _ => a=root
    | .inr _, .inl b => b=root
    | .inr _, .inr _ => False
  symm:= ⟨by intro a b h; cases a <;> cases b <;> simp_all [T.adj_comm]⟩
  loopless:= ⟨by intro a; cases a <;> simp⟩

theorem degree_as_sum {V:Type} [Fintype V] (G:SimpleGraph V)
    [DecidableRel G.Adj] (v:V):
    G.degree v=∑ u,if G.Adj v u then 1 else 0:=by
  classical
  rw [SimpleGraph.degree,G.neighborFinset_eq_filter]
  simp

theorem attachLeaves_tree {α β:Type} [Fintype α] [Fintype β]
    (T:SimpleGraph α) (root:α) (hT:T.IsTree):
    (attachLeaves (β:=β) T root).IsTree:=by
  classical
  let H:=attachLeaves (β:=β) T root
  let inclusion:T→g H:= ⟨Sum.inl,fun h => h⟩
  have hroot:∀ a:α ⊕ β,H.Reachable a (.inl root):=by
    intro a
    cases a with
    | inl a => exact (hT.connected a root).map inclusion
    | inr b => exact SimpleGraph.Adj.reachable (show H.Adj (.inr b) (.inl root) from rfl)
  have:Nonempty (α ⊕ β):= ⟨.inl root⟩
  have hconn:H.Connected:= ⟨fun a b => (hroot a).trans (hroot b).symm⟩
  have hleft (a:α):H.degree (.inl a) =
      T.degree a + if a=root then Fintype.card β else 0:=by
    rw [degree_as_sum,Fintype.sum_sum_type,degree_as_sum]
    simp only [H,attachLeaves]
    split_ifs <;> simp_all
  have hright (b:β):H.degree (.inr b)=1:=by
    rw [degree_as_sum,Fintype.sum_sum_type]
    simp [H,attachLeaves,eq_comm]
  have hsum:(∑ v,H.degree v)=(∑ a,T.degree a) + 2 * Fintype.card β:=by
    rw [Fintype.sum_sum_type]
    simp_rw [hleft,hright]
    simp [Finset.sum_add_distrib]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hcount:=hT.card_edgeFinset
  have hhand:=H.sum_degrees_eq_twice_card_edges
  rw [hsum,T.sum_degrees_eq_twice_card_edges] at hhand
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_sum,
    ← SimpleGraph.edgeFinset_card]
  omega

noncomputable def isolatedBag {V:Type} [DecidableEq V] {G:SimpleGraph V} (S:Set V)
    (D:TreeDecomposition (G.induce S)):D.Node ⊕ ↥(Sᶜ)→ Finset V
  | .inl i => (D.bag i).image Subtype.val
  | .inr v => {v.val}

theorem isolatedBag_connected {V:Type} [DecidableEq V] {G:SimpleGraph V} (S:Set V)
    (D:TreeDecomposition (G.induce S)) (root:D.Node) (v:V):
    ((attachLeaves (β:= ↥(Sᶜ)) D.tree root).induce
      {i | v∈ isolatedBag S D i}).Connected:=by
  classical
  by_cases hv:v∈ S
  · let old:=D.tree.induce {i | (⟨v,hv⟩:S)∈ D.bag i}
    let new:=(attachLeaves (β:= ↥(Sᶜ)) D.tree root).induce
      {i | v∈ isolatedBag S D i}
    let f:old→g new:=
      { toFun:=fun i => ⟨.inl i.val,by
          change v∈ (D.bag i.val).image Subtype.val
          exact Finset.mem_image.mpr ⟨⟨v,hv⟩,i.property,rfl⟩⟩
        map_rel':=fun h => h }
    apply (D.bag_indices_connected ⟨v,hv⟩).map f
    rintro ⟨i,hi⟩
    cases i with
    | inl i =>
      have hi':(⟨v,hv⟩:S)∈ D.bag i:=by
        obtain ⟨u,hu,he⟩:=Finset.mem_image.mp hi
        have:u=⟨v,hv⟩:=Subtype.ext he
        simpa [this] using hu
      exact ⟨⟨i,hi'⟩,rfl⟩
    | inr u =>
      have:v=u.val:=by simpa [isolatedBag] using hi
      exact (u.property (this ▸ hv)).elim
  · let new:=(attachLeaves (β:= ↥(Sᶜ)) D.tree root).induce
      {i | v∈ isolatedBag S D i}
    let newV:= {i:D.Node ⊕ ↥(Sᶜ) // v∈ isolatedBag S D i}
    have hi:∀ i:newV,i.val=.inr ⟨v,hv⟩:=by
      rintro ⟨i,hi⟩
      cases i with
      | inl i =>
        obtain ⟨u,_,he⟩:=Finset.mem_image.mp hi
        exact (hv (he ▸ u.property)).elim
      | inr u =>
        have:v=u.val:=by simpa [isolatedBag] using hi
        exact congrArg Sum.inr (Subtype.ext this.symm)
    have:Subsingleton newV:= ⟨fun a b => Subtype.ext ((hi a).trans (hi b).symm)⟩
    have:Nonempty newV:= ⟨⟨.inr ⟨v,hv⟩,by simp [isolatedBag]⟩⟩
    change new.Connected
    exact
      { preconnected:=fun a b => by
          have he:a=b:= ‹Subsingleton newV›.elim a b
          subst b
          exact SimpleGraph.Reachable.refl _
        nonempty:= ‹Nonempty newV› }

noncomputable def extendIsolated {V:Type} [Fintype V] {G:SimpleGraph V}
    (S:Set V) (isolated:∀ v,v∉ S→ G.IsIsolated v)
    (D:TreeDecomposition (G.induce S)):TreeDecomposition G:=by
  classical
  letI:=D.nodeFintype
  have:Nonempty D.Node:=D.isTree.connected.nonempty
  let root:=Classical.arbitrary D.Node
  exact
    { Node:=D.Node ⊕ ↥(Sᶜ)
      tree:=attachLeaves D.tree root
      isTree:=attachLeaves_tree D.tree root D.isTree
      bag:=isolatedBag S D
      vertex_mem_bag:=by
        intro v
        by_cases hv:v∈ S
        · obtain ⟨i,hi⟩:=D.vertex_mem_bag ⟨v,hv⟩
          exact ⟨.inl i,Finset.mem_image.mpr ⟨⟨v,hv⟩,hi,rfl⟩⟩
        · exact ⟨.inr ⟨v,hv⟩,by simp [isolatedBag]⟩
      edge_mem_bag:=by
        intro u v huv
        have hu:u∈ S:=by
          by_contra hu
          exact isolated u hu v huv
        have hv:v∈ S:=by
          by_contra hv
          exact isolated v hv u huv.symm
        obtain ⟨i,hiu,hiv⟩:=D.edge_mem_bag
          (show (G.induce S).Adj ⟨u,hu⟩ ⟨v,hv⟩ from huv)
        exact ⟨.inl i,Finset.mem_image.mpr ⟨⟨u,hu⟩,hiu,rfl⟩,
          Finset.mem_image.mpr ⟨⟨v,hv⟩,hiv,rfl⟩⟩
      bag_indices_connected:=isolatedBag_connected S D root }

theorem extendIsolated_card {V:Type} [Fintype V] {G:SimpleGraph V}
    (S:Set V) (isolated:∀ v,v∉ S→ G.IsIsolated v)
    (D:TreeDecomposition (G.induce S)) (B:ℕ) (hB:1≤ B)
    (hD:∀ i, (D.bag i).card≤ B):
    ∀ i, ((extendIsolated S isolated D).bag i).card≤ B:=by
  classical
  intro i
  cases i with
  | inl i => exact Finset.card_image_le.trans (hD i)
  | inr v => simpa [extendIsolated,isolatedBag] using hB

noncomputable def pullback {V W:Type} [Fintype V] {G:SimpleGraph V}
    {H:SimpleGraph W} (f:G ↪g H) (D:TreeDecomposition H):
    TreeDecomposition G:=by
  classical
  exact
    { Node:=D.Node
      nodeFintype:=D.nodeFintype
      tree:=D.tree
      isTree:=D.isTree
      bag:=fun i => Finset.univ.filter fun v => f v∈ D.bag i
      vertex_mem_bag:=by
        intro v
        obtain ⟨i,hi⟩:=D.vertex_mem_bag (f v)
        exact ⟨i,by simp [hi]⟩
      edge_mem_bag:=by
        intro u v huv
        obtain ⟨i,hiu,hiv⟩:=D.edge_mem_bag (f.map_adj_iff.mpr huv)
        exact ⟨i,by simp [hiu],by simp [hiv]⟩
      bag_indices_connected:=by
        intro v
        have hset:{i | v∈ Finset.univ.filter fun v => f v∈ D.bag i} =
            {i | f v∈ D.bag i}:=by ext i; simp
        rw [hset]
        exact D.bag_indices_connected (f v) }

theorem pullback_card {V W:Type} [Fintype V] {G:SimpleGraph V}
    {H:SimpleGraph W} (f:G ↪g H) (D:TreeDecomposition H) (i:D.Node):
    ((pullback f D).bag i).card≤ (D.bag i).card:=by
  classical
  let B:=(pullback f D).bag i
  calc
    B.card=(B.image f).card:=(Finset.card_image_of_injective B f.injective).symm
    _≤ (D.bag i).card:=Finset.card_le_card (by
      intro w hw
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2)

noncomputable def restoreDeleted {V:Type} [Fintype V] {G:SimpleGraph V}
    (X:Finset V) (D:TreeDecomposition (G.induce (↑X:Set V)ᶜ)):
    TreeDecomposition G:=by
  classical
  have:Nonempty D.Node:=D.isTree.connected.nonempty
  exact
    { Node:=D.Node
      nodeFintype:=D.nodeFintype
      tree:=D.tree
      isTree:=D.isTree
      bag:=fun i => X ∪ (D.bag i).image Subtype.val
      vertex_mem_bag:=by
        intro v
        by_cases hv:v∈ X
        · exact ⟨Classical.arbitrary D.Node,by simp [hv]⟩
        · obtain ⟨i,hi⟩:=D.vertex_mem_bag ⟨v,hv⟩
          exact ⟨i,Finset.mem_union_right X (Finset.mem_image.mpr ⟨⟨v,hv⟩,hi,rfl⟩)⟩
      edge_mem_bag:=by
        intro u v huv
        by_cases hu:u∈ X <;> by_cases hv:v∈ X
        · exact ⟨Classical.arbitrary D.Node,by simp [hu,hv]⟩
        · obtain ⟨i,hi⟩:=D.vertex_mem_bag ⟨v,hv⟩
          exact ⟨i,by simp [hu],Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v,hv⟩,hi,rfl⟩)⟩
        · obtain ⟨i,hi⟩:=D.vertex_mem_bag ⟨u,hu⟩
          exact ⟨i,Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨u,hu⟩,hi,rfl⟩),by simp [hv]⟩
        · obtain ⟨i,hiu,hiv⟩:=D.edge_mem_bag
            (show (G.induce (↑X:Set V)ᶜ).Adj ⟨u,hu⟩ ⟨v,hv⟩ from huv)
          exact ⟨i,Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨u,hu⟩,hiu,rfl⟩),Finset.mem_union_right X
            (Finset.mem_image.mpr ⟨⟨v,hv⟩,hiv,rfl⟩)⟩
      bag_indices_connected:=by
        intro v
        by_cases hv:v∈ X
        · have hset:{i | v∈ X ∪ (D.bag i).image Subtype.val}=Set.univ:=by
            ext i; simp [hv]
          rw [hset]
          exact (SimpleGraph.induceUnivIso D.tree).connected_iff.mpr D.isTree.connected
        · have hset:{i | v∈ X ∪ (D.bag i).image Subtype.val} =
              {i | (⟨v,hv⟩:↥((↑X:Set V)ᶜ))∈ D.bag i}:=by
            ext i
            simp only [Finset.mem_union,hv,false_or,Finset.mem_image]
            constructor
            · rintro ⟨u,hu,he⟩
              have:u=⟨v,hv⟩:=Subtype.ext he
              simpa [this] using hu
            · intro hi
              exact ⟨⟨v,hv⟩,hi,rfl⟩
          rw [hset]
          exact D.bag_indices_connected ⟨v,hv⟩ }

theorem restoreDeleted_card {V:Type} [Fintype V] {G:SimpleGraph V}
    (X:Finset V) (D:TreeDecomposition (G.induce (↑X:Set V)ᶜ)) (B:ℕ)
    (hD:∀ i, (D.bag i).card≤ B):
    ∀ i, ((restoreDeleted X D).bag i).card≤ X.card + B:=by
  classical
  intro i
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_image_le.trans (hD i)) X.card)

end Lax263307Proofs.TreeExtensions

end

section

namespace Lax263307Proofs.BlowUpDeletion

open Lax263307.IndependentBlowUp Lax263307.BlowUpDeletion Lax228581.Treewidth
open TreeExtensions

theorem high_degree_card {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (s:ℕ):
    s * (highDegree G copies s).card≤ 2 * (graph G copies).edgeSet.ncard:=by
  classical
  let H:=graph G copies
  calc
    s * (highDegree G copies s).card=∑ _v∈ highDegree G copies s,s:=by
      simp [Nat.mul_comm]
    _≤ ∑ v∈ highDegree G copies s,H.degree v:=by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.le_of_lt (Finset.mem_filter.mp hv).2
    _≤ ∑ v,H.degree v:=Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _=2 * H.edgeFinset.card:=H.sum_degrees_eq_twice_card_edges
    _=2 * H.edgeSet.ncard:=by
      rw [SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard]

theorem fibre_le_neighbor_degree {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (v:Fin n) (b:Vertex copies) (adj:G.Adj b.1 v):
    copies v≤ (by classical exact (graph G copies).degree b):=by
  classical
  let H:=graph G copies
  calc
    copies v=(lift copies {v}).card:=by
      rw [Lax263307Proofs.BlowUpIndependentSets.lift_cardinality]
      simp
    _≤ (H.neighborFinset b).card:=Finset.card_le_card (by
      intro a ha
      have:a.1=v:=by simpa [lift] using ha
      have hadj:H.Adj b a:=by change G.Adj b.1 a.1; simpa [this] using adj
      simpa using hadj)
    _=H.degree b:=SimpleGraph.card_neighborFinset_eq_degree _ _

theorem active_fibre_bound {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (s:ℕ)
    (a:↥((↑(highDegree G copies s):Set (Vertex copies))ᶜ))
    (active:¬((graph G copies).induce
      (↑(highDegree G copies s):Set (Vertex copies))ᶜ).IsIsolated a):
    copies a.val.1≤ s:=by
  classical
  obtain ⟨b,hab⟩:∃ b, ((graph G copies).induce
      (↑(highDegree G copies s):Set (Vertex copies))ᶜ).Adj a b:=by
    simpa [SimpleGraph.IsIsolated] using active
  have hb:(graph G copies).degree b.val≤ s:=by
    have:=b.property
    simpa [highDegree] using this
  exact (fibre_le_neighbor_degree G copies a.val.1 b.val hab.symm).trans hb

theorem deletion_decomposition {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (s w:ℕ) (width:HasTreewidthAtMost G w):
    ∃ D:TreeDecomposition (graph G copies),
      ∀ i, (D.bag i).card≤ (highDegree G copies s).card + max 1 (s * (w + 1)):=by
  classical
  let X:=highDegree G copies s
  let H:=(graph G copies).induce (↑X:Set (Vertex copies))ᶜ
  let S:Set ↥((↑X:Set (Vertex copies))ᶜ):= {a | ¬H.IsIsolated a}
  let f:H.induce S ↪g graph G (fun _ => s):=
    { toFun:=fun a => ⟨a.val.val.1, ⟨a.val.val.2.val,
          a.val.val.2.isLt.trans_le (active_fibre_bound G copies s a.val a.property)⟩⟩
      inj':=by
        intro a b he
        have hfirst:=congrArg Sigma.fst he
        cases a with
        | mk a ha =>
          cases b with
          | mk b hb =>
            cases a with
            | mk a ha' =>
              cases b with
              | mk b hb' =>
                cases a with
                | mk av ai =>
                  cases b with
                  | mk bv bi =>
                    dsimp at hfirst
                    subst bv
                    have hidx:ai=bi:=Fin.ext (congrArg (fun a => a.2.val) he)
                    subst bi
                    rfl
      map_rel_iff':=by intro a b; rfl }
  obtain ⟨D,hD⟩:=Lax263307Proofs.BlowUpDecompositions.bounded_blowup_decomposition
    G (fun _ => s) s w (fun _ => le_rfl) width
  let D₀:=pullback f D
  have hD₀:∀ i, (D₀.bag i).card≤ max 1 (s * (w + 1)):=
    fun i => (pullback_card f D i).trans ((hD i).trans (le_max_right _ _))
  have hisolated:∀ a,a∉ S→ H.IsIsolated a:=by
    intro a ha
    exact Classical.not_not.mp ha
  let D₁:=extendIsolated S hisolated D₀
  have hD₁:∀ i, (D₁.bag i).card≤ max 1 (s * (w + 1)):=
    extendIsolated_card S hisolated D₀ _ (le_max_left _ _) hD₀
  exact ⟨restoreDeleted X D₁,restoreDeleted_card X D₁ _ hD₁⟩

theorem power_bound {n:ℕ} (G:SimpleGraph (Fin n))
    (copies:Fin n→ ℕ) (w:ℕ) (b c:ℝ) (hb:0≤ b) (hb₁:b < 1)
    (_hc:0 < c) (width:HasTreewidthAtMost G w)
    (width_bound:(w + 1:ℕ)≤
      c * Real.rpow ((graph G copies).edgeSet.ncard + 1) b):
    ∃ D:TreeDecomposition (graph G copies), ∀ i,
      ((D.bag i).card:ℝ)≤ (3 + 2 * c) *
        Real.rpow ((graph G copies).edgeSet.ncard + 1) ((1 + b) / 2):=by
  classical
  let m:=(graph G copies).edgeSet.ncard
  let M:ℝ:=(m:ℝ) + 1
  let α:=(1 - b) / 2
  let β:=(1 + b) / 2
  let q:=Real.rpow M α
  let t:=Real.rpow M β
  let s:=Nat.ceil q
  have hM:1≤ M:=by dsimp [M]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hMpos:0 < M:=lt_of_lt_of_le zero_lt_one hM
  have hα:0≤ α:=by dsimp [α]; linarith
  have hβ:0≤ β:=by dsimp [β]; linarith
  have hq:1≤ q:=Real.one_le_rpow hM hα
  have ht:1≤ t:=Real.one_le_rpow hM hβ
  have hqs:q≤ (s:ℝ):=Nat.le_ceil q
  have hs:(s:ℝ)≤ 2 * q:=by
    have hceil:=Nat.ceil_le_floor_add_one q
    have hfloor:=Nat.floor_le (show 0≤ q by linarith)
    have hcast:(s:ℝ)≤ (Nat.floor q:ℝ) + 1:=by exact_mod_cast hceil
    linarith
  have hqt:q * t=M:=by
    dsimp [q,t]
    rw [← Real.rpow_add hMpos]
    have:α + β=1:=by dsimp [α,β]; ring
    rw [this,Real.rpow_one]
  have hqb:q * Real.rpow M b=t:=by
    dsimp [q,t]
    rw [← Real.rpow_add hMpos]
    have:α + b=β:=by dsimp [α,β]; ring
    rw [this]
  have hhigh:((highDegree G copies s).card:ℝ)≤ 2 * t:=by
    have hdegree:(s:ℝ) * (highDegree G copies s).card≤ 2 * (m:ℝ):=by
      exact_mod_cast Lax263307Proofs.BlowUpDeletion.high_degree_card G copies s
    have hX:0≤ ((highDegree G copies s).card:ℝ):=by positivity
    have hqX:q * (highDegree G copies s).card≤ (s:ℝ) * (highDegree G copies s).card:=
      mul_le_mul_of_nonneg_right hqs hX
    have hmul:q * (highDegree G copies s).card≤ q * (2 * t):=by
      calc
        q * (highDegree G copies s).card≤ 2 * (m:ℝ):=hqX.trans hdegree
        _≤ 2 * M:=by dsimp [M]; linarith
        _=q * (2 * t):=by rw [mul_left_comm,hqt]
    exact (mul_le_mul_iff_right₀ (show 0 < q by linarith)).mp hmul
  have hlift:(s:ℝ) * (w + 1:ℕ)≤ 2 * c * t:=by
    calc
      (s:ℝ) * (w + 1:ℕ)≤ (2 * q) * (c * Real.rpow M b):=
        mul_le_mul hs width_bound (by positivity) (by positivity)
      _=2 * c * t:=by rw [← hqb]; ring
  obtain ⟨D,hD⟩:=Lax263307Proofs.BlowUpDeletion.deletion_decomposition G copies s w width
  refine ⟨D, ?_⟩
  intro i
  have hbag:((D.bag i).card:ℝ)≤ (highDegree G copies s).card +
      max 1 ((s:ℝ) * (w + 1:ℕ)):=by exact_mod_cast hD i
  have hmax:max 1 ((s:ℝ) * (w + 1:ℕ))≤ 1 + (s:ℝ) * (w + 1:ℕ):=
    max_le (le_add_of_nonneg_right (by positivity)) (by linarith)
  change ((D.bag i).card:ℝ)≤ (3 + 2 * c) * t
  nlinarith

end Lax263307Proofs.BlowUpDeletion

end

section

namespace Lax263307Proofs.SeparatorComponents

open Lax263307.SeparatorComponents

noncomputable def components {n:ℕ} (G:SimpleGraph (Fin n))
    (S:Finset (Fin n)):
    Partition G S (G.induce (↑S:Set (Fin n))ᶜ).ConnectedComponent:=by
  classical
  let H:=G.induce (↑S:Set (Fin n))ᶜ
  let vertices (c:H.ConnectedComponent):=(Subtype.val '' c.supp).toFinset
  exact
    { vertices:=vertices
      outside:=by
        intro c v hv
        obtain ⟨u,_,rfl⟩:=Set.mem_toFinset.mp hv
        exact u.property
      unique:=by
        intro v hv
        let u:↥((↑S:Set (Fin n))ᶜ):= ⟨v,hv⟩
        refine ⟨H.connectedComponentMk u, ?_, ?_⟩
        · exact Set.mem_toFinset.mpr ⟨u,rfl,rfl⟩
        · intro c hc
          obtain ⟨w,hw,he⟩:=Set.mem_toFinset.mp hc
          have hwu:w=u:=Subtype.ext he
          change H.connectedComponentMk w=c at hw
          rw [hwu] at hw
          exact hw.symm
      closed:=by
        intro c u v hu hv huv
        obtain ⟨u',hu',rfl⟩:=Set.mem_toFinset.mp hu
        let v':↥((↑S:Set (Fin n))ᶜ):= ⟨v,hv⟩
        exact Set.mem_toFinset.mpr ⟨v',
          (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c
            (show H.Adj u' v' from huv)).mp hu',rfl⟩ }

end Lax263307Proofs.SeparatorComponents

end

section

namespace Lax263307Proofs.SeparatorDecompositions

variable {ι:Type} {V:ι→ Type}

def join (T:∀ i,SimpleGraph (V i)) (root:∀ i,V i):SimpleGraph (Unit ⊕ Sigma V) where
  Adj
    | .inl _, .inl _ => False
    | .inl _, .inr ⟨i,v⟩ => v=root i
    | .inr ⟨i,v⟩, .inl _ => v=root i
    | .inr ⟨i,u⟩, .inr ⟨j,v⟩ => ∃ h:i=j, (T i).Adj u (h.symm ▸ v)
  symm:= ⟨by
    intro a b hab
    cases a with
    | inl a => cases b <;> exact hab
    | inr a =>
      cases b with
      | inl b => exact hab
      | inr b =>
        rcases a with ⟨i,u⟩
        rcases b with ⟨j,v⟩
        obtain ⟨h,hadj⟩:=hab
        subst j
        exact ⟨rfl,hadj.symm⟩⟩
  loopless:= ⟨by
    intro a
    cases a with
    | inl a => exact id
    | inr a =>
      rcases a with ⟨i,v⟩
      rintro ⟨h,hadj⟩
      exact (T i).ne_of_adj hadj rfl⟩

noncomputable instance (T:∀ i,SimpleGraph (V i)) (root:∀ i,V i):DecidableRel (join T root).Adj:=
  fun _ _ => Classical.propDecidable _

variable [Fintype ι] [∀ i,Fintype (V i)]

theorem join_tree (T:∀ i,SimpleGraph (V i)) (root:∀ i,V i) (trees:∀ i, (T i).IsTree):
    (join T root).IsTree:=by
  classical
  let H:=join T root
  have hreach:∀ a:Unit ⊕ Sigma V,H.Reachable a (.inl ()):=by
    intro a
    cases a with
    | inl a => cases a; exact SimpleGraph.Reachable.refl _
    | inr a =>
      rcases a with ⟨i,u⟩
      let inclusion:T i→g H:= {
        toFun:=fun v => .inr ⟨i,v⟩
        map_rel':=fun h => ⟨rfl,h⟩ }
      exact ((trees i).connected u (root i)).map inclusion |>.trans
        (SimpleGraph.Adj.reachable (show H.Adj (.inr ⟨i,root i⟩) (.inl ()) from rfl))
  have hconnected:H.Connected:= {
    preconnected:=fun a b => (hreach a).trans (hreach b).symm
    nonempty:= ⟨.inl ()⟩ }
  have hrootdegree:H.degree (.inl ())=Fintype.card ι:=by
    rw [Lax263307Proofs.TreeExtensions.degree_as_sum,Fintype.sum_sum_type,Fintype.sum_sigma]
    simp [H,join]
  have hchilddegree (i:ι) (u:V i):
      H.degree (.inr ⟨i,u⟩)=(T i).degree u + (if u=root i then 1 else 0):=by
    rw [Lax263307Proofs.TreeExtensions.degree_as_sum,Fintype.sum_sum_type,Fintype.sum_sigma]
    have hinner (j:ι):(∑ v:V j,if H.Adj (.inr ⟨i,u⟩) (.inr ⟨j,v⟩) then 1 else 0) =
        if j=i then (T i).degree u else 0:=by
      by_cases h:j=i
      · subst j
        simpa [H,join] using (Lax263307Proofs.TreeExtensions.degree_as_sum (T i) u).symm
      · have hne:i ≠ j:=Ne.symm h
        simp [H,join,h,hne]
    simp_rw [hinner]
    simp [H,join,add_comm]
  have heach (i:ι):(∑ v:V i, (T i).degree v) + 2=2 * Fintype.card (V i):=by
    have htree:=(trees i).card_edgeFinset
    have hhand:=(T i).sum_degrees_eq_twice_card_edges
    omega
  have hsums:(∑ i, ∑ v:V i, (T i).degree v) + 2 * Fintype.card ι =
      2 * ∑ i,Fintype.card (V i):=by
    have h:=Finset.sum_congr rfl (fun i (_:i∈ (Finset.univ:Finset ι)) => heach i)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
      Finset.mul_sum,Nat.mul_comm] using h
  have hsum:(∑ v,H.degree v)=2 * ∑ i,Fintype.card (V i):=by
    rw [Fintype.sum_sum_type,Fintype.sum_sigma]
    simp_rw [hchilddegree,Finset.sum_add_distrib]
    simp [hrootdegree]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconnected, ?_⟩
  have hhand:=H.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_sigma,
    ← SimpleGraph.edgeFinset_card]
  simp only [Fintype.card_unit]
  omega

open Lax228581.Treewidth Lax263307.SeparatorComponents
open Lax263307Proofs.SeparatorComponents (components)
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators

variable {n:ℕ} {G:SimpleGraph (Fin n)} {S:Finset (Fin n)}

noncomputable def bag (P:Partition G S ι)
    (D:∀ i,TreeDecomposition (G.induce (↑(P.vertices i):Set (Fin n)))):
    Unit ⊕ (Σ i, (D i).Node)→ Finset (Fin n)
  | .inl _ => S
  | .inr ⟨i,j⟩ => S ∪ ((D i).bag j).image Subtype.val

theorem bag_connected (P:Partition G S ι)
    (D:∀ i,TreeDecomposition (G.induce (↑(P.vertices i):Set (Fin n))))
    (root:∀ i, (D i).Node) (v:Fin n):
    ((join (fun i => (D i).tree) root).induce {j | v∈ bag P D j}).Connected:=by
  classical
  let T:=join (fun i => (D i).tree) root
  let H:=T.induce {j | v∈ bag P D j}
  by_cases hv:v∈ S
  · have hall (j:Unit ⊕ (Σ i, (D i).Node)):v∈ bag P D j:=by
      cases j <;> simp [bag,hv]
    let:∀ i,Fintype (D i).Node:=fun i => (D i).nodeFintype
    let f:T→g H:= { toFun:=fun j => ⟨j,hall j⟩,map_rel':=fun h => h }
    exact (join_tree (fun i => (D i).tree) root (fun i => (D i).isTree)).connected.map f
      (fun ⟨j,_⟩ => ⟨j,rfl⟩)
  · obtain ⟨i,hi,hunique⟩:=P.unique v hv
    let u:↥(↑(P.vertices i):Set (Fin n)):= ⟨v,hi⟩
    let K:=(D i).tree.induce {j | u∈ (D i).bag j}
    let f:K→g H:= {
      toFun:=fun j => ⟨.inr ⟨i,j.val⟩,Finset.mem_union_right S
        (Finset.mem_image.mpr ⟨u,j.property,rfl⟩)⟩
      map_rel':=fun h => ⟨rfl,h⟩ }
    apply ((D i).bag_indices_connected u).map f
    rintro ⟨j,hj⟩
    cases j with
    | inl j => exact (hv hj).elim
    | inr j =>
      rcases j with ⟨k,j⟩
      obtain ⟨w,hw,he⟩:=Finset.mem_image.mp ((Finset.mem_union.mp hj).resolve_left hv)
      have hk:k=i:=hunique k (he ▸ w.property)
      subst k
      have hwu:w=u:=Subtype.ext he
      exact ⟨⟨j,by simpa [hwu] using hw⟩,rfl⟩

noncomputable def glue (P:Partition G S ι)
    (D:∀ i,TreeDecomposition (G.induce (↑(P.vertices i):Set (Fin n)))):
    TreeDecomposition G:=by
  classical
  let:∀ i,Fintype (D i).Node:=fun i => (D i).nodeFintype
  let root (i:ι):(D i).Node:=Classical.choice (D i).isTree.connected.nonempty
  exact {
    Node:=Unit ⊕ (Σ i, (D i).Node)
    tree:=join (fun i => (D i).tree) root
    isTree:=join_tree (fun i => (D i).tree) root (fun i => (D i).isTree)
    bag:=bag P D
    vertex_mem_bag:=by
      intro v
      by_cases hv:v∈ S
      · exact ⟨.inl (),hv⟩
      · obtain ⟨i,hi,_⟩:=P.unique v hv
        obtain ⟨j,hj⟩:=(D i).vertex_mem_bag ⟨v,hi⟩
        exact ⟨.inr ⟨i,j⟩,Finset.mem_union_right S
          (Finset.mem_image.mpr ⟨⟨v,hi⟩,hj,rfl⟩)⟩
    edge_mem_bag:=by
      intro u v huv
      by_cases hu:u∈ S
      · by_cases hv:v∈ S
        · exact ⟨.inl (),hu,hv⟩
        · obtain ⟨i,hi,_⟩:=P.unique v hv
          obtain ⟨j,hj⟩:=(D i).vertex_mem_bag ⟨v,hi⟩
          exact ⟨.inr ⟨i,j⟩,Finset.mem_union_left _ hu,
            Finset.mem_union_right S (Finset.mem_image.mpr ⟨⟨v,hi⟩,hj,rfl⟩)⟩
      · obtain ⟨i,hi,_⟩:=P.unique u hu
        by_cases hv:v∈ S
        · obtain ⟨j,hj⟩:=(D i).vertex_mem_bag ⟨u,hi⟩
          exact ⟨.inr ⟨i,j⟩,Finset.mem_union_right S
            (Finset.mem_image.mpr ⟨⟨u,hi⟩,hj,rfl⟩),Finset.mem_union_left _ hv⟩
        · have hvpart:=P.closed i u v hi hv huv
          obtain ⟨j,hju,hjv⟩:=(D i).edge_mem_bag
            (show (G.induce (↑(P.vertices i):Set (Fin n))).Adj ⟨u,hi⟩ ⟨v,hvpart⟩ from huv)
          exact ⟨.inr ⟨i,j⟩,
            Finset.mem_union_right S (Finset.mem_image.mpr ⟨⟨u,hi⟩,hju,rfl⟩),
            Finset.mem_union_right S (Finset.mem_image.mpr ⟨⟨v,hvpart⟩,hjv,rfl⟩)⟩
    bag_indices_connected:=bag_connected P D root }

theorem glue_card (P:Partition G S ι)
    (D:∀ i,TreeDecomposition (G.induce (↑(P.vertices i):Set (Fin n))))
    (B:ℕ) (bound:∀ i j, ((D i).bag j).card≤ B):
    ∀ j, ((glue P D).bag j).card≤ S.card + B:=by
  classical
  intro j
  cases j with
  | inl j => change S.card≤ S.card + B; omega
  | inr j =>
    rcases j with ⟨i,j⟩
    exact (Finset.card_union_le S (((D i).bag j).image Subtype.val)).trans (Nat.add_le_add_left
      (Finset.card_image_le.trans (bound i j)) S.card)

theorem glue_bound {n:ℕ} (G:SimpleGraph (Fin n)) (S:Finset (Fin n))
    {ι:Type} [Fintype ι] (P:Partition G S ι)
    (D:∀ i,TreeDecomposition (G.induce (↑(P.vertices i):Set (Fin n))))
    (B:ℕ) (bound:∀ i j, ((D i).bag j).card≤ B):
    ∃ E:TreeDecomposition G, ∀ j, (E.bag j).card≤ S.card + B:=
  ⟨glue P D,glue_card P D B bound⟩

noncomputable def oneBag {V:Type} [Fintype V] (G:SimpleGraph V):TreeDecomposition G:=by
  classical
  exact {
    Node:=Unit
    tree:= ⊥
    isTree:=SimpleGraph.IsTree.of_subsingleton
    bag:=fun _ => Finset.univ
    vertex_mem_bag:=fun v => ⟨(),Finset.mem_univ v⟩
    edge_mem_bag:=fun {_ _} _ => ⟨(),Finset.mem_univ _,Finset.mem_univ _⟩
    bag_indices_connected:=fun v => by
      have:Nonempty {i:Unit // v∈ (Finset.univ:Finset V)}:= ⟨⟨(),Finset.mem_univ v⟩⟩
      exact { preconnected:=SimpleGraph.Preconnected.of_subsingleton,nonempty:=this } }

theorem embedding_edge_bound {V W:Type} [Fintype V] [Fintype W]
    {H:SimpleGraph V} {G:SimpleGraph W} (f:H ↪g G):H.edgeSet.ncard≤ G.edgeSet.ncard:=by
  classical
  have h:=Fintype.card_le_of_injective f.mapEdgeSet f.mapEdgeSet.injective
  simpa only [Set.fintypeCard_eq_ncard] using h

theorem components_balanced {n:ℕ} (G:SimpleGraph (Fin n)) (S:Finset (Fin n))
    (balanced:IsBalancedSeparator G S):
    ∀ i,3 * ((components G S).vertices i).card≤ 2 * n:=by
  classical
  intro i
  have hcard:((components G S).vertices i).card=i.supp.ncard:=by
    change (Subtype.val '' i.supp).toFinset.card=_
    rw [Set.toFinset_card,Set.fintypeCard_eq_ncard,Set.ncard_image_of_injective i.supp Subtype.val_injective]
  rw [hcard]
  exact balanced i

theorem recursive_bag_bound (C:GraphClass) (hereditary:IsHereditary C)
    (B:ℕ→ ℕ) (monotone:Monotone B) (positive:∀ m,1≤ B m)
    (separators:∀ n (G:SimpleGraph (Fin n)),G∈ C n→
      ∃ S:Finset (Fin n),IsBalancedSeparator G S∧ S.card≤ B G.edgeSet.ncard)
    {n:ℕ} (G:SimpleGraph (Fin n)) (member:G∈ C n):
    ∃ D:TreeDecomposition G, ∀ j,
      (D.bag j).card≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth n + 1):=by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn:n≤ 1
    · refine ⟨oneBag G, ?_⟩
      intro j
      change (Finset.univ:Finset (Fin n)).card≤ _
      simp only [Finset.card_univ,Fintype.card_fin]
      rw [Lax263307.RecursionDepth.depth,if_pos hn]
      simpa using hn.trans (positive G.edgeSet.ncard)
    · obtain ⟨S,hbalanced,hS⟩:=separators n G member
      let P:=components G S
      let I:=(G.induce (↑S:Set (Fin n))ᶜ).ConnectedComponent
      let:Fintype I:=Fintype.ofFinite I
      have hpart:=components_balanced G S hbalanced
      have child (i:I):∃ D:TreeDecomposition (G.induce (↑(P.vertices i):Set (Fin n))),
          ∀ j, (D.bag j).card≤ B G.edgeSet.ncard * Lax263307.RecursionDepth.depth n:=by
        let U:= ↥(↑(P.vertices i):Set (Fin n))
        let r:=Fintype.card U
        let e:U ≃ Fin r:=Fintype.equivFin U
        let H:=(G.induce (↑(P.vertices i):Set (Fin n))).comap e.symm
        let f:H ↪g G:= {
          toFun:=fun v => (e.symm v).val
          inj':=fun a b h => e.symm.injective (Subtype.ext h)
          map_rel_iff':=Iff.rfl }
        have hr:r=(P.vertices i).card:=Fintype.card_coe _
        have hrbal:3 * r≤ 2 * n:=by rw [hr]; exact hpart i
        have hH:=hereditary r n H G member ⟨f⟩
        obtain ⟨D,hD⟩:=ih r (by omega) H hH
        let g:(G.induce (↑(P.vertices i):Set (Fin n))) ↪g H:= {
          toFun:=e
          inj':=e.injective
          map_rel_iff':=by intro a b; simp [H] }
        let E:=Lax263307Proofs.TreeExtensions.pullback g D
        refine ⟨E,fun j => ?_⟩
        have hm:=monotone (embedding_edge_bound f)
        have hd:=Lax263307Proofs.RecursionDepth.balanced_decrease n r (by omega) hrbal
        exact (Lax263307Proofs.TreeExtensions.pullback_card g D j).trans
          ((hD j).trans (Nat.mul_le_mul hm hd))
      choose D hD using child
      obtain ⟨E,hE⟩:=Lax263307Proofs.SeparatorDecompositions.glue_bound G S P D
        (B G.edgeSet.ncard * Lax263307.RecursionDepth.depth n) hD
      refine ⟨E,fun j => (hE j).trans ?_⟩
      nlinarith

end Lax263307Proofs.SeparatorDecompositions

end

section

namespace Lax263307.ConnectedBags

open Lax228581.Treewidth

def meetingNodes {n:ℕ} {G:SimpleGraph (Fin n)}
    (D:TreeDecomposition G) (U:Finset (Fin n)):Set D.Node:=
  {i | ∃ v∈ U,v∈ D.bag i}

end Lax263307.ConnectedBags

end

section

namespace Lax263307.ConnectedRepresentations

open Lax228581.Treewidth

structure Representation {t n:ℕ} (H:SimpleGraph (Fin t))
    (G:SimpleGraph (Fin n)) where

  carrier:Fin t→ Finset (Fin n)

  connected:∀ v, (G.induce (↑(carrier v):Set (Fin n))).Connected

  touching:∀ u v,H.Adj u v→ ∃ a,a∈ carrier u∧ a∈ carrier v

def users {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (R:Representation H G) (a:Fin n):Finset (Fin t):=
  Finset.univ.filter fun v => a∈ R.carrier v

end Lax263307.ConnectedRepresentations

end

section

namespace Lax263307.AlmostEmbeddings

open scoped Classical

open Lax228581.Treewidth

structure AlmostEmbedding {t n:ℕ} (H:SimpleGraph (Fin t))
    (G:SimpleGraph (Fin n)) where

  vertexMap:Fin t→ Fin n

  route:H.edgeSet→ Finset (Fin n)

  connected:∀ e, (G.induce (↑(route e):Set (Fin n))).Connected

  endpoints:∀ e v,v∈ e.val→ vertexMap v∈ route e

  disjoint:∀ e f,Disjoint e.val.toFinset f.val.toFinset→ Disjoint (route e) (route f)

def IsInduced {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (E:AlmostEmbedding H G):Prop:=
  ∀ e f,Disjoint e.val.toFinset f.val.toFinset→
    ∀ a∈ E.route e, ∀ b∈ E.route f, ¬G.Adj a b

noncomputable def vertexCarrier {t n:ℕ} {H:SimpleGraph (Fin t)}
    {G:SimpleGraph (Fin n)} (E:AlmostEmbedding H G) (v:Fin t):Finset (Fin n):=
  Finset.univ.biUnion fun e:H.edgeSet => if v∈ e.val then E.route e else ∅

end Lax263307.AlmostEmbeddings

end

section

namespace Lax263307.InducedRouteEdges

open scoped Classical

open AlmostEmbeddings

noncomputable def routeUnion {t n:ℕ} {H:SimpleGraph (Fin t)}
    [DecidableRel H.Adj] {G:SimpleGraph (Fin n)} (E:AlmostEmbedding H G):Finset (Fin n):=
  Finset.univ.biUnion E.route

end Lax263307.InducedRouteEdges

end

section

namespace Lax263307.RoutePruning

open scoped Classical

open AlmostEmbeddings

noncomputable def longEdges {t n:ℕ} {H:SimpleGraph (Fin t)} [DecidableRel H.Adj]
    {G:SimpleGraph (Fin n)} (E:AlmostEmbedding H G) (L:ℕ):Finset (Sym2 (Fin t)):=
  (Finset.univ.filter fun e:H.edgeSet => L < (E.route e).card).image Subtype.val

end Lax263307.RoutePruning

end

section

namespace Lax263307.Entropy

def IsProbability {n:ℕ} (π:Fin n→ ℝ):Prop:=
  (∀ v,0≤ π v)∧ (∑ v,π v)=1

noncomputable def naturalEntropy {n:ℕ} (π:Fin n→ ℝ):ℝ:=
  ∑ v,Real.negMulLog (π v)

noncomputable def entropy {n:ℕ} (π:Fin n→ ℝ):ℝ:=
  naturalEntropy π / Real.log 2

end Lax263307.Entropy

end

section

namespace Lax263307.PathSampling

open Entropy (adjacencyMass edgeCost)

structure Distribution (n q:ℕ) where

  probability:Fin q→ ℝ

  nonnegative:∀ i,0≤ probability i

  normalized:(∑ i,probability i)=1

  vertices:Fin q→ Finset (Fin n)

noncomputable def load {n q:ℕ} (P:Distribution n q) (v:Fin n):ℝ:=
  ∑ i,if v∈ P.vertices i then P.probability i else 0

noncomputable def expectedSize {n q:ℕ} (P:Distribution n q):ℝ:=
  ∑ i,P.probability i * ((P.vertices i).card:ℝ)

noncomputable def collisionProbability {n q:ℕ} (P:Distribution n q):ℝ:=
  ∑ i, ∑ j,if ¬Disjoint (P.vertices i) (P.vertices j) then
    P.probability i * P.probability j else 0

noncomputable def adjacencyProbability {n q:ℕ} (G:SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P:Distribution n q):ℝ:=
  ∑ i, ∑ j,if ∃ u∈ P.vertices i, ∃ v∈ P.vertices j,G.Adj u v then
    P.probability i * P.probability j else 0

end Lax263307.PathSampling

end

section

namespace Lax263307.RoutingNormalization

open scoped Classical

def IsUniquePair {n q:ℕ} (E:Fin n→ Fin n→ Fin q→ Prop):Prop:=
  ∀ i u v u' v',E u v i→ E u' v' i→ u=u'∧ v=v'

noncomputable def routed {n q:ℕ} (w:Fin q→ ℝ)
    (E:Fin n→ Fin n→ Fin q→ Prop) (u v:Fin n):ℝ:=
  ∑ i,if E u v i then w i else 0

noncomputable def probability {n q:ℕ} (w:Fin q→ ℝ)
    (E:Fin n→ Fin n→ Fin q→ Prop) (u v:Fin n) (i:Fin q):ℝ:=
  if E u v i then w i / (routed w E u v * (n:ℝ) ^ 2) else 0

end Lax263307.RoutingNormalization

end

section

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

def uniformWeight (n:ℕ):VertexWeight n:=fun _ => 1

end Lax455465.ProductNetwork

end

section

open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork

abbrev PathFlow (n:ℕ):=List (Fin n)→₀ ℝ≥0

def IsPathFlow {n:ℕ} (F:PathFlow n):Prop:=
  ∀ P∈ F.support,2≤ P.length∧ P.Nodup

noncomputable def arcLoad {n:ℕ} (F:PathFlow n) (u v:Fin n):ℝ≥0:=
  ∑ P∈ F.support,F P * ((P.zip P.tail).count (u,v):ℝ≥0)

noncomputable def edgeLoad {n:ℕ} (kind:EdgeKind) (F:PathFlow n)
    (u v:Fin n):ℝ≥0:=
  match kind with
  | .undirected => arcLoad F u v + arcLoad F v u
  | .directed => arcLoad F u v

noncomputable def routed {n:ℕ} (F:PathFlow n) (s t:Fin n):ℝ≥0:=
  ∑ P∈ F.support,
    if P.head?=some s∧ P.getLast?=some t then F P else 0

def IsConcurrentFlow {n:ℕ} (kind:EdgeKind) (N:Network n)
    (π:VertexWeight n) (f:ℝ≥0) (F:PathFlow n):Prop:=
  IsPathFlow F∧
    (∀ u v,edgeLoad kind F u v≤ N.capacity u v)∧
      ∀ s t,s ≠ t→ f * pairDemand kind π s t≤ routed F s t

end Lax455465.ConcurrentFlow

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

noncomputable def FlowCertificate.flow {n:ℕ} (certificate:FlowCertificate n):
    PathFlow n:=
  certificate.paths.foldl
    (fun F record => F + Finsupp.single record.1 (record.2:ℝ≥0)) 0

end Lax455465.RationalEncoding

end

section

namespace Lax263307.SplitPathProjection

open scoped NNReal NNRat
open VertexSplitting Lax455465.ProductNetwork Lax455465.ConcurrentFlow

def expandRoute {n:ℕ} (Q:List (Fin n)):List (Fin (2 * n)):=
  Q.flatMap fun v => [minus v,plus v]

end Lax263307.SplitPathProjection

end

section

namespace Lax263307.RouteDistributions

open PathSampling (load)
open scoped NNReal NNRat
open RoutingNormalization VertexSplitting
open Lax455465.ConcurrentFlow

structure Distribution {n:ℕ} (G:SimpleGraph (Fin n)) (q:ℕ) where
  probability:Fin q→ ℝ
  nonnegative:∀ i,0≤ probability i
  normalized:(∑ i,probability i)=1
  route:Fin q→ List (Fin n)
  valid:∀ i,0 < probability i→ (route i).Nodup∧ (route i).IsChain G.Adj∧ route i ≠ []
  uniform:∀ u v, (∑ i,if (route i).head?=some u∧ (route i).getLast?=some v then
    probability i else 0)=1 / (n:ℝ) ^ 2

noncomputable def Distribution.toSampling {n q:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q):PathSampling.Distribution n q where
  probability:=D.probability
  nonnegative:=D.nonnegative
  normalized:=D.normalized
  vertices i:=(D.route i).toFinset

end Lax263307.RouteDistributions

end

section

namespace Lax263307.ConditionalRoutes

open RouteDistributions

noncomputable def conditional {n q:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (u v:Fin n) (i:Fin q):ℝ:=
  if (D.route i).head?=some u∧ (D.route i).getLast?=some v then
    (n:ℝ) ^ 2 * D.probability i else 0

end Lax263307.ConditionalRoutes

end

section

namespace Lax263307.FiniteProductSampling

variable {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

noncomputable def weight (f:ι→ κ→ ℝ) (φ:ι→ κ):ℝ:= ∏ a,f a (φ a)

end Lax263307.FiniteProductSampling

end

section

namespace Lax263307.CoupledRouteSampling

open RouteDistributions ConditionalRoutes
open FiniteProductSampling

noncomputable def uniformWeight (n:ℕ):Fin n→ ℝ:=fun _ => 1 / (n:ℝ)

noncomputable def jointWeight {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (a b:Fin m→ Fin t)
    (φ:Fin t→ Fin n) (ψ:Fin m→ Fin q):ℝ:=
  weight (fun _:Fin t => uniformWeight n) φ *
    weight (fun e => conditional D (φ (a e)) (φ (b e))) ψ

end Lax263307.CoupledRouteSampling

end

section

namespace Lax263307.SamplingOutcomes

open scoped Classical

open PathSampling

noncomputable def eventProbability {n q:ℕ} (P:Distribution n q)
    (event:Set (Fin q)):ℝ:=
  ∑ i,if i∈ event then P.probability i else 0

end Lax263307.SamplingOutcomes

end

section

namespace Lax263307.CoupledSamplingBounds

open scoped Classical

open PathSampling (adjacencyProbability collisionProbability expectedSize)
open RouteDistributions CoupledRouteSampling

def Interaction {n q:ℕ} (G:SimpleGraph (Fin n))
    (D:Distribution G q) (i j:Fin q):Prop:=
  ¬Disjoint (D.route i).toFinset (D.route j).toFinset∨
    ∃ u∈ (D.route i).toFinset, ∃ v∈ (D.route j).toFinset,G.Adj u v

noncomputable instance {n q:ℕ} (G:SimpleGraph (Fin n))
    (D:Distribution G q) (i j:Fin q):Decidable (Interaction G D i j):=Classical.propDecidable _

noncomputable def badProbability {n q t m:ℕ} (G:SimpleGraph (Fin n))
    (D:Distribution G q) (a b:Fin m→ Fin t):ℝ:=
  ∑ φ, ∑ ψ,if ∃ e f,Function.Injective ![a e,b e,a f,b f]∧ Interaction G D (ψ e) (ψ f)
    then jointWeight D a b φ ψ else 0

end Lax263307.CoupledSamplingBounds

end

section

namespace Lax263307.InducedEmbeddingWidth

open PathSampling (adjacencyProbability collisionProbability expectedSize)
open RouteDistributions (Distribution)
open RoutePruning (longEdges)
open AlmostEmbeddings InducedRouteEdges Lax228581.Treewidth
open GraphClasses

def HasBagBound (C:GraphClass) (W:ℕ→ ℕ):Prop:=
  ∀ n (G:SimpleGraph (Fin n)),G∈ C n→
    ∃ D:TreeDecomposition G, ∀ i, (D.bag i).card≤ W G.edgeSet.ncard

end Lax263307.InducedEmbeddingWidth

end

section

namespace Lax263307.PowerBagBounds

open GraphClasses InducedEmbeddingWidth Lax228581.Treewidth

def bagBound (a A m:ℕ):ℕ:=Nat.nthRoot a (A * (m + 1) ^ (a - 1))

end Lax263307.PowerBagBounds

end

section

namespace Lax263307Proofs.EdgeBagBounds

theorem log2_le_log (n:ℕ):
    (Nat.log2 n:ℝ)≤ Real.log ((n:ℝ) + 1) / Real.log 2:=by
  have htwo:0 < Real.log 2:=Real.log_pos (by norm_num)
  have hp:(2:ℝ) ^ Nat.log2 n≤ (n:ℝ) + 1:=by
    by_cases hn:n=0
    · simp [hn]
    · have h:=Nat.pow_log_le_self 2 hn
      rw [← Nat.log2_eq_log_two] at h
      have hh:(2:ℝ) ^ Nat.log2 n≤ n:=by exact_mod_cast h
      linarith
  have h:=Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at h
  exact (le_div_iff₀ htwo).mpr h

theorem depth_absorb (ε:ℝ) (hε:0 < ε) (n m:ℕ) (order_bound:n≤ 2 * m):
    (Lax263307.RecursionDepth.depth n + 1:ℝ)≤
      (2 / (ε * Real.log 2) + 5) * Real.rpow ((m:ℝ) + 1) ε:=by
  let z:ℝ:=m + 1
  have hz:1≤ z:=by dsimp [z]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hp:1≤ Real.rpow z ε:=Real.one_le_rpow hz hε.le
  have hlog2:0 < Real.log 2:=Real.log_pos (by norm_num)
  have hlog:Real.log ((n:ℝ) + 1)≤ Real.log (2 * z):=
    Real.log_le_log (by positivity) (by dsimp [z]; exact_mod_cast (show n + 1≤ 2 * (m + 1) by omega))
  have hsplit:Real.log (2 * z)=Real.log 2 + Real.log z:=
    Real.log_mul (by norm_num) (by linarith)
  have hdr:(Lax263307.RecursionDepth.depth n:ℝ)≤ 2 * ((Nat.log2 n:ℝ) + 1):=by
    exact_mod_cast Lax263307Proofs.RecursionDepth.logarithmic_bound n
  have hnat:=log2_le_log n
  have hsmall:=Real.log_le_rpow_div (show 0≤ z by linarith) hε
  have htop:Real.log ((n:ℝ) + 1)≤ Real.log 2 + Real.rpow z ε / ε:=
    hlog.trans (hsplit.le.trans (add_le_add_right hsmall _))
  have hnat':(Nat.log2 n:ℝ)≤ 1 + Real.rpow z ε / (ε * Real.log 2):=by
    apply hnat.trans
    calc
      _≤ (Real.log 2 + Real.rpow z ε / ε) / Real.log 2:=
        div_le_div_of_nonneg_right htop hlog2.le
      _=_:=by field_simp
  have heq:(2 / (ε * Real.log 2) + 5) * Real.rpow z ε =
      2 * (Real.rpow z ε / (ε * Real.log 2)) + 5 * Real.rpow z ε:=by ring
  change (Lax263307.RecursionDepth.depth n:ℝ) + 1≤ _
  rw [heq]
  linarith

open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators Lax228581.Treewidth

theorem edge_order_bound (C:GraphClass) (hereditary:IsHereditary C)
    (B:ℕ→ ℕ) (monotone:Monotone B) (positive:∀ m,1≤ B m)
    (separators:∀ n (G:SimpleGraph (Fin n)),G∈ C n→
      ∃ S:Finset (Fin n),IsBalancedSeparator G S∧ S.card≤ B G.edgeSet.ncard)
    {n:ℕ} (G:SimpleGraph (Fin n)) (member:G∈ C n):
    ∃ r:ℕ,r≤ 2 * G.edgeSet.ncard∧ ∃ D:TreeDecomposition G, ∀ j,
      (D.bag j).card≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth r + 1):=by
  classical
  let U:=Finset.univ.filter (fun v => 0 < G.degree v)
  have hU:U.card≤ 2 * G.edgeSet.ncard:=by
    have hsum:(∑ v:Fin n,if 0 < G.degree v then 1 else 0)≤ ∑ v:Fin n,G.degree v:=by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> omega
    rw [G.sum_degrees_eq_twice_card_edges,G.edgeFinset_card,Set.fintypeCard_eq_ncard] at hsum
    simpa [U] using hsum
  let V:= ↥(↑U:Set (Fin n))
  let r:=Fintype.card V
  let e:V ≃ Fin r:=Fintype.equivFin V
  let H:=(G.induce (↑U:Set (Fin n))).comap e.symm
  let f:H ↪g G:= {
    toFun:=fun v => (e.symm v).val
    inj':=fun a b h => e.symm.injective (Subtype.ext h)
    map_rel_iff':=Iff.rfl }
  have hH:=hereditary r n H G member ⟨f⟩
  obtain ⟨D,hD⟩:=Lax263307Proofs.SeparatorDecompositions.recursive_bag_bound C hereditary B monotone positive separators H hH
  let g:(G.induce (↑U:Set (Fin n))) ↪g H:= {
    toFun:=e
    inj':=e.injective
    map_rel_iff':=by intro a b; simp [H] }
  let E:=Lax263307Proofs.TreeExtensions.pullback g D
  have hB:1≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth r + 1):=
    by have:=positive G.edgeSet.ncard; nlinarith
  have hE (j:E.Node):(E.bag j).card≤ B G.edgeSet.ncard * (Lax263307.RecursionDepth.depth r + 1):=
    (Lax263307Proofs.TreeExtensions.pullback_card g D j).trans ((hD j).trans
      (Nat.mul_le_mul_right _ (monotone (Lax263307Proofs.SeparatorDecompositions.embedding_edge_bound f))))
  have isolated (v:Fin n) (hv:v∉ (↑U:Set (Fin n))):G.IsIsolated v:=by
    have hz:G.degree v=0:=by
      have hnot:¬0 < G.degree v:=by simpa [U] using hv
      omega
    intro u hu
    exact (G.degree_eq_zero v).mp hz u hu
  refine ⟨r, ?_,Lax263307Proofs.TreeExtensions.extendIsolated (G:=G) (↑U) isolated E,
    Lax263307Proofs.TreeExtensions.extendIsolated_card (G:=G) (↑U) isolated E _ hB hE⟩
  have hr:r=U.card:=Fintype.card_coe _
  rw [hr]
  exact hU

theorem sublinear_bag_bound (C:GraphClass) (hereditary:IsHereditary C)
    (separators:HasStronglyEdgeSublinearSeparators C):
    ∃ β c:ℝ,0≤ β∧ β < 1∧ 0 < c∧ ∀ n (G:SimpleGraph (Fin n)),G∈ C n→
      ∃ D:TreeDecomposition G, ∀ j,
        ((D.bag j).card:ℝ)≤ c * Real.rpow ((G.edgeSet.ncard:ℝ) + 1) β:=by
  classical
  obtain ⟨b,c,hb,hb1,hc,hsep⟩:=separators
  let ε:=(1 - b) / 2
  have hε:0 < ε:=by dsimp [ε]; linarith
  let B (m:ℕ):=Nat.ceil (c * Real.rpow ((m:ℝ) + 1) b)
  have hmono:Monotone B:=by
    intro m t hmt
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_left _ hc.le
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hmt 1) hb
  have hpos (m:ℕ):1≤ B m:=by
    apply Nat.one_le_ceil_iff.mpr
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) b)
  have hseps:∀ n (G:SimpleGraph (Fin n)),G∈ C n→
      ∃ S:Finset (Fin n),IsBalancedSeparator G S∧ S.card≤ B G.edgeSet.ncard:=by
    intro n G hG
    obtain ⟨S,hS,hcost⟩:=hsep n G hG
    exact ⟨S,hS,Nat.cast_le.mp (hcost.trans (Nat.le_ceil _))⟩
  have hDpos:0 < 2 / (ε * Real.log 2) + 5:=by
    have:0 < Real.log 2:=Real.log_pos (by norm_num)
    positivity
  refine ⟨b + ε, (c + 1) * (2 / (ε * Real.log 2) + 5),by dsimp [ε]; linarith,
    by dsimp [ε]; linarith,mul_pos (by linarith) hDpos, ?_⟩
  intro n G hG
  obtain ⟨r,hr,D,hD⟩:=edge_order_bound C hereditary B hmono hpos hseps G hG
  refine ⟨D,fun j => ?_⟩
  let m:=G.edgeSet.ncard
  have hpow:1≤ Real.rpow ((m:ℝ) + 1) b:=Real.one_le_rpow (by have:=Nat.cast_nonneg m (α:=ℝ); linarith) hb
  have hB:(B m:ℝ)≤ (c + 1) * Real.rpow ((m:ℝ) + 1) b:=by
    have hceil:=(Nat.ceil_lt_add_one (show 0≤ c * Real.rpow ((m:ℝ) + 1) b by positivity)).le
    change (Nat.ceil (c * Real.rpow ((m:ℝ) + 1) b):ℝ)≤ _
    nlinarith
  have hdr:=depth_absorb ε hε r m hr
  have hj:((D.bag j).card:ℝ)≤ (B m:ℝ) * (Lax263307.RecursionDepth.depth r + 1):=by
    exact_mod_cast hD j
  calc
    _≤ (B m:ℝ) * (Lax263307.RecursionDepth.depth r + 1):=hj
    _≤ ((c + 1) * Real.rpow ((m:ℝ) + 1) b) *
        ((2 / (ε * Real.log 2) + 5) * Real.rpow ((m:ℝ) + 1) ε):=
      mul_le_mul hB hdr (by positivity) (by positivity)
    _=_:=by
      have hpower:Real.rpow ((m:ℝ) + 1) (b + ε) =
          Real.rpow ((m:ℝ) + 1) b * Real.rpow ((m:ℝ) + 1) ε:=
        Real.rpow_add (by positivity) b ε
      change _=(c + 1) * (2 / (ε * Real.log 2) + 5) * Real.rpow ((m:ℝ) + 1) (b + ε)
      rw [hpower]
      ring

end Lax263307Proofs.EdgeBagBounds

end

section

namespace Lax263307Proofs.BlowUpBagBounds

open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open Lax263307.BlowUpClasses Lax263307.IndependentBlowUp Lax228581.Treewidth

theorem blowup_sublinear_bag_bound (C:GraphClass) (hereditary:IsHereditary C)
    (separators:HasStronglyEdgeSublinearSeparators C):
    ∃ β c:ℝ,0≤ β∧ β < 1∧ 0 < c∧ ∀ m (H:SimpleGraph (Fin m)),H∈ blowUpClass C m→
      ∃ D:TreeDecomposition H, ∀ j,
        ((D.bag j).card:ℝ)≤ c * Real.rpow ((H.edgeSet.ncard:ℝ) + 1) β:=by
  classical
  obtain ⟨b,c,hb,hb1,hc,hbase⟩:=Lax263307Proofs.EdgeBagBounds.sublinear_bag_bound C hereditary separators
  refine ⟨(1 + b) / 2,3 + 2 * (c + 2),by linarith,by linarith,by linarith, ?_⟩
  intro m H hH
  obtain ⟨n,G,hG,p,hAdj⟩:=hH
  let U:=Finset.univ.image p
  let V:= ↥(↑U:Set (Fin n))
  let r:=Fintype.card V
  let e:V ≃ Fin r:=Fintype.equivFin V
  let G₀:=G.comap (fun i:Fin r => (e.symm i).val)
  let f:G₀ ↪g G:= {
    toFun:=fun i => (e.symm i).val
    inj':=fun a b h => e.symm.injective (Subtype.ext h)
    map_rel_iff':=Iff.rfl }
  have hG₀:=hereditary r n G₀ G hG ⟨f⟩
  let q (u:Fin m):Fin r:=e ⟨p u,Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩⟩
  have hq (u:Fin m):(e.symm (q u)).val=p u:=by
    dsimp only [q]
    rw [e.symm_apply_apply]
  have hqsurj:Function.Surjective q:=by
    intro i
    obtain ⟨u,_,hu⟩:=Finset.mem_image.mp (e.symm i).property
    refine ⟨u,e.symm.injective (Subtype.ext ?_)⟩
    rw [hq]
    exact hu
  have hAdj₀ (u v:Fin m):H.Adj u v↔ G₀.Adj (q u) (q v):=by
    change H.Adj u v↔ G.Adj (e.symm (q u)).val (e.symm (q v)).val
    rw [hq,hq]
    exact hAdj u v
  let s (i:Fin r):=Classical.choose (hqsurj i)
  have hs (i:Fin r):q (s i)=i:=Classical.choose_spec (hqsurj i)
  let representative:G₀ ↪g H:= {
    toFun:=s
    inj':=(show Function.LeftInverse q s from hs).injective
    map_rel_iff':=by intro i j; change H.Adj (s i) (s j)↔ G₀.Adj i j; rw [hAdj₀,hs,hs] }
  have hedge:G₀.edgeSet.ncard≤ H.edgeSet.ncard:=
    Lax263307Proofs.SeparatorDecompositions.embedding_edge_bound representative
  let copies (i:Fin r):=Fintype.card {u:Fin m // q u=i}
  let label:Vertex copies ≃ Fin m:=
    (Equiv.sigmaCongrRight (fun i => (Fintype.equivFin {u:Fin m // q u=i}).symm)).trans
      (Equiv.sigmaFiberEquiv q)
  have hlabel (u:Vertex copies):q (label u)=u.1:=by
    change q (((Fintype.equivFin {v:Fin m // q v=u.1}).symm u.2).val)=u.1
    exact ((Fintype.equivFin {v:Fin m // q v=u.1}).symm u.2).property
  let iso:graph G₀ copies ≃g H:= {
    toEquiv:=label
    map_rel_iff':=by
      intro u v
      change H.Adj (label u) (label v)↔ G₀.Adj u.1 v.1
      rw [hAdj₀,hlabel,hlabel] }
  have hcount:(graph G₀ copies).edgeSet.ncard=H.edgeSet.ncard:=by
    have h:=Fintype.card_congr iso.mapEdgeSet
    simpa only [Set.fintypeCard_eq_ncard] using h
  let M:ℝ:=(H.edgeSet.ncard:ℝ) + 1
  have hM:1≤ M:=by dsimp [M]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hpow:1≤ Real.rpow M b:=Real.one_le_rpow hM hb
  obtain ⟨D₀,hD₀⟩:=hbase r G₀ hG₀
  have hbags (j:D₀.Node):((D₀.bag j).card:ℝ)≤ c * Real.rpow M b:=by
    exact (hD₀ j).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by dsimp [M]; exact_mod_cast Nat.add_le_add_right hedge 1) hb) hc.le)
  let w:=Nat.ceil ((c + 1) * Real.rpow M b) - 1
  have hceilpos:1≤ Nat.ceil ((c + 1) * Real.rpow M b):=Nat.one_le_ceil_iff.mpr (by positivity)
  have hw:w + 1=Nat.ceil ((c + 1) * Real.rpow M b):=Nat.sub_add_cancel hceilpos
  have hwidth:HasTreewidthAtMost G₀ w:=by
    refine ⟨D₀,fun j => ?_⟩
    rw [hw]
    have hcard:((D₀.bag j).card:ℝ)≤ (Nat.ceil ((c + 1) * Real.rpow M b):ℝ):=
      (hbags j).trans ((by nlinarith:c * Real.rpow M b≤ (c + 1) * Real.rpow M b).trans (Nat.le_ceil _))
    exact_mod_cast hcard
  have hwidth_bound:(w + 1:ℕ)≤ (c + 2) * Real.rpow ((graph G₀ copies).edgeSet.ncard + 1) b:=by
    rw [hw,hcount]
    have h:=(Nat.ceil_lt_add_one (show 0≤ (c + 1) * Real.rpow M b by positivity)).le
    change (Nat.ceil ((c + 1) * Real.rpow M b):ℝ)≤ (c + 2) * Real.rpow M b
    nlinarith
  obtain ⟨D,hD⟩:=Lax263307Proofs.BlowUpDeletion.power_bound G₀ copies w b (c + 2) hb hb1 (by linarith)
    hwidth hwidth_bound
  let E:=Lax263307Proofs.TreeExtensions.pullback iso.symm.toRelEmbedding D
  refine ⟨E,fun j => ?_⟩
  have hcard:((E.bag j).card:ℝ)≤ ((D.bag j).card:ℝ):=by
    exact_mod_cast Lax263307Proofs.TreeExtensions.pullback_card iso.symm.toRelEmbedding D j
  exact hcard.trans (by simpa only [hcount] using hD j)

theorem blowup_power_bag_bound (C:GraphClass) (hereditary:IsHereditary C)
    (separators:HasStronglyEdgeSublinearSeparators C):
    ∃ a A:ℕ,0 < a∧ 0 < A∧ Lax263307.PowerBagBounds.HasPowerBagBound (blowUpClass C) a A:=by
  obtain ⟨β,c,_hβ,hβ1,hc,hbags⟩:=Lax263307Proofs.BlowUpBagBounds.blowup_sublinear_bag_bound C hereditary separators
  have hgap:0 < 1 - β:=by linarith
  obtain ⟨a,ha⟩:=exists_nat_gt (1 / (1 - β))
  have hap:0 < a:=by
    have hi:0 < 1 / (1 - β):=div_pos zero_lt_one hgap
    have:(0:ℝ) < a:=hi.trans ha
    exact_mod_cast this
  have hexp:β * (a:ℝ)≤ (a - 1:ℕ):=by
    have hg:1 < (a:ℝ) * (1 - β):=(div_lt_iff₀ hgap).mp ha
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    nlinarith
  let A:=Nat.ceil (c ^ a) + 1
  have hA:c ^ a≤ (A:ℝ):=by
    have h:=Nat.le_ceil (c ^ a)
    simp only [A,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨a,A,hap,by dsimp [A]; omega, ?_⟩
  intro n G hG
  obtain ⟨D,hD⟩:=hbags n G hG
  refine ⟨D,fun j => ?_⟩
  let m:=G.edgeSet.ncard
  have hm:1≤ (m:ℝ) + 1:=by have:=Nat.cast_nonneg m (α:=ℝ); linarith
  have hj:((D.bag j).card:ℝ) ^ a≤ (A:ℝ) * ((m:ℝ) + 1) ^ (a - 1):=by
    calc
      _≤ (c * Real.rpow ((m:ℝ) + 1) β) ^ a:=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hD j) a
      _=c ^ a * Real.rpow ((m:ℝ) + 1) (β * (a:ℝ)):=by
        rw [mul_pow]
        have hp:Real.rpow ((m:ℝ) + 1) (β * (a:ℝ)) =
            Real.rpow ((m:ℝ) + 1) β ^ a:=Real.rpow_mul_natCast (by linarith) β a
        rw [hp]
      _≤ (A:ℝ) * Real.rpow ((m:ℝ) + 1) (a - 1:ℕ):=
        mul_le_mul hA (Real.rpow_le_rpow_of_exponent_le hm hexp) (Real.rpow_nonneg (by linarith) _) (Nat.cast_nonneg A)
      _=_:=by rw [Real.rpow_eq_pow,Real.rpow_natCast]
  exact_mod_cast hj

end Lax263307Proofs.BlowUpBagBounds

end

section

namespace Lax263307Proofs.PositiveWeights

open Lax263307.WeightedIndependentSet Lax263307.PositiveWeights RelaxationAlgebra

theorem clipped_weight_eq {n:ℕ} (w:Fin n→ ℚ) (I:Finset (Fin n)):
    weight w (discardNonpositive w I)=weight (positiveWeights w) I:=by
  simp only [weight,discardNonpositive,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h:0 < w v
  · simp [h,positiveWeights,max_eq_left h.le]
  · simp [h,positiveWeights,max_eq_right (not_lt.mp h)]

theorem signed_weight_transfer {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ ℚ)
    (ε:ℚ) (_accuracy_nonnegative:0≤ ε) (accuracy_le_one:ε≤ 1)
    (I:Finset (Fin n)) (approximation:IsApproximation G (positiveWeights w) ε I):
    IsApproximation G w ε (discardNonpositive w I):=by
  refine ⟨independent_subset G approximation.1 (Finset.filter_subset _ _), ?_⟩
  intro J hJ
  rw [clipped_weight_eq]
  have hweight:weight w J≤ weight (positiveWeights w) J:=
    Finset.sum_le_sum fun v _ => le_max_left (w v) 0
  exact (mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr accuracy_le_one)).trans
    (approximation.2 J hJ)

theorem nonpositive_case {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ ℚ)
    (nonpositive:∀ v,w v≤ 0) (ε:ℚ) (_accuracy_nonnegative:0≤ ε)
    (accuracy_le_one:ε≤ 1):IsApproximation G w ε ∅:=by
  refine ⟨by simp [SimpleGraph.IsIndepSet], ?_⟩
  intro J _
  have hsum:weight w J≤ 0:=Finset.sum_nonpos fun v _ => nonpositive v
  simpa [weight] using mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr accuracy_le_one) hsum

end Lax263307Proofs.PositiveWeights

end

section

namespace Lax263307Proofs.RoundingBounds

open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

theorem maximum_nonnegative {n:ℕ} (w:Fin n→ ℚ):0≤ maximumWeight w:=by
  exact (insert 0 (Finset.univ.image w)).le_max' 0 (by simp)

theorem scale_positive {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ)
    (hn:0 < n) (hε:0 < ε) (hW:0 < maximumWeight w):0 < scale w ε:=by
  have hnQ:(0:ℚ) < n:=by exact_mod_cast hn
  exact div_pos (mul_pos hε hW) (mul_pos (by norm_num) hnQ)

theorem pointwise_bounds {n:ℕ} (w:Fin n→ ℚ) (τ:ℚ)
    (nonnegative:∀ v,0≤ w v) (positive_scale:0 < τ):
    ∀ v,τ * (roundedCopies w τ v:ℚ)≤ w v∧
      w v - τ≤ τ * (roundedCopies w τ v:ℚ):=by
  intro v
  have hupper:=(le_div_iff₀ positive_scale).1
    (Nat.floor_le (div_nonneg (nonnegative v) positive_scale.le))
  have hlower:=(div_lt_iff₀ positive_scale).1 (Nat.lt_floor_add_one (w v / τ))
  dsimp [roundedCopies]
  constructor <;> nlinarith

theorem set_rounding_loss {n:ℕ} (w:Fin n→ ℚ) (τ:ℚ)
    (nonnegative:∀ v,0≤ w v) (positive_scale:0 < τ) (J:Finset (Fin n)):
    weight w J - (J.card:ℚ) * τ≤ τ * ((∑ v∈ J,roundedCopies w τ v:ℕ):ℚ):=by
  calc
    weight w J - (J.card:ℚ) * τ=∑ v∈ J, (w v - τ):=by
      simp [weight,Finset.sum_sub_distrib]
    _≤ ∑ v∈ J,τ * (roundedCopies w τ v:ℚ):=
      Finset.sum_le_sum fun v _ =>
        (Lax263307Proofs.RoundingBounds.pointwise_bounds w τ nonnegative positive_scale v).2
    _=τ * ((∑ v∈ J,roundedCopies w τ v:ℕ):ℚ):=by
      push_cast
      rw [Finset.mul_sum]

end Lax263307Proofs.RoundingBounds

end

section

namespace Lax263307Proofs.WeightedProjection

open Lax263307.WeightedIndependentSet Lax263307.WeightRounding Lax263307.IndependentBlowUp
open RoundingBounds

theorem exists_optimal_set {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ ℚ):
    ∃ I:Finset (Fin n),G.IsIndepSet (I:Set (Fin n))∧
      ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ weight w J≤ weight w I:=by
  classical
  let S:=Finset.univ.filter fun I:Finset (Fin n) => G.IsIndepSet (I:Set (Fin n))
  have hS:S.Nonempty:= ⟨∅,by simp [S,SimpleGraph.IsIndepSet]⟩
  obtain ⟨I,hI,hmax⟩:=Finset.exists_max_image S (weight w) hS
  refine ⟨I, (Finset.mem_filter.mp hI).2, ?_⟩
  intro J hJ
  exact hmax J (by simp [S,hJ])

theorem maximum_le_optimal {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ ℚ)
    (I:Finset (Fin n))
    (hmax:∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ weight w J≤ weight w I):
    maximumWeight w≤ weight w I:=by
  apply Finset.max'_le
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · simpa [weight] using hmax ∅ (by simp [SimpleGraph.IsIndepSet])
  · obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha
    simpa [weight] using hmax {v} (by simp [SimpleGraph.IsIndepSet])

theorem projection_weight_lower {n:ℕ} (w:Fin n→ ℚ) (τ:ℚ)
    (hw:∀ v,0≤ w v) (hτ:0 < τ) (K:Finset (Vertex (roundedCopies w τ))):
    τ * (K.card:ℚ)≤ weight w (project K):=by
  have hcard:(K.card:ℚ)≤ ((∑ v∈ project K,roundedCopies w τ v:ℕ):ℚ):=by
    exact_mod_cast Lax263307Proofs.BlowUpIndependentSets.projection_capacity (roundedCopies w τ) K
  calc
    τ * (K.card:ℚ)≤ τ * ((∑ v∈ project K,roundedCopies w τ v:ℕ):ℚ):=
      mul_le_mul_of_nonneg_left hcard hτ.le
    _=∑ v∈ project K,τ * (roundedCopies w τ v:ℚ):=by
      push_cast
      rw [Finset.mul_sum]
    _≤ weight w (project K):=Finset.sum_le_sum fun v _ =>
      (Lax263307Proofs.RoundingBounds.pointwise_bounds w τ hw hτ v).1

theorem approximation_transfer {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ ℚ)
    (ε:ℚ) (nonnegative:∀ v,0≤ w v) (positive_order:0 < n)
    (positive_accuracy:0 < ε) (accuracy_lt_one:ε < 1)
    (positive_maximum:0 < maximumWeight w)
    (K:Finset (Vertex (copies w ε)))
    (approximation:IsCardinalityApproximation G (copies w ε) (ε / 2) K):
    IsApproximation G w ε (project K):=by
  obtain ⟨I,hI,hmax⟩:=exists_optimal_set G w
  have hW:=maximum_le_optimal G w I hmax
  have hopt:0≤ weight w I:=(maximum_nonnegative w).trans hW
  have hτ:=scale_positive w ε positive_order positive_accuracy positive_maximum
  have hρ:0≤ 1 - ε / 2:=by linarith
  have hn:(n:ℚ) ≠ 0:=by exact_mod_cast ne_of_gt positive_order
  have hcardI:(I.card:ℚ)≤ n:=by
    exact_mod_cast (show I.card≤ n from by simpa using Finset.card_le_univ I)
  have hscale:(n:ℚ) * scale w ε=(ε / 2) * maximumWeight w:=by
    unfold scale
    field_simp
  have herror:(I.card:ℚ) * scale w ε≤ (ε / 2) * weight w I:=by
    calc
      (I.card:ℚ) * scale w ε≤ (n:ℚ) * scale w ε:=
        mul_le_mul_of_nonneg_right hcardI hτ.le
      _=(ε / 2) * maximumWeight w:=hscale
      _≤ (ε / 2) * weight w I:=mul_le_mul_of_nonneg_left hW (by positivity)
  have hloss:=Lax263307Proofs.RoundingBounds.set_rounding_loss
    w (scale w ε) nonnegative hτ I
  change weight w I - (I.card:ℚ) * scale w ε≤
    scale w ε * ((∑ v∈ I,copies w ε v:ℕ):ℚ) at hloss
  rw [← Lax263307Proofs.BlowUpIndependentSets.lift_cardinality (copies w ε) I] at hloss
  have hrounded:(1 - ε / 2) * weight w I≤
      scale w ε * ((lift (copies w ε) I).card:ℚ):=by linarith
  have hcompare:=approximation.2 (lift (copies w ε) I)
    (Lax263307Proofs.BlowUpIndependentSets.lift_independent G (copies w ε) I hI)
  have hscaled:=mul_le_mul_of_nonneg_left hcompare hτ.le
  have hweight:=projection_weight_lower w (scale w ε) nonnegative hτ K
  have hcombined:(1 - ε / 2) ^ 2 * weight w I≤ weight w (project K):=by
    calc
      (1 - ε / 2) ^ 2 * weight w I=(1 - ε / 2) * ((1 - ε / 2) * weight w I):=by ring
      _≤ (1 - ε / 2) * (scale w ε * ((lift (copies w ε) I).card:ℚ)):=
        mul_le_mul_of_nonneg_left hrounded hρ
      _=scale w ε * ((1 - ε / 2) * ((lift (copies w ε) I).card:ℚ)):=by ring
      _≤ scale w ε * (K.card:ℚ):=hscaled
      _≤ weight w (project K):=hweight
  have hfactor:1 - ε≤ (1 - ε / 2) ^ 2:=by nlinarith [sq_nonneg ε]
  have hmain:=(mul_le_mul_of_nonneg_right hfactor hopt).trans hcombined
  refine ⟨Lax263307Proofs.BlowUpIndependentSets.project_independent G (copies w ε) K approximation.1, ?_⟩
  intro J hJ
  exact (mul_le_mul_of_nonneg_left (hmax J hJ) (by linarith)).trans hmain

end Lax263307Proofs.WeightedProjection

end

section

namespace Lax263307.ConditioningDistribution

open LinearRelaxation

noncomputable def marginal {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (k:ℕ) (v:Fin n):ℝ:=
  conditioned y A v / k

noncomputable def joint {n r:ℕ} (y:MomentVector n r)
    (A:Finset (Fin n)) (k:ℕ) (u v:Fin n):ℝ:=
  value y (insert u (insert v A)) / ((k:ℝ) ^ 2 * value y A)

end Lax263307.ConditioningDistribution

end

section

namespace Lax263307Proofs.EntropyAlgebra

open Lax263307.Entropy

theorem log_two_pos:0 < Real.log 2:=Real.log_pos (by norm_num)

theorem log_two_le_one:Real.log 2≤ 1:=by
  have:=Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  norm_num at this ⊢
  exact this

theorem probability_entry_le_one {n:ℕ} (π:Fin n→ ℝ) (hπ:IsProbability π)
    (v:Fin n):π v≤ 1:=by
  rw [← hπ.2]
  exact Finset.single_le_sum (fun u _ => hπ.1 u) (Finset.mem_univ v)

theorem scaled_negMulLog_div (a x:ℝ) (ha:0 < a):
    a * Real.negMulLog (x / a)=Real.negMulLog x + x * Real.log a:=by
  by_cases hx:x=0
  · simp [hx]
  · dsimp [Real.negMulLog]
    rw [Real.log_div hx (ne_of_gt ha)]
    field_simp
    ring

theorem relative_term_bound (x a b:ℝ) (hx:0 < x) (ha:0 < a) (hb:0 < b):
    x - a * b≤ -Real.negMulLog x - x * Real.log a - x * Real.log b:=by
  have hab:0 < a * b:=mul_pos ha hb
  have h:=Real.log_le_sub_one_of_pos (div_pos hab hx)
  rw [Real.log_div (ne_of_gt hab) (ne_of_gt hx),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hb)] at h
  have hm:=mul_le_mul_of_nonneg_left h hx.le
  simp_rw [mul_sub] at hm
  rw [mul_div_cancel₀ _ (ne_of_gt hx),mul_one] at hm
  dsimp [Real.negMulLog]
  nlinarith

theorem natural_entropy_nonneg {n:ℕ} (π:Fin n→ ℝ) (hπ:IsProbability π):
    0≤ naturalEntropy π:=
  Finset.sum_nonneg fun v _ => Real.negMulLog_nonneg (hπ.1 v) (probability_entry_le_one π hπ v)

theorem natural_entropy_le_log {n:ℕ} (π:Fin n→ ℝ) (hπ:IsProbability π):
    naturalEntropy π≤ Real.log n:=by
  have hn:0 < n:=by
    by_contra hn
    have hn0:n=0:=by omega
    subst n
    simpa using hπ.2
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  have hn0:(n:ℝ) ≠ 0:=ne_of_gt hnR
  have hw:(∑ _v:Fin n, (1 / (n:ℝ)))=1:=by simp [hn0]
  have h:=Real.concaveOn_negMulLog.le_map_sum
    (t:=Finset.univ) (w:=fun _:Fin n => 1 / (n:ℝ)) (p:=π)
    (fun _ _ => (one_div_pos.mpr hnR).le) hw (fun v _ => hπ.1 v)
  simp only [smul_eq_mul] at h
  simp_rw [← Finset.mul_sum] at h
  rw [hπ.2,mul_one] at h
  have hm:=mul_le_mul_of_nonneg_left h hnR.le
  rw [← mul_assoc,mul_one_div_cancel hn0,one_mul] at hm
  have heq:(n:ℝ) * Real.negMulLog (1 / (n:ℝ))=Real.log n:=by
    simp [Real.negMulLog,hn0]
  exact hm.trans_eq heq

end Lax263307Proofs.EntropyAlgebra

end

section

namespace Lax263307Proofs.EntropyDecrease

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307.Entropy EntropyAlgebra

theorem adjacencyMass_div {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℝ) (k:ℝ) (hk:k ≠ 0):
    adjacencyMass G (fun v => x v / k)=adjacencyMass G x / k ^ 2:=by
  unfold adjacencyMass
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs
  · field_simp
  · simp

end Lax263307Proofs.EntropyDecrease

end

section

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open EntropyDecrease

theorem value_cast {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n)):
    value (realVector y) A=(rationalValue y A:ℝ):=by
  by_cases hA:A.card≤ r + 2 <;> simp [value,realVector,rationalValue,hA]

theorem edge_cost_formula {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y:RationalVector n r) (A:Finset (Fin n)) (hA:0 < rationalValue y A):
    edgeCost G (conditioned (realVector y) A) =
      (edgeNumerator G y A:ℝ) / (2 * (rationalValue y A:ℝ) ^ 2):=by
  have hpos:(0:ℝ) < (rationalValue y A:ℝ):=by exact_mod_cast hA
  have hcost:conditioned (realVector y) A=fun v =>
      (rationalValue y (insert v A):ℝ) / (rationalValue y A:ℝ):=by
    funext v
    simp [conditioned,value_cast]
  have hnum:adjacencyMass G (fun v => (rationalValue y (insert v A):ℝ)) =
      (edgeNumerator G y A:ℝ):=by
    unfold adjacencyMass edgeNumerator
    push_cast
    simp only [apply_ite,Rat.cast_mul,Rat.cast_zero]
  rw [edgeCost,hcost,adjacencyMass_div G _ _ (ne_of_gt hpos),hnum]
  ring

theorem passes_iff {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r) (A:Finset (Fin n)) (hp:0 < p):
    Passes G k p y A↔ 0 < value (realVector y) A∧
      edgeCost G (conditioned (realVector y) A)≤ (k:ℝ) ^ 2 / p:=by
  have hpR:(0:ℝ) < p:=by exact_mod_cast hp
  constructor
  · rintro ⟨hpos,hineq⟩
    have hposR:(0:ℝ) < (rationalValue y A:ℝ):=by exact_mod_cast hpos
    refine ⟨by rw [value_cast]; exact hposR, ?_⟩
    rw [edge_cost_formula G y A hpos]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hposR)) hpR).2
    have hR:(p:ℝ) * (edgeNumerator G y A:ℝ)≤
        2 * (k:ℝ) ^ 2 * (rationalValue y A:ℝ) ^ 2:=by exact_mod_cast hineq
    nlinarith
  · rintro ⟨hposR,hineq⟩
    rw [value_cast] at hposR
    have hpos:0 < rationalValue y A:=by exact_mod_cast hposR
    refine ⟨hpos, ?_⟩
    rw [edge_cost_formula G y A hpos] at hineq
    have hR:=(div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hposR)) hpR).1 hineq
    have hresult:(p:ℝ) * (edgeNumerator G y A:ℝ)≤
        2 * (k:ℝ) ^ 2 * (rationalValue y A:ℝ) ^ 2:=by nlinarith
    exact_mod_cast hresult

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

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def realVector {n:ℕ} (x:Fin n→ ℚ):Fin n→ ℝ:=fun j => x j

end Lax109476.RationalCertificates

end

section

namespace Lax109476Proofs.RationalRounding

theorem roundDown_le (q:ℚ) (D:ℕ) (hD:0 < D):roundDown q D≤ q:=by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).mpr
  exact Int.floor_le _

theorem lt_roundDown_add (q:ℚ) (D:ℕ) (hD:0 < D):
    q < roundDown q D + 1 / D:=by
  have hp:(0:ℚ) < D:=by exact_mod_cast hD
  unfold roundDown
  rw [← add_div,lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

theorem roundDown_error (q:ℚ) (D:ℕ) (hD:0 < D):
    0≤ (q:ℝ) - (roundDown q D:ℝ)∧
      (q:ℝ) - (roundDown q D:ℝ) < 1 / (D:ℝ):=by
  have h₁:(roundDown q D:ℝ)≤ (q:ℝ):=by
    exact_mod_cast roundDown_le q D hD
  have h₂:(q:ℝ) < (roundDown q D:ℝ) + 1 / (D:ℝ):=by
    have h:=(Rat.cast_lt (K:=ℝ)).mpr (lt_roundDown_add q D hD)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
  constructor <;> linarith

theorem roundDown_vector_error (n:ℕ) (x:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    (∑ i, ((x i:ℝ) - (roundDown (x i) D:ℝ)) ^ 2)≤
      (n:ℝ) * (1 / (D:ℝ)) ^ 2:=by
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  calc
    _≤ ∑ _i:Fin n, (1 / (D:ℝ)) ^ 2:=by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h₁,h₂⟩:=roundDown_error (x i) D hD
      nlinarith [show (0:ℝ) < 1 / (D:ℝ) by positivity]
    _=_:=by simp

theorem sqrtUpper_bounds (q:ℚ) (hq:0≤ q) (D:ℕ) (hD:0 < D):
    Real.sqrt (q:ℝ)≤ (sqrtUpper q D:ℝ)∧
      (sqrtUpper q D:ℝ) < Real.sqrt (q:ℝ) + 2 / (D:ℝ):=by
  let c:=Nat.ceil (q * (D:ℚ) ^ 2)
  let s:=Nat.sqrt c
  have hqR:(0:ℝ)≤ q:=by exact_mod_cast hq
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  have hcl:(q:ℝ) * (D:ℝ) ^ 2≤ c:=by
    have h:q * (D:ℚ) ^ 2≤ (c:ℚ):=Nat.le_ceil _
    have h':=(Rat.cast_le (K:=ℝ)).mpr h
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast] using h'
  have hcu:(c:ℝ) < (q:ℝ) * (D:ℝ) ^ 2 + 1:=by
    have h:(c:ℚ) < q * (D:ℚ) ^ 2 + 1:=
      Nat.ceil_lt_add_one (show (0:ℚ)≤ q * (D:ℚ) ^ 2 by positivity)
    have h':=(Rat.cast_lt (K:=ℝ)).mpr h
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_one] using h'
  have hsl:(s:ℝ) ^ 2≤ c:=by
    have h:s ^ 2≤ c:=Nat.sqrt_le' c
    have h':=(Nat.cast_le (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow] using h'
  have hsu:(c:ℝ) < ((s:ℝ) + 1) ^ 2:=by
    have h:c < (s + 1) ^ 2:=Nat.lt_succ_sqrt' c
    have h':=(Nat.cast_lt (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h'
  have hs:(0:ℝ)≤ s:=Nat.cast_nonneg _
  have hroot:=Real.sq_sqrt hqR
  have hrootpos:=Real.sqrt_nonneg (q:ℝ)
  have hsqr:(Real.sqrt (q:ℝ) * (D:ℝ)) ^ 2=(q:ℝ) * (D:ℝ) ^ 2:=by
    rw [mul_pow,hroot]
  have hl:Real.sqrt (q:ℝ) * D≤ (s:ℝ) + 1:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hcl,hsu,hsqr,ht,hs]
  have hu:(s:ℝ) + 1 < Real.sqrt (q:ℝ) * D + 2:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hsl,hcu,hsqr,ht,hs,
      sq_nonneg ((s:ℝ) - Real.sqrt (q:ℝ) * D)]
  have heq:(sqrtUpper q D:ℝ)=((s:ℝ) + 1) / D:=by
    simp [sqrtUpper,c,s]
  rw [heq]
  constructor
  · exact (le_div_iff₀ hDR).mpr hl
  · calc
      _ < (Real.sqrt (q:ℝ) * D + 2) / D:=
        (div_lt_div_iff_of_pos_right hDR).mpr hu
      _=_:=by field_simp

end Lax109476Proofs.RationalRounding

end

section

namespace Lax109476Proofs.EllipsoidStep

noncomputable def centralCutForm (n r t:ℝ):ℝ:=
  (n + 1) ^ 2 / n ^ 2 * (t + 1 / (n + 1)) ^ 2 +
    (n ^ 2 - 1) / n ^ 2 * (r - t ^ 2)

theorem centralCutForm_le_one (n r t:ℝ) (hn:2≤ n)
    (hr:r≤ 1) (ht₁:-1≤ t) (ht₂:t≤ 0):
    centralCutForm n r t≤ 1:=by
  have hnpos:0 < n:=by linarith
  have hnzero:n ≠ 0:=ne_of_gt hnpos
  have hnplus:n + 1 ≠ 0:=by linarith
  have hid:centralCutForm n r t =
      ((n ^ 2 - 1) * r + 2 * (n + 1) * t * (t + 1) + 1) / n ^ 2:=by
    unfold centralCutForm
    field_simp
    ring
  rw [hid]
  apply (div_le_one (sq_pos_of_pos hnpos)).mpr
  have hcoeff:0≤ n ^ 2 - 1:=by nlinarith
  have hrad:=mul_le_mul_of_nonneg_left hr hcoeff
  have htprod:t * (t + 1)≤ 0:=
    mul_nonpos_of_nonpos_of_nonneg ht₂ (by linarith)
  have hterm:2 * (n + 1) * (t * (t + 1))≤ 0:=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) htprod
  nlinarith

noncomputable def determinantFactor (n:ℕ):ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) ^ (n - 1) *
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2

theorem determinantFactor_pos (n:ℕ) (hn:2≤ n):0 < determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  unfold determinantFactor
  apply mul_pos
  · apply pow_pos
    apply div_pos <;> nlinarith
  · apply sq_pos_of_pos
    apply div_pos <;> linarith

theorem log_determinantFactor_le (n:ℕ) (hn:2≤ n):
    Real.log (determinantFactor n)≤ -1 / ((n:ℝ) + 1):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hdiff:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  let a:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let b:=(n:ℝ) / ((n:ℝ) + 1)
  have ha:0 < a:=div_pos (sq_pos_of_pos hnp) hdiff
  have hb:0 < b:=div_pos hnp hplus
  have hlogA:=Real.log_le_sub_one_of_pos ha
  have hlogB:=Real.log_le_sub_one_of_pos hb
  have hk:((n - 1:ℕ):ℝ)=(n:ℝ) - 1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have heqA:((n - 1:ℕ):ℝ) * (a - 1)=1 / ((n:ℝ) + 1):=by
    rw [hk]
    dsimp [a]
    field_simp
    ring
  have heqB:2 * (b - 1)=-2 / ((n:ℝ) + 1):=by
    dsimp [b]
    field_simp
    ring
  have hA:=mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (n - 1))
  have hB:=mul_le_mul_of_nonneg_left hlogB (show (0:ℝ)≤ 2 by norm_num)
  rw [heqA] at hA
  rw [heqB] at hB
  change Real.log (a ^ (n - 1) * b ^ 2)≤ _
  rw [Real.log_mul (ne_of_gt (pow_pos ha _)) (ne_of_gt (sq_pos_of_pos hb)),
    Real.log_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _≤ 1 / ((n:ℝ) + 1) + -2 / ((n:ℝ) + 1):=add_le_add hA hB
    _=-1 / ((n:ℝ) + 1):=by ring

open Matrix

theorem enlarged_shrink_bound (n:ℕ) (hn:2≤ n) (δ:ℝ) (hδ:0≤ δ)
    (hδsmall:δ≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):
    (1 + δ) ^ n * Real.sqrt (determinantFactor n)≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hbase:0 < 1 + δ:=by linarith
  have hsqrt:=Real.sqrt_pos.mpr (determinantFactor_pos n hn)
  have hlogbase:Real.log (1 + δ)≤ δ:=by
    simpa using Real.log_le_sub_one_of_pos hbase
  have hlogshrink:Real.log (Real.sqrt (determinantFactor n))≤
      -1 / (2 * ((n:ℝ) + 1)):=by
    rw [Real.log_sqrt (le_of_lt (determinantFactor_pos n hn))]
    calc
      _≤ (-1 / ((n:ℝ) + 1)) / 2:=
        div_le_div_of_nonneg_right (log_determinantFactor_le n hn) (by norm_num)
      _=_:=by field_simp
  have hδmul:(n:ℝ) * δ≤ 1 / (4 * ((n:ℝ) + 1)):=by
    calc
      _≤ (n:ℝ) * (1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hδsmall (le_of_lt hnp)
      _=_:=by field_simp
  have hlogbound:Real.log ((1 + δ) ^ n * Real.sqrt (determinantFactor n))≤
      -1 / (4 * ((n:ℝ) + 1)):=by
    rw [Real.log_mul (ne_of_gt (pow_pos hbase n)) (ne_of_gt hsqrt),Real.log_pow]
    calc
      _≤ (n:ℝ) * δ + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add (mul_le_mul_of_nonneg_left hlogbase (le_of_lt hnp)) hlogshrink
      _≤ 1 / (4 * ((n:ℝ) + 1)) + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add hδmul (le_refl _)
      _=_:=by field_simp; ring
  simpa only [Real.exp_log (mul_pos (pow_pos hbase n) hsqrt)] using
    Real.exp_le_exp.mpr hlogbound

theorem iterated_shrink_bound (n:ℕ) (v:ℕ→ ℝ)
    (hstep:∀ k,v (k + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k)
    (k:ℕ):
    v k≤ Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0:=by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k:=hstep k
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) *
            (Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0):=
          mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
        _=_:=by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring

end Lax109476Proofs.EllipsoidStep

end

section

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

theorem symmetric_form {ι:Type} [Fintype ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (u v:ι→ ℝ):
    u ⬝ᵥ (A *ᵥ v)=v ⬝ᵥ (A *ᵥ u):=by
  have ht:Aᵀ=A:=(Matrix.isHermitian_iff_isSymm.mp hA).eq
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,ht,dotProduct_comm]

theorem quadratic_error_bound {n:ℕ} (E:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (hE:∀ i j, |E i j|≤ ε) (x:Fin n→ ℝ):
    |x ⬝ᵥ (E *ᵥ x)|≤ (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have hcs:(∑ i, |x i|) ^ 2≤ (n:ℝ) * (x ⬝ᵥ x):=by
    have h:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _:Fin n => (1:ℝ)) (fun i => |x i|)
    simpa [dotProduct,sq_abs,pow_two] using h
  calc
    _=|∑ i, ∑ j,x i * E i j * x j|:=by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    _≤ ∑ i, ∑ j, |x i * E i j * x j|:=by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _≤ ∑ i, ∑ j,ε * |x i| * |x j|:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _≤ |x i| * ε * |x j|:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _=_:=by ring
    _=ε * (∑ i, |x i|) ^ 2:=by
      simp only [Finset.mul_sum,Finset.sum_mul,pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤ ε * ((n:ℝ) * (x ⬝ᵥ x)):=mul_le_mul_of_nonneg_left hcs hε
    _=_:=by ring

theorem posDef_of_quadratic_le {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.IsHermitian)
    (hAB:∀ x,x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ (B *ᵥ x)):B.PosDef:=by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB
  intro x hx
  have hpos:0 < x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.dotProduct_mulVec_pos hx
  simpa using hpos.trans_le (hAB x)

theorem inverse_variational_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (x y:ι→ ℝ):
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:A *ᵥ (A⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hnonneg:0≤ (y - A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (y - A⁻¹ *ᵥ x)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (y - A⁻¹ *ᵥ x)
  rw [Matrix.mulVec_sub,hcancel,sub_dotProduct,dotProduct_sub,
    dotProduct_sub,symmetric_form hA.1 (A⁻¹ *ᵥ x) y,hcancel,
    dotProduct_comm y x,dotProduct_comm (A⁻¹ *ᵥ x) x] at hnonneg
  linarith

theorem inverse_quadratic_antitone {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef)
    (hAB:∀ y,y ⬝ᵥ (A *ᵥ y)≤ y ⬝ᵥ (B *ᵥ y)) (x:ι→ ℝ):
    x ⬝ᵥ (B⁻¹ *ᵥ x)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:B *ᵥ (B⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit),Matrix.one_mulVec]
  have hvar:=inverse_variational_bound hA x (B⁻¹ *ᵥ x)
  have hle:=hAB (B⁻¹ *ᵥ x)
  rw [hcancel,dotProduct_comm (B⁻¹ *ᵥ x) x] at hle
  linarith

def realShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ):
    Matrix (Fin n) (Fin n) ℝ:=fun i j => (A i j:ℝ)

theorem enlargement_sandwich {n:ℕ} (A R:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (herr:∀ i j, |R i j - A i j|≤ ε)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)∧
      x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)≤
        x ⬝ᵥ (A *ᵥ x) + 2 * (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have h:=quadratic_error_bound (R - A) ε hε herr x
  rw [Matrix.sub_mulVec,dotProduct_sub] at h
  have hh:=abs_le.mp h
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  constructor <;> linarith [hh.1,hh.2]

theorem roundedShape_sandwich {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape A *ᵥ x)≤ x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)∧
      x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
        x ⬝ᵥ (realShape A *ᵥ x) + (2 * (n:ℝ) / D) * (x ⬝ᵥ x):=by
  let R:Matrix (Fin n) (Fin n) ℝ:=
    fun i j => (RationalRounding.roundDown (A i j) D:ℝ)
  have herr:∀ i j, |R i j - realShape A i j|≤ 1 / (D:ℝ):=by
    intro i j
    have h:=RationalRounding.roundDown_error (A i j) D hD
    dsimp [R,realShape]
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]
  have hid:realShape (roundedShape A D)=R + ((n:ℝ) * (1 / D)) • 1:=by
    ext i j
    change ((RationalRounding.roundDown (A i j) D +
      ((n:ℚ) / D) * (if i=j then 1 else 0):ℚ):ℝ) =
      (RationalRounding.roundDown (A i j) D:ℝ) +
        ((n:ℝ) * (1 / D)) * (if i=j then 1 else 0)
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hid]
  simpa only [mul_one_div] using
    enlargement_sandwich (realShape A) R (1 / D) (by positivity) herr x

theorem roundedShape_isHermitian {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:A.IsSymm) (D:ℕ):(realShape (roundedShape A D)).IsHermitian:=by
  rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
  intro i j
  simp [realShape,roundedShape,hA.apply i j,Matrix.one_apply,eq_comm]

theorem roundedShape_posDef {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape A D)).PosDef:=by
  have hsym:A.IsSymm:=by
    apply Matrix.IsSymm.ext
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    dsimp [realShape] at h
    exact_mod_cast h
  exact posDef_of_quadratic_le hA (roundedShape_isHermitian A hsym D)
    (fun x => (roundedShape_sandwich A D hD x).1)

theorem roundedShape_contains {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ)
    (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1):
    x ⬝ᵥ ((realShape (roundedShape A D))⁻¹ *ᵥ x)≤ 1:=
  (inverse_quadratic_antitone hA (roundedShape_posDef A hA D hD)
    (fun y => (roundedShape_sandwich A D hD y).1) x).trans hx

theorem roundedShape_relative_bound {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (lowerBound η:ℝ) (hη:0≤ η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ η * lowerBound) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
      (1 + η) * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  have hxx:0≤ x ⬝ᵥ x:=by
    simpa using dotProduct_star_self_nonneg x
  have herror:=mul_le_mul_of_nonneg_right hprecision hxx
  have hrelative:=mul_le_mul_of_nonneg_left (hlower x) hη
  have hround:=(roundedShape_sandwich A D hD x).2
  nlinarith only [herror,hrelative,hround]

theorem inverse_smul {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (k:ℝ) (hk:k ≠ 0):
    (k • A)⁻¹=k⁻¹ • A⁻¹:=by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    inv_mul_cancel₀ hk,one_smul]

theorem inverse_form_upper_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x)) (x:ι→ ℝ):
    x ⬝ᵥ (A⁻¹ *ᵥ x)≤ lowerBound⁻¹ * (x ⬝ᵥ x):=by
  have hI:(1:Matrix ι ι ℝ).PosDef:=Matrix.PosDef.one
  have hlI:(lowerBound • (1:Matrix ι ι ℝ)).PosDef:=hI.smul hl
  have horder:∀ y,y ⬝ᵥ ((lowerBound • (1:Matrix ι ι ℝ)) *ᵥ y)≤
      y ⬝ᵥ (A *ᵥ y):=by
    intro y
    simpa only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
      smul_eq_mul] using hbound y
  have h:=inverse_quadratic_antitone hlI hA horder x
  rw [inverse_smul hI lowerBound (ne_of_gt hl)] at h
  simpa only [inv_one,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul] using h

theorem center_displacement_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ (A *ᵥ (x + e))≤ (1 + η) ^ 2:=by
  have hnonneg:0≤ (η • x - e) ⬝ᵥ (A *ᵥ (η • x - e)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (η • x - e)
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    symmetric_form hA.1 e x] at hnonneg
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hA.1 e x]
  have hb₁:=mul_le_mul_of_nonneg_left hx (show 0≤ η ^ 2 + η by positivity)
  have hb₂:=mul_le_mul_of_nonneg_left he (show 0≤ 1 + η by positivity)
  nlinarith only [hnonneg,hb₁,hb₂,hη]

theorem enlargedShape_contains_displaced {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ ((((1 + η) ^ 2) • A)⁻¹ *ᵥ (x + e))≤ 1:=by
  have hk:0 < (1 + η) ^ 2:=by positivity
  rw [inverse_smul hA _ (ne_of_gt hk),Matrix.smul_mulVec,
    dotProduct_smul,smul_eq_mul]
  calc
    _≤ ((1 + η) ^ 2)⁻¹ * (1 + η) ^ 2:=
      mul_le_mul_of_nonneg_left (center_displacement_bound hA.inv η hη x e hx he)
        (inv_nonneg.mpr (le_of_lt hk))
    _=1:=inv_mul_cancel₀ (ne_of_gt hk)

theorem roundedCenter_error {n:ℕ} {A:Matrix (Fin n) (Fin n) ℝ}
    (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x))
    (c:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    let e:Fin n→ ℝ:=fun i => (c i:ℝ) - RationalRounding.roundDown (c i) D
    e ⬝ᵥ (A⁻¹ *ᵥ e)≤ lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2):=by
  dsimp only
  apply (inverse_form_upper_bound hA lowerBound hl hbound _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hl))
  simpa only [dotProduct, ← pow_two] using
    RationalRounding.roundDown_vector_error n c D hD

end Lax109476Proofs.EllipsoidRounding

end

section

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

theorem form_cauchy_schwarz {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (a x:ι→ ℝ) (ha:a ≠ 0):
    (x ⬝ᵥ (A *ᵥ a)) ^ 2≤ (a ⬝ᵥ (A *ᵥ a)) * (x ⬝ᵥ (A *ᵥ x)):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnonneg:0≤ (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (q • x - t • a)
  have hid:(q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) =
      q * (q * (x ⬝ᵥ (A *ᵥ x)) - t ^ 2):=by
    simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
      dotProduct_sub,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.1 a x]
    dsimp [q,t]
    ring
  rw [hid] at hnonneg
  have h:=nonneg_of_mul_nonneg_right hnonneg hq
  change t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x))
  linarith

noncomputable def realCutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ)
    (a:Fin n→ ℝ):Matrix (Fin n) (Fin n) ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) •
    (A - (2 / (((n:ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

theorem realShape_cutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    realShape (cutShape n A a)=realCutShape n (realShape A) (fun i => (a i:ℝ)):=by
  ext i j
  simp [realShape,cutShape,realCutShape,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct,Rat.cast_sum,smul_eq_mul]

theorem realCutShape_sandwich (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2 * (x ⬝ᵥ (A *ᵥ x))≤
      x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
    x ⬝ᵥ (realCutShape n A a *ᵥ x)≤
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hα:0 < α:=by dsimp [α]; apply div_pos <;> nlinarith
  have hβ:0≤ β:=by dsimp [β]; positivity
  have hcs:t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x)):=form_cauchy_schwarz hA a x ha
  have hcs':t ^ 2 / q≤ x ⬝ᵥ (A *ᵥ x):=(div_le_iff₀ hq).mpr (by nlinarith)
  have hterm:0≤ β * (t ^ 2 / q):=by positivity
  have htermUpper:=mul_le_mul_of_nonneg_left hcs' hβ
  have hid:x ⬝ᵥ (realCutShape n A a *ᵥ x) =
      α * ((x ⬝ᵥ (A *ᵥ x)) - β * (t ^ 2 / q)):=by
    simp only [realCutShape,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.vecMulVec_mulVec,dotProduct_smul,dotProduct_sub,
      smul_eq_mul]
    dsimp [α,β,q,t]
    simp only [dotProduct_comm (A *ᵥ a) x,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hfactor:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  rw [hid, ← hfactor]
  constructor
  · have h:=mul_le_mul_of_nonneg_left htermUpper (le_of_lt hα)
    nlinarith only [h]
  · have h:=mul_nonneg (le_of_lt hα) hterm
    nlinarith only [h]

theorem realCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):(realCutShape n A a).PosDef:=by
  have hsym:(realCutShape n A a).IsHermitian:=by
    rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    simp [realCutShape,Matrix.smul_apply,Matrix.sub_apply,Matrix.vecMulVec,
      smul_eq_mul,h,mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by positivity
  have hxx:0 < x ⬝ᵥ (A *ᵥ x):=by simpa using hA.dotProduct_mulVec_pos hx
  simpa using (mul_pos hp hxx).trans_le (realCutShape_sandwich n hn A hA a x ha).1

theorem realCutShape_inverse (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a)⁻¹ =
      (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) •
        (A⁻¹ + (2 / (((n:ℝ) - 1) * (a ⬝ᵥ (A *ᵥ a)))) •
          Matrix.vecMulVec a a):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnzero:(n:ℝ) ≠ 0:=by linarith
  have hminus:(n:ℝ) - 1 ≠ 0:=by linarith
  have hplus:(n:ℝ) + 1 ≠ 0:=by linarith
  have hdiff:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hAA:A * A⁻¹=1:=Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hrow:(A *ᵥ a) ᵥ* A⁻¹=a:=by
    rw [Matrix.vecMul_mulVec, (Matrix.isHermitian_iff_isSymm.mp hA.1).eq,
      hAA,Matrix.vecMul_one]
  have hcross:Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) * Matrix.vecMulVec a a =
      (a ⬝ᵥ (A *ᵥ a)) • Matrix.vecMulVec (A *ᵥ a) a:=by
    rw [Matrix.vecMulVec_mul_vecMulVec,dotProduct_comm]
    ext i j
    simp [Matrix.vecMulVec,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm]
  apply Matrix.inv_eq_right_inv
  unfold realCutShape
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hc:(((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1))=1:=by field_simp
  rw [hc,one_smul]
  simp only [mul_add,sub_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [hAA,hcross,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hrow]
  simp only [smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ring

theorem det_realCutShape (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a).det=A.det * EllipsoidStep.determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:q ≠ 0:=by
    have hp:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hfactor:A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) =
      A * (1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)):=by
    rw [mul_sub,Matrix.mul_one,Matrix.mul_smul,Matrix.mul_vecMulVec]
  have hdet:(1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)).det=1 - β:=by
    have h:=Matrix.det_one_add_replicateCol_mul_replicateRow
      (ι:=Unit) a (-(β / q) • (A *ᵥ a))
    have hd:a ⬝ᵥ (-(β / q) • (A *ᵥ a))=-β:=by
      rw [dotProduct_smul]
      change -(β / q) * q=-β
      field_simp
    have hd':(-(β / q) • (A *ᵥ a)) ⬝ᵥ a=-β:=by
      rw [dotProduct_comm]
      exact hd
    rw [hd'] at h
    simpa [← Matrix.vecMulVec_eq Unit,sub_eq_add_neg,neg_smul] using h
  have hform:realCutShape n A a =
      α • (A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a)):=by
    dsimp [realCutShape,α,β,q]
    congr 2
    congr 1
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [hform,Matrix.det_smul,Fintype.card_fin,hfactor,Matrix.det_mul,hdet]
  have hαβ:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  unfold EllipsoidStep.determinantFactor
  calc
    _=A.det * (α ^ (n - 1) * (α * (1 - β))):=by
      nth_rewrite 1 [show n=(n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    _=_:=by rw [hαβ]

theorem realCutShape_quadratic (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) =
      EllipsoidStep.centralCutForm n (x ⬝ᵥ (A⁻¹ *ᵥ x))
        ((a ⬝ᵥ x) / Real.sqrt q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let s:=1 / (((n:ℝ) + 1) * Real.sqrt q)
  let z:=x + s • (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hzz:z ⬝ᵥ (A⁻¹ *ᵥ z) =
      x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q:=by
    dsimp [z]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,hc,add_dotProduct,
      dotProduct_add,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.inv.1 (A *ᵥ a) x,dotProduct_comm x a,
      dotProduct_comm (A *ᵥ a) a]
    dsimp [q]
    ring
  have haz:a ⬝ᵥ z=a ⬝ᵥ x + s * q:=by
    simp [z,q,dotProduct_add,dotProduct_smul]
  change z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)=_
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    dotProduct_smul,dotProduct_add,smul_eq_mul,dotProduct_comm z a]
  rw [hzz,haz]
  simp only [op_smul_eq_smul,smul_eq_mul]
  change (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
    ((x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q) +
      (2 / (((n:ℝ) - 1) * q)) * (((a ⬝ᵥ x) + s * q) * ((a ⬝ᵥ x) + s * q)))=_
  dsimp [s,EllipsoidStep.centralCutForm]
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  rw [← htsq]
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem realCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1) (hcut:a ⬝ᵥ x≤ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)≤ 1:=by
  dsimp only
  rw [realCutShape_quadratic n hn A hA a x ha]
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hav:A *ᵥ a ≠ 0:=by
    intro h
    have h':=hc
    rw [h,Matrix.mulVec_zero] at h'
    exact ha h'.symm
  have hcs:=form_cauchy_schwarz hA.inv (A *ᵥ a) x hav
  rw [hc,dotProduct_comm x a,dotProduct_comm (A *ᵥ a) a] at hcs
  have hcs':((a ⬝ᵥ x) / Real.sqrt q) ^ 2≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
    rw [div_pow,Real.sq_sqrt (le_of_lt hq)]
    apply (div_le_iff₀ hq).mpr
    simpa [q,mul_comm] using hcs
  have ht:-1≤ (a ⬝ᵥ x) / Real.sqrt q:=by nlinarith
  exact EllipsoidStep.centralCutForm_le_one n _ _ (by exact_mod_cast hn)
    hx ht (div_nonpos_of_nonpos_of_nonneg hcut (le_of_lt hs))

theorem roundedCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape (cutShape n A a) D)).PosDef:=by
  apply roundedShape_posDef _ _ D hD
  rw [realShape_cutShape]
  exact realCutShape_posDef n hn (realShape A) hA _ ha

theorem roundedCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D)
    (x:Fin n→ ℝ) (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1)
    (hcut:(fun i => (a i:ℝ)) ⬝ᵥ x≤ 0):
    let ar:Fin n→ ℝ:=fun i => (a i:ℝ)
    let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (realShape A *ᵥ ar)
    z ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ z)≤ 1:=by
  have hQ:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA _ ha
  apply roundedShape_contains _ hQ D hD
  rw [realShape_cutShape]
  exact realCutShape_contains n hn (realShape A) hA _ x ha hx hcut

theorem realCutShape_coarse_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    (1 / 4:ℝ) * (x ⬝ᵥ (A *ᵥ x))≤ x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
      x ⬝ᵥ (realCutShape n A a *ᵥ x)≤ 2 * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hxx:0≤ x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hp:0 < (n:ℝ) + 1:=by linarith
  have hd:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  have hratio:(1 / 2:ℝ)≤ (n:ℝ) / ((n:ℝ) + 1):=
    (le_div_iff₀ hp).mpr (by linarith)
  have hlo:(1 / 4:ℝ)≤ ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    nlinarith
  have hhi:(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)≤ 2:=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have h:=realCutShape_sandwich n hn A hA a x ha
  exact ⟨(mul_le_mul_of_nonneg_right hlo hxx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hhi hxx)⟩

theorem dyadic_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (2:ℝ) ^ (l + s + n + 1)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hpow:(0:ℝ) < 2 ^ (l + s + n + 1):=by positivity
  apply (div_le_iff₀ hpow).mpr
  simp only [pow_add,pow_one]
  have hl:(2:ℝ) ^ l ≠ 0:=by positivity
  have hs:(2:ℝ) ^ s ≠ 0:=by positivity
  field_simp
  nlinarith

end Lax109476Proofs.EllipsoidBounds

end

section

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

theorem cut_direction_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (A *ᵥ a) ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ (A *ᵥ a)) =
      (((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * (a ⬝ᵥ (A *ᵥ a)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    hc,dotProduct_smul,dotProduct_add,smul_eq_mul,
    op_smul_eq_smul,dotProduct_comm (A *ᵥ a) a]
  field_simp
  ring

theorem center_approximation_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r:ℝ) (hr:0 < r):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e) =
      ((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2:=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hrz:r ≠ 0:=ne_of_gt hr
  dsimp only
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [cut_direction_form n hn A hA a ha]
  change _=((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  change (1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
    ((1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
      ((((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * q))=_
  rw [← htsq]
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem center_approximation_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r ε:ℝ)
    (hr:Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ r)
    (herr:r - Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ ε):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e)≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hrp:0 < r:=hs.trans_le hr
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have ht:0≤ r - Real.sqrt q:=by linarith
  have hε:0≤ ε:=ht.trans herr
  have hsquare:q≤ r ^ 2:=by nlinarith [Real.sq_sqrt (le_of_lt hq)]
  dsimp only
  rw [center_approximation_form n hn A hA a ha r hrp,div_pow,mul_pow]
  change (r - Real.sqrt q) ^ 2 / ((n:ℝ) ^ 2 * r ^ 2)≤ _
  calc
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * r ^ 2):=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=
      div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))

theorem form_add_le_two {ι:Type} [Fintype ι] [DecidableEq ι]
    {B:Matrix ι ι ℝ} (hB:B.PosDef) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (B *ᵥ (u + v))≤
      2 * (u ⬝ᵥ (B *ᵥ u)) + 2 * (v ⬝ᵥ (B *ᵥ v)):=by
  have h:0≤ (u - v) ⬝ᵥ (B *ᵥ (u - v)):=by
    simpa using hB.posSemidef.dotProduct_mulVec_nonneg (u - v)
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,
    symmetric_form hB.1 v u] at h
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hB.1 v u]
  linarith

noncomputable def exactCenter (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ):Fin n→ ℝ:=
  realVector c -
    (1 / (((n:ℝ) + 1) * Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
      (realShape A *ᵥ realVector a)

theorem cast_direction_form (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ)=realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
  simp [dotProduct,Matrix.mulVec,realShape,realVector,Rat.cast_sum]

theorem approximateCenter_difference (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    exactCenter n A a c - realVector (approximateCenter n A a c D) =
      (1 / (((n:ℝ) + 1) * (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ)) -
        1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
        (realShape A *ᵥ realVector a):=by
  ext i
  simp [exactCenter,approximateCenter,realVector,realShape,Matrix.mulVec,
    dotProduct,Rat.cast_sum,smul_eq_mul]
  ring

theorem roundedCenter_total_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound η:ℝ) (hl:0 < lowerBound)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ η ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ η ^ 2 / 4):
    let e:=exactCenter n A a c - realVector (roundedCenter n A a c D)
    e ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ e)≤ η ^ 2:=by
  let ar:=realVector a
  let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
  let Q:=realShape (roundedShape (cutShape n A a) D)
  let e₁:=exactCenter n A a c - realVector (approximateCenter n A a c D)
  let e₂:=realVector (approximateCenter n A a c D) - realVector (roundedCenter n A a c D)
  have hq:0 < q:=by simpa [q,ar] using hA.dotProduct_mulVec_pos ha
  have hqrat:0≤ a ⬝ᵥ (A *ᵥ a):=by
    have hp:(0:ℝ)≤ ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ):=by
      rw [cast_direction_form]
      exact le_of_lt hq
    exact_mod_cast hp
  have hQ:Q.PosDef:=roundedCutShape_posDef n hn A hA a ha D hD
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA ar ha
  have horder:∀ y,y ⬝ᵥ (realShape (cutShape n A a) *ᵥ y)≤ y ⬝ᵥ (Q *ᵥ y):=
    fun y => (roundedShape_sandwich (cutShape n A a) D hD y).1
  have h₁:e₁ ⬝ᵥ (Q⁻¹ *ᵥ e₁)≤ η ^ 2 / 4:=by
    apply (inverse_quadratic_antitone hC hQ horder e₁).trans
    rw [realShape_cutShape]
    obtain ⟨hr,herr⟩:=RationalRounding.sqrtUpper_bounds (a ⬝ᵥ (A *ᵥ a)) hqrat D hD
    rw [cast_direction_form] at hr herr
    have hb:=center_approximation_error n hn (realShape A) hA ar ha
      (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ) (2 / D) hr (by linarith)
    change e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤ _
    have hid:(2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q) =
        4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 * q):=by ring
    have hb':e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤
        (2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q):=by
      dsimp [e₁]
      rw [approximateCenter_difference]
      exact hb
    exact hb'.trans (hid ▸ hsqrt)
  have h₂:e₂ ⬝ᵥ (Q⁻¹ *ᵥ e₂)≤ η ^ 2 / 4:=by
    have h:=roundedCenter_error hQ lowerBound hl hlower (approximateCenter n A a c D) D hD
    exact h.trans hgrid
  have he:exactCenter n A a c - realVector (roundedCenter n A a c D)=e₁ + e₂:=by
    dsimp [e₁,e₂]
    abel
  dsimp only
  rw [he]
  have h:=form_add_le_two hQ.inv e₁ e₂
  linarith

theorem realShape_roundedStepShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (η:ℚ):
    realShape (roundedStepShape n A a D η) =
      ((1 + (η:ℝ)) ^ 2) • realShape (roundedShape (cutShape n A a) D):=by
  ext i j
  simp [realShape,roundedStepShape,Matrix.smul_apply,smul_eq_mul]

theorem roundedStepShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η):(realShape (roundedStepShape n A a D η)).PosDef:=by
  rw [realShape_roundedStepShape]
  apply (roundedCutShape_posDef n hn A hA a ha D hD).smul
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  positivity

theorem roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound:ℝ) (hl:0 < lowerBound) (η:ℚ) (hη:0 < η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ (η:ℝ) ^ 2 / 4)
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  have hQ:=roundedCutShape_posDef n hn A hA a ha D hD
  have he:=roundedCenter_total_error n hn A hA a c ha D hD lowerBound η hl hlower hsqrt hgrid
  have hxe:(x - exactCenter n A a c) ⬝ᵥ
      ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ
        (x - exactCenter n A a c))≤ 1:=by
    have h:=roundedCutShape_contains n hn A hA a ha D hD (x - realVector c) hx hcut
    have hid:x - exactCenter n A a c=x - realVector c +
        (1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
            (realShape A *ᵥ realVector a):=by
      unfold exactCenter
      abel
    rw [hid]
    exact h
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have h:=enlargedShape_contains_displaced hQ η hp
    (x - exactCenter n A a c)
    (exactCenter n A a c - realVector (roundedCenter n A a c D)) hxe he
  rw [realShape_roundedStepShape]
  simpa only [sub_add_sub_cancel] using h

end Lax109476Proofs.EllipsoidCenter

end

section

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

theorem gridDenominator_pos (l s n:ℕ):0 < gridDenominator l s n:=by
  unfold gridDenominator
  positivity

theorem grid_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (gridDenominator l s n:ℝ)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hp:(2:ℝ) ^ (l + s + n + 1)≤ (gridDenominator l s n:ℝ):=by
    unfold gridDenominator
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show l + s + n + 1≤ l + s + n + 3 by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (dyadic_shape_precision l s n)

theorem dyadic_center_precision (l s n:ℕ):
    4 / (((gridDenominator l s n:ℕ):ℝ) ^ 2 * ((2:ℝ) ^ l)⁻¹)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4∧
    (((2:ℝ) ^ l)⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4:=by
  let L:=(2:ℝ) ^ l
  let S:=(2:ℝ) ^ s
  let N:=(2:ℝ) ^ (n + 3)
  have hL:1≤ L:=one_le_pow₀ (by norm_num)
  have hS:0 < S:=by dsimp [S]; positivity
  have hN:8≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    have h:=one_le_pow₀ (show (1:ℝ)≤ 2 by norm_num) (n:=n)
    linarith
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hnN:8 * (n:ℝ)≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    nlinarith
  have hLN:N ^ 2≤ L * N ^ 2:=by
    simpa using mul_le_mul_of_nonneg_right hL (sq_nonneg N)
  have hid:(gridDenominator l s n:ℝ)=L * S * N:=by
    simp only [gridDenominator,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [L,S,N]
    rw [show l + s + n + 3=l + s + (n + 3) by omega,pow_add,pow_add]
  have hLz:L ≠ 0:=by linarith
  have hSz:S ≠ 0:=ne_of_gt hS
  have hNz:N ≠ 0:=by linarith
  change 4 / ((gridDenominator l s n:ℝ) ^ 2 * L⁻¹)≤ (S⁻¹) ^ 2 / 4∧
    (L⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤ (S⁻¹) ^ 2 / 4
  rw [hid,inv_inv]
  constructor
  · field_simp
    nlinarith only [hN,hLN]
  · field_simp
    nlinarith only [hN,hnN,hLN]

theorem exactCut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
  have he:((2:ℝ) ^ (l + 2))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
    rw [pow_add]
    norm_num
  rw [he]
  calc
    _=(1 / 4:ℝ) * (((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)):=by ring
    _≤ (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)):=
      mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
    _≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      rw [realShape_cutShape]
      exact (realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha).1

theorem cut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=
  (exactCut_lower_bound n hn A hA a ha l hbound x).trans
    (roundedShape_sandwich (cutShape n A a) D hD x).1

theorem uniform_roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l s:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    let D:=gridDenominator (l + 2) s n
    let η:ℚ:=1 / (2:ℚ) ^ s
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  let D:=gridDenominator (l + 2) s n
  let η:ℚ:=1 / (2:ℚ) ^ s
  let lowerBound:=((2:ℝ) ^ (l + 2))⁻¹
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hη:0 < η:=by dsimp [η]; positivity
  have hl:0 < lowerBound:=by dsimp [lowerBound]; positivity
  have hcast:(η:ℝ)=((2:ℝ) ^ s)⁻¹:=by simp [η]
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hlower:=cut_lower_bound n hn A hA a ha D hD l hbound
  have hq:lowerBound≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
    have he:lowerBound=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
      dsimp [lowerBound]
      rw [pow_add]
      norm_num
    have hp:0≤ ((2:ℝ) ^ l)⁻¹:=by positivity
    have h:=hbound (realVector a)
    have h':=mul_le_mul_of_nonneg_left hanorm hp
    rw [he]
    nlinarith only [h,h',hp]
  have hprec:=dyadic_center_precision (l + 2) s n
  have hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4:=by
    rw [hcast]
    apply le_trans _ hprec.1
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    have hn₂:1≤ (n:ℝ) ^ 2:=by nlinarith
    have hprod:=mul_le_mul_of_nonneg_left hq (sq_nonneg (D:ℝ))
    have hqp:0≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by linarith
    have h:=mul_le_mul_of_nonneg_right hn₂
      (mul_nonneg (sq_nonneg (D:ℝ)) hqp)
    nlinarith only [hprod,h]
  apply roundedStep_contains n hn A hA a c ha D hD lowerBound hl η hη hlower hsqrt
  · simpa only [hcast] using hprec.2
  · exact hx
  · exact hcut

end Lax109476Proofs.EllipsoidPrecision

end

section

namespace Lax109476Proofs.EllipsoidDeterminant

open Matrix EllipsoidRounding

theorem eigenvalue_le_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)) (i:ι):
    hA.eigenvalues i≤ k:=by
  let v:ι→ ℝ:=(hA.eigenvectorBasis i).ofLp
  have hv:v ≠ 0:=by
    intro h
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun h j
  have hxx:0 < v ⬝ᵥ v:=by
    simpa using (dotProduct_star_self_pos_iff (v:=v)).mpr hv
  have he:A *ᵥ v=hA.eigenvalues i • v:=hA.mulVec_eigenvectorBasis i
  have h:=hbound v
  rw [he,dotProduct_smul,smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hxx).mp h

theorem det_le_pow_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosSemidef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)):
    A.det≤ k ^ Fintype.card ι:=by
  rw [hA.1.det_eq_prod_eigenvalues]
  simpa [RCLike.ofReal_real_eq_id] using Finset.prod_le_prod
    (s:=Finset.univ (α:=ι)) (g:=fun _ => k)
    (fun i _ => hA.eigenvalues_nonneg i)
    (fun i _ => eigenvalue_le_of_form_bound hA.1 k hbound i)

theorem det_le_relative_pow {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (B *ᵥ x)≤ k * (x ⬝ᵥ (A *ᵥ x))):
    B.det≤ k ^ Fintype.card ι * A.det:=by
  open scoped MatrixOrder in
  have hsqrt:∃ R:Matrix ι ι ℝ,R.IsHermitian∧ IsUnit R∧ R * R=A:=by
    let R:=CFC.sqrt A
    have hRR:R * R=A:=by
      simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
    have hu:IsUnit (R * R):=hRR.symm ▸ hA.isUnit
    exact ⟨R, (CFC.sqrt_nonneg A).posSemidef.1,
      isUnit_of_mul_isUnit_left hu,hRR⟩
  obtain ⟨R,hR,hu,hRR⟩:=hsqrt
  have hRinv:R⁻¹.IsHermitian:=hR.inv
  have hRi:IsUnit R⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hu
  have hRRi:R * R⁻¹=1:=Matrix.mul_nonsing_inv R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRiR:R⁻¹ * R=1:=Matrix.nonsing_inv_mul R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  let C:=R⁻¹ * B * R⁻¹
  have hC:C.PosDef:=by
    simpa only [hRinv.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hRi)
  have hid:R⁻¹ * A * R⁻¹=1:=by
    rw [← hRR, ← Matrix.mul_assoc,hRiR,Matrix.one_mul,hRRi]
  have hform (M:Matrix ι ι ℝ) (x:ι→ ℝ):
      x ⬝ᵥ ((R⁻¹ * M * R⁻¹) *ᵥ x) =
        (R⁻¹ *ᵥ x) ⬝ᵥ (M *ᵥ (R⁻¹ *ᵥ x)):=by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact (symmetric_form hRinv x (M *ᵥ (R⁻¹ *ᵥ x))).trans (dotProduct_comm _ _)
  have hb:∀ x,x ⬝ᵥ (C *ᵥ x)≤ k * (x ⬝ᵥ x):=by
    intro x
    have h:=hbound (R⁻¹ *ᵥ x)
    rw [← hform B x, ← hform A x,hid,Matrix.one_mulVec] at h
    exact h
  have hc:=det_le_pow_of_form_bound hC.posSemidef k hb
  have hdet:B.det=C.det * A.det:=by
    dsimp [C]
    rw [Matrix.det_mul,Matrix.det_mul, ← hRR,Matrix.det_mul]
    have hd:R.det * (R⁻¹).det=1:=by
      rw [← Matrix.det_mul,hRRi,Matrix.det_one]
    calc
      _=B.det * (R.det * (R⁻¹).det) ^ 2:=by rw [hd]; ring
      _=_:=by ring
  rw [hdet]
  exact mul_le_mul_of_nonneg_right hc (le_of_lt hA.det_pos)

end Lax109476Proofs.EllipsoidDeterminant

end

section

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant Lax109476.RationalCertificates

theorem stepAccuracy_pos (n:ℕ):0 < stepAccuracy n:=by
  unfold stepAccuracy
  positivity

theorem stepAccuracy_small (n:ℕ) (hn:2≤ n):
    (stepAccuracy n:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < 8 * (n:ℝ) * ((n:ℝ) + 1):=by positivity
  have h₁:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have h₂:(n:ℝ) + 1≤ (2:ℝ) ^ (n + 1):=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n + 1)).le
  have hprod:=mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have he:(2:ℝ) ^ (2 * n + 4)=8 * ((2:ℝ) ^ n * (2:ℝ) ^ (n + 1)):=by
    rw [← pow_add,show 2 * n + 4=(n + (n + 1)) + 3 by omega,pow_add]
    norm_num
    ring
  have hb:8 * (n:ℝ) * ((n:ℝ) + 1)≤ (2:ℝ) ^ (2 * n + 4):=by
    rw [he]
    nlinarith only [hprod]
  simp only [stepAccuracy,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hp hb

theorem storedShape_relative_bound (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (hD:0 < D) (η:ℚ) (hη:0≤ η)
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + (η:ℝ)) ^ 3 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
  have hp:(0:ℝ)≤ η:=by exact_mod_cast hη
  have h:=roundedShape_relative_bound (cutShape n A a) D hD lowerBound η hp hlower hprecision x
  rw [realShape_roundedStepShape]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  calc
    _≤ (1 + (η:ℝ)) ^ 2 *
        ((1 + (η:ℝ)) * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))):=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _=_:=by ring

theorem storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η)
    (hsmall:(η:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)))
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound):
    Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have hη₁:(η:ℝ)≤ 1:=by
    have hh:1 / (8 * (n:ℝ) * ((n:ℝ) + 1))≤ 1:=
      (div_le_one (by positivity)).mpr (by nlinarith)
    exact hsmall.trans hh
  have hscalar:(1 + (η:ℝ)) ^ 3≤ (1 + 2 * (η:ℝ)) ^ 2:=by
    have hsq:(η:ℝ) ^ 2≤ η:=by nlinarith
    have hcube:=mul_le_mul_of_nonneg_left hsq (le_of_lt hp)
    nlinarith only [hcube,hp,sq_nonneg (η:ℝ)]
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hP:=roundedStepShape_posDef n hn A hA a ha D hD η hη
  have hrelative:∀ x,x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + 2 * (η:ℝ)) ^ 2 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
    intro x
    have hnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
    exact (storedShape_relative_bound n A a D hD η (le_of_lt hη) lowerBound hlower hprecision x).trans
      (mul_le_mul_of_nonneg_right hscalar hnonneg)
  have hdet:=det_le_relative_pow hC hP ((1 + 2 * (η:ℝ)) ^ 2) hrelative
  rw [Fintype.card_fin] at hdet
  have hpow:((1 + 2 * (η:ℝ)) ^ 2) ^ n=((1 + 2 * (η:ℝ)) ^ n) ^ 2:=by
    rw [← pow_mul, ← pow_mul,Nat.mul_comm]
  have hsqrt:Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realShape (cutShape n A a)).det:=by
    have h:=Real.sqrt_le_sqrt hdet
    rw [hpow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)] at h
    exact h
  have hδ:2 * (η:ℝ)≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1)):=by
    calc
      _≤ 2 * (1 / (8 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _=_:=by
        simp only [div_eq_mul_inv,_root_.mul_inv_rev]
        norm_num
        ring
  have hshrink:=EllipsoidStep.enlarged_shrink_bound n hn (2 * (η:ℝ))
    (by positivity) hδ
  rw [realShape_cutShape] at hsqrt
  change Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
    (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realCutShape n (realShape A) (realVector a)).det at hsqrt
  rw [det_realCutShape n hn (realShape A) hA (realVector a) ha] at hsqrt
  rw [Real.sqrt_mul (le_of_lt hA.det_pos)] at hsqrt
  calc
    _≤ ((1 + 2 * (η:ℝ)) ^ n * Real.sqrt (EllipsoidStep.determinantFactor n)) *
        Real.sqrt (realShape A).det:=by nlinarith only [hsqrt]
    _≤ _:=mul_le_mul_of_nonneg_right hshrink (Real.sqrt_nonneg _)

theorem uniform_storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)):
    Real.sqrt (realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hprec:=grid_shape_precision (l + 2) (2 * n + 4) n
  have hcast:(stepAccuracy n:ℝ)=((2:ℝ) ^ (2 * n + 4))⁻¹:=by
    simp [stepAccuracy]
  apply storedStep_shrink n hn A hA a ha _ (gridDenominator_pos _ _ _)
    (stepAccuracy n) (stepAccuracy_pos n) (stepAccuracy_small n hn)
    (((2:ℝ) ^ (l + 2))⁻¹) (exactCut_lower_bound n hn A hA a ha l hbound)
  simpa only [hcast] using hprec

theorem uniform_storedStep_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)) (x:Fin n→ ℝ):
    let P:=realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))
    (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤ x ⬝ᵥ (P *ᵥ x)∧
      x ⬝ᵥ (P *ᵥ x)≤ 4 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  let D:=gridDenominator (l + 2) (2 * n + 4) n
  let η:=stepAccuracy n
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hp:(0:ℝ) < η:=by exact_mod_cast stepAccuracy_pos n
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hη:(η:ℝ)≤ 1 / 8:=by
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    apply (stepAccuracy_small n hn).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hR:=roundedCutShape_posDef n hn A hA a ha D hD
  have hnonneg:0≤ x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hcutnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor:1≤ (1 + (η:ℝ)) ^ 2:=by nlinarith
  have hfactorUpper:(1 + (η:ℝ)) ^ 3≤ 2:=by
    calc
      _≤ (9 / 8:ℝ) ^ 3:=pow_le_pow_left₀ (by positivity) (by linarith) 3
      _≤ _:=by norm_num
  have hprec:2 * (n:ℝ) / D≤ (η:ℝ) * ((2:ℝ) ^ (l + 2))⁻¹:=by
    simpa [η,stepAccuracy] using grid_shape_precision (l + 2) (2 * n + 4) n
  have hrelative:=storedShape_relative_bound n A a D hD η (le_of_lt (stepAccuracy_pos n))
    _ (exactCut_lower_bound n hn A hA a ha l hbound) hprec x
  have hcoarse:=realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha
  have hcoarse':(1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)∧
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)≤ 2 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
    rw [realShape_cutShape]
    exact hcoarse
  dsimp only
  constructor
  · apply hcoarse'.1.trans
    apply (roundedShape_sandwich (cutShape n A a) D hD x).1.trans
    rw [realShape_roundedStepShape]
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact le_mul_of_one_le_left hnonneg hfactor
  · apply hrelative.trans
    have h:=mul_le_mul_of_nonneg_right hfactorUpper hcutnonneg
    nlinarith only [h,hcoarse'.2]

end Lax109476Proofs.EllipsoidIteration

end

section

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

def shapes (n:ℕ) (a:ℕ→ Fin n→ ℚ):ℕ→ Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

def centers (n:ℕ) (a:ℕ→ Fin n→ ℚ) (c₀:Fin n→ ℚ):ℕ→ Fin n→ ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

theorem shapes_invariant (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    (realShape (shapes n a k)).PosDef∧
    ∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)≤ (4:ℝ) ^ k * (x ⬝ᵥ x):=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      rw [hid]
      exact ⟨Matrix.PosDef.one,by simp⟩
  | succ k ih =>
      have hne:realVector (a k) ≠ 0:=by
        intro h
        have hh:=ha k
        rw [h,dotProduct_zero] at hh
        norm_num at hh
      constructor
      · exact roundedStepShape_posDef n hn _ ih.1 _ hne _
          (gridDenominator_pos _ _ _) _ (stepAccuracy_pos n)
      · intro x
        have hs:=uniform_storedStep_bounds n hn (shapes n a k) ih.1 (a k) (ha k)
          (2 * k) (fun y => (ih.2 y).1) x
        have he:((2:ℝ) ^ (2 * (k + 1)))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ (2 * k))⁻¹:=by
          rw [show 2 * (k + 1)=2 * k + 2 by omega,pow_add]
          norm_num
        constructor
        · rw [he]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).1 (show (0:ℝ)≤ 1 / 4 by norm_num)
          change _≤ x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)
          nlinarith only [hh,hs.1]
        · change x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)≤ _
          rw [pow_succ]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).2 (show (0:ℝ)≤ 4 by norm_num)
          nlinarith only [hh,hs.2]

theorem shapes_shrink (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    Real.sqrt (realShape (shapes n a k)).det≤
      Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))):=by
  let v:=fun j => Real.sqrt (realShape (shapes n a j)).det
  have hstep:∀ j,v (j + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v j:=by
    intro j
    have hi:=shapes_invariant n hn a ha j
    exact uniform_storedStep_shrink n hn (shapes n a j) hi.1 (a j) (ha j)
      (2 * j) (fun x => (hi.2 x).1)
  have h:=EllipsoidStep.iterated_shrink_bound n v hstep k
  have hid:realShape (shapes n a 0)=1:=by
    ext i j
    simp [shapes,realShape,Matrix.one_apply,apply_ite]
  simpa only [v,hid,Matrix.det_one,Real.sqrt_one,mul_one] using h

theorem preserves_points_up_to (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (x:Fin n→ ℝ) (hx:(x - realVector c₀) ⬝ᵥ (x - realVector c₀)≤ 1)
    (k:ℕ)
    (hcut:∀ j < k,realVector (a j) ⬝ᵥ (x - realVector (centers n a c₀ j))≤ 0):
    (x - realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x - realVector (centers n a c₀ k)))≤ 1:=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      simpa only [centers,hid,inv_one,Matrix.one_mulVec] using hx
  | succ k ih =>
      have hi:=shapes_invariant n hn a ha k
      exact uniform_roundedStep_contains n hn (shapes n a k) hi.1 (a k) (centers n a c₀ k)
        (ha k) (2 * k) (2 * n + 4) (fun y => (hi.2 y).1) x
        (ih (fun j hj => hcut j (by omega))) (hcut k (by omega))

theorem shapes_below_threshold (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (B:ℕ):
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det <
      (((2:ℝ) ^ B)⁻¹) ^ n:=by
  have htarget:0 < (((2:ℝ) ^ B)⁻¹) ^ n:=by positivity
  have hlog:Real.log (2:ℝ)≤ 1:=by
    have h:=Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlogtarget:Real.log ((((2:ℝ) ^ B)⁻¹) ^ n) =
      -((B * n:ℕ):ℝ) * Real.log 2:=by
    rw [Real.log_pow,Real.log_inv,Real.log_pow]
    push_cast
    ring
  have he:-(thresholdSteps n B:ℝ) / (4 * ((n:ℝ) + 1)) =
      -(((B * n:ℕ):ℝ) + 1):=by
    have hp:(n:ℝ) + 1 ≠ 0:=by positivity
    unfold thresholdSteps
    push_cast
    field_simp
  have hlt:-(((B * n:ℕ):ℝ) + 1) < -((B * n:ℕ):ℝ) * Real.log 2:=by
    have h:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (B * n))
    linarith
  have h:=shapes_shrink n hn a ha (thresholdSteps n B)
  rw [he] at h
  apply h.trans_lt
  rw [← Real.exp_log htarget,hlogtarget]
  exact Real.exp_lt_exp.mpr hlt

end Lax109476Proofs.EllipsoidSequence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι:Type} [Fintype ι] [DecidableEq ι]

theorem quadratic_parallelogram (A:Matrix ι ι ℝ) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)):=by
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub]
  ring

theorem inverse_form_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    ∀ u:ι→ ℝ,u ⬝ᵥ (A⁻¹ *ᵥ u)≤ (r ^ 2)⁻¹ * (u ⬝ᵥ u):=by
  intro u
  by_cases hu:u=0
  · simp [hu]
  have hnorm:0 < u ⬝ᵥ u:=by
    simpa using (dotProduct_star_self_pos_iff (v:=u)).mpr hu
  let t:=r / Real.sqrt (u ⬝ᵥ u)
  let e:=t • u
  have ht:0 < t:=div_pos hr (Real.sqrt_pos.mpr hnorm)
  have hsq:(Real.sqrt (u ⬝ᵥ u)) ^ 2=u ⬝ᵥ u:=Real.sq_sqrt hnorm.le
  have he:e ⬝ᵥ e=r ^ 2:=by
    simp only [e,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    dsimp [t]
    field_simp
    nlinarith
  have hp:=hball e he.le
  have hm:=hball (-e) (by simpa using he.le)
  have hbase:0≤ (z - c) ⬝ᵥ (A⁻¹ *ᵥ (z - c)):=
    hA.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hid:=quadratic_parallelogram A⁻¹ (z - c) e
  have hp':((z - c) + e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) + e))≤ 1:=by
    have heq:(z - c) + e=z + e - c:=by abel_nf
    rw [heq]
    exact hp
  have hm':((z - c) - e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) - e))≤ 1:=by
    have heq:(z - c) - e=z + -e - c:=by abel_nf
    rw [heq]
    exact hm
  have hqe:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ 1:=by linarith
  have hqe':t ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ 1:=by
    simpa only [e,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,
      smul_eq_mul, ← mul_assoc, ← pow_two] using hqe
  have htform:t ^ 2=r ^ 2 / (u ⬝ᵥ u):=by
    dsimp [t]
    rw [div_pow,hsq]
  rw [htform,div_mul_eq_mul_div] at hqe'
  have hscale:r ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ u ⬝ᵥ u:=
    (div_le_one hnorm).mp hqe'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hscale)

theorem sqrt_det_lower_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    r ^ Fintype.card ι≤ Real.sqrt A.det:=by
  have hbound:=inverse_form_bound_of_ball hA z c r hr hball
  have hdet:=det_le_pow_of_form_bound hA.inv.posSemidef ((r ^ 2)⁻¹) hbound
  rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_pow] at hdet
  have ha:=hA.det_pos
  have hrpow:0 < (r ^ 2) ^ Fintype.card ι:=pow_pos (sq_pos_of_pos hr) _
  have hd:(r ^ 2) ^ Fintype.card ι≤ A.det:=(inv_le_inv₀ ha hrpow).mp hdet
  have hs:=Real.sq_sqrt ha.le
  have hsr:=Real.sqrt_nonneg A.det
  have hrr:(r ^ Fintype.card ι) ^ 2=(r ^ 2) ^ Fintype.card ι:=by ring
  nlinarith [pow_nonneg hr.le (Fintype.card ι)]

end Lax109476Proofs.EllipsoidBall

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidTermination

open Lax109476.RationalCertificates
open EllipsoidRounding EllipsoidSequence EllipsoidBall

theorem cannot_retain_ball (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (z:Fin n→ ℝ) (B:ℕ)
    (hunit:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector c₀) ⬝ᵥ (z + e - realVector c₀)≤ 1):
    ¬ ∀ k < thresholdSteps n B, ∀ e:Fin n→ ℝ,
      e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      realVector (a k) ⬝ᵥ (z + e - realVector (centers n a c₀ k))≤ 0:=by
  intro hcut
  let K:=thresholdSteps n B
  have hshape:=(shapes_invariant n hn a ha K).1
  have hball:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector (centers n a c₀ K)) ⬝ᵥ
        ((realShape (shapes n a K))⁻¹ *ᵥ (z + e - realVector (centers n a c₀ K)))≤ 1:=by
    intro e he
    exact preserves_points_up_to n hn a ha c₀ (z + e) (hunit e he) K
      (fun j hj => hcut j hj e he)
  have hlo:=sqrt_det_lower_bound_of_ball hshape z (realVector (centers n a c₀ K))
    (((2:ℝ) ^ B)⁻¹) (by positivity) hball
  have hhi:=shapes_below_threshold n hn a ha B
  simp only [Fintype.card_fin] at hlo
  exact (not_lt_of_ge hlo) hhi

end Lax109476Proofs.EllipsoidTermination

end

section

namespace Lax455465Proofs.LpCertificateParser

open Lax109476.RationalEncoding Lax109476.RationalCertificates

def value (sign num den:ℕ):ℚ:=
  if sign=1 then -(num:ℚ) / den else (num:ℚ) / den

def rational:List ℕ→ Option (ℚ × List ℕ)
  | sign::num::den::rest => some (value sign num den,rest)
  | _ => none

def vector:ℕ→ List ℕ→ Option (List ℚ × List ℕ)
  | 0,input => some ([],input)
  | n + 1,input => (rational input).bind fun qr =>
      (vector n qr.2).map fun tail => (qr.1::tail.1,tail.2)

private theorem signed_num (z:ℤ):
    (if z < 0 then -((z.natAbs:ℕ):ℚ) else ((z.natAbs:ℕ):ℚ))=(z:ℚ):=by
  cases z <;> simp

theorem rational_encode (q:ℚ) (tail:List ℕ):
    rational (encodeRational q ++ tail)=some (q,tail):=by
  unfold encodeRational
  simp only [List.cons_append,List.nil_append,rational,value]
  have hsign:=signed_num q.num
  by_cases h:q.num < 0
  · simp only [if_pos h] at hsign ⊢
    rw [hsign,q.num_div_den]
    simp only [if_true]
  · simp only [if_neg h,show ¬(0:ℕ)=1 by decide,if_false] at hsign ⊢
    rw [hsign,q.num_div_den]

theorem vector_encode (qs:List ℚ) (tail:List ℕ):
    vector qs.length (qs.flatMap encodeRational ++ tail)=some (qs,tail):=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,vector,
      rational_encode,Option.bind_some,ih,Option.map_some]

def vectorFunction (n:ℕ) (input:List ℕ):Option ((Fin n→ ℚ) × List ℕ):=
  (vector n input).map fun result => (fun i => result.1.getD i.val 0,result.2)

theorem vectorFunction_encode {n:ℕ} (x:Fin n→ ℚ) (tail:List ℕ):
    vectorFunction n (encodeVector x ++ tail)=some (x,tail):=by
  have h:=vector_encode (List.ofFn x) tail
  simp only [List.length_ofFn] at h
  simp only [vectorFunction,encodeVector,h,Option.map_some]
  congr 2
  funext i
  simp [List.getD_eq_getElem?_getD,i.isLt]

def certificate (m n:ℕ):List ℕ→ Option (Certificate m n × List ℕ)
  | 0::rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction m zr.2).map fun yr => (.optimal zr.1 yr.1,yr.2)
  | 1::rest => (vectorFunction m rest).map fun yr => (.infeasible yr.1,yr.2)
  | 2::rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction n zr.2).map fun dr => (.unbounded zr.1 dr.1,dr.2)
  | _ => none

theorem certificate_encode {m n:ℕ} (c:Certificate m n) (tail:List ℕ):
    certificate m n (encodeCertificate c ++ tail)=some (c,tail):=by
  cases c <;> simp only [encodeCertificate,List.cons_append,List.nil_append,
    List.append_assoc,certificate,vectorFunction_encode,Option.bind_some,Option.map_some]

end Lax455465Proofs.LpCertificateParser

end

section

namespace Lax263307Proofs.RegisteredLP

open Lax263307.RegisteredLP
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

theorem vector_eq (n:ℕ) (input:List ℕ):
    vector n input=Lax455465Proofs.LpCertificateParser.vector n input:=by
  induction n generalizing input with
  | zero => rfl
  | succ n ih =>
    simp only [vector,Lax455465Proofs.LpCertificateParser.vector,ih]
    rfl

theorem vectorFunction_eq (n:ℕ) (input:List ℕ):
    vectorFunction n input=Lax455465Proofs.LpCertificateParser.vectorFunction n input:=by
  simp only [vectorFunction,Lax455465Proofs.LpCertificateParser.vectorFunction,vector_eq]

theorem parse_eq (m n:ℕ) (input:List ℕ):
    parse m n input=Lax455465Proofs.LpCertificateParser.certificate m n input:=by
  cases input with
  | nil => rfl
  | cons tag rest =>
    rcases tag with _ | (_ | (_ | tag)) <;>
      simp only [parse,Lax455465Proofs.LpCertificateParser.certificate,vectorFunction_eq]

theorem parse_encode {m n:ℕ} (c:Certificate m n) (tail:List ℕ):
    parse m n (encodeCertificate c ++ tail)=some (c,tail):=by
  rw [parse_eq]
  exact Lax455465Proofs.LpCertificateParser.certificate_encode c tail

end Lax263307Proofs.RegisteredLP

end

section

namespace Lax263307Proofs.NativeEncodedLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.RegisteredLP

theorem certificate_eq {m n:ℕ} (solve:List ℕ→ List ℕ) (P:Program ℚ m n)
    (c:Certificate m n) (hc:solve (encodeProgram P)=encodeCertificate c):
    certificate solve P=c:=by
  have hparse:parse m n (encodeCertificate c)=some (c,[]):=by
    simpa only [List.append_nil] using Lax263307Proofs.RegisteredLP.parse_encode c []
  simp only [certificate,hc,hparse,Option.map_some,Option.getD_some]

theorem exists_solver:∃ solve:List ℕ→ List ℕ,
    Lax759944.RamPolytime.RamPolytime solve∧ Encoded solve:=by
  obtain ⟨solve,hpoly,hsolve⟩:=Lax109476Proofs.RamUniformSolver.exists_exact_polynomial_time_solver
  refine ⟨solve,hpoly,?_⟩
  intro m n P
  obtain ⟨c,hencoded,hvalid⟩:=hsolve m n P
  rw [certificate_eq solve P c hencoded]
  exact ⟨hencoded,hvalid⟩

end Lax263307Proofs.NativeEncodedLP

end

section

namespace Lax263307Proofs.ExhaustiveTargets

open Lax263307.ExhaustiveTargets

theorem candidate_complete (n k:ℕ) (I:Finset (Fin n)):
    I∈ candidates n k↔ I.card=k:=by
  constructor
  · intro hI
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hI
    obtain ⟨hsub,hlen⟩:=List.mem_sublistsLen.mp hl
    rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)),hlen]
  · intro hI
    let l:=(List.finRange n).filter fun v => decide (v∈ I)
    have hsub:List.Sublist l (List.finRange n):=List.filter_sublist
    have hnodup:l.Nodup:=hsub.nodup (List.nodup_finRange n)
    have heq:l.toFinset=I:=by ext v; simp [l]
    have hlen:l.length=k:=by rw [← List.toFinset_card_of_nodup hnodup,heq,hI]
    exact List.mem_map.mpr ⟨l,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,heq⟩

theorem search_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ):
    match findIndependentSet G k with
    | some I => G.IsIndepSet (I:Set (Fin n))∧ I.card=k
    | none => ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k:=by
  cases hsearch:findIndependentSet G k with
  | some I =>
    have hI:G.IsIndepSet (I:Set (Fin n)):=by
      simpa using List.find?_some hsearch
    exact ⟨hI, (Lax263307Proofs.ExhaustiveTargets.candidate_complete n k I).mp
      (List.mem_of_find?_eq_some hsearch)⟩
  | none =>
    intro J hJ
    by_contra hlarge
    obtain ⟨I,hIJ,hcard⟩:=Finset.exists_subset_card_eq (Nat.le_of_not_gt hlarge)
    have hI:G.IsIndepSet (I:Set (Fin n)):=hJ.mono (by simpa using hIJ)
    have hmem:=(Lax263307Proofs.ExhaustiveTargets.candidate_complete n k I).mpr hcard
    have hnone:=List.find?_eq_none.mp hsearch I hmem
    simp [hI] at hnone

end Lax263307Proofs.ExhaustiveTargets

end

section

namespace Lax263307Proofs.TargetSearch

open Lax263307.TargetSearch

theorem search_invariants {n:ℕ} (G:SimpleGraph (Fin n)) (ρ:ℝ)
    (attempt:ℕ→ Option (Finset (Fin n))) (N:ℕ)
    (success:∀ k,k≤ N→ ∀ I,attempt k=some I→
      G.IsIndepSet (I:Set (Fin n))∧ ρ * k≤ I.card)
    (failure:∀ k,0 < k→ k≤ N→ attempt k=none→
      ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k)
    (k:ℕ) (hk:k≤ N)
    (upper:∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card≤ k):
    let result:=search attempt k
    G.IsIndepSet (result.1:Set (Fin n))∧
      (∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card≤ result.2)∧
      result.2≤ k∧ ρ * result.2≤ result.1.card:=by
  induction k with
  | zero =>
    simp only [search,mul_zero,Finset.card_empty,Nat.cast_zero,le_refl,and_true]
    exact ⟨by intro a ha; simp at ha,upper⟩
  | succ k ih =>
    cases he:attempt (k + 1) with
    | some I =>
      obtain ⟨hI,hsize⟩:=success _ hk I he
      simp only [search,he]
      exact ⟨hI,upper,le_rfl,hsize⟩
    | none =>
      have upper':∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card≤ k:=by
        intro J hJ
        exact Nat.le_of_lt_succ (failure _ (by omega) hk he J hJ)
      obtain ⟨hI,hu,hk',hsize⟩:=ih (by omega) upper'
      simp only [search,he]
      exact ⟨hI,hu,hk'.trans (Nat.le_succ k),hsize⟩

theorem search_correct {n:ℕ} (G:SimpleGraph (Fin n)) (ρ:ℝ)
    (attempt:ℕ→ Option (Finset (Fin n)))
    (success:∀ k,k≤ n→ ∀ I,attempt k=some I→
      G.IsIndepSet (I:Set (Fin n))∧ ρ * k≤ I.card)
    (failure:∀ k,0 < k→ k≤ n→ attempt k=none→
      ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k):
    let result:=search attempt n
    G.IsIndepSet (result.1:Set (Fin n))∧
      (∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card≤ result.2)∧
      result.2≤ n∧ ρ * result.2≤ result.1.card:=by
  apply search_invariants G ρ attempt n success failure n le_rfl
  intro J _
  simpa using Finset.card_le_univ J

end Lax263307Proofs.TargetSearch

end

section

namespace Lax920634.EdgeExpansion

def IsSubcubic {V:Type} [Finite V] (G:SimpleGraph V):Prop:=
  ∀ v, (G.neighborSet v).ncard≤ 3

end Lax920634.EdgeExpansion

end

section

namespace Lax263307.WidthGrowth

def threshold (a A c:ℕ):ℕ:=(12 * c) ^ a * A * (6 * (24 * c) ^ 2 + 1) ^ (a - 1)

end Lax263307.WidthGrowth

end

section

namespace Lax263307.CutTraces

open RepeatedCutAccounting (cost)
open SeparatorComponents EdgeSublinearSeparators

structure Trace {n:ℕ} (G:SimpleGraph (Fin n)) (start:Finset (Fin n)) (steps:ℕ) where
  remaining:ℕ→ Finset (Fin n)
  left:ℕ→ Finset (Fin n)
  right:ℕ→ Finset (Fin n)
  initial:remaining 0=start
  cover:∀ i < steps,left i ∪ right i=remaining i
  next:∀ i < steps,remaining (i + 1)=left i \ right i
  nonempty:∀ i < steps, (right i).Nonempty
  small_piece:∀ i < steps,2 * (right i \ left i).card≤ (remaining i).card
  separated:∀ i < steps, ∀ u∈ left i \ right i, ∀ v∈ right i \ left i, ¬G.Adj u v

noncomputable def separator {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q):Finset (Fin n):=Finset.univ.biUnion fun i:Fin q => T.left i ∩ T.right i

def parts {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q):Option (Fin q)→ Finset (Fin n)
  | none => T.remaining q
  | some i => T.right i \ T.left i

end Lax263307.CutTraces

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax263307.RoundedOracleSearch

open BufferedEllipsoid (scale)
open Lax109476.RationalEncoding (encodeRational)
open Lax759944.BinaryWordEncoding (bitSize)
open Matrix

def normalSchedule {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (k:ℕ):Fin n→ ℤ:=
  selectedNormal (oracle k (trajectory oracle k).2)

end Lax263307.RoundedOracleSearch

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

namespace Lax263307.ProjectedOracle

open BufferedEllipsoid (scale)
open ComponentCutEncoding (coefficient)
open DistanceProjection (distanceProgram)
open MomentLP (Index decode dimension encode program)
open RationalCutBuffer (integerNormal)
open RationalProjection (classify)
open RegisteredLP (certificate)
open RoundedOracleSearch (Reply rationalNormal)
open LinearRelaxation AlgorithmParameters

def SearchCorrect {n:ℕ} (G:SimpleGraph (Fin n)) (k h D:ℕ):Option (Finset (Fin n))→ Prop
  | some I => Good G k h D I
  | none => IsIndependenceBound G Finset.univ (k-1)

end Lax263307.ProjectedOracle

end

section

namespace Lax263307.RecursiveAlgorithm

open ExhaustiveTargets (findIndependentSet)
open RecursionDepth (depth)
open ComputedSeparators AlgorithmParameters

def Correct {n:ℕ} (G:SimpleGraph (Fin n)) (k fuel D:ℕ):Option (Finset (Fin n))→ Prop
  | some I => G.IsIndepSet (I:Set (Fin n))∧ (1 - 4*(1/(D:ℝ)))^fuel * (k:ℝ)≤ I.card
  | none => ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k

end Lax263307.RecursiveAlgorithm

end

section

namespace Lax263307Proofs.BalancedPartitions

open Lax263307.SeparatorComponents Lax263307.EdgeSublinearSeparators

theorem walk_stays {n:ℕ} {G:SimpleGraph (Fin n)} {S:Finset (Fin n)} {ι:Type}
    (P:Partition G S ι) (i:ι) {u v:↥((↑S:Set (Fin n))ᶜ)}
    (walk:(G.induce (↑S:Set (Fin n))ᶜ).Walk u v) (hu:u.val∈ P.vertices i):
    v.val∈ P.vertices i:=by
  induction walk with
  | nil => exact hu
  | @cons a b c hab rest ih =>
    apply ih
    exact P.closed i a.val b.val hu b.property hab

theorem balanced_separator {n:ℕ} (G:SimpleGraph (Fin n)) (S:Finset (Fin n))
    {ι:Type} (P:Partition G S ι) (balanced:∀ i,3 * (P.vertices i).card≤ 2 * n):
    IsBalancedSeparator G S:=by
  classical
  intro K
  obtain ⟨u,hu⟩:=K.nonempty_supp
  obtain ⟨i,hi,_⟩:=P.unique u.val u.property
  have hsubset:Subtype.val '' K.supp ⊆ (↑(P.vertices i):Set (Fin n)):=by
    rintro v ⟨w,hw,rfl⟩
    exact walk_stays P i (K.reachable_of_mem_supp hu hw).some hi
  have hcard:K.supp.ncard≤ (P.vertices i).card:=by
    have h:=Set.ncard_mono hsubset
    rw [Set.ncard_image_of_injective K.supp Subtype.val_injective,Set.ncard_coe_finset] at h
    exact h
  exact (Nat.mul_le_mul_left 3 hcard).trans (balanced i)

end Lax263307Proofs.BalancedPartitions

end

section

namespace Lax263307Proofs.RepeatedCutAccounting

open Lax263307.RepeatedCutAccounting

theorem disjoint_shore_card {n q:ℕ} (B:Fin q→ Finset (Fin n))
    (disjoint:Pairwise fun i j => Disjoint (B i) (B j)):(∑ i, (B i).card)≤ n:=by
  classical
  have hd:(↑(Finset.univ:Finset (Fin q)):Set (Fin q)).PairwiseDisjoint B:=by
    intro i _ j _ hij
    exact disjoint hij
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ (Finset.univ.biUnion B)

theorem cost_union_le_sum {n q:ℕ} (x:Fin n→ ℝ) (nonnegative:∀ v,0≤ x v)
    (S:Fin q→ Finset (Fin n)):cost x (Finset.univ.biUnion S)≤ ∑ i,cost x (S i):=by
  classical
  have hterm (v:Fin n):(if v∈ Finset.univ.biUnion S then x v else 0)≤
      ∑ i,if v∈ S i then x v else 0:=by
    by_cases h:v∈ Finset.univ.biUnion S
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp h
      rw [if_pos h]
      have hs:=Finset.single_le_sum (f:=fun i => if v∈ S i then x v else 0)
        (fun i _ => by split_ifs <;> first | exact nonnegative v | exact le_refl 0) (Finset.mem_univ i)
      simpa only [if_pos hi] using hs
    · rw [if_neg h]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact nonnegative v | exact le_refl 0
  calc
    _=∑ v:Fin n,if v∈ Finset.univ.biUnion S then x v else 0:=by simp only [cost,Finset.sum_ite_mem,Finset.univ_inter]
    _≤ ∑ v:Fin n, ∑ i,if v∈ S i then x v else 0:=Finset.sum_le_sum fun v _ => hterm v
    _=∑ i, ∑ v:Fin n,if v∈ S i then x v else 0:=Finset.sum_comm
    _=_:=by simp only [cost,Finset.sum_ite_mem,Finset.univ_inter]

theorem total_cut_cost {n q:ℕ} (x:Fin n→ ℝ) (nonnegative:∀ v,0≤ x v)
    (A B:Fin q→ Finset (Fin n)) (disjoint:Pairwise fun i j => Disjoint (B i) (B j))
    (ρ γ:ℝ) (rho_nonnegative:0≤ ρ) (gamma_positive:0 < γ)
    (each_cut:∀ i,cost x (A i ∩ B i)≤ 4 * ρ * (A i).card * (B i).card / γ):
    cost x (Finset.univ.biUnion fun i => A i ∩ B i)≤ 4 * ρ * (n:ℝ) ^ 2 / γ:=by
  classical
  have hcoef:0≤ 4 * ρ * (n:ℝ) / γ:=by positivity
  have hsum:(∑ i, ((B i).card:ℝ))≤ n:=by exact_mod_cast disjoint_shore_card B disjoint
  have hA (i:Fin q):((A i).card:ℝ)≤ n:=by
    exact_mod_cast (show (A i).card≤ n by simpa using Finset.card_le_univ (A i))
  calc
    _≤ ∑ i,cost x (A i ∩ B i):=cost_union_le_sum x nonnegative _
    _≤ ∑ i, (4 * ρ * (n:ℝ) / γ) * (B i).card:=by
      apply Finset.sum_le_sum
      intro i _
      apply (each_cut i).trans
      have h:=mul_le_mul_of_nonneg_left (hA i) (show 0≤ 4 * ρ * ((B i).card:ℝ) / γ by positivity)
      convert h using 1 <;> ring
    _=(4 * ρ * (n:ℝ) / γ) * (∑ i, ((B i).card:ℝ)):=(Finset.mul_sum _ _ _).symm
    _≤ (4 * ρ * (n:ℝ) / γ) * n:=mul_le_mul_of_nonneg_left hsum hcoef
    _=_:=by ring

end Lax263307Proofs.RepeatedCutAccounting

end

section

namespace Lax263307Proofs.CutTraces

open Lax263307.SeparatorComponents Lax263307.EdgeSublinearSeparators Lax263307.CutTraces

theorem right_subset {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (i:ℕ) (hi:i < q):T.right i ⊆ T.remaining i:=by
  rw [← T.cover i hi]
  exact Finset.subset_union_right

theorem next_sdiff {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (i:ℕ) (hi:i < q):T.remaining (i + 1)=T.remaining i \ T.right i:=by
  rw [T.next i hi, ← T.cover i hi]
  ext v
  simp only [Finset.mem_sdiff,Finset.mem_union]
  tauto

theorem remaining_formula {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (j:ℕ) (hj:j≤ q):
    T.remaining j=start \ (Finset.range j).biUnion T.right:=by
  revert hj
  induction j with
  | zero => intro _; simp [T.initial]
  | succ j ih =>
    intro hj
    rw [next_sdiff T j (by omega),ih (by omega),Finset.range_add_one,Finset.biUnion_insert]
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto

theorem remaining_mono {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (i j:ℕ) (hij:i≤ j) (hj:j≤ q):
    T.remaining j ⊆ T.remaining i:=by
  rw [remaining_formula T j hj,remaining_formula T i (by omega)]
  intro v hv
  have hv:=Finset.mem_sdiff.mp hv
  apply Finset.mem_sdiff.mpr
  refine ⟨hv.1, ?_⟩
  intro hi
  obtain ⟨k,hk,hkv⟩:=Finset.mem_biUnion.mp hi
  exact hv.2 (Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hk) hij),hkv⟩)

theorem right_pairwise {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q):Pairwise fun i j:Fin q => Disjoint (T.right i) (T.right j):=by
  have earlier (i j:Fin q) (hij:i.val < j.val):Disjoint (T.right i) (T.right j):=by
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hv:=remaining_mono T (i.val + 1) j.val (by omega) j.isLt.le
      (right_subset T j j.isLt hvj)
    rw [next_sdiff T i i.isLt] at hv
    exact (Finset.mem_sdiff.mp hv).2 hvi
  intro i j hne
  have hv:i.val ≠ j.val:=by intro h; exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hij | hji
  · exact earlier i j hij
  · exact (earlier j i hji).symm

theorem step_bound {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q):q≤ start.card:=by
  have hcard:∀ j≤ q,j + (T.remaining j).card≤ start.card:=by
    intro j
    induction j with
    | zero => intro _; simp [T.initial]
    | succ j ih =>
      intro hj
      have hprev:=ih (by omega)
      have hB:0 < (T.right j).card:=Finset.card_pos.mpr (T.nonempty j (by omega))
      have hsum:=Finset.card_sdiff_add_card_eq_card (right_subset T j (by omega))
      rw [← next_sdiff T j (by omega)] at hsum
      omega
  have h:=hcard q (le_refl _)
  omega

theorem final_disjoint {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (i:Fin q):Disjoint (T.remaining q) (T.right i):=by
  apply Finset.disjoint_left.mpr
  intro v hv hvi
  have h:=remaining_mono T (i.val + 1) q (by omega) (le_refl _) hv
  rw [next_sdiff T i i.isLt] at h
  exact (Finset.mem_sdiff.mp h).2 hvi

theorem parts_outside {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (i:Option (Fin q)) (v:Fin n) (hv:v∈ parts T i):v∉ separator T:=by
  classical
  intro hs
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hs
  have hjB:=(Finset.mem_inter.mp hj).2
  cases i with
  | none => exact Finset.disjoint_left.mp (final_disjoint T j) hv hjB
  | some i =>
    have hi:=Finset.mem_sdiff.mp hv
    by_cases he:i=j
    · subst j
      exact hi.2 (Finset.mem_inter.mp hj).1
    · exact Finset.disjoint_left.mp (right_pairwise T he) hi.1 hjB

theorem parts_unique {n q:ℕ} {G:SimpleGraph (Fin n)}
    (T:Trace G Finset.univ q) (v:Fin n) (hs:v∉ separator T):
    ∃! i,v∈ parts T i:=by
  classical
  by_cases hex:∃ i:Fin q,v∈ T.right i
  · obtain ⟨i,hi⟩:=hex
    have hnotA:v∉ T.left i:=by
      intro hv
      exact hs (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_inter.mpr ⟨hv,hi⟩⟩)
    refine ⟨some i,Finset.mem_sdiff.mpr ⟨hi,hnotA⟩, ?_⟩
    intro j hj
    cases j with
    | none => exact (Finset.disjoint_left.mp (final_disjoint T i) hj hi).elim
    | some j =>
      have hji:j=i:=by
        by_contra h
        exact Finset.disjoint_left.mp (right_pairwise T h) (Finset.mem_sdiff.mp hj).1 hi
      exact congrArg some hji
  · have hv:v∈ T.remaining q:=by
      rw [remaining_formula T q (le_refl _)]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro h
      obtain ⟨i,hi,hvi⟩:=Finset.mem_biUnion.mp h
      exact hex ⟨⟨i,Finset.mem_range.mp hi⟩,hvi⟩
    refine ⟨none,hv, ?_⟩
    intro i hi
    cases i with
    | none => rfl
    | some i => exact (hex ⟨i, (Finset.mem_sdiff.mp hi).1⟩).elim

theorem no_cross_parts {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (T:Trace G start q) (i j:Option (Fin q)) (different:i ≠ j)
    (u v:Fin n) (hu:u∈ parts T i) (hv:v∈ parts T j):¬G.Adj u v:=by
  cases i with
  | none =>
    cases j with
    | none => exact (different rfl).elim
    | some j =>
      have hu':u∈ T.left j \ T.right j:=by
        rw [← T.next j j.isLt]
        exact remaining_mono T (j.val + 1) q (by omega) (le_refl _) hu
      exact T.separated j j.isLt u hu' v hv
  | some i =>
    cases j with
    | none =>
      have hv':v∈ T.left i \ T.right i:=by
        rw [← T.next i i.isLt]
        exact remaining_mono T (i.val + 1) q (by omega) (le_refl _) hv
      exact fun h => T.separated i i.isLt v hv' u hu h.symm
    | some j =>
      have hne:i.val ≠ j.val:=by intro h; exact different (congrArg some (Fin.ext h))
      rcases lt_or_gt_of_ne hne with hij | hji
      · have hv':v∈ T.left i \ T.right i:=by
          rw [← T.next i i.isLt]
          exact remaining_mono T (i.val + 1) j (by omega) j.isLt.le
            (right_subset T j j.isLt (Finset.mem_sdiff.mp hv).1)
        exact fun h => T.separated i i.isLt v hv' u hu h.symm
      · have hu':u∈ T.left j \ T.right j:=by
          rw [← T.next j j.isLt]
          exact remaining_mono T (j.val + 1) i (by omega) i.isLt.le
            (right_subset T i i.isLt (Finset.mem_sdiff.mp hu).1)
        exact T.separated j j.isLt u hu' v hv

def partition {n q:ℕ} {G:SimpleGraph (Fin n)} (T:Trace G Finset.univ q):
    Partition G (separator T) (Option (Fin q)) where
  vertices:=parts T
  outside:=parts_outside T
  unique:=parts_unique T
  closed:=by
    intro i u v hu hv huv
    obtain ⟨j,hj,_⟩:=parts_unique T v hv
    have hji:j=i:=by
      by_contra h
      exact no_cross_parts T i j (Ne.symm h) u v hu hj huv
    simpa [hji] using hj

theorem trace_correct {n q:ℕ} (G:SimpleGraph (Fin n)) (T:Trace G Finset.univ q)
    (finished:3 * (T.remaining q).card≤ 2 * n)
    (x:Fin n→ ℝ) (nonnegative:∀ v,0≤ x v) (ρ γ:ℝ) (hρ:0≤ ρ) (hγ:0 < γ)
    (each_cut:∀ i < q,Lax263307.RepeatedCutAccounting.cost x (T.left i ∩ T.right i)≤
      4 * ρ * (T.left i).card * (T.right i).card / γ):
    q≤ n∧ IsBalancedSeparator G (separator T)∧
      Lax263307.RepeatedCutAccounting.cost x (separator T)≤ 4 * ρ * (n:ℝ) ^ 2 / γ:=by
  classical
  refine ⟨by simpa using step_bound T, ?_, ?_⟩
  · apply Lax263307Proofs.BalancedPartitions.balanced_separator G (separator T) (partition T)
    intro i
    cases i with
    | none => exact finished
    | some i =>
      have h:=T.small_piece i i.isLt
      have hr:(T.remaining i).card≤ n:=by simpa using Finset.card_le_univ (T.remaining i)
      change 3 * (T.right i \ T.left i).card≤ 2 * n
      omega
  · exact Lax263307Proofs.RepeatedCutAccounting.total_cut_cost x nonnegative
      (fun i:Fin q => T.left i) (fun i:Fin q => T.right i) (right_pairwise T) ρ γ hρ hγ
        (fun i => each_cut i i.isLt)

def emptyTrace {n:ℕ} (G:SimpleGraph (Fin n)) (start:Finset (Fin n)):Trace G start 0 where
  remaining:=fun _ => start
  left:=fun _ => ∅
  right:=fun _ => ∅
  initial:=rfl
  cover:=by intro i hi; omega
  next:=by intro i hi; omega
  nonempty:=by intro i hi; omega
  small_piece:=by intro i hi; omega
  separated:=by intro i hi; omega

def prepend {n q:ℕ} {G:SimpleGraph (Fin n)} {start:Finset (Fin n)}
    (A B:Finset (Fin n)) (cover:A ∪ B=start) (nonempty:B.Nonempty)
    (small:2 * (B \ A).card≤ start.card)
    (separated:∀ u∈ A \ B, ∀ v∈ B \ A, ¬G.Adj u v)
    (T:Trace G (A \ B) q):Trace G start (q + 1) where
  remaining | 0 => start | i + 1 => T.remaining i
  left | 0 => A | i + 1 => T.left i
  right | 0 => B | i + 1 => T.right i
  initial:=rfl
  cover:=by intro i hi; cases i with
    | zero => exact cover
    | succ i => exact T.cover i (by omega)
  next:=by intro i hi; cases i with
    | zero => exact T.initial
    | succ i => exact T.next i (by omega)
  nonempty:=by intro i hi; cases i with
    | zero => exact nonempty
    | succ i => exact T.nonempty i (by omega)
  small_piece:=by intro i hi; cases i with
    | zero => exact small
    | succ i => exact T.small_piece i (by omega)
  separated:=by intro i hi; cases i with
    | zero => exact separated
    | succ i => exact T.separated i (by omega)

end Lax263307Proofs.CutTraces

end

section

namespace Lax263307Proofs.PowerBagBounds

open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth Lax228581.Treewidth
open Lax263307.PowerBagBounds

theorem root_bag_bound (C:GraphClass) (a A:ℕ) (a_positive:0 < a) (A_positive:0 < A)
    (class_bound:HasPowerBagBound C a A):
    Monotone (bagBound a A)∧ HasBagBound C (bagBound a A)∧
      (∀ m,1≤ bagBound a A m)∧
      (∀ m, (bagBound a A m) ^ a≤ A * (m + 1) ^ (a - 1)):=by
  have ha:a ≠ 0:=ne_of_gt a_positive
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n hmn
    apply (Nat.le_nthRoot_iff ha).mpr
    exact (Nat.pow_nthRoot_le (Or.inl ha)).trans
      (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (Nat.succ_le_succ hmn) _))
  · intro n G hG
    obtain ⟨D,hD⟩:=class_bound n G hG
    exact ⟨D,fun i => (Nat.le_nthRoot_iff ha).mpr (hD i)⟩
  · intro m
    apply (Nat.le_nthRoot_iff ha).mpr
    simp only [one_pow]
    exact Nat.succ_le_of_lt (Nat.mul_pos A_positive (Nat.pow_pos (Nat.succ_pos m)))
  · intro m
    exact Nat.pow_nthRoot_le (Or.inl ha)

end Lax263307Proofs.PowerBagBounds

end

section

namespace Lax263307Proofs.EdgeDeletionWidth

open Lax228581.Treewidth

noncomputable def restoreCoveredEdges {n:ℕ} {G H:SimpleGraph (Fin n)}
    (X:Finset (Fin n))
    (covered:∀ u v,G.Adj u v→ H.Adj u v∨ u∈ X∨ v∈ X)
    (D:TreeDecomposition H):TreeDecomposition G:=by
  classical
  exact
    { Node:=D.Node
      nodeFintype:=D.nodeFintype
      tree:=D.tree
      isTree:=D.isTree
      bag:=fun i => X ∪ D.bag i
      vertex_mem_bag:=by
        intro v
        obtain ⟨i,hi⟩:=D.vertex_mem_bag v
        exact ⟨i,Finset.mem_union_right X hi⟩
      edge_mem_bag:=by
        intro u v huv
        rcases covered u v huv with h | hu | hv
        · obtain ⟨i,hiu,hiv⟩:=D.edge_mem_bag h
          exact ⟨i,Finset.mem_union_right X hiu,Finset.mem_union_right X hiv⟩
        · obtain ⟨i,hi⟩:=D.vertex_mem_bag v
          exact ⟨i,Finset.mem_union_left _ hu,Finset.mem_union_right X hi⟩
        · obtain ⟨i,hi⟩:=D.vertex_mem_bag u
          exact ⟨i,Finset.mem_union_right X hi,Finset.mem_union_left _ hv⟩
      bag_indices_connected:=by
        intro v
        by_cases hv:v∈ X
        · have hset:{i | v∈ X ∪ D.bag i}=Set.univ:=by ext i; simp [hv]
          rw [hset]
          exact (SimpleGraph.induceUnivIso D.tree).connected_iff.mpr D.isTree.connected
        · have hset:{i | v∈ X ∪ D.bag i}={i | v∈ D.bag i}:=by ext i; simp [hv]
          rw [hset]
          exact D.bag_indices_connected v }

theorem restore_edges {n:ℕ} (G:SimpleGraph (Fin n)) (F:Finset (Sym2 (Fin n)))
    (w:ℕ) (width:HasTreewidthAtMost (G.deleteEdges (↑F:Set (Sym2 (Fin n)))) w):
    HasTreewidthAtMost G (w + F.card):=by
  classical
  let H:=G.deleteEdges (↑F:Set (Sym2 (Fin n)))
  let X:=F.image fun e => e.out.1
  have hcovered:∀ u v,G.Adj u v→ H.Adj u v∨ u∈ X∨ v∈ X:=by
    intro u v huv
    by_cases he:s(u,v)∈ F
    · have hx:s(u,v).out.1∈ X:=Finset.mem_image.mpr ⟨s(u,v),he,rfl⟩
      have hmem:s(u,v).out.1=u∨ s(u,v).out.1=v:=
        Sym2.mem_iff.mp (Sym2.out_fst_mem s(u,v))
      rcases hmem with hu | hv
      · exact Or.inr (Or.inl (hu ▸ hx))
      · exact Or.inr (Or.inr (hv ▸ hx))
    · exact Or.inl (by simpa [H,SimpleGraph.deleteEdges_adj] using And.intro huv he)
  obtain ⟨D,hD⟩:=width
  refine ⟨restoreCoveredEdges X hcovered D, ?_⟩
  intro i
  have hX:X.card≤ F.card:=Finset.card_image_le
  change (X ∪ D.bag i).card≤ w + F.card + 1
  have hbag:=Finset.card_union_le X (D.bag i)
  have hi:=hD i
  omega

end Lax263307Proofs.EdgeDeletionWidth

end

section

namespace Lax263307Proofs.HostRestriction

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges

theorem restrict_to_route_union {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (induced:IsInduced E)
    (nonempty:(routeUnion E).Nonempty):
    ∃ r, ∃ K:SimpleGraph (Fin r), ∃ _f:K ↪g G, ∃ E':AlmostEmbedding H K,
      IsInduced E'∧ (∀ e, (E'.route e).card=(E.route e).card)∧
      K.edgeSet.ncard=(G.induce (↑(routeUnion E):Set (Fin n))).edgeSet.ncard:=by
  classical
  let U:=routeUnion E
  let S:Set (Fin n):= ↑U
  let r:=Fintype.card S
  let idx:S ≃ Fin r:=Fintype.equivFin S
  obtain ⟨root,hroot⟩:=nonempty
  let forward:Fin r→ Fin n:=fun i => (idx.symm i).val
  let backward:Fin n→ Fin r:=fun v =>
    if hv:v∈ U then idx ⟨v,hv⟩ else idx ⟨root,hroot⟩
  let K:=G.comap forward
  let f:K ↪g G:= {
    toFun:=forward
    inj':=by intro i j h; exact idx.symm.injective (Subtype.ext h)
    map_rel_iff':=by intro i j; rfl }
  have route_subset (e:H.edgeSet):E.route e ⊆ U:=by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,hv⟩
  have hf (v:Fin n) (hv:v∈ U):forward (backward v)=v:=by
    simp [backward,hv,forward]
  have hb_inj (u v:Fin n) (hu:u∈ U) (hv:v∈ U) (h:backward u=backward v):u=v:=by
    have hh:=congrArg forward h
    rwa [hf u hu,hf v hv] at hh
  let E':AlmostEmbedding H K:= {
    vertexMap:=fun v => backward (E.vertexMap v)
    route:=fun e => (E.route e).image backward
    connected:=by
      intro e
      let map:G.induce (↑(E.route e):Set (Fin n))→g
          K.induce (↑((E.route e).image backward):Set (Fin r)):= {
        toFun:=fun v => ⟨backward v.val,Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩
        map_rel':=by
          intro u v huv
          change G.Adj (forward (backward u.val)) (forward (backward v.val))
          rwa [hf u.val (route_subset e u.property),hf v.val (route_subset e v.property)] }
      apply (E.connected e).map map
      rintro ⟨z,hz⟩
      obtain ⟨v,hv,hvz⟩:=Finset.mem_image.mp hz
      exact ⟨⟨v,hv⟩,Subtype.ext hvz⟩
    endpoints:=by
      intro e v hv
      exact Finset.mem_image.mpr ⟨E.vertexMap v,E.endpoints e v hv,rfl⟩
    disjoint:=by
      intro e h eh
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨u,hu,huz⟩:=Finset.mem_image.mp hz
      obtain ⟨v,hv,hvz⟩:=Finset.mem_image.mp hz'
      have huv:=hb_inj u v (route_subset e hu) (route_subset h hv) (huz.trans hvz.symm)
      subst v
      exact Finset.disjoint_left.mp (E.disjoint e h eh) hu hv }
  refine ⟨r,K,f,E', ?_, ?_, ?_⟩
  · intro e h eh u hu v hv huv
    obtain ⟨x,hx,hxu⟩:=Finset.mem_image.mp hu
    obtain ⟨y,hy,hyv⟩:=Finset.mem_image.mp hv
    subst u v
    apply induced e h eh x hx y hy
    change G.Adj (forward (backward x)) (forward (backward y)) at huv
    rwa [hf x (route_subset e hx),hf y (route_subset h hy)] at huv
  · intro e
    apply Finset.card_image_iff.mpr
    intro u hu v hv h
    exact hb_inj u v (route_subset e hu) (route_subset e hv) h
  · let iso:K ≃g G.induce S:= {
      toEquiv:=idx.symm
      map_rel_iff':=by intro u v; rfl }
    have h:=Fintype.card_congr iso.mapEdgeSet
    simpa only [Set.fintypeCard_eq_ncard] using h

end Lax263307Proofs.HostRestriction

end

section

namespace Lax263307Proofs.ConnectedBags

open Lax263307.ConnectedBags Lax228581.Treewidth

theorem vertex_meeting_reachable {n:ℕ} {G:SimpleGraph (Fin n)}
    (D:TreeDecomposition G) (U:Finset (Fin n)) (v:Fin n) (hv:v∈ U)
    (i j:↥(meetingNodes D U)) (hi:v∈ D.bag i.val) (hj:v∈ D.bag j.val):
    (D.tree.induce (meetingNodes D U)).Reachable i j:=by
  let f:=D.tree.induceHomOfLE
    (show {k | v∈ D.bag k} ⊆ meetingNodes D U from fun k hk => ⟨v,hv,hk⟩)
  exact ((D.bag_indices_connected v) ⟨i.val,hi⟩ ⟨j.val,hj⟩).map f.toHom

theorem walk_meeting_reachable {n:ℕ} {G:SimpleGraph (Fin n)}
    (D:TreeDecomposition G) (U:Finset (Fin n))
    {u v:↥(↑U:Set (Fin n))} (p:(G.induce (↑U:Set (Fin n))).Walk u v)
    (i j:↥(meetingNodes D U)) (hi:u.val∈ D.bag i.val) (hj:v.val∈ D.bag j.val):
    (D.tree.induce (meetingNodes D U)).Reachable i j:=by
  induction p generalizing i with
  | @nil u => exact vertex_meeting_reachable D U u.val u.property i j hi hj
  | @cons u a v huv p ih =>
    obtain ⟨b,hbu,hba⟩:=D.edge_mem_bag huv
    let b':↥(meetingNodes D U):= ⟨b,u.val,u.property,hbu⟩
    exact (vertex_meeting_reachable D U u.val u.property i b' hi hbu).trans
      (ih b' hba hj)

theorem meeting_connected {n:ℕ} (G:SimpleGraph (Fin n))
    (D:TreeDecomposition G) (U:Finset (Fin n))
    (connected:(G.induce (↑U:Set (Fin n))).Connected):
    (D.tree.induce (meetingNodes D U)).Connected:=by
  obtain ⟨u⟩:=connected.nonempty
  obtain ⟨b,hb⟩:=D.vertex_mem_bag u.val
  have hnonempty:Nonempty ↥(meetingNodes D U):= ⟨⟨b,u.val,u.property,hb⟩⟩
  refine { preconnected:= ?_,nonempty:=hnonempty }
  intro i j
  obtain ⟨a,ha,hai⟩:=i.property
  obtain ⟨b,hb,hbj⟩:=j.property
  obtain ⟨p⟩:=connected ⟨a,ha⟩ ⟨b,hb⟩
  exact walk_meeting_reachable D U p i j hai hbj

end Lax263307Proofs.ConnectedBags

end

section

namespace Lax263307Proofs.ConnectedRepresentations

open Lax263307.ConnectedRepresentations Lax263307.ConnectedBags Lax228581.Treewidth

def representationBag {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (R:Representation H G) (bag:Finset (Fin n)):Finset (Fin t):=
  bag.biUnion (users R)

theorem representationBag_mem {t n:ℕ} {H:SimpleGraph (Fin t)}
    {G:SimpleGraph (Fin n)} (R:Representation H G) (bag:Finset (Fin n))
    (v:Fin t):v∈ representationBag R bag↔ ∃ a∈ R.carrier v,a∈ bag:=by
  simp only [representationBag,users,Finset.mem_biUnion,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor <;> rintro ⟨a,ha,hb⟩ <;> exact ⟨a,hb,ha⟩

def transfer {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (R:Representation H G) (D:TreeDecomposition G):TreeDecomposition H where
  Node:=D.Node
  nodeFintype:=D.nodeFintype
  tree:=D.tree
  isTree:=D.isTree
  bag i:=representationBag R (D.bag i)
  vertex_mem_bag v:=by
    obtain ⟨a⟩:=(R.connected v).nonempty
    obtain ⟨i,hi⟩:=D.vertex_mem_bag a.val
    exact ⟨i, (representationBag_mem R (D.bag i) v).mpr ⟨a.val,a.property,hi⟩⟩
  edge_mem_bag:=by
    intro u v huv
    obtain ⟨a,hau,hav⟩:=R.touching u v huv
    obtain ⟨i,hi⟩:=D.vertex_mem_bag a
    exact ⟨i, (representationBag_mem R (D.bag i) u).mpr ⟨a,hau,hi⟩,
      (representationBag_mem R (D.bag i) v).mpr ⟨a,hav,hi⟩⟩
  bag_indices_connected v:=by
    have hset:{i | v∈ representationBag R (D.bag i)}=meetingNodes D (R.carrier v):=by
      ext i
      exact representationBag_mem R (D.bag i) v
    rw [hset]
    exact Lax263307Proofs.ConnectedBags.meeting_connected G D (R.carrier v) (R.connected v)

theorem transfer_decomposition {t n:ℕ} (H:SimpleGraph (Fin t))
    (G:SimpleGraph (Fin n)) (R:Representation H G)
    (B w:ℕ) (load_bound:∀ a, (users R a).card≤ B)
    (D:TreeDecomposition G) (bag_bound:∀ i, (D.bag i).card≤ w):
    ∃ D':TreeDecomposition H, ∀ i, (D'.bag i).card≤ B * w:=by
  refine ⟨transfer R D, ?_⟩
  intro i
  calc
    (representationBag R (D.bag i)).card≤ ∑ a∈ D.bag i, (users R a).card:=
      Finset.card_biUnion_le
    _≤ ∑ _a∈ D.bag i,B:=Finset.sum_le_sum fun a _ => load_bound a
    _=B * (D.bag i).card:=by simp [Nat.mul_comm]
    _≤ B * w:=Nat.mul_le_mul_left B (bag_bound i)

end Lax263307Proofs.ConnectedRepresentations

end

section

namespace Lax263307Proofs.AlmostEmbeddings

open Lax263307.AlmostEmbeddings Lax263307.ConnectedRepresentations Lax228581.Treewidth

theorem carrier_mem {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (E:AlmostEmbedding H G) (v:Fin t) (a:Fin n):
    a∈ vertexCarrier E v↔ ∃ e:H.edgeSet,v∈ e.val∧ a∈ E.route e:=by
  classical
  unfold vertexCarrier
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e,_,ha⟩
    by_cases hv:v∈ e.val
    · exact ⟨e,hv,by simpa only [if_pos hv] using ha⟩
    · simp [hv] at ha
  · rintro ⟨e,hv,ha⟩
    exact ⟨e,Finset.mem_univ _,by simpa only [if_pos hv] using ha⟩

theorem carrier_connected {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (E:AlmostEmbedding H G) (v:Fin t) (active:¬H.IsIsolated v):
    (G.induce (↑(vertexCarrier E v):Set (Fin n))).Connected:=by
  classical
  obtain ⟨u,huv⟩:∃ u,H.Adj v u:=by simpa [SimpleGraph.IsIsolated] using active
  let e:H.edgeSet:= ⟨s(v,u),huv⟩
  have he:v∈ e.val:=Sym2.mem_mk_left _ _
  have hroot:=E.endpoints e v he
  have hroot':E.vertexMap v∈ vertexCarrier E v:=(carrier_mem E v _).mpr ⟨e,he,hroot⟩
  let root:↥(↑(vertexCarrier E v):Set (Fin n)):= ⟨E.vertexMap v,hroot'⟩
  have hreach:∀ a:↥(↑(vertexCarrier E v):Set (Fin n)),
      (G.induce (↑(vertexCarrier E v):Set (Fin n))).Reachable a root:=by
    intro a
    obtain ⟨f,hvf,haf⟩:=(carrier_mem E v a.val).mp a.property
    have hsubset:(↑(E.route f):Set (Fin n)) ⊆ ↑(vertexCarrier E v):=by
      intro b hb
      exact (carrier_mem E v b).mpr ⟨f,hvf,hb⟩
    exact ((E.connected f) ⟨a.val,haf⟩ ⟨E.vertexMap v,E.endpoints f v hvf⟩).map
      (G.induceHomOfLE hsubset).toHom
  exact
    { preconnected:=fun a b => (hreach a).trans (hreach b).symm
      nonempty:= ⟨root⟩ }

noncomputable def representation {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    (E:AlmostEmbedding H G) (active:∀ v, ¬H.IsIsolated v):Representation H G where
  carrier:=vertexCarrier E
  connected:=fun v => carrier_connected E v (active v)
  touching:=by
    intro u v huv
    let e:H.edgeSet:= ⟨s(u,v),huv⟩
    have hue:u∈ e.val:=Sym2.mem_mk_left _ _
    have hve:v∈ e.val:=Sym2.mem_mk_right _ _
    exact ⟨E.vertexMap u, (carrier_mem E u _).mpr ⟨e,hue,E.endpoints e u hue⟩,
      (carrier_mem E v _).mpr ⟨e,hve,E.endpoints e u hue⟩⟩

theorem incident_endpoints {t:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    {x y:Fin t} (hxy:H.Adj x y) (f:H.edgeSet)
    (incident:¬Disjoint ({x,y}:Finset (Fin t)) f.val.toFinset):
    f.val.toFinset ⊆ H.neighborFinset x ∪ H.neighborFinset y:=by
  obtain ⟨b,hb,hbf⟩:=Finset.not_disjoint_iff.mp incident
  have hbf':b∈ f.val:=Sym2.mem_toFinset.mp hbf
  obtain ⟨c,hfc⟩:=Sym2.mem_iff_exists.mp hbf'
  have hbc:H.Adj b c:=by
    change s(b,c)∈ H.edgeSet
    rw [← hfc]
    exact f.property
  intro a ha
  have ha':a=b∨ a=c:=by simpa [hfc] using ha
  have hb':b=x∨ b=y:=by simpa using hb
  rcases hb' with rfl | rfl <;> rcases ha' with rfl | rfl
  · exact Finset.mem_union_right _ (by simpa using hxy.symm)
  · exact Finset.mem_union_left _ (by simpa using hbc)
  · exact Finset.mem_union_left _ (by simpa using hxy)
  · exact Finset.mem_union_right _ (by simpa using hbc)

theorem representation_load {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (d:ℕ)
    (hdegree:∀ v,H.degree v≤ d) (active:∀ v, ¬H.IsIsolated v) (a:Fin n):
    (users (representation E active) a).card≤ 2 * d:=by
  classical
  let L:=users (representation E active) a
  by_cases hL:L=∅
  · simp [L,hL]
  · obtain ⟨v,hv⟩:=Finset.nonempty_iff_ne_empty.mpr hL
    have hva:a∈ vertexCarrier E v:=(Finset.mem_filter.mp hv).2
    obtain ⟨e,_,hae⟩:=(carrier_mem E v a).mp hva
    let x:=e.val.out.1
    let y:=e.val.out.2
    have heq:e.val=s(x,y):=e.val.out_eq.symm
    have hxy:H.Adj x y:=by
      change s(x,y)∈ H.edgeSet
      rw [← heq]
      exact e.property
    have hsubset:L ⊆ H.neighborFinset x ∪ H.neighborFinset y:=by
      intro w hw
      have hwa:a∈ vertexCarrier E w:=(Finset.mem_filter.mp hw).2
      obtain ⟨f,hwf,haf⟩:=(carrier_mem E w a).mp hwa
      have hincident:¬Disjoint e.val.toFinset f.val.toFinset:=by
        intro hdisj
        exact Finset.disjoint_left.mp (E.disjoint e f hdisj) hae haf
      have hincident':¬Disjoint ({x,y}:Finset (Fin t)) f.val.toFinset:=by
        simpa [heq,Sym2.toFinset_mk_eq] using hincident
      exact incident_endpoints H hxy f hincident' (Sym2.mem_toFinset.mpr hwf)
    calc
      L.card≤ (H.neighborFinset x ∪ H.neighborFinset y).card:=Finset.card_le_card hsubset
      _≤ (H.neighborFinset x).card + (H.neighborFinset y).card:=Finset.card_union_le _ _
      _=H.degree x + H.degree y:=rfl
      _≤ 2 * d:=by have hx:=hdegree x; have hy:=hdegree y; omega

theorem transfer_decomposition {t n:ℕ} (H:SimpleGraph (Fin t))
    [DecidableRel H.Adj] (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G)
    (d w:ℕ) (degree_bound:∀ v,H.degree v≤ d)
    (no_isolates:∀ v, ¬H.IsIsolated v)
    (D:TreeDecomposition G) (bag_bound:∀ i, (D.bag i).card≤ w):
    ∃ D':TreeDecomposition H, ∀ i, (D'.bag i).card≤ 2 * d * w:=by
  exact Lax263307Proofs.ConnectedRepresentations.transfer_decomposition H G
    (representation E no_isolates) (2 * d) w
    (representation_load H G E d degree_bound no_isolates) D bag_bound

end Lax263307Proofs.AlmostEmbeddings

end

section

namespace Lax263307Proofs.InducedRouteEdges

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges

noncomputable def incidentEdges {t:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (e:H.edgeSet):
    Finset H.edgeSet:=by
  classical
  exact Finset.univ.filter fun f => ¬Disjoint e.val.toFinset f.val.toFinset

theorem incidentEdges_card {t:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (e:H.edgeSet) (d:ℕ) (hdegree:∀ v,H.degree v≤ d):
    (incidentEdges H e).card≤ 2 * d:=by
  classical
  let x:=e.val.out.1
  let y:=e.val.out.2
  have heq:e.val=s(x,y):=e.val.out_eq.symm
  have hsub:(incidentEdges H e).image Subtype.val ⊆
      H.incidenceFinset x ∪ H.incidenceFinset y:=by
    intro q hq
    obtain ⟨f,hf,hfq⟩:=Finset.mem_image.mp hq
    subst q
    obtain ⟨b,hbe,hbf⟩:=Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hf).2
    have hb:b=x∨ b=y:=by simpa [heq] using hbe
    have hbf':=Sym2.mem_toFinset.mp hbf
    rcases hb with rfl | rfl
    · exact Finset.mem_union_left _ ((H.mem_incidenceFinset x f.val).mpr ⟨f.property,hbf'⟩)
    · exact Finset.mem_union_right _ ((H.mem_incidenceFinset y f.val).mpr ⟨f.property,hbf'⟩)
  calc
    (incidentEdges H e).card=((incidentEdges H e).image Subtype.val).card:=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _≤ (H.incidenceFinset x ∪ H.incidenceFinset y).card:=Finset.card_le_card hsub
    _≤ (H.incidenceFinset x).card + (H.incidenceFinset y).card:=Finset.card_union_le _ _
    _=H.degree x + H.degree y:=by rw [H.card_incidenceFinset_eq_degree,H.card_incidenceFinset_eq_degree]
    _≤ 2 * d:=by have hx:=hdegree x; have hy:=hdegree y; omega

theorem routeUnion_card {t n:ℕ} {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)}
    [DecidableRel H.Adj]
    (E:AlmostEmbedding H G) (L:ℕ) (hlength:∀ e, (E.route e).card≤ L):
    (routeUnion E).card≤ H.edgeSet.ncard * L:=by
  classical
  calc
    (routeUnion E).card≤ ∑ e, (E.route e).card:=Finset.card_biUnion_le
    _≤ ∑ _e:H.edgeSet,L:=Finset.sum_le_sum fun e _ => hlength e
    _=Fintype.card H.edgeSet * L:=by simp
    _=H.edgeSet.ncard * L:=by rw [Set.fintypeCard_eq_ncard]

theorem routeUnion_degree {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (d L:ℕ)
    (induced:IsInduced E) (hdegree:∀ v,H.degree v≤ d)
    (hlength:∀ e, (E.route e).card≤ L)
    (a:↥(↑(routeUnion E):Set (Fin n))):
    (by classical exact (G.induce (↑(routeUnion E):Set (Fin n))).degree a)≤ 2 * d * L:=by
  classical
  let F:=G.induce (↑(routeUnion E):Set (Fin n))
  obtain ⟨e,_,hae⟩:=Finset.mem_biUnion.mp a.property
  let B:=(incidentEdges H e).biUnion E.route
  have hsub:(F.neighborFinset a).image Subtype.val ⊆ B:=by
    intro b hb
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hb
    have hab:F.Adj a b:=by simpa using hb
    obtain ⟨f,_,hbf⟩:=Finset.mem_biUnion.mp b.property
    have hinc:¬Disjoint e.val.toFinset f.val.toFinset:=by
      intro hdisj
      exact induced e f hdisj a.val hae b.val hbf hab
    exact Finset.mem_biUnion.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinc⟩,hbf⟩
  calc
    F.degree a=((F.neighborFinset a).image Subtype.val).card:=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _≤ B.card:=Finset.card_le_card hsub
    _≤ ∑ f∈ incidentEdges H e, (E.route f).card:=Finset.card_biUnion_le
    _≤ ∑ _f∈ incidentEdges H e,L:=Finset.sum_le_sum fun f _ => hlength f
    _=(incidentEdges H e).card * L:=by simp
    _≤ 2 * d * L:=Nat.mul_le_mul_right L (incidentEdges_card H e d hdegree)

theorem edge_bound {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (d L:ℕ)
    (induced:IsInduced E) (degree_bound:∀ v,H.degree v≤ d)
    (length_bound:∀ e, (E.route e).card≤ L):
    (G.induce (↑(routeUnion E):Set (Fin n))).edgeSet.ncard≤
      d * H.edgeSet.ncard * L ^ 2:=by
  classical
  let F:=G.induce (↑(routeUnion E):Set (Fin n))
  change F.edgeSet.ncard≤ d * H.edgeSet.ncard * L ^ 2
  have hsum:(∑ a,F.degree a)≤ 2 * d * L * (routeUnion E).card:=by
    calc
      (∑ a,F.degree a)≤ ∑ _a:↥(↑(routeUnion E):Set (Fin n)),2 * d * L:=
        Finset.sum_le_sum fun a _ => routeUnion_degree H G E d L induced degree_bound length_bound a
      _=2 * d * L * (routeUnion E).card:=by simp [Nat.mul_comm]
  have horder:=routeUnion_card E L length_bound
  have hcount:(∑ a,F.degree a)=2 * F.edgeSet.ncard:=by
    rw [F.sum_degrees_eq_twice_card_edges,SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard]
  have hproduct:=Nat.mul_le_mul_left (2 * d * L) horder
  have hbound:2 * F.edgeSet.ncard≤ 2 * (d * H.edgeSet.ncard * L ^ 2):=by
    calc
      2 * F.edgeSet.ncard≤ 2 * d * L * (routeUnion E).card:=by simpa only [hcount] using hsum
      _≤ 2 * d * L * (H.edgeSet.ncard * L):=hproduct
      _=2 * (d * H.edgeSet.ncard * L ^ 2):=by ring
  omega

end Lax263307Proofs.InducedRouteEdges

end

section

namespace Lax263307Proofs.IsolatedEmbeddingTransfer

open Lax263307.AlmostEmbeddings Lax228581.Treewidth
open Lax263307Proofs.TreeExtensions

noncomputable def restrictSource {r t n:ℕ} {K:SimpleGraph (Fin r)}
    {H:SimpleGraph (Fin t)} {G:SimpleGraph (Fin n)} (f:K ↪g H)
    (E:AlmostEmbedding H G):AlmostEmbedding K G where
  vertexMap:=fun v => E.vertexMap (f v)
  route:=fun e => E.route (f.toHom.mapEdgeSet e)
  connected:=fun e => E.connected _
  endpoints:=by
    intro e v hv
    apply E.endpoints
    exact Sym2.mem_map.mpr ⟨v,hv,rfl⟩
  disjoint:=by
    intro e h hd
    apply E.disjoint
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u,hu,huz⟩:=Sym2.mem_map.mp (Sym2.mem_toFinset.mp hz)
    obtain ⟨v,hv,hvz⟩:=Sym2.mem_map.mp (Sym2.mem_toFinset.mp hz')
    have huv:u=v:=f.injective (huz.trans hvz.symm)
    subst v
    exact Finset.disjoint_left.mp hd (Sym2.mem_toFinset.mpr hu) (Sym2.mem_toFinset.mpr hv)

theorem embedding_degree {r t:ℕ} (K:SimpleGraph (Fin r)) [DecidableRel K.Adj]
    (H:SimpleGraph (Fin t)) [DecidableRel H.Adj] (f:K ↪g H) (v:Fin r):
    K.degree v≤ H.degree (f v):=by
  classical
  rw [← K.card_neighborSet_eq_degree v, ← H.card_neighborSet_eq_degree (f v)]
  apply Fintype.card_le_of_injective (f.toHom.mapNeighborSet v)
  intro a b h
  apply Subtype.ext
  exact f.injective (congrArg Subtype.val h)

theorem transfer_decomposition {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (d w:ℕ)
    (degree_bound:∀ v,H.degree v≤ d)
    (D:TreeDecomposition G) (bag_bound:∀ i, (D.bag i).card≤ w):
    ∃ D':TreeDecomposition H, ∀ i, (D'.bag i).card≤ max 1 (2 * d * w):=by
  classical
  let S:Set (Fin t):= {v | ¬H.IsIsolated v}
  let r:=Fintype.card S
  let e:S ≃ Fin r:=Fintype.equivFin S
  let f:Fin r→ Fin t:=fun v => (e.symm v).val
  let K:=H.comap f
  let emb:K ↪g H:= {
    toFun:=f
    inj':=by intro u v h; exact e.symm.injective (Subtype.ext h)
    map_rel_iff':=by intro u v; rfl }
  have no_isolates (v:Fin r):¬K.IsIsolated v:=by
    have hv:¬H.IsIsolated (f v):=(e.symm v).property
    obtain ⟨u,hu⟩:∃ u,H.Adj (f v) u:=by simpa [SimpleGraph.IsIsolated] using hv
    have hau:u∈ S:=by
      intro h
      exact h (f v) hu.symm
    let z:=e ⟨u,hau⟩
    have hz:f z=u:=by simp [f,z]
    intro h
    apply h z
    change H.Adj (f v) (f z)
    rwa [hz]
  have degree_K (v:Fin r):K.degree v≤ d:=
    (embedding_degree K H emb v).trans (degree_bound _)
  obtain ⟨DK,hDK⟩:=Lax263307Proofs.AlmostEmbeddings.transfer_decomposition K G
    (restrictSource emb E) d w degree_K no_isolates D bag_bound
  let inv:H.induce S ↪g K:= {
    toFun:=e
    inj':=e.injective
    map_rel_iff':=by
      intro u v
      change H.Adj (f (e u)) (f (e v))↔ H.Adj u.val v.val
      simp [f] }
  let DS:=pullback inv DK
  have isolated (v:Fin t) (hv:v∉ S):H.IsIsolated v:=by simpa [S] using hv
  refine ⟨extendIsolated S isolated DS, ?_⟩
  apply extendIsolated_card S isolated DS _ (le_max_left _ _)
  intro i
  exact (pullback_card inv DK i).trans ((hDK i).trans (le_max_right _ _))

end Lax263307Proofs.IsolatedEmbeddingTransfer

end

section

namespace Lax263307Proofs.RoutePruning

open Lax263307.AlmostEmbeddings Lax263307.RoutePruning

theorem longEdges_mem {t n:ℕ} {H:SimpleGraph (Fin t)} [DecidableRel H.Adj]
    {G:SimpleGraph (Fin n)} (E:AlmostEmbedding H G) (L:ℕ) (e:H.edgeSet):
    e.val∈ longEdges E L↔ L < (E.route e).card:=by
  classical
  simp only [longEdges,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨f,hf,he⟩
    have hfe:f=e:=Subtype.ext he
    simpa [hfe] using hf
  · intro h
    exact ⟨e,h,rfl⟩

theorem long_edge_count {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (L:ℕ):
    L * (longEdges E L).card≤ ∑ e:H.edgeSet, (E.route e).card:=by
  classical
  let S:=Finset.univ.filter fun e:H.edgeSet => L < (E.route e).card
  have hc:(longEdges E L).card=S.card:=Finset.card_image_of_injective _ Subtype.val_injective
  rw [hc]
  calc
    L * S.card=∑ _e∈ S,L:=by simp [Nat.mul_comm]
    _≤ ∑ e∈ S, (E.route e).card:=Finset.sum_le_sum fun e he =>
      (Finset.mem_filter.mp he).2.le
    _≤ ∑ e:H.edgeSet, (E.route e).card:=Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)

noncomputable def restrictEdges {t n:ℕ} {K H:SimpleGraph (Fin t)}
    {G:SimpleGraph (Fin n)} (subgraph:K≤ H) (E:AlmostEmbedding H G):AlmostEmbedding K G where
  vertexMap:=E.vertexMap
  route e:=E.route ⟨e.val,SimpleGraph.edgeSet_mono subgraph e.property⟩
  connected _e:=E.connected _
  endpoints _e v hv:=E.endpoints _ v hv
  disjoint _e _f h:=E.disjoint _ _ h

theorem prune_routes {t n:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) (E:AlmostEmbedding H G) (induced:IsInduced E) (L:ℕ):
    ∃ E':AlmostEmbedding (H.deleteEdges (↑(longEdges E L):Set (Sym2 (Fin t)))) G,
      IsInduced E'∧ (∀ e, (E'.route e).card≤ L):=by
  classical
  let F:=longEdges E L
  let K:=H.deleteEdges (↑F:Set (Sym2 (Fin t)))
  let E':=restrictEdges (H.deleteEdges_le (↑F:Set (Sym2 (Fin t)))) E
  refine ⟨E', ?_, ?_⟩
  · intro e f h
    exact induced _ _ h
  · intro e
    let old:H.edgeSet:= ⟨e.val,SimpleGraph.edgeSet_mono (H.deleteEdges_le _) e.property⟩
    have he:e.val∉ F:=by
      have h:e.val∈ H.edgeSet \ (↑F:Set (Sym2 (Fin t))):=by
        simpa only [SimpleGraph.edgeSet_deleteEdges] using e.property
      exact h.2
    have hshort:(E.route old).card≤ L:=by
      by_contra h
      have hlong:L < (E.route old).card:=by omega
      exact he ((longEdges_mem E L old).mpr hlong)
    exact hshort

end Lax263307Proofs.RoutePruning

end

section

namespace Lax263307Proofs.ConditionalRoutes

open Lax263307.RouteDistributions Lax263307.ConditionalRoutes

theorem conditional_correct {n q:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (u v:Fin n):
    (∀ i,0≤ conditional D u v i)∧ (∑ i,conditional D u v i)=1∧
      (∀ i,0 < conditional D u v i→ (D.route i).head?=some u∧
        (D.route i).getLast?=some v∧ (D.route i).Nodup∧ (D.route i).IsChain G.Adj):=by
  classical
  have hpositive:(0:ℝ) < (n:ℝ) ^ 2:=by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold conditional
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (D.nonnegative i)
    · rfl
  · have heq (i:Fin q):conditional D u v i=(n:ℝ) ^ 2 *
        (if (D.route i).head?=some u∧ (D.route i).getLast?=some v then D.probability i else 0):=by
      unfold conditional
      split_ifs <;> simp
    simp_rw [heq]
    rw [← Finset.mul_sum,D.uniform]
    exact mul_div_cancel₀ 1 (ne_of_gt hpositive)
  · intro i hi
    unfold conditional at hi
    split_ifs at hi with h
    · have hp:0 < D.probability i:=(mul_pos_iff_of_pos_left hpositive).mp hi
      have hv:=D.valid i hp
      exact ⟨h.1,h.2,hv.1,hv.2.1⟩
    · exact (lt_irrefl _ hi).elim

theorem mixture_identity {n q:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (i:Fin q):
    (∑ u, ∑ v,conditional D u v i)=(n:ℝ) ^ 2 * D.probability i:=by
  classical
  by_cases hp:D.probability i=0
  · simp [conditional,hp]
  · have hpositive:0 < D.probability i:=lt_of_le_of_ne (D.nonnegative i) (Ne.symm hp)
    have hne:=(D.valid i hpositive).2.2
    let u:=(D.route i).head hne
    let v:=(D.route i).getLast hne
    have hs:(D.route i).head?=some u:=List.head?_eq_some_head hne
    have ht:(D.route i).getLast?=some v:=List.getLast?_eq_some_getLast hne
    simp only [conditional,hs,ht,Option.some.injEq,ite_and]
    simp

theorem independent_pair_mixture {n q:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (i j:Fin q):
    (∑ u, ∑ v, ∑ s, ∑ t,
      conditional D u v i * conditional D s t j / (n:ℝ) ^ 4) =
        D.probability i * D.probability j:=by
  classical
  simp_rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [mixture_identity]
  simp_rw [← Finset.sum_mul]
  rw [mixture_identity]
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  field_simp

end Lax263307Proofs.ConditionalRoutes

end

section

namespace Lax263307Proofs.FiniteProductSampling

open Lax263307.FiniteProductSampling

variable {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem normalized (f:ι→ κ→ ℝ) (mass:∀ a, (∑ x,f a x)=1):
    (∑ φ:ι→ κ,weight f φ)=1:=by
  classical
  unfold weight
  rw [← Fintype.prod_sum]
  simp only [mass,Finset.prod_const_one]

theorem feature_marginal (f:ι→ κ→ ℝ) (mass:∀ a, (∑ x,f a x)=1)
    (S:Finset ι) (g:ι→ κ→ ℝ):
    (∑ φ:ι→ κ,weight f φ * ∏ a∈ S,g a (φ a)) =
      ∏ a∈ S, ∑ x,f a x * g a x:=by
  classical
  have hterm (φ:ι→ κ):weight f φ * (∏ a∈ S,g a (φ a)) =
      ∏ a,f a (φ a) * (if a∈ S then g a (φ a) else 1):=by
    rw [Finset.prod_mul_distrib,Fintype.prod_ite_mem]
    rfl
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun a x => f a x * (if a∈ S then g a x else 1))]
  have hfactor (a:ι):
      (∑ x,f a x * (if a∈ S then g a x else 1)) =
      if a∈ S then (∑ x,f a x * g a x) else 1:=by
    by_cases ha:a∈ S
    · simp [ha]
    · simp [ha,mass a]
  simp_rw [hfactor]
  exact Fintype.prod_ite_mem S _

theorem single_marginal (f:ι→ κ→ ℝ) (mass:∀ a, (∑ x,f a x)=1)
    (a:ι) (g:κ→ ℝ):
    (∑ φ:ι→ κ,weight f φ * g (φ a))=∑ x,f a x * g x:=by
  classical
  simpa using feature_marginal f mass {a} (fun _ x => g x)

theorem pair_marginal (f:ι→ κ→ ℝ) (mass:∀ a, (∑ x,f a x)=1)
    (a b:ι) (different:a ≠ b) (g h:κ→ ℝ):
    (∑ φ:ι→ κ,weight f φ * (g (φ a) * h (φ b))) =
      (∑ x,f a x * g x) * (∑ x,f b x * h x):=by
  classical
  have heq (φ:ι→ κ):(∏ c∈ ({a,b}:Finset ι),
      if c=a then g (φ c) else h (φ c))=g (φ a) * h (φ b):=by
    simp [different,Ne.symm different]
  have hm:=feature_marginal f mass {a,b} (fun c x => if c=a then g x else h x)
  simp_rw [heq] at hm
  simpa [different,Ne.symm different] using hm

theorem restriction_marginal (f:ι→ κ→ ℝ) (mass:∀ a, (∑ x,f a x)=1)
    (S:Finset ι) (H:(↥S→ κ)→ ℝ):
    (∑ φ:ι→ κ,weight f φ * H (fun a:↥S => φ a)) =
      ∑ ψ:↥S→ κ,weight (fun a:↥S => f a) ψ * H ψ:=by
  classical
  let e:=Equiv.piEquivPiSubtypeProd (fun a:ι => a∈ S) (fun _ => κ)
  have hsplit (ψ:↥S→ κ) (ξ:{a:ι // a∉ S}→ κ):
      weight f (e.symm (ψ,ξ))=weight (fun a:↥S => f a) ψ *
        weight (fun a:{a:ι // a∉ S} => f a) ξ:=by
    unfold weight
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun a:ι => a∈ S)]
    congr 1 <;> apply Finset.prod_congr (by ext; simp) <;> intro a _ <;>
      simp [e,Equiv.piEquivPiSubtypeProd,a.property]
  have heval (ψ:↥S→ κ) (ξ:{a:ι // a∉ S}→ κ):
      (fun a:↥S => e.symm (ψ,ξ) a)=ψ:=by
    funext a
    simp [e,Equiv.piEquivPiSubtypeProd,a.property]
  rw [← e.symm.sum_comp (fun φ => weight f φ * H (fun a:↥S => φ a))]
  simp only [Fintype.sum_prod_type]
  simp_rw [hsplit,heval]
  apply Finset.sum_congr rfl
  intro ψ _
  have hterm (ξ:{a:ι // a∉ S}→ κ):
      weight (fun a:↥S => f a) ψ * weight (fun a:{a:ι // a∉ S} => f a) ξ * H ψ =
      (weight (fun a:↥S => f a) ψ * H ψ) * weight (fun a:{a:ι // a∉ S} => f a) ξ:=by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hm:=normalized (fun a:{a:ι // a∉ S} => f a) (fun a => mass a)
  rw [hm,mul_one]

theorem embedding_marginal {k:ℕ} (f:ι→ κ→ ℝ)
    (mass:∀ a, (∑ x,f a x)=1) (j:Fin k ↪ ι) (H:(Fin k→ κ)→ ℝ):
    (∑ φ:ι→ κ,weight f φ * H (fun a => φ (j a))) =
      ∑ ψ:Fin k→ κ,weight (fun a => f (j a)) ψ * H ψ:=by
  classical
  let S:=Finset.univ.map j
  let a:Fin k→ ↥S:=fun b => ⟨j b,Finset.mem_map.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩
  have ha:Function.Bijective a:=by
    constructor
    · intro b c h
      exact j.injective (congrArg Subtype.val h)
    · rintro ⟨c,hc⟩
      obtain ⟨b,_,hb⟩:=Finset.mem_map.mp hc
      exact ⟨b,Subtype.ext hb⟩
  let e:Fin k ≃ ↥S:=Equiv.ofBijective a ha
  let A:(Fin k→ κ) ≃ (↥S→ κ):=Equiv.arrowCongr e (Equiv.refl κ)
  have hev (ψ:Fin k→ κ) (b:Fin k):A ψ (e b)=ψ b:=by simp [A]
  have hw (ψ:Fin k→ κ):
      weight (fun b:↥S => f b) (A ψ)=weight (fun b => f (j b)) ψ:=by
    unfold weight
    rw [← e.prod_comp (fun b:↥S => f b (A ψ b))]
    apply Finset.prod_congr rfl
    intro b _
    rw [hev]
    rfl
  have h:=restriction_marginal f mass S (fun ψ => H (fun b => ψ (a b)))
  change (∑ φ:ι→ κ,weight f φ * H (fun b => φ (j b)))=_ at h
  rw [h]
  symm
  apply Fintype.sum_equiv A
  intro ψ
  rw [hw]
  congr 1
  apply congrArg H
  funext b
  exact (hev ψ b).symm

end Lax263307Proofs.FiniteProductSampling

end

section

namespace Lax263307Proofs.CoupledRouteSampling

open Lax263307.RouteDistributions Lax263307.ConditionalRoutes
open Lax263307.FiniteProductSampling
open Lax263307Proofs.FiniteProductSampling (single_marginal pair_marginal)
open Lax263307.CoupledRouteSampling

theorem uniform_mass {n:ℕ} (hn:0 < n):(∑ x,uniformWeight n x)=1:=by
  simp [uniformWeight]
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  field_simp

theorem joint_normalized {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t):
    (∀ φ ψ,0≤ jointWeight D a b φ ψ)∧
      (∑ φ, ∑ ψ,jointWeight D a b φ ψ)=1:=by
  classical
  have hcond (φ:Fin t→ Fin n) (e:Fin m):=Lax263307Proofs.ConditionalRoutes.conditional_correct D hn (φ (a e)) (φ (b e))
  refine ⟨?_, ?_⟩
  · intro φ ψ
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro e _
      exact div_nonneg zero_le_one (by positivity)
    · apply Finset.prod_nonneg
      intro e _
      exact (hcond φ e).1 _
  · unfold jointWeight
    simp_rw [← Finset.mul_sum,Lax263307Proofs.FiniteProductSampling.normalized _ (fun e => (hcond _ e).2.1),mul_one]
    exact Lax263307Proofs.FiniteProductSampling.normalized _ (fun _ => uniform_mass hn)

theorem joint_valid {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t)
    (φ:Fin t→ Fin n) (ψ:Fin m→ Fin q) (positive:0 < jointWeight D a b φ ψ):
    ∀ e, (D.route (ψ e)).head?=some (φ (a e))∧
      (D.route (ψ e)).getLast?=some (φ (b e))∧
      (D.route (ψ e)).Nodup∧ (D.route (ψ e)).IsChain G.Adj:=by
  classical
  intro e
  have hprod:weight (fun e => conditional D (φ (a e)) (φ (b e))) ψ ≠ 0:=
    (mul_ne_zero_iff.mp (ne_of_gt positive)).2
  have he:conditional D (φ (a e)) (φ (b e)) (ψ e) ≠ 0:=
    Finset.prod_ne_zero_iff.mp hprod e (Finset.mem_univ _)
  have hc:=Lax263307Proofs.ConditionalRoutes.conditional_correct D hn (φ (a e)) (φ (b e))
  exact hc.2.2 (ψ e) (lt_of_le_of_ne (hc.1 _) (Ne.symm he))

theorem sum_two {κ:Type*} [Fintype κ] (h:(Fin 2→ κ)→ ℝ):
    (∑ ψ,h ψ)=∑ u, ∑ v,h ![u,v]:=by
  rw [← (finTwoArrowEquiv κ).symm.sum_comp h]
  simp only [Fintype.sum_prod_type]
  rfl

theorem single_edge_law {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t)
    (e:Fin m) (nonloop:a e ≠ b e) (i:Fin q):
    (∑ φ, ∑ ψ,jointWeight D a b φ ψ * (if ψ e=i then (1:ℝ) else 0)) =
      D.probability i:=by
  classical
  have hinner (φ:Fin t→ Fin n):
      (∑ ψ,jointWeight D a b φ ψ * (if ψ e=i then (1:ℝ) else 0)) =
      weight (fun _:Fin t => uniformWeight n) φ * conditional D (φ (a e)) (φ (b e)) i:=by
    unfold jointWeight
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [single_marginal _ (fun c => (Lax263307Proofs.ConditionalRoutes.conditional_correct D hn _ _).2.1) e
      (fun x => if x=i then (1:ℝ) else 0)]
    simp
  simp_rw [hinner]
  let j:Fin 2 ↪ Fin t:= ⟨![a e,b e],by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all⟩
  have hp:=Lax263307Proofs.FiniteProductSampling.embedding_marginal (fun _:Fin t => uniformWeight n)
    (fun _ => uniform_mass hn) j (fun ψ => conditional D (ψ 0) (ψ 1) i)
  change (∑ φ,weight (fun _:Fin t => uniformWeight n) φ *
    conditional D (φ (a e)) (φ (b e)) i)=_ at hp
  rw [hp,sum_two]
  simp only [weight,Fin.prod_univ_two,uniformWeight,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hm:=Lax263307Proofs.ConditionalRoutes.mixture_identity D i
  simp_rw [← Finset.mul_sum]
  rw [hm]
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  field_simp

theorem sum_four {κ:Type*} [Fintype κ] (h:(Fin 4→ κ)→ ℝ):
    (∑ ψ,h ψ)=∑ u, ∑ v, ∑ s, ∑ t,h ![u,v,s,t]:=by
  let e:(κ × κ) × (κ × κ) ≃ (Fin 4→ κ):=
    (Equiv.prodCongr (finTwoArrowEquiv κ).symm (finTwoArrowEquiv κ).symm).trans (Fin.appendEquiv 2 2)
  have he (u v s t:κ):e ((u,v), (s,t))=![u,v,s,t]:=by
    funext i
    fin_cases i <;> rfl
  rw [← e.sum_comp h]
  simp only [Fintype.sum_prod_type]
  simp_rw [he]

theorem nonincident_edge_law {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t)
    (e f:Fin m) (nonincident:Function.Injective ![a e,b e,a f,b f]) (i j:Fin q):
    (∑ φ, ∑ ψ,jointWeight D a b φ ψ *
      ((if ψ e=i then (1:ℝ) else 0) * (if ψ f=j then (1:ℝ) else 0))) =
      D.probability i * D.probability j:=by
  classical
  have hef:e ≠ f:=by
    intro h
    have hi:(0:Fin 4)=2:=nonincident (by simp [h])
    exact (by decide:(0:Fin 4) ≠ 2) hi
  have hinner (φ:Fin t→ Fin n):
      (∑ ψ,jointWeight D a b φ ψ *
        ((if ψ e=i then (1:ℝ) else 0) * (if ψ f=j then (1:ℝ) else 0))) =
      weight (fun _:Fin t => uniformWeight n) φ *
        (conditional D (φ (a e)) (φ (b e)) i * conditional D (φ (a f)) (φ (b f)) j):=by
    unfold jointWeight
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [pair_marginal _ (fun c => (Lax263307Proofs.ConditionalRoutes.conditional_correct D hn _ _).2.1) e f hef
      (fun x => if x=i then (1:ℝ) else 0) (fun x => if x=j then (1:ℝ) else 0)]
    simp
  simp_rw [hinner]
  let J:Fin 4 ↪ Fin t:= ⟨![a e,b e,a f,b f],nonincident⟩
  have hp:=Lax263307Proofs.FiniteProductSampling.embedding_marginal (fun _:Fin t => uniformWeight n)
    (fun _ => uniform_mass hn) J (fun ψ => conditional D (ψ 0) (ψ 1) i * conditional D (ψ 2) (ψ 3) j)
  change (∑ φ,weight (fun _:Fin t => uniformWeight n) φ *
    (conditional D (φ (a e)) (φ (b e)) i * conditional D (φ (a f)) (φ (b f)) j))=_ at hp
  rw [hp,sum_four]
  simp only [weight,uniformWeight,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  have hterm (u v s t:Fin n):
      (1 / (n:ℝ)) ^ 4 * (conditional D u v i * conditional D s t j) =
      conditional D u v i * conditional D s t j / (n:ℝ) ^ 4:=by ring
  simp_rw [hterm]
  exact Lax263307Proofs.ConditionalRoutes.independent_pair_mixture D hn i j

end Lax263307Proofs.CoupledRouteSampling

end

section

namespace Lax263307Proofs.SamplingOutcomes

open Lax263307.PathSampling Lax263307.SamplingOutcomes

theorem event_union_bound {n q:ℕ} (P:Distribution n q) (A B:Set (Fin q)):
    eventProbability P (A ∪ B)≤ eventProbability P A + eventProbability P B:=by
  classical
  unfold eventProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases ha:i∈ A <;> by_cases hb:i∈ B <;> simp [ha,hb,P.nonnegative i]

theorem event_complement {n q:ℕ} (P:Distribution n q) (A:Set (Fin q)):
    eventProbability P Aᶜ=1 - eventProbability P A:=by
  classical
  have heq:eventProbability P Aᶜ + eventProbability P A=1:=by
    unfold eventProbability
    rw [← Finset.sum_add_distrib, ← P.normalized]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:i∈ A <;> simp [hi]
  linarith

theorem markov_bound {n q:ℕ} (P:Distribution n q) (cost:Fin q→ ℝ)
    (nonnegative:∀ i,0≤ cost i) (T:ℝ) (positive:0 < T):
    eventProbability P {i | T < cost i}≤ (∑ i,P.probability i * cost i) / T:=by
  classical
  apply (le_div_iff₀ positive).mpr
  unfold eventProbability
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  change (if T < cost i then P.probability i else 0) * T≤ P.probability i * cost i
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h.le (P.nonnegative i)
  · simpa using mul_nonneg (P.nonnegative i) (nonnegative i)

theorem good_outcome {n q:ℕ} (P:Distribution n q) (bad:Set (Fin q))
    (cost:Fin q→ ℝ) (M:ℝ) (positive:0 < M)
    (nonnegative:∀ i,0≤ cost i)
    (bad_bound:eventProbability P bad≤ 1 / 4)
    (expected_bound:(∑ i,P.probability i * cost i)≤ M):
    ∃ i,0 < P.probability i∧ i∉ bad∧ cost i≤ 4 * M:=by
  classical
  let expensive:Set (Fin q):= {i | 4 * M < cost i}
  have hcost:eventProbability P expensive≤ 1 / 4:=by
    calc
      eventProbability P expensive≤ (∑ i,P.probability i * cost i) / (4 * M):=
        Lax263307Proofs.SamplingOutcomes.markov_bound P cost nonnegative (4 * M) (by positivity)
      _≤ M / (4 * M):=div_le_div_of_nonneg_right expected_bound (by positivity)
      _=1 / 4:=by field_simp
  have hbad:eventProbability P (bad ∪ expensive)≤ 1 / 2:=by
    have hu:=event_union_bound P bad expensive
    linarith
  have hgood:0 < eventProbability P (bad ∪ expensive)ᶜ:=by
    rw [event_complement]
    linarith
  unfold eventProbability at hgood
  obtain ⟨i,_,hi⟩:=Finset.exists_lt_of_sum_lt
    (show (∑ _i:Fin q, (0:ℝ)) <
      ∑ i,if i∈ (bad ∪ expensive)ᶜ then P.probability i else 0 from by simpa using hgood)
  by_cases hmem:i∈ (bad ∪ expensive)ᶜ
  · rw [if_pos hmem] at hi
    have hnb:i∉ bad:=fun hb => hmem (Or.inl hb)
    have hnc:cost i≤ 4 * M:=le_of_not_gt (fun hc => hmem (Or.inr hc))
    exact ⟨i,hi,hnb,hnc⟩
  · simp only [if_neg hmem,lt_self_iff_false] at hi

end Lax263307Proofs.SamplingOutcomes

end

section

namespace Lax263307Proofs.CoupledSamplingBounds

open Lax263307.RouteDistributions Lax263307.CoupledRouteSampling Lax263307.CoupledSamplingBounds

variable {Ω I J:Type*} [Fintype Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem integrate_single (w:Ω→ ℝ) (X:Ω→ I) (p:I→ ℝ)
    (law:∀ i, (∑ ω,w ω * (if X ω=i then (1:ℝ) else 0))=p i)
    (h:I→ ℝ):(∑ ω,w ω * h (X ω))=∑ i,p i * h i:=by
  classical
  have hterm (ω:Ω):w ω * h (X ω) =
      ∑ i,w ω * (if X ω=i then (1:ℝ) else 0) * h i:=by
    simp [mul_ite,eq_comm]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,law]

theorem integrate_pair (w:Ω→ ℝ) (X:Ω→ I) (Y:Ω→ J) (p:I→ ℝ) (r:J→ ℝ)
    (law:∀ i j, (∑ ω,w ω * ((if X ω=i then (1:ℝ) else 0) *
      (if Y ω=j then (1:ℝ) else 0)))=p i * r j)
    (h:I→ J→ ℝ):
    (∑ ω,w ω * h (X ω) (Y ω))=∑ i, ∑ j, (p i * r j) * h i j:=by
  classical
  have hterm (ω:Ω):w ω * h (X ω) (Y ω) =
      ∑ i, ∑ j,w ω * ((if X ω=i then (1:ℝ) else 0) *
        (if Y ω=j then (1:ℝ) else 0)) * h i j:=by
    simp [mul_ite,eq_comm]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,law]

theorem single_edge_expectation {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t)
    (e:Fin m) (nonloop:a e ≠ b e) (h:Fin q→ ℝ):
    (∑ φ, ∑ ψ,jointWeight D a b φ ψ * h (ψ e))=∑ i,D.probability i * h i:=by
  classical
  have law (i:Fin q):
      (∑ ω:(Fin t→ Fin n) × (Fin m→ Fin q),
        jointWeight D a b ω.1 ω.2 * (if ω.2 e=i then (1:ℝ) else 0))=D.probability i:=by
    simp only [Fintype.sum_prod_type]
    exact Lax263307Proofs.CoupledRouteSampling.single_edge_law D hn a b e nonloop i
  simpa only [Fintype.sum_prod_type] using integrate_single
    (fun ω:(Fin t→ Fin n) × (Fin m→ Fin q) => jointWeight D a b ω.1 ω.2)
    (fun ω => ω.2 e) D.probability law h

theorem nonincident_edge_expectation {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t)
    (e f:Fin m) (nonincident:Function.Injective ![a e,b e,a f,b f]) (h:Fin q→ Fin q→ ℝ):
    (∑ φ, ∑ ψ,jointWeight D a b φ ψ * h (ψ e) (ψ f)) =
      ∑ i, ∑ j, (D.probability i * D.probability j) * h i j:=by
  classical
  have law (i j:Fin q):
      (∑ ω:(Fin t→ Fin n) × (Fin m→ Fin q),jointWeight D a b ω.1 ω.2 *
        ((if ω.2 e=i then (1:ℝ) else 0) * (if ω.2 f=j then (1:ℝ) else 0))) =
          D.probability i * D.probability j:=by
    simp only [Fintype.sum_prod_type]
    exact Lax263307Proofs.CoupledRouteSampling.nonincident_edge_law D hn a b e f nonincident i j
  simpa only [Fintype.sum_prod_type] using integrate_pair
    (fun ω:(Fin t→ Fin n) × (Fin m→ Fin q) => jointWeight D a b ω.1 ω.2)
    (fun ω => ω.2 e) (fun ω => ω.2 f) D.probability D.probability law h

theorem total_length_expectation {n q t m:ℕ} {G:SimpleGraph (Fin n)}
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t)
    (nonloop:∀ e,a e ≠ b e):
    (∑ φ, ∑ ψ,jointWeight D a b φ ψ * (∑ e, ((D.route (ψ e)).toFinset.card:ℝ))) =
      (m:ℝ) * Lax263307.PathSampling.expectedSize D.toSampling:=by
  classical
  simp_rw [Finset.mul_sum]
  conv_lhs => arg 2; ext φ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [single_edge_expectation D hn a b _ (nonloop _) (fun i => ((D.route i).toFinset.card:ℝ))]
  simp [Lax263307.PathSampling.expectedSize,Distribution.toSampling,nsmul_eq_mul]

theorem interaction_bound {n q:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D:Distribution G q):
    (∑ i, ∑ j, (D.probability i * D.probability j) * (if Interaction G D i j then (1:ℝ) else 0))≤
      Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling:=by
  classical
  unfold Lax263307.PathSampling.collisionProbability Lax263307.PathSampling.adjacencyProbability Distribution.toSampling
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  change (D.probability i * D.probability j) * (if Interaction G D i j then 1 else 0)≤
    (if ¬Disjoint (D.route i).toFinset (D.route j).toFinset then D.probability i * D.probability j else 0) +
    (if ∃ u∈ (D.route i).toFinset, ∃ v∈ (D.route j).toFinset,G.Adj u v then D.probability i * D.probability j else 0)
  have hp:=mul_nonneg (D.nonnegative i) (D.nonnegative j)
  by_cases hd:Disjoint (D.route i).toFinset (D.route j).toFinset <;>
    by_cases ha:∃ u∈ (D.route i).toFinset, ∃ v∈ (D.route j).toFinset,G.Adj u v <;>
    simp only [Interaction,hd,ha,not_true_eq_false,not_false_eq_true,false_or,true_or,
      if_true,if_false,mul_one,mul_zero] <;> linarith

theorem union_bound (w:Ω→ ℝ) (nonnegative:∀ ω,0≤ w ω) (E:J→ Ω→ Prop):
    (by classical exact ∑ ω,if ∃ j,E j ω then w ω else 0)≤
      (by classical exact ∑ j, ∑ ω,if E j ω then w ω else 0):=by
  classical
  have hterm (ω:Ω):(if ∃ j,E j ω then w ω else 0)≤ ∑ j,if E j ω then w ω else 0:=by
    by_cases h:∃ j,E j ω
    · obtain ⟨j,hj⟩:=h
      rw [if_pos ⟨j,hj⟩]
      have hs:=Finset.single_le_sum (f:=fun j => if E j ω then w ω else 0)
        (fun j _ => by split_ifs <;> first | exact nonnegative ω | exact le_refl 0) (Finset.mem_univ j)
      simpa only [if_pos hj] using hs
    · rw [if_neg h]
      apply Finset.sum_nonneg
      intro j _
      split_ifs <;> first | exact nonnegative ω | exact le_refl 0
  calc
    _≤ ∑ ω, ∑ j,if E j ω then w ω else 0:=Finset.sum_le_sum fun ω _ => hterm ω
    _=_:=Finset.sum_comm

theorem bad_probability_bound {n q t m:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t):
    badProbability G D a b≤ (m:ℝ) ^ 2 *
      (Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling):=by
  classical
  let Ω:=(Fin t→ Fin n) × (Fin m→ Fin q)
  let w:Ω→ ℝ:=fun ω => jointWeight D a b ω.1 ω.2
  let E:(Fin m × Fin m)→ Ω→ Prop:=fun ef ω =>
    Function.Injective ![a ef.1,b ef.1,a ef.2,b ef.2]∧ Interaction G D (ω.2 ef.1) (ω.2 ef.2)
  have hnneg:=(Lax263307Proofs.CoupledRouteSampling.joint_normalized D hn a b).1
  have hu:=union_bound w (fun ω => hnneg _ _) E
  have hbad:badProbability G D a b≤ ∑ ef:Fin m × Fin m, ∑ ω:Ω,
      if E ef ω then w ω else 0:=by
    simpa only [Ω,E,w,badProbability,Fintype.sum_prod_type,Prod.exists] using hu
  have hpair (ef:Fin m × Fin m):(∑ ω:Ω,if E ef ω then w ω else 0)≤
      Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling:=by
    by_cases hi:Function.Injective ![a ef.1,b ef.1,a ef.2,b ef.2]
    · have heq:(∑ ω:Ω,if E ef ω then w ω else 0) =
          ∑ φ, ∑ ψ,jointWeight D a b φ ψ *
            (if Interaction G D (ψ ef.1) (ψ ef.2) then (1:ℝ) else 0):=by
        simp [Ω,E,w,Fintype.sum_prod_type,hi,mul_ite]
      rw [heq,nonincident_edge_expectation D hn a b _ _ hi (fun i j => if Interaction G D i j then (1:ℝ) else 0)]
      exact interaction_bound G D
    · have hz:(∑ ω:Ω,if E ef ω then w ω else 0)=0:=by simp [E,hi]
      rw [hz]
      apply le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) (interaction_bound G D)
      split_ifs <;> simp only [mul_one,mul_zero] <;>
        first | exact mul_nonneg (D.nonnegative _) (D.nonnegative _) | exact le_refl 0
  calc
    _≤ ∑ ef:Fin m × Fin m, ∑ ω:Ω,if E ef ω then w ω else 0:=hbad
    _≤ ∑ _ef:Fin m × Fin m,
        (Lax263307.PathSampling.collisionProbability D.toSampling +
          Lax263307.PathSampling.adjacencyProbability G D.toSampling):=
      Finset.sum_le_sum fun ef _ => hpair ef
    _=_:=by simp [sq,nsmul_eq_mul]; ring

theorem finite_good_outcome (w:Ω→ ℝ) (nonnegative:∀ ω,0≤ w ω)
    (normalized:(∑ ω,w ω)=1) (bad:Ω→ Prop) (cost:Ω→ ℝ)
    (cost_nonnegative:∀ ω,0≤ cost ω) (M:ℝ) (positive:0 < M)
    (bad_bound:(by classical exact ∑ ω,if bad ω then w ω else 0)≤ (1 / 4:ℝ))
    (expected_bound:(∑ ω,w ω * cost ω)≤ M):
    ∃ ω,0 < w ω∧ ¬bad ω∧ cost ω≤ 4 * M:=by
  classical
  let q:=Fintype.card Ω
  let e:Ω ≃ Fin q:=Fintype.equivFin Ω
  let P:Lax263307.PathSampling.Distribution 0 q:= {
    probability:=fun i => w (e.symm i)
    nonnegative:=fun i => nonnegative _
    normalized:=(e.symm.sum_comp w).trans normalized
    vertices:=fun _ => ∅ }
  have hbad:Lax263307.SamplingOutcomes.eventProbability P {i | bad (e.symm i)}≤ 1 / 4:=by
    unfold Lax263307.SamplingOutcomes.eventProbability
    change (∑ i,if bad (e.symm i) then w (e.symm i) else 0)≤ _
    rw [e.symm.sum_comp (fun ω => if bad ω then w ω else 0)]
    exact bad_bound
  have hexpected:(∑ i,P.probability i * cost (e.symm i))≤ M:=by
    change (∑ i, (fun ω => w ω * cost ω) (e.symm i))≤ M
    exact (e.symm.sum_comp (fun ω => w ω * cost ω)).trans_le expected_bound
  obtain ⟨i,hi,hgood,hcost⟩:=Lax263307Proofs.SamplingOutcomes.good_outcome P
    {i | bad (e.symm i)} (fun i => cost (e.symm i)) M positive
      (fun i => cost_nonnegative _) hbad hexpected
  exact ⟨e.symm i,hi,hgood,hcost⟩

theorem good_route_sample {n q t m:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D:Distribution G q) (hn:0 < n) (a b:Fin m→ Fin t) (nonloop:∀ e,a e ≠ b e)
    (M:ℝ) (positive:0 < M)
    (bad_budget:(m:ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling)≤ 1 / 4)
    (length_budget:(m:ℝ) * Lax263307.PathSampling.expectedSize D.toSampling≤ M):
    ∃ φ:Fin t→ Fin n, ∃ ψ:Fin m→ Fin q,
      0 < jointWeight D a b φ ψ∧
      (∀ e f,Function.Injective ![a e,b e,a f,b f]→ ¬Interaction G D (ψ e) (ψ f))∧
      (∑ e, ((D.route (ψ e)).toFinset.card:ℝ))≤ 4 * M:=by
  classical
  let Ω:=(Fin t→ Fin n) × (Fin m→ Fin q)
  let w:Ω→ ℝ:=fun ω => jointWeight D a b ω.1 ω.2
  let bad:Ω→ Prop:=fun ω =>
    ∃ e f,Function.Injective ![a e,b e,a f,b f]∧ Interaction G D (ω.2 e) (ω.2 f)
  let cost:Ω→ ℝ:=fun ω => ∑ e, ((D.route (ω.2 e)).toFinset.card:ℝ)
  have hnneg:=Lax263307Proofs.CoupledRouteSampling.joint_normalized D hn a b
  have hnormalized:(∑ ω:Ω,w ω)=1:=by
    simpa only [Ω,w,Fintype.sum_prod_type] using hnneg.2
  have hbad:(∑ ω:Ω,if bad ω then w ω else 0)≤ 1 / 4:=by
    have h:=(Lax263307Proofs.CoupledSamplingBounds.bad_probability_bound G D hn a b).trans bad_budget
    simpa only [badProbability,Ω,bad,w,Fintype.sum_prod_type] using h
  have hexpected:(∑ ω:Ω,w ω * cost ω)≤ M:=by
    simpa only [Ω,w,cost,Fintype.sum_prod_type,Lax263307Proofs.CoupledSamplingBounds.total_length_expectation D hn a b nonloop] using length_budget
  obtain ⟨ω,hp,hg,hc⟩:=finite_good_outcome w (fun ω => hnneg.1 _ _) hnormalized bad cost
    (fun ω => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) M positive
    (by
      convert hbad using 1
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h:bad ω <;> simp [h]) hexpected
  refine ⟨ω.1,ω.2,hp, ?_,hc⟩
  intro e f hef hint
  exact hg ⟨e,f,hef,hint⟩

end Lax263307Proofs.CoupledSamplingBounds

end

section

namespace Lax263307Proofs.SampledAlmostEmbeddings

open Lax263307.RouteDistributions Lax263307.CoupledRouteSampling Lax263307.CoupledSamplingBounds
open Lax263307.AlmostEmbeddings

theorem route_connected {n:ℕ} (G:SimpleGraph (Fin n)) (Q:List (Fin n))
    (nonempty:Q ≠ []) (chain:Q.IsChain G.Adj):
    (G.induce (↑Q.toFinset:Set (Fin n))).Connected:=by
  let W:=SimpleGraph.Walk.ofSupport Q nonempty chain
  have h:=W.connected_induce_support
  have hs:W.support=Q:=SimpleGraph.Walk.support_ofSupport nonempty chain
  rw [hs] at h
  have hset:(↑Q.toFinset:Set (Fin n))={v | v∈ Q}:=by ext v; simp
  rwa [← hset] at h

theorem edge_endpoints_distinct {t:ℕ} (H:SimpleGraph (Fin t)) (e:H.edgeSet):
    e.val.out.1 ≠ e.val.out.2:=by
  have h:H.Adj e.val.out.1 e.val.out.2:=by
    change s(e.val.out.1,e.val.out.2)∈ H.edgeSet
    have heq:e.val=s(e.val.out.1,e.val.out.2):=e.val.out_eq.symm
    rw [← heq]
    exact e.property
  exact H.ne_of_adj h

theorem disjoint_endpoints {t:ℕ} (H:SimpleGraph (Fin t)) (e f:H.edgeSet)
    (disjoint:Disjoint e.val.toFinset f.val.toFinset):
    Function.Injective ![e.val.out.1,e.val.out.2,f.val.out.1,f.val.out.2]:=by
  classical
  have hxy:=edge_endpoints_distinct H e
  have huv:=edge_endpoints_distinct H f
  have he₁:e.val.out.1∈ e.val.toFinset:=Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)
  have he₂:e.val.out.2∈ e.val.toFinset:=Sym2.mem_toFinset.mpr (Sym2.out_snd_mem _)
  have hf₁:f.val.out.1∈ f.val.toFinset:=Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)
  have hf₂:f.val.out.2∈ f.val.toFinset:=Sym2.mem_toFinset.mpr (Sym2.out_snd_mem _)
  have cross (x y:Fin t) (hx:x∈ e.val.toFinset) (hy:y∈ f.val.toFinset):x ≠ y:=by
    intro h
    subst y
    exact Finset.disjoint_left.mp disjoint hx hy
  have h₁:=cross _ _ he₁ hf₁
  have h₂:=cross _ _ he₁ hf₂
  have h₃:=cross _ _ he₂ hf₁
  have h₄:=cross _ _ he₂ hf₂
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem exists_induced_almost_embedding {t n q:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (D:Distribution G q) (hn:0 < n)
    (M:ℝ) (positive:0 < M)
    (bad_budget:(H.edgeSet.ncard:ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling)≤ 1 / 4)
    (length_budget:(H.edgeSet.ncard:ℝ) * Lax263307.PathSampling.expectedSize D.toSampling≤ M):
    ∃ E:AlmostEmbedding H G,IsInduced E∧ (∑ e, ((E.route e).card:ℝ))≤ 4 * M:=by
  classical
  let m:=Fintype.card H.edgeSet
  let idx:H.edgeSet ≃ Fin m:=Fintype.equivFin H.edgeSet
  let a:Fin m→ Fin t:=fun i => (idx.symm i).val.out.1
  let b:Fin m→ Fin t:=fun i => (idx.symm i).val.out.2
  have hedgecard:m=H.edgeSet.ncard:=Set.fintypeCard_eq_ncard H.edgeSet
  have nonloop (i:Fin m):a i ≠ b i:=edge_endpoints_distinct H (idx.symm i)
  have hbad:(m:ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling)≤ 1 / 4:=by simpa [hedgecard] using bad_budget
  have hlen:(m:ℝ) * Lax263307.PathSampling.expectedSize D.toSampling≤ M:=by simpa [hedgecard] using length_budget
  obtain ⟨φ,ψ,hp,hgood,hcost⟩:=Lax263307Proofs.CoupledSamplingBounds.good_route_sample G D hn a b nonloop M positive hbad hlen
  have hvalid:=Lax263307Proofs.CoupledRouteSampling.joint_valid D hn a b φ ψ hp
  let E:AlmostEmbedding H G:= {
    vertexMap:=φ
    route:=fun e => (D.route (ψ (idx e))).toFinset
    connected:=by
      intro e
      have h:=hvalid (idx e)
      have hne:D.route (ψ (idx e)) ≠ []:=by intro hn; simp [hn] at h
      exact route_connected G _ hne h.2.2.2
    endpoints:=by
      intro e v hv
      have hev:v=e.val.out.1∨ v=e.val.out.2:=by
        rw [← e.val.out_eq] at hv
        exact Sym2.mem_iff.mp hv
      have h:=hvalid (idx e)
      rcases hev with rfl | rfl
      · apply List.mem_toFinset.mpr
        have hs:(D.route (ψ (idx e))).head?=some (φ e.val.out.1):=by simpa [a] using h.1
        exact List.mem_of_head? hs
      · apply List.mem_toFinset.mpr
        have hs:(D.route (ψ (idx e))).getLast?=some (φ e.val.out.2):=by simpa [b] using h.2.1
        exact List.mem_of_getLast? hs
    disjoint:=by
      intro e f hef
      have hi:Function.Injective ![a (idx e),b (idx e),a (idx f),b (idx f)]:=by
        simpa [a,b] using disjoint_endpoints H e f hef
      exact not_not.mp ((not_or.mp (hgood (idx e) (idx f) hi)).1) }
  refine ⟨E, ?_, ?_⟩
  · intro e f hef u hu v hv huv
    have hi:Function.Injective ![a (idx e),b (idx e),a (idx f),b (idx f)]:=by
      simpa [a,b] using disjoint_endpoints H e f hef
    exact (not_or.mp (hgood (idx e) (idx f) hi)).2 ⟨u,hu,v,hv,huv⟩
  · have hsum:(∑ e:H.edgeSet, ((E.route e).card:ℝ)) =
        ∑ i:Fin m, ((D.route (ψ i)).toFinset.card:ℝ):=by
      exact Fintype.sum_equiv idx _ _ (fun e => rfl)
    rw [hsum]
    exact hcost

end Lax263307Proofs.SampledAlmostEmbeddings

end

section

namespace Lax263307Proofs.InducedEmbeddingWidth

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges Lax228581.Treewidth
open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth

theorem transfer_class_bound {t n:ℕ} (C:GraphClass) (hereditary:IsHereditary C)
    (W:ℕ→ ℕ) (monotone:Monotone W) (class_bound:HasBagBound C W)
    (H:SimpleGraph (Fin t)) [DecidableRel H.Adj] (G:SimpleGraph (Fin n))
    (member:G∈ C n) (E:AlmostEmbedding H G) (induced:IsInduced E) (d L:ℕ)
    (degree_bound:∀ v,H.degree v≤ d) (length_bound:∀ e, (E.route e).card≤ L):
    ∃ D:TreeDecomposition H, ∀ i, (D.bag i).card≤
      max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)):=by
  classical
  by_cases hu:(routeUnion E).Nonempty
  · obtain ⟨r,K,f,E',hE',hcards,hcount⟩:=
      Lax263307Proofs.HostRestriction.restrict_to_route_union H G E induced hu
    have hK:K∈ C r:=hereditary r n K G member ⟨f⟩
    have hsmall:K.edgeSet.ncard≤ d * H.edgeSet.ncard * L ^ 2:=by
      rw [hcount]
      exact Lax263307Proofs.InducedRouteEdges.edge_bound H G E d L induced degree_bound length_bound
    obtain ⟨DK,hDK⟩:=class_bound r K hK
    have hbags:∀ i, (DK.bag i).card≤ W (d * H.edgeSet.ncard * L ^ 2):=
      fun i => (hDK i).trans (monotone hsmall)
    exact Lax263307Proofs.IsolatedEmbeddingTransfer.transfer_decomposition H K E' d _ degree_bound DK hbags
  · have he:routeUnion E=∅:=Finset.not_nonempty_iff_eq_empty.mp hu
    have isolated (v:Fin t):H.IsIsolated v:=by
      intro u huv
      let e:H.edgeSet:= ⟨s(v,u),huv⟩
      have hr:E.vertexMap v∈ routeUnion E:=Finset.mem_biUnion.mpr
        ⟨e,Finset.mem_univ _,E.endpoints e v (Sym2.mem_mk_left _ _)⟩
      simp [he] at hr
    have zero_degree (v:Fin t):H.degree v≤ 0:=by
      rw [(H.degree_eq_zero v).mpr (isolated v)]
    obtain ⟨DG,hDG⟩:=class_bound n G member
    obtain ⟨DH,hDH⟩:=Lax263307Proofs.IsolatedEmbeddingTransfer.transfer_decomposition H G E 0 _ zero_degree DG hDG
    refine ⟨DH, ?_⟩
    intro i
    have hb:(DH.bag i).card≤ 1:=by simpa using hDH i
    exact hb.trans (le_max_left _ _)

theorem transfer_after_pruning {t n:ℕ} (C:GraphClass) (hereditary:IsHereditary C)
    (W:ℕ→ ℕ) (monotone:Monotone W) (class_bound:HasBagBound C W)
    (H:SimpleGraph (Fin t)) [DecidableRel H.Adj] (G:SimpleGraph (Fin n))
    (member:G∈ C n) (E:AlmostEmbedding H G) (induced:IsInduced E) (d L:ℕ)
    (degree_bound:∀ v,H.degree v≤ d):
    ∃ D:TreeDecomposition H, ∀ i, (D.bag i).card≤
      max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + (Lax263307.RoutePruning.longEdges E L).card:=by
  classical
  let F:=Lax263307.RoutePruning.longEdges E L
  let K:=H.deleteEdges (↑F:Set (Sym2 (Fin t)))
  obtain ⟨E',hinduced,hshort⟩:=Lax263307Proofs.RoutePruning.prune_routes H G E induced L
  have degK (v:Fin t):K.degree v≤ d:=
    (K.degree_le_of_le (H.deleteEdges_le _)).trans (degree_bound v)
  obtain ⟨DK,hDK⟩:=Lax263307Proofs.InducedEmbeddingWidth.transfer_class_bound C hereditary W monotone class_bound K G member E' hinduced d L degK hshort
  have hcount:K.edgeSet.ncard≤ H.edgeSet.ncard:=
    Set.ncard_mono (SimpleGraph.edgeSet_mono (H.deleteEdges_le _))
  let B:=max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2))
  have hB:1≤ B:=le_max_left _ _
  have hbags (i:DK.Node):(DK.bag i).card≤ B:=by
    apply (hDK i).trans
    apply max_le_max (le_refl 1)
    apply Nat.mul_le_mul_left
    apply monotone
    exact Nat.mul_le_mul_right (L ^ 2) (Nat.mul_le_mul_left d hcount)
  have hwidth:HasTreewidthAtMost K (B - 1):=by
    refine ⟨DK, ?_⟩
    intro i
    simpa only [Nat.sub_add_cancel hB] using hbags i
  obtain ⟨DH,hDH⟩:=Lax263307Proofs.EdgeDeletionWidth.restore_edges H F (B - 1) hwidth
  refine ⟨DH, ?_⟩
  intro i
  have h:=hDH i
  change (DH.bag i).card≤ B + F.card
  omega

theorem treewidth_after_pruning {t n:ℕ} (C:GraphClass) (hereditary:IsHereditary C)
    (W:ℕ→ ℕ) (monotone:Monotone W) (class_bound:HasBagBound C W)
    (H:SimpleGraph (Fin t)) [DecidableRel H.Adj] (G:SimpleGraph (Fin n))
    (member:G∈ C n) (E:AlmostEmbedding H G) (induced:IsInduced E) (d L:ℕ)
    (degree_bound:∀ v,H.degree v≤ d):
    treewidth H + 1≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) +
      (Lax263307.RoutePruning.longEdges E L).card:=by
  classical
  let B:=max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + (Lax263307.RoutePruning.longEdges E L).card
  have hB:1≤ B:=by dsimp [B]; omega
  obtain ⟨D,hD⟩:=transfer_after_pruning C hereditary W monotone class_bound H G member E induced d L degree_bound
  have hwidth:HasTreewidthAtMost H (B - 1):=by
    refine ⟨D, ?_⟩
    intro i
    simpa only [Nat.sub_add_cancel hB] using hD i
  have hw:treewidth H≤ B - 1:=Nat.sInf_le hwidth
  change treewidth H + 1≤ B
  omega

theorem sampled_width_bound {t n q:ℕ} (C:GraphClass) (hereditary:IsHereditary C)
    (W:ℕ→ ℕ) (monotone:Monotone W) (class_bound:HasBagBound C W)
    (H:SimpleGraph (Fin t)) [DecidableRel H.Adj] (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member:G∈ C n) (D:Lax263307.RouteDistributions.Distribution G q) (hn:0 < n)
    (d L:ℕ) (degree_bound:∀ v,H.degree v≤ d) (M:ℝ) (positive:0 < M)
    (bad_budget:(H.edgeSet.ncard:ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling)≤ 1 / 4)
    (length_budget:(H.edgeSet.ncard:ℝ) * Lax263307.PathSampling.expectedSize D.toSampling≤ M):
    ∃ removed:ℕ, (L:ℝ) * removed≤ 4 * M∧
      treewidth H + 1≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed:=by
  classical
  obtain ⟨E,hinduced,hcost⟩:=Lax263307Proofs.SampledAlmostEmbeddings.exists_induced_almost_embedding H G D hn M positive bad_budget length_budget
  let removed:=(Lax263307.RoutePruning.longEdges E L).card
  refine ⟨removed, ?_,Lax263307Proofs.InducedEmbeddingWidth.treewidth_after_pruning C hereditary W monotone class_bound H G member E hinduced d L degree_bound⟩
  have hcount:(L:ℝ) * removed≤ ∑ e, ((E.route e).card:ℝ):=by
    exact_mod_cast Lax263307Proofs.RoutePruning.long_edge_count H G E L
  exact hcount.trans hcost

end Lax263307Proofs.InducedEmbeddingWidth

end

section

namespace Lax263307Proofs.PathSampling

open Lax263307.PathSampling Lax263307.Entropy

theorem load_nonnegative {n q:ℕ} (P:Distribution n q) (v:Fin n):
    0≤ load P v:=by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact P.nonnegative i
  · exact le_rfl

theorem indicator_product (a b:Prop) [Decidable a] [Decidable b] (x y:ℝ):
    (if a then x else 0) * (if b then y else 0)=if a∧ b then x * y else 0:=by
  by_cases ha:a <;> by_cases hb:b <;> simp [ha,hb]

theorem swap_inner_sums {a b c:ℕ} (f:Fin a→ Fin b→ Fin c→ ℝ):
    (∑ i, ∑ j, ∑ v,f i j v)=∑ v, ∑ i, ∑ j,f i j v:=by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem pair_load_product {n q:ℕ} (P:Distribution n q) (u v:Fin n):
    (∑ i, ∑ j,if u∈ P.vertices i∧ v∈ P.vertices j then
      P.probability i * P.probability j else 0)=load P u * load P v:=by
  unfold load
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (indicator_product _ _ _ _).symm

theorem expected_size_identity {n q:ℕ} (P:Distribution n q):
    expectedSize P=∑ v,load P v:=by
  unfold expectedSize load
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.sum_ite_mem,mul_comm]

theorem collision_union_bound {n q:ℕ} (P:Distribution n q):
    collisionProbability P≤ ∑ v, (load P v) ^ 2:=by
  classical
  have hpair (i j:Fin q):
      (if ¬Disjoint (P.vertices i) (P.vertices j) then P.probability i * P.probability j else 0)≤
      ∑ v:Fin n,if v∈ P.vertices i∧ v∈ P.vertices j then
        P.probability i * P.probability j else 0:=by
    by_cases h:¬Disjoint (P.vertices i) (P.vertices j)
    · obtain ⟨v,hvi,hvj⟩:=Finset.not_disjoint_iff.mp h
      rw [if_pos h]
      have hs:=Finset.single_le_sum
        (f:=fun v:Fin n => if v∈ P.vertices i∧ v∈ P.vertices j then
          P.probability i * P.probability j else 0)
        (fun v _ => by split_ifs <;> first | exact mul_nonneg (P.nonnegative i) (P.nonnegative j) | exact le_rfl)
        (Finset.mem_univ v)
      simpa only [if_pos (And.intro hvi hvj)] using hs
    · rw [if_neg h]
      apply Finset.sum_nonneg
      intro v _
      split_ifs <;> first | exact mul_nonneg (P.nonnegative i) (P.nonnegative j) | exact le_rfl
  calc
    collisionProbability P≤ ∑ i, ∑ j, ∑ v:Fin n,
        if v∈ P.vertices i∧ v∈ P.vertices j then P.probability i * P.probability j else 0:=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _=∑ v, ∑ i, ∑ j,
        if v∈ P.vertices i∧ v∈ P.vertices j then P.probability i * P.probability j else 0:=
      swap_inner_sums _
    _=∑ v, (load P v) ^ 2:=by simp_rw [pair_load_product,pow_two]

theorem adjacency_union_bound {n q:ℕ} (G:SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P:Distribution n q):
    adjacencyProbability G P≤ adjacencyMass G (load P):=by
  classical
  have hpair (i j:Fin q):
      (if ∃ u∈ P.vertices i, ∃ v∈ P.vertices j,G.Adj u v then
        P.probability i * P.probability j else 0)≤
      ∑ u:Fin n, ∑ v:Fin n,if G.Adj u v∧ u∈ P.vertices i∧ v∈ P.vertices j then
        P.probability i * P.probability j else 0:=by
    have hn (u v:Fin n):
        0≤ if G.Adj u v∧ u∈ P.vertices i∧ v∈ P.vertices j then
          P.probability i * P.probability j else 0:=by
      split_ifs <;> first | exact mul_nonneg (P.nonnegative i) (P.nonnegative j) | exact le_rfl
    split_ifs with h
    · obtain ⟨u,hui,v,hvj,huv⟩:=h
      calc
        P.probability i * P.probability j≤ ∑ v':Fin n,
            if G.Adj u v'∧ u∈ P.vertices i∧ v'∈ P.vertices j then
              P.probability i * P.probability j else 0:=by
          have hs:=Finset.single_le_sum (fun v' _ => hn u v') (Finset.mem_univ v)
          simpa only [if_pos (And.intro huv (And.intro hui hvj))] using hs
        _≤ _:=Finset.single_le_sum (fun u' _ => Finset.sum_nonneg fun v' _ => hn u' v')
          (Finset.mem_univ u)
    · exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => hn u v
  have hswap:(∑ i, ∑ j, ∑ u:Fin n, ∑ v:Fin n,
      if G.Adj u v∧ u∈ P.vertices i∧ v∈ P.vertices j then
        P.probability i * P.probability j else 0) =
      ∑ u:Fin n, ∑ v:Fin n, ∑ i, ∑ j,
        if G.Adj u v∧ u∈ P.vertices i∧ v∈ P.vertices j then
          P.probability i * P.probability j else 0:=by
    rw [swap_inner_sums]
    apply Finset.sum_congr rfl
    intro u _
    exact swap_inner_sums _
  calc
    adjacencyProbability G P≤ ∑ i, ∑ j, ∑ u:Fin n, ∑ v:Fin n,
        if G.Adj u v∧ u∈ P.vertices i∧ v∈ P.vertices j then
          P.probability i * P.probability j else 0:=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _=∑ u:Fin n, ∑ v:Fin n, ∑ i, ∑ j,
        if G.Adj u v∧ u∈ P.vertices i∧ v∈ P.vertices j then
          P.probability i * P.probability j else 0:=hswap
    _=adjacencyMass G (load P):=by
      unfold adjacencyMass
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv:G.Adj u v
      · simp only [huv,true_and,if_true]
        exact pair_load_product P u v
      · simp [huv]

theorem adjacencyMass_scale {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℝ) (c:ℝ):
    adjacencyMass G (fun v => c * x v)=c ^ 2 * adjacencyMass G x:=by
  unfold adjacencyMass
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

theorem sampling_bounds {n q:ℕ} (G:SimpleGraph (Fin n))
    [DecidableRel G.Adj] (P:Distribution n q) (x:Fin n→ ℝ) (k ℓ p:ℝ)
    (k_positive:0 < k) (ℓ_nonnegative:0≤ ℓ) (p_positive:0 < p)
    (cost_bounds:∀ v,0≤ x v∧ x v≤ 1) (mass:(∑ v,x v)≤ k)
    (load_bound:∀ v,load P v≤ ℓ * x v / k)
    (edge_bound:edgeCost G x≤ k ^ 2 / p):
    collisionProbability P≤ ℓ ^ 2 / k∧
      adjacencyProbability G P≤ 2 * ℓ ^ 2 / p∧ expectedSize P≤ ℓ:=by
  let c:=ℓ / k
  have hc:0≤ c:=div_nonneg ℓ_nonnegative k_positive.le
  have hload (v:Fin n):load P v≤ c * x v:=by
    simpa only [c,div_eq_mul_inv,mul_right_comm] using load_bound v
  have hsq (v:Fin n):(load P v) ^ 2≤ c ^ 2 * x v:=by
    have hscale:0≤ c * x v:=mul_nonneg hc (cost_bounds v).1
    have hpow:(load P v) ^ 2≤ (c * x v) ^ 2:=
      (sq_le_sq₀ (load_nonnegative P v) hscale).mpr (hload v)
    have hx:(x v) ^ 2≤ x v:=by nlinarith [(cost_bounds v).1, (cost_bounds v).2]
    calc
      (load P v) ^ 2≤ (c * x v) ^ 2:=hpow
      _=c ^ 2 * (x v) ^ 2:=by ring
      _≤ c ^ 2 * x v:=mul_le_mul_of_nonneg_left hx (sq_nonneg c)
  have hcoll:collisionProbability P≤ ℓ ^ 2 / k:=by
    calc
      collisionProbability P≤ ∑ v, (load P v) ^ 2:=
        Lax263307Proofs.PathSampling.collision_union_bound P
      _≤ ∑ v,c ^ 2 * x v:=Finset.sum_le_sum fun v _ => hsq v
      _=c ^ 2 * (∑ v,x v):=by rw [← Finset.mul_sum]
      _≤ c ^ 2 * k:=mul_le_mul_of_nonneg_left mass (sq_nonneg c)
      _=ℓ ^ 2 / k:=by dsimp [c]; field_simp
  have hadj:adjacencyMass G (load P)≤ c ^ 2 * adjacencyMass G x:=by
    rw [← adjacencyMass_scale G x c]
    unfold adjacencyMass
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    split_ifs
    · exact mul_le_mul (hload u) (hload v) (load_nonnegative P v)
        (mul_nonneg hc (cost_bounds u).1)
    · exact le_rfl
  have he:adjacencyMass G x≤ 2 * k ^ 2 / p:=by
    unfold edgeCost at edge_bound
    calc
      adjacencyMass G x≤ 2 * (k ^ 2 / p):=by linarith
      _=2 * k ^ 2 / p:=by ring
  have hadj':adjacencyProbability G P≤ 2 * ℓ ^ 2 / p:=by
    calc
      adjacencyProbability G P≤ adjacencyMass G (load P):=
        Lax263307Proofs.PathSampling.adjacency_union_bound G P
      _≤ c ^ 2 * adjacencyMass G x:=hadj
      _≤ c ^ 2 * (2 * k ^ 2 / p):=mul_le_mul_of_nonneg_left he (sq_nonneg c)
      _=2 * ℓ ^ 2 / p:=by dsimp [c]; field_simp
  have hsize:expectedSize P≤ ℓ:=by
    rw [Lax263307Proofs.PathSampling.expected_size_identity]
    calc
      (∑ v,load P v)≤ ∑ v,c * x v:=Finset.sum_le_sum fun v _ => hload v
      _=c * (∑ v,x v):=by rw [← Finset.mul_sum]
      _≤ c * k:=mul_le_mul_of_nonneg_left mass hc
      _=ℓ:=by dsimp [c]; field_simp
  exact ⟨hcoll,hadj',hsize⟩

end Lax263307Proofs.PathSampling

end

section

namespace Lax263307Proofs.CostSamplingObstruction

open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth Lax228581.Treewidth

theorem sufficient_budget (m ℓ k p:ℝ) (k_positive:0 < k) (p_positive:0 < p)
    (hk:8 * m ^ 2 * ℓ ^ 2≤ k) (hp:16 * m ^ 2 * ℓ ^ 2≤ p):
    m ^ 2 * (ℓ ^ 2 / k + 2 * ℓ ^ 2 / p)≤ 1 / 4:=by
  have h₁:m ^ 2 * ℓ ^ 2 / k≤ 1 / 8:=(div_le_iff₀ k_positive).mpr (by nlinarith)
  have h₂:2 * m ^ 2 * ℓ ^ 2 / p≤ 1 / 8:=(div_le_iff₀ p_positive).mpr (by nlinarith)
  calc
    m ^ 2 * (ℓ ^ 2 / k + 2 * ℓ ^ 2 / p)=m ^ 2 * ℓ ^ 2 / k + 2 * m ^ 2 * ℓ ^ 2 / p:=by ring
    _≤ 1 / 8 + 1 / 8:=add_le_add h₁ h₂
    _=1 / 4:=by norm_num

theorem cost_width_obstruction {t n q:ℕ} (C:GraphClass) (hereditary:IsHereditary C)
    (W:ℕ→ ℕ) (monotone:Monotone W) (class_bound:HasBagBound C W)
    (H:SimpleGraph (Fin t)) [DecidableRel H.Adj] (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member:G∈ C n) (D:Lax263307.RouteDistributions.Distribution G q) (hn:0 < n)
    (d L:ℕ) (degree_bound:∀ v,H.degree v≤ d) (edge_positive:0 < H.edgeSet.ncard)
    (x:Fin n→ ℝ) (k ℓ p:ℝ) (k_positive:0 < k) (ℓ_positive:0 < ℓ) (p_positive:0 < p)
    (cost_bounds:∀ v,0≤ x v∧ x v≤ 1) (mass:(∑ v,x v)≤ k)
    (load_bound:∀ v,Lax263307.PathSampling.load D.toSampling v≤ ℓ * x v / k)
    (edge_bound:Lax263307.Entropy.edgeCost G x≤ k ^ 2 / p)
    (target_large:8 * (H.edgeSet.ncard:ℝ) ^ 2 * ℓ ^ 2≤ k)
    (sparsity_large:16 * (H.edgeSet.ncard:ℝ) ^ 2 * ℓ ^ 2≤ p):
    ∃ removed:ℕ, (L:ℝ) * removed≤ 4 * (H.edgeSet.ncard:ℝ) * ℓ∧
      treewidth H + 1≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed:=by
  classical
  obtain ⟨hcoll,hadj,hsize⟩:=Lax263307Proofs.PathSampling.sampling_bounds G D.toSampling x k ℓ p
    k_positive ℓ_positive.le p_positive cost_bounds mass load_bound edge_bound
  have hbad:(H.edgeSet.ncard:ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling)≤ 1 / 4:=by
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add hcoll hadj) (sq_nonneg _))
    exact sufficient_budget _ ℓ k p k_positive p_positive target_large sparsity_large
  have hM:0 < (H.edgeSet.ncard:ℝ) * ℓ:=mul_pos (by exact_mod_cast edge_positive) ℓ_positive
  have hlen:=mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg H.edgeSet.ncard:(0:ℝ)≤ _)
  obtain ⟨removed,hremoved,hwidth⟩:=Lax263307Proofs.InducedEmbeddingWidth.sampled_width_bound C hereditary
    W monotone class_bound H G member D hn d L degree_bound _ hM hbad hlen
  exact ⟨removed,by simpa only [mul_assoc] using hremoved,hwidth⟩

end Lax263307Proofs.CostSamplingObstruction

end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.DecompositionHelpers

 theorem path_support_subset_walk {T:Type} (tree:SimpleGraph T) (acyclic:tree.IsAcyclic)
    {s t:T} (p:tree.Walk s t) (hp:p.IsPath) (q:tree.Walk s t):
    p.support ⊆ q.support:=by
  classical
  letI:=acyclic.subsingleton_path s t
  have h:(⟨p,hp⟩:tree.Path s t)=q.toPath:=Subsingleton.elim _ _
  have he:p=q.toPath.val:=congrArg Subtype.val h
  rw [he]
  exact q.support_toPath_subset_support

end EdgeSublinearMWIS.Main.DecompositionHelpers

end

section

namespace EdgeSublinearMWIS.Main.SourceTreewidthBridge
open Lax228581.Treewidth

 theorem decomposition {n:ℕ} {G:SimpleGraph (Fin n)} (D:TreeDecomposition G):
    RobertsonSeymour1986.GM5.IsTreeDecomposition G D.tree D.bag:=by
  classical
  refine ⟨D.isTree,D.vertex_mem_bag,fun _ _ h => D.edge_mem_bag h,?_⟩
  intro s z t p hp hz v hv
  obtain ⟨q⟩:=(D.bag_indices_connected v).preconnected
    (⟨s,(Finset.mem_inter.mp hv).1⟩) (⟨t,(Finset.mem_inter.mp hv).2⟩)
  let q':=q.map (⟨Subtype.val,fun h => h⟩:D.tree.induce {i | v∈ D.bag i}→g D.tree)
  have hsub:=DecompositionHelpers.path_support_subset_walk D.tree D.isTree.isAcyclic p hp q'
  have hmem:z∈ q'.support:=hsub hz
  simp only [q',SimpleGraph.Walk.support_map,List.mem_map] at hmem
  obtain ⟨x,hx,rfl⟩:=hmem
  exact x.property

 theorem hasWidth {n:ℕ} {G:SimpleGraph (Fin n)} {w:ℕ}
    (h:HasTreewidthAtMost G w):RobertsonSeymour1986.GM5.TreewidthLE G w:=by
  obtain ⟨D,hD⟩:=h
  letI:=D.nodeFintype
  exact ⟨D.Node,inferInstance,D.tree,D.bag,decomposition D,hD⟩

 theorem nonempty_width {n:ℕ} (G:SimpleGraph (Fin n)):
    {w | HasTreewidthAtMost G w}.Nonempty:=by
  classical
  let D:TreeDecomposition G:= {
    Node:=Unit
    tree:= ⊥
    isTree:= ⟨SimpleGraph.Connected.of_subsingleton,by simp⟩
    bag:=fun _ => Finset.univ
    vertex_mem_bag:=fun _ => ⟨(),by simp⟩
    edge_mem_bag:=fun {_ _} _ => ⟨(),by simp⟩
    bag_indices_connected:=fun v => by
      haveI:Nonempty {i:Unit | v∈ (Finset.univ:Finset (Fin n))}:= ⟨⟨(),by simp⟩⟩
      exact SimpleGraph.Connected.of_subsingleton
  }
  exact ⟨n,D,fun _ => by simp [D]⟩

 theorem tw_le {n:ℕ} (G:SimpleGraph (Fin n)):PlantedSubgraphLD.tw G≤ treewidth G:=by
  apply Nat.sInf_le
  apply hasWidth
  exact Nat.sInf_mem (nonempty_width G)
end EdgeSublinearMWIS.Main.SourceTreewidthBridge

namespace Lax263307Proofs.SourceGraphs
open Lax920634.EdgeExpansion Lax228581.Treewidth EdgeSublinearMWIS.Main
 theorem controlled_family:∃ widthConstant sizeConstant:ℕ,
    0 < widthConstant∧ 0 < sizeConstant∧
    ∀ request:ℕ, ∃ n, ∃ H:SimpleGraph (Fin n),request≤ n∧
      n≤ sizeConstant * (request + 1)∧ IsSubcubic H∧
      n≤ widthConstant * (treewidth H + 1):=by
  classical
  obtain ⟨c,t₀,hc,hh⟩:=lemma_10
  obtain ⟨W,hW⟩:=exists_nat_gt c⁻¹
  have hWpos:0 < W:=by exact_mod_cast lt_trans (inv_pos.mpr hc) hW
  refine ⟨W,t₀+1,hWpos,by omega,?_⟩
  intro request
  let n:=max request t₀
  obtain ⟨H,hsub,hwidth⟩:=hh n (le_max_right _ _)
  refine ⟨n,H,le_max_left _ _,?_,hsub,?_⟩
  · dsimp [n]; apply max_le <;> nlinarith
  · have tw:=SourceTreewidthBridge.tw_le H
    have ht:(n:ℝ)≤ c⁻¹*(treewidth H:ℝ):=by
      rw [mul_comm,le_mul_inv_iff₀ hc]
      have ht:(PlantedSubgraphLD.tw H:ℝ)≤ treewidth H:=by exact_mod_cast tw
      nlinarith
    have hwc:(n:ℝ)≤ (W:ℝ) * ((treewidth H:ℝ)+1):=by
      calc
        _≤ c⁻¹*(treewidth H:ℝ):=ht
        _≤ (W:ℝ)*(treewidth H:ℝ):=mul_le_mul_of_nonneg_right hW.le (by positivity)
        _≤ _:=by nlinarith [Nat.cast_nonneg (α:=ℝ) W]
    exact_mod_cast hwc
end Lax263307Proofs.SourceGraphs

end

section

namespace Lax263307Proofs.WidthGrowth

open Lax263307.WidthGrowth

theorem order_bound (a A c ℓ t m q:ℕ) (a_positive:0 < a) (ℓ_positive:0 < ℓ)
    (t_positive:0 < t) (W:ℕ→ ℕ)
    (W_positive:∀ M,1≤ W M) (W_power:∀ M, (W M) ^ a≤ A * (M + 1) ^ (a - 1))
    (edges:m≤ 2 * t) (discarded:(24 * c * ℓ) * q≤ 4 * m * ℓ)
    (width:t≤ c * (max 1 (6 * W (3 * m * (24 * c * ℓ) ^ 2)) + q)):
    t≤ threshold a A c * ℓ ^ (2 * (a - 1)):=by
  let M:=3 * m * (24 * c * ℓ) ^ 2
  have hq:24 * c * q≤ 4 * m:=by
    apply Nat.le_of_mul_le_mul_right (c:=ℓ) _ ℓ_positive
    convert discarded using 1; ring
  have hq':3 * c * q≤ t:=by nlinarith
  have hmax:max 1 (6 * W M)=6 * W M:=max_eq_right (by have h:=W_positive M; omega)
  have ht:t≤ 12 * c * W M:=by
    change t≤ c * (max 1 (6 * W M) + q) at width
    rw [hmax] at width
    nlinarith
  have hm:M≤ 6 * (24 * c) ^ 2 * t * ℓ ^ 2:=by
    calc
      M=(3 * (24 * c) ^ 2 * ℓ ^ 2) * m:=by dsimp [M]; ring
      _≤ (3 * (24 * c) ^ 2 * ℓ ^ 2) * (2 * t):=Nat.mul_le_mul_left _ edges
      _=_:=by ring
  have hone:1≤ t * ℓ ^ 2:=Nat.succ_le_of_lt (Nat.mul_pos t_positive (Nat.pow_pos ℓ_positive))
  have hM:M + 1≤ (6 * (24 * c) ^ 2 + 1) * t * ℓ ^ 2:=by
    calc
      M + 1≤ 6 * (24 * c) ^ 2 * t * ℓ ^ 2 + t * ℓ ^ 2:=Nat.add_le_add hm hone
      _=_:=by ring
  have hpow:t ^ a≤ threshold a A c * t ^ (a - 1) * ℓ ^ (2 * (a - 1)):=by
    calc
      t ^ a≤ (12 * c * W M) ^ a:=Nat.pow_le_pow_left ht _
      _=(12 * c) ^ a * (W M) ^ a:=by rw [mul_pow]
      _≤ (12 * c) ^ a * (A * (M + 1) ^ (a - 1)):=Nat.mul_le_mul_left _ (W_power M)
      _≤ (12 * c) ^ a * (A * ((6 * (24 * c) ^ 2 + 1) * t * ℓ ^ 2) ^ (a - 1)):=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hM _))
      _=_:=by simp only [mul_pow, ← pow_mul,threshold]; ring
  have heq:t ^ a=t * t ^ (a - 1):=by
    have ha:(a - 1) + 1=a:=Nat.sub_add_cancel (Nat.succ_le_of_lt a_positive)
    calc
      t ^ a=t ^ ((a - 1) + 1):=congrArg (t ^ ·) ha.symm
      _=_:=by rw [pow_succ,mul_comm]
  have hfinal:t * t ^ (a - 1)≤ (threshold a A c * ℓ ^ (2 * (a - 1))) * t ^ (a - 1):=by
    calc
      _=t ^ a:=heq.symm
      _≤ threshold a A c * t ^ (a - 1) * ℓ ^ (2 * (a - 1)):=hpow
      _=_:=by ring
  exact Nat.le_of_mul_le_mul_right hfinal (Nat.pow_pos t_positive)

end Lax263307Proofs.WidthGrowth

end

section

namespace Lax263307Proofs.NoBoundedLoadRoutes

open Lax263307.GraphClasses Lax263307.PowerBagBounds Lax228581.Treewidth
open Lax263307.InducedEmbeddingWidth Lax263307Proofs.TreeExtensions

theorem edgeless_width_zero {t:ℕ} (H:SimpleGraph (Fin t))
    (edgeless:∀ v u, ¬H.Adj v u):treewidth H=0:=by
  classical
  let S:Set (Fin t):= ∅
  let D:TreeDecomposition (H.induce S):= {
    Node:=Unit
    tree:= ⊥
    isTree:=SimpleGraph.IsTree.of_subsingleton
    bag:=fun _ => ∅
    vertex_mem_bag:=fun v => False.elim v.property
    edge_mem_bag:=by intro u _ _; exact False.elim u.property
    bag_indices_connected:=fun v => False.elim v.property }
  have hisolated (v:Fin t) (_:v∉ S):H.IsIsolated v:=edgeless v
  have hwidth:HasTreewidthAtMost H 0:=by
    refine ⟨extendIsolated S hisolated D, ?_⟩
    exact extendIsolated_card S hisolated D 1 (le_refl _) (fun _ => by simp [D])
  exact Nat.le_zero.mp (Nat.sInf_le hwidth)

theorem subcubic_edges {t:ℕ} (H:SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (degree_bound:∀ v,H.degree v≤ 3):H.edgeSet.ncard≤ 2 * t:=by
  classical
  have hsum:(∑ v,H.degree v)≤ ∑ _v:Fin t,3:=Finset.sum_le_sum fun v _ => degree_bound v
  rw [H.sum_degrees_eq_twice_card_edges,H.edgeFinset_card,Set.fintypeCard_eq_ncard] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  omega

theorem scale_square (c b a:ℕ):
    8 * (c * b ^ (2 * a)) ^ 2 * b ^ 2=8 * c ^ 2 * b ^ (4 * a + 2):=by
  calc
    _=8 * c ^ 2 * (b ^ ((2 * a) * 2) * b ^ 2):=by rw [mul_pow, ← pow_mul]; ring
    _=_:=by rw [← pow_add,show (2 * a) * 2 + 2=4 * a + 2 by omega]

theorem no_bounded_load_routes (C:GraphClass) (hereditary:IsHereditary C)
    (a A:ℕ) (a_positive:0 < a) (A_positive:0 < A) (class_bound:HasPowerBagBound C a A):
    ∃ K:ℕ,0 < K∧ ∀ (n q:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ ∀ (D:Lax263307.RouteDistributions.Distribution G q),0 < n→
      ∀ (ℓ:ℕ),0 < ℓ→ ∀ (x:Fin n→ ℝ) (k p:ℝ),0 < k→ 0 < p→
      (∀ v,0≤ x v∧ x v≤ 1)→ (∑ v,x v)≤ k→
      (∀ v,Lax263307.PathSampling.load D.toSampling v≤ (ℓ:ℝ) * x v / k)→
      Lax263307.Entropy.edgeCost G x≤ k ^ 2 / p→
      (K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ k→
      (2 * K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ p→ False:=by
  classical
  obtain ⟨CW,CS,hCW,hCS,family⟩:=Lax263307Proofs.SourceGraphs.controlled_family
  obtain ⟨hmonotone,hclass,hWpositive,hWpower⟩:=Lax263307Proofs.PowerBagBounds.root_bag_bound C a A a_positive A_positive class_bound
  let W:=bagBound a A
  let T:=Lax263307.WidthGrowth.threshold a A CW
  let scale:=2 * CS * (T + CW + 3)
  let K:=8 * scale ^ 2 + 1
  refine ⟨K,Nat.zero_lt_succ _, ?_⟩
  intro n q G _ hG D hn ℓ hℓ x k p hk hp hcost hmass hload hedge htarget hsparse
  let request:=(T + CW + 1) * (ℓ + 1) ^ (2 * a) + 1
  obtain ⟨t,H,hrequest,hsize,hsubcubic,hlinear⟩:=family request
  have hpw:1≤ (ℓ + 1) ^ (2 * a):=Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos ℓ))
  have hgreater:CW < t:=by
    have h:=Nat.mul_le_mul_left (T + CW + 1) hpw
    change (T + CW + 1) * 1≤ (T + CW + 1) * (ℓ + 1) ^ (2 * a) at h
    dsimp [request] at hrequest
    omega
  have htpos:0 < t:=lt_of_le_of_lt (Nat.zero_le CW) hgreater
  have hdeg (v:Fin t):H.degree v≤ 3:=by
    rw [← H.card_neighborSet_eq_degree v,Set.fintypeCard_eq_ncard]
    exact hsubcubic v
  have hmpos:0 < H.edgeSet.ncard:=by
    by_contra h
    have hz:H.edgeSet.ncard=0:=by omega
    have hnone:∀ v u, ¬H.Adj v u:=by
      intro v u h
      have hh:0 < H.edgeSet.ncard:=(Set.ncard_pos (Set.toFinite H.edgeSet)).mpr ⟨s(v,u),h⟩
      omega
    rw [edgeless_width_zero H hnone,zero_add,mul_one] at hlinear
    omega
  have hmedges:=subcubic_edges H hdeg
  have hrequestcap:request + 1≤ (T + CW + 3) * (ℓ + 1) ^ (2 * a):=by
    dsimp [request]
    nlinarith
  have hmcap:H.edgeSet.ncard≤ scale * (ℓ + 1) ^ (2 * a):=by
    calc
      _≤ 2 * t:=hmedges
      _≤ 2 * (CS * (request + 1)):=Nat.mul_le_mul_left 2 hsize
      _≤ 2 * (CS * ((T + CW + 3) * (ℓ + 1) ^ (2 * a))):=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left CS hrequestcap)
      _=_:=by dsimp [scale]; ring
  have hbudget:8 * H.edgeSet.ncard ^ 2 * ℓ ^ 2≤ K * (ℓ + 1) ^ (4 * a + 2):=by
    calc
      _≤ 8 * (scale * (ℓ + 1) ^ (2 * a)) ^ 2 * (ℓ + 1) ^ 2:=
        Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hmcap _)) (Nat.pow_le_pow_left (Nat.le_succ ℓ) _)
      _=8 * scale ^ 2 * (ℓ + 1) ^ (4 * a + 2):=scale_square _ _ _
      _≤ _:=Nat.mul_le_mul_right _ (by dsimp [K]; omega)
  have hbudget₂:16 * H.edgeSet.ncard ^ 2 * ℓ ^ 2≤ (2 * K) * (ℓ + 1) ^ (4 * a + 2):=by
    have h:=Nat.mul_le_mul_left 2 hbudget
    convert h using 1 <;> ring
  have htarget':8 * (H.edgeSet.ncard:ℝ) ^ 2 * (ℓ:ℝ) ^ 2≤ k:=by
    have h:8 * (H.edgeSet.ncard:ℝ) ^ 2 * (ℓ:ℝ) ^ 2≤ (K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2):=by exact_mod_cast hbudget
    exact h.trans htarget
  have hsparse':16 * (H.edgeSet.ncard:ℝ) ^ 2 * (ℓ:ℝ) ^ 2≤ p:=by
    have h:16 * (H.edgeSet.ncard:ℝ) ^ 2 * (ℓ:ℝ) ^ 2≤ (2 * K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2):=by exact_mod_cast hbudget₂
    exact h.trans hsparse
  obtain ⟨removed,hremoved,hwidth⟩:=Lax263307Proofs.CostSamplingObstruction.cost_width_obstruction
    C hereditary W hmonotone hclass H G hG D hn 3 (24 * CW * ℓ) hdeg hmpos x k ℓ p hk
      (by exact_mod_cast hℓ) hp hcost hmass hload hedge htarget' hsparse'
  have hr:(24 * CW * ℓ) * removed≤ 4 * H.edgeSet.ncard * ℓ:=by exact_mod_cast hremoved
  have hw:t≤ CW * (max 1 (6 * W (3 * H.edgeSet.ncard * (24 * CW * ℓ) ^ 2)) + removed):=by
    exact hlinear.trans (Nat.mul_le_mul_left CW hwidth)
  have horder:=Lax263307Proofs.WidthGrowth.order_bound a A CW ℓ t H.edgeSet.ncard removed a_positive hℓ
    htpos W hWpositive hWpower hmedges hr hw
  have hpower:ℓ ^ (2 * (a - 1))≤ (ℓ + 1) ^ (2 * a):=by
    exact (Nat.pow_le_pow_left (Nat.le_succ ℓ) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos ℓ) (by omega))
  have hsmall:t≤ (T + CW + 1) * (ℓ + 1) ^ (2 * a):=by
    calc
      t≤ T * ℓ ^ (2 * (a - 1)):=horder
      _≤ T * (ℓ + 1) ^ (2 * a):=Nat.mul_le_mul_left T hpower
      _≤ _:=Nat.mul_le_mul_right _ (by omega)
  dsimp [request] at hrequest
  omega

end Lax263307Proofs.NoBoundedLoadRoutes

end

section

namespace Lax263307Proofs.RoutingNormalization

open Lax263307.RoutingNormalization

theorem pair_mass {n q:ℕ} (w:Fin q→ ℝ)
    (E:Fin n→ Fin n→ Fin q→ Prop) (hn:0 < n) (u v:Fin n)
    (positive:0 < routed w E u v):
    (∑ i,probability w E u v i)=1 / (n:ℝ) ^ 2:=by
  classical
  have hterm (i:Fin q):probability w E u v i =
      (if E u v i then w i else 0) / (routed w E u v * (n:ℝ) ^ 2):=by
    unfold probability
    split_ifs <;> simp
  simp_rw [hterm, ← Finset.sum_div]
  change routed w E u v / (routed w E u v * (n:ℝ) ^ 2)=_
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  field_simp

theorem total_mass {n q:ℕ} (w:Fin q→ ℝ)
    (E:Fin n→ Fin n→ Fin q→ Prop) (hn:0 < n)
    (positive:∀ u v,0 < routed w E u v):
    (∑ u, ∑ v, ∑ i,probability w E u v i)=1:=by
  simp_rw [pair_mass w E hn _ _ (positive _ _)]
  simp
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  field_simp

theorem pair_unique_sum {n q:ℕ} (E:Fin n→ Fin n→ Fin q→ Prop)
    (unique:IsUniquePair E) (i:Fin q) (a:ℝ) (nonnegative:0≤ a):
    (by classical exact ∑ u, ∑ v,if E u v i then a else 0)≤ a:=by
  classical
  by_cases hexists:∃ u v,E u v i
  · obtain ⟨u₀,v₀,hE⟩:=hexists
    have heq (u v:Fin n):E u v i↔ u=u₀∧ v=v₀:=by
      constructor
      · intro h
        exact unique i u v u₀ v₀ h hE
      · rintro ⟨rfl,rfl⟩
        exact hE
    simp_rw [heq,ite_and]
    simp
  · have hnone (u v:Fin n):¬E u v i:=fun h => hexists ⟨u,v,h⟩
    simp_rw [if_neg (hnone _ _)]
    simpa using nonnegative

theorem normalization_correct {n q:ℕ} (w:Fin q→ ℝ)
    (E:Fin n→ Fin n→ Fin q→ Prop) (hn:0 < n)
    (nonnegative:∀ i,0≤ w i) (positive:∀ u v,0 < routed w E u v):
    (∀ u v i,0≤ probability w E u v i)∧
      (∀ u v, (∑ i,probability w E u v i)=1 / (n:ℝ) ^ 2)∧
      (∑ u, ∑ v, ∑ i,probability w E u v i)=1:=by
  classical
  refine ⟨?_,fun u v => pair_mass w E hn u v (positive u v),total_mass w E hn positive⟩
  intro u v i
  unfold probability
  split_ifs
  · exact div_nonneg (nonnegative i) (mul_nonneg (positive u v).le (sq_nonneg _))
  · exact le_refl 0

theorem normalized_load_bound {n q:ℕ} (w:Fin q→ ℝ)
    (E:Fin n→ Fin n→ Fin q→ Prop) (hn:0 < n)
    (nonnegative:∀ i,0≤ w i) (unique:IsUniquePair E)
    (γ:ℝ) (γ_positive:0 < γ) (lower_bound:∀ u v,1 / γ≤ routed w E u v)
    (cost:Fin q→ ℝ) (cost_nonnegative:∀ i,0≤ cost i):
    (∑ u, ∑ v, ∑ i,probability w E u v i * cost i)≤
      γ / (n:ℝ) ^ 2 * (∑ i,w i * cost i):=by
  classical
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  have hden:(0:ℝ) < (n:ℝ) ^ 2:=sq_pos_of_pos hnR
  have hγ:0≤ γ / (n:ℝ) ^ 2:=div_nonneg γ_positive.le hden.le
  have hpositive (u v:Fin n):0 < routed w E u v:=
    lt_of_lt_of_le (by positivity) (lower_bound u v)
  have hfactor (u v:Fin n):1≤ γ * routed w E u v:=by
    have h:=(div_le_iff₀ γ_positive).mp (lower_bound u v)
    nlinarith
  have hterm (u v:Fin n) (i:Fin q):probability w E u v i * cost i≤
      γ / (n:ℝ) ^ 2 * (if E u v i then w i * cost i else 0):=by
    by_cases hE:E u v i
    · simp only [probability,if_pos hE]
      have hw:w i / routed w E u v≤ γ * w i:=by
        apply (div_le_iff₀ (hpositive u v)).mpr
        have h:=mul_le_mul_of_nonneg_left (hfactor u v) (nonnegative i)
        nlinarith
      have heq:w i / (routed w E u v * (n:ℝ) ^ 2) * cost i =
          (w i / routed w E u v * cost i) / (n:ℝ) ^ 2:=by ring
      rw [heq]
      have h:=div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hw (cost_nonnegative i)) hden.le
      calc
        (w i / routed w E u v * cost i) / (n:ℝ) ^ 2≤
            (γ * w i * cost i) / (n:ℝ) ^ 2:=h
        _=γ / (n:ℝ) ^ 2 * (w i * cost i):=by ring
    · simp [probability,hE]
  have hswap:(∑ u, ∑ v, ∑ i,γ / (n:ℝ) ^ 2 * (if E u v i then w i * cost i else 0)) =
      ∑ i,γ / (n:ℝ) ^ 2 * ∑ u, ∑ v,if E u v i then w i * cost i else 0:=by
    conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  calc
    (∑ u, ∑ v, ∑ i,probability w E u v i * cost i)≤
        ∑ u, ∑ v, ∑ i,γ / (n:ℝ) ^ 2 * (if E u v i then w i * cost i else 0):=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun i _ => hterm u v i
    _=∑ i,γ / (n:ℝ) ^ 2 * ∑ u, ∑ v,if E u v i then w i * cost i else 0:=hswap
    _≤ ∑ i,γ / (n:ℝ) ^ 2 * (w i * cost i):=Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (pair_unique_sum E unique i _
        (mul_nonneg (nonnegative i) (cost_nonnegative i))) hγ
    _=γ / (n:ℝ) ^ 2 * (∑ i,w i * cost i):=(Finset.mul_sum _ _ _).symm

end Lax263307Proofs.RoutingNormalization

end

section

open scoped NNReal

namespace Lax455465Proofs.ProductCorollaries

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.RationalEncoding Lax455465.FlowCutCertificate Lax759944.RamPolytime

theorem directed_product:
  ∃ (solve:List ℕ→ List ℕ) (C:ℝ),RamPolytime solve∧ 0 < C∧
    ∀ (n:ℕ) (I:RationalInstance n),2≤ supportCount I.weights→
      ∃ certificate:Certificate n,
        solve (encodeInput .directed I)=encodeCertificate certificate∧
        IsValid .directed I C certificate:=by
  obtain ⟨solve,C,htime,hC,hsolve⟩:=
    Lax455465Proofs.RamProductAlgorithm.exists_polynomial_time_flow_cut
  refine ⟨solve,C,htime,hC, ?_⟩
  intro n I hp
  exact hsolve .directed n I (by intro h; cases h) hp

private theorem supportCount_of_uniform {n:ℕ} (I:RationalInstance n)
    (hweights:∀ v,I.weight v=1):supportCount I.weights=n:=by
  simp [supportCount,RationalInstance.weights,hweights]

theorem directed_uniform:
  ∃ (solve:List ℕ→ List ℕ) (C:ℝ),RamPolytime solve∧ 0 < C∧
    ∀ (n:ℕ) (I:RationalInstance n), (∀ v,I.weight v=1)→ 2≤ n→
      ∃ certificate:Certificate n,
        solve (encodeInput .directed I)=encodeCertificate certificate∧
        AdmissibleCut I.weights certificate.cut∧
        IsArcConcurrentFlow .directed I.network I.weights
          (certificate.flow.value:ℝ≥0) certificate.flow.flow∧
        (ratioCost I.network I.weights certificate.cut:ℝ)≤
          C * logFactor n * (certificate.flow.value:ℝ):=by
  obtain ⟨solve,C,htime,hC,hsolve⟩:=
    Lax455465Proofs.ProductCorollaries.directed_product
  refine ⟨solve,C,htime,hC, ?_⟩
  intro n I hweights hn
  have hp:=supportCount_of_uniform I hweights
  obtain ⟨certificate,hout,hvalid⟩:=hsolve n I (by simpa [hp] using hn)
  refine ⟨certificate,hout, ?_⟩
  simpa only [IsValid,hp] using hvalid

end Lax455465Proofs.ProductCorollaries

end

section

namespace Lax263307Proofs.VertexSplitting

open scoped NNReal NNRat
open Lax263307.VertexSplitting Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax455465.ConcurrentFlow

@[simp] theorem original_minus {n:ℕ} (v:Fin n):original (minus v)=v:=by
  apply Fin.ext
  simp [original,minus]

@[simp] theorem original_plus {n:ℕ} (v:Fin n):original (plus v)=v:=by
  apply Fin.ext
  dsimp [original,plus]
  omega

theorem capacity_reverse {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (v:Fin n):
    (splitInstance G x large).capacity (plus v) (minus v)=large:=by
  simp [splitInstance,minus,plus,original]

theorem capacity_edge {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (u v:Fin n) (huv:G.Adj u v):
    (splitInstance G x large).capacity (plus u) (minus v)=large:=by
  simp only [splitInstance,original_plus,original_minus]
  simp [minus,plus,huv]

theorem port_cases {n:ℕ} (v:Fin (2 * n)):
    v=minus (original v)∨ v=plus (original v):=by
  by_cases heven:v.val % 2=0
  · left
    apply Fin.ext
    dsimp [minus,original]
    omega
  · right
    apply Fin.ext
    dsimp [plus,original]
    omega

theorem capacity_le_cut {N:ℕ} (I:Network N) (U:Finset (Fin N))
    (a b:Fin N) (ha:a∈ U) (hb:b∉ U):
    I.capacity a b≤ cutCapacity I U:=by
  classical
  exact (Finset.single_le_sum (f:=I.capacity a) (fun _ _ => zero_le) (Finset.mem_compl.mpr hb)).trans
    (Finset.single_le_sum (f:=fun u => ∑ v∈ Uᶜ,I.capacity u v) (fun _ _ => zero_le) ha)

theorem small_cut_reverse_closed {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (v:Fin n) (hv:plus v∈ U):minus v∈ U:=by
  by_contra hn
  have h:=capacity_le_cut (splitInstance G x large).network U (plus v) (minus v) hv hn
  change ((splitInstance G x large).capacity (plus v) (minus v):ℝ≥0)≤ _ at h
  rw [capacity_reverse] at h
  exact (not_lt_of_ge h) small

theorem small_cut_no_cross_edge {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (u v:Fin n) (hu:plus u∈ U) (hv:minus v∉ U):¬G.Adj u v:=by
  intro huv
  have h:=capacity_le_cut (splitInstance G x large).network U (plus u) (minus v) hu hv
  change ((splitInstance G x large).capacity (plus u) (minus v):ℝ≥0)≤ _ at h
  rw [capacity_edge G x large u v huv] at h
  exact (not_lt_of_ge h) small

theorem original_in_left {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (v:Fin (2 * n)) (hv:v∈ U):original v∈ leftShore U:=by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases port_cases v with he | he
  · exact he ▸ hv
  · exact small_cut_reverse_closed G x large U small _ (he ▸ hv)

theorem original_in_right {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (v:Fin (2 * n)) (hv:v∉ U):original v∈ rightShore U:=by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases port_cases v with he | he
  · intro hp
    exact hv (he.symm ▸ small_cut_reverse_closed G x large U small _ hp)
  · intro hp
    exact hv (he.symm ▸ hp)

def encodePort {n:ℕ} (v:Fin (2 * n)):Fin n × Fin 2:=
  (original v, ⟨v.val % 2,by omega⟩)

theorem encodePort_injective (n:ℕ):Function.Injective (encodePort (n:=n)):=by
  intro v w he
  have hfirst:=congrArg (fun a => a.1.val) he
  have hsecond:=congrArg (fun a => a.2.val) he
  apply Fin.ext
  dsimp [encodePort,original] at hfirst hsecond
  omega

theorem shore_card_bounds {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0)):
    U.card≤ 2 * (leftShore U).card∧ Uᶜ.card≤ 2 * (rightShore U).card:=by
  have hleft:U.image encodePort ⊆ (leftShore U).product Finset.univ:=by
    intro a ha
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨original_in_left G x large U small v hv,Finset.mem_univ _⟩
  have hright:Uᶜ.image encodePort ⊆ (rightShore U).product Finset.univ:=by
    intro a ha
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ⟨original_in_right G x large U small v
      (Finset.mem_compl.mp hv),Finset.mem_univ _⟩
  have hcardL:=Finset.card_le_card hleft
  have hcardR:=Finset.card_le_card hright
  rw [Finset.card_image_of_injective _ (encodePort_injective n)] at hcardL hcardR
  simpa [Nat.mul_comm] using And.intro hcardL hcardR

theorem small_cut_separation {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (nonempty:U.Nonempty) (proper:Uᶜ.Nonempty):
    (leftShore U).Nonempty∧ (rightShore U).Nonempty∧
      leftShore U ∪ rightShore U=Finset.univ∧
      (∀ u∈ leftShore U \ rightShore U, ∀ v∈ rightShore U \ leftShore U, ¬G.Adj u v)∧
      U.card≤ 2 * (leftShore U).card∧ Uᶜ.card≤ 2 * (rightShore U).card:=by
  have hleft:(leftShore U).Nonempty:=by
    obtain ⟨v,hv⟩:=nonempty
    exact ⟨original v,original_in_left G x large U small v hv⟩
  have hright:(rightShore U).Nonempty:=by
    obtain ⟨v,hv⟩:=proper
    exact ⟨original v,original_in_right G x large U small v (Finset.mem_compl.mp hv)⟩
  have hcover:leftShore U ∪ rightShore U=Finset.univ:=by
    ext v
    simp only [leftShore,rightShore,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hv:minus v∈ U
    · exact iff_true_intro (Or.inl hv)
    · exact iff_true_intro (Or.inr fun hp => hv (small_cut_reverse_closed G x large U small v hp))
  have hsep:∀ u∈ leftShore U \ rightShore U,
      ∀ v∈ rightShore U \ leftShore U, ¬G.Adj u v:=by
    intro u hu v hv
    have hu':plus u∈ U:=by
      have:=(Finset.mem_sdiff.mp hu).2
      simpa [rightShore] using this
    have hv':minus v∉ U:=by
      have:=(Finset.mem_sdiff.mp hv).2
      simpa [leftShore] using this
    exact small_cut_no_cross_edge G x large U small u v hu' hv'
  exact ⟨hleft,hright,hcover,hsep,shore_card_bounds G x large U small⟩

theorem split_certificate:
  ∃ (solve:List ℕ→ List ℕ) (C:ℝ),Lax759944.RamPolytime.RamPolytime solve∧ 0 < C∧
    ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x:Fin n→ ℚ≥0) (large:ℚ≥0),0 < n→
      let I:=splitInstance G x large
      ∃ certificate:Lax455465.FlowCutCertificate.Certificate (2 * n),
        solve (encodeInput .directed I)=Lax455465.FlowCutCertificate.encodeCertificate certificate∧
        AdmissibleCut I.weights certificate.cut∧
        IsArcConcurrentFlow .directed I.network I.weights
          (certificate.flow.value:ℝ≥0) certificate.flow.flow∧
        (ratioCost I.network I.weights certificate.cut:ℝ)≤
          C * logFactor (2 * n) * (certificate.flow.value:ℝ):=by
  obtain ⟨solve,C,hp,hC,hsolve⟩:=
    Lax455465Proofs.ProductCorollaries.directed_uniform
  refine ⟨solve,C,hp,hC, ?_⟩
  intro n G inst x large hn
  exact hsolve (2 * n) (splitInstance G x large) (fun _ => rfl) (by omega)

theorem sum_ports {n:ℕ} (f:Fin (2 * n)→ ℝ≥0):
    (∑ s,f s)=∑ v, (f (minus v) + f (plus v)):=by
  classical
  have hsurj:Function.Surjective (encodePort (n:=n)):=by
    rintro ⟨v,p⟩
    fin_cases p
    · exact ⟨minus v,by
        apply Prod.ext
        · exact original_minus v
        · apply Fin.ext; simp [encodePort,minus]⟩
    · exact ⟨plus v,by
        apply Prod.ext
        · exact original_plus v
        · apply Fin.ext; simp [encodePort,plus]⟩
  let e:=Equiv.ofBijective encodePort ⟨encodePort_injective n,hsurj⟩
  have heq:(∑ s,f s)=∑ a:Fin n × Fin 2,
      if a.2=0 then f (minus a.1) else f (plus a.1):=by
    apply Fintype.sum_equiv e
    intro s
    change f s=if (encodePort s).2=0 then f (minus (original s)) else f (plus (original s))
    by_cases hp:s.val % 2=0
    · have hp':(encodePort s).2=0:=Fin.ext hp
      rw [if_pos hp']
      congr 1
      apply Fin.ext
      dsimp [minus,original]
      omega
    · have hp':(encodePort s).2 ≠ 0:=by
        intro h
        exact hp (congrArg Fin.val h)
      rw [if_neg hp']
      congr 1
      apply Fin.ext
      dsimp [plus,original]
      omega
  rw [heq,Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem capacity_minus {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (v:Fin n) (t:Fin (2 * n)):
    (splitInstance G x large).capacity (minus v) t=if t=plus v then x v else 0:=by
  simp only [splitInstance]
  rw [original_minus]
  simp only [minus,Nat.mul_mod_right,zero_ne_one,
    false_and,if_false,true_and]
  have heq:t.val=2 * v.val + 1↔ t=plus v:=by
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [heq]

theorem capacity_plus_plus {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (u v:Fin n):
    (splitInstance G x large).capacity (plus u) (plus v)=0:=by
  have hbad:¬(2 * v.val + 1=2 * u.val):=by omega
  simp [splitInstance,plus,hbad]

theorem capacity_plus_minus {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (u v:Fin n):
    (splitInstance G x large).capacity (plus u) (minus v) =
      if u=v∨ G.Adj u v then large else 0:=by
  have hback:v.val=u.val↔ u=v:=by
    exact ⟨fun h => Fin.ext h.symm,fun h => congrArg Fin.val h.symm⟩
  simp only [splitInstance,original_plus,original_minus]
  simp [plus,minus,hback,ite_or]

theorem small_cut_plus_zero {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (u:Fin n) (hu:plus u∈ U) (t:Fin (2 * n)) (ht:t∉ U):
    (splitInstance G x large).capacity (plus u) t=0:=by
  rcases port_cases t with h | h
  · rw [h,capacity_plus_minus]
    have hv:minus (original t)∉ U:=by intro hv; exact ht (h.symm ▸ hv)
    have hne:u ≠ original t:=by
      intro he
      exact hv (he ▸ small_cut_reverse_closed G x large U small u hu)
    have hadj:=small_cut_no_cross_edge G x large U small u (original t) hu hv
    simp [hne,hadj]
  · rw [h,capacity_plus_plus]

theorem small_cut_cost {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n)))
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0)):
    cutCapacity (splitInstance G x large).network U =
      ∑ v∈ leftShore U ∩ rightShore U, (x v:ℝ≥0):=by
  classical
  let I:=splitInstance G x large
  let f (s:Fin (2 * n)):ℝ≥0:=if s∈ U then ∑ t∈ Uᶜ,I.network.capacity s t else 0
  have hminus (v:Fin n):f (minus v) =
      if minus v∈ U∧ plus v∉ U then (x v:ℝ≥0) else 0:=by
    have hinner:(∑ t∈ Uᶜ,I.network.capacity (minus v) t) =
        if plus v∉ U then (x v:ℝ≥0) else 0:=by
      change (∑ t∈ Uᶜ, ((splitInstance G x large).capacity (minus v) t:ℝ≥0))=_
      simp_rw [capacity_minus]
      by_cases hp:plus v∈ U
      · rw [if_neg (not_not.mpr hp)]
        apply Finset.sum_eq_zero
        intro t ht
        have hne:t ≠ plus v:=fun he => (Finset.mem_compl.mp ht) (he.symm ▸ hp)
        simp [hne]
      · rw [if_pos hp,Finset.sum_eq_single (plus v)]
        · simp
        · intro t ht hne
          simp [hne]
        · simp [hp]
    dsimp [f]
    rw [hinner]
    by_cases hm:minus v∈ U <;> by_cases hp:plus v∈ U <;> simp [hm,hp]
  have hplus (v:Fin n):f (plus v)=0:=by
    dsimp [f]
    split_ifs with hv
    · apply Finset.sum_eq_zero
      intro t ht
      change ((splitInstance G x large).capacity (plus v) t:ℝ≥0)=0
      rw [small_cut_plus_zero G x large U small v hv t (Finset.mem_compl.mp ht)]
      simp
    · rfl
  have hcapacity:cutCapacity I.network U=∑ s,f s:=by
    simp only [f,Finset.sum_ite_mem,Finset.univ_inter]
    rfl
  rw [hcapacity,sum_ports]
  simp_rw [hminus,hplus,add_zero]
  have hshore:∀ v:Fin n, (minus v∈ U∧ plus v∉ U)↔ v∈ leftShore U ∩ rightShore U:=by
    intro v
    simp [leftShore,rightShore]
  simp_rw [hshore]
  simpa only [Finset.univ_inter] using
    (Finset.sum_ite_mem (Finset.univ:Finset (Fin n)) (leftShore U ∩ rightShore U)
      (fun v => (x v:ℝ≥0)))

theorem separator_cost_bound {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (U:Finset (Fin (2 * n))) (ρ:ℝ)
    (nonnegative:0≤ ρ)
    (small:cutCapacity (splitInstance G x large).network U < (large:ℝ≥0))
    (admissible:AdmissibleCut (splitInstance G x large).weights U)
    (ratio:(ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights U:ℝ)≤ ρ):
    (∑ v∈ leftShore U ∩ rightShore U, (x v:ℝ))≤
      4 * ρ * (leftShore U).card * (rightShore U).card:=by
  classical
  let I:=splitInstance G x large
  have hweights:I.weights=uniformWeight (2 * n):=by
    funext v
    simp [I,splitInstance,RationalInstance.weights,uniformWeight]
  have hmass (V:Finset (Fin (2 * n))):mass I.weights V=(V.card:ℝ≥0):=by
    simp [hweights,mass,uniformWeight]
  have hleft:(0:ℝ) < U.card:=by
    have h:=admissible.1
    rw [hmass] at h
    exact_mod_cast h
  have hright:(0:ℝ) < Uᶜ.card:=by
    have h:=admissible.2
    rw [hmass] at h
    exact_mod_cast h
  have hratio:(cutCapacity I.network U:ℝ) / ((U.card:ℝ) * Uᶜ.card)≤ ρ:=by
    change (ratioCost I.network I.weights U:ℝ)≤ ρ at ratio
    simpa only [ratioCost,hmass,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast] using ratio
  have hcap:=(div_le_iff₀ (mul_pos hleft hright)).mp hratio
  have hcards:=shore_card_bounds G x large U small
  have hL:(U.card:ℝ)≤ 2 * (leftShore U).card:=by exact_mod_cast hcards.1
  have hR:(Uᶜ.card:ℝ)≤ 2 * (rightShore U).card:=by exact_mod_cast hcards.2
  have hprod:=mul_le_mul hL hR (by positivity) (by positivity)
  have hρ:=mul_le_mul_of_nonneg_left hprod nonnegative
  have hcost:(cutCapacity I.network U:ℝ) =
      ∑ v∈ leftShore U ∩ rightShore U, (x v:ℝ):=by
    rw [Lax263307Proofs.VertexSplitting.small_cut_cost G x large U small]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    norm_cast
  rw [hcost] at hcap
  nlinarith

theorem small_cut_of_low_flow {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0)
    (certificate:Lax455465.FlowCutCertificate.Certificate (2 * n)) (ρ γ:ℝ)
    (nonnegative:0≤ ρ) (positive:0 < γ)
    (admissible:AdmissibleCut (splitInstance G x large).weights certificate.cut)
    (ratio:(ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights certificate.cut:ℝ)≤
        ρ * (certificate.flow.value:ℝ))
    (low_value:(certificate.flow.value:ℝ) < 1 / γ)
    (large_capacity:ρ * (2 * n:ℕ) ^ 2 / γ < (large:ℝ)):
    cutCapacity (splitInstance G x large).network certificate.cut < (large:ℝ≥0):=by
  classical
  let I:=splitInstance G x large
  let U:=certificate.cut
  have hweights:I.weights=uniformWeight (2 * n):=by
    funext v
    simp [I,splitInstance,RationalInstance.weights,uniformWeight]
  have hmass (V:Finset (Fin (2 * n))):mass I.weights V=(V.card:ℝ≥0):=by
    simp [hweights,mass,uniformWeight]
  have hleft:(0:ℝ) < U.card:=by
    have h:=admissible.1
    change 0 < mass I.weights U at h
    rw [hmass] at h
    exact_mod_cast h
  have hright:(0:ℝ) < Uᶜ.card:=by
    have h:=admissible.2
    change 0 < mass I.weights Uᶜ at h
    rw [hmass] at h
    exact_mod_cast h
  have hratio:(cutCapacity I.network U:ℝ) / ((U.card:ℝ) * Uᶜ.card)≤
      ρ * (certificate.flow.value:ℝ):=by
    change (ratioCost I.network I.weights U:ℝ)≤ _ at ratio
    simpa only [ratioCost,hmass,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast] using ratio
  have hcap:=(div_le_iff₀ (mul_pos hleft hright)).mp hratio
  have hL:(U.card:ℝ)≤ (2 * n:ℕ):=by
    exact_mod_cast (show U.card≤ 2 * n by simpa using Finset.card_le_univ U)
  have hR:(Uᶜ.card:ℝ)≤ (2 * n:ℕ):=by
    exact_mod_cast (show Uᶜ.card≤ 2 * n by simpa using Finset.card_le_univ Uᶜ)
  have hproduct:(U.card:ℝ) * Uᶜ.card≤ ((2 * n:ℕ):ℝ) ^ 2:=by
    simpa only [pow_two] using mul_le_mul hL hR hright.le (by positivity)
  have hflow:=mul_le_mul_of_nonneg_left low_value.le nonnegative
  have hscale:0≤ ρ * (1 / γ):=mul_nonneg nonnegative (by positivity)
  have hbound:(cutCapacity I.network U:ℝ)≤ ρ * (2 * n:ℕ) ^ 2 / γ:=by
    calc
      (cutCapacity I.network U:ℝ)≤ (ρ * (certificate.flow.value:ℝ)) *
          ((U.card:ℝ) * Uᶜ.card):=hcap
      _≤ (ρ * (1 / γ)) * ((U.card:ℝ) * Uᶜ.card):=
        mul_le_mul_of_nonneg_right hflow (mul_nonneg hleft.le hright.le)
      _≤ (ρ * (1 / γ)) * ((2 * n:ℕ):ℝ) ^ 2:=mul_le_mul_of_nonneg_left hproduct hscale
      _=ρ * (2 * n:ℕ) ^ 2 / γ:=by ring
  have hlt:=hbound.trans_lt large_capacity
  change (cutCapacity I.network U:ℝ≥0) < (large:ℝ≥0)
  exact_mod_cast hlt

theorem flow_or_separation {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0)
    (certificate:Lax455465.FlowCutCertificate.Certificate (2 * n)) (ρ γ:ℝ)
    (nonnegative:0≤ ρ) (positive:0 < γ)
    (admissible:AdmissibleCut (splitInstance G x large).weights certificate.cut)
    (flow_valid:IsArcConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights (certificate.flow.value:ℝ≥0) certificate.flow.flow)
    (ratio:(ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights certificate.cut:ℝ)≤
        ρ * (certificate.flow.value:ℝ))
    (large_capacity:ρ * (2 * n:ℕ) ^ 2 / γ < (large:ℝ)):
    ((1 / γ≤ (certificate.flow.value:ℝ))∧
      IsArcConcurrentFlow .directed (splitInstance G x large).network
        (splitInstance G x large).weights (certificate.flow.value:ℝ≥0) certificate.flow.flow)∨
    ((leftShore certificate.cut).Nonempty∧ (rightShore certificate.cut).Nonempty∧
      leftShore certificate.cut ∪ rightShore certificate.cut=Finset.univ∧
      (∀ u∈ leftShore certificate.cut \ rightShore certificate.cut,
        ∀ v∈ rightShore certificate.cut \ leftShore certificate.cut, ¬G.Adj u v)∧
      (∑ v∈ leftShore certificate.cut ∩ rightShore certificate.cut, (x v:ℝ))≤
        4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ):=by
  by_cases hhigh:1 / γ≤ (certificate.flow.value:ℝ)
  · exact Or.inl ⟨hhigh,flow_valid⟩
  · have hlow:(certificate.flow.value:ℝ) < 1 / γ:=lt_of_not_ge hhigh
    have hsmall:=small_cut_of_low_flow G x large certificate ρ γ nonnegative positive
      admissible ratio hlow large_capacity
    have hnonempty:certificate.cut.Nonempty:=by
      by_contra he
      have hzero:=Finset.not_nonempty_iff_eq_empty.mp he
      have h:=admissible.1
      simp [hzero,mass] at h
    have hproper:certificate.cutᶜ.Nonempty:=by
      by_contra he
      have hzero:=Finset.not_nonempty_iff_eq_empty.mp he
      have h:=admissible.2
      simp [hzero,mass] at h
    obtain ⟨hA,hB,hcover,hsep,_,_⟩:=
      Lax263307Proofs.VertexSplitting.small_cut_separation G x large certificate.cut hsmall hnonempty hproper
    have hratio:(ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights certificate.cut:ℝ)≤ ρ / γ:=by
      calc
        _≤ ρ * (certificate.flow.value:ℝ):=ratio
        _≤ ρ * (1 / γ):=mul_le_mul_of_nonneg_left hlow.le nonnegative
        _=ρ / γ:=by ring
    have hcost:=Lax263307Proofs.VertexSplitting.separator_cost_bound G x large certificate.cut
      (ρ / γ) (div_nonneg nonnegative positive.le) hsmall admissible hratio
    right
    refine ⟨hA,hB,hcover,hsep, ?_⟩
    calc
      _≤ 4 * (ρ / γ) * (leftShore certificate.cut).card * (rightShore certificate.cut).card:=hcost
      _=4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ:=by ring

end Lax263307Proofs.VertexSplitting

end

section

namespace Lax263307Proofs.SplitPathProjection

open scoped NNReal NNRat
open Lax263307.VertexSplitting Lax263307.SplitPathProjection
open Lax263307Proofs.VertexSplitting
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

theorem minus_ne_plus {n:ℕ} (u v:Fin n):minus u ≠ plus v:=by
  intro h
  have hv:=congrArg Fin.val h
  dsimp [minus,plus] at hv
  omega

theorem plus_injective (n:ℕ):Function.Injective (plus (n:=n)):=by
  intro u v h
  have hv:=congrArg Fin.val h
  apply Fin.ext
  dsimp [plus] at hv
  omega

theorem minus_mem_expand {n:ℕ} (Q:List (Fin n)) (u:Fin n) (hu:u∈ Q):
    minus u∈ expandRoute Q:=by
  exact List.mem_flatMap.mpr ⟨u,hu,by simp⟩

theorem minus_injective (n:ℕ):Function.Injective (minus (n:=n)):=by
  intro u v h
  simpa only [original_minus] using congrArg original h

theorem capacity_arc_count_count {n:ℕ} (Q:List (Fin n)) (v:Fin n):
    ((expandRoute Q).zip (expandRoute Q).tail).count (minus v,plus v)=Q.count v:=by
  induction Q with
  | nil => simp [expandRoute]
  | cons u Q ih =>
    by_cases huv:u=v
    · subst u
      cases Q with
      | nil => simp [expandRoute]
      | cons w Q =>
        have hcross:(plus v,minus w) ≠ (minus v,plus v):=by
          intro he
          exact minus_ne_plus v v (congrArg Prod.fst he).symm
        change ((minus v,plus v)::(plus v,minus w)::
          ((expandRoute (w::Q)).zip (expandRoute (w::Q)).tail)).count (minus v,plus v)=_
        rw [List.count_cons_self,List.count_cons_of_ne hcross,ih,List.count_cons_self]
    · have hfirst:(minus u,plus u) ≠ (minus v,plus v):=by
        intro he
        exact huv (minus_injective n (congrArg Prod.fst he))
      cases Q with
      | nil => simp [expandRoute,hfirst,huv]
      | cons w Q =>
        have hcross:(plus u,minus w) ≠ (minus v,plus v):=by
          intro he
          exact minus_ne_plus v u (congrArg Prod.fst he).symm
        change ((minus u,plus u)::(plus u,minus w)::
          ((expandRoute (w::Q)).zip (expandRoute (w::Q)).tail)).count (minus v,plus v)=_
        rw [List.count_cons_of_ne hfirst,List.count_cons_of_ne hcross,ih,
          List.count_cons_of_ne huv]

theorem capacity_arc_count {n:ℕ} (Q:List (Fin n)) (simple:Q.Nodup) (v:Fin n):
    ((expandRoute Q).zip (expandRoute Q).tail).count (minus v,plus v) =
      if v∈ Q then 1 else 0:=by
  rw [capacity_arc_count_count]
  by_cases hv:v∈ Q
  · rw [if_pos hv]
    exact List.nodup_iff_count_eq_one.mp simple v hv
  · rw [if_neg hv]
    exact List.count_eq_zero.mpr hv

theorem project_simple_path_aux {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (P:List (Fin (2 * n))) (u v:Fin n)
    (simple:P.Nodup)
    (chain:P.IsChain (fun a b => 0 < (splitInstance G x large).capacity a b))
    (start:P.head?=some (minus u)) (finish:P.getLast?=some (plus v)):
    ∃ Q:List (Fin n),P=expandRoute Q∧ Q.Nodup∧ Q.IsChain G.Adj∧
      Q.head?=some u∧ Q.getLast?=some v:=by
  cases P with
  | nil => simp at start
  | cons a rest =>
    have ha:a=minus u:=by simpa using start
    subst a
    cases rest with
    | nil =>
      have heq:minus u=plus v:=by simpa using finish
      exact (minus_ne_plus u v heq).elim
    | cons b tail =>
      have hfirst:=(List.isChain_cons_cons.mp chain).1
      rw [capacity_minus] at hfirst
      have hb:b=plus u:=by
        by_contra hb
        simp [hb] at hfirst
      subst b
      cases tail with
      | nil =>
        have huv:u=v:=plus_injective n (by simpa using finish)
        subst v
        exact ⟨[u],rfl,by simp,by simp,rfl,rfl⟩
      | cons c tail =>
        have hsecond:=(List.isChain_cons_cons.mp (List.isChain_cons_cons.mp chain).2).1
        rcases port_cases c with hc | hc
        · let w:=original c
          have hcap:0 < (splitInstance G x large).capacity (plus u) (minus w):=hc ▸ hsecond
          rw [capacity_plus_minus] at hcap
          have hne:u ≠ w:=by
            intro huw
            have hnot:=(List.nodup_cons.mp simple).1
            apply hnot
            exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
              (Or.inl (hc.trans (congrArg minus huw.symm)).symm)))
          have huw:G.Adj u w:=by
            by_contra hadj
            simp [hne,hadj] at hcap
          have htail_simple:(minus w::tail).Nodup:=by
            exact hc ▸ (List.nodup_cons.mp (List.nodup_cons.mp simple).2).2
          have htail_chain:(minus w::tail).IsChain
              (fun a b => 0 < (splitInstance G x large).capacity a b):=by
            exact hc ▸ (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp chain).2).2
          have htail_finish:(minus w::tail).getLast?=some (plus v):=by
            have hlast:(c::tail).getLast?=some (plus v):=by
              simpa only [List.getLast?_cons_cons] using finish
            exact hc ▸ hlast
          obtain ⟨Q,hQ,hnodup,hchain,hhead,hlast⟩:=project_simple_path_aux G x large
            (minus w::tail) w v htail_simple htail_chain rfl htail_finish
          have huQ:u∉ Q:=by
            intro hu
            have hnot:=(List.nodup_cons.mp simple).1
            apply hnot
            right
            rw [hc,hQ]
            exact minus_mem_expand Q u hu
          have hchain':(u::Q).IsChain G.Adj:=by
            apply List.IsChain.cons hchain
            intro z hz
            have hzw:z=w:=by simpa [hhead,eq_comm] using hz
            simpa [hzw] using huw
          refine ⟨u::Q, ?_,List.nodup_cons.mpr ⟨huQ,hnodup⟩,hchain',rfl, ?_⟩
          · simp only [expandRoute,List.flatMap_cons,List.cons_append,List.nil_append]
            rw [hc,hQ]
            rfl
          · have hnonempty:Q ≠ []:=by intro h; simp [h] at hhead
            simpa only [List.getLast?_cons_of_ne_nil hnonempty] using hlast
        · rw [hc,capacity_plus_plus] at hsecond
          simp at hsecond
termination_by P.length
decreasing_by simp_wf; subst_vars; simp only [List.length_cons]; omega

theorem project_simple_path {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (P:List (Fin (2 * n))) (u v:Fin n)
    (simple:P.Nodup)
    (chain:P.IsChain (fun a b => 0 < (splitInstance G x large).capacity a b))
    (start:P.head?=some (minus u)) (finish:P.getLast?=some (plus v)):
    ∃ Q:List (Fin n),P=expandRoute Q∧ Q.Nodup∧ Q.IsChain G.Adj∧
      Q.head?=some u∧ Q.getLast?=some v:=
  project_simple_path_aux G x large P u v simple chain start finish

theorem chain_of_zip {α:Type} (P:List α) (R:α→ α→ Prop):
    (∀ p∈ P.zip P.tail,R p.1 p.2)→ P.IsChain R:=by
  induction P with
  | nil => intro _; simp
  | cons a P ih =>
    intro h
    cases P with
    | nil => simp
    | cons b P =>
      apply List.isChain_cons_cons.mpr
      refine ⟨h (a,b) (by simp), ?_⟩
      apply ih
      intro p hp
      exact h p (by simpa only [List.tail_cons,List.zip_cons_cons,List.mem_cons] using Or.inr hp)

theorem positive_support_chain {N:ℕ} (network:Network N) (π:VertexWeight N)
    (f:ℝ≥0) (F:PathFlow N) (feasible:IsConcurrentFlow .directed network π f F)
    (P:List (Fin N)) (member:P∈ F.support):
    P.IsChain (fun a b => 0 < network.capacity a b):=by
  classical
  apply chain_of_zip
  rintro ⟨a,b⟩ hab
  have hF:0 < F P:=pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp member)
  have hc:(0:ℝ≥0) < (P.zip P.tail).count (a,b):=by
    exact_mod_cast List.count_pos_iff.mpr hab
  have hterm:=mul_pos hF hc
  have hsum:F P * ((P.zip P.tail).count (a,b):ℝ≥0)≤ arcLoad F a b:=
    Finset.single_le_sum (f:=fun Q => F Q * ((Q.zip Q.tail).count (a,b):ℝ≥0))
      (fun _ _ => bot_le) member
  exact (hterm.trans_le hsum).trans_le (feasible.2.1 a b)

theorem split_support_projection {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (large:ℚ≥0) (f:ℝ≥0) (F:PathFlow (2 * n))
    (feasible:IsConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F)
    (P:List (Fin (2 * n))) (member:P∈ F.support) (u v:Fin n)
    (start:P.head?=some (minus u)) (finish:P.getLast?=some (plus v)):
    ∃ Q:List (Fin n),P=expandRoute Q∧ Q.Nodup∧ Q.IsChain G.Adj∧
      Q.head?=some u∧ Q.getLast?=some v:=by
  have hsimple:=(feasible.1 P member).2
  have hchain:=positive_support_chain (splitInstance G x large).network
    (splitInstance G x large).weights f F feasible P member
  have hchain':P.IsChain (fun a b => 0 < (splitInstance G x large).capacity a b):=by
    apply hchain.imp
    intro a b h
    change 0 < ((splitInstance G x large).capacity a b:ℝ≥0) at h
    exact_mod_cast h
  exact Lax263307Proofs.SplitPathProjection.project_simple_path G x large P u v hsimple hchain' start finish

end Lax263307Proofs.SplitPathProjection

end

section

namespace Lax455465Proofs.PathSimplification
open List
variable {α:Type*} [DecidableEq α]

def suffixAt (a:α) (xs:List α):List α:=xs.dropWhile (fun b => decide (b ≠ a))

def simplify:List α→ List α
  | [] => []
  | a::xs => let ys:=simplify xs
    if a∈ ys then suffixAt a ys else a::ys

def arcs (xs:List α):=xs.zip xs.tail

@[simp] theorem arcs_nil:arcs ([]:List α)=[]:=rfl
@[simp] theorem arcs_singleton (a:α):arcs [a]=[]:=rfl
@[simp] theorem arcs_cons_cons (a b:α) (xs:List α):
    arcs (a::b::xs)=(a,b)::arcs (b::xs):=rfl

theorem from_sublist (a:α) (xs:List α):suffixAt a xs <+ xs:=List.dropWhile_sublist _

theorem from_head (a:α) (xs:List α) (ha:a∈ xs):(suffixAt a xs).head?=some a:=by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    by_cases he:b=a
    · subst b; simp [suffixAt]
    · have hx:a∈xs:=by simpa [Ne.symm he] using ha
      simpa [suffixAt,he] using ih hx

theorem from_last (a:α) (xs:List α) (ha:a∈xs):(suffixAt a xs).getLast?=xs.getLast?:=by
  induction xs with
  | nil => cases ha
  | cons b xs ih =>
    by_cases he:b=a
    · subst b; simp [suffixAt]
    · have hx:a∈xs:=by simpa [Ne.symm he] using ha
      have hs:suffixAt a (b::xs)=suffixAt a xs:=by simp [suffixAt,he]
      rw [hs,ih hx,List.getLast?_cons_of_ne_nil (List.ne_nil_of_mem hx)]

theorem arcs_from_sublist (a:α) (xs:List α):arcs (suffixAt a xs) <+ arcs xs:=by
  induction xs with
  | nil => simp [suffixAt]
  | cons b xs ih =>
    by_cases he:b=a
    · subst b; simp [suffixAt]
    · have hs:suffixAt a (b::xs)=suffixAt a xs:=by simp [suffixAt,he]
      rw [hs]
      exact ih.trans (by cases xs <;> simp)

theorem sublist (xs:List α):simplify xs <+ xs:=by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · exact ((from_sublist a (simplify xs)).trans ih).cons a
    · exact ih.cons_cons a

theorem nodup (xs:List α):(simplify xs).Nodup:=by
  induction xs with
  | nil => simp [simplify]
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · exact ih.sublist (from_sublist a (simplify xs))
    · exact List.nodup_cons.mpr ⟨h,ih⟩

@[simp] theorem head (xs:List α):(simplify xs).head?=xs.head?:=by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [simplify,List.head?_cons]
    split_ifs with h
    · exact from_head a _ h
    · rfl

@[simp] theorem eq_nil (xs:List α):simplify xs=[]↔ xs=[]:=by
  constructor
  · intro h
    have hh:=head xs
    rw [h] at hh
    cases xs <;> simp_all
  · intro h; subst xs; rfl

@[simp] theorem last (xs:List α):(simplify xs).getLast?=xs.getLast?:=by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · rw [from_last a _ h,ih]
      have hne:xs ≠ []:=by intro he; subst xs; simp [simplify] at h
      cases xs with
      | nil => exact (hne rfl).elim
      | cons b xs => rfl
    · cases xs with
      | nil => rfl
      | cons b xs =>
        have hne:simplify (b::xs) ≠ []:=by simp
        cases hy:simplify (b::xs) with
        | nil => exact (hne hy).elim
        | cons c ys =>
          simpa only [hy,List.getLast?_cons_cons] using ih

theorem arcs_sublist (xs:List α):arcs (simplify xs) <+ arcs xs:=by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [simplify]
    split_ifs with h
    · exact ((arcs_from_sublist a (simplify xs)).trans ih).trans (by cases xs <;> simp)
    · cases xs with
      | nil => rfl
      | cons b xs =>
        have hh:=head (b::xs)
        cases hy:simplify (b::xs) with
        | nil => simp [hy] at hh
        | cons c ys =>
          have hc:c=b:=by simpa [hy] using hh
          subst c
          simp only [hy,arcs_cons_cons] at ih ⊢
          exact ih.cons_cons (a,b)

theorem distinct_endpoints {xs:List α} {s t:α} (hne:s ≠ t)
    (hs:xs.head?=some s) (ht:xs.getLast?=some t):
    2≤ (simplify xs).length∧ (simplify xs).Nodup∧
      (simplify xs).head?=some s∧ (simplify xs).getLast?=some t:=by
  have hh:=(head xs).trans hs
  have hl:=(last xs).trans ht
  refine ⟨?_,nodup xs,hh,hl⟩
  cases he:simplify xs with
  | nil => simp [he] at hh
  | cons a ys =>
    cases ys with
    | nil => simp only [he,List.head?_cons,Option.some.injEq] at hh
             simp only [he,List.getLast?_singleton,Option.some.injEq] at hl
             exact (hne (hh.symm.trans hl)).elim
    | cons b ys => simp

end Lax455465Proofs.PathSimplification

end

section

open scoped BigOperators
namespace Lax455465Proofs.PathCounting
open PathSimplification
variable {α:Type*} [Fintype α] [DecidableEq α]

def count (xs:List α) (u v:α):ℚ:=(arcs xs).count (u,v)

@[simp] theorem count_nil (u v:α):count [] u v=0:=rfl
@[simp] theorem count_singleton (a u v:α):count [a] u v=0:=rfl

theorem count_cons_cons (a b u v:α) (xs:List α):
    count (a::b::xs) u v=count (b::xs) u v+(if a=u∧ b=v then 1 else 0):=by
  simp only [count,arcs_cons_cons,List.count_cons,Nat.cast_add]
  by_cases he:a=u∧ b=v
  · rcases he with ⟨rfl,rfl⟩
    simp
  · have hh:(u,v) ≠ (a,b):=by simpa [Prod.mk.injEq,eq_comm] using he
    simp [he,hh]

theorem arcs_nodup {xs:List α} (h:xs.Nodup):(arcs xs).Nodup:=by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      rw [arcs_cons_cons,List.nodup_cons]
      refine ⟨?_,ih (List.nodup_cons.mp h).2⟩
      intro he
      exact (List.nodup_cons.mp h).1 (List.of_mem_zip he).1

theorem balance {xs:List α} {s t:α} (hs:xs.head?=some s)
    (ht:xs.getLast?=some t) (u:α):
    (∑ v,count xs u v)-(∑ v,count xs v u)=
      (if u=s then 1 else 0)-(if u=t then 1 else 0):=by
  induction xs generalizing s with
  | nil => simp at hs
  | cons a xs ih =>
    have ha:a=s:=by simpa using hs
    subst a
    cases xs with
    | nil =>
      have hst:s=t:=by simpa using ht
      subst t
      simp
    | cons b xs =>
      have hh:=ih rfl (by simpa using ht)
      simp only [count_cons_cons,Finset.sum_add_distrib]
      have hsum₁:(∑ v:α,if s=u∧ b=v then (1:ℚ) else 0)=if u=s then 1 else 0:=by
        by_cases he:u=s
        · subst u; simp
        · simp [he,Ne.symm he]
      have hsum₂:(∑ v:α,if s=v∧ b=u then (1:ℚ) else 0)=if u=b then 1 else 0:=by
        by_cases he:u=b
        · subst u; simp
        · simp [he,Ne.symm he]
      rw [hsum₁,hsum₂]
      linarith

end Lax455465Proofs.PathCounting

end

section

open scoped BigOperators
namespace Lax455465Proofs.RealPositivePath
open PathSimplification
variable {α:Type*} [Fintype α] [DecidableEq α]

def Balance (g:α→ α→ ℝ) (s t:α) (a:ℝ):Prop:=
  ∀ u, (∑ v,g u v) - (∑ v,g v u) =
    (if u=s then a else 0) - (if u=t then a else 0)

theorem reachable (g:α→ α→ ℝ) (hg:∀ u v,0≤ g u v)
    (s t:α) (a:ℝ) (ha:0 < a) (hbal:Balance g s t a):
    Relation.ReflTransGen (fun u v => 0 < g u v) s t:=by
  classical
  by_contra ht
  let R:Finset α:=Finset.univ.filter fun u =>
    Relation.ReflTransGen (fun u v => 0 < g u v) s u
  have hmem (u:α):u∈ R↔ Relation.ReflTransGen (fun u v => 0 < g u v) s u:=by
    simp [R]
  have hsR:s∈ R:=(hmem s).mpr .refl
  have htR:t∉ R:=fun h => ht ((hmem t).mp h)
  have houtzero:∀ u∈ R, ∀ v∉ R,g u v=0:=by
    intro u hu v hv
    have hn:¬ 0 < g u v:=fun hp => hv ((hmem v).mpr (((hmem u).mp hu).tail hp))
    exact le_antisymm (le_of_not_gt hn) (hg u v)
  have hout:(∑ u∈ R, ∑ v,g u v)=∑ u∈ R, ∑ v∈ R,g u v:=by
    apply Finset.sum_congr rfl
    intro u hu
    exact (Finset.sum_subset (Finset.subset_univ R) (fun v _ hv => houtzero u hu v hv)).symm
  have hin:(∑ u∈ R, ∑ v∈ R,g u v)≤ ∑ u∈ R, ∑ v,g v u:=by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro u hu
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun v _ _ => hg v u)
  have hsum:=Finset.sum_congr (s₁:=R) (s₂:=R) rfl (fun u _ => hbal u)
  simp only [Finset.sum_sub_distrib] at hsum
  have hsource:(∑ u∈ R,if u=s then a else 0)=a:=by simp [hsR]
  have htarget:(∑ u∈ R,if u=t then a else 0)=0:=by simp [htR]
  rw [hsource,htarget,sub_zero,hout] at hsum
  linarith

theorem walk_of_reachable (g:α→ α→ ℝ) {s t:α}
    (h:Relation.ReflTransGen (fun u v => 0 < g u v) s t):
    ∃ xs:List α,xs.head?=some s∧ xs.getLast?=some t∧
      ∀ e∈ arcs xs,0 < g e.1 e.2:=by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[t],rfl,rfl,by simp⟩
  | @head u v huv hvt ih =>
    obtain ⟨xs,hs,ht,he⟩:=ih
    cases xs with
    | nil => simp at hs
    | cons v' xs =>
      have hv:v'=v:=by simpa using hs
      subst v'
      refine ⟨u::v::xs,rfl,by simpa using ht, ?_⟩
      intro e he'
      rcases (by simpa only [arcs_cons_cons,List.mem_cons] using he':e=(u,v)∨ e∈ arcs (v::xs)) with rfl | he'
      · exact huv
      · exact he e he'

theorem exists_path (g:α→ α→ ℝ) (hg:∀ u v,0≤ g u v)
    (s t:α) (hst:s ≠ t) (a:ℝ) (ha:0 < a) (hbal:Balance g s t a):
    ∃ xs:List α,xs.head?=some s∧ xs.getLast?=some t∧ xs.Nodup∧
      2≤ xs.length∧ ∀ e∈ arcs xs,0 < g e.1 e.2:=by
  obtain ⟨xs,hs,ht,he⟩:=walk_of_reachable g (reachable g hg s t a ha hbal)
  obtain ⟨hlen,hn,hs',ht'⟩:=distinct_endpoints hst hs ht
  exact ⟨simplify xs,hs',ht',hn,hlen,fun e h => he e ((arcs_sublist xs).subset h)⟩

end Lax455465Proofs.RealPositivePath

end

section

open scoped BigOperators
namespace Lax455465Proofs.RealPathCounting
open PathSimplification
variable {α:Type*} [Fintype α] [DecidableEq α]

def count (xs:List α) (u v:α):ℝ:=(arcs xs).count (u,v)

theorem count_eq {xs:List α} (h:xs.Nodup) (u v:α):
    count xs u v=if (u,v)∈ arcs xs then 1 else 0:=by
  simp only [count, (PathCounting.arcs_nodup h).count]
  split_ifs <;> norm_num

theorem nonnegative (xs:List α) (u v:α):0≤ count xs u v:=by
  unfold count
  positivity

theorem balance {xs:List α} {s t:α} (hs:xs.head?=some s)
    (ht:xs.getLast?=some t) (u:α):
    (∑ v,count xs u v) - (∑ v,count xs v u) =
      (if u=s then 1 else 0) - (if u=t then 1 else 0):=by
  have h:=congrArg (fun q:ℚ => (q:ℝ)) (PathCounting.balance hs ht u)
  simpa only [PathCounting.count,Rat.cast_sub,Rat.cast_sum,Rat.cast_natCast,
    apply_ite,Rat.cast_one,Rat.cast_zero,count] using h

end Lax455465Proofs.RealPathCounting

end

section

open scoped BigOperators
namespace Lax455465Proofs.RealPathSubtraction
open PathSimplification RealPositivePath
variable {α:Type*} [Fintype α] [DecidableEq α]

def residual (g:α→ α→ ℝ) (xs:List α) (w:ℝ) (u v:α):ℝ:=
  g u v-w*RealPathCounting.count xs u v

noncomputable def support (g:α→ α→ ℝ):Finset (α×α):=
  Finset.univ.filter fun e => 0 < g e.1 e.2

theorem residual_le (g:α→ α→ ℝ) (xs:List α) (w:ℝ) (hw:0≤ w) (u v:α):
    residual g xs w u v≤ g u v:=by
  unfold residual
  exact sub_le_self _ (mul_nonneg hw (RealPathCounting.nonnegative xs u v))

theorem residual_nonnegative (g:α→ α→ ℝ) (hg:∀ u v,0≤ g u v)
    (xs:List α) (hn:xs.Nodup) (w:ℝ)
    (hw:∀ e∈arcs xs,w≤ g e.1 e.2):∀ u v,0≤ residual g xs w u v:=by
  intro u v
  rw [residual,RealPathCounting.count_eq hn]
  by_cases he:(u,v)∈arcs xs
  · simp only [if_pos he,mul_one]
    exact sub_nonneg.mpr (hw (u,v) he)
  · simp only [if_neg he,mul_zero,sub_zero]
    exact hg u v

theorem residual_balance (g:α→ α→ ℝ) (s t:α) (a:ℝ)
    (hg:Balance g s t a) (xs:List α)
    (hs:xs.head?=some s) (ht:xs.getLast?=some t) (w:ℝ):
    Balance (residual g xs w) s t (a-w):=by
  intro u
  simp only [residual,Finset.sum_sub_distrib,←Finset.mul_sum]
  have hp:=RealPathCounting.balance hs ht u
  have hb:=hg u
  have hpw:=congrArg (fun z:ℝ => w*z) hp
  split_ifs at hpw hb ⊢ <;> nlinarith [hpw]

theorem support_subset (g:α→ α→ ℝ) (xs:List α) (w:ℝ) (hw:0≤ w):
    support (residual g xs w) ⊆ support g:=by
  intro e he
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
  exact he.trans_le (residual_le g xs w hw e.1 e.2)

theorem support_decreases (g:α→ α→ ℝ) (xs:List α) (hn:xs.Nodup)
    (w:ℝ) (hw:0 < w) (e:α×α) (he:e∈arcs xs) (hge:g e.1 e.2=w):
    (support (residual g xs w)).card < (support g).card:=by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨support_subset g xs w hw.le,?_⟩
  intro hsame
  have hmem:e∈support g:=by simp [support,hge,hw]
  rw [←hsame] at hmem
  have hz:residual g xs w e.1 e.2=0:=by
    rw [residual,RealPathCounting.count_eq hn,if_pos he,hge]
    ring
  simp [support,hz] at hmem

theorem exists_amount (g:α→ α→ ℝ) (xs:List α)
    (hx:2≤ xs.length) (hpos:∀ e∈arcs xs,0 < g e.1 e.2) (a:ℝ) (ha:0 < a):
    ∃ w,0 < w∧ w≤ a∧ (∀ e∈arcs xs,w≤ g e.1 e.2)∧
      (w=a∨ ∃ e∈arcs xs,g e.1 e.2=w):=by
  have hne:(arcs xs).toFinset.Nonempty:=by
    cases xs with
    | nil => simp at hx
    | cons u xs =>
      cases xs with
      | nil => simp at hx
      | cons v xs => exact ⟨(u,v),by simp⟩
  let b:=(arcs xs).toFinset.inf' hne (fun e => g e.1 e.2)
  obtain ⟨e,he,heq⟩:=Finset.exists_mem_eq_inf' hne (fun e => g e.1 e.2)
  have hb:0 < b:=by rw [show b=g e.1 e.2 from heq]; exact hpos e (List.mem_toFinset.mp he)
  refine ⟨min a b,lt_min ha hb,min_le_left _ _,?_,?_⟩
  · intro e he
    exact (min_le_right _ _).trans (Finset.inf'_le _ (List.mem_toFinset.mpr he))
  · by_cases hab:a≤ b
    · exact Or.inl (min_eq_left hab)
    · exact Or.inr ⟨e,List.mem_toFinset.mp he,by rw [min_eq_right (le_of_not_ge hab)]; exact heq.symm⟩

end Lax455465Proofs.RealPathSubtraction

end

section

open scoped BigOperators
namespace Lax455465Proofs.RealFlowDecomposition
open PathSimplification RealPositivePath RealPathSubtraction
variable {α:Type*} [Fintype α] [DecidableEq α]

abbrev Records (α:Type*):=List (List α × ℝ)

def mass (rs:Records α):ℝ:=(rs.map Prod.snd).sum
def load (rs:Records α) (u v:α):ℝ:=
  (rs.map fun r => r.2*RealPathCounting.count r.1 u v).sum
def Valid (s t:α) (rs:Records α):Prop:=
  ∀ r∈rs,0 < r.2∧ r.1.head?=some s∧ r.1.getLast?=some t∧ r.1.Nodup

@[simp] theorem mass_nil:mass ([]:Records α)=0:=rfl
@[simp] theorem mass_cons (r:List α×ℝ) (rs:Records α):mass (r::rs)=r.2+mass rs:=rfl
@[simp] theorem load_nil (u v:α):load ([]:Records α) u v=0:=rfl
@[simp] theorem load_cons (r:List α×ℝ) (rs:Records α) (u v:α):
    load (r::rs) u v=r.2*RealPathCounting.count r.1 u v+load rs u v:=rfl

theorem exists_records (g:α→ α→ ℝ) (hg:∀ u v,0≤ g u v)
    (s t:α) (hst:s ≠ t) (a:ℝ) (ha:0≤ a) (hbal:Balance g s t a):
    ∃ rs:Records α,Valid s t rs∧ mass rs=a∧
      (∀ u v,load rs u v≤ g u v)∧ rs.length≤ (support g).card+1:=by
  have aux:∀ m (g:α→ α→ ℝ) (a:ℝ),
      (support g).card=m→ (∀ u v,0≤ g u v)→ 0≤ a→
      Balance g s t a→
      ∃ rs:Records α,Valid s t rs∧ mass rs=a∧
        (∀ u v,load rs u v≤ g u v)∧ rs.length≤ (support g).card+1:=by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g a hcard hg ha hbal
      by_cases haz:a=0
      · subst a
        exact ⟨[],by simp [Valid],rfl,hg,by simp⟩
      have hapos:0 < a:=lt_of_le_of_ne ha (Ne.symm haz)
      obtain ⟨xs,hs,ht,hn,hsize,hpos⟩:=exists_path g hg s t hst a hapos hbal
      obtain ⟨w,hw,hwa,hwg,hstop⟩:=exists_amount g xs hsize hpos a hapos
      have hres:=residual_nonnegative g hg xs hn w hwg
      have hvalid:0 < w∧ xs.head?=some s∧ xs.getLast?=some t∧ xs.Nodup:= ⟨hw,hs,ht,hn⟩
      rcases hstop with hwaeq | ⟨e,he,hew⟩
      · refine ⟨[(xs,w)],?_,by simpa using hwaeq,?_,by simp⟩
        · intro r hr
          have he:r=(xs,w):=by simpa using hr
          subst r
          exact hvalid
        · intro u v
          have hh:=hres u v
          simp only [load_cons,load_nil,add_zero]
          unfold RealPathSubtraction.residual at hh
          linarith
      · have hdec:=support_decreases g xs hn w hw e he hew
        obtain ⟨rs,hvalidrs,hmass,hload,hlen⟩:=
          ih (support (residual g xs w)).card (by omega) (residual g xs w) (a-w) rfl
            hres (sub_nonneg.mpr hwa) (residual_balance g s t a hbal xs hs ht w)
        refine ⟨(xs,w)::rs,?_,?_,?_,?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hvalid
          · exact hvalidrs r hr
        · simp only [mass_cons,hmass]
          ring
        · intro u v
          have hh:=hload u v
          simp only [load_cons]
          unfold RealPathSubtraction.residual at hh
          linarith
        · simp only [List.length_cons]
          omega
  exact aux (support g).card g a rfl hg ha hbal

end Lax455465Proofs.RealFlowDecomposition

end

section

open scoped BigOperators
namespace Lax455465Proofs.AcyclicFlowDecomposition
open PathSimplification PathSubtraction
variable {α:Type*} [Fintype α] [DecidableEq α]

abbrev Records (α:Type*):=List (List α × ℚ)

def mass (rs:Records α):ℚ:=(rs.map Prod.snd).sum
def load (rs:Records α) (u v:α):ℚ:=
  (rs.map fun r => r.2*PathCounting.count r.1 u v).sum

@[simp] theorem mass_nil:mass ([]:Records α)=0:=rfl
@[simp] theorem mass_cons (r:List α×ℚ) (rs:Records α):mass (r::rs)=r.2+mass rs:=rfl
@[simp] theorem load_nil (u v:α):load ([]:Records α) u v=0:=rfl
@[simp] theorem load_cons (r:List α×ℚ) (rs:Records α) (u v:α):
    load (r::rs) u v=r.2*PathCounting.count r.1 u v+load rs u v:=rfl

end Lax455465Proofs.AcyclicFlowDecomposition

end

section

open scoped BigOperators NNRat NNReal
namespace Lax455465Proofs.PathCertificateInterpretation
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open AcyclicFlowDecomposition

noncomputable def flow {n:ℕ}:Records (Fin n)→ PathFlow n
  | [] => 0
  | r::rs => Finsupp.single r.1 (r.2.toNNRat:ℝ≥0)+flow rs

theorem amount_cast (q:ℚ) (hq:0≤ q):((q.toNNRat:ℝ≥0):ℝ)=(q:ℝ):=by
  change (q.toNNRat:ℝ)=(q:ℝ)
  rw [←Rat.cast_nnratCast,Rat.coe_toNNRat q hq]

theorem arcLoad_add {n:ℕ} (F G:PathFlow n) (u v:Fin n):
    arcLoad (F+G) u v=arcLoad F u v+arcLoad G u v:=by
  simpa only [arcLoad,Finsupp.sum] using
    (Finsupp.sum_add_index' (f:=F) (g:=G)
      (h:=fun xs (w:ℝ≥0) => w*((xs.zip xs.tail).count (u,v):ℝ≥0))
      (fun _ => by simp) (fun _ _ _ => add_mul _ _ _))

theorem routed_add {n:ℕ} (F G:PathFlow n) (s t:Fin n):
    routed (F+G) s t=routed F s t+routed G s t:=by
  change (F+G).sum (fun xs w => if xs.head?=some s∧ xs.getLast?=some t then w else 0)=_
  rw [Finsupp.sum_add_index']
  · rfl
  · intro xs
    split_ifs <;> rfl
  · intro xs a b
    split_ifs <;> simp

theorem arcLoad_single {n:ℕ} (xs:List (Fin n)) (w:ℝ≥0) (u v:Fin n):
    arcLoad (Finsupp.single xs w) u v=w*((xs.zip xs.tail).count (u,v):ℝ≥0):=by
  simpa only [arcLoad,Finsupp.sum] using
    (Finsupp.sum_single_index (a:=xs) (b:=w)
      (h:=fun ys (w:ℝ≥0) => w*((ys.zip ys.tail).count (u,v):ℝ≥0)) (by simp))

theorem routed_single {n:ℕ} (xs:List (Fin n)) (w:ℝ≥0) (s t:Fin n):
    routed (Finsupp.single xs w) s t=if xs.head?=some s∧ xs.getLast?=some t then w else 0:=by
  change (Finsupp.single xs w).sum
    (fun ys z => if ys.head?=some s∧ ys.getLast?=some t then z else 0)=_
  exact Finsupp.sum_single_index (by split_ifs <;> rfl)

theorem arcLoad_cast {n:ℕ} (rs:Records (Fin n)) (h:∀ r∈rs,0≤ r.2) (u v:Fin n):
    (arcLoad (flow rs) u v:ℝ)=(load rs u v:ℝ):=by
  induction rs with
  | nil => simp [flow,arcLoad]
  | cons r rs ih =>
    have hr:=h r (by simp)
    have ht:∀ r'∈rs,0≤ r'.2:=fun r' hr' => h r' (by simp [hr'])
    rw [flow,arcLoad_add,arcLoad_single]
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,amount_cast r.2 hr,
      ih ht,load_cons,Rat.cast_add,Rat.cast_mul,PathCounting.count,Rat.cast_natCast,PathSimplification.arcs]

theorem support_mem {n:ℕ} (rs:Records (Fin n)) (xs:List (Fin n))
    (h:xs∈(flow rs).support):∃ r∈rs,r.1=xs:=by
  induction rs with
  | nil => simp [flow] at h
  | cons r rs ih =>
    have hh:=Finsupp.support_add h
    rcases Finset.mem_union.mp hh with hh | hh
    · have he:xs=r.1:=Finset.mem_singleton.mp (Finsupp.support_single_subset hh)
      exact ⟨r,by simp,he.symm⟩
    · obtain ⟨r',hr',he⟩:=ih hh
      exact ⟨r',by simp [hr'],he⟩

end Lax455465Proofs.PathCertificateInterpretation

end

section

open scoped BigOperators NNReal
namespace Lax455465Proofs.RealPathFlow
open Lax455465.ConcurrentFlow RealFlowDecomposition
open PathCertificateInterpretation (arcLoad_add arcLoad_single routed_add routed_single)

noncomputable def flow {n:ℕ}:Records (Fin n)→ PathFlow n
  | [] => 0
  | r::rs => Finsupp.single r.1 r.2.toNNReal + flow rs

theorem arcLoad_cast {n:ℕ} (rs:Records (Fin n)) (h:∀ r∈ rs,0≤ r.2) (u v:Fin n):
    (arcLoad (flow rs) u v:ℝ)=load rs u v:=by
  induction rs with
  | nil => simp [flow,arcLoad,load]
  | cons r rs ih =>
    have hr:=h r (by simp)
    have ht:∀ r'∈ rs,0≤ r'.2:=fun r' hr' => h r' (by simp [hr'])
    rw [flow,arcLoad_add,arcLoad_single]
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,
      Real.coe_toNNReal _ hr,ih ht,load_cons,RealPathCounting.count,PathSimplification.arcs]

theorem routed_self {n:ℕ} {s t:Fin n} {rs:Records (Fin n)}
    (h:Valid s t rs):(routed (flow rs) s t:ℝ)=mass rs:=by
  induction rs with
  | nil => simp [flow,routed,mass]
  | cons r rs ih =>
    have hr:=h r (by simp)
    have ht:Valid s t rs:=fun r' hr' => h r' (by simp [hr'])
    rw [flow,routed_add,routed_single,if_pos ⟨hr.2.1,hr.2.2.1⟩]
    simp only [NNReal.coe_add,Real.coe_toNNReal _ hr.1.le,ih ht,mass_cons]

theorem support_mem {n:ℕ} (rs:Records (Fin n)) (xs:List (Fin n))
    (h:xs∈ (flow rs).support):∃ r∈ rs,r.1=xs:=by
  induction rs with
  | nil => simp [flow] at h
  | cons r rs ih =>
    rcases Finset.mem_union.mp (Finsupp.support_add h) with hh | hh
    · have he:xs=r.1:=Finset.mem_singleton.mp (Finsupp.support_single_subset hh)
      exact ⟨r,by simp,he.symm⟩
    · obtain ⟨r',hr',he⟩:=ih hh
      exact ⟨r',by simp [hr'],he⟩

theorem isPathFlow {n:ℕ} {s t:Fin n} (hst:s ≠ t) {rs:Records (Fin n)}
    (h:Valid s t rs):IsPathFlow (flow rs):=by
  intro xs hxs
  obtain ⟨r,hr,rfl⟩:=support_mem rs xs hxs
  have hh:=h r hr
  refine ⟨?_,hh.2.2.2⟩
  cases he:r.1 with
  | nil => simp [he] at hh
  | cons u xs =>
    cases xs with
    | nil =>
      have hs:u=s:=by simpa [he] using hh.2.1
      have ht:u=t:=by simpa [he] using hh.2.2.1
      exact (hst (hs.symm.trans ht)).elim
    | cons v xs => simp [he]

end Lax455465Proofs.RealPathFlow

end

section

open scoped BigOperators NNReal
namespace Lax455465Proofs.PathFlowSums
open Lax455465.ConcurrentFlow
open PathCertificateInterpretation (arcLoad_add routed_add)

theorem isPathFlow_add {n:ℕ} {F G:PathFlow n} (hF:IsPathFlow F) (hG:IsPathFlow G):
    IsPathFlow (F+G):=by
  intro xs hxs
  rcases Finset.mem_union.mp (Finsupp.support_add hxs) with h | h
  · exact hF xs h
  · exact hG xs h

theorem isPathFlow_sum {n:ℕ} {ι:Type*} (S:Finset ι) (F:ι→ PathFlow n)
    (h:∀ i∈ S,IsPathFlow (F i)):IsPathFlow (∑ i∈ S,F i):=by
  classical
  induction S using Finset.induction_on with
  | empty => simp [IsPathFlow]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact isPathFlow_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem arcLoad_sum {n:ℕ} {ι:Type*} (S:Finset ι) (F:ι→ PathFlow n) (u v:Fin n):
    arcLoad (∑ i∈ S,F i) u v=∑ i∈ S,arcLoad (F i) u v:=by
  classical
  induction S using Finset.induction_on with
  | empty => simp [arcLoad]
  | @insert i S hi ih => rw [Finset.sum_insert hi,arcLoad_add,ih,Finset.sum_insert hi]

theorem routed_sum {n:ℕ} {ι:Type*} (S:Finset ι) (F:ι→ PathFlow n) (s t:Fin n):
    routed (∑ i∈ S,F i) s t=∑ i∈ S,routed (F i) s t:=by
  classical
  induction S using Finset.induction_on with
  | empty => simp [routed]
  | @insert i S hi ih => rw [Finset.sum_insert hi,routed_add,ih,Finset.sum_insert hi]

end Lax455465Proofs.PathFlowSums

end

section

open scoped BigOperators NNReal
namespace Lax455465Proofs.ArcToPath
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open RealPositivePath RealFlowDecomposition PathFlowSums

theorem commodity {n:ℕ} (s t:Fin n) (g:Fin n→ Fin n→ ℝ≥0)
    (a:ℝ≥0) (hst:s ≠ t)
    (hbal:Balance (fun u v => (g u v:ℝ)) s t (a:ℝ)):
    ∃ P:PathFlow n,IsPathFlow P∧ (∀ u v,arcLoad P u v≤ g u v)∧
      routed P s t=a:=by
  obtain ⟨rs,hvalid,hmass,hload,_⟩:=exists_records (fun u v => (g u v:ℝ))
    (fun u v => (g u v).coe_nonneg) s t hst (a:ℝ) a.coe_nonneg hbal
  have hpos:∀ r∈ rs,0≤ r.2:=fun r hr => (hvalid r hr).1.le
  refine ⟨RealPathFlow.flow rs,RealPathFlow.isPathFlow hst hvalid, ?_, ?_⟩
  · intro u v
    apply NNReal.coe_le_coe.mp
    rw [RealPathFlow.arcLoad_cast rs hpos]
    exact hload u v
  · apply NNReal.coe_injective
    rw [RealPathFlow.routed_self hvalid,hmass]

theorem exists_path_flow {n:ℕ} (kind:EdgeKind) (N:Network n)
    (π:VertexWeight n) (f:ℝ≥0) (F:ArcFlow n)
    (hF:IsArcConcurrentFlow kind N π f F):
    ∃ P:PathFlow n,IsConcurrentFlow kind N π f P∧
      ∀ u v,arcLoad P u v≤ totalArcLoad F u v:=by
  classical
  have hc:∀ s t, ∃ P:PathFlow n,IsPathFlow P∧
      (∀ u v,arcLoad P u v≤ F s t u v)∧
      (s ≠ t→ f * pairDemand kind π s t≤ routed P s t):=by
    intro s t
    by_cases hst:s=t
    · refine ⟨0,by simp [IsPathFlow], ?_, ?_⟩
      · intro u v
        simp [arcLoad]
      · intro hne
        exact (hne hst).elim
    · have hb:Balance (fun u v => (F s t u v:ℝ)) s t
          (f * pairDemand kind π s t:ℝ≥0):=by
        intro u
        simpa only [requiredSupply,if_neg hst,apply_ite,NNReal.coe_zero] using hF.2 s t u
      obtain ⟨P,hP,hload,hrouted⟩:=commodity s t (F s t) (f * pairDemand kind π s t) hst hb
      exact ⟨P,hP,hload,fun _ => hrouted.ge⟩
  choose P hP hload hdemand using hc
  let Q:PathFlow n:= ∑ s, ∑ t,P s t
  have hQ:IsPathFlow Q:=
    isPathFlow_sum _ _ (fun s _ => isPathFlow_sum _ _ (fun t _ => hP s t))
  have hloadQ:∀ u v,arcLoad Q u v≤ totalArcLoad F u v:=by
    intro u v
    simp only [Q,arcLoad_sum,totalArcLoad]
    exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hload s t u v
  refine ⟨Q, ⟨hQ, ?_, ?_⟩,hloadQ⟩
  · intro u v
    cases kind with
    | directed => exact (hloadQ u v).trans (hF.1 u v)
    | undirected => exact (add_le_add (hloadQ u v) (hloadQ v u)).trans (hF.1 u v)
  · intro s t hst
    apply (hdemand s t hst).trans
    simp only [Q,routed_sum]
    have h₁:routed (P s t) s t≤ ∑ j,routed (P s j) s t:=
      Finset.single_le_sum (f:=fun j => routed (P s j) s t)
        (fun _ _ => bot_le) (Finset.mem_univ t)
    have h₂:(∑ j,routed (P s j) s t)≤ ∑ i, ∑ j,routed (P i j) s t:=
      Finset.single_le_sum (f:=fun i => ∑ j,routed (P i j) s t)
        (fun _ _ => bot_le) (Finset.mem_univ s)
    exact h₁.trans h₂

end Lax455465Proofs.ArcToPath

end

section

namespace Lax263307Proofs.RouteDistributions

open Lax263307.RouteDistributions

noncomputable def tripleEquiv (n q:ℕ):Fin (n * (n * q)) ≃ Fin n × (Fin n × Fin q):=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

theorem sum_triples {n q:ℕ} (f:Fin n × (Fin n × Fin q)→ ℝ):
    (∑ j,f (tripleEquiv n q j))=∑ u, ∑ v, ∑ i,f (u,v,i):=by
  rw [(tripleEquiv n q).sum_comp]
  simp only [Fintype.sum_prod_type]

open Lax263307.RoutingNormalization

theorem finite_routes {n q:ℕ} (G:SimpleGraph (Fin n)) (hn:0 < n)
    (w:Fin q→ ℝ) (E:Fin n→ Fin n→ Fin q→ Prop)
    (w_nonnegative:∀ i,0≤ w i) (γ:ℝ) (γ_positive:0 < γ)
    (lower:∀ u v,1 / γ≤ routed w E u v)
    (Q:Fin q→ List (Fin n))
    (routes:∀ u v i,E u v i→ (Q i).Nodup∧ (Q i).IsChain G.Adj∧
      (Q i).head?=some u∧ (Q i).getLast?=some v):
    ∃ D:Distribution G (n * (n * q)), ∀ z,
      Lax263307.PathSampling.load D.toSampling z≤ γ / (n:ℝ) ^ 2 *
        (∑ i,w i * (if z∈ Q i then (1:ℝ) else 0)):=by
  classical
  have positive (u v:Fin n):0 < routed w E u v:=
    lt_of_lt_of_le (by positivity) (lower u v)
  obtain ⟨hp,hpair,htotal⟩:=Lax263307Proofs.RoutingNormalization.normalization_correct w E hn w_nonnegative positive
  have unique:IsUniquePair E:=by
    intro i u v u' v' h h'
    have hends:=routes u v i h
    have hends':=routes u' v' i h'
    exact ⟨Option.some.inj (hends.2.2.1.symm.trans hends'.2.2.1),
      Option.some.inj (hends.2.2.2.symm.trans hends'.2.2.2)⟩
  let p:Fin n × (Fin n × Fin q)→ ℝ:=fun a => probability w E a.1 a.2.1 a.2.2
  have hvalid (u v:Fin n) (i:Fin q) (h:0 < probability w E u v i):E u v i:=by
    by_contra hE
    simp [probability,hE] at h
  have huniform (s t:Fin n):
      (∑ u, ∑ v, ∑ i,if (Q i).head?=some s∧ (Q i).getLast?=some t then
        probability w E u v i else 0)=1 / (n:ℝ) ^ 2:=by
    have hterm (u v:Fin n) (i:Fin q):
        (if (Q i).head?=some s∧ (Q i).getLast?=some t then probability w E u v i else 0) =
        (if u=s∧ v=t then probability w E u v i else 0):=by
      by_cases hE:E u v i
      · obtain ⟨_,_,hstart,hfinish⟩:=routes u v i hE
        simp only [hstart,hfinish,Option.some.injEq]
      · simp [probability,hE]
    simp_rw [hterm,ite_and]
    simpa using hpair s t
  let D:Distribution G (n * (n * q)):= {
    probability:=fun j => p (tripleEquiv n q j)
    nonnegative:=fun j => hp _ _ _
    normalized:=by
      rw [sum_triples]
      exact htotal
    route:=fun j => Q (tripleEquiv n q j).2.2
    valid:=by
      intro j hj
      have he:=hvalid _ _ _ hj
      have h:=routes _ _ _ he
      refine ⟨h.1,h.2.1, ?_⟩
      intro hnil
      have hstart:=h.2.2.1
      simp [hnil] at hstart
    uniform:=by
      intro s t
      rw [sum_triples (fun a => if (Q a.2.2).head?=some s∧
        (Q a.2.2).getLast?=some t then p a else 0)]
      exact huniform s t }
  refine ⟨D, ?_⟩
  intro z
  have hload:Lax263307.PathSampling.load D.toSampling z =
      ∑ u, ∑ v, ∑ i,probability w E u v i * (if z∈ Q i then (1:ℝ) else 0):=by
    unfold Lax263307.PathSampling.load Distribution.toSampling
    change (∑ j,if z∈ (Q (tripleEquiv n q j).2.2).toFinset then
      p (tripleEquiv n q j) else 0)=_
    rw [sum_triples (fun a => if z∈ (Q a.2.2).toFinset then p a else 0)]
    simp only [List.mem_toFinset]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p]
    split_ifs <;> simp
  rw [hload]
  apply Lax263307Proofs.RoutingNormalization.normalized_load_bound w E hn w_nonnegative unique γ γ_positive lower
  intro i
  split_ifs <;> norm_num

open scoped NNReal NNRat
open Lax263307.VertexSplitting Lax263307.SplitPathProjection
open Lax455465.ConcurrentFlow Lax455465.ProductNetwork

theorem split_path_distribution {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn:0 < n) (x:Fin n→ ℚ≥0) (large:ℚ≥0) (γ:ℝ) (γ_positive:0 < γ)
    (f:ℝ≥0) (high:1 / γ≤ (f:ℝ)) (F:PathFlow (2 * n))
    (feasible:IsConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F):
    ∃ q, ∃ D:Distribution G q, ∀ z,
      Lax263307.PathSampling.load D.toSampling z≤ γ * (x z:ℝ) / (n:ℝ) ^ 2:=by
  classical
  let ι:= ↥F.support
  let q:=Fintype.card ι
  let e:ι ≃ Fin q:=Fintype.equivFin ι
  let P:Fin q→ List (Fin (2 * n)):=fun i => (e.symm i).val
  let w:Fin q→ ℝ:=fun i => (F (P i):ℝ)
  let E:Fin n→ Fin n→ Fin q→ Prop:=fun u v i =>
    (P i).head?=some (minus u)∧ (P i).getLast?=some (plus v)
  have member (i:Fin q):P i∈ F.support:=(e.symm i).property
  have sum_paths (a:List (Fin (2 * n))→ ℝ):
      (∑ i,a (P i))=∑ R∈ F.support,a R:=by
    change (∑ i, (fun j:ι => a j.val) (e.symm i))=_
    exact (e.symm.sum_comp (fun j:ι => a j.val)).trans (Finset.sum_coe_sort F.support a)
  have lower (u v:Fin n):1 / γ≤ Lax263307.RoutingNormalization.routed w E u v:=by
    have hdemand:=feasible.2.2 (minus u) (plus v)
      (Lax263307Proofs.SplitPathProjection.minus_ne_plus u v)
    have hdemand':f≤ Lax455465.ConcurrentFlow.routed F (minus u) (plus v):=by
      simpa [pairDemand,splitInstance,Lax455465.RationalEncoding.RationalInstance.weights] using hdemand
    have hrouted:Lax263307.RoutingNormalization.routed w E u v =
        (Lax455465.ConcurrentFlow.routed F (minus u) (plus v):ℝ):=by
      unfold Lax263307.RoutingNormalization.routed Lax455465.ConcurrentFlow.routed
      push_cast
      simp only [apply_ite (fun a:ℝ≥0 => (a:ℝ)),NNReal.coe_zero]
      rw [← sum_paths (fun R => if R.head?=some (minus u)∧ R.getLast?=some (plus v)
        then (F R:ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [E,w]
    rw [hrouted]
    exact high.trans (by exact_mod_cast hdemand')
  have projections (i:Fin q) (h:∃ u v,E u v i):
      ∃ Q:List (Fin n),P i=expandRoute Q∧ Q.Nodup∧ Q.IsChain G.Adj∧
        (∃ u v,E u v i∧ Q.head?=some u∧ Q.getLast?=some v):=by
    obtain ⟨u,v,hs,ht⟩:=h
    obtain ⟨Q,hP,hsimple,hchain,hhead,hlast⟩:=
      Lax263307Proofs.SplitPathProjection.split_support_projection G x large f F feasible (P i)
        (member i) u v hs ht
    exact ⟨Q,hP,hsimple,hchain,u,v, ⟨hs,ht⟩,hhead,hlast⟩
  let Q:Fin q→ List (Fin n):=fun i =>
    if h:∃ u v,E u v i then Classical.choose (projections i h) else []
  have route_spec (i:Fin q) (h:∃ u v,E u v i):
      P i=expandRoute (Q i)∧ (Q i).Nodup∧ (Q i).IsChain G.Adj∧
        (∃ u v,E u v i∧ (Q i).head?=some u∧ (Q i).getLast?=some v):=by
    dsimp only [Q]
    rw [dif_pos h]
    exact Classical.choose_spec (projections i h)
  have routes (u v:Fin n) (i:Fin q) (h:E u v i):
      (Q i).Nodup∧ (Q i).IsChain G.Adj∧
        (Q i).head?=some u∧ (Q i).getLast?=some v:=by
    obtain ⟨hP,hsimple,hchain,s,t,hE,hs,ht⟩:=route_spec i ⟨u,v,h⟩
    have hu:s=u:=Lax263307Proofs.SplitPathProjection.minus_injective n
      (Option.some.inj (hE.1.symm.trans h.1))
    have hv:t=v:=Lax263307Proofs.SplitPathProjection.plus_injective n
      (Option.some.inj (hE.2.symm.trans h.2))
    exact ⟨hsimple,hchain,hu ▸ hs,hv ▸ ht⟩
  obtain ⟨D,hD⟩:=Lax263307Proofs.RouteDistributions.finite_routes G hn w E (fun i => NNReal.coe_nonneg _) γ γ_positive lower Q routes
  refine ⟨_,D, ?_⟩
  intro z
  have hterm (i:Fin q):
      w i * (if z∈ Q i then (1:ℝ) else 0)≤
        (F (P i):ℝ) * (((P i).zip (P i).tail).count (minus z,plus z):ℝ):=by
    by_cases h:∃ u v,E u v i
    · obtain ⟨hP,hsimple,_⟩:=route_spec i h
      rw [hP,Lax263307Proofs.SplitPathProjection.capacity_arc_count (Q i) hsimple z]
      dsimp [w]
      rw [hP]
      split_ifs <;> simp
    · have hQ:Q i=[]:=by simp [Q,h]
      simp only [hQ,List.not_mem_nil,if_false,mul_zero]
      positivity
  have hsum:(∑ i,w i * (if z∈ Q i then (1:ℝ) else 0))≤
      (arcLoad F (minus z) (plus z):ℝ):=by
    calc
      _≤ ∑ i, (F (P i):ℝ) * (((P i).zip (P i).tail).count (minus z,plus z):ℝ):=
        Finset.sum_le_sum fun i _ => hterm i
      _=(arcLoad F (minus z) (plus z):ℝ):=by
        rw [sum_paths (fun R => (F R:ℝ) * ((R.zip R.tail).count (minus z,plus z):ℝ))]
        simp [arcLoad]
  have hcapacity:(arcLoad F (minus z) (plus z):ℝ)≤ (x z:ℝ):=by
    have h:=feasible.2.1 (minus z) (plus z)
    change arcLoad F (minus z) (plus z)≤ ((splitInstance G x large).capacity (minus z) (plus z):ℝ≥0) at h
    rw [Lax263307Proofs.VertexSplitting.capacity_minus] at h
    simp only at h
    exact_mod_cast h
  calc
    _≤ γ / (n:ℝ) ^ 2 * (∑ i,w i * (if z∈ Q i then (1:ℝ) else 0)):=hD z
    _≤ γ / (n:ℝ) ^ 2 * (x z:ℝ):=
      mul_le_mul_of_nonneg_left (hsum.trans hcapacity) (by positivity)
    _=_:=by ring

theorem split_arc_distribution {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn:0 < n) (x:Fin n→ ℚ≥0) (large:ℚ≥0) (γ:ℝ) (γ_positive:0 < γ)
    (f:ℝ≥0) (high:1 / γ≤ (f:ℝ)) (F:ArcFlow (2 * n))
    (feasible:IsArcConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F):
    ∃ q, ∃ D:Distribution G q, ∀ z,
      Lax263307.PathSampling.load D.toSampling z≤ γ * (x z:ℝ) / (n:ℝ) ^ 2:=by
  obtain ⟨P,hP,_⟩:=Lax455465Proofs.ArcToPath.exists_path_flow .directed
    (splitInstance G x large).network (splitInstance G x large).weights f F feasible
  exact split_path_distribution G hn x large γ γ_positive f high P hP

end Lax263307Proofs.RouteDistributions

end

section

namespace Lax263307Proofs.ForcedSeparation

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

theorem certificate_separation (C:GraphClass) (hereditary:IsHereditary C)
    (a A:ℕ) (a_positive:0 < a) (A_positive:0 < A) (class_bound:HasPowerBagBound C a A):
    ∃ K:ℕ,0 < K∧ ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ 0 < n→ ∀ (x:Fin n→ ℚ≥0) (large:ℚ≥0)
      (certificate:Lax455465.FlowCutCertificate.Certificate (2 * n)) (ρ γ k p:ℝ) (ℓ:ℕ),
      0 < ℓ→ 0≤ ρ→ 0 < γ→ 0 < k→ 0 < p→
      γ * k≤ (ℓ:ℝ) * (n:ℝ) ^ 2→ (∀ v, (x v:ℝ)≤ 1)→
      (∑ v, (x v:ℝ))≤ k→
      Lax263307.Entropy.edgeCost G (fun v => (x v:ℝ))≤ k ^ 2 / p→
      (K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ k→
      (2 * K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ p→
      AdmissibleCut (splitInstance G x large).weights certificate.cut→
      IsArcConcurrentFlow .directed (splitInstance G x large).network
        (splitInstance G x large).weights (certificate.flow.value:ℝ≥0) certificate.flow.flow→
      (ratioCost (splitInstance G x large).network (splitInstance G x large).weights certificate.cut:ℝ)≤
        ρ * (certificate.flow.value:ℝ)→
      ρ * (2 * n:ℕ) ^ 2 / γ < (large:ℝ)→
      (leftShore certificate.cut).Nonempty∧ (rightShore certificate.cut).Nonempty∧
      leftShore certificate.cut ∪ rightShore certificate.cut=Finset.univ∧
      (∀ u∈ leftShore certificate.cut \ rightShore certificate.cut,
        ∀ v∈ rightShore certificate.cut \ leftShore certificate.cut, ¬G.Adj u v)∧
      (∑ v∈ leftShore certificate.cut ∩ rightShore certificate.cut, (x v:ℝ))≤
        4 * ρ * (leftShore certificate.cut).card * (rightShore certificate.cut).card / γ:=by
  classical
  obtain ⟨K,hK,impossible⟩:=Lax263307Proofs.NoBoundedLoadRoutes.no_bounded_load_routes
    C hereditary a A a_positive A_positive class_bound
  refine ⟨K,hK, ?_⟩
  intro n G _ hG hn x large certificate ρ γ k p ℓ hℓ hρ hγ hk hp hscale hcost hmass hedge
    htarget hsparse hadmissible hflow hratio hlarge
  rcases Lax263307Proofs.VertexSplitting.flow_or_separation G x large certificate ρ γ hρ hγ
    hadmissible hflow hratio hlarge with ⟨hhigh,hvalid⟩ | hseparation
  · obtain ⟨q,D,hD⟩:=Lax263307Proofs.RouteDistributions.split_arc_distribution G hn x large γ hγ
      (certificate.flow.value:ℝ≥0) hhigh certificate.flow.flow hvalid
    have hden:(0:ℝ) < (n:ℝ) ^ 2:=by positivity
    have hfactor:γ / (n:ℝ) ^ 2≤ (ℓ:ℝ) / k:=(div_le_div_iff₀ hden hk).mpr hscale
    have hload (v:Fin n):Lax263307.PathSampling.load D.toSampling v≤ (ℓ:ℝ) * (x v:ℝ) / k:=by
      calc
        _≤ γ * (x v:ℝ) / (n:ℝ) ^ 2:=hD v
        _=γ / (n:ℝ) ^ 2 * (x v:ℝ):=by ring
        _≤ (ℓ:ℝ) / k * (x v:ℝ):=mul_le_mul_of_nonneg_right hfactor (by positivity)
        _=_:=by ring
    exact (impossible n q G hG D hn ℓ hℓ (fun v => (x v:ℝ)) k p hk hp
      (fun v => ⟨by positivity,hcost v⟩) hmass hload hedge htarget hsparse).elim
  · exact hseparation

end Lax263307Proofs.ForcedSeparation

end

section

namespace Lax263307Proofs.LightSeparators

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax263307.RepeatedCutAccounting Lax263307.Entropy
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

theorem logFactor_nonnegative (n:ℕ):0≤ logFactor n:=by
  unfold logFactor
  apply div_nonneg _ (Real.log_pos (by norm_num)).le
  by_cases hn:n=0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast (show 1≤ n by omega))

theorem logFactor_upper (n:ℕ):logFactor n≤ (Nat.log2 n:ℝ) + 1:=by
  by_cases hn:n=0
  · simp [hn,logFactor]
  · have hp:=(Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    rw [← Nat.log2_eq_log_two] at hp
    have hpr:(n:ℝ)≤ (2:ℝ) ^ (Nat.log2 n + 1):=by exact_mod_cast hp
    have h:=Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hpr
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one] at h
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr h

theorem logFactor_mono {m n:ℕ} (positive:0 < m) (bound:m≤ n):logFactor m≤ logFactor n:=
  div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast positive) (by exact_mod_cast bound))
    (Real.log_pos (by norm_num)).le

theorem bounded_ratio (C:ℝ) (positive:0 < C):
    ∃ B:ℕ,0 < B∧ ∀ n r:ℕ,0 < r→ r≤ n→
      C * logFactor (2 * r)≤ (B:ℝ) * ((Nat.log2 (2 * n):ℝ) + 1):=by
  let B:=Nat.ceil C
  have hB:0 < B:=Nat.ceil_pos.mpr positive
  refine ⟨B,hB, ?_⟩
  intro n r hr hrn
  have hlog:=(logFactor_mono (by omega:0 < 2 * r) (Nat.mul_le_mul_left 2 hrn)).trans
    (logFactor_upper (2 * n))
  exact mul_le_mul (Nat.le_ceil C) hlog (logFactor_nonnegative _) (Nat.cast_nonneg B)

theorem sum_embedding {m n:ℕ} (f:Fin m ↪ Fin n) (x:Fin n→ ℝ)
    (nonnegative:∀ v,0≤ x v):(∑ v,x (f v))≤ ∑ v,x v:=by
  classical
  calc
    _=∑ v∈ Finset.univ.image f,x v:=(Finset.sum_image (fun _ _ _ _ h => f.injective h)).symm
    _≤ _:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => nonnegative v)

theorem edge_cost_embedding {m n:ℕ} (H:SimpleGraph (Fin m)) (G:SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel G.Adj] (f:H ↪g G)
    (x:Fin n→ ℝ) (nonnegative:∀ v,0≤ x v):
    edgeCost H (x ∘ f)≤ edgeCost G x:=by
  classical
  unfold edgeCost adjacencyMass
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hnonneg (u v:Fin n):0≤ (if G.Adj u v then x u * x v else 0):=by
    split_ifs
    · exact mul_nonneg (nonnegative u) (nonnegative v)
    · exact le_refl _
  calc
    (∑ u:Fin m, ∑ v:Fin m,if H.Adj u v then (x ∘ f) u * (x ∘ f) v else 0) =
        ∑ u:Fin m, ∑ v:Fin m,if G.Adj (f u) (f v) then x (f u) * x (f v) else 0:=by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      simp only [Function.comp_apply,f.map_adj_iff]
    _≤ ∑ u:Fin m, ∑ v:Fin n,if G.Adj (f u) v then x (f u) * x v else 0:=
      Finset.sum_le_sum (fun u _ => sum_embedding f.toEmbedding _ (hnonneg (f u)))
    _≤ _:=sum_embedding f.toEmbedding _ (fun u => Finset.sum_nonneg (fun v _ => hnonneg u v))

theorem small_piece {n:ℕ} (A B:Finset (Fin n)) (cover:A ∪ B=Finset.univ)
    (smaller:B.card≤ A.card):2 * (B \ A).card≤ n:=by
  have h:=Finset.card_union_add_card_inter A B
  rw [cover,Finset.card_univ,Fintype.card_fin] at h
  have hpart:=Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hpart
  omega

theorem remainder_scale (n r ℓ:ℕ) (hn:0 < n) (hℓ:0 < ℓ)
    (k:ℝ) (hk:0 < k) (large:2 * n < 3 * r):
    0 < (ℓ:ℝ) * (n:ℝ) ^ 2 / (3 * k)∧
      ((ℓ:ℝ) * (n:ℝ) ^ 2 / (3 * k)) * k≤ (ℓ:ℝ) * (r:ℝ) ^ 2:=by
  have hn':(0:ℝ) < n:=by exact_mod_cast hn
  have hℓ':(0:ℝ) < ℓ:=by exact_mod_cast hℓ
  have hr':(0:ℝ)≤ r:=Nat.cast_nonneg _
  have hlarge:2 * (n:ℝ) < 3 * (r:ℝ):=by exact_mod_cast large
  have hs:(n:ℝ) ^ 2≤ 3 * (r:ℝ) ^ 2:=by
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hlarge)) (show 0≤ 3 * (r:ℝ) + 2 * n by positivity)]
  refine ⟨by positivity, ?_⟩
  have heq:((ℓ:ℝ) * (n:ℝ) ^ 2 / (3 * k)) * k=(ℓ:ℝ) * (n:ℝ) ^ 2 / 3:=by
    field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hs hℓ'.le]

end Lax263307Proofs.LightSeparators

end

section

namespace Lax263307Proofs.ComputedSeparators

open scoped NNReal NNRat
open Lax263307.ComputedSeparators Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.VertexSplitting Lax263307.Entropy Lax263307.RepeatedCutAccounting
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax263307Proofs.LightSeparators

theorem decode_cut_certificate {n:ℕ} (c:Lax455465.FlowCutCertificate.Certificate n):
    decodeCut n (Lax455465.FlowCutCertificate.encodeCertificate c)=c.cut:=by
  ext v
  unfold decodeCut
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  change (encodeCut c.cut ++ encodeArcs c.flow).getD v.val 0=1↔ v∈ c.cut
  have hv:v.val < (encodeCut c.cut).length:=by simp [encodeCut]
  rw [List.getD_append _ _ 0 v.val hv,List.getD_eq_getElem _ 0 hv]
  simp [encodeCut]

def embedding {n:ℕ} (G:SimpleGraph (Fin n)) (R:Finset (Fin n)):restriction G R ↪g G where
  toFun:=label R
  inj':=(label R).injective
  map_rel_iff':=Iff.rfl

theorem oriented {n:ℕ} (G:SimpleGraph (Fin n)) (x:Fin n→ ℝ) (ρ γ:ℝ)
    (A B:Finset (Fin n)) (ha:A.Nonempty) (hb:B.Nonempty)
    (cover:A ∪ B=Finset.univ)
    (separated:∀ u∈ A \ B, ∀ v∈ B \ A, ¬G.Adj u v)
    (bound:cost x (A ∩ B)≤ 4 * ρ * A.card * B.card / γ):
    let s:=Lax263307.ComputedSeparators.orient A B
    s.1 ∪ s.2=Finset.univ∧ s.2.Nonempty∧ 2 * (s.2 \ s.1).card≤ n∧
      (∀ u∈ s.1 \ s.2, ∀ v∈ s.2 \ s.1, ¬G.Adj u v)∧
      cost x (s.1 ∩ s.2)≤ 4 * ρ * s.1.card * s.2.card / γ:=by
  dsimp only [Lax263307.ComputedSeparators.orient]
  split_ifs with h
  · exact ⟨cover,hb,small_piece A B cover h,separated,bound⟩
  · refine ⟨by rw [Finset.union_comm]; exact cover,ha,
      small_piece B A (by rw [Finset.union_comm]; exact cover) (by omega), ?_, ?_⟩
    · intro u hu v hv hadj
      exact separated v hv u hu hadj.symm
    · rw [Finset.inter_comm]
      convert bound using 1
      ring

theorem lifted {r n:ℕ} (H:SimpleGraph (Fin r)) (G:SimpleGraph (Fin n))
    (f:H ↪g G) (R:Finset (Fin n)) (onto:Finset.univ.image f=R)
    (x:Fin n→ ℝ) (ρ γ:ℝ) (A B:Finset (Fin r))
    (cover:A ∪ B=Finset.univ) (nonempty:B.Nonempty)
    (small:2 * (B \ A).card≤ r)
    (separated:∀ u∈ A \ B, ∀ v∈ B \ A, ¬H.Adj u v)
    (bound:cost (x ∘ f) (A ∩ B)≤ 4 * ρ * A.card * B.card / γ):
    A.image f ∪ B.image f=R∧ (B.image f).Nonempty∧
      2 * (B.image f \ A.image f).card≤ R.card∧
      (∀ u∈ A.image f \ B.image f, ∀ v∈ B.image f \ A.image f, ¬G.Adj u v)∧
      cost x (A.image f ∩ B.image f)≤ 4 * ρ * (A.image f).card * (B.image f).card / γ:=by
  have hcard (S:Finset (Fin r)):(S.image f).card=S.card:=
    Finset.card_image_of_injective _ f.injective
  have hR:R.card=r:=by rw [← onto,hcard,Finset.card_univ,Fintype.card_fin]
  refine ⟨?_,nonempty.image f, ?_, ?_, ?_⟩
  · rw [← Finset.image_union,cover,onto]
  · rw [← Finset.image_sdiff B A f.injective,hcard,hR]
    exact small
  · intro u hu v hv hadj
    rw [← Finset.image_sdiff A B f.injective] at hu
    rw [← Finset.image_sdiff B A f.injective] at hv
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hv
    exact separated a ha b hb (f.map_adj_iff.mp hadj)
  · rw [← Finset.image_inter A B f.injective,hcard,hcard]
    unfold cost
    rw [Finset.sum_image (fun _ _ _ _ h => f.injective h)]
    exact bound

theorem exists_solver (C:GraphClass) (hereditary:IsHereditary C)
    (a A:ℕ) (ha:0 < a) (hA:0 < A) (class_bound:HasPowerBagBound C a A):
    ∃ (solve:List ℕ→ List ℕ) (K B:ℕ),Lax759944.RamPolytime.RamPolytime solve∧
      0 < K∧ 0 < B∧ ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ 0 < n→ ∀ (x:Fin n→ ℚ≥0) (k p ℓ:ℕ),
      0 < k→ 0 < p→ 0 < ℓ→
      (∀ v, (x v:ℝ)≤ 1)→ (∑ v, (x v:ℝ))≤ k→
      edgeCost G (fun v => (x v:ℝ))≤ (k:ℝ) ^ 2 / p→
      (K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ k→
      (2 * K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ p→
      ∀ R:Finset (Fin n),2 * n < 3 * R.card→
        let s:=step solve G x B ℓ k R
        s.1 ∪ s.2=R∧ s.2.Nonempty∧ 2 * (s.2 \ s.1).card≤ R.card∧
          (∀ u∈ s.1 \ s.2, ∀ v∈ s.2 \ s.1, ¬G.Adj u v)∧
          cost (fun v => (x v:ℝ)) (s.1 ∩ s.2)≤
            4 * (ratio B n:ℝ) * s.1.card * s.2.card / (scale n ℓ k:ℝ):=by
  obtain ⟨K,hK,hforced⟩:=Lax263307Proofs.ForcedSeparation.certificate_separation C hereditary a A ha hA class_bound
  obtain ⟨solve,c,hpoly,hc,hsolve⟩:=Lax263307Proofs.VertexSplitting.split_certificate
  obtain ⟨B,hB,hratio⟩:=bounded_ratio c hc
  refine ⟨solve,K,B,hpoly,hK,hB, ?_⟩
  intro n G _ hG hn x k p ℓ hk hp hℓ hx hmass hedge htarget hsparsity R hlargeR
  let r:=R.card
  let H:=restriction G R
  let f:H ↪g G:=embedding G R
  let y:Fin r→ ℚ≥0:=fun v => x (f v)
  let ρ:ℝ:=(ratio B n:ℝ)
  let γ:ℝ:=(scale n ℓ k:ℝ)
  let large:=largeCapacity B n r ℓ k
  have hrpos:0 < r:=by dsimp [r]; omega
  have hrn:r≤ n:=R.card_le_univ.trans_eq (Fintype.card_fin n)
  have hρeq:ρ=(B:ℝ) * ((Nat.log2 (2 * n):ℝ) + 1):=by dsimp [ρ,ratio]; push_cast; rfl
  have hγeq:γ=(ℓ:ℝ) * (n:ℝ) ^ 2 / (3 * k):=by dsimp [γ,scale]; push_cast; rfl
  have hρ:0≤ ρ:=by rw [hρeq]; positivity
  have hγ:0 < γ:=by
    rw [hγeq]
    exact (remainder_scale n n ℓ hn hℓ k (by exact_mod_cast hk) (by omega)).1
  have hcap:ρ * (2 * r:ℕ) ^ 2 / γ < (large:ℝ):=by
    have h:=Nat.le_ceil (ratio B n * (2 * r:ℕ) ^ 2 / scale n ℓ k)
    have hq:ratio B n * (2 * r:ℕ) ^ 2 / scale n ℓ k < (large:ℚ):=by
      change ratio B n * (2 * r:ℕ) ^ 2 / scale n ℓ k <
        ((Nat.ceil (ratio B n * (2 * r:ℕ) ^ 2 / scale n ℓ k) + 1:ℕ):ℚ)
      rw [Nat.cast_add,Nat.cast_one]
      linarith
    dsimp only [ρ,γ]
    exact_mod_cast hq
  obtain ⟨cert,hencoded,hadmissible,hflow,hcut⟩:=hsolve r H y large hrpos
  have hcut':(ratioCost (splitInstance H y large).network
      (splitInstance H y large).weights cert.cut:ℝ)≤ ρ * (cert.flow.value:ℝ):=by
    apply hcut.trans (mul_le_mul_of_nonneg_right _ (by positivity))
    rw [hρeq]
    exact hratio n r hrpos hrn
  have hxnonnegative (v:Fin n):0≤ (x v:ℝ):=by positivity
  have hscale:γ * k≤ (ℓ:ℝ) * (r:ℝ) ^ 2:=by
    rw [hγeq]
    exact (remainder_scale n r ℓ hn hℓ k (by exact_mod_cast hk) hlargeR).2
  have hmass':(∑ v:Fin r, (y v:ℝ))≤ k:=
    (sum_embedding f.toEmbedding (fun v => (x v:ℝ)) hxnonnegative).trans hmass
  have hedge':edgeCost H (fun v => (y v:ℝ))≤ (k:ℝ) ^ 2 / p:=
    (edge_cost_embedding H G f (fun v => (x v:ℝ)) hxnonnegative).trans hedge
  obtain ⟨hleft,hright,hcover,hsep,hcost⟩:=
    hforced r H (hereditary r n H G hG ⟨f⟩) hrpos y large cert ρ γ k p ℓ hℓ hρ hγ
      (by exact_mod_cast hk) (by exact_mod_cast hp) hscale (fun v => hx (f v)) hmass' hedge'
      htarget hsparsity hadmissible hflow hcut' hcap
  have hs:=oriented H (fun v => (y v:ℝ)) ρ γ (leftShore cert.cut) (rightShore cert.cut)
    hleft hright hcover hsep hcost
  have honto:Finset.univ.image f=R:=Finset.image_orderEmbOfFin_univ R rfl
  have hlift:=lifted H G f R honto (fun v => (x v:ℝ)) ρ γ _ _
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have hdecode:decodeCut (2 * R.card) (solve (encodeInput .directed
      (splitInstance (restriction G R) (fun v => x (label R v))
        (largeCapacity B n R.card ℓ k))))=cert.cut:=by
    change decodeCut (2 * r) (solve (encodeInput .directed (splitInstance H y large)))=cert.cut
    rw [hencoded,decode_cut_certificate]
  simp only [step,hdecode]
  exact hlift

theorem cuts_trace {n:ℕ} (G:SimpleGraph (Fin n)) (x:Fin n→ ℝ) (ρ γ:ℝ)
    (cut:Finset (Fin n)→ Finset (Fin n) × Finset (Fin n))
    (correct:∀ R:Finset (Fin n),2 * n < 3 * R.card→
      let s:=cut R
      s.1 ∪ s.2=R∧ s.2.Nonempty∧ 2 * (s.2 \ s.1).card≤ R.card∧
        (∀ u∈ s.1 \ s.2, ∀ v∈ s.2 \ s.1, ¬G.Adj u v)∧
        cost x (s.1 ∩ s.2)≤ 4 * ρ * s.1.card * s.2.card / γ)
    (fuel:ℕ) (start:Finset (Fin n)) (budget:start.card≤ fuel):
    ∃ T:Lax263307.CutTraces.Trace G start (cuts cut fuel start).length,
      3 * (T.remaining (cuts cut fuel start).length).card≤ 2 * n∧
      (∀ i:Fin (cuts cut fuel start).length,
        (T.left i,T.right i)=(cuts cut fuel start).get i)∧
      ∀ i < (cuts cut fuel start).length,
        cost x (T.left i ∩ T.right i)≤ 4 * ρ * (T.left i).card * (T.right i).card / γ:=by
  induction fuel generalizing start with
  | zero =>
    refine ⟨Lax263307Proofs.CutTraces.emptyTrace G start, ?_, ?_, ?_⟩
    · change 3 * start.card≤ 2 * n
      omega
    · intro i
      exact Fin.elim0 i
    · intro i hi
      simp [cuts] at hi
  | succ fuel ih =>
    by_cases hstop:3 * start.card≤ 2 * n
    · have hcs:cuts cut (fuel + 1) start=[]:=by rw [cuts,if_pos hstop]
      rw [hcs]
      refine ⟨Lax263307Proofs.CutTraces.emptyTrace G start,hstop, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i hi
        simp at hi
    · have hs:=correct start (lt_of_not_ge hstop)
      let s:=cut start
      have hBsub:s.2 ⊆ start:=by rw [← hs.1]; exact Finset.subset_union_right
      have hnext:s.1 \ s.2=start \ s.2:=by
        rw [← hs.1]
        ext v
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
      have hcount:=Finset.card_sdiff_add_card_eq_card hBsub
      have hpositive:0 < s.2.card:=Finset.card_pos.mpr hs.2.1
      have hbudget:(s.1 \ s.2).card≤ fuel:=by rw [hnext]; omega
      obtain ⟨T,hfinished,hmatches,hcosts⟩:=ih (s.1 \ s.2) hbudget
      have hcs:cuts cut (fuel + 1) start=s::cuts cut fuel (s.1 \ s.2):=by
        rw [cuts,if_neg hstop]
      rw [hcs]
      refine ⟨Lax263307Proofs.CutTraces.prepend s.1 s.2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 T,
        hfinished, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact hmatches j
      · intro i hi
        cases i with
        | zero => exact hs.2.2.2.2
        | succ i => exact hcosts i (by simpa using hi)

theorem mem_separator {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (v:Fin n):
    v∈ Lax263307.ComputedSeparators.separator cs↔ ∃ s∈ cs,v∈ s.1 ∩ s.2:=by
  induction cs with
  | nil => simp [Lax263307.ComputedSeparators.separator]
  | cons s cs ih =>
    simp only [Lax263307.ComputedSeparators.separator,List.foldr_cons,Finset.mem_union]
    change v∈ s.1 ∩ s.2∨ v∈ Lax263307.ComputedSeparators.separator cs↔ _
    rw [ih]
    simp only [List.mem_cons,exists_eq_or_imp]

theorem separator_eq {n q:ℕ} (G:SimpleGraph (Fin n)) (start:Finset (Fin n))
    (cs:List (Finset (Fin n) × Finset (Fin n))) (hsize:cs.length=q)
    (T:Lax263307.CutTraces.Trace G start q)
    (agrees:∀ i:Fin cs.length, (T.left i,T.right i)=cs.get i):
    Lax263307.ComputedSeparators.separator cs=Lax263307.CutTraces.separator T:=by
  ext v
  rw [mem_separator]
  simp only [Lax263307.CutTraces.separator,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨s,hs,hv⟩
    obtain ⟨i,hi⟩:=List.mem_iff_get.mp hs
    have hm:=(agrees i).trans hi
    refine ⟨⟨i.val,by rw [← hsize]; exact i.isLt⟩, ?_⟩
    change v∈ T.left i.val ∩ T.right i.val
    have hl:T.left i.val=s.1:=congrArg Prod.fst hm
    have hr:T.right i.val=s.2:=congrArg Prod.snd hm
    rw [hl,hr]
    exact hv
  · rintro ⟨i,hv⟩
    let j:Fin cs.length:= ⟨i.val,by rw [hsize]; exact i.isLt⟩
    refine ⟨cs.get j,List.get_mem cs j, ?_⟩
    rw [← agrees j]
    exact hv

theorem remaining_eq {n:ℕ} (G:SimpleGraph (Fin n)) (start:Finset (Fin n))
    (cs:List (Finset (Fin n) × Finset (Fin n)))
    (T:Lax263307.CutTraces.Trace G start cs.length)
    (agrees:∀ i:Fin cs.length, (T.left i,T.right i)=cs.get i):
    remaining start cs=T.remaining cs.length:=by
  unfold remaining
  split_ifs with h
  · exact ((congrArg T.remaining h).trans T.initial).symm
  · let i:Fin cs.length:= ⟨cs.length - 1,by omega⟩
    change (cs.get i).1 \ (cs.get i).2=T.remaining cs.length
    rw [← agrees i]
    have hi:i.val + 1=cs.length:=by dsimp [i]; omega
    exact (T.next i i.isLt).symm.trans (congrArg T.remaining hi)

theorem pieces_eq {n:ℕ} (G:SimpleGraph (Fin n))
    (cs:List (Finset (Fin n) × Finset (Fin n)))
    (T:Lax263307.CutTraces.Trace G Finset.univ cs.length)
    (agrees:∀ i:Fin cs.length, (T.left i,T.right i)=cs.get i) (i:Option (Fin cs.length)):
    pieces cs i=Lax263307.CutTraces.parts T i:=by
  cases i with
  | none => exact remaining_eq G Finset.univ cs T agrees
  | some i =>
    change (cs.get i).2 \ (cs.get i).1=T.right i \ T.left i
    rw [← agrees i]

theorem light_separator (C:GraphClass) (hereditary:IsHereditary C)
    (a A:ℕ) (ha:0 < a) (hA:0 < A) (class_bound:HasPowerBagBound C a A):
    ∃ (solve:List ℕ→ List ℕ) (K B:ℕ),Lax759944.RamPolytime.RamPolytime solve∧
      0 < K∧ 0 < B∧ ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ 0 < n→ ∀ (x:Fin n→ ℚ≥0) (k p ℓ:ℕ),
      0 < k→ 0 < p→ 0 < ℓ→
      (∀ v, (x v:ℝ)≤ 1)→ (∑ v, (x v:ℝ))≤ k→
      edgeCost G (fun v => (x v:ℝ))≤ (k:ℝ) ^ 2 / p→
      (K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ k→
      (2 * K:ℝ) * ((ℓ:ℝ) + 1) ^ (4 * a + 2)≤ p→
      let cs:=cuts (step solve G x B ℓ k) n Finset.univ
      cs.length≤ n∧
        Lax263307.EdgeSublinearSeparators.IsBalancedSeparator G
          (Lax263307.ComputedSeparators.separator cs)∧
        cost (fun v => (x v:ℝ)) (Lax263307.ComputedSeparators.separator cs)≤
          12 * (ratio B n:ℝ) * k / ℓ∧
        ∃ P:Lax263307.SeparatorComponents.Partition G
            (Lax263307.ComputedSeparators.separator cs) (Option (Fin cs.length)),
          (∀ i,P.vertices i=pieces cs i)∧ ∀ i,3 * (P.vertices i).card≤ 2 * n:=by
  obtain ⟨solve,K,B,hpoly,hK,hB,hstep⟩:=exists_solver C hereditary a A ha hA class_bound
  refine ⟨solve,K,B,hpoly,hK,hB, ?_⟩
  intro n G _ hG hn x k p ℓ hk hp hℓ hx hmass hedge htarget hsparsity
  let cut:=step solve G x B ℓ k
  let cs:=cuts cut n Finset.univ
  have hcorrect:=hstep n G hG hn x k p ℓ hk hp hℓ hx hmass hedge htarget hsparsity
  have hρ:0≤ (ratio B n:ℝ):=by dsimp [ratio]; positivity
  have hγ:0 < (scale n ℓ k:ℝ):=by
    have hpos:(0:ℚ) < scale n ℓ k:=by dsimp [scale]; positivity
    exact_mod_cast hpos
  have hxnonnegative (v:Fin n):0≤ (x v:ℝ):=by positivity
  obtain ⟨T,hfinished,hmatches,hcosts⟩:=cuts_trace G (fun v => (x v:ℝ))
    (ratio B n) (scale n ℓ k) cut hcorrect n Finset.univ (by simp)
  have h:=Lax263307Proofs.CutTraces.trace_correct G T hfinished (fun v => (x v:ℝ))
    hxnonnegative (ratio B n) (scale n ℓ k) hρ hγ hcosts
  have heq:=separator_eq G Finset.univ cs rfl T hmatches
  have hcosteq:4 * (ratio B n:ℝ) * (n:ℝ) ^ 2 / (scale n ℓ k:ℝ) =
      12 * (ratio B n:ℝ) * k / ℓ:=by
    dsimp only [scale]
    push_cast
    have hnR:(n:ℝ) ≠ 0:=by exact_mod_cast (ne_of_gt hn)
    have hkR:(k:ℝ) ≠ 0:=by exact_mod_cast (ne_of_gt hk)
    have hℓR:(ℓ:ℝ) ≠ 0:=by exact_mod_cast (ne_of_gt hℓ)
    field_simp
    ring
  change cs.length≤ n∧ _
  rw [heq]
  refine ⟨h.1,h.2.1,by rw [← hcosteq]; exact h.2.2,
    Lax263307Proofs.CutTraces.partition T, ?_, ?_⟩
  · intro i
    exact (pieces_eq G cs T hmatches i).symm
  · intro i
    cases i with
    | none => exact hfinished
    | some i =>
      have hsmall:=T.small_piece i i.isLt
      have hrem:(T.remaining i).card≤ n:=by simpa using Finset.card_le_univ (T.remaining i)
      change 3 * (T.right i \ T.left i).card≤ 2 * n
      omega

end Lax263307Proofs.ComputedSeparators

end

section

namespace Lax263307Proofs.RecursiveAlgorithm

open Lax263307.RecursiveAlgorithm Lax263307.ComputedSeparators
open Lax263307.GraphClasses Lax263307.AlgorithmParameters

theorem image_subset {n:ℕ} (C:Finset (Fin n)) (I:Finset (Fin C.card)):
    I.image (label C) ⊆ C:=by
  intro v hv
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
  exact C.orderEmbOfFin_mem rfl i

theorem image_independent {n:ℕ} (G:SimpleGraph (Fin n)) (C:Finset (Fin n))
    (I:Finset (Fin C.card)) (hI:(restriction G C).IsIndepSet (I:Set (Fin C.card))):
    G.IsIndepSet (I.image (label C):Set (Fin n)):=by
  intro u hu v hv huv
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hv
  exact hI hi hj (fun hij => huv (congrArg (label C) hij))

theorem restriction_bound {n:ℕ} (G:SimpleGraph (Fin n)) (C:Finset (Fin n)) (t:ℕ)
    (hbound:∀ I:Finset (Fin C.card), (restriction G C).IsIndepSet (I:Set (Fin C.card))→ I.card < t):
    Lax263307.LinearRelaxation.IsIndependenceBound G C (t-1):=by
  intro J hJC hJ
  let I:=Finset.univ.filter (fun i:Fin C.card => label C i∈ J)
  have heq:I.image (label C)=J:=by
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      have hcover:Finset.univ.image (label C)=C:=Finset.image_orderEmbOfFin_univ C rfl
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hcover.symm ▸ hJC hv)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi ▸ hv⟩,hi⟩
  have hI:(restriction G C).IsIndepSet (I:Set (Fin C.card)):=by
    intro i hi j hj hij
    exact hJ (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      ((label C).injective.ne hij)
  have hcard:I.card=J.card:=by
    rw [← heq,Finset.card_image_of_injective _ (label C).injective]
  have hh:=hbound I hI
  rw [hcard] at hh
  omega

theorem attempt_correct (C:GraphClass) (hereditary:IsHereditary C)
    (lp flow:List ℕ→ List ℕ) (a K B D:ℕ) (hD:4≤ D)
    (oracle:∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ 0 < n→ ∀ k h:ℕ,cutoff a K B n D < k→
      ∀ (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n))),
      Lax263307.NearOracle.ChildCorrect G D h child→
      Lax263307.ProjectedOracle.SearchCorrect G k h D
        (Lax263307.ProjectedOracle.search lp flow a K B D G k child))
    (fuel:ℕ) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG:G∈ C n) (hdepth:Lax263307.RecursionDepth.depth n≤ fuel) (k:ℕ):
    Correct G k fuel D (attempt lp flow a K B D fuel G k):=by
  have hDpos:(0:ℝ) < D:=Nat.cast_pos.mpr (by omega)
  have hβ:0≤ 1 - 4*(1/(D:ℝ))∧ 1 - 4*(1/(D:ℝ))≤ 1:=by
    have hd:(4:ℝ)≤ D:=Nat.cast_le.mpr hD
    constructor
    · apply sub_nonneg.mpr
      rw [mul_one_div,div_le_one hDpos]
      exact hd
    · have:(0:ℝ)≤ 4*(1/(D:ℝ)):=by positivity
      linarith
  induction fuel generalizing n k with
  | zero =>
    unfold attempt
    split_ifs with hsmall hlarge
    · have hh:=Lax263307Proofs.ExhaustiveTargets.search_correct G k
      cases he:Lax263307.ExhaustiveTargets.findIndependentSet G k with
      | none => rw [he] at hh; exact hh
      | some I =>
        rw [he] at hh
        exact ⟨hh.1,by simp [hh.2]⟩
    · intro J _
      have hj:J.card≤ n:=by simpa using Finset.card_le_univ J
      omega
    · have hn:1 < n:=by omega
      rw [Lax263307.RecursionDepth.depth,if_neg (by omega)] at hdepth
      omega
  | succ fuel ih =>
    unfold attempt
    split_ifs with hsmall hlarge
    · have hh:=Lax263307Proofs.ExhaustiveTargets.search_correct G k
      cases he:Lax263307.ExhaustiveTargets.findIndependentSet G k with
      | none => rw [he] at hh; exact hh
      | some I =>
        rw [he] at hh
        refine ⟨hh.1, ?_⟩
        have hp:=pow_le_one₀ (n:=fuel+1) hβ.1 hβ.2
        have hm:=mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg k:(0:ℝ)≤ k)
        simpa [hh.2] using hm
    · intro J _
      have hj:J.card≤ n:=by simpa using Finset.card_le_univ J
      omega
    · have hn:1 < n:=by omega
      let child:=fun (S:Finset (Fin n)) t =>
        (attempt lp flow a K B D fuel (restriction G S) t).map (fun I => I.image (label S))
      have hc:Lax263307.NearOracle.ChildCorrect G D fuel child:=by
        intro S hS t
        have hclass:=hereditary S.card n (restriction G S) G hG
          ⟨Lax263307Proofs.ComputedSeparators.embedding G S⟩
        have hdep:=Lax263307Proofs.RecursionDepth.balanced_decrease n S.card hn hS
        have hh:=ih (restriction G S) hclass (by omega) t
        dsimp only [child]
        cases he:attempt lp flow a K B D fuel (restriction G S) t with
        | some I =>
          rw [he] at hh
          change _∧ _∧ _
          refine ⟨image_subset S I,image_independent G S I hh.1, ?_⟩
          rw [Finset.card_image_of_injective _ (label S).injective]
          exact hh.2
        | none =>
          rw [he] at hh
          exact restriction_bound G S t hh
      have hh:=oracle n G hG (by omega) k fuel (by omega) child hc
      change Correct G k (fuel+1) D (Lax263307.ProjectedOracle.search lp flow a K B D G k child)
      cases he:Lax263307.ProjectedOracle.search lp flow a K B D G k child with
      | some I =>
        rw [he] at hh
        exact hh
      | none =>
        rw [he] at hh
        intro J hJ
        have hb:=hh J (Finset.subset_univ J) hJ
        have hk:0 < k:=by omega
        omega

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

theorem independentSet_correct (C:GraphClass) (hereditary:IsHereditary C)
    (lp flow:List ℕ→ List ℕ) (a K B:ℕ)
    (horacle:∀ n (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],G∈ C n→ 0< n→
      ∀ D k h,4≤ D→ cutoff a K B n D< k→
      ∀ child,Lax263307.NearOracle.ChildCorrect G D h child→
        Lax263307.ProjectedOracle.SearchCorrect G k h D
          (Lax263307.ProjectedOracle.search lp flow a K B D G k child))
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG:G∈ C n)
    (ε:ℚ) (hε:0<ε) (hεsmall:ε<1):
    Lax263307.WeightedIndependentSet.IsApproximation G (fun _ => 1) ε
      (independentSet lp flow a K B G ε):=by
  let D:=accuracyDenominator n ε
  let depth:=Lax263307.RecursionDepth.depth n
  have hD:=(accuracy_budget n ε hε).1
  have hcorrect (k:ℕ):=attempt_correct C hereditary lp flow a K B D hD
    (fun n G _ hG hn k h hlarge child hc => horacle n G hG hn D k h hD hlarge child hc)
    depth G hG le_rfl k
  have hsuccess:∀ k,k≤ n→ ∀ I,attempt lp flow a K B D depth G k=some I→
      G.IsIndepSet (I:Set (Fin n))∧ (1-4*(1/(D:ℝ)))^depth * (k:ℝ)≤ I.card:=by
    intro k _ I he
    have hh:=hcorrect k
    rw [he] at hh
    exact hh
  have hfailure:∀ k,0 < k→ k≤ n→ attempt lp flow a K B D depth G k=none→
      ∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card < k:=by
    intro k _ _ he
    have hh:=hcorrect k
    rw [he] at hh
    exact hh
  have hs:=Lax263307Proofs.TargetSearch.search_correct G ((1-4*(1/(D:ℝ)))^depth)
    (attempt lp flow a K B D depth G) hsuccess hfailure
  change _∧ _∧ _∧ _ at hs
  let result:=solve lp flow a K B D G
  have hind:G.IsIndepSet (result.1:Set (Fin n)):=hs.1
  have hu:∀ J:Finset (Fin n),G.IsIndepSet (J:Set (Fin n))→ J.card≤ result.2:=hs.2.1
  have hsize:(1-(4/(D:ℚ)))^depth * (result.2:ℚ)≤ result.1.card:=by
    have hr:(1-4*(1/(D:ℝ)))^depth * (result.2:ℝ)≤ result.1.card:=hs.2.2.2
    apply (Rat.cast_le (K:=ℝ)).mp
    push_cast
    simpa only [mul_one_div] using hr
  apply Lax263307Proofs.RecursionDepth.approximation_transfer G result.1 result.2 depth (4/(D:ℚ)) ε
    hind hu (by positivity) _ hεsmall.le (accuracy_budget n ε hε).2 hsize
  have hDq:(4:ℚ)≤ D:=Nat.cast_le.mpr hD
  have hDpos:(0:ℚ) < D:=Nat.cast_pos.mpr (by omega)
  exact (div_le_one hDpos).mpr hDq

end Lax263307Proofs.RecursiveAlgorithm

end

section

namespace Lax263307Proofs.AlgorithmParameters

open Lax263307.AlgorithmParameters

theorem sparsity_positive {a K B n D:ℕ} (hK:0 < K):0 < sparsity a K B n D:=by
  unfold sparsity targetThreshold
  positivity

theorem budgets {a K B n D k:ℕ} (hK:0 < K) (hB:0 < B)
    (hD:4≤ D) (large:cutoff a K B n D < k):
    0 < load B n D∧ 0 < sparsity a K B n D∧ 0 < level a K B n D∧
      0 < (1 / (D:ℝ))∧ (1 / (D:ℝ))≤ 1 / 4∧
      12 * (B:ℝ) * ((Nat.log2 (2 * n):ℝ) + 1)≤
        (1 / (D:ℝ)) * load B n D∧
      (sparsity a K B n D:ℝ) * ((Nat.log2 n:ℝ) + 1)≤ level a K B n D∧
      (K:ℝ) * ((load B n D:ℝ) + 1) ^ (4 * a + 2)≤ k∧
      (2 * K:ℝ) * ((load B n D:ℝ) + 1) ^ (4 * a + 2)≤ sparsity a K B n D:=by
  have hp:=sparsity_positive (a:=a) (B:=B) (n:=n) (D:=D) hK
  have hD':(0:ℝ) < D:=by exact_mod_cast (show 0 < D by omega)
  have hD4:(4:ℝ)≤ D:=by exact_mod_cast hD
  have ht:targetThreshold a K B n D≤ k:=
    (le_max_left _ _).trans large.le
  refine ⟨?_,hp, ?_,by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · unfold load logarithm
    positivity
  · unfold level
    positivity
  · exact one_div_le_one_div_of_le (by norm_num) hD4
  · have heq:(1 / (D:ℝ)) * load B n D =
        12 * (B:ℝ) * ((Nat.log2 (2 * n):ℝ) + 1):=by
      simp only [load,logarithm,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
      field_simp
    exact heq.ge
  · simp [level,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  · exact_mod_cast ht
  · simp only [sparsity,targetThreshold,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat]
    ring_nf
    exact le_rfl

theorem conditioning_floor (a K B n D:ℕ):
    (momentFloor a K B n D:ℝ) =
      Lax263307.HeavyConditioning.probabilityFloor n (sparsity a K B n D) ^ level a K B n D:=by
  unfold momentFloor
  push_cast
  simp only [floorDenominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Lax263307.HeavyConditioning.probabilityFloor]
  rw [one_div_pow]

end Lax263307Proofs.AlgorithmParameters

end

section

namespace Lax263307Proofs.BufferedEllipsoid

open Matrix Lax263307.BufferedEllipsoid

theorem coordinate_ball_bound {n:ℕ} (e:Fin n→ ℝ) (ρ:ℝ) (nonnegative:0≤ ρ)
    (ball:e ⬝ᵥ e≤ ρ ^ 2):∀ i, |e i|≤ ρ:=by
  intro i
  have h:(e i) ^ 2≤ ∑ j, (e j) ^ 2:=
    Finset.single_le_sum (fun j _ => sq_nonneg (e j)) (Finset.mem_univ i)
  have hs:(e i) ^ 2≤ ρ ^ 2:=h.trans (by simpa only [dotProduct,pow_two] using ball)
  simpa only [abs_of_nonneg nonnegative] using (sq_le_sq).mp hs

theorem scaled_cube_norm {n:ℕ} (positive:0 < n) (z:Fin n→ ℝ)
    (cube:∀ i,0≤ z i∧ z i≤ 1):scale z ⬝ᵥ scale z≤ (1 / 16:ℝ):=by
  have hn:(0:ℝ) < n:=by exact_mod_cast positive
  have hn1:(1:ℝ)≤ n:=by exact_mod_cast positive
  have each (i:Fin n):(scale z i) ^ 2≤ (1 / (4 * (n:ℝ))) ^ 2:=by
    have hlow:0≤ scale z i:=div_nonneg (cube i).1 (by positivity)
    have hhigh:scale z i≤ 1 / (4 * (n:ℝ)):=div_le_div_of_nonneg_right (cube i).2 (by positivity)
    exact pow_le_pow_left₀ hlow hhigh 2
  have hsum:=Finset.sum_le_sum (fun i (_:i∈ (Finset.univ:Finset (Fin n))) => each i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have heq:(n:ℝ) * (1 / (4 * (n:ℝ))) ^ 2=1 / (16 * n):=by field_simp; ring
  have hbound:1 / (16 * (n:ℝ))≤ (1 / 16:ℝ):=by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  simpa only [dotProduct,pow_two] using hsum.trans (heq.le.trans hbound)

theorem initial_ball {n:ℕ} (positive:0 < n) (z:Fin n→ ℝ)
    (cube:∀ i,0≤ z i∧ z i≤ 1) (ρ:ℝ) (nonnegative:0≤ ρ) (small:ρ≤ 1 / 4)
    (e:Fin n→ ℝ) (ball:e ⬝ᵥ e≤ ρ ^ 2):
    (scale z + e) ⬝ᵥ (scale z + e)≤ 1:=by
  have hscale:=Lax263307Proofs.BufferedEllipsoid.scaled_cube_norm positive z cube
  have hr:ρ ^ 2≤ (1 / 16:ℝ):=by nlinarith
  have hs:=Finset.sum_le_sum (fun i (_:i∈ (Finset.univ:Finset (Fin n))) =>
    show (scale z i + e i) ^ 2≤ 2 * (scale z i) ^ 2 + 2 * (e i) ^ 2 from by
      nlinarith [sq_nonneg (scale z i - e i)])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hs':(scale z + e) ⬝ᵥ (scale z + e)≤ 2 * (scale z ⬝ᵥ scale z) + 2 * (e ⬝ᵥ e):=by
    simpa only [dotProduct,pow_two,Pi.add_apply] using hs
  linarith

theorem integer_normal_norm {n:ℕ} (a:Fin n→ ℤ) (nonzero:∃ i,a i ≠ 0):
    1≤ (fun i => (a i:ℝ)) ⬝ᵥ (fun i => (a i:ℝ)):=by
  obtain ⟨i,hi⟩:=nonzero
  have hs:(0:ℤ) < (a i) ^ 2:=sq_pos_of_ne_zero hi
  have hsi:(1:ℤ)≤ (a i) ^ 2:=by omega
  have hsr:(1:ℝ)≤ (a i:ℝ) ^ 2:=by exact_mod_cast hsi
  have hsum:=Finset.single_le_sum (fun j (_:j∈ (Finset.univ:Finset (Fin n))) =>
    sq_nonneg (a j:ℝ)) (Finset.mem_univ i)
  exact hsr.trans (by simpa only [dotProduct,pow_two] using hsum)

end Lax263307Proofs.BufferedEllipsoid

end

section

namespace Lax263307Proofs.RoundedOracleSearch

open Matrix Lax263307.RoundedOracleSearch
open Lax109476.RationalCertificates

theorem cached_eq {n:ℕ} (state:State n):cached state=state:=by
  apply Prod.ext
  · funext i j
    simp [cached,Vector.get]
    rfl
  · funext i
    simp [cached,Vector.get]
    rfl

theorem scan_sound {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (Good:Result→ Prop)
    (answers:∀ k center answer,oracle k center=.found answer→ Good answer)
    (count k:ℕ) (state:State n) (answer:Result)
    (found:scan oracle k count state=some answer):Good answer:=by
  induction count generalizing k state with
  | zero => simp [scan] at found
  | succ count ih =>
    cases hreply:oracle k state.2 with
    | found result =>
      have heq:result=answer:=by simpa only [scan,hreply,Option.some.injEq] using found
      subst answer
      exact answers k state.2 result hreply
    | reject => simp [scan,hreply] at found
    | cut a =>
      apply ih (k + 1) (update k state a)
      simpa only [scan,hreply] using found

theorem search_sound {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (B:ℕ) (Good:Result→ Prop)
    (answers:∀ k center answer,oracle k center=.found answer→ Good answer):
    ∀ answer,search oracle B=some answer→ Good answer:=by
  intro answer found
  exact scan_sound oracle Good answers (steps n B) 0 (1,0) answer found

theorem scan_failure {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (no_reject:∀ k center,oracle k center ≠ .reject) (count k:ℕ)
    (failed:scan oracle k count (trajectory oracle k)=none):
    ∀ j,k≤ j→ j < k + count→ ∃ a,oracle j (trajectory oracle j).2=.cut a:=by
  induction count generalizing k with
  | zero => intro j hj hj'; omega
  | succ count ih =>
    cases hreply:oracle k (trajectory oracle k).2 with
    | found answer => simp [scan,hreply] at failed
    | reject => exact False.elim (no_reject k _ hreply)
    | cut a =>
      have hnext:trajectory oracle (k + 1)=update k (trajectory oracle k) a:=by
        simp only [trajectory,hreply,selectedNormal]
      have htail:scan oracle (k + 1) count (trajectory oracle (k + 1))=none:=by
        rw [hnext]
        simpa only [scan,hreply] using failed
      intro j hj hj'
      by_cases heq:j=k
      · subst j
        exact ⟨a,hreply⟩
      · exact ih (k + 1) htail j (by omega) (by omega)

theorem schedule_norm {n:ℕ} {Result:Type} (positive:0 < n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i ≠ 0) (k:ℕ):
    1≤ realVector (rationalNormal (normalSchedule oracle k)) ⬝ᵥ
      realVector (rationalNormal (normalSchedule oracle k)):=by
  have hnormal:∃ i,normalSchedule oracle k i ≠ 0:=by
    unfold normalSchedule
    cases hreply:oracle k (trajectory oracle k).2 with
    | cut a => exact nonzero k _ a hreply
    | found answer => exact ⟨⟨0,positive⟩,by simp [selectedNormal,fallback]⟩
    | reject => exact ⟨⟨0,positive⟩,by simp [selectedNormal,fallback]⟩
  have hcast:realVector (rationalNormal (normalSchedule oracle k)) =
      (fun i => (normalSchedule oracle k i:ℝ)):=by
    funext i
    simp [realVector,rationalNormal]
  rw [hcast]
  exact Lax263307Proofs.BufferedEllipsoid.integer_normal_norm (normalSchedule oracle k) hnormal

theorem trajectory_eq_sequences {n:ℕ} {Result:Type}
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (k:ℕ):
    (trajectory oracle k).1=Lax109476Proofs.EllipsoidSequence.shapes n
      (fun j => rationalNormal (normalSchedule oracle j)) k∧
    (trajectory oracle k).2=Lax109476Proofs.EllipsoidSequence.centers n
      (fun j => rationalNormal (normalSchedule oracle j)) 0 k:=by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    change (update k (trajectory oracle k) (normalSchedule oracle k)).1=_∧
      (update k (trajectory oracle k) (normalSchedule oracle k)).2=_
    simp only [update,cached_eq]
    change Lax109476Proofs.EllipsoidCenter.roundedStepShape n (trajectory oracle k).1
        (rationalNormal (normalSchedule oracle k))
        (Lax109476Proofs.EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n)
        (Lax109476Proofs.EllipsoidIteration.stepAccuracy n)=_∧
      Lax109476Proofs.EllipsoidCenter.roundedCenter n (trajectory oracle k).1
        (rationalNormal (normalSchedule oracle k)) (trajectory oracle k).2
        (Lax109476Proofs.EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n)=_
    simp only [Lax109476Proofs.EllipsoidSequence.shapes,Lax109476Proofs.EllipsoidSequence.centers]
    rw [ih.1,ih.2]
    exact ⟨rfl,rfl⟩

theorem search_complete {n:ℕ} {Result:Type} (dimension:2≤ n)
    (oracle:ℕ→ (Fin n→ ℚ)→ Reply n Result) (B:ℕ) (precision:2≤ B)
    (nonzero:∀ k center a,oracle k center=.cut a→ ∃ i,a i ≠ 0)
    (no_reject:∀ k center,oracle k center ≠ .reject)
    (z:Fin n→ ℝ) (cube:∀ i,0≤ z i∧ z i≤ 1)
    (retains:∀ k center a,oracle k center=.cut a→
      ∀ e:Fin n→ ℝ, (∀ i, |e i|≤ ((2:ℝ) ^ B)⁻¹)→
        (fun i => (a i:ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale z + e - (fun i => (center i:ℝ)))≤ 0):
    ∃ answer,search oracle B=some answer:=by
  by_contra hfound
  have hnone:search oracle B=none:=by
    cases h:search oracle B with
    | none => rfl
    | some answer => exact False.elim (hfound ⟨answer,h⟩)
  have hcuts:=scan_failure oracle no_reject (steps n B) 0 hnone
  let a:ℕ→ Fin n→ ℚ:=fun k => rationalNormal (normalSchedule oracle k)
  let ρ:ℝ:=((2:ℝ) ^ B)⁻¹
  have hρ:0≤ ρ:=by dsimp [ρ]; positivity
  have hsmall:ρ≤ 1 / 4:=by
    have hp:(4:ℝ)≤ (2:ℝ) ^ B:=by
      have h:=pow_le_pow_right₀ (show (1:ℝ)≤ 2 by norm_num) precision
      norm_num at h
      exact h
    dsimp [ρ]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num:(0:ℝ) < 4) hp
  apply Lax109476Proofs.EllipsoidTermination.cannot_retain_ball n dimension a
    (fun k => schedule_norm (by omega) oracle nonzero k) 0
    (Lax263307.BufferedEllipsoid.scale z) B
  · intro e he
    have h:=Lax263307Proofs.BufferedEllipsoid.initial_ball (by omega) z cube ρ hρ hsmall e he
    have hzero:realVector (0:Fin n→ ℚ)=0:=by funext i; simp [realVector]
    rw [hzero]
    simpa only [sub_zero] using h
  · intro k hk e he
    obtain ⟨normal,hreply⟩:=hcuts k (by omega)
      (by simpa only [Lax109476Proofs.EllipsoidSequence.thresholdSteps,steps,Nat.zero_add] using hk)
    have hnormal:a k=rationalNormal normal:=by
      simp only [a,normalSchedule,hreply,selectedNormal]
    rw [hnormal]
    have h:=retains k (trajectory oracle k).2 normal hreply e
      (Lax263307Proofs.BufferedEllipsoid.coordinate_ball_bound e ρ hρ he)
    rw [(trajectory_eq_sequences oracle k).2] at h
    have hcast:realVector (rationalNormal normal)=(fun i => (normal i:ℝ)):=by
      funext i
      simp [realVector,rationalNormal]
    rw [hcast]
    exact h

end Lax263307Proofs.RoundedOracleSearch

end

section

namespace Lax263307Proofs.ProjectedOracle

open Matrix
open Lax263307.ProjectedOracle Lax263307.AlgorithmParameters
open Lax263307.LinearRelaxation Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem search_correct {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K B D:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k h:ℕ)
    (hn:0 < n) (hk:0 < k)
    (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n)))
    (oracle_correct:∀ center,Correct G k h a K B D center (run lp flow a K B D G k child center)):
    SearchCorrect G k h D (search lp flow a K B D G k child):=by
  let oracle:=fun (_:ℕ) center => run lp flow a K B D G k child center
  have hs:∀ I,Lax263307.RoundedOracleSearch.search oracle (precision a K B n D)=some I→ Good G k h D I:=by
    apply Lax263307Proofs.RoundedOracleSearch.search_sound
    intro t center I he
    have hh:=oracle_correct center
    change Correct G k h a K B D center (oracle t center) at hh
    rw [he] at hh
    exact hh
  cases hout:search lp flow a K B D G k child with
  | some I => exact hs I hout
  | none =>
    intro J _ hJ
    by_contra hlarge
    have hsize:k≤ J.card:=by omega
    obtain ⟨I,hIJ,hcard⟩:=Finset.exists_subset_card_eq hsize
    have hI:G.IsIndepSet (I:Set (Fin n)):=hJ.mono (by simpa using hIJ)
    have hmem:indicator (level a K B n D) I∈ independentSetHull G k (level a K B n D):=
      subset_convexHull ℝ _ ⟨I,hI,hcard,rfl⟩
    have hnz:∀ t center normal,oracle t center=.cut normal→ ∃ i,normal i ≠ 0:=by
      intro t center normal he
      have hh:=oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      exact hh.1
    have hno:∀ t center,oracle t center ≠ .reject:=by
      intro t center he
      have hh:=oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      change independentSetHull G k (level a K B n D)=∅ at hh
      rw [hh] at hmem
      exact hmem
    have hretain:∀ t center normal,oracle t center=.cut normal→
        ∀ e:Index n (level a K B n D)→ ℝ,
        (∀ i, |e i|≤ ((2:ℝ)^precision a K B n D)⁻¹)→
        (fun i => (normal i:ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale (encode (indicator (level a K B n D) I)) + e -
            (fun i => (center i:ℝ)))≤ 0:=by
      intro t center normal he e he'
      have hh:=oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      exact hh.2 _ hmem e he'
    have hcube:∀ i:Index n (level a K B n D),
        0≤ encode (indicator (level a K B n D) I) i∧ encode (indicator (level a K B n D) I) i≤ 1:=by
      intro i
      simp only [encode,indicator]
      split_ifs <;> norm_num
    obtain ⟨answer,hans⟩:=Lax263307Proofs.RoundedOracleSearch.search_complete
      (Lax263307Proofs.CoordinateCatalog.catalog_two n (level a K B n D) hn) oracle
      (precision a K B n D) (by unfold precision; omega) hnz hno _ hcube hretain
    change search lp flow a K B D G k child=some answer at hans
    rw [hout] at hans
    contradiction

open Lax263307.GraphClasses Lax263307.PowerBagBounds

end Lax263307Proofs.ProjectedOracle

end

section

namespace Lax263307Proofs.ConditionedCosts

open Lax263307.LinearRelaxation RelaxationAlgebra

theorem conditioning_invariants {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A:Finset (Fin n)) (size:A.card≤ r) (positive:0 < value y A):
    (∀ v,0≤ conditioned y A v∧ conditioned y A v≤ 1)∧
    (∑ v:Fin n,conditioned y A v)=k∧
    (∀ v∈ A,conditioned y A v=1)∧
    (∀ v,0 < conditioned y A v→ 0 < value y (insert v A)):=by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    have hsize:=insert_size A (show A.card≤ r + 1 by omega) v
    have hnonneg:0≤ value y (insert v A):=by
      rw [value_of_size y _ hsize]
      exact (feasible.bounds _).1
    exact ⟨div_nonneg hnonneg positive.le,
      (div_le_one positive).2 (feasible.monotone A (by omega) v)⟩
  · simp_rw [conditioned, ← Finset.sum_div]
    rw [feasible.mass A (by omega)]
    exact mul_div_cancel_right₀ _ (ne_of_gt positive)
  · intro v hv
    simp [conditioned,Finset.insert_eq_of_mem hv,ne_of_gt positive]
  · intro v hv
    exact (div_pos_iff_of_pos_right positive).1 hv

end Lax263307Proofs.ConditionedCosts

end

section

namespace Lax263307Proofs.RecursiveRounding

open Lax263307.LinearRelaxation Lax263307.SeparatorComponents

theorem parts_disjoint {n:ℕ} {ι:Type} [Fintype ι]
    {G:SimpleGraph (Fin n)} {S:Finset (Fin n)} (P:Partition G S ι):
    (↑(Finset.univ:Finset ι):Set ι).PairwiseDisjoint P.vertices:=by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨c,_,hc⟩:=P.unique v (P.outside i v hvi)
  exact hij ((hc i hvi).trans (hc j hvj).symm)

theorem parts_cover {n:ℕ} {ι:Type} [Fintype ι]
    {G:SimpleGraph (Fin n)} {S:Finset (Fin n)} (P:Partition G S ι):
    combine P.vertices=Finset.univ \ S:=by
  classical
  ext v
  simp only [combine,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨i,hi⟩
    exact P.outside i v hi
  · intro hv
    obtain ⟨i,hi,_⟩:=P.unique v hv
    exact ⟨i,hi⟩

theorem parts_sum {n:ℕ} {ι:Type} [Fintype ι]
    {G:SimpleGraph (Fin n)} {S:Finset (Fin n)} (P:Partition G S ι)
    (x:Fin n→ ℝ):
    (∑ i, ∑ v∈ P.vertices i,x v)=(∑ v,x v) - ∑ v∈ S,x v:=by
  classical
  rw [← Finset.sum_biUnion (parts_disjoint P)]
  change (∑ v∈ combine P.vertices,x v)=_
  rw [parts_cover P]
  have hsplit:=Finset.sum_sdiff (f:=x) (Finset.subset_univ S)
  linarith

theorem combine_independent {n:ℕ} {ι:Type} [Fintype ι]
    (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (P:Partition G S ι)
    (I:ι→ Finset (Fin n)) (inside:∀ i,I i ⊆ P.vertices i)
    (independent:∀ i,G.IsIndepSet (I i:Set (Fin n))):
    G.IsIndepSet (combine I:Set (Fin n))∧ (combine I).card=∑ i, (I i).card:=by
  classical
  have hdisj:(↑(Finset.univ:Finset ι):Set ι).PairwiseDisjoint I:=by
    intro i hi j hj hne
    exact (parts_disjoint P hi hj hne).mono (inside i) (inside j)
  refine ⟨?_,Finset.card_biUnion hdisj⟩
  intro a ha b hb hab hadj
  obtain ⟨i,_,hai⟩:=Finset.mem_biUnion.mp ha
  obtain ⟨j,_,hbj⟩:=Finset.mem_biUnion.mp hb
  have hai':=inside i hai
  have hbj':=inside j hbj
  have hbi:=P.closed i a b hai' (P.outside j b hbj') hadj
  obtain ⟨c,_,hc⟩:=P.unique b (P.outside j b hbj')
  have hij:i=j:=(hc i hbi).trans (hc j hbj').symm
  subst j
  exact independent i hai hbj hab hadj

end Lax263307Proofs.RecursiveRounding

end

section

namespace Lax263307Proofs.HeavyRecursiveRounding

open Lax263307.LinearRelaxation Lax263307.SeparatorComponents
open Lax263307.ComponentCutEncoding

theorem ignored_cost {n:ℕ} {ι:Type} [Fintype ι] (c:ι→ ℝ) (δ k:ℝ)
    (hn:0 < n) (hδ:0≤ δ) (hk:0≤ k) (count:Fintype.card ι≤ 2 * n):
    (∑ i,if δ * k / (4 * n) < c i then 0 else c i)≤ δ * k / 2:=by
  classical
  have hn':(0:ℝ) < n:=by exact_mod_cast hn
  have hcut:0≤ δ * k / (4 * n):=by positivity
  have each (i:ι):(if δ * k / (4 * n) < c i then 0 else c i)≤ δ * k / (4 * n):=by
    split_ifs with h
    · exact hcut
    · exact not_lt.mp h
  have hsum:=Finset.sum_le_sum (fun i (_:i∈ (Finset.univ:Finset ι)) => each i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hcount:(Fintype.card ι:ℝ)≤ 2 * n:=by exact_mod_cast count
  have heq:2 * (n:ℝ) * (δ * k / (4 * n))=δ * k / 2:=by field_simp; ring
  exact hsum.trans ((mul_le_mul_of_nonneg_right hcount hcut).trans_eq heq)

theorem heavy_union_size {n:ℕ} {ι:Type} [Fintype ι]
    (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (P:Partition G S ι)
    (x:Fin n→ ℝ) (k:ℕ) (h:ℕ) (δ:ℝ)
    (hn:0 < n) (hδ:0≤ δ) (small:δ≤ 1 / 4)
    (count:Fintype.card ι≤ 2 * n)
    (mass:(∑ v,x v)=k) (light:∑ v∈ S,x v≤ δ * k)
    (I:ι→ Finset (Fin n)) (targets:ι→ ℕ)
    (inside:∀ i,I i ⊆ P.vertices i)
    (independent:∀ i,G.IsIndepSet (I i:Set (Fin n)))
    (rounded:∀ i,δ * k / (4 * n) < ∑ v∈ P.vertices i,x v→
      (1 - δ) * (∑ v∈ P.vertices i,x v) < targets i)
    (answers:∀ i,δ * k / (4 * n) < ∑ v∈ P.vertices i,x v→
      (1 - 4 * δ) ^ h * (targets i:ℝ)≤ (I i).card):
    G.IsIndepSet (combine I:Set (Fin n))∧
      (1 - 4 * δ) ^ (h + 1) * (k:ℝ)≤ (combine I).card:=by
  classical
  let c (i:ι):= ∑ v∈ P.vertices i,x v
  let cutoff:ℝ:=δ * k / (4 * n)
  have hsplit:(∑ i,if cutoff < c i then c i else 0) +
      (∑ i,if cutoff < c i then 0 else c i)=∑ i,c i:=by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hsum:=Lax263307Proofs.RecursiveRounding.parts_sum P x
  have hignored:=Lax263307Proofs.HeavyRecursiveRounding.ignored_cost c δ k hn hδ (Nat.cast_nonneg k) count
  rw [mass] at hsum
  have hheavy:(1 - 3 * δ / 2) * (k:ℝ)≤ ∑ i,if cutoff < c i then c i else 0:=by
    change (∑ i,c i)=_ at hsum
    change (∑ i,if cutoff < c i then 0 else c i)≤ _ at hignored
    linarith
  have hf:0≤ (1 - 4 * δ) ^ h:=pow_nonneg (by linarith) _
  have hone:0≤ 1 - δ:=by linarith
  have each (i:ι):(1 - 4 * δ) ^ h * (1 - δ) * (if cutoff < c i then c i else 0)≤ (I i).card:=by
    by_cases hi:cutoff < c i
    · rw [if_pos hi]
      have ht:=(rounded i hi).le
      have ha:=answers i hi
      have ht':(1 - 4 * δ) ^ h * (1 - δ) * c i≤ (1 - 4 * δ) ^ h * (targets i:ℝ):=by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht hf
      exact ht'.trans ha
    · rw [if_neg hi,mul_zero]
      exact Nat.cast_nonneg _
  obtain ⟨hI,hcard⟩:=Lax263307Proofs.RecursiveRounding.combine_independent G S P I inside independent
  have hanswers:=Finset.sum_le_sum (fun i (_:i∈ (Finset.univ:Finset ι)) => each i)
  rw [← Finset.mul_sum] at hanswers
  have hmass:=mul_le_mul_of_nonneg_left hheavy (mul_nonneg hf hone)
  have hstep:1 - 4 * δ≤ (1 - δ) * (1 - 3 * δ / 2):=by nlinarith [sq_nonneg δ]
  have hstep':=mul_le_mul_of_nonneg_right hstep (mul_nonneg hf (Nat.cast_nonneg k))
  have hfinal:(1 - 4 * δ) ^ (h + 1) * (k:ℝ)≤ ∑ i, ((I i).card:ℝ):=by
    rw [pow_succ]
    nlinarith [hanswers,hmass,hstep']
  exact ⟨hI,hfinal.trans_eq (by exact_mod_cast hcard.symm)⟩

end Lax263307Proofs.HeavyRecursiveRounding

end

section

namespace Lax263307Proofs.ComponentCutEncoding

open Lax263307.LinearRelaxation Lax263307.ComponentCutEncoding

theorem coordinate_sum {n r:ℕ} (A:Finset (Fin n)) (size:A.card≤ r + 2)
    (z:MomentVector n r):
    (∑ B:Coordinate n r,if A=B.val then z B else 0)=value z A:=by
  classical
  rw [RelaxationAlgebra.value_of_size z A size]
  rw [Finset.sum_eq_single ⟨A,size⟩]
  · simp
  · intro B _ hB
    have hne:A ≠ B.val:=fun he => hB (Subtype.ext he.symm)
    simp [hne]
  · simp

theorem evaluation_identity {n r:ℕ} (A C:Finset (Fin n)) (u:ℕ)
    (size:A.card≤ r) (z:MomentVector n r):
    evaluate (coefficient A C u) z =
      (∑ v∈ C,value z (insert v A)) - (u:ℝ) * value z A:=by
  classical
  unfold evaluate coefficient
  push_cast
  simp_rw [sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
  have hfirst:(∑ B:Coordinate n r, ∑ v∈ C,
      (if insert v A=B.val then (1:ℝ) else 0) * z B) =
      ∑ v∈ C,value z (insert v A):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    simpa only [ite_mul,one_mul,zero_mul] using
      coordinate_sum (insert v A) (by have:=Finset.card_insert_le v A; omega) z
  have hsecond:(∑ B:Coordinate n r,
      (if A=B.val then (u:ℝ) else 0) * z B) =
      (u:ℝ) * value z A:=by
    simp only [ite_mul,zero_mul]
    have heq (B:Coordinate n r):(if A=B.val then (u:ℝ) * z B else 0) =
        (u:ℝ) * (if A=B.val then z B else 0):=by split_ifs <;> simp
    simp_rw [heq, ← Finset.mul_sum]
    rw [coordinate_sum A (by omega)]
  rw [hfirst,hsecond]

end Lax263307Proofs.ComponentCutEncoding

end

section

namespace Lax263307Proofs.ComponentCuts

open Lax263307.LinearRelaxation RelaxationAlgebra

theorem indicator_cut {n:ℕ} (G:SimpleGraph (Fin n)) (r:ℕ)
    (C:Finset (Fin n)) (u:ℕ) (bound:IsIndependenceBound G C u)
    (A:Finset (Fin n)) (size:A.card≤ r)
    (I:Finset (Fin n)) (independent:G.IsIndepSet (I:Set (Fin n))):
    ∑ v∈ C,value (indicator r I) (insert v A)≤
      (u:ℝ) * value (indicator r I) A:=by
  rw [indicator_sum I A C (by omega),indicator_value I A (by omega)]
  by_cases hAI:A ⊆ I
  · simp only [if_pos hAI,mul_one]
    exact_mod_cast bound (C ∩ I) Finset.inter_subset_left
      (independent_subset G independent Finset.inter_subset_right)
  · simp [hAI]

theorem cut_convex {n r:ℕ} (A C:Finset (Fin n)) (u:ℕ):
    Convex ℝ {z:MomentVector n r |
      ∑ v∈ C,value z (insert v A)≤ (u:ℝ) * value z A}:=by
  intro y hy z hz a b ha hb _
  simp only [Set.mem_ofPred_eq] at hy hz ⊢
  simp_rw [value_combination,Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    a * (∑ v∈ C,value y (insert v A)) + b * (∑ v∈ C,value z (insert v A))≤
      a * ((u:ℝ) * value y A) + b * ((u:ℝ) * value z A):=
        add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hz hb)
    _=_:=by ring

theorem valid_cut {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (C:Finset (Fin n)) (u:ℕ) (bound:IsIndependenceBound G C u)
    (A:Finset (Fin n)) (size:A.card≤ r)
    (z:MomentVector n r) (member:z∈ independentSetHull G k r):
    ∑ v∈ C,value z (insert v A)≤ (u:ℝ) * value z A:=by
  apply convexHull_min (t:= {z | ∑ v∈ C,value z (insert v A)≤
    (u:ℝ) * value z A}) ?_ (cut_convex A C u) member
  rintro y ⟨I,hI,_,rfl⟩
  exact indicator_cut G r C u bound A size I hI

end Lax263307Proofs.ComponentCuts

end

section

namespace Lax263307Proofs.StrongComponentGaps

open Lax263307.LinearRelaxation Lax263307.ComponentCutEncoding

theorem coordinate_indicator_sum {n r:ℕ} (S:Finset (Fin n)):
    (∑ B:Coordinate n r,if S=B.val then (1:ℝ) else 0)≤ 1:=by
  classical
  by_cases hS:S.card≤ r + 2
  · let B₀:Coordinate n r:= ⟨S,hS⟩
    have heq (B:Coordinate n r):S=B.val↔ B₀=B:=by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp_rw [heq]
    simp
  · have hne (B:Coordinate n r):S ≠ B.val:=by intro h; exact hS (h ▸ B.property)
    simp [hne]

theorem coefficient_l1 {n r:ℕ} (A C:Finset (Fin n)) (u:ℕ):
    (∑ B:Coordinate n r, |(coefficient A C u B:ℝ)|)≤ C.card + u:=by
  classical
  have hpoint (B:Coordinate n r):|(coefficient A C u B:ℝ)|≤
      (∑ v∈ C,if insert v A=B.val then (1:ℝ) else 0) +
        (if A=B.val then (u:ℝ) else 0):=by
    unfold coefficient
    push_cast
    have h:=abs_sub_le (∑ v∈ C,if insert v A=B.val then (1:ℝ) else 0)
      0 (if A=B.val then (u:ℝ) else 0)
    have hsum:0≤ (∑ v∈ C,if insert v A=B.val then (1:ℝ) else 0):=
      Finset.sum_nonneg (fun v _ => by split_ifs <;> positivity)
    have hif:0≤ (if A=B.val then (u:ℝ) else 0):=by split_ifs <;> positivity
    simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hsum,abs_of_nonneg hif] using h
  calc
    _≤ ∑ B:Coordinate n r, ((∑ v∈ C,if insert v A=B.val then (1:ℝ) else 0) +
        (if A=B.val then (u:ℝ) else 0)):=Finset.sum_le_sum (fun B _ => hpoint B)
    _=(∑ v∈ C, ∑ B:Coordinate n r,if insert v A=B.val then (1:ℝ) else 0) +
        (∑ B:Coordinate n r,if A=B.val then (u:ℝ) else 0):=by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
    _≤ C.card + u:=by
      have hC:(∑ v∈ C, ∑ B:Coordinate n r,if insert v A=B.val then (1:ℝ) else 0)≤ C.card:=by
        simpa using Finset.sum_le_sum (fun v (_:v∈ C) => coordinate_indicator_sum (insert v A))
      have hu:(∑ B:Coordinate n r,if A=B.val then (u:ℝ) else 0)≤ u:=by
        have h:=mul_le_mul_of_nonneg_left (coordinate_indicator_sum (r:=r) A) (Nat.cast_nonneg u:(0:ℝ)≤ _)
        simpa only [Finset.mul_sum,mul_ite,mul_one,mul_zero] using h
      exact add_le_add hC hu

theorem evaluation_stable {n r:ℕ} (A C:Finset (Fin n)) (u:ℕ)
    (x y:MomentVector n r) (ρ:ℝ) (hρ:0≤ ρ)
    (near:∀ B, |x B - y B|≤ ρ):
    |evaluate (coefficient A C u) x - evaluate (coefficient A C u) y|≤ (C.card + u) * ρ:=by
  classical
  unfold evaluate
  rw [← Finset.sum_sub_distrib]
  calc
    _≤ ∑ B, |(coefficient A C u B:ℝ) * x B - (coefficient A C u B:ℝ) * y B|:=Finset.abs_sum_le_sum_abs _ _
    _≤ ∑ B, |(coefficient A C u B:ℝ)| * ρ:=by
      apply Finset.sum_le_sum
      intro B _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (near B) (abs_nonneg _)
    _≤ _:=by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (coefficient_l1 A C u) hρ

theorem component_gap {n r:ℕ} (G:SimpleGraph (Fin n)) (k:ℕ)
    (y:MomentVector n r) (A C:Finset (Fin n)) (u:ℕ)
    (size:A.card≤ r) (bound:IsIndependenceBound G C u)
    (η δ:ℝ) (hη:0 < η) (hδ:0 < δ) (hn:0 < n) (hk:0 < k)
    (moment:η≤ value y A)
    (heavy:δ * (k:ℝ) / (2 * n)≤ ∑ v∈ C,conditioned y A v)
    (rounded:(u:ℝ)≤ (1 - δ) * ∑ v∈ C,conditioned y A v):
    (∀ z∈ independentSetHull G k r,evaluate (coefficient A C u) z≤ 0)∧
      η * δ ^ 2 * (k:ℝ) / (2 * n)≤ evaluate (coefficient A C u) y:=by
  have hpos:0 < value y A:=hη.trans_le moment
  have hn':(0:ℝ) < n:=by exact_mod_cast hn
  have hk':(0:ℝ) < k:=by exact_mod_cast hk
  let c:= ∑ v∈ C,conditioned y A v
  have hcost:δ ^ 2 * (k:ℝ) / (2 * n)≤ c - u:=by
    have hmul:=mul_le_mul_of_nonneg_left heavy hδ.le
    have he:δ * (δ * (k:ℝ) / (2 * n))=δ ^ 2 * (k:ℝ) / (2 * n):=by ring
    rw [he] at hmul
    dsimp only [c]
    nlinarith [hmul]
  have hgap:0≤ δ ^ 2 * (k:ℝ) / (2 * n):=by positivity
  have heq:evaluate (coefficient A C u) y=value y A * (c - u):=by
    rw [Lax263307Proofs.ComponentCutEncoding.evaluation_identity A C u size]
    dsimp [c]
    simp_rw [conditioned, ← Finset.sum_div]
    field_simp
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Lax263307Proofs.ComponentCutEncoding.evaluation_identity A C u size]
    exact sub_nonpos.mpr (Lax263307Proofs.ComponentCuts.valid_cut G k r C u bound A size z hz)
  · rw [heq]
    have h:=mul_le_mul moment hcost hgap hpos.le
    calc
      _=η * (δ ^ 2 * (k:ℝ) / (2 * n)):=by ring
      _≤ _:=h

theorem query_gap {n r:ℕ} (G:SimpleGraph (Fin n)) (k:ℕ)
    (x y:MomentVector n r) (A C:Finset (Fin n)) (u:ℕ)
    (size:A.card≤ r) (bound:IsIndependenceBound G C u) (upper:u≤ n)
    (η δ:ℝ) (hη:0 < η) (hδ:0 < δ) (hn:0 < n) (hk:0 < k)
    (moment:η≤ value y A)
    (heavy:δ * (k:ℝ) / (2 * n)≤ ∑ v∈ C,conditioned y A v)
    (rounded:(u:ℝ)≤ (1 - δ) * ∑ v∈ C,conditioned y A v)
    (near:∀ B, |x B - y B|≤ η * δ ^ 2 / (8 * (n:ℝ) ^ 2)):
    (∀ z∈ independentSetHull G k r,evaluate (coefficient A C u) z≤ 0)∧
      η * δ ^ 2 / (4 * n)≤ evaluate (coefficient A C u) x:=by
  obtain ⟨hvalid,hgap⟩:=Lax263307Proofs.StrongComponentGaps.component_gap G k y A C u size bound η δ hη hδ hn hk moment heavy rounded
  have hn':(0:ℝ) < n:=by exact_mod_cast hn
  have hk1:(1:ℝ)≤ k:=by exact_mod_cast hk
  let ρ:=η * δ ^ 2 / (8 * (n:ℝ) ^ 2)
  have hρ:0≤ ρ:=by dsimp [ρ]; positivity
  have hstab:=Lax263307Proofs.StrongComponentGaps.evaluation_stable A C u x y ρ hρ near
  have hC:(C.card:ℝ)≤ n:=by exact_mod_cast C.card_le_univ.trans_eq (Fintype.card_fin n)
  have hu:(u:ℝ)≤ n:=by exact_mod_cast upper
  have hstab':|evaluate (coefficient A C u) x - evaluate (coefficient A C u) y|≤ 2 * n * ρ:=
    hstab.trans (mul_le_mul_of_nonneg_right (by linarith:(C.card:ℝ) + u≤ 2 * n) hρ)
  have hsmall:2 * (n:ℝ) * ρ=η * δ ^ 2 / (4 * n):=by dsimp [ρ]; field_simp; ring
  have hbase:η * δ ^ 2 / (2 * n)≤ η * δ ^ 2 * (k:ℝ) / (2 * n):=
    div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hk1 (show 0≤ η * δ ^ 2 by positivity)]) (by positivity)
  have heq:η * δ ^ 2 / (2 * n)=2 * (η * δ ^ 2 / (4 * n)):=by ring
  have hdiff:=(abs_le.mp hstab').1
  rw [hsmall] at hdiff
  rw [heq] at hbase
  exact ⟨hvalid,by linarith⟩

end Lax263307Proofs.StrongComponentGaps

end

section

namespace Lax263307Proofs.ComputedRounding

open Lax263307.ComputedRounding Lax263307.LinearRelaxation Lax263307.SeparatorComponents
open Lax263307.ComponentCutEncoding

theorem target_bounds (δ c:ℚ) (hδ:δ≤ 1) (hc:0≤ c):
    (1 - δ) * c < (target δ c:ℚ)∧ (target δ c - 1:ℕ)≤ (1 - δ) * c:=by
  constructor
  · simpa only [target,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one ((1 - δ) * c)
  · simpa only [target,Nat.add_sub_cancel] using
      Nat.floor_le (mul_nonneg (sub_nonneg.mpr hδ) hc)

theorem collect_correct {n r:ℕ} {ι:Type} [Fintype ι]
    (G:SimpleGraph (Fin n)) (k h:ℕ) (δ:ℚ) (η:ℝ)
    (hn:0 < n) (hk:0 < k) (hδ:0 < δ) (small:δ≤ 1 / 4) (hη:0 < η)
    (x y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A S:Finset (Fin n)) (P:Partition G S ι) (size:A.card≤ r)
    (moment:η≤ value y A) (count:Fintype.card ι≤ 2 * n)
    (light:∑ v∈ S,conditioned y A v≤ (δ:ℝ) * k)
    (order:List ι) (complete:∀ i,i∈ order)
    (c:ι→ ℚ) (cost_cast:∀ i, (c i:ℝ)=∑ v∈ P.vertices i,conditioned y A v)
    (query:ι→ ℕ→ Option (Finset (Fin n)))
    (queries:∀ i,δ * k / (4 * n) < c i→
      match query i (target δ (c i)) with
      | some I => I ⊆ P.vertices i∧ G.IsIndepSet (I:Set (Fin n))∧
          (1 - 4 * (δ:ℝ)) ^ h * (target δ (c i):ℝ)≤ I.card
      | none => IsIndependenceBound G (P.vertices i) (target δ (c i) - 1))
    (near:∀ B, |x B - y B|≤ η * (δ:ℝ) ^ 2 / (32 * (n:ℝ) ^ 2)):
    match collect order P.vertices δ k c query with
    | .found I => G.IsIndepSet (I:Set (Fin n))∧
        (1 - 4 * (δ:ℝ)) ^ (h + 1) * (k:ℝ)≤ I.card
    | .cut C u => u≤ n∧ IsIndependenceBound G C u∧
        (∀ z∈ independentSetHull G k r,evaluate (coefficient A C u) z≤ 0)∧
        η * (δ:ℝ) ^ 2 / (16 * n)≤ evaluate (coefficient A C u) x∧
        (∑ B:Coordinate n r, |(coefficient A C u B:ℝ)|)≤ 2 * n:=by
  have hδR:(0:ℝ) < δ:=by exact_mod_cast hδ
  have hsmallR:(δ:ℝ)≤ 1 / 4:=by
    have hs:(δ:ℝ)≤ ((1 / 4:ℚ):ℝ):=Rat.cast_le.mpr small
    norm_num at hs ⊢
    exact hs
  have hinv:=Lax263307Proofs.ConditionedCosts.conditioning_invariants G k r y feasible A size
    (hη.trans_le moment)
  have hc0 (i:ι):(0:ℝ)≤ c i:=by
    rw [cost_cast]
    exact Finset.sum_nonneg (fun v _ => (hinv.1 v).1)
  have hc1 (i:ι):(c i:ℝ)≤ (P.vertices i).card:=by
    rw [cost_cast]
    simpa using Finset.sum_le_sum (fun v (_:v∈ P.vertices i) => (hinv.1 v).2)
  have ht (i:ι):(1 - (δ:ℝ)) * (c i:ℝ) < (target δ (c i):ℝ)∧
      (target δ (c i) - 1:ℕ)≤ (1 - (δ:ℝ)) * (c i:ℝ):=by
    have ht:=target_bounds δ (c i) (by linarith) (by exact_mod_cast hc0 i)
    exact_mod_cast ht
  have active_iff (i:ι):δ * k / (4 * n) < c i↔
      (δ:ℝ) * k / (4 * n) < ∑ v∈ P.vertices i,conditioned y A v:=by
    rw [← cost_cast]
    norm_cast
  unfold collect
  cases hfind:order.find? (fun i => (answer δ k c query i).isNone) with
  | some i =>
    have hnone:answer δ k c query i=none:=by
      simpa only [Option.isNone_iff_eq_none] using List.find?_some hfind
    have hactive:δ * k / (4 * n) < c i:=by
      by_contra hfalse
      simp only [answer,if_neg hfalse] at hnone
      contradiction
    have hquery:query i (target δ (c i))=none:=by
      simpa only [answer,if_pos hactive] using hnone
    have hbound:=queries i hactive
    rw [hquery] at hbound
    have hcard:(P.vertices i).card≤ n:=(P.vertices i).card_le_univ.trans_eq (Fintype.card_fin n)
    have hupper:target δ (c i) - 1≤ n:=by
      have hupperR:(target δ (c i) - 1:ℕ)≤ (n:ℝ):=by
        have hcardR:((P.vertices i).card:ℝ)≤ n:=by exact_mod_cast hcard
        nlinarith only [(ht i).2,hc0 i,hc1 i,hδR,hcardR]
      exact_mod_cast hupperR
    have hheavy:((δ:ℝ) / 2) * k / (2 * n)≤ ∑ v∈ P.vertices i,conditioned y A v:=by
      have heq:((δ:ℝ) / 2) * k / (2 * n)=(δ:ℝ) * k / (4 * n):=by ring
      rw [heq]
      exact ((active_iff i).mp hactive).le
    have hround:(target δ (c i) - 1:ℕ)≤
        (1 - (δ:ℝ) / 2) * ∑ v∈ P.vertices i,conditioned y A v:=by
      rw [← cost_cast]
      nlinarith only [(ht i).2,hc0 i,hδR]
    have hnear:∀ B, |x B - y B|≤ η * ((δ:ℝ) / 2) ^ 2 / (8 * (n:ℝ) ^ 2):=by
      intro B
      convert near B using 1
      ring
    obtain ⟨hvalid,hgap⟩:=Lax263307Proofs.StrongComponentGaps.query_gap G k x y A (P.vertices i)
      (target δ (c i) - 1) size hbound hupper η ((δ:ℝ) / 2) hη (by linarith) hn hk
      moment hheavy hround hnear
    refine ⟨hupper,hbound,hvalid, ?_, ?_⟩
    · convert hgap using 1
      ring
    · apply (Lax263307Proofs.StrongComponentGaps.coefficient_l1 A (P.vertices i) (target δ (c i) - 1)).trans
      exact_mod_cast (show (P.vertices i).card + (target δ (c i) - 1)≤ 2 * n by omega)
  | none =>
    have hsome (i:ι):∃ I,answer δ k c query i=some I:=by
      have hi:=List.find?_eq_none.mp hfind i (complete i)
      cases he:answer δ k c query i with
      | none => simp only [he,Option.isNone_none] at hi; contradiction
      | some I => exact ⟨I,rfl⟩
    let I:ι→ Finset (Fin n):=fun i => (answer δ k c query i).getD ∅
    have hlegal (i:ι):I i ⊆ P.vertices i∧ G.IsIndepSet (I i:Set (Fin n)):=by
      by_cases hactive:δ * k / (4 * n) < c i
      · obtain ⟨J,hJ⟩:=hsome i
        have hq:query i (target δ (c i))=some J:=by simpa only [answer,if_pos hactive] using hJ
        have hs:=queries i hactive
        rw [hq] at hs
        have hI:I i=J:=by simp only [I,hJ,Option.getD_some]
        rw [hI]
        exact ⟨hs.1,hs.2.1⟩
      · have hI:I i=∅:=by simp only [I,answer,if_neg hactive,Option.getD_some]
        rw [hI]
        exact ⟨Finset.empty_subset _,by intro a ha; simp at ha⟩
    apply Lax263307Proofs.HeavyRecursiveRounding.heavy_union_size G S P (conditioned y A) k h δ
      hn hδR.le hsmallR count hinv.2.1 light I (fun i => target δ (c i))
      (fun i => (hlegal i).1) (fun i => (hlegal i).2)
    · intro i _
      rw [← cost_cast]
      exact (ht i).1
    · intro i hi
      have hactive:=(active_iff i).mpr hi
      obtain ⟨J,hJ⟩:=hsome i
      have hq:query i (target δ (c i))=some J:=by simpa only [answer,if_pos hactive] using hJ
      have hs:=queries i hactive
      rw [hq] at hs
      simpa only [I,hJ,Option.getD_some] using hs.2.2

end Lax263307Proofs.ComputedRounding

end

section

namespace Lax263307Proofs.ConditioningDistribution

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution RelaxationAlgebra

theorem distribution_identities {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A:Finset (Fin n)) (size:A.card < r) (positive:0 < value y A)
    (target_positive:0 < k):
    (∀ v,0≤ marginal y A k v)∧
    (∑ v:Fin n,marginal y A k v)=1∧
    (∀ u v,0≤ joint y A k u v)∧
    (∀ u v,joint y A k u v=joint y A k v u)∧
    (∀ v, (∑ u:Fin n,joint y A k u v)=marginal y A k v)∧
    (∀ u v,G.Adj u v→ joint y A k u v=0)∧
    (∀ u v,0 < marginal y A k v→
      marginal y (insert v A) k u=joint y A k u v / marginal y A k v):=by
  have hk:(0:ℝ) < k:=by exact_mod_cast target_positive
  have hk0:(k:ℝ) ≠ 0:=ne_of_gt hk
  have hA0:value y A ≠ 0:=ne_of_gt positive
  have invariants:=Lax263307Proofs.ConditionedCosts.conditioning_invariants
    G k r y feasible A (by omega) positive
  have hsize (v:Fin n):(insert v A).card≤ r + 1:=by
    have:=Finset.card_insert_le v A
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact div_nonneg (invariants.1 v).1 hk.le
  · simp_rw [marginal, ← Finset.sum_div]
    rw [invariants.2.1,div_self hk0]
  · intro u v
    have hnonneg:0≤ value y (insert u (insert v A)):=by
      rw [value_of_size y _ (insert_size _ (hsize v) u)]
      exact (feasible.bounds _).1
    exact div_nonneg hnonneg (mul_nonneg (sq_nonneg _) positive.le)
  · intro u v
    simp only [joint,Finset.insert_comm]
  · intro v
    simp_rw [joint, ← Finset.sum_div]
    rw [feasible.mass (insert v A) (hsize v)]
    dsimp [marginal,conditioned]
    field_simp
  · intro u v huv
    have hnot:¬G.IsIndepSet (↑(insert u (insert v A)):Set (Fin n)):=by
      intro hi
      exact hi (by simp) (by simp) huv.ne huv
    have hz:=feasible.vanishes
      ⟨insert u (insert v A),insert_size _ (hsize v) u⟩ hnot
    rw [joint,value_of_size y _ (insert_size _ (hsize v) u),hz,zero_div]
  · intro u v hv
    have hv0:value y (insert v A) ≠ 0:=by
      have hcost:0 < conditioned y A v:=(div_pos_iff_of_pos_right hk).1 hv
      exact ne_of_gt (invariants.2.2.2 v hcost)
    dsimp [marginal,conditioned,joint]
    field_simp

end Lax263307Proofs.ConditioningDistribution

end

section

namespace Lax263307Proofs.EntropyBounds

open Lax263307.Entropy EntropyAlgebra

theorem entropy_bounds {n:ℕ} (π:Fin n→ ℝ) (probability:IsProbability π):
    0≤ entropy π∧ entropy π≤ Real.logb 2 n:=by
  constructor
  · exact div_nonneg (natural_entropy_nonneg π probability) log_two_pos.le
  · exact div_le_div_of_nonneg_right (natural_entropy_le_log π probability) log_two_pos.le

end Lax263307Proofs.EntropyBounds

end

section

namespace Lax263307Proofs.EntropyGap

open Lax263307.Entropy EntropyAlgebra

theorem joint_entry_le {n:ℕ} (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hq:∀ u v,0≤ q u v) (hm:∀ v, (∑ u,q u v)=π v) (u v:Fin n):
    q u v≤ π v:=by
  rw [← hm v]
  exact Finset.single_le_sum (fun i _ => hq i v) (Finset.mem_univ u)

theorem row_marginal {n:ℕ} (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hs:∀ u v,q u v=q v u) (hm:∀ v, (∑ u,q u v)=π v) (u:Fin n):
    (∑ v,q u v)=π u:=by
  simp_rw [hs u]
  exact hm u

theorem weighted_conditional_entropy {n:ℕ} (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hπ:IsProbability π) (hq:∀ u v,0≤ q u v)
    (hm:∀ v, (∑ u,q u v)=π v):
    (∑ v,π v * naturalEntropy (fun u => q u v / π v)) =
      (∑ v, ∑ u,Real.negMulLog (q u v)) - naturalEntropy π:=by
  have hpoint (u v:Fin n):
      π v * Real.negMulLog (q u v / π v) =
        Real.negMulLog (q u v) + q u v * Real.log (π v):=by
    rcases eq_or_lt_of_le (hπ.1 v) with hv | hv
    · have hzero:q u v=0:=le_antisymm
        ((joint_entry_le π q hq hm u v).trans_eq hv.symm) (hq u v)
      simp [← hv,hzero]
    · exact scaled_negMulLog_div _ _ hv
  simp_rw [naturalEntropy,Finset.mul_sum,hpoint,Finset.sum_add_distrib,
    ← Finset.sum_mul,hm]
  simp [Real.negMulLog,Finset.sum_neg_distrib,sub_eq_add_neg]

theorem natural_gap_bound {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (hπ:IsProbability π) (hq:∀ u v,0≤ q u v)
    (hs:∀ u v,q u v=q v u) (hm:∀ v, (∑ u,q u v)=π v)
    (he:∀ u v,G.Adj u v→ q u v=0):
    adjacencyMass G π≤ naturalEntropy π -
      ∑ v,π v * naturalEntropy (fun u => q u v / π v):=by
  let cost:=fun u v => -Real.negMulLog (q u v) -
    q u v * Real.log (π u) - q u v * Real.log (π v)
  have hpoint (u v:Fin n):
      q u v - π u * π v + (if G.Adj u v then π u * π v else 0)≤ cost u v:=by
    by_cases hedge:G.Adj u v
    · simp [cost,hedge,he u v hedge]
    · simp only [if_neg hedge,add_zero]
      rcases eq_or_lt_of_le (hq u v) with hzero | hpos
      · simp only [← hzero,Real.negMulLog_zero,zero_mul,sub_zero,zero_sub,cost]
        simpa using neg_nonpos.mpr (mul_nonneg (hπ.1 u) (hπ.1 v))
      · have hv:=lt_of_lt_of_le hpos (joint_entry_le π q hq hm u v)
        have hu:=lt_of_lt_of_le (hpos.trans_eq (hs u v)) (joint_entry_le π q hq hm v u)
        exact relative_term_bound _ _ _ hpos hu hv
  have htotal:(∑ v, ∑ u,q u v)=1:=by simp_rw [hm]; exact hπ.2
  have hproduct:(∑ v, ∑ u,π u * π v)=1:=by
    simp_rw [← Finset.sum_mul,hπ.2,one_mul]
    exact hπ.2
  have hcrossV:(∑ v, ∑ u,q u v * Real.log (π v))=-naturalEntropy π:=by
    simp only [← Finset.sum_mul,hm,naturalEntropy,Real.negMulLog,
      neg_mul,Finset.sum_neg_distrib,neg_neg]
  have hcrossU:(∑ v, ∑ u,q u v * Real.log (π u))=-naturalEntropy π:=by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,row_marginal π q hs hm,naturalEntropy,
      Real.negMulLog,neg_mul,Finset.sum_neg_distrib,neg_neg]
  have hsum:=Finset.sum_le_sum (s:=Finset.univ) fun v _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun u _ => hpoint u v
  have hadj:(∑ v, ∑ u,if G.Adj u v then π u * π v else 0)=adjacencyMass G π:=by
    rw [Finset.sum_comm]
    rfl
  simp_rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,cost,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib] at hsum
  rw [htotal,hproduct,hadj,hcrossU,hcrossV] at hsum
  rw [weighted_conditional_entropy π q hπ hq hm]
  linarith

theorem average_entropy_gap {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π:Fin n→ ℝ) (q:Fin n→ Fin n→ ℝ)
    (probability:IsProbability π) (nonnegative:∀ u v,0≤ q u v)
    (symmetric:∀ u v,q u v=q v u)
    (marginals:∀ v, (∑ u,q u v)=π v)
    (edge_zero:∀ u v,G.Adj u v→ q u v=0):
    adjacencyMass G π≤ entropy π - ∑ v,π v * entropy (fun u => q u v / π v):=by
  have hgap:=natural_gap_bound G π q probability nonnegative symmetric marginals edge_zero
  have hmass:0≤ adjacencyMass G π:=by
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact mul_nonneg (probability.1 u) (probability.1 v)
    · exact le_rfl
  have hm:adjacencyMass G π * Real.log 2≤ adjacencyMass G π:=by
    nlinarith [log_two_le_one]
  simp_rw [entropy, ← mul_div_assoc, ← Finset.sum_div, ← sub_div]
  exact (le_div_iff₀ log_two_pos).2 (hm.trans hgap)

end Lax263307Proofs.EntropyGap

end

section

namespace Lax263307Proofs.ConditioningExistence

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution Lax263307.Entropy
open EntropyAlgebra RelaxationAlgebra

theorem marginal_probability {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (hy:IsFeasible G k r y)
    (A:Finset (Fin n)) (hA:A.card≤ r) (hpos:0 < value y A) (hk:0 < k):
    IsProbability (marginal y A k):=by
  have hkR:(0:ℝ) < k:=by exact_mod_cast hk
  have h:=Lax263307Proofs.ConditionedCosts.conditioning_invariants G k r y hy A hA hpos
  refine ⟨fun v => div_nonneg (h.1 v).1 hkR.le, ?_⟩
  simp_rw [marginal, ← Finset.sum_div]
  rw [h.2.1,div_self (ne_of_gt hkR)]

end Lax263307Proofs.ConditioningExistence

end

section

namespace Lax263307Proofs.HeavyConditioning

open Lax263307.Entropy Lax263307.HeavyConditioning

theorem heavy_weight_decrease {n:ℕ} (π f:Fin n→ ℝ) (probability:IsProbability π)
    (nonnegative:∀ v,0 < π v→ 0≤ f v) (H L p:ℝ)
    (hH:0≤ H) (hHL:H≤ L) (hL:0 < L) (hp:0 < p) (hn:0 < n)
    (average:(∑ v,π v * f v) < H - 2 / p):
    ∃ v:Fin n,1 / (2 * (n:ℝ) * p * L)≤ π v∧ f v < H - 1 / p:=by
  classical
  let τ:ℝ:=1 / (2 * (n:ℝ) * p * L)
  have hn':(0:ℝ) < n:=by exact_mod_cast hn
  have hτ:0 < τ:=by dsimp [τ]; positivity
  by_contra hnone
  push Not at hnone
  have each (v:Fin n):π v * (H - f v)≤ π v / p + τ * L:=by
    by_cases hv:τ≤ π v
    · have hfv:=hnone v hv
      have hprod:=mul_le_mul_of_nonneg_left (show H - f v≤ 1 / p by linarith) (probability.1 v)
      have hτL:0≤ τ * L:=mul_nonneg hτ.le hL.le
      simpa only [mul_one_div] using hprod.trans (le_add_of_nonneg_right hτL)
    · have hsmall:π v≤ τ:=(not_le.mp hv).le
      have hprod:π v * (H - f v)≤ π v * H:=by
        by_cases hpos:0 < π v
        · exact mul_le_mul_of_nonneg_left (by linarith [nonnegative v hpos]) (probability.1 v)
        · have hz:π v=0:=le_antisymm (not_lt.mp hpos) (probability.1 v)
          simp [hz]
      have hmul:π v * H≤ τ * L:=
        (mul_le_mul_of_nonneg_right hsmall hH).trans (mul_le_mul_of_nonneg_left hHL hτ.le)
      exact (hprod.trans hmul).trans (le_add_of_nonneg_left (div_nonneg (probability.1 v) hp.le))
  have hsum:=Finset.sum_le_sum (fun v (_:v∈ (Finset.univ:Finset (Fin n))) => each v)
  simp only [Finset.sum_sub_distrib,mul_sub, ← Finset.sum_mul,Finset.sum_add_distrib,
    ← Finset.sum_div,probability.2,one_mul,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hsum
  have hτeq:(n:ℝ) * τ * L=1 / (2 * p):=by
    dsimp [τ]
    field_simp
  rw [hτeq] at hsum
  have hfrac:1 / p + 1 / (2 * p) < 2 / p:=by
    field_simp
    nlinarith
  linarith

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307Proofs.EntropyDecrease Lax263307Proofs.ConditioningExistence

theorem heavy_entropy_decrease {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p:ℕ) (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (A:Finset (Fin n)) (size:A.card < r) (positive:0 < value y A)
    (target_positive:0 < k) (threshold_positive:0 < p) (order_positive:0 < n)
    (expensive:(k:ℝ) ^ 2 / p < edgeCost G (conditioned y A)):
    ∃ v:Fin n,probabilityFloor n p≤ marginal y A k v∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k) - 1 / p:=by
  have hk:(0:ℝ) < k:=by exact_mod_cast target_positive
  have hp:(0:ℝ) < p:=by exact_mod_cast threshold_positive
  obtain ⟨hπ,hsum,hq,hsym,hmarg,hedge,hcond⟩:=
    Lax263307Proofs.ConditioningDistribution.distribution_identities
      G k r y feasible A size positive target_positive
  have hprob:IsProbability (marginal y A k):= ⟨hπ,hsum⟩
  have hgap:=Lax263307Proofs.EntropyGap.average_entropy_gap
    G (marginal y A k) (joint y A k) hprob hq hsym hmarg hedge
  have hscaled:adjacencyMass G (marginal y A k) =
      adjacencyMass G (conditioned y A) / (k:ℝ) ^ 2:=
    adjacencyMass_div G (conditioned y A) k (ne_of_gt hk)
  have hmass:(2:ℝ) / p < adjacencyMass G (marginal y A k):=by
    rw [hscaled]
    apply (div_lt_div_iff₀ hp (sq_pos_of_pos hk)).2
    have h:=(div_lt_iff₀ hp).1 expensive
    unfold edgeCost at h
    nlinarith
  have havg:(∑ v,marginal y A k v * entropy (fun u => joint y A k u v / marginal y A k v)) <
      entropy (marginal y A k) - 2 / p:=by linarith
  have hnonnegative (v:Fin n) (hv:0 < marginal y A k v):
      0≤ entropy (fun u => joint y A k u v / marginal y A k v):=by
    have hcost:0 < conditioned y A v:=(div_pos_iff_of_pos_right hk).mp hv
    have hnext:=(Lax263307Proofs.ConditionedCosts.conditioning_invariants
      G k r y feasible A size.le positive).2.2.2 v hcost
    have hcard:(insert v A).card≤ r:=(Finset.card_insert_le v A).trans (by omega)
    have h:=(Lax263307Proofs.EntropyBounds.entropy_bounds _
      (marginal_probability G k r y feasible (insert v A) hcard hnext target_positive)).1
    have heq:marginal y (insert v A) k=fun u => joint y A k u v / marginal y A k v:=
      funext (fun u => hcond u v hv)
    rwa [heq] at h
  have hb:=Lax263307Proofs.EntropyBounds.entropy_bounds _ hprob
  have hL:Real.logb 2 n≤ (Nat.log2 n:ℝ) + 1:=
    Lax263307Proofs.LightSeparators.logFactor_upper n
  obtain ⟨v,hv,hdrop⟩:=heavy_weight_decrease (marginal y A k)
    (fun v => entropy (fun u => joint y A k u v / marginal y A k v)) hprob hnonnegative
    (entropy (marginal y A k)) ((Nat.log2 n:ℝ) + 1) p hb.1 (hb.2.trans hL)
    (by positivity) hp order_positive havg
  have hfloor:0 < probabilityFloor n p:=by unfold probabilityFloor; positivity
  have hvpos:0 < marginal y A k v:=hfloor.trans_le hv
  refine ⟨v,hv, ?_⟩
  have heq:marginal y (insert v A) k=fun u => joint y A k u v / marginal y A k v:=
    funext (fun u => hcond u v hvpos)
  rwa [heq]

theorem heavy_low_edge_cost {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p:ℕ) (y:MomentVector n r) (feasible:IsFeasible G k r y)
    (order_positive:0 < n) (target_positive:0 < k)
    (level_positive:0 < r) (threshold_positive:0 < p)
    (budget:(p:ℝ) * ((Nat.log2 n:ℝ) + 1)≤ r):
    ∃ A:Finset (Fin n),A.card≤ r∧ probabilityFloor n p ^ r≤ value y A∧
      0 < value y A∧ (∀ v,0≤ conditioned y A v∧ conditioned y A v≤ 1)∧
      (∑ v,conditioned y A v)=k∧ edgeCost G (conditioned y A)≤ (k:ℝ) ^ 2 / p:=by
  classical
  have hn:(0:ℝ) < n:=by exact_mod_cast order_positive
  have hk:(0:ℝ) < k:=by exact_mod_cast target_positive
  have hp:(0:ℝ) < p:=by exact_mod_cast threshold_positive
  let τ:=probabilityFloor n p
  have hτ:0 < τ:=by dsimp [τ,probabilityFloor]; positivity
  have hτ1:τ≤ 1:=by
    have hn1:(1:ℝ)≤ n:=by exact_mod_cast order_positive
    have hp1:(1:ℝ)≤ p:=by exact_mod_cast threshold_positive
    dsimp [τ,probabilityFloor]
    apply (div_le_one (by positivity)).mpr
    have hL:(1:ℝ)≤ (Nat.log2 n:ℝ) + 1:=le_add_of_nonneg_left (Nat.cast_nonneg _)
    nlinarith [mul_le_mul hn1 hp1 (by positivity) (by norm_num)]
  have hzero:value y (∅:Finset (Fin n))=1:=feasible.normalized
  have hprob0:=marginal_probability G k r y feasible ∅ (by simp) (by rw [hzero]; norm_num) target_positive
  have hbounds0:=Lax263307Proofs.EntropyBounds.entropy_bounds _ hprob0
  have hL:entropy (marginal y ∅ k)≤ (Nat.log2 n:ℝ) + 1:=
    hbounds0.2.trans (Lax263307Proofs.LightSeparators.logFactor_upper n)
  suffices hgood:∃ A:Finset (Fin n),A.card≤ r∧ τ ^ r≤ value y A∧
      0 < value y A∧ edgeCost G (conditioned y A)≤ (k:ℝ) ^ 2 / p by
    obtain ⟨A,hA,hval,hpos,he⟩:=hgood
    have h:=Lax263307Proofs.ConditionedCosts.conditioning_invariants G k r y feasible A hA hpos
    exact ⟨A,hA,hval,hpos,h.1,h.2.1,he⟩
  by_contra hnone
  push Not at hnone
  have hstep:∀ t:ℕ,t≤ r→ ∃ A:Finset (Fin n),A.card≤ t∧ τ ^ t≤ value y A∧
      0 < value y A∧ entropy (marginal y A k)≤ entropy (marginal y ∅ k) - (t:ℝ) / p∧
      (0 < t→ entropy (marginal y A k) < entropy (marginal y ∅ k) - (t:ℝ) / p):=by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨∅,by simp,by simp [hzero],by rw [hzero]; norm_num,by simp,by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨A,hA,hval,hpos,hH,_⟩:=ih (by omega)
      have hvalr:τ ^ r≤ value y A:=
        (pow_le_pow_of_le_one hτ.le hτ1 (by omega:t≤ r)).trans hval
      obtain ⟨v,hv,hdrop⟩:=Lax263307Proofs.HeavyConditioning.heavy_entropy_decrease G k r p y feasible A (by omega) hpos
        target_positive threshold_positive order_positive (hnone A (by omega) hvalr hpos)
      have hvpos:0 < marginal y A k v:=hτ.trans_le hv
      have hcost:0 < conditioned y A v:=(div_pos_iff_of_pos_right hk).mp hvpos
      have hnext:=(Lax263307Proofs.ConditionedCosts.conditioning_invariants
        G k r y feasible A (by omega) hpos).2.2.2 v hcost
      have heq:value y (insert v A)=(k:ℝ) * marginal y A k v * value y A:=by
        unfold marginal conditioned
        field_simp
      have hk1:(1:ℝ)≤ k:=by exact_mod_cast target_positive
      have hprod:τ * value y A≤ value y (insert v A):=by
        rw [heq]
        have hkmarg:τ≤ (k:ℝ) * marginal y A k v:=
          hv.trans (by nlinarith)
        exact mul_le_mul_of_nonneg_right hkmarg hpos.le
      have hnextval:τ ^ (t + 1)≤ value y (insert v A):=by
        rw [pow_succ]
        exact (mul_le_mul_of_nonneg_right hval hτ.le).trans (by simpa [mul_comm] using hprod)
      have hcard:(insert v A).card≤ t + 1:=(Finset.card_insert_le v A).trans (by omega)
      have hstrict:entropy (marginal y (insert v A) k) <
          entropy (marginal y ∅ k) - ((t + 1:ℕ):ℝ) / p:=by
        push_cast
        rw [add_div]
        linarith
      exact ⟨insert v A,hcard,hnextval,hnext,hstrict.le,fun _ => hstrict⟩
  obtain ⟨A,hA,_hval,hpos,_hH,hstrict⟩:=hstep r le_rfl
  have hnonnegative:=(Lax263307Proofs.EntropyBounds.entropy_bounds _
    (marginal_probability G k r y feasible A hA hpos target_positive)).1
  have hbudget:(Nat.log2 n:ℝ) + 1≤ (r:ℝ) / p:=(le_div_iff₀ hp).mpr (by nlinarith [budget])
  have hfinal:=hstrict level_positive
  linarith

end Lax263307Proofs.HeavyConditioning

end

section

namespace Lax263307Proofs.HeavyRationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open Lax263307.HeavyConditioning Lax263307.HeavyRationalConditioning

theorem floor_cast (n p:ℕ):(rationalFloor n p:ℝ)=probabilityFloor n p:=by
  unfold rationalFloor probabilityFloor
  push_cast
  rfl

theorem heavy_passes_iff {n r:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p:ℕ) (y:RationalVector n r) (A:Finset (Fin n)) (hp:0 < p):
    HeavyPasses G k p y A↔ 0 < value (realVector y) A∧
      edgeCost G (conditioned (realVector y) A)≤ (k:ℝ) ^ 2 / p∧
      probabilityFloor n p ^ r≤ value (realVector y) A:=by
  have hfloor:rationalFloor n p ^ r≤ rationalValue y A↔
      probabilityFloor n p ^ r≤ value (realVector y) A:=by
    rw [Lax263307Proofs.RationalConditioning.value_cast, ← floor_cast]
    norm_cast
  rw [HeavyPasses,Lax263307Proofs.RationalConditioning.passes_iff G k p y A hp,hfloor]
  tauto

theorem search_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p:ℕ) (y:RationalVector n r) (feasible:IsFeasible G k r (realVector y))
    (order_positive:0 < n) (target_positive:0 < k)
    (level_positive:0 < r) (threshold_positive:0 < p)
    (budget:(p:ℝ) * ((Nat.log2 n:ℝ) + 1)≤ r):
    ∃ A:Finset (Fin n),findHeavyConditioning G k p y=some A∧ A.card≤ r∧
      probabilityFloor n p ^ r≤ value (realVector y) A∧ 0 < value (realVector y) A∧
      (∀ v,0≤ conditioned (realVector y) A v∧ conditioned (realVector y) A v≤ 1)∧
      (∑ v,conditioned (realVector y) A v)=k∧
      edgeCost G (conditioned (realVector y) A)≤ (k:ℝ) ^ 2 / p:=by
  obtain ⟨B,hB,hfloorB,hposB,_,_,heB⟩:=Lax263307Proofs.HeavyConditioning.heavy_low_edge_cost
    G k r p (realVector y) feasible order_positive target_positive level_positive threshold_positive budget
  have hpassB:=(heavy_passes_iff G k p y B threshold_positive).mpr ⟨hposB,heB,hfloorB⟩
  have hmemB:=(Lax263307Proofs.RationalConditioning.candidate_complete n r B).mpr hB
  cases hsearch:findHeavyConditioning G k p y with
  | none =>
    have hnone:=List.find?_eq_none.mp hsearch B hmemB
    simp [hpassB] at hnone
  | some A =>
    have hpass:HeavyPasses G k p y A:=by
      have h:=List.find?_some hsearch
      simpa using h
    have hA:=(Lax263307Proofs.RationalConditioning.candidate_complete n r A).mp
      (List.mem_of_find?_eq_some hsearch)
    have htest:=(heavy_passes_iff G k p y A threshold_positive).mp hpass
    have h:=Lax263307Proofs.ConditionedCosts.conditioning_invariants
      G k r (realVector y) feasible A hA htest.1
    exact ⟨A,rfl,hA,htest.2.2,htest.1,h.1,h.2.1,htest.2.1⟩

end Lax263307Proofs.HeavyRationalConditioning

end

section

namespace Lax263307Proofs.NearOracle

open scoped NNRat
open Lax263307.NearOracle Lax263307.GraphClasses Lax263307.PowerBagBounds
open Lax263307.LinearRelaxation Lax263307.RationalConditioning
open Lax263307.AlgorithmParameters Lax263307.ComputedSeparators
open Lax263307.RepeatedCutAccounting

theorem costs_cast {n r:ℕ} (y:RationalVector n r) (A:Finset (Fin n))
    (nonnegative:∀ v,0≤ conditioned (realVector y) A v) (v:Fin n):
    (costs y A v:ℝ)=conditioned (realVector y) A v:=by
  have heq:((rationalValue y (insert v A) / rationalValue y A:ℚ):ℝ) =
      conditioned (realVector y) A v:=by
    simp only [conditioned,Lax263307Proofs.RationalConditioning.value_cast,Rat.cast_div]
  have hq:(0:ℚ)≤ rationalValue y (insert v A) / rationalValue y A:=by
    exact_mod_cast (heq.symm ▸ nonnegative v)
  change ((max 0 (rationalValue y (insert v A) / rationalValue y A):ℚ):ℝ)=_
  rw [max_eq_right hq]
  exact heq

theorem order_complete (q:ℕ) (i:Option (Fin q)):i∈ order q:=by
  cases i <;> simp [order]

theorem exists_oracle_with_parts (C:GraphClass) (hereditary:IsHereditary C)
    (a A:ℕ) (ha:0 < a) (hA:0 < A) (class_bound:HasPowerBagBound C a A):
    ∃ (flow:List ℕ→ List ℕ) (K B:ℕ),Lax759944.RamPolytime.RamPolytime flow∧
      0 < K∧ 0 < B∧ SeparatorCorrect C flow a K B∧ ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G∈ C n→ 0 < n→ ∀ (D k h:ℕ),4≤ D→ cutoff a K B n D < k→
      ∀ (y:RationalVector n (level a K B n D)),
      IsFeasible G k (level a K B n D) (realVector y)→
      ∀ (x:MomentVector n (level a K B n D)),
      (∀ T, |x T - realVector y T|≤ (momentFloor a K B n D:ℝ) *
        (1 / (D:ℝ)) ^ 2 / (32 * (n:ℝ) ^ 2))→
      ∀ (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n))),ChildCorrect G D h child→
      Correct G k h D (momentFloor a K B n D) x (run flow a K B D G k y child):=by
  obtain ⟨flow,K,B,hpoly,hK,hB,hsep⟩:=
    Lax263307Proofs.ComputedSeparators.light_separator C hereditary a A ha hA class_bound
  refine ⟨flow,K,B,hpoly,hK,hB,hsep, ?_⟩
  intro n G _ hG hn D k h hD hlarge y hfeasible x hnear child hchild
  let r:=level a K B n D
  let p:=sparsity a K B n D
  let ℓ:=load B n D
  let δ:ℚ:=1 / D
  let η:ℝ:=momentFloor a K B n D
  have hb:=Lax263307Proofs.AlgorithmParameters.budgets hK hB hD hlarge
  have hk:0 < k:=by omega
  have hδcast:(δ:ℝ)=1 / (D:ℝ):=by dsimp [δ]; push_cast; rfl
  have hδ:(0:ℚ) < δ:=by rw [← Rat.cast_pos (K:=ℝ),hδcast]; exact hb.2.2.2.1
  have hsmall:δ≤ (1 / 4:ℚ):=by
    have hh:(δ:ℝ)≤ ((1 / 4:ℚ):ℝ):=by
      norm_num
      rw [hδcast]
      exact hb.2.2.2.2.1
    exact Rat.cast_le.mp hh
  have hη:0 < η:=by
    have hp:0 < sparsity a K B n D:=hb.2.1
    dsimp only [η]
    rw [Lax263307Proofs.AlgorithmParameters.conditioning_floor]
    unfold Lax263307.HeavyConditioning.probabilityFloor
    positivity
  obtain ⟨A,hfind,hsize,hmoment,hpositive,hcosts,hmass,hedge⟩:=
    Lax263307Proofs.HeavyRationalConditioning.search_correct G k r p y hfeasible hn hk hb.2.2.1 hb.2.1 hb.2.2.2.2.2.2.1
  have hmoment':η≤ value (realVector y) A:=by
    dsimp only [η]
    rw [Lax263307Proofs.AlgorithmParameters.conditioning_floor]
    exact hmoment
  let costs':=costs y A
  have hcast (v:Fin n):(costs' v:ℝ)=conditioned (realVector y) A v:=
    costs_cast y A (fun v => (hcosts v).1) v
  have hbound (v:Fin n):(costs' v:ℝ)≤ 1:=by rw [hcast]; exact (hcosts v).2
  have hmass':(∑ v, (costs' v:ℝ))≤ k:=by simp only [hcast]; exact hmass.le
  have hedge':Lax263307.Entropy.edgeCost G (fun v => (costs' v:ℝ))≤ (k:ℝ) ^ 2 / p:=by
    simpa only [hcast] using hedge
  have hS:=hsep n G hG hn costs' k p ℓ hk hb.2.1 hb.1 hbound hmass' hedge'
    hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2
  let cs:=cuts (step flow G costs' B ℓ k) n Finset.univ
  obtain ⟨hq,_,hlight,P,hverts,hparts⟩:=hS
  have hverts':P.vertices=pieces cs:=funext hverts
  let c:Option (Fin cs.length)→ ℚ:=fun i => ∑ v∈ pieces cs i, (costs' v:ℚ)
  have hc (i:Option (Fin cs.length)):(c i:ℝ)=∑ v∈ P.vertices i,conditioned (realVector y) A v:=by
    dsimp only [c]
    rw [hverts i]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    exact hcast v
  have hcount:Fintype.card (Option (Fin cs.length))≤ 2 * n:=by
    change cs.length≤ n at hq
    simp only [Fintype.card_option,Fintype.card_fin]
    omega
  have hlight':(∑ v∈ Lax263307.ComputedSeparators.separator cs,conditioned (realVector y) A v)≤
      (δ:ℝ) * k:=by
    have hℓ:(0:ℝ) < ℓ:=by exact_mod_cast hb.1
    have hbudget:12 * (ratio B n:ℝ)≤ (δ:ℝ) * ℓ:=by
      dsimp only [ratio]
      push_cast
      rw [hδcast]
      simpa only [mul_assoc] using hb.2.2.2.2.2.1
    have hlast:12 * (ratio B n:ℝ) * k / ℓ≤ (δ:ℝ) * k:=by
      apply (div_le_iff₀ hℓ).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg k)]
    have hh:=hlight.trans hlast
    simpa only [cost,hcast] using hh
  have hqueries:∀ i:Option (Fin cs.length),δ * k / (4 * n) < c i→
      match child (P.vertices i) (Lax263307.ComputedRounding.target δ (c i)) with
      | some I => I ⊆ P.vertices i∧ G.IsIndepSet (I:Set (Fin n))∧
          (1 - 4 * (δ:ℝ)) ^ h * (Lax263307.ComputedRounding.target δ (c i):ℝ)≤ I.card
      | none => IsIndependenceBound G (P.vertices i) (Lax263307.ComputedRounding.target δ (c i) - 1):=by
    intro i _
    have hh:=hchild (P.vertices i) (hparts i) (Lax263307.ComputedRounding.target δ (c i))
    cases he:child (P.vertices i) (Lax263307.ComputedRounding.target δ (c i)) <;>
      simpa only [he,hδcast] using hh
  have hnear':∀ T, |x T - realVector y T|≤ η * (δ:ℝ) ^ 2 / (32 * (n:ℝ) ^ 2):=by
    simpa only [hδcast] using hnear
  have hcol:=Lax263307Proofs.ComputedRounding.collect_correct G k h δ η hn hk hδ hsmall hη
    x (realVector y) hfeasible A (Lax263307.ComputedSeparators.separator cs) P hsize hmoment' hcount hlight'
    (order cs.length) (order_complete cs.length) c hc
    (fun i t => child (P.vertices i) t) hqueries hnear'
  rw [hverts'] at hcol
  dsimp only [run]
  rw [hfind]
  change Correct G k h D η x
    (match Lax263307.ComputedRounding.collect (order cs.length) (pieces cs) δ k c
      (fun i t => child (pieces cs i) t) with
      | .found I => Result.found I
      | .cut C u => Result.cut A C u)
  cases hout:Lax263307.ComputedRounding.collect (order cs.length) (pieces cs) δ k c
      (fun i t => child (pieces cs i) t) with
  | found I =>
    rw [hout] at hcol
    simpa only [Correct,hδcast] using hcol
  | cut C u =>
    rw [hout] at hcol
    change A.card≤ r∧ _
    exact ⟨hsize,by simpa only [hδcast] using hcol⟩

end Lax263307Proofs.NearOracle

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem exists_solvers_with_parts (C:GraphClass) (hereditary:IsHereditary C)
    (a A:ℕ) (ha:0< a) (hA:0< A) (hclass:PowerBagBounds.HasPowerBagBound C a A):
    ∃ lp flow K b,Lax759944.RamPolytime.RamPolytime lp∧ NativeEncodedLP.Encoded lp∧
      Lax759944.RamPolytime.RamPolytime flow∧ 0< K∧ 0< b∧ NearOracle.SeparatorCorrect C flow a K b∧ OracleCorrect C lp flow a K b:=by
  obtain ⟨lp,hpoly,hlp⟩:=NativeEncodedLP.exists_solver
  obtain ⟨flow,K,b,hflow,hK,hb,hsep,hnear⟩:=NearOracle.exists_oracle_with_parts C hereditary a A ha hA hclass
  refine ⟨lp,flow,K,b,hpoly,hlp,hflow,hK,hb,hsep,?_⟩
  intro n G _ hG hn D k h hD hlarge child hc center
  apply Lax263307Proofs.ProjectedOracle.run_correct lp flow a K b D G k h hK hn hD
    (fun m N P => (hlp m N P).2) child
  intro y hy x hx
  exact hnear n G hG hn D k h hD hlarge y hy x hx child hc

theorem search_correct {C:GraphClass} {lp flow:List ℕ→ List ℕ} {a K b:ℕ}
    (ho:OracleCorrect C lp flow a K b) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG:G∈ C n) (hn:0< n) (D k h:ℕ) (hD:4≤ D) (hlarge:cutoff a K b n D< k)
    (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n))) (hc:NearOracle.ChildCorrect G D h child):
    ProjectedOracle.SearchCorrect G k h D (ProjectedOracle.search lp flow a K b D G k child):=by
  exact Lax263307Proofs.ProjectedOracle.search_correct lp flow a K b D G k h hn (by omega) child
    (ho n G hG hn D k h hD hlarge child hc)

def child {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b D fuel:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (S:Finset (Fin n)) (t:ℕ):Option (Finset (Fin n)):=
  (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t).map
    (fun I => I.image (label S))

end Lax263307Proofs.NativeRecursiveOracle

end

section

namespace Lax263307Proofs.WeightedAlgorithm

open Lax263307.WeightedAlgorithm Lax263307.WeightRounding Lax263307.IndependentBlowUp
open Lax263307.PositiveWeights Lax263307.WeightedIndependentSet
open Lax263307.GraphClasses Lax263307.BlowUpClasses Lax263307.EdgeSublinearSeparators

theorem relabel_approximation {n:ℕ} (G:SimpleGraph (Fin n)) (copies:Fin n→ ℕ)
    (δ:ℚ) (I:Finset (Fin (∑ v,copies v)))
    (hI:IsApproximation (numbered G copies) (fun _ => 1) δ I):
    IsCardinalityApproximation G copies δ (I.image (labeling copies)):=by
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hv
    exact hI.1 hi hj (fun hij => huv (congrArg (labeling copies) hij))
  · intro J hJ
    let J':=J.image (labeling copies).symm
    have hJ':(numbered G copies).IsIndepSet (J':Set (Fin (∑ v,copies v))):=by
      intro i hi j hj hij
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hi
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hj
      have huv:u ≠ v:=fun he => hij (congrArg (labeling copies).symm he)
      simpa only [numbered,SimpleGraph.comap_adj,Equiv.apply_symm_apply] using hJ hu hv huv
    have hh:=hI.2 J' hJ'
    simp only [weight,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    rw [Finset.card_image_of_injective _ (labeling copies).injective]
    simpa only [J',Finset.card_image_of_injective _ (labeling copies).symm.injective] using hh

end Lax263307Proofs.WeightedAlgorithm

end

section

namespace Lax263307Proofs.NativeSolverSemantics

open Lax263307 GraphClasses EdgeSublinearSeparators PowerBagBounds BlowUpClasses
open WeightedAlgorithm WeightRounding PositiveWeights WeightedIndependentSet

theorem exists_solvers_with_parts (C:GraphClass) (hereditary:IsHereditary C)
    (separators:HasStronglyEdgeSublinearSeparators C):
    ∃ (lp flow:List ℕ→ List ℕ) (a A K b:ℕ),
      Lax759944.RamPolytime.RamPolytime lp∧ NativeEncodedLP.Encoded lp∧
      Lax759944.RamPolytime.RamPolytime flow∧ 0< a∧ 0< A∧ 0< K∧ 0< b∧
      HasPowerBagBound (blowUpClass C) a A∧ NearOracle.SeparatorCorrect (blowUpClass C) flow a K b∧ NativeRecursiveOracle.OracleCorrect (blowUpClass C) lp flow a K b∧
      ∀ n (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],G∈ C n→
        ∀ weights ε,0<ε→ ε<1→ IsApproximation G weights ε (solve lp flow a K b G weights ε):=by
  obtain ⟨a,A,ha,hA,hbound⟩:=Lax263307Proofs.BlowUpBagBounds.blowup_power_bag_bound C hereditary separators
  obtain ⟨lp,flow,K,b,hpolyLP,hlp,hpolyFlow,hK,hb,hsep,ho⟩:=NativeRecursiveOracle.exists_solvers_with_parts
    (blowUpClass C) (Lax263307Proofs.BlowUpClasses.hereditary_closure C) a A ha hA hbound
  have hunweighted:∀ n (G:SimpleGraph (Fin n)) [DecidableRel G.Adj],G∈ blowUpClass C n→
      ∀ ε:ℚ,0<ε→ ε<1→ IsApproximation G (fun _ => 1) ε (RecursiveAlgorithm.independentSet lp flow a K b G ε):=by
    intro n G _ hG ε hε hε1
    exact Lax263307Proofs.RecursiveAlgorithm.independentSet_correct (blowUpClass C) (Lax263307Proofs.BlowUpClasses.hereditary_closure C)
      lp flow a K b (fun m H _ hH hm D k h hD hlarge child hc =>
        NativeRecursiveOracle.search_correct ho H hH hm D k h hD hlarge child hc) G hG ε hε hε1
  refine ⟨lp,flow,a,A,K,b,hpolyLP,hlp,hpolyFlow,ha,hA,hK,hb,hbound,hsep,ho,?_⟩
  intro n G _ hG w ε hε hεsmall
  dsimp only [solve]
  split_ifs with htrivial
  · apply Lax263307Proofs.PositiveWeights.nonpositive_case G w _ ε hε.le hεsmall.le
    intro v
    rcases htrivial with hn | hw
    · exact False.elim (by have:=v.isLt; omega)
    · have hmax:positiveWeights w v≤ maximumWeight (positiveWeights w):=by apply Finset.le_max'; simp
      exact (le_max_left (w v) 0).trans (hmax.trans hw)
  · have hn:0< n:=by omega
    have hmax:0< maximumWeight (positiveWeights w):=lt_of_not_ge (fun h => htrivial (Or.inr h))
    let cp:=copies (positiveWeights w) ε
    let H:=numbered G cp
    have hclass:H∈ blowUpClass C (∑ v,cp v):=Lax263307Proofs.BlowUpClasses.copy_graph_mem C G hG cp _ (labeling cp)
    have happrox:=hunweighted _ H hclass (ε/2) (by positivity) (by linarith)
    apply Lax263307Proofs.PositiveWeights.signed_weight_transfer G w ε hε.le hεsmall.le
    apply Lax263307Proofs.WeightedProjection.approximation_transfer G (positiveWeights w) ε
      (fun v => le_max_right _ _) hn hε hεsmall hmax
    exact Lax263307Proofs.WeightedAlgorithm.relabel_approximation G cp (ε/2) _ happrox

end Lax263307Proofs.NativeSolverSemantics

end

theorem solution:∀ (C:Lax263307.GraphClasses.GraphClass),
  Lax263307.GraphClasses.IsHereditary C→
    Lax263307.EdgeSublinearSeparators.HasStronglyEdgeSublinearSeparators C→
      ∃ (lp:List Nat→ List Nat) (flow:List Nat→ List Nat) (a:Nat) (A:Nat) (K:Nat) (b:Nat),
        And (Lax759944.RamPolytime.RamPolytime lp)
          (And (Lax263307Proofs.NativeEncodedLP.Encoded lp)
            (And (Lax759944.RamPolytime.RamPolytime flow)
              (And (Nat.lt ((0:Nat)) a)
                (And (Nat.lt ((0:Nat)) A)
                  (And (Nat.lt ((0:Nat)) K)
                    (And (Nat.lt ((0:Nat)) b)
                      (And (Lax263307.PowerBagBounds.HasPowerBagBound (Lax263307.BlowUpClasses.blowUpClass C) a A)
                        (And
                          (Lax263307Proofs.NearOracle.SeparatorCorrect (Lax263307.BlowUpClasses.blowUpClass C) flow a K
                            b)
                          (And
                            (Lax263307Proofs.NativeRecursiveOracle.OracleCorrect (Lax263307.BlowUpClasses.blowUpClass C)
                              lp flow a K b)
                            (∀ (n:Nat) (G:SimpleGraph (Fin n))
                              [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
                              @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                                  (@Set.instMembership (SimpleGraph (Fin n))) (C n) G→
                                ∀ (weights:Fin n→ Rat) (ε:Rat),
                                  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
                                    @LT.lt Rat Rat.instLT ε
                                        (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))→
                                      @Lax263307.WeightedIndependentSet.IsApproximation n G weights ε
                                        (@Lax263307.WeightedAlgorithm.solve n lp flow a K b G inst weights ε))))))))))):= @Lax263307Proofs.NativeSolverSemantics.exists_solvers_with_parts
