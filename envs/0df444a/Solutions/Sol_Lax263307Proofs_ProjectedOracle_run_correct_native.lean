-- Prove2me | solution 1 for Lax263307Proofs.ProjectedOracle.run_correct_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:59:41.013199+00:00
-- url     : https://prove2.me/submissions/0b676df6-2fd6-4992-969b-557135b0684e

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces

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

namespace Lax263307Proofs.RelaxationAlgebra

open Lax263307.LinearRelaxation

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

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

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

namespace Lax263307Proofs.CoordinateCatalog

open Lax263307.LinearRelaxation Lax263307.RationalConditioning Lax263307.CoordinateCatalog

theorem catalog_complete (n r:ℕ) (A:Coordinate n r):A∈ catalog n r:=by
  have hmem:A.val∈ sets n r:=
    List.mem_dedup.mpr ((Lax263307Proofs.RationalConditioning.candidate_complete n (r + 2) A.val).mpr A.property)
  apply List.mem_map.mpr
  exact ⟨⟨A.val,hmem⟩,List.mem_attach _ _,Subtype.ext rfl⟩

theorem catalog_positive (n r:ℕ):0 < (catalog n r).length:=by
  have hmem:=Lax263307Proofs.CoordinateCatalog.catalog_complete n r (⟨∅,by simp⟩:Coordinate n r)
  exact List.length_pos_of_mem hmem

end Lax263307Proofs.CoordinateCatalog

end

section

open scoped BigOperators

namespace Lax109476.LinearProgram

def IsBoundedAbove {m n:ℕ} (P:Program ℝ m n):Prop:=
  ∃ B:ℝ, ∀ x,PrimalFeasible P x→ primalValue P x≤ B

def IsPrimalOptimal {K:Type} [Ring K] [PartialOrder K] {m n:ℕ}
    (P:Program K m n) (x:Fin n→ K):Prop:=
  PrimalFeasible P x∧ ∀ z,PrimalFeasible P z→ primalValue P z≤ primalValue P x

end Lax109476.LinearProgram

end

section

open scoped BigOperators

namespace Lax109476Proofs.Basic

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem transpose_identity {m n:ℕ} (P:Program ℝ m n)
    (x:Fin n→ ℝ) (y:Fin m→ ℝ):
    (∑ j,columnValue P y j * x j)=∑ i,rowValue P x i * y i:=by
  simp only [columnValue,rowValue,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weak_duality:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x:Fin n→ ℝ) (y:Fin m→ ℝ),
      PrimalFeasible P x→ DualFeasible P y→ primalValue P x≤ dualValue P y:=by
  intro m n P x y hx hy
  calc
    primalValue P x≤ ∑ j,columnValue P y j * x j:=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hy.2 j) (hx.1 j)
    _=∑ i,rowValue P x i * y i:=transpose_identity P x y
    _≤ dualValue P y:=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)

theorem farkas_soundness:
    ∀ (m n:ℕ) (P:Program ℝ m n) (y:Fin m→ ℝ),
      IsInfeasibilityCertificate P y→ ¬ IsFeasible P:=by
  intro m n P y hy ⟨x,hx⟩
  have hnonneg:0≤ ∑ j,columnValue P y j * x j:=
    Finset.sum_nonneg fun j _ => mul_nonneg (hy.2.1 j) (hx.1 j)
  have hle:(∑ j,columnValue P y j * x j)≤ dualValue P y:=by
    rw [transpose_identity]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)
  exact (not_lt_of_ge (hnonneg.trans hle)) hy.2.2

end Lax109476Proofs.Basic

end

section

open scoped BigOperators

namespace Lax109476Proofs.Duality

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem row_scale {m n:ℕ} (P:Program ℝ m n) (d:Fin n→ ℝ)
    (t:ℝ) (i:Fin m):rowValue P (fun j => t * d j) i=t * rowValue P d i:=by
  simp only [rowValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem objective_scale {m n:ℕ} (P:Program ℝ m n) (d:Fin n→ ℝ)
    (t:ℝ):primalValue P (fun j => t * d j)=t * primalValue P d:=by
  simp only [primalValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem row_add {m n:ℕ} (P:Program ℝ m n) (x d:Fin n→ ℝ)
    (i:Fin m):rowValue P (fun j => x j + d j) i=rowValue P x i + rowValue P d i:=by
  simp [rowValue,mul_add,Finset.sum_add_distrib]

theorem objective_add {m n:ℕ} (P:Program ℝ m n) (x d:Fin n→ ℝ):
    primalValue P (fun j => x j + d j)=primalValue P x + primalValue P d:=by
  simp [primalValue,mul_add,Finset.sum_add_distrib]

end Lax109476Proofs.Duality

end

section

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def realVector {n:ℕ} (x:Fin n→ ℚ):Fin n→ ℝ:=fun j => x j

def IsCorrectOutcome {m n:ℕ} (P:Program ℚ m n):Certificate m n→ Prop
  | .optimal x _ => IsPrimalOptimal (toReal P) (realVector x)
  | .infeasible _ => ¬ IsFeasible (toReal P)
  | .unbounded _ _ => IsFeasible (toReal P)∧ ¬ IsBoundedAbove (toReal P)

end Lax109476.RationalCertificates

end

section

open scoped BigOperators

namespace Lax109476Proofs.Certificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RecessionDirection Lax109476.RationalCertificates
open Lax109476Proofs.Duality

theorem recession_soundness:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x d:Fin n→ ℝ),
      PrimalFeasible P x→ IsImprovingDirection P d→ ¬ IsBoundedAbove P:=by
  intro m n P x d hx hd ⟨B,hB⟩
  have hbase:=hB x hx
  have hpos:0 < primalValue P d:=hd.2.2
  let t:=(B - primalValue P x) / primalValue P d + 1
  have ht:0≤ t:=by
    dsimp [t]
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hbase) (le_of_lt hpos)) (by norm_num)
  let z:Fin n→ ℝ:=fun j => x j + t * d j
  have hz:PrimalFeasible P z:=by
    refine ⟨fun j => add_nonneg (hx.1 j) (mul_nonneg ht (hd.1 j)), ?_⟩
    intro i
    change rowValue P (fun j => x j + t * d j) i≤ P.b i
    rw [row_add,row_scale]
    have hdir:t * rowValue P d i≤ 0:=
      mul_nonpos_of_nonneg_of_nonpos ht (hd.2.1 i)
    linarith [hx.2 i]
  have hval:primalValue P z=B + primalValue P d:=by
    change primalValue P (fun j => x j + t * d j)=_
    rw [objective_add,objective_scale]
    dsimp [t]
    field_simp [ne_of_gt hpos]
    ring
  have hbound:=hB z hz
  rw [hval] at hbound
  linarith [hd.2.2]

private theorem cast_row {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ) (i:Fin m):
    rowValue (toReal P) (realVector x) i=(rowValue P x i:ℚ):=by
  simp [rowValue,toReal,realVector]

private theorem cast_column {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (j:Fin n):
    columnValue (toReal P) (realVector y) j=(columnValue P y j:ℚ):=by
  simp [columnValue,toReal,realVector]

private theorem cast_primal {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ):
    primalValue (toReal P) (realVector x)=(primalValue P x:ℚ):=by
  simp [primalValue,toReal,realVector]

private theorem cast_dual {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ):
    dualValue (toReal P) (realVector y)=(dualValue P y:ℚ):=by
  simp [dualValue,toReal,realVector]

private theorem cast_feasible {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ) (hx:PrimalFeasible P x):
    PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℚ)
    exact_mod_cast hx.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i:ℚ):ℝ)≤ (P.b i:ℚ)
    exact_mod_cast hx.2 i

private theorem cast_dual_feasible {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (hy:DualFeasible P y):
    DualFeasible (toReal P) (realVector y):=by
  constructor
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    change ((P.c j:ℚ):ℝ)≤ (columnValue P y j:ℚ)
    exact_mod_cast hy.2 j

private theorem cast_farkas {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (hy:IsInfeasibilityCertificate P y):
    IsInfeasibilityCertificate (toReal P) (realVector y):=by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    exact_mod_cast hy.2.1 j
  · rw [cast_dual]
    exact_mod_cast hy.2.2

private theorem cast_direction {m n:ℕ} (P:Program ℚ m n)
    (d:Fin n→ ℚ) (hd:IsImprovingDirection P d):
    IsImprovingDirection (toReal P) (realVector d):=by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change (0:ℝ)≤ (d j:ℚ)
    exact_mod_cast hd.1 j
  · intro i
    rw [cast_row]
    exact_mod_cast hd.2.1 i
  · rw [cast_primal]
    exact_mod_cast hd.2.2

theorem certificate_soundness:
    ∀ (m n:ℕ) (P:Program ℚ m n) (certificate:Certificate m n),
      IsValidCertificate P certificate→ IsCorrectOutcome P certificate:=by
  intro m n P certificate h
  cases certificate with
  | optimal x y =>
      rcases h with ⟨hx,hy,heq⟩
      have hxR:=cast_feasible P x hx
      have hyR:=cast_dual_feasible P y hy
      have heqR:primalValue (toReal P) (realVector x) =
          dualValue (toReal P) (realVector y):=by
        rw [cast_primal,cast_dual,heq]
      refine ⟨hxR, ?_⟩
      intro z hz
      rw [heqR]
      exact Lax109476Proofs.Basic.weak_duality m n (toReal P)
        z (realVector y) hz hyR
  | infeasible y =>
      exact Lax109476Proofs.Basic.farkas_soundness m n
        (toReal P) (realVector y) (cast_farkas P y h)
  | unbounded x d =>
      have hxR:=cast_feasible P x h.1
      exact ⟨⟨realVector x,hxR⟩,
        Lax109476Proofs.Certificates.recession_soundness m n (toReal P)
          (realVector x) (realVector d) hxR (cast_direction P d h.2)⟩

end Lax109476Proofs.Certificates

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

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

namespace Lax263307Proofs.AlgorithmParameters

open Lax263307.AlgorithmParameters

theorem sparsity_positive {a K B n D:ℕ} (hK:0 < K):0 < sparsity a K B n D:=by
  unfold sparsity targetThreshold
  positivity

theorem conditioning_floor (a K B n D:ℕ):
    (momentFloor a K B n D:ℝ) =
      Lax263307.HeavyConditioning.probabilityFloor n (sparsity a K B n D) ^ level a K B n D:=by
  unfold momentFloor
  push_cast
  simp only [floorDenominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    Lax263307.HeavyConditioning.probabilityFloor]
  rw [one_div_pow]

theorem protected_radius {a K B n D:ℕ} (hK:0 < K) (hn:0 < n) (hD:0 < D):
    2≤ precision a K B n D∧
      ((2:ℝ) ^ precision a K B n D)⁻¹≤
        (momentFloor a K B n D:ℝ) /
          (256 * (Lax263307.MomentLP.dimension n (level a K B n D):ℝ) * (n:ℝ) ^ 2 * (D:ℝ) ^ 2):=by
  have hp:=sparsity_positive (a:=a) (B:=B) (n:=n) (D:=D) hK
  have hN:0 < Lax263307.MomentLP.dimension n (level a K B n D):=
    Lax263307Proofs.CoordinateCatalog.catalog_positive n _
  have hQ:0 < floorDenominator a K B n D:=by unfold floorDenominator; positivity
  have hM:0 < radiusDenominator a K B n D:=by unfold radiusDenominator; positivity
  have hM':(0:ℝ) < radiusDenominator a K B n D:=by exact_mod_cast hM
  have hpow:radiusDenominator a K B n D≤ 2 ^ precision a K B n D:=by
    exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by unfold precision; omega))
  have hpow':(radiusDenominator a K B n D:ℝ)≤ (2:ℝ) ^ precision a K B n D:=by
    exact_mod_cast hpow
  refine ⟨by unfold precision; omega, ?_⟩
  have heq:(momentFloor a K B n D:ℝ) /
      (256 * (Lax263307.MomentLP.dimension n (level a K B n D):ℝ) * (n:ℝ) ^ 2 * (D:ℝ) ^ 2) =
      1 / (radiusDenominator a K B n D:ℝ):=by
    simp only [momentFloor,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
      radiusDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [heq]
  simpa only [one_div] using one_div_le_one_div_of_le hM' hpow'

end Lax263307Proofs.AlgorithmParameters

end

section

namespace Lax263307Proofs.MomentLP

open Lax263307.LinearRelaxation Lax263307.CoordinateCatalog Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem decode_encode {K:Type} {n r:ℕ} (y:Coordinate n r→ K):decode (encode y)=y:=by
  funext A
  simp [decode,encode]

theorem single_row_value {n r:ℕ} (x:Index n r→ ℝ) (A:Finset (Fin n)):
    (∑ j, (singleRow A j:ℝ) * x j)=value (decode x) A:=by
  by_cases hA:A.card≤ r + 2
  · let B:Coordinate n r:= ⟨A,hA⟩
    let i:Index n r:=(indexing n r).symm B
    have heq (j:Index n r):A=(indexing n r j).val↔ i=j:=by
      constructor
      · intro h
        apply (indexing n r).injective
        change indexing n r ((indexing n r).symm B)=indexing n r j
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
      · intro h
        rw [← h]
        simp [i,B]
    simp only [singleRow,apply_ite,Rat.cast_one,Rat.cast_zero,ite_mul,one_mul,zero_mul]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    simp [value,decode,hA,i,B]
  · have hne (j:Index n r):A ≠ (indexing n r j).val:=by
      intro h
      exact hA (h ▸ (indexing n r j).property)
    simp [singleRow,hne,value,hA]

theorem monotone_row_value {n r:ℕ} (x:Index n r→ ℝ) (A:Finset (Fin n)) (v:Fin n):
    (∑ j, (monotoneRow A v j:ℝ) * x j)=value (decode x) (insert v A) - value (decode x) A:=by
  simp only [monotoneRow,Rat.cast_sub,sub_mul,Finset.sum_sub_distrib]
  rw [Lax263307Proofs.MomentLP.single_row_value,Lax263307Proofs.MomentLP.single_row_value]

theorem mass_row_value {n r:ℕ} (x:Index n r→ ℝ) (A:Finset (Fin n)) (k:ℕ):
    (∑ j, (massRow A k j:ℝ) * x j) =
      (∑ v,value (decode x) (insert v A)) - (k:ℝ) * value (decode x) A:=by
  simp only [massRow,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,
    sub_mul,Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Lax263307Proofs.MomentLP.single_row_value]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,Lax263307Proofs.MomentLP.single_row_value]

abbrev Rows (n r:ℕ):=Fin (2 + (dimension n r + (dimension n r + (dimension n r * n + (dimension n r + dimension n r)))))

def normalPort {n r:ℕ} (i:Fin 2):Rows n r:=
  Fin.castAdd (dimension n r + (dimension n r + (dimension n r * n + (dimension n r + dimension n r)))) i

def upperPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.castAdd (dimension n r + (dimension n r * n + (dimension n r + dimension n r))) i)

def vanishPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.castAdd (dimension n r * n + (dimension n r + dimension n r)) i))

def monotonePort {n r:ℕ} (i:Index n r) (v:Fin n):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.castAdd (dimension n r + dimension n r) (finProdFinEquiv (i,v)))))

def massPlusPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.natAdd (dimension n r * n) (Fin.castAdd (dimension n r) i))))

def massMinusPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.natAdd (dimension n r * n) (Fin.natAdd (dimension n r) i))))

theorem indexed_value {n r:ℕ} (x:Index n r→ ℝ) (i:Index n r):
    value (decode x) (indexing n r i).val=x i:=by
  rw [value,dif_pos (indexing n r i).property]
  change x ((indexing n r).symm (indexing n r i))=x i
  rw [Equiv.symm_apply_apply]

theorem normal_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Fin 2):
    rowValue (toReal (program G k r)) x (normalPort i) =
      if i=0 then value (decode x) ∅ else -value (decode x) ∅:=by
  unfold rowValue toReal program normalPort
  simp only [Fin.addCases_left]
  by_cases hi:i=0
  · simp only [if_pos hi]
    exact Lax263307Proofs.MomentLP.single_row_value x ∅
  · simp only [if_neg hi,Rat.cast_neg,neg_mul,Finset.sum_neg_distrib]
    rw [Lax263307Proofs.MomentLP.single_row_value]

theorem upper_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (upperPort i)=x i:=by
  unfold rowValue toReal program upperPort
  simp only [Fin.addCases_left,Fin.addCases_right]
  rw [Lax263307Proofs.MomentLP.single_row_value,indexed_value]

theorem vanish_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (vanishPort i) =
      if G.IsIndepSet ((indexing n r i).val:Set (Fin n)) then 0 else x i:=by
  unfold rowValue toReal program vanishPort
  simp only [Fin.addCases_left,Fin.addCases_right]
  split_ifs
  · simp
  · rw [Lax263307Proofs.MomentLP.single_row_value,indexed_value]

theorem monotone_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r) (v:Fin n):
    rowValue (toReal (program G k r)) x (monotonePort i v) =
      if (indexing n r i).val.card≤ r + 1 then
        value (decode x) (insert v (indexing n r i).val) - value (decode x) (indexing n r i).val else 0:=by
  unfold rowValue toReal program monotonePort
  simp only [Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply]
  split_ifs
  · exact monotone_row_value x _ v
  · simp

theorem mass_plus_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (massPlusPort i) =
      if (indexing n r i).val.card≤ r + 1 then
        (∑ v,value (decode x) (insert v (indexing n r i).val)) - (k:ℝ) * value (decode x) (indexing n r i).val else 0:=by
  unfold rowValue toReal program massPlusPort
  simp only [Fin.addCases_left,Fin.addCases_right]
  split_ifs
  · exact mass_row_value x _ k
  · simp

theorem mass_minus_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (massMinusPort i) =
      if (indexing n r i).val.card≤ r + 1 then
        -((∑ v,value (decode x) (insert v (indexing n r i).val)) - (k:ℝ) * value (decode x) (indexing n r i).val) else 0:=by
  unfold rowValue toReal program massMinusPort
  simp only [Fin.addCases_right]
  split_ifs
  · simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib]
    rw [mass_row_value]
  · simp

theorem normal_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Fin 2):
    (toReal (program G k r)).b (normalPort i)=if i=0 then 1 else -1:=by
  by_cases hi:i=0 <;> simp [toReal,program,normalPort,hi]

theorem upper_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (upperPort i)=1:=by
  simp only [toReal,program,upperPort,Fin.addCases_left,Fin.addCases_right,Rat.cast_one]

theorem vanish_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (vanishPort i)=0:=by
  simp only [toReal,program,vanishPort,Fin.addCases_right,Rat.cast_zero]

theorem monotone_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r) (v:Fin n):
    (toReal (program G k r)).b (monotonePort i v)=0:=by
  simp only [toReal,program,monotonePort,Fin.addCases_right,Rat.cast_zero]

theorem mass_plus_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (massPlusPort i)=0:=by
  simp only [toReal,program,massPlusPort,Fin.addCases_right,Rat.cast_zero]

theorem mass_minus_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (massMinusPort i)=0:=by
  simp only [toReal,program,massMinusPort,Fin.addCases_right,Rat.cast_zero]

theorem primal_characterization {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ):
    PrimalFeasible (toReal (program G k r)) x↔ Lax263307.LinearRelaxation.IsFeasible G k r (decode x):=by
  constructor
  · rintro ⟨hnonnegative,hrows⟩
    have hupper (i:Index n r):x i≤ 1:=by
      have h:=hrows (upperPort i)
      rwa [upper_row,upper_rhs] at h
    exact {
      normalized:=by
        have h0:=hrows (normalPort (0:Fin 2))
        have h1:=hrows (normalPort (1:Fin 2))
        rw [normal_row,normal_rhs] at h0 h1
        norm_num at h0 h1
        linarith
      bounds:=fun A => ⟨hnonnegative ((indexing n r).symm A),hupper ((indexing n r).symm A)⟩
      monotone:=by
        intro A hA v
        let B:Coordinate n r:= ⟨A,by omega⟩
        let i:Index n r:=(indexing n r).symm B
        have hi:(indexing n r i).val=A:=by simp [i,B]
        have h:=hrows (monotonePort i v)
        rw [monotone_row,monotone_rhs,hi,if_pos hA] at h
        exact sub_nonpos.mp h
      vanishes:=by
        intro A hA
        let i:Index n r:=(indexing n r).symm A
        have hi:indexing n r i=A:=Equiv.apply_symm_apply _ _
        have h:=hrows (vanishPort i)
        rw [vanish_row,vanish_rhs,hi,if_neg hA] at h
        exact le_antisymm h (hnonnegative i)
      mass:=by
        intro A hA
        let B:Coordinate n r:= ⟨A,by omega⟩
        let i:Index n r:=(indexing n r).symm B
        have hi:(indexing n r i).val=A:=by simp [i,B]
        have hp:=hrows (massPlusPort i)
        have hm:=hrows (massMinusPort i)
        rw [mass_plus_row,mass_plus_rhs,hi,if_pos hA] at hp
        rw [mass_minus_row,mass_minus_rhs,hi,if_pos hA] at hm
        linarith }
  · intro feasible
    refine ⟨?_, ?_⟩
    · intro i
      simpa [decode] using (feasible.bounds (indexing n r i)).1
    · intro row
      refine Fin.addCases (fun i:Fin 2 => ?_) (fun row => ?_) row
      · change rowValue (toReal (program G k r)) x (normalPort i)≤ (toReal (program G k r)).b (normalPort i)
        rw [normal_row,normal_rhs,feasible.normalized]
      · refine Fin.addCases (fun i:Index n r => ?_) (fun row => ?_) row
        · change rowValue (toReal (program G k r)) x (upperPort i)≤ (toReal (program G k r)).b (upperPort i)
          rw [upper_row,upper_rhs]
          simpa [decode] using (feasible.bounds (indexing n r i)).2
        · refine Fin.addCases (fun i:Index n r => ?_) (fun row => ?_) row
          · change rowValue (toReal (program G k r)) x (vanishPort i)≤ (toReal (program G k r)).b (vanishPort i)
            rw [vanish_row,vanish_rhs]
            by_cases hI:G.IsIndepSet ((indexing n r i).val:Set (Fin n))
            · simp [hI]
            · have hzero:x i=0:=by simpa [decode] using feasible.vanishes (indexing n r i) hI
              simp [hI,hzero]
          · refine Fin.addCases (fun j:Fin (dimension n r * n) => ?_) (fun row => ?_) row
            · obtain ⟨⟨i,v⟩,rfl⟩:=(finProdFinEquiv:Index n r × Fin n ≃ Fin (dimension n r * n)).surjective j
              change rowValue (toReal (program G k r)) x (monotonePort i v)≤ (toReal (program G k r)).b (monotonePort i v)
              rw [monotone_row,monotone_rhs]
              by_cases hi:(indexing n r i).val.card≤ r + 1
              · rw [if_pos hi]
                exact sub_nonpos.mpr (feasible.monotone _ hi v)
              · simp [hi]
            · refine Fin.addCases (fun i:Index n r => ?_) (fun i:Index n r => ?_) row
              · change rowValue (toReal (program G k r)) x (massPlusPort i)≤ (toReal (program G k r)).b (massPlusPort i)
                rw [mass_plus_row,mass_plus_rhs]
                by_cases hi:(indexing n r i).val.card≤ r + 1
                · rw [if_pos hi,feasible.mass _ hi]
                  simp
                · simp [hi]
              · change rowValue (toReal (program G k r)) x (massMinusPort i)≤ (toReal (program G k r)).b (massMinusPort i)
                rw [mass_minus_row,mass_minus_rhs]
                by_cases hi:(indexing n r i).val.card≤ r + 1
                · rw [if_pos hi,feasible.mass _ hi]
                  simp
                · simp [hi]

theorem evaluate_encoding {n r:ℕ} (a:Coordinate n r→ ℤ) (x:Index n r→ ℝ):
    Lax263307.ComponentCutEncoding.evaluate a (decode x) =
      (fun j => ((encode a j:ℤ):ℝ)) ⬝ᵥ x:=by
  classical
  unfold Lax263307.ComponentCutEncoding.evaluate dotProduct
  have h:=(indexing n r).sum_comp (fun A => (a A:ℝ) * decode x A)
  simpa only [decode,encode,Equiv.symm_apply_apply] using h.symm

end Lax263307Proofs.MomentLP

end

section

namespace Lax263307Proofs.DistanceProjection

open Lax109476.LinearProgram Lax263307.DistanceProjection

theorem old_row {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (i:Fin m):
    rowValue (distanceProgram P center) z (Fin.castAdd (n + n) i)=rowValue P (point z) i:=by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_left]
  rw [Fin.sum_univ_add]
  simp [point]

theorem plus_row {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (i:Fin n):
    rowValue (distanceProgram P center) z (Fin.natAdd m (Fin.castAdd n i))=point z i - distance z:=by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_left,Fin.addCases_right]
  rw [Fin.sum_univ_add]
  simp [point,distance,sub_eq_add_neg]

theorem minus_row {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (i:Fin n):
    rowValue (distanceProgram P center) z (Fin.natAdd m (Fin.natAdd n i))=-point z i - distance z:=by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_right]
  rw [Fin.sum_univ_add]
  simp [point,distance,sub_eq_add_neg]

theorem primal_characterization {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ):
    PrimalFeasible (distanceProgram P center) z↔
      PrimalFeasible P (point z)∧ 0≤ distance z∧
        ∀ j, |point z j - center j|≤ distance z:=by
  constructor
  · rintro ⟨hnonneg,hrows⟩
    refine ⟨⟨fun j => hnonneg (Fin.castAdd 1 j),fun i => ?_⟩,
      hnonneg (Fin.natAdd n (0:Fin 1)),fun j => ?_⟩
    · have h:=hrows (Fin.castAdd (n + n) i)
      rw [old_row] at h
      simpa only [distanceProgram,Fin.addCases_left] using h
    · have hplus:=hrows (Fin.natAdd m (Fin.castAdd n j))
      have hminus:=hrows (Fin.natAdd m (Fin.natAdd n j))
      rw [plus_row] at hplus
      rw [minus_row] at hminus
      simp only [distanceProgram,Fin.addCases_left,Fin.addCases_right] at hplus hminus
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rintro ⟨⟨hnonneg,hrows⟩,ht,hnear⟩
    constructor
    · intro j
      refine Fin.addCases (fun j => hnonneg j) (fun j => ?_) j
      have hj:j=0:=Fin.eq_zero j
      subst j
      exact ht
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [old_row]
        simpa only [distanceProgram,Fin.addCases_left] using hrows i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [plus_row]
          simp only [distanceProgram,Fin.addCases_left,Fin.addCases_right]
          have h:=(abs_le.mp (hnear j)).2
          linarith
        · rw [minus_row]
          simp only [distanceProgram,Fin.addCases_right]
          have h:=(abs_le.mp (hnear j)).1
          linarith

theorem objective_value {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ):
    primalValue (distanceProgram P center) z=-distance z:=by
  unfold primalValue distanceProgram
  rw [Fin.sum_univ_add]
  simp [distance]

theorem objective_bounded {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ):
    IsBoundedAbove (distanceProgram P center):=by
  refine ⟨0,fun z hz => ?_⟩
  rw [objective_value]
  exact neg_nonpos.mpr ((primal_characterization P center z).mp hz).2.1

theorem projection_feasible_iff {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ):
    IsFeasible (distanceProgram P center)↔ IsFeasible P:=by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨point z, ((primal_characterization P center z).mp hz).1⟩
  · rintro ⟨y,hy⟩
    let t:= ∑ j, |y j - center j|
    let z:Fin (n + 1)→ ℝ:=Fin.addCases y (fun _:Fin 1 => t)
    refine ⟨z, (primal_characterization P center z).mpr ?_⟩
    have hpoint:point z=y:=by funext j; simp [point,z]
    have hdist:distance z=t:=by simp [distance,z]
    rw [hpoint,hdist]
    refine ⟨hy,Finset.sum_nonneg (fun j _ => abs_nonneg _), ?_⟩
    intro j
    exact Finset.single_le_sum (fun j _ => abs_nonneg (y j - center j)) (Finset.mem_univ j)

theorem point_column {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ) (j:Fin n):
    columnValue (distanceProgram P center) dual (Fin.castAdd 1 j) =
      columnValue P (oldMultipliers dual) j - normal dual j:=by
  unfold columnValue distanceProgram
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  simp [oldMultipliers,plusMultipliers,minusMultipliers,normal]
  ring

theorem distance_column {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ):
    columnValue (distanceProgram P center) dual (Fin.natAdd n (0:Fin 1)) =
      -(∑ j,plusMultipliers dual j) - ∑ j,minusMultipliers dual j:=by
  unfold columnValue distanceProgram
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  simp [plusMultipliers,minusMultipliers,Finset.sum_neg_distrib]
  ring

theorem dual_objective {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ):
    dualValue (distanceProgram P center) dual=dualValue P (oldMultipliers dual) - ∑ j,normal dual j * center j:=by
  unfold dualValue distanceProgram
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,neg_mul,Finset.sum_neg_distrib]
  simp only [oldMultipliers,normal,minusMultipliers,plusMultipliers,sub_mul,Finset.sum_sub_distrib]
  have hcomm:(∑ j,center j * dual (Fin.natAdd m (Fin.castAdd n j))) =
      ∑ j,dual (Fin.natAdd m (Fin.castAdd n j)) * center j:=by apply Finset.sum_congr rfl; intro j _; ring
  have hcomm':(∑ j,center j * dual (Fin.natAdd m (Fin.natAdd n j))) =
      ∑ j,dual (Fin.natAdd m (Fin.natAdd n j)) * center j:=by apply Finset.sum_congr rfl; intro j _; ring
  rw [hcomm,hcomm']
  ring

theorem dual_normal {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ) (feasible:DualFeasible (distanceProgram P center) dual):
    (∑ j, |normal dual j|)≤ 1∧
      ∀ z,PrimalFeasible P z→ (∑ j,normal dual j * z j)≤ dualValue P (oldMultipliers dual):=by
  have hplus (j:Fin n):0≤ plusMultipliers dual j:=feasible.1 _
  have hminus (j:Fin n):0≤ minusMultipliers dual j:=feasible.1 _
  have hmass:(∑ j,plusMultipliers dual j) + (∑ j,minusMultipliers dual j)≤ 1:=by
    have h:=feasible.2 (Fin.natAdd n (0:Fin 1))
    rw [distance_column] at h
    simp only [distanceProgram,Fin.addCases_right] at h
    linarith
  constructor
  · have h:=Finset.sum_le_sum (fun j (_:j∈ (Finset.univ:Finset (Fin n))) =>
      show |normal dual j|≤ plusMultipliers dual j + minusMultipliers dual j from by
        unfold normal
        exact abs_le.mpr ⟨by linarith [hplus j,hminus j],by linarith [hplus j,hminus j]⟩)
    rw [Finset.sum_add_distrib] at h
    exact h.trans hmass
  · intro z hz
    have hcol (j:Fin n):normal dual j≤ columnValue P (oldMultipliers dual) j:=by
      have h:=feasible.2 (Fin.castAdd 1 j)
      rw [point_column] at h
      simp only [distanceProgram,Fin.addCases_left] at h
      linarith
    calc
      _≤ ∑ j,columnValue P (oldMultipliers dual) j * z j:=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hz.1 j))
      _=∑ i,oldMultipliers dual i * rowValue P z i:=by
        unfold columnValue rowValue
        simp_rw [Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _≤ dualValue P (oldMultipliers dual):=
        Finset.sum_le_sum (fun i _ => by
          have hnonnegative:0≤ oldMultipliers dual i:=feasible.1 _
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz.2 i) hnonnegative)

theorem optimal_gap {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (dual:Fin (m + (n + n))→ ℝ)
    (primal:PrimalFeasible (distanceProgram P center) z)
    (dual_feasible:DualFeasible (distanceProgram P center) dual)
    (matching:primalValue (distanceProgram P center) z=dualValue (distanceProgram P center) dual):
    PrimalFeasible P (point z)∧ 0≤ distance z∧
      (∀ j, |point z j - center j|≤ distance z)∧
      (∑ j, |normal dual j|)≤ 1∧
      (∀ y,PrimalFeasible P y→ (∑ j,normal dual j * y j)≤ dualValue P (oldMultipliers dual))∧
      (∑ j,normal dual j * center j) - dualValue P (oldMultipliers dual)=distance z:=by
  obtain ⟨hpoint,hdist,hnear⟩:=(primal_characterization P center z).mp primal
  obtain ⟨hl1,hvalid⟩:=Lax263307Proofs.DistanceProjection.dual_normal P center dual dual_feasible
  refine ⟨hpoint,hdist,hnear,hl1,hvalid, ?_⟩
  rw [objective_value,dual_objective] at matching
  linarith

end Lax263307Proofs.DistanceProjection

end

section

namespace Lax263307Proofs.RationalCutBuffer

open Matrix Lax263307.RationalCutBuffer

theorem denominator_positive {n:ℕ} (a:Fin n→ ℚ):0 < denominator a:=by
  exact Finset.prod_pos (fun i _ => (a i).den_pos)

theorem integer_normal_cast {n:ℕ} (a:Fin n→ ℚ) (i:Fin n):
    (integerNormal a i:ℝ)=(denominator a:ℝ) * (a i:ℝ):=by
  have hdvd:(a i).den ∣ denominator a:=
    Finset.dvd_prod_of_mem (fun i => (a i).den) (Finset.mem_univ i)
  have hdiv:(denominator a:ℚ) =
      (denominator a / (a i).den:ℕ) * ((a i).den:ℚ):=by
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have h:(integerNormal a i:ℚ)=(denominator a:ℚ) * a i:=by
    rw [integerNormal,Int.cast_mul,Int.cast_natCast]
    conv_rhs => rw [← (a i).num_div_den,hdiv]
    have hd:((a i).den:ℚ) ≠ 0:=by exact_mod_cast (a i).den_ne_zero
    field_simp
  exact_mod_cast h

theorem normal_nonzero {n:ℕ} (a:Fin n→ ℚ) (x z:Fin n→ ℝ)
    (gap:(fun i => (a i:ℝ)) ⬝ᵥ z < (fun i => (a i:ℝ)) ⬝ᵥ x):
    ∃ i,integerNormal a i ≠ 0:=by
  by_contra! hzero
  have hD:(0:ℝ) < denominator a:=by exact_mod_cast Lax263307Proofs.RationalCutBuffer.denominator_positive a
  have ha (i:Fin n):(a i:ℝ)=0:=by
    have h:=Lax263307Proofs.RationalCutBuffer.integer_normal_cast a i
    rw [hzero i,Int.cast_zero] at h
    nlinarith
  simp only [dotProduct,ha,zero_mul,Finset.sum_const_zero] at gap
  exact lt_irrefl _ gap

theorem dot_stable {n:ℕ} (a x y:Fin n→ ℝ) (ρ L:ℝ)
    (nonnegative:0≤ ρ) (norm:(∑ i, |a i|)≤ L)
    (near:∀ i, |x i - y i|≤ ρ):|a ⬝ᵥ x - a ⬝ᵥ y|≤ L * ρ:=by
  unfold dotProduct
  rw [← Finset.sum_sub_distrib]
  calc
    _≤ ∑ i, |a i * x i - a i * y i|:=Finset.abs_sum_le_sum_abs _ _
    _≤ ∑ i, |a i| * ρ:=by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (near i) (abs_nonneg _)
    _≤ _:=by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right norm nonnegative

theorem central_buffer {n:ℕ} (a x z perturbed:Fin n→ ℝ) (α Δ ρ L:ℝ)
    (nonnegative:0≤ ρ) (norm:(∑ i, |a i|)≤ L)
    (valid:a ⬝ᵥ z≤ α) (gap:α + Δ≤ a ⬝ᵥ x)
    (small:L * ρ≤ Δ / 2) (near:∀ i, |perturbed i - z i|≤ ρ):
    a ⬝ᵥ perturbed≤ a ⬝ᵥ x - Δ / 2:=by
  have h:=(abs_le.mp (Lax263307Proofs.RationalCutBuffer.dot_stable a perturbed z ρ L nonnegative norm near)).2
  linarith

theorem scaled_cleared_cut {n:ℕ} (positive:0 < n) (a:Fin n→ ℚ)
    (query z:Fin n→ ℝ) (α Δ ρ L:ℝ)
    (nonnegative:0≤ ρ) (norm:(∑ i, |(a i:ℝ)|)≤ L)
    (valid:(fun i => (a i:ℝ)) ⬝ᵥ z≤ α)
    (gap:α + Δ≤ (fun i => (a i:ℝ)) ⬝ᵥ (fun i => 4 * (n:ℝ) * query i))
    (small:L * ρ≤ Δ / 2) (e:Fin n→ ℝ)
    (near:∀ i, |e i|≤ ρ / (4 * n)):
    (fun i => (integerNormal a i:ℝ)) ⬝ᵥ
      (Lax263307.BufferedEllipsoid.scale z + e - query)≤ 0:=by
  have hn:(0:ℝ) < n:=by exact_mod_cast positive
  let perturbed (i:Fin n):=4 * (n:ℝ) * (Lax263307.BufferedEllipsoid.scale z i + e i)
  have hnear (i:Fin n):|perturbed i - z i|≤ ρ:=by
    have heq:perturbed i - z i=4 * (n:ℝ) * e i:=by
      dsimp [perturbed,Lax263307.BufferedEllipsoid.scale]
      field_simp
      ring
    rw [heq,abs_mul,abs_of_pos (by positivity:0 < 4 * (n:ℝ))]
    have h:=mul_le_mul_of_nonneg_left (near i) (by positivity:0≤ 4 * (n:ℝ))
    have hc:4 * (n:ℝ) * (ρ / (4 * n))=ρ:=by field_simp
    exact h.trans_eq hc
  have hcut:=Lax263307Proofs.RationalCutBuffer.central_buffer (fun i => (a i:ℝ))
    (fun i => 4 * (n:ℝ) * query i) z perturbed α Δ ρ L nonnegative norm valid gap small hnear
  have hΔ:0≤ Δ:=by
    have hL:0≤ L:=(Finset.sum_nonneg (fun i _ => abs_nonneg (a i:ℝ))).trans norm
    nlinarith [mul_nonneg hL nonnegative]
  have hc:(fun i => (a i:ℝ)) ⬝ᵥ
      (Lax263307.BufferedEllipsoid.scale z + e - query)≤ 0:=by
    have heq:(fun i => (a i:ℝ)) ⬝ᵥ perturbed -
        (fun i => (a i:ℝ)) ⬝ᵥ (fun i => 4 * (n:ℝ) * query i) =
        4 * (n:ℝ) * ((fun i => (a i:ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale z + e - query)):=by
      simp only [dotProduct,perturbed,Pi.add_apply,Pi.sub_apply]
      rw [← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h:4 * (n:ℝ) * ((fun i => (a i:ℝ)) ⬝ᵥ
        (Lax263307.BufferedEllipsoid.scale z + e - query))≤ 0:=by
      rw [← heq]
      linarith
    exact nonpos_of_mul_nonpos_right h (by positivity)
  have hD:(0:ℝ)≤ denominator a:=Nat.cast_nonneg _
  simp_rw [Lax263307Proofs.RationalCutBuffer.integer_normal_cast]
  unfold dotProduct at hc ⊢
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_nonpos_of_nonneg_of_nonpos hD hc

end Lax263307Proofs.RationalCutBuffer

end

section

namespace Lax263307Proofs.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax263307.DistanceProjection

theorem cast_row {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (i:Fin m):
    rowValue (toReal P) (realVector x) i=((rowValue P x i:ℚ):ℝ):=by
  unfold rowValue toReal realVector
  push_cast
  rfl

theorem cast_column {m n:ℕ} (P:Program ℚ m n) (x:Fin m→ ℚ) (j:Fin n):
    columnValue (toReal P) (realVector x) j=((columnValue P x j:ℚ):ℝ):=by
  unfold columnValue toReal realVector
  push_cast
  rfl

theorem cast_primal_value {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ):
    primalValue (toReal P) (realVector x)=((primalValue P x:ℚ):ℝ):=by
  unfold primalValue toReal realVector
  push_cast
  rfl

theorem cast_dual_value {m n:ℕ} (P:Program ℚ m n) (x:Fin m→ ℚ):
    dualValue (toReal P) (realVector x)=((dualValue P x:ℚ):ℝ):=by
  unfold dualValue toReal realVector
  push_cast
  rfl

theorem primal_transfer {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (feasible:PrimalFeasible P x):
    PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℝ)
    exact_mod_cast feasible.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i:ℚ):ℝ)≤ (P.b i:ℝ)
    exact_mod_cast feasible.2 i

theorem dual_transfer {m n:ℕ} (P:Program ℚ m n) (x:Fin m→ ℚ) (feasible:DualFeasible P x):
    DualFeasible (toReal P) (realVector x):=by
  constructor
  · intro i
    change (0:ℝ)≤ (x i:ℝ)
    exact_mod_cast feasible.1 i
  · intro j
    rw [cast_column]
    change (P.c j:ℝ)≤ ((columnValue P x j:ℚ):ℝ)
    exact_mod_cast feasible.2 j

theorem distance_cast {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ):
    toReal (distanceProgram P center)=distanceProgram (toReal P) (realVector center):=by
  unfold toReal distanceProgram
  congr 1
  · funext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]
      · simp
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> first | rfl | simp [apply_ite]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> first | rfl | simp [apply_ite]
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> (simp only [Fin.addCases_left,Fin.addCases_right]; simp [realVector])
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> norm_num

theorem normal_cast {m n:ℕ} (dual:Fin (m + (n + n))→ ℚ):
    normal (realVector dual)=fun j => ((normal dual j:ℚ):ℝ):=by
  funext j
  simp [normal,plusMultipliers,minusMultipliers,realVector]

theorem classify_correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ)
    (certificate:Certificate (m + (n + n)) (n + 1))
    (valid:IsValidCertificate (distanceProgram P center) certificate):
    Lax263307.RationalProjection.Correct P center ρ
      (Lax263307.RationalProjection.classify P ρ certificate):=by
  cases certificate with
  | optimal z dual =>
    obtain ⟨primal,dual_feasible,matching⟩:=valid
    have hp:=primal_transfer (distanceProgram P center) z primal
    have hd:=dual_transfer (distanceProgram P center) dual dual_feasible
    rw [distance_cast] at hp hd
    have hm:primalValue (distanceProgram (toReal P) (realVector center)) (realVector z) =
        dualValue (distanceProgram (toReal P) (realVector center)) (realVector dual):=by
      rw [← distance_cast,cast_primal_value,cast_dual_value,matching]
    have hg:=Lax263307Proofs.DistanceProjection.optimal_gap
      (toReal P) (realVector center) (realVector z) (realVector dual) hp hd hm
    have hdistance:distance (realVector z)=((distance z:ℚ):ℝ):=rfl
    have hpoint:point (realVector z)=realVector (point z):=rfl
    have hold:oldMultipliers (realVector dual)=realVector (oldMultipliers dual):=rfl
    simp only [Lax263307.RationalProjection.classify]
    split_ifs with hnear
    · change PrimalFeasible (toReal P) (realVector (point z))∧ _
      refine ⟨by simpa only [hpoint] using hg.1, ?_⟩
      intro j
      have hdist:((distance z:ℚ):ℝ)≤ (ρ:ℝ):=by exact_mod_cast hnear
      exact (hg.2.2.1 j).trans hdist
    · change (∑ j, |((normal dual j:ℚ):ℝ)|)≤ 1∧ _
      have hfar:(ρ:ℝ) < ((distance z:ℚ):ℝ):=by
        exact_mod_cast (lt_of_not_ge hnear)
      have hgap:=hg.2.2.2.2.2
      rw [normal_cast,hold,cast_dual_value,hdistance] at hgap
      refine ⟨?_, ?_, ?_⟩
      · simpa only [normal_cast] using hg.2.2.2.1
      · simpa only [normal_cast,hold,cast_dual_value] using hg.2.2.2.2.1
      · simpa only [← hgap,realVector] using hfar
  | infeasible dual =>
    have hbad:=Lax109476Proofs.Certificates.certificate_soundness _ _
      (distanceProgram P center) (.infeasible dual) valid
    change ¬ IsFeasible (toReal (distanceProgram P center)) at hbad
    rw [distance_cast,Lax263307Proofs.DistanceProjection.projection_feasible_iff] at hbad
    exact hbad
  | unbounded z direction =>
    have hbad:=Lax109476Proofs.Certificates.certificate_soundness _ _
      (distanceProgram P center) (.unbounded z direction) valid
    change IsFeasible (toReal (distanceProgram P center))∧
      ¬ IsBoundedAbove (toReal (distanceProgram P center)) at hbad
    rw [distance_cast] at hbad
    exact False.elim (hbad.2 (Lax263307Proofs.DistanceProjection.objective_bounded
      (toReal P) (realVector center)))

end Lax263307Proofs.RationalProjection

end

section

namespace Lax263307Proofs.RelaxationFeasibility

open Lax263307.LinearRelaxation RelaxationAlgebra

theorem indicator_feasible {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (I:Finset (Fin n)) (independent:G.IsIndepSet (I:Set (Fin n)))
    (cardinality:I.card=k):IsFeasible G k r (indicator r I):=by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [value,indicator]
  · intro A
    dsimp [indicator]
    split_ifs <;> norm_num
  · intro A hA v
    rw [indicator_value I _ (insert_size A hA v),
      indicator_value I A (by omega)]
    by_cases hAI:A ⊆ I
    · simp only [if_pos hAI]
      split_ifs <;> norm_num
    · have hnot:¬insert v A ⊆ I:=fun h => hAI ((Finset.subset_insert v A).trans h)
      simp [hAI,hnot]
  · intro A hA
    have hnot:¬A.val ⊆ I:=fun h => hA (independent_subset G independent h)
    simp [indicator,hnot]
  · intro A hA
    rw [indicator_sum I A Finset.univ hA,indicator_value I A (by omega)]
    simp [cardinality]

theorem feasible_convex {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ):
    Convex ℝ {y:MomentVector n r | IsFeasible G k r y}:=by
  intro y hy z hz a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [value_combination,hy.normalized,hz.normalized]
    simpa using hab
  · intro A
    change 0≤ a * y A + b * z A∧ a * y A + b * z A≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hy.bounds A).1) (mul_nonneg hb (hz.bounds A).1)
    · calc
        a * y A + b * z A≤ a * 1 + b * 1:=
          add_le_add (mul_le_mul_of_nonneg_left (hy.bounds A).2 ha)
            (mul_le_mul_of_nonneg_left (hz.bounds A).2 hb)
        _=1:=by simpa using hab
  · intro A hA v
    rw [value_combination,value_combination]
    exact add_le_add (mul_le_mul_of_nonneg_left (hy.monotone A hA v) ha)
      (mul_le_mul_of_nonneg_left (hz.monotone A hA v) hb)
  · intro A hA
    change a * y A + b * z A=0
    simp [hy.vanishes A hA,hz.vanishes A hA]
  · intro A hA
    simp_rw [value_combination,Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hy.mass A hA,hz.mass A hA]
    ring

theorem hull_feasible {n:ℕ} (G:SimpleGraph (Fin n)) (k r:ℕ)
    (y:MomentVector n r) (member:y∈ independentSetHull G k r):
    IsFeasible G k r y:=by
  apply convexHull_min (t:= {y | IsFeasible G k r y}) ?_ (feasible_convex G k r) member
  rintro z ⟨I,hI,hk,rfl⟩
  exact Lax263307Proofs.RelaxationFeasibility.indicator_feasible G k r I hI hk

end Lax263307Proofs.RelaxationFeasibility

end

section

namespace Lax263307Proofs.ProjectedOracle

open Matrix
open Lax263307.ProjectedOracle Lax263307.AlgorithmParameters
open Lax263307.LinearRelaxation Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem far_feasible {m N:ℕ} (P:Program ℚ m N) (x:Fin N→ ℚ) (ρ:ℚ)
    (cert:Certificate (m+(N+N)) (N+1))
    (valid:IsValidCertificate (Lax263307.DistanceProjection.distanceProgram P x) cert)
    (normal:Fin N→ ℚ) (α:ℚ)
    (far:Lax263307.RationalProjection.classify P ρ cert=.far normal α):
    Lax109476.LinearProgram.IsFeasible (toReal P):=by
  cases cert with
  | infeasible dual => simp [Lax263307.RationalProjection.classify] at far
  | unbounded z direction => simp [Lax263307.RationalProjection.classify] at far
  | optimal z dual =>
    have hp:=Lax263307Proofs.RationalProjection.primal_transfer _ z valid.1
    rw [Lax263307Proofs.RationalProjection.distance_cast] at hp
    exact ⟨Lax263307.DistanceProjection.point (Lax109476.RationalCertificates.realVector z),
      (Lax263307Proofs.DistanceProjection.primal_characterization _ _ _).mp hp |>.1⟩

theorem cast_raw {N:ℕ} (c:Fin N→ ℚ):
    Lax109476.RationalCertificates.realVector (raw c)=fun i => 4 * (N:ℝ) * (c i:ℝ):=by
  funext i
  simp [raw,Lax109476.RationalCertificates.realVector]

theorem tolerance_cast (a K B n D:ℕ):
    (tolerance a K B n D:ℝ)=(momentFloor a K B n D:ℝ) *
      (1 / (D:ℝ)) ^ 2 / (32 * (n:ℝ)^2):=by
  simp only [tolerance,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]
  ring

theorem cut_dot {n r:ℕ} (b:Coordinate n r→ ℤ) (x:Index n r→ ℝ):
    (fun i => ((Lax263307.RoundedOracleSearch.rationalNormal (encode b) i:ℚ):ℝ)) ⬝ᵥ x =
      Lax263307.ComponentCutEncoding.evaluate b (decode x):=by
  rw [Lax263307Proofs.MomentLP.evaluate_encoding]
  congr 1

theorem cut_norm {n r:ℕ} (b:Coordinate n r→ ℤ):
    (∑ i:Index n r, |((Lax263307.RoundedOracleSearch.rationalNormal (encode b) i:ℚ):ℝ)|) =
      ∑ T, |(b T:ℝ)|:=by
  simp only [Lax263307.RoundedOracleSearch.rationalNormal,Rat.cast_intCast,encode]
  exact Equiv.sum_comp (Lax263307.CoordinateCatalog.indexing n r) (fun T => |(b T:ℝ)|)

theorem run_correct {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K B D:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k h:ℕ)
    (hK:0 < K) (hn:0 < n) (hD:4≤ D)
    (lp_valid:∀ (m N:ℕ) (P:Program ℚ m N),IsValidCertificate P (Lax263307.RegisteredLP.certificate lp P))
    (child:Finset (Fin n)→ ℕ→ Option (Finset (Fin n)))
    (near_correct:∀ y:Lax263307.RationalConditioning.RationalVector n (level a K B n D),
      Lax263307.LinearRelaxation.IsFeasible G k (level a K B n D) (Lax263307.RationalConditioning.realVector y)→
      ∀ x:MomentVector n (level a K B n D),
      (∀ T, |x T - Lax263307.RationalConditioning.realVector y T|≤ (momentFloor a K B n D:ℝ) *
        (1 / (D:ℝ))^2 / (32 * (n:ℝ)^2))→
      Lax263307.NearOracle.Correct G k h D (momentFloor a K B n D) x
        (Lax263307.NearOracle.run flow a K B D G k y child))
    (center:Index n (level a K B n D)→ ℚ):
    Correct G k h a K B D center (run lp flow a K B D G k child center):=by
  let r:=level a K B n D
  let N:=dimension n r
  let P:=program G k r
  let q:=raw center
  let ρ:=tolerance a K B n D
  let η:ℝ:=momentFloor a K B n D
  let cert:=Lax263307.RegisteredLP.certificate lp (Lax263307.DistanceProjection.distanceProgram P q)
  have hv:=lp_valid _ _ (Lax263307.DistanceProjection.distanceProgram P q)
  have hc:=Lax263307Proofs.RationalProjection.classify_correct P q ρ cert hv
  have hN:0 < N:=Lax263307Proofs.CoordinateCatalog.catalog_positive n r
  have hnr:(0:ℝ) < n:=Nat.cast_pos.mpr hn
  have hNr:(0:ℝ) < N:=Nat.cast_pos.mpr hN
  have hDr:(0:ℝ) < D:=Nat.cast_pos.mpr (by omega)
  have hp:0 < sparsity a K B n D:=by
    dsimp [sparsity,targetThreshold]
    positivity
  have hη:0 < η:=by
    dsimp only [η]
    rw [Lax263307Proofs.AlgorithmParameters.conditioning_floor]
    unfold Lax263307.HeavyConditioning.probabilityFloor
    positivity
  have hρ:(0:ℝ) < (ρ:ℝ):=by rw [tolerance_cast]; positivity
  have hprotect:=(Lax263307Proofs.AlgorithmParameters.protected_radius (a:=a) (B:=B) hK hn (by omega:0 < D)).2
  have hnear_radius:((2:ℝ)^precision a K B n D)⁻¹≤ (ρ:ℝ) / (8 * N):=by
    convert hprotect using 1
    dsimp [ρ,tolerance]
    push_cast
    ring
  dsimp only [run]
  cases hout:Lax263307.RationalProjection.classify P ρ cert with
  | reject =>
    rw [hout] at hc
    change independentSetHull G k r=∅
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply hc
    refine ⟨encode z, (Lax263307Proofs.MomentLP.primal_characterization G k r (encode z)).mpr ?_⟩
    rw [Lax263307Proofs.MomentLP.decode_encode]
    exact Lax263307Proofs.RelaxationFeasibility.hull_feasible G k r z hz
  | far normal α =>
    rw [hout] at hc
    obtain ⟨hnorm,hvalid,hgap⟩:=hc
    obtain ⟨z,hz⟩:=far_feasible P q ρ cert hv normal α hout
    have hnz:=Lax263307Proofs.RationalCutBuffer.normal_nonzero normal (Lax109476.RationalCertificates.realVector q) z (by
      have hh:=hvalid z hz
      change (Lax109476.RationalCertificates.realVector normal) ⬝ᵥ z < (Lax109476.RationalCertificates.realVector normal) ⬝ᵥ (Lax109476.RationalCertificates.realVector q)
      dsimp [dotProduct,Lax109476.RationalCertificates.realVector] at *
      linarith only [hh,hgap,hρ])
    change (∃ i,_ ≠ 0)∧ _
    refine ⟨hnz, ?_⟩
    intro z hz e he
    apply Lax263307Proofs.RationalCutBuffer.scaled_cleared_cut hN normal (Lax109476.RationalCertificates.realVector center) (encode z)
      (α:ℝ) (ρ:ℝ) ((ρ:ℝ)/2) 1 (by positivity) hnorm
    · apply hvalid
      apply (Lax263307Proofs.MomentLP.primal_characterization G k r _).mpr
      rw [Lax263307Proofs.MomentLP.decode_encode]
      exact Lax263307Proofs.RelaxationFeasibility.hull_feasible G k r z hz
    · have heq:(fun i => 4 * (N:ℝ) * (Lax109476.RationalCertificates.realVector center i))=Lax109476.RationalCertificates.realVector q:=(cast_raw center).symm
      rw [heq]
      change (α:ℝ) + (ρ:ℝ)≤ ∑ i, (normal i:ℝ) * (q i:ℝ)
      linarith only [hgap]
    · simp
    · intro i
      have hh:=(he i).trans hnear_radius
      rw [show (ρ:ℝ) / 2 / (4 * N)=(ρ:ℝ) / (8 * N) by ring]
      exact hh
  | near y =>
    rw [hout] at hc
    obtain ⟨hy,hclose⟩:=hc
    have hfeas:Lax263307.LinearRelaxation.IsFeasible G k r
        (Lax263307.RationalConditioning.realVector (decode y)):=
      (Lax263307Proofs.MomentLP.primal_characterization G k r (Lax109476.RationalCertificates.realVector y)).mp hy
    have hclose':∀ T, |decode (Lax109476.RationalCertificates.realVector q) T - Lax263307.RationalConditioning.realVector (decode y) T|≤
        η * (1 / (D:ℝ))^2 / (32 * (n:ℝ)^2):=by
      intro T
      have hh:=hclose ((Lax263307.CoordinateCatalog.indexing n r).symm T)
      rw [abs_sub_comm] at hh
      change |decode (Lax109476.RationalCertificates.realVector q) T - Lax263307.RationalConditioning.realVector (decode y) T|≤ (tolerance a K B n D:ℝ) at hh
      rw [tolerance_cast] at hh
      exact hh
    have ho:=near_correct (decode y) hfeas (decode (Lax109476.RationalCertificates.realVector q)) hclose'
    dsimp only
    cases hresult:Lax263307.NearOracle.run flow a K B D G k (decode y) child with
    | reject => rw [hresult] at ho; exact False.elim ho
    | found I => rw [hresult] at ho; exact ho
    | cut A C u =>
      rw [hresult] at ho
      obtain ⟨_,_,_,hvalid,hgap,hnorm⟩:=ho
      let b:=Lax263307.ComponentCutEncoding.coefficient (r:=r) A C u
      let normal:=Lax263307.RoundedOracleSearch.rationalNormal (encode b)
      have hnorm':(∑ i, |(normal i:ℝ)|)≤ 2 * n:=by rw [cut_norm]; exact hnorm
      have hgap':η * (1/(D:ℝ))^2 / (16*n)≤ (Lax109476.RationalCertificates.realVector normal) ⬝ᵥ Lax109476.RationalCertificates.realVector q:=by
        change η * (1/(D:ℝ))^2 / (16*n)≤ (fun i => (normal i:ℝ)) ⬝ᵥ Lax109476.RationalCertificates.realVector q
        rw [cut_dot]
        exact hgap
      have hnz:=Lax263307Proofs.RationalCutBuffer.normal_nonzero normal (Lax109476.RationalCertificates.realVector q) 0 (by
        simp only [dotProduct_zero]
        exact lt_of_lt_of_le (by positivity) hgap')
      change (∃ i,_ ≠ 0)∧ _
      refine ⟨hnz, ?_⟩
      intro z hz e he
      apply Lax263307Proofs.RationalCutBuffer.scaled_cleared_cut hN normal (Lax109476.RationalCertificates.realVector center) (encode z)
        0 (η * (1/(D:ℝ))^2 / (16*n)) ((ρ:ℝ)/2) (2*n) (by positivity) hnorm'
      · rw [cut_dot,Lax263307Proofs.MomentLP.decode_encode]
        exact hvalid z hz
      · have heq:(fun i => 4 * (N:ℝ) * (Lax109476.RationalCertificates.realVector center i))=Lax109476.RationalCertificates.realVector q:=(cast_raw center).symm
        rw [heq,zero_add]
        exact hgap'
      · dsimp only [ρ]
        rw [tolerance_cast]
        dsimp only [η]
        field_simp
        ring_nf
        exact le_rfl
      · intro i
        have hh:=(he i).trans hnear_radius
        rw [show (ρ:ℝ) / 2 / (4 * N)=(ρ:ℝ) / (8 * N) by ring]
        exact hh

open Lax263307.GraphClasses Lax263307.PowerBagBounds

end Lax263307Proofs.ProjectedOracle

end

theorem solution:∀ {n:Nat} (lp flow:List Nat→ List Nat) (a K B D:Nat) (G:SimpleGraph (Fin n))
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
                  (@Lax263307.ProjectedOracle.run n lp flow a K B D G inst k child center):= @Lax263307Proofs.ProjectedOracle.run_correct
