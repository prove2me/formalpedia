-- Prove2me | solution 1 for OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:31:14.362028+00:00
-- url     : https://prove2.me/submissions/866751eb-492b-4b1b-9d6c-dc862027a742

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinPopulation
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer bin populations for the companion weight evaluator -/

namespace ContingencyTables.CompanionBinPopulation

open scoped BigOperators Classical

variable {C : Type*} [Fintype C]

lemma assignment_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    Fintype.card (Assignments B N v)=∏ c,(FairBits.fiber B (N c) (v c)).card := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_coe]

end ContingencyTables.CompanionBinPopulation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestPhysicalCompletion ForestLiteralCount

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Absolute component totals sum to at most the total absolute demand.
Each vertex is counted in one component, including isolated vertices. -/
theorem sum_abs_componentTotal (root : V → V) (r : V → ℝ) :
    (∑ a, |∑ v, if root v=a then r v else 0|)≤∑ v, |r v| := by
  calc
    _ ≤ ∑ a, ∑ v, |if root v=a then r v else 0| :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      have he (a v : V) : |if root v=a then r v else 0|=
          if root v=a then |r v| else 0 := by split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_comm]
      simp

end Generic

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the actual scaled forest-penalty Lipschitz bound -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_change (x y : ℝ) : |intervalCost x-intervalCost y| ≤ |x-y| := by
  have hsub (x y : ℝ) : intervalCost x ≤ intervalCost y+|x-y| := by
    unfold intervalCost
    apply max_le
    · linarith [le_max_left (0:ℝ) (max (-y) (y-1)),abs_nonneg (x-y)]
    · apply max_le
      · have hh : -y ≤ max 0 (max (-y) (y-1)) :=
          (le_max_left _ _).trans (le_max_right _ _)
        linarith [neg_le_abs (x-y)]
      · have hh : y-1 ≤ max 0 (max (-y) (y-1)) :=
          (le_max_right _ _).trans (le_max_right _ _)
        linarith [le_abs_self (x-y)]
  apply abs_le.mpr
  constructor
  · have hh := hsub y x
    rw [abs_sub_comm y x] at hh
    linarith
  · linarith [hsub x y]

lemma tree_card_le (A : Instance I J) : Fintype.card (TreeCell A.T) ≤ A.d := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer free assignments use the original scaled affine tree values -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma intervalCost_div (x b : ℝ) (hb : 0 < b) :
    intervalCost (x/b)=max 0 (max (-x) (x-b))/b := by
  unfold intervalCost
  have he : x/b-1=(x-b)/b := by field_simp [hb.ne']
  rw [he,← neg_div, max_div_div_right hb.le]
  simpa only [zero_div] using max_div_div_right hb.le (0:ℝ) (max (-x) (x-b))

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open ForestCountIdentification BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rowCounts_bounds (A : Instance I J) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (i : I) (j : J) (hs : A.small i j=true) :
    0 ≤ rowCounts A z i j ∧ rowCounts A z i j ≤ A.b i j := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have hh : smallX A.small z i j ≤ A.b i j := by
    simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
  change (smallX A.small z i j:ℤ) ≤ (A.b i j:ℤ)
  exact_mod_cast hh

lemma columnCounts_bounds (A : Instance I J) (z : View A → ℕ) (i : I) (j : J) :
    0 ≤ columnCounts A z i j ∧ columnCounts A z i j ≤ A.b i j := by
  unfold columnCounts
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast Nat.sub_le (A.b i j) (smallY A.small z i j)⟩

lemma integerCube_zero (A : Instance I J) (B : ℝ) : integerCube A B (zeroAssignment A)=0 := by
  funext a
  simp only [integerCube,zeroAssignment,Nat.cast_zero,mul_zero,zero_div,Pi.zero_apply]

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binWidth_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < binWidth A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold binWidth
  positivity

lemma height_positive (A : Instance I J) (C : ℝ) (hC : 0 < C) : 0 < height A C := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  unfold height
  positivity

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer bins have the manuscript's Cartesian populations -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem integerFiber_card (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).card=
      ∏ t : FreeCell A.small A.T,(FairBits.fiber K (freeRange A t) (naturalBin A v t)).card := by
  let : DecidableEq (FreeCell A.small A.T) := Classical.decEq _
  calc
    _ = Fintype.card {f // f∈integerFiber A K hK v} := (Fintype.card_coe _).symm
    _ = _ := Fintype.card_congr (integerFiberEquiv A K hK v)
    _ = _ := CompanionBinPopulation.assignment_card K (freeRange A) (naturalBin A v)

lemma assignmentCount_eq_prod (A : Instance I J) :
    assignmentCount A=∏ t : FreeCell A.small A.T,freeRange A t := by
  simp only [assignmentCount,FreeIndex,Fintype.card_pi,Fintype.card_fin,freeRange]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleJointLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization of the actual bin-then-integer sampling law -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma integerPoint_distance (A : Instance I J) (C : ℝ) (K : ℕ) (hK : 0 < K)
    (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    ∀ i,|integerPoint A C f i-realCorner (integerBin A K hK f) i| ≤ 1 := by
  intro i
  let t := index A i
  let N := freeRange A t
  let x := (f t).val
  have hq : (0:ℚ) ≤ (K:ℚ)*x/N := by positivity
  have hlo : (FairBits.scale K N x:ℚ) ≤ (K:ℚ)*x/N := Nat.floor_le hq
  have hhi : (K:ℚ)*x/N < (FairBits.scale K N x:ℚ)+1 := Nat.lt_floor_add_one _
  have hloR : (FairBits.scale K N x:ℝ) ≤ (K:ℝ)*x/N := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div] using (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR : (K:ℝ)*x/N < (FairBits.scale K N x:ℝ)+1 := by
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).mpr hhi
  have hN : (N:ℝ)=(A.b t.val.1 t.val.2:ℝ)+1 := by simp [N,freeRange]
  change |binWidth A C*(f t).val/((A.b t.val.1 t.val.2:ℝ)+1)-
    (FairBits.scale K N (f t).val:ℝ)| ≤ 1
  rw [←hB,←hN]
  change |(K:ℝ)*x/N-(FairBits.scale K N x:ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBinIntervals
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer intervals inside the companion evaluator bins -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma binOffsetValue_mem (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K)
    (x : (i : Fin (dimension A)) → Fin (binSize A K v i)) :
    binOffsetValue A K hK v x∈integerFiber A K hK v := (binOffsetsEquiv A K hK v x).property

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCorrectionArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rationalIntegerPoint_cast (A : Instance I J) (C : ℕ) (f : FreeIndex A.small A.T A.b)
    (i : Fin (dimension A)) :
    (rationalIntegerPoint A C f i:ℝ)=integerPoint A C f i := by
  simp only [rationalIntegerPoint,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,rationalBinWidth_cast,
    integerPoint,ForestScaledPenalty.integerCube,freeRange,Nat.cast_add,Nat.cast_one]
  push_cast
  rfl

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleSchedule
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma sampleCount_positive (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) : 0 < sampleCount j delta failure := by
  have hh := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
  have hp : (0:ℚ) < sampleCount j delta failure := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast hp

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_TreeCategorical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma fold_den (xs : List Fraction) (a : Fraction) (ha : 0<a.2) :
    0<(xs.foldl (fun a b=>add (b,a)) a).2 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons _ _ ih => exact ih _ (normalize_den_pos _)
lemma fold_val (xs : List Fraction) (a : Fraction) (ha : 0<a.2)
    (hx : ∀ b∈xs,0<b.2) :
    val (xs.foldl (fun a b=>add (b,a)) a)=val a+(xs.map val).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hab : 0<(add (b,a)).2 := normalize_den_pos _
    rw [List.foldl_cons,ih _ hab (fun c hc=>hx c (by simp [hc])),
      add_val b a (Nat.ne_of_gt (hx b (by simp))) (Nat.ne_of_gt ha)]
    simp only [List.map_cons,List.sum_cons]
    ring
lemma sum_den (xs : List Fraction) : 0<(sum xs).2 := fold_den xs (0,1) (by decide)
lemma sum_val (xs : List Fraction) (hx : ∀ b∈xs,0<b.2) :
    val (sum xs)=(xs.map val).sum := by
  rw [sum,fold_val xs (0,1) (by decide) hx]
  simp [val]

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisSemantics
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural coordinate encodings of dense axis moves -/

namespace ContingencyTables.DensePrograms
open ProfilePrograms GridBoundary
open scoped Classical

lemma listExchange_increment {q : ℕ} (v : Fin q → ℕ) (i : Fin q) :
    listExchange (List.ofFn v,(i.val,q))=
      List.ofFn (Function.update v i (v i+1)) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjq : j<q := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using hj
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      exchangeEntry,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hjq,dite_true,
      Option.getD_some,ite_eq_right (Nat.ne_of_lt hjq),Nat.sub_zero]
    by_cases hji : (⟨j,hjq⟩ : Fin q)=i
    · subst i
      simp only [Function.update_self,ite_true, if_true]
    · have hne : j≠i.val := fun h => hji (Fin.ext h)
      simp only [hne,ite_false,Nat.add_zero,Function.update_of_ne hji]

lemma listExchange_decrement {q : ℕ} (v : Fin q → ℕ) (i : Fin q) :
    listExchange (List.ofFn v,(q,i.val))=
      List.ofFn (Function.update v i (v i-1)) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro j hj _
    have hjq : j<q := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using hj
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      exchangeEntry,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hjq,dite_true,
      Option.getD_some,ite_eq_right (Nat.ne_of_lt hjq),Nat.add_zero]
    by_cases hji : (⟨j,hjq⟩ : Fin q)=i
    · subst i
      simp only [Function.update_self,ite_true, if_true]
    · have hne : j≠i.val := fun h => hji (Fin.ext h)
      simp only [hne,ite_false,Nat.sub_zero,Function.update_of_ne hji]

lemma gridNatCode_getD {q K : ℕ} (a : Grid (I := Fin q) K) (i : Fin q) :
    (gridNatCode a).getD i.val 0=(corner a i).toNat := by
  simp only [gridNatCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,
    dite_true,Option.getD_some,Fin.eta]

lemma gridNatCode_update {q K : ℕ} (a : Grid (I := Fin q) K) (i : Fin q)
    (v : Set.Icc (0 : ℤ) ((K : ℤ)-1)) :
    gridNatCode (Function.update a i v)=
      List.ofFn (Function.update (fun j => (corner a j).toNat) i v.val.toNat) := by
  apply congrArg List.ofFn
  funext j
  by_cases hji : j=i
  · subst j
    simp only [Function.update_self,corner]
  · simp only [Function.update_of_ne hji,corner]

/-- The bounded list operation implements exactly the signed geometric
axis proposal, including both boundary rejections. -/
theorem axisListStep_eq {q K : ℕ} (a : Grid (I := Fin q) K) (i : Fin q) (sign : Bool) :
    axisListStep (((K,gridNatCode a),i.val),sign)=
      (axisStep a i sign).map gridNatCode := by
  have hlen : (gridNatCode a).length=q := by simp only [gridNatCode,List.length_ofFn]
  have hnonneg : 0 ≤ corner a i := (a i).property.1
  have hupper : corner a i≤(K : ℤ)-1 := (a i).property.2
  have hcast : ((corner a i).toNat : ℤ)=corner a i := Int.toNat_of_nonneg hnonneg
  cases sign with
  | false =>
    simp only [axisListStep,hlen,i.isLt,ite_true, if_true,Bool.false_eq_true,ite_false,
      gridNatCode_getD,axisStep]
    by_cases h : 0 ≤ corner a i-1
    · have hn : 0<(corner a i).toNat := by omega
      rw [ite_eq_left hn,dite_eq_left h,Option.map_some]
      let v : Set.Icc (0 : ℤ) ((K : ℤ)-1) := ⟨corner a i-1,h,by omega⟩
      have hc := gridNatCode_update a i v
      have he : v.val.toNat=(corner a i).toNat-1 := by dsimp only [v]; omega
      rw [he] at hc
      exact congrArg some ((listExchange_decrement (fun j => (corner a j).toNat) i).trans hc.symm)
    · have hn : ¬0<(corner a i).toNat := by omega
      rw [ite_eq_right hn,dite_eq_right h,Option.map_none]
  | true =>
    simp only [axisListStep,hlen,i.isLt,ite_true, if_true,gridNatCode_getD,axisStep]
    by_cases h : corner a i+1≤(K : ℤ)-1
    · have hn : (corner a i).toNat+1<K := by omega
      rw [ite_eq_left hn,dite_eq_left h,Option.map_some]
      let v : Set.Icc (0 : ℤ) ((K : ℤ)-1) := ⟨corner a i+1,by omega,h⟩
      have hc := gridNatCode_update a i v
      have he : v.val.toNat=(corner a i).toNat+1 := by dsimp only [v]; omega
      rw [he] at hc
      exact congrArg some ((listExchange_increment (fun j => (corner a j).toNat) i).trans hc.symm)
    · have hn : ¬(corner a i).toNat+1<K := by omega
      rw [ite_eq_right hn,dite_eq_right h,Option.map_none]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-word decoding for a dense coordinate proposal -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

lemma directionCode_first {q : ℕ} (v : Fin (q*2)) :
    ((directionCodeEquiv q).symm v).1.val=v.val/2 := rfl

lemma directionCode_second {q : ℕ} (v : Fin (q*2)) :
    ((directionCodeEquiv q).symm v).2=decide (v.val%2=1) := by
  have hf (b : Fin 2) : finTwoEquiv b=decide (b.val=1) := by
    fin_cases b <;> rfl
  exact hf _

/-- A binary index gives exactly the signed coordinate code used by
the finite dense-chain transition; unused indices still reject. -/
theorem axisWordStep_eq {q K k : ℕ} (a : Grid (I := Fin q) K) (bits : Fin k → Bool) :
    axisWordStep ((K,gridNatCode a),List.ofFn bits)=
      (axisCodeStep a (FairBits.binaryWordEquiv k bits)).map gridNatCode := by
  rw [axisWordStep,bitValue_eq_word]
  let v := FairBits.binaryWordEquiv k bits
  change axisListStep (((K,gridNatCode a),v.val/2),decide (v.val%2=1))=
    (axisCodeStep a v).map gridNatCode
  by_cases hv : v.val<q*2
  · let u : Fin (q*2) := ⟨v.val,hv⟩
    let dir := (directionCodeEquiv q).symm u
    have hfirst : dir.1.val=v.val/2 := directionCode_first u
    have hsecond : dir.2=decide (v.val%2=1) := directionCode_second u
    rw [←hfirst,←hsecond,axisListStep_eq]
    simp only [axisCodeStep,dite_eq_left hv]
    rfl
  · have hi : ¬v.val/2<q := by omega
    have hlen : (gridNatCode a).length=q := by simp only [gridNatCode,List.length_ofFn]
    simp only [axisListStep,hlen,ite_eq_right hi,axisCodeStep,dite_eq_right hv,Option.map_none]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary evaluation of the finite Metropolis coin -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

theorem dyadicWordAccept_ofFn (gap k : ℕ) (bits : Fin k → Bool) :
    dyadicWordAccept (List.ofFn bits,gap)=
      decide (FairBits.acceptDyadic gap k (FairBits.binaryWordEquiv k bits)) := by
  simp only [dyadicWordAccept,List.length_ofFn,bitValue_eq_word,FairBits.acceptDyadic]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMetropolisSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary dense program realizes the exact finite transition -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped Classical

noncomputable section

lemma ofFn_split_take {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).take p=List.ofFn ((splitWordEquiv p k bits).1) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left (Nat.le_add_right p k)]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

lemma ofFn_split_drop {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).drop p=List.ofFn ((splitWordEquiv p k bits).2) := by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn,Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change p+i=p+i
    rfl

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma wordChunk_ofFn {n k : ℕ} (bits : Fin (n*k) → Bool) (i : Fin n) :
    wordChunk ((k,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j))) := by
  have hbound : k ≤ n*k-i.val*k := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul,Nat.add_comm] using
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
  apply List.ext_getElem
  · simp only [wordChunk,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [wordChunk,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change i.val*k+j=j+k*i.val
    ac_rfl

theorem wordChunks_ofFn {n k : ℕ} (hk : 0<k) (bits : Fin (n*k) → Bool) :
    wordChunks (k,List.ofFn bits)=
      List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j)))) := by
  have hrows : completeWordRows (k,List.ofFn bits)=List.range n := by
    simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ hk]
  unfold wordChunks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i<n := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact wordChunk_ofFn bits ⟨i,hin⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_EstimatorWordBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact disjoint word layout of one weight estimator

There is one bank of ratio samples for every phase, followed by one bank
of correction samples. Each correction sample has its own walk and bin
words. This is the literal layout used by the executable allocator.
-/

namespace ContingencyTables.EstimatorWordBanks

open DensePrograms GridBoundary FairBits
open scoped Classical

lemma ratio_chunks (j S r t b : ℕ) (hr : 0 < r)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) (a : Fin j) :
    wordChunks (r,wordChunk ((S*r,(List.ofFn bits).take (j*(S*r))),a.val))=
      List.ofFn (fun i : Fin S => List.ofFn ((wordEquiv j S r t b bits).1 a i)) := by
  rw [ofFn_split_take,wordChunk_ofFn]
  rw [wordChunks_ofFn hr]
  rfl

lemma ratio_rows (j S r t b : ℕ) (hs : 0 < S) (hr : 0 < r)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) :
    completeWordRows (S*r,(List.ofFn bits).take (j*(S*r)))=List.range j := by
  rw [ofFn_split_take]
  simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ (Nat.mul_pos hs hr)]

lemma correction_chunks (j S r t b : ℕ) (ht : 0 < t+b)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) :
    (wordChunks (t+b,(List.ofFn bits).drop (j*(S*r)))).take S=
      List.ofFn (fun i : Fin S => List.ofFn
        (gridWordEquiv S (t+b) (splitWordEquiv (j*(S*r)) (S*(t+b)) bits).2 i)) := by
  rw [ofFn_split_drop,wordChunks_ofFn ht]
  exact List.take_of_length_le (by simp)

lemma correction_take (j S r t b : ℕ)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) (i : Fin S) :
    (List.ofFn (gridWordEquiv S (t+b)
      (splitWordEquiv (j*(S*r)) (S*(t+b)) bits).2 i)).take t=
        List.ofFn ((wordEquiv j S r t b bits).2 i).1 := by
  rw [ofFn_split_take]
  rfl

lemma correction_drop (j S r t b : ℕ)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) (i : Fin S) :
    (List.ofFn (gridWordEquiv S (t+b)
      (splitWordEquiv (j*(S*r)) (S*(t+b)) bits).2 i)).drop t=
        List.ofFn ((wordEquiv j S r t b bits).2 i).2 := by
  rw [ofFn_split_drop]
  rfl

end ContingencyTables.EstimatorWordBanks

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScaledWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem scaledWordValue_ofFn (M k : ℕ) (hM : 0<M) (bits : Fin k → Bool) :
    scaledWordValue (M,List.ofFn bits)=(FairBits.scaledBitInteger M k hM bits).val := by
  simp only [scaledWordValue,List.length_ofFn,bitValue_eq_word]
  rfl

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

open scoped BigOperators

lemma take_ofFn_sum {q : ℕ} (width : Fin q → ℕ) (i : Fin q) :
    ((List.ofFn width).take i.val).sum=∑ j : Fin i.val,width (Fin.castLE i.isLt.le j) := by
  rw [←Fin.ofFn_take_eq_take_ofFn i.isLt.le,List.sum_ofFn]
  rfl

theorem dependentChunk_ofFn {q : ℕ} (width : Fin q → ℕ)
    (bits : Fin (∑ i,width i) → Bool) (i : Fin q) :
    dependentChunk ((List.ofFn width,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin (width i) => bits (finSigmaFinEquiv ⟨i,j⟩)) := by
  have hw : (List.ofFn width).getD i.val 0=width i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  have hb : ((List.ofFn width).take i.val).sum+width i≤∑ j,width j := by
    by_cases hi : width i=0
    · rw [hi,Nat.add_zero,←List.sum_ofFn]
      exact (List.take_sublist i.val (List.ofFn width)).sum_le_sum (fun _ _ => Nat.zero_le _)
    · have hh := (finSigmaFinEquiv (⟨i,⟨width i-1,by omega⟩⟩ : Sigma (fun i => Fin (width i)))).isLt
      rw [finSigmaFinEquiv_apply,←take_ofFn_sum] at hh
      dsimp only at hh
      omega
  have hlen : width i≤(∑ j,width j)-((List.ofFn width).take i.val).sum :=
    Nat.le_sub_of_add_le (by omega)
  apply List.ext_getElem
  · simp only [dependentChunk,chunkStart,List.length_take,List.length_drop,List.length_ofFn,hw,
      min_eq_left hlen]
  · intro j hj _
    simp only [dependentChunk,chunkStart,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    simp only [finSigmaFinEquiv_apply,take_ofFn_sum]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the actual variable-width offset word layout -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary FairBits

lemma cellPairs_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    cellPairs (List.ofFn r,List.ofFn c)=List.ofFn (fun v : Fin (m*n) =>
      (((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).1.val,
        ((finProdFinEquiv : Fin m×Fin n ≃ Fin (m*n)).symm v).2.val)) := by
  apply List.ext_getElem
  · simp only [cellPairs,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    simp only [cellPairs,List.getElem_map,List.getElem_range,List.getElem_ofFn,pairAt,List.length_ofFn]
    rfl

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAcceptanceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the rational acceptance coin

The integer quotient computes the exact floor threshold used by the
finite-word acceptance law. The word length controls all powering and
word traversal, even for malformed fraction inputs.
-/

namespace ContingencyTables.FractionAcceptanceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

noncomputable section

lemma fraction_threshold (B : ℕ) (q : TreeFraction.Fraction) :
    FairBits.rationalThreshold B (TreeFraction.val q)=q.1*2^B/q.2 := by
  by_cases hd : q.2=0
  · simp [FairBits.rationalThreshold,TreeFraction.val,hd]
  · let M := q.1*2^B
    have hdq : (q.2:ℚ)≠0 := by exact_mod_cast hd
    have he : (2:ℚ)^B*TreeFraction.val q=(M:ℚ)/q.2 := by
      simp only [TreeFraction.val,M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    change ⌊(2:ℚ)^B*TreeFraction.val q⌋₊=_
    rw [he]
    have hh := Nat.mul_cast_floor_div_cancel (R := ℚ) (n := q.2)
      hd ((M:ℚ)/q.2)
    simpa only [div_mul_cancel₀ _ hdq,Nat.floor_natCast] using hh.symm

end
end ContingencyTables.FractionAcceptanceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RationalIntervalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary arithmetic for a forest interval penalty

A signed affine numerator is stored as a difference of two naturals.
Its distance outside the interval [0,1] is a nonnegative fraction with
the same denominator; no signed rational comparison is required.
-/

namespace ContingencyTables.RationalIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma intervalCode_denominator (z : Input) : 0<(intervalCode z).2 :=
  TreeFraction.normalize_den_pos _

noncomputable section

/-- Exact agreement with the interval cost in the forest density. The
only side condition is the strictly positive tree capacity denominator. -/
theorem intervalCode_value (p n d : ℕ) (hd : 0<d) :
    TreeFraction.val (intervalCode ((p,n),d))=
      max 0 (max (-(((p:ℚ)-n)/d)) (((p:ℚ)-n)/d-1)) := by
  rw [intervalCode,TreeFraction.normalize_val]
  change (((n-p)+(p-(n+d)):ℕ):ℚ)/d=_
  have hdq : (0:ℚ)<d := by exact_mod_cast hd
  let x : ℚ := ((p:ℚ)-n)/d
  change (((n-p)+(p-(n+d)):ℕ):ℚ)/d=max 0 (max (-x) (x-1))
  by_cases hpn : p≤n
  · have hx : x≤0 := div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (by exact_mod_cast hpn)) hdq.le
    have hsub : p≤n+d := by omega
    simp only [Nat.sub_eq_zero_of_le hsub,Nat.add_zero,Nat.cast_sub hpn,
      max_eq_left (show x-1≤-x by linarith),max_eq_right (neg_nonneg.mpr hx)]
    dsimp only [x]
    ring
  · have hnp : n≤p := by omega
    have hx : 0≤x := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hnp)) hdq.le
    by_cases hpd : p≤n+d
    · have hx1 : x≤1 := (div_le_one hdq).mpr (by
        have hh : (p:ℚ)≤n+d := by exact_mod_cast hpd
        linarith)
      simp only [Nat.sub_eq_zero_of_le hnp,Nat.sub_eq_zero_of_le hpd,Nat.zero_add,
        Nat.cast_zero,zero_div]
      symm
      exact max_eq_left (max_le (neg_nonpos.mpr hx) (by linarith))
    · have hdp : n+d≤p := by omega
      have hx1 : 1≤x := (le_div_iff₀ hdq).mpr (by
        have hh : (n:ℚ)+d≤p := by exact_mod_cast hdp
        linarith)
      simp only [Nat.sub_eq_zero_of_le hnp,Nat.zero_add,Nat.cast_sub hdp,Nat.cast_add,
        max_eq_right (show -x≤x-1 by linarith),max_eq_right (sub_nonneg.mpr hx1)]
      dsimp only [x]
      field_simp [hdq.ne']
      ring

end
end ContingencyTables.RationalIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list evaluation of the forest's signed affine numerators

Each coefficient is stored by its nonnegative and nonpositive parts.
The program performs two finite product sums and passes their difference
to the proved interval-cost routine. Large capacities are never iterated.
-/

namespace ContingencyTables.ForestAffineProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

noncomputable section
variable {q : ℕ}

lemma parts_data (offset : ℤ) (coefficient : Fin q → ℤ) (v : Fin q → ℕ) (den : ℕ) :
    ((parts (data offset coefficient v den)).1:ℤ)-(parts (data offset coefficient v den)).2=
      offset+∑ i,coefficient i*(v i:ℤ) := by
  simp only [parts,data,List.map_ofFn,Function.comp_apply,positiveTerm,negativeTerm,
    List.sum_ofFn,Nat.cast_add,Nat.cast_sum,Nat.cast_mul]
  rw [add_sub_add_comm,←Finset.sum_sub_distrib,signedParts_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←sub_mul,signedParts_sub]

/-- All signs and products in an affine tree term are executed in
binary; the resulting fraction is its exact interval penalty. -/
theorem evaluate_data (offset : ℤ) (coefficient : Fin q → ℤ) (v : Fin q → ℕ)
    (den : ℕ) (hd : 0<den) :
    TreeFraction.val (evaluate (data offset coefficient v den))=
      max 0 (max (-(((offset:ℚ)+∑ i,(coefficient i:ℚ)*(v i:ℚ))/den))
        (((offset:ℚ)+∑ i,(coefficient i:ℚ)*(v i:ℚ))/den-1)) := by
  have he : ((parts (data offset coefficient v den)).1:ℚ)-
      (parts (data offset coefficient v den)).2=
      (offset:ℚ)+∑ i,(coefficient i:ℚ)*(v i:ℚ) := by
    exact_mod_cast parts_data offset coefficient v den
  calc
    _ = max 0 (max (-((((parts (data offset coefficient v den)).1:ℚ)-
          (parts (data offset coefficient v den)).2)/den))
        ((((parts (data offset coefficient v den)).1:ℚ)-
          (parts (data offset coefficient v den)).2)/den-1)) :=
      RationalIntervalProgram.intervalCode_value _ _ _ hd
    _ = _ := by rw [he]


open CompanionFactorialApplication ForestAssignmentSplit CompanionOracleDensity GraphCompletionCounts

end
end ContingencyTables.ForestAffineProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedPairProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed arithmetic used to prepare the forest evaluator

A pair stores a difference of naturals. Arithmetic never iterates through
the represented integer value, and normalization returns the exact
positive/negative parts expected by the affine penalty program.
-/

namespace ContingencyTables.SignedPairProgram

open MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma value_plus (a b : Signed) : value (plus (a,b))=value a+value b := by
  simp only [value,plus,Nat.cast_add]
  ring

lemma value_neg (a : Signed) : value (neg a)= -value a := by
  unfold value neg
  ring

lemma value_minus (a b : Signed) : value (minus (a,b))=value a-value b := by
  rw [minus,value_plus,value_neg]
  ring

lemma value_times (a b : Signed) : value (times (a,b))=value a*value b := by
  simp only [value,times,Nat.cast_add,Nat.cast_mul]
  ring

lemma value_normalize (a : Signed) : value (normalize a)=value a := by
  rw [normalize_eq]
  exact ForestAffineProgram.signedParts_sub (value a)

end ContingencyTables.SignedPairProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedFloorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary floor of a signed rational

Two natural quotients and the comparison of their remainders compute
the exact floor. No loop depends on the numeric numerator or denominator.
-/

namespace ContingencyTables.SignedFloorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram

theorem scaledFloor_value (p n d : ℕ) (xs : List Bool) :
    value (scaledFloor (((p,n),d),xs))=
      ⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋ := by
  rw [scaledFloor,scale,floorCode_value]
  congr 1
  push_cast
  ring

end ContingencyTables.SignedFloorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphRoots
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit least roots of finite graph components

The selector uses the finite reachability closure, not a choice of a
quotient representative. Its defining closure runs exactly n growth
rounds on Fin n, including disconnected and singleton components.
-/

namespace ContingencyTables.FiniteGraphRoots

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma root_le {u v : Fin n} (h : G.Reachable u v) : root G u≤v :=
  Finset.min'_le _ v ((mem_closure G u v).mpr h)

end ContingencyTables.FiniteGraphRoots

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCompletion
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forest completion with an explicit component-root selector

Only reachability and constancy on each component are needed for the
integral completion. Making these data explicit permits the executed
least-root selector to replace the original quotient representative,
without asserting that two different selectors are equal.
-/

namespace ContingencyTables.RootedCompletion

open scoped BigOperators Classical
open SimpleGraph GraphIntegralCompletion ForestCut ForestCapacity MaximumForest

variable {V : Type*}

lemma rowColumn_root {m n : ℕ} (T : SimpleGraph (Fin m⊕Fin n)) [DecidableRel T.Adj]
    (v : Fin m⊕Fin n) :
    (rowColumn T).root v=finSumFinEquiv.symm
      (FiniteGraphRoots.root (T.comap finSumFinEquiv.symm) (finSumFinEquiv v)) := rfl

end ContingencyTables.RootedCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCut
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit endpoint on the side away from a selected root

One reachability test in the edge-deleted forest selects the endpoint.
No choice of a component representative or of a cut vertex is needed.
-/

namespace ContingencyTables.RootedCut

open scoped BigOperators Classical
open SimpleGraph MaximumForest RootedCompletion GraphCompletionCounts ForestCut
open ForestCapacity

variable {V : Type*}

theorem selected_nonroot (T : SimpleGraph V) (S : Selection T) (hT : T.IsAcyclic)
    {u v a : V} (ht : T.Adj u v) (ha : cut T u v (S.root u) a=true) : a≠S.root a := by
  intro he
  have hp := away_properties T hT ht (S.root u) (S.reachable u).symm
  have hreach : (T.deleteEdges {s(u,v)}).Reachable (away T u v (S.root u)) a := by
    simpa only [cut,side,decide_eq_true_eq] using ha
  have hcomp := hp.1.trans (hreach.mono (T.deleteEdges_le {s(u,v)}))
  have hsame : S.root a=S.root u :=
    (S.constant hcomp).symm.trans (S.idempotent u)
  have hae : a=S.root u := he.trans hsame
  have hbad : cut T u v (S.root u) (S.root u)=true := by simpa only [hae] using ha
  exact Bool.false_ne_true (hp.2.1.symm.trans hbad)

variable {I J : Type*}

lemma treeCut_nonroot (T : SimpleGraph (I⊕J)) (S : Selection T) (hT : T.IsAcyclic)
    (t : TreeCell T) (v : I⊕J) (hv : treeCut T S t v=true) : v≠S.root v :=
  selected_nonroot T S hT t.property hv

lemma sign_abs_le_one (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) : |sign T S t a|≤1 := by
  unfold sign
  cases treeCut T S t (.inl a.1) <;> cases treeCut T S t (.inr a.2) <;>
    norm_num [indicator]

lemma other_tree_sign_zero (T : SimpleGraph (I⊕J)) (S : Selection T)
    (t : TreeCell T) (a : I×J) (ha : T.Adj (.inl a.1) (.inr a.2)) (hne : a≠t.val) :
    sign T S t a=0 := by
  have hh := side_eq_of_tree_edge T (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (away T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1))) ha
    (by intro he; exact hne (cell_edge_injective he))
  exact sub_eq_zero.mpr (congrArg indicator hh)

end ContingencyTables.RootedCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAffine
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut coefficients for an explicitly selected forest root

The same signed cut calculation applies to the executed root selector.
In particular, coefficient size and the maximum-forest capacity bound
do not depend on a classical choice of cut representative.
-/

namespace ContingencyTables.RootedAffine

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedCut GraphCompletionCounts
open ForestCapacity ForestCut MaximumForest

variable {I J : Type*} [Fintype I] [Fintype J]

lemma coefficient_abs_le_one (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) : |coefficient A S t a|≤1 := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,sign_abs_self A.T S A.hT,div_one]
    exact sign_abs_le_one A.T S t a
  · norm_num

lemma capacity_le_of_coefficient_ne_zero (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (ha : coefficient A S t a≠0) :
    A.b a.1 a.2≤A.b t.val.1 t.val.2 := by
  have hf : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2) := by
    by_contra hn
    exact ha (by simp only [coefficient,hn,ite_false])
  have hcross : treeCut A.T S t (.inl a.1)≠treeCut A.T S t (.inr a.2) := by
    intro he
    apply ha
    simp [coefficient,hf,sign,he]
  have h := crossing_free_edge_le (cellGraph A.small) A.T (capacity A.b)
    A.hTG A.hT A.hmax (s(Sum.inl t.val.1,Sum.inr t.val.2))
    (by simpa using t.property)
    (away A.T (.inl t.val.1) (.inr t.val.2) (S.root (.inl t.val.1)))
    (show (cellGraph A.small).Adj (.inl a.1) (.inr a.2) from hf.1) hf.2 hcross
  simpa only [capacity_cell] using h

theorem normalized_coefficient_bound (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (a : I×J) (B : ℝ) (hB : 0<B) :
    |coefficient A S t a*((A.b a.1 a.2:ℝ)+1)/B/(A.b t.val.1 t.val.2:ℝ)|≤2/B := by
  have hb : (1:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
  by_cases ha : coefficient A S t a=0
  · simp only [ha,zero_mul,zero_div,abs_zero]
    positivity
  have hcap : (A.b a.1 a.2:ℝ)≤A.b t.val.1 t.val.2 := by
    exact_mod_cast capacity_le_of_coefficient_ne_zero A S t a ha
  rw [abs_div,abs_div,abs_mul,abs_of_pos hB,
    abs_of_pos (by linarith : (0:ℝ)<A.b t.val.1 t.val.2),
    abs_of_nonneg (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<A.b t.val.1 t.val.2)).mpr
  rw [div_le_iff₀ hB]
  have hh := mul_le_mul_of_nonneg_right (coefficient_abs_le_one A S t a)
    (by positivity : (0:ℝ)≤(A.b a.1 a.2:ℝ)+1)
  field_simp [hB.ne']
  nlinarith

theorem affine_of_nonroot_equations (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (x q z : I → J → ℝ)
    (hr : ∀ i,Sum.inl i≠S.root (.inl i) →
      rowDifference A.small x z (fun i j => (A.X i j:ℝ)) i=0)
    (hc : ∀ j,Sum.inr j≠S.root (.inr j) →
      columnDifference A.small q z (fun i j => (A.X i j:ℝ)) j=0) :
    z t.val.1 t.val.2=affineTree A S t x q (fun a => z a.1 a.2) := by
  let f : I×J → ℝ := fun a => cutTerm A.small
    (fun i => treeCut A.T S t (.inl i)) (fun j => treeCut A.T S t (.inr j))
    x q z (fun i j => (A.X i j:ℝ)) a.1 a.2
  have hsum : (∑ a,f a)=0 := by
    rw [Fintype.sum_prod_type]
    exact cut_sum_zero A.small _ _ x q z _
      (fun i hi => hr i (treeCut_nonroot A.T S A.hT t (.inl i) hi))
      (fun j hj => hc j (treeCut_nonroot A.T S A.hT t (.inr j) hj))
  have hterm (a : I×J) : f a=
      (if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)+
      (if A.small a.1 a.2 then
        indicator (treeCut A.T S t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          indicator (treeCut A.T S t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) else 0)-
      sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2) := by
    by_cases he : a=t.val
    · subst a
      have hs : A.small t.val.1 t.val.2=false := A.hTG t.property
      simp only [f,cutTerm,hs,Bool.false_eq_true,ite_false,ite_true, if_true,coefficient,t.property,
        not_true_eq_false,and_false,sign,mul_zero,zero_mul,add_zero,sub_zero]
    · by_cases hs : A.small a.1 a.2=true
      · simp [f,cutTerm,hs,he,coefficient]
      · have hs' : A.small a.1 a.2=false := Bool.eq_false_iff.mpr hs
        by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
        · have hz := other_tree_sign_zero A.T S t a ht he
          simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_true_eq_false,and_false,zero_add,mul_zero,zero_mul,sub_zero]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=0
          rw [hz,zero_mul]
        · simp only [f,cutTerm,hs',Bool.false_eq_true,ite_false,he,coefficient,ht,
            not_false_eq_true,and_self,ite_true, if_true,zero_add,zero_sub]
          change sign A.T S t a*(z a.1 a.2-(A.X a.1 a.2:ℝ))=
            -(sign A.T S t t.val*(-sign A.T S t a/sign A.T S t t.val)*
              (z a.1 a.2-A.X a.1 a.2))
          field_simp [sign_self_ne_zero A.T S A.hT t]
  simp_rw [hterm] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  have hsingle : (∑ a : I×J,
      if a=t.val then sign A.T S t t.val*(z a.1 a.2-A.X a.1 a.2) else 0)=
      sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2) := by simp
  rw [hsingle] at hsum
  change sign A.T S t t.val*(z t.val.1 t.val.2-A.X t.val.1 t.val.2)+
    smallContribution A S t x q-
    (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=0 at hsum
  have hprod : (∑ a : I×J,sign A.T S t t.val*coefficient A S t a*(z a.1 a.2-A.X a.1 a.2))=
      sign A.T S t t.val*((∑ a : I×J,coefficient A S t a*z a.1 a.2)-
        ∑ a : I×J,coefficient A S t a*(A.X a.1 a.2:ℝ)) := by
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hprod] at hsum
  unfold affineTree AffinePenalty.affineValue offset
  apply mul_left_cancel₀ (sign_self_ne_zero A.T S A.hT t)
  rw [mul_add,mul_sub,mul_sub,←mul_div_assoc,
    mul_div_cancel_left₀ _ (sign_self_ne_zero A.T S A.hT t)]
  nlinarith [hsum]

end ContingencyTables.RootedAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhysicalCompletion
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal residual completion for the executed root convention

The row and column small views remain distinct. The explicit selected
roots determine which incidence equations are enforced; the resulting
integral completion is exactly the selected-cut affine formula.
-/

namespace ContingencyTables.RootedPhysicalCompletion

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedAffine GraphCompletionCounts ForestCut
open ForestPhysicalCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The cut-defined coefficients evaluate the actual integral solution
for this root convention, including every unbalanced small profile. -/
theorem solved_eq_affine (A : Instance I J) (S : Selection A.T) (t : TreeCell A.T)
    (x q free : I → J → ℤ) :
    (solved A S x q free t.val.1 t.val.2:ℝ)=
      affineTree A S t (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
        (fun a => (free a.1 a.2:ℝ)) := by
  let z : I → J → ℝ := fun i j => (completed A S x q free i j:ℝ)
  have hh := affine_of_nonroot_equations A S t (fun i j => (x i j:ℝ))
    (fun i j => (q i j:ℝ)) z (by
      intro i hi
      have hr := row_completed_sum A S x q free i hi
      unfold rowDifference
      have he : (∑ j,if A.small i j then (x i j:ℝ) else z i j)=(A.r i:ℝ) := by
        dsimp only [z]
        exact_mod_cast hr
      have hX : (∑ j,(A.X i j:ℝ))=(A.r i:ℝ) := by exact_mod_cast A.hXr i
      calc
        _=(∑ j,if A.small i j then (x i j:ℝ) else z i j)-(∑ j,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self]) (by
      intro j hj
      have hc := column_completed_sum A S x q free j hj
      unfold columnDifference
      have he : (∑ i,if A.small i j then (q i j:ℝ) else z i j)=(A.c j:ℝ) := by
        dsimp only [z]
        exact_mod_cast hc
      have hX : (∑ i,(A.X i j:ℝ))=(A.c j:ℝ) := by exact_mod_cast A.hXc j
      calc
        _=(∑ i,if A.small i j then (q i j:ℝ) else z i j)-(∑ i,(A.X i j:ℝ)) := by
          rw [←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _=0 := by rw [he,hX,sub_self])
  have hz : z t.val.1 t.val.2=(solved A S x q free t.val.1 t.val.2:ℝ) := by
    simp only [z,completed,t.property,ite_true, if_true]
  rw [hz] at hh
  rw [hh]
  unfold affineTree AffinePenalty.affineValue
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ht : A.T.Adj (.inl a.1) (.inr a.2)
  · simp only [coefficient,ht,not_true_eq_false,and_false,ite_false,zero_mul]
  · simp only [z,completed,ht,ite_false]

end ContingencyTables.RootedPhysicalCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root discrepancy is independent of the free entries

Every large-cell edge stays in a maximum-forest component.  Its two
incidences therefore cancel in the selected-root component sum.
-/

namespace ContingencyTables.RootedRootPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPhysicalCompletion
open ForestPhysicalCompletion (rowResidual columnResidual fixedRow fixedColumn)
open ForestRootPenalty (residualDemand smallDemand)

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma componentSum_decidable (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) :
    (∑ v,@ite ℤ (S.root v=a) (Classical.propDecidable _) (d v) 0)=
      ∑ v,if S.root v=a then d v else 0 := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : S.root v=a <;> simp only [h,ite_true, if_true,ite_false]

lemma root_eq_large (A : Instance I J) (S : Selection A.T) (i : I) (j : J)
    (hs : A.small i j=false) : S.root (.inl i)=S.root (.inr j) := by
  have hcap : ∀ e∈(ForestCapacity.cellGraph A.small).edgeSet,0<ForestCapacity.capacity A.b e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have hg : (ForestCapacity.cellGraph A.small).Adj u v := by simpa using he
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim hg
      | inr j => exact (A.hlarge i j hg).2
    | inr j =>
      cases v with
      | inl i => exact (A.hlarge i j hg).2
      | inr j' => exact False.elim hg
  have hspans := MaximumForest.maximum_spans (ForestCapacity.cellGraph A.small) A.T
    (ForestCapacity.capacity A.b) A.hTG A.hT A.hmax hcap
  apply S.constant
  rw [hspans]
  exact (show (ForestCapacity.cellGraph A.small).Adj (.inl i) (.inr j) from hs).reachable

lemma componentTotal_residual (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a=
      componentTotal A S (smallDemand A.small A.X x q) a := by
  let R : I → ℤ := fun i => if S.root (.inl i)=a then 1 else 0
  let C : J → ℤ := fun j => if S.root (.inr j)=a then 1 else 0
  have hrow (i : I) : R i*rowResidual A.small A.T A.r x free i=
      ∑ j,R i*(A.X i j-fixedRow A.small A.T x free i j) := by
    rw [rowResidual,←A.hXr i,←Finset.sum_sub_distrib,Finset.mul_sum]
  have hcol (j : J) : C j*(-columnResidual A.small A.T A.c q free j)=
      ∑ i,C j*(fixedColumn A.small A.T q free i j-A.X i j) := by
    rw [columnResidual,←A.hXc j,neg_sub,←Finset.sum_sub_distrib,Finset.mul_sum]
  unfold componentTotal residualDemand smallDemand
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  change (∑ i,R i*rowResidual A.small A.T A.r x free i)+
      (∑ j,C j*(-columnResidual A.small A.T A.c q free j))=
    (∑ i,R i*(∑ j,if A.small i j then A.X i j-x i j else 0))+
      ∑ j,C j*(∑ i,if A.small i j then q i j-A.X i j else 0)
  simp_rw [hrow,hcol,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => C j*(fixedColumn A.small A.T q free i j-A.X i j)),
    Finset.sum_comm (f := fun j i => C j*(if A.small i j then q i j-A.X i j else 0)),
    ←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : A.small i j=true
  · simp [fixedRow,fixedColumn,hs]
  · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
    have he : R i=C j := by unfold R C; rw [root_eq_large A S i j hs']
    rw [he]
    simp only [fixedRow,fixedColumn,hs',Bool.false_eq_true,ite_false]
    ring

lemma table_row_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (i : I) :
    (∑ j,table A.T S r c i j)=
      r i-∑ v,if S.root v=Sum.inl i then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inl i)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ i',flow S (Sum.elim r (fun j => -c j)) (.inl i) (.inl i'))=0 := by
    apply Finset.sum_eq_zero
    intro i' _
    apply flow_supported
    intro h
    exact A.hTG h
  simp only [hz,zero_add,Sum.elim_inl] at hs
  rw [componentSum_decidable] at hs
  simpa only [table] using hs

lemma table_column_all (A : Instance I J) (S : Selection A.T)
    (r : I → ℤ) (c : J → ℤ) (j : J) :
    -(∑ i,table A.T S r c i j)=
      -c j-∑ v,if S.root v=Sum.inr j then Sum.elim r (fun j => -c j) v else 0 := by
  have hs := flow_divergence_all S (Sum.elim r (fun j => -c j)) (.inr j)
  rw [Fintype.sum_sum_type] at hs
  have hz : (∑ j',flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inr j'))=0 := by
    apply Finset.sum_eq_zero
    intro j' _
    apply flow_supported
    intro h
    exact A.hTG h
  have hskew : (∑ i,flow S (Sum.elim r (fun j => -c j)) (.inr j) (.inl i))=
      -(∑ i,table A.T S r c i j) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact flow_skew S _ _ _
  simp only [hz,add_zero,Sum.elim_inr,hskew] at hs
  rw [componentSum_decidable] at hs
  exact hs

theorem signedResidual_eq_small (A : Instance I J) (S : Selection A.T)
    (x q free : I → J → ℤ) (a : I⊕J) :
    signedResidual A S x q free a=-componentTotal A S (smallDemand A.small A.X x q) a := by
  suffices he : signedResidual A S x q free a=
      -componentTotal A S (residualDemand A.small A.T A.r A.c x q free) a by
    rw [he,componentTotal_residual]
  have htotal : ∀ d : I⊕J → ℤ,
      (∑ v,if S.root v=a then d v else 0)=componentTotal A S d a := by
    intro d
    simp [componentTotal,ite_mul]
  cases a with
  | inl i =>
    simp only [signedResidual,Sum.elim_inl]
    simp_rw [row_pointwise]
    rw [Finset.sum_add_distrib]
    have hr := table_row_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) i
    change (∑ j,solved A S x q free i j)=_ at hr
    rw [hr,htotal]
    unfold residualDemand rowResidual columnResidual
    ring
  | inr j =>
    simp only [signedResidual,Sum.elim_inr]
    simp_rw [column_pointwise]
    rw [Finset.sum_add_distrib]
    have hc := table_column_all A S (rowResidual A.small A.T A.r x free)
      (columnResidual A.small A.T A.c q free) j
    change -(∑ i,solved A S x q free i j)=_ at hc
    have hc' : (∑ i,solved A S x q free i j)=columnResidual A.small A.T A.c q free j+
        ∑ v,if S.root v=Sum.inr j then
          Sum.elim (rowResidual A.small A.T A.r x free)
            (fun j => -columnResidual A.small A.T A.c q free j) v else 0 := by linarith
    rw [hc',htotal]
    unfold residualDemand rowResidual columnResidual
    ring

end ContingencyTables.RootedRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial signed component sums for the executed root labels -/

namespace ContingencyTables.RootedComponentProgram

open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

lemma absoluteDifference_eq (p q : ℕ) : absoluteDifference (p,q)=( (p:ℤ)-q).natAbs := by
  rcases Nat.le_total p q with hpq|hqp
  · rw [Int.natAbs_natCast_sub_natCast_of_le hpq]
    simp [absoluteDifference,Nat.sub_eq_zero_of_le hpq]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hqp]
    simp [absoluteDifference,Nat.sub_eq_zero_of_le hqp]

lemma parts_records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) (a : Fin n) :
    ((parts (a.val,records root p q)).1:ℤ)-(parts (a.val,records root p q)).2=
      ∑ i,if root i=a then (p i:ℤ)-q i else 0 := by
  simp only [parts,records,List.map_ofFn,Function.comp_apply,positiveTerm,negativeTerm,
    List.sum_ofFn,Nat.cast_sum]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : root i=a
  · simp [h]
  · have hval : a.val≠(root i).val := by
      intro he
      exact h (Fin.ext he.symm)
    simp [h,hval]

theorem component_records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) (a : Fin n) :
    component (a.val,records root p q)=(∑ i,if root i=a then (p i:ℤ)-q i else 0).natAbs := by
  rw [component,absoluteDifference_eq,parts_records]

theorem total_records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) :
    total (records root p q)=∑ a,(∑ i,if root i=a then (p i:ℤ)-q i else 0).natAbs := by
  have he : (List.range n).map (fun a => component (a,records root p q))=
      List.ofFn (fun a : Fin n => component (a.val,records root p q)) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro i hi _
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  unfold total
  rw [show (records root p q).length=n by simp only [records,List.length_ofFn]]
  rw [he,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a _
  exact component_records root p q a

end ContingencyTables.RootedComponentProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational assembly of the companion forest penalty

The natural root discrepancy and the finite list of tree affine forms
are combined by polynomial binary arithmetic to compute rationalD,
including the original maximum-forest cuts.
-/

namespace ContingencyTables.ForestPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionFactorialApplication CompanionOracleDensity ForestAssignmentSplit GraphCompletionCounts
open ForestScaledPenalty
open scoped BigOperators Classical

lemma penaltyCode_value (z : Input) :
    TreeFraction.val (penaltyCode z)=(z.1.1:ℚ)*
      ((z.1.2:ℚ)+(z.2.map (fun t => TreeFraction.val (ForestAffineProgram.evaluate t))).sum) := by
  rw [penaltyCode,TreeFraction.mul_val,TreeFraction.add_val _ _ (show (1:ℕ)≠0 from Nat.one_ne_zero) (by
    exact (TreeFraction.sum_den _).ne')]
  rw [show TreeFraction.val (z.1.1,1)=(z.1.1:ℚ) by simp [TreeFraction.val],
    show TreeFraction.val (z.1.2,1)=(z.1.2:ℚ) by simp [TreeFraction.val]]
  rw [treeSum,TreeFraction.sum_val]
  · simp only [List.map_map,Function.comp_def]
  · intro f hf
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hf
    exact RationalIntervalProgram.intervalCode_denominator _


lemma exponentCode_value (z : ExponentInput) :
    exponentCode z=⌊(z.1.1:ℚ)/z.1.2*TreeFraction.val (penaltyCode z.2)⌋₊ := by
  have h := FractionAcceptanceProgram.fraction_threshold 0 (weightedPenalty z)
  simp only [FairBits.rationalThreshold,pow_zero,one_mul,Nat.mul_one] at h
  rw [exponentCode,←h,weightedPenalty,TreeFraction.mul_val]
  rfl

end ContingencyTables.ForestPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledPenalty
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convexity and the physical scaled Lipschitz bound for selected roots -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedRootPenalty
open ForestScaledPenalty (intervalCost intervalCost_nonnegative intervalCost_change
  free_card_le tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem penalty_change (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (x q : I → J → ℤ)
    (v w : FreeCell A.small A.T → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ f,|v f-w f|≤ r) :
    |penalty A S C B x q v-penalty A S C B x q w|≤(2*C*(A.d:ℝ)^2/B)*r := by
  have hterm (t : TreeCell A.T) :
      |intervalCost (scaledTree A S B x q v t)-intervalCost (scaledTree A S B x q w t)|≤
        (A.d:ℝ)*(2/B)*r := by
    apply (intervalCost_change _ _).trans
    have hh := AffinePenalty.affineValue_change (normalizedOffset A S t x q)
      (normalizedCoefficient A S B t) v w (2/B) r (by positivity)
      (fun f => normalized_coefficient_bound A S t f.val B hB) hvw
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast free_card_le A) (by positivity : (0:ℝ)≤2/B)) hr)
  have he : penalty A S C B x q v-penalty A S C B x q w=
      C*∑ t : TreeCell A.T,(intervalCost (scaledTree A S B x q v t)-
        intervalCost (scaledTree A S B x q w t)) := by
    unfold penalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he,abs_mul,abs_of_nonneg hC]
  calc
    _≤ C*∑ t : TreeCell A.T,|intervalCost (scaledTree A S B x q v t)-
      intervalCost (scaledTree A S B x q w t)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hC
    _≤ C*∑ _t : TreeCell A.T,(A.d:ℝ)*(2/B)*r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hterm t)) hC
    _=C*((Fintype.card (TreeCell A.T):ℝ)*((A.d:ℝ)*(2/B)*r)) := by simp
    _≤ C*((A.d:ℝ)*((A.d:ℝ)*(2/B)*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by exact_mod_cast tree_card_le A) (by positivity)) hC
    _=_ := by ring

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedIntegerEvaluation
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral coefficients of the executed selected-root affine penalty -/

namespace ContingencyTables.RootedIntegerEvaluation

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit

variable {I J : Type*} [Fintype I] [Fintype J]

theorem numerator_div (A : Instance I J) (S : Selection A.T) (B : ℕ) (hB : 0<B)
    (t : TreeCell A.T) (x q : I → J → ℤ) (v : FreeCell A.small A.T → ℕ) :
    (numerator A S B t x q v:ℚ)/((B:ℚ)*A.b t.val.1 t.val.2)=
      rationalScaledTree A S B x q (fun f => (v f:ℚ)) t := by
  have hBQ : (B:ℚ)≠0 := by exact_mod_cast hB.ne'
  have hb : (A.b t.val.1 t.val.2:ℚ)≠0 := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (A.hlarge _ _ (A.hTG t.property)).2).ne'
  have hsum : (∑ f : FreeCell A.small A.T,
      ((coefficient A S t f.val:ℚ)*((A.b f.val.1 f.val.2:ℚ)+1)/B/
        (A.b t.val.1 t.val.2:ℚ))*(v f:ℚ))=
      (∑ f : FreeCell A.small A.T,
        (coefficient A S t f.val:ℚ)*((A.b f.val.1 f.val.2:ℚ)+1)*(v f:ℚ))/
        ((B:ℚ)*A.b t.val.1 t.val.2) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro f _
    field_simp [hBQ,hb]
  simp only [numerator,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_sum,Int.cast_one,
    rationalScaledTree,hsum]
  field_simp [hBQ,hb]

theorem evaluate_forest (A : Instance I J) (S : Selection A.T) (B : ℕ) (hB : 0<B)
    (t : TreeCell A.T) (x y : I → J → ℤ)
    {n : ℕ} (e : Fin n ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    MatchingFPRAS.TreeFraction.val (ForestAffineProgram.evaluate (forestData A S B t x y e v))=
      max 0 (max (-rationalScaledTree A S B x y (fun f => (v f:ℚ)) t)
        (rationalScaledTree A S B x y (fun f => (v f:ℚ)) t-1)) := by
  have hb := (A.hlarge _ _ (A.hTG t.property)).2
  have hn : (((B:ℤ)*offset A S t x y:ℤ):ℚ)+
      ∑ i : Fin n,
        ((coefficient A S t (e i).val*((A.b (e i).val.1 (e i).val.2:ℤ)+1):ℤ):ℚ)*
          (v (e i):ℚ)=(numerator A S B t x y v:ℚ) := by
    simp only [numerator,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,Int.cast_sum]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold forestData
  rw [ForestAffineProgram.evaluate_data _ _ _ _ (Nat.mul_pos hB hb),hn,Nat.cast_mul,
    numerator_div A S B hB]

end ContingencyTables.RootedIntegerEvaluation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary penalty evaluation for the selected-root forest

The signed affine and fraction programs compute the root-specific
geometric penalty from its explicit input metadata.
-/

namespace ContingencyTables.RootedPenaltyProgram

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open MatchingFPRAS RootedIntegerEvaluation

variable {I J : Type*} [Fintype I] [Fintype J]

theorem penaltyCode_data (A : Instance I J) (S : Selection A.T) (C : ℕ) (hC : 0<C)
    (x q : I → J → ℤ) {nt nf : ℕ}
    (trees : Fin nt ≃ TreeCell A.T) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (ForestPenaltyProgram.penaltyCode (data A S C x q trees free v))=
      rationalPenalty A S C x q (fun f => (v f:ℚ)) := by
  have hB : 0<CompanionOracleDensity.rationalBinWidth A C := by
    unfold CompanionOracleDensity.rationalBinWidth
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one A.hd) _)
  rw [ForestPenaltyProgram.penaltyCode_value]
  simp only [data,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    evaluate_forest A S _ hB]
  unfold rationalPenalty
  congr 2
  exact Fintype.sum_equiv trees _ _ (fun _ => rfl)

theorem exponentCode_data (A : Instance I J) (S : Selection A.T) (C a : ℕ) (hC : 0<C)
    (x q : I → J → ℤ) {nt nf : ℕ}
    (trees : Fin nt ≃ TreeCell A.T) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    ForestPenaltyProgram.exponentCode
        ((a,CompanionOracleDensity.rationalHeight A C),data A S C x q trees free v)=
      ⌊(a:ℚ)/CompanionOracleDensity.rationalHeight A C*
        rationalPenalty A S C x q (fun f => (v f:ℚ))⌋₊ := by
  rw [ForestPenaltyProgram.exponentCode_value,penaltyCode_data A S C hC]

end ContingencyTables.RootedPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentSemantics
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed component sums equal the root penalty

The root-only filter in the manuscript costs no separate test: every
nonroot has an empty root fibre.  This connects the polynomial grouped
signed-sum program to the actual selected-root discrepancy.
-/

namespace ContingencyTables.RootedComponentProgram

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

lemma componentTotal_zero (A : Instance I J) (S : Selection A.T)
    (d : I⊕J → ℤ) (a : I⊕J) (ha : a≠S.root a) :
    RootedRootPenalty.componentTotal A S d a=0 := by
  have hroot (v : I⊕J) : S.root v≠a := by
    intro hv
    apply ha
    calc
      a=S.root v := hv.symm
      _=S.root (S.root v) := (S.idempotent v).symm
      _=S.root a := congrArg S.root hv
  unfold RootedRootPenalty.componentTotal
  apply Finset.sum_eq_zero
  intro v _
  simp only [hroot v,ite_false,zero_mul]

theorem rootCount_eq_componentTotals (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) :
    RootedPenaltyProgram.rootCount A S x q=
      ∑ a,(RootedRootPenalty.componentTotal A S
        (ForestRootPenalty.smallDemand A.small A.X x q) a).natAbs := by
  unfold RootedPenaltyProgram.rootCount
  simp_rw [RootedRootPenalty.signedResidual_eq_small,Int.natAbs_neg]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a=S.root a
  · have hflag : RootedPenalty.rootFlag S a=true := decide_eq_true ha
    exact ite_eq_left hflag
  · rw [componentTotal_zero A S _ a ha]
    simp only [Int.natAbs_zero,ite_self]

/-- The positive and negative entries may be the actual row and column
small-view sums. Their difference is the only representation invariant
needed by the finite signed component program. -/
theorem total_records_rootCount (A : Instance I J) (S : Selection A.T)
    (x q : I → J → ℤ) {n : ℕ} (e : Fin n ≃ I⊕J) (p m : Fin n → ℕ)
    (hd : ∀ i,(p i:ℤ)-m i=ForestRootPenalty.smallDemand A.small A.X x q (e i)) :
    total (records (fun i => e.symm (S.root (e i))) p m)=
      RootedPenaltyProgram.rootCount A S x q := by
  have hs (a : Fin n) :
      (∑ i,if e.symm (S.root (e i))=a then (p i:ℤ)-m i else 0)=
        RootedRootPenalty.componentTotal A S
          (ForestRootPenalty.smallDemand A.small A.X x q) (e a) := by
    calc
      _=∑ i,if S.root (e i)=e a then
          ForestRootPenalty.smallDemand A.small A.X x q (e i) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hd i]
        simp only [Equiv.symm_apply_eq]
      _=∑ v,if S.root v=e a then
          ForestRootPenalty.smallDemand A.small A.X x q v else 0 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _=_ := by
        simp only [RootedRootPenalty.componentTotal,ite_mul,one_mul,zero_mul]
  rw [total_records]
  calc
    _=∑ a,(RootedRootPenalty.componentTotal A S
        (ForestRootPenalty.smallDemand A.small A.X x q) (e a)).natAbs := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hs]
    _=∑ a,(RootedRootPenalty.componentTotal A S
        (ForestRootPenalty.smallDemand A.small A.X x q) a).natAbs :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _=_ := (rootCount_eq_componentTotals A S x q).symm

end ContingencyTables.RootedComponentProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphRootProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program computing a component root

The graph is supplied by adjacency lists. The program makes one growth
round per stored vertex, then minimizes the reached indices. No loop
depends on the numeric size of an index or of an edge capacity.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.TreeTyped Polynomial

lemma minimum_fold_le (xs : List ℕ) (b : ℕ) :
    xs.foldl (fun b a => min a b) b≤b := by
  induction xs generalizing b with
  | nil => exact le_rfl
  | cons a xs ih => exact (ih (min a b)).trans (min_le_right _ _)

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphRootSemantics
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact correctness of the finite component-root program

The stored adjacency list is identified with the given finite graph.
Each list growth round is the proved finite reachability growth, and
the final binary minimum is the least vertex of the actual component.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma grow_bound (rows : GraphCode) (s : List ℕ) {a : ℕ}
    (ha : a∈grow (rows,s)) : a < rows.length := by
  exact List.mem_range.mp (List.mem_of_mem_filter ha)

lemma iterate_bound (v : Fin n) (k : ℕ) :
    ∀ a∈(fun s => grow (graphCode G,s))^[k] [v.val],a<n := by
  cases k with
  | zero =>
    intro a ha
    simp only [Function.iterate_zero_apply,List.mem_singleton] at ha
    exact ha ▸ v.isLt
  | succ k =>
    intro a ha
    rw [Function.iterate_succ_apply'] at ha
    simpa only [graphCode_length] using grow_bound _ _ ha

lemma reached_bound (v : Fin n) {a : ℕ} (ha : a∈reached (graphCode G,v.val)) : a<n := by
  rw [reached_eq_iterate] at ha
  exact iterate_bound G v n a ha

lemma minimum_fold_le_of_mem (xs : List ℕ) (b a : ℕ) (ha : a∈xs) :
    xs.foldl (fun b a => min a b) b≤a := by
  induction xs generalizing b with
  | nil => simp only [List.not_mem_nil] at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with h|ha
    · subst x
      exact (minimum_fold_le xs (min a b)).trans (min_le_left _ _)
    · exact ih (min x b) ha

lemma le_minimum_fold (xs : List ℕ) (b a : ℕ) (hb : a≤b)
    (hs : ∀ x∈xs,a≤x) : a≤xs.foldl (fun b x => min x b) b := by
  induction xs generalizing b with
  | nil => exact hb
  | cons x xs ih =>
    exact ih (min x b) (le_min (hs x (by simp)) hb)
      (fun y hy => hs y (by simp [hy]))

/-- The executed least root agrees with the explicit mathematical
selector. It does not identify that selector with a quotient choice. -/
theorem rootCode_eq (v : Fin n) :
    rootCode (graphCode G,v.val)=(FiniteGraphRoots.root G v).val := by
  unfold rootCode
  rw [graphCode_length]
  apply le_antisymm
  · exact minimum_fold_le_of_mem _ _ _ ((reached_mem_iff G v _).mpr
      (FiniteGraphRoots.root_reachable G v))
  · apply le_minimum_fold _ _ _ (FiniteGraphRoots.root G v).isLt.le
    intro a ha
    let u : Fin n := ⟨a,reached_bound G v ha⟩
    have hr : G.Reachable v u := (reached_mem_iff G v u).mp ha
    exact FiniteGraphRoots.root_le G hr

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every root label before summing its signed demand

The input contains an adjacency list and one positive/negative demand
pair per vertex. The polynomial program computes the root labels itself.
-/

namespace ContingencyTables.RootedComponentCode

open MatchingFPRAS.TreeTyped Polynomial
open RootedCompletion RootedComponentProgram FiniteGraphRootProgram
open scoped BigOperators Classical

lemma labels_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p q : Fin n → ℕ) :
    labels (FiniteGraphRootProgram.graphCode G,List.ofFn (fun i => (p i,q i)))=
      records (FiniteGraphRoots.root G) p q := by
  apply List.ext_getElem
  · simp only [labels,List.length_map,List.length_range,List.length_ofFn,records]
  · intro i hi hj
    have hin : i<n := by
      simpa only [records,List.length_ofFn] using hj
    simp only [labels,List.getElem_map,List.getElem_range,entry,records,List.getElem_ofFn]
    rw [FiniteGraphRootProgram.rootCode_eq G ⟨i,hin⟩]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hin,dite_true,Option.getD_some]

open CompanionFactorialApplication

end ContingencyTables.RootedComponentCode

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphCutSemantics
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact edge-deletion and cut-metadata computation -/

namespace ContingencyTables.FiniteGraphCutProgram

open SimpleGraph FiniteGraphRootProgram

lemma keep_eq_true_iff (u v i a : ℕ) :
    keep (((u,v),i),a)=true ↔ ¬(i=u ∧ a=v) ∧ ¬(i=v ∧ a=u) := by
  unfold keep
  split_ifs <;> simp_all

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma deleteRow_graph (u v i : Fin n) :
    deleteRow ((graphCode G,(u.val,v.val)),i.val)=
      adjacencyRow (G.deleteEdges {s(u,v)}) i := by
  unfold deleteRow
  rw [graphCode_getD]
  unfold adjacencyRow
  rw [List.filter_map,List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,keep_eq_true_iff,
    SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff,Fin.ext_iff]
  tauto

theorem deleteGraph_graph (u v : Fin n) :
    deleteGraph (graphCode G,(u.val,v.val))=graphCode (G.deleteEdges {s(u,v)}) := by
  apply List.ext_getElem
  · simp only [deleteGraph,List.length_map,indices,List.length_range,graphCode_length]
  · intro i hi _
    have hi' : i<n := by
      simpa only [deleteGraph,List.length_map,indices,List.length_range,graphCode_length] using hi
    simp only [deleteGraph,indices,List.getElem_map,List.getElem_range]
    rw [deleteRow_graph G u v ⟨i,hi'⟩]
    simp only [graphCode,List.getElem_ofFn]

lemma reachableCode_graph (u v : Fin n) :
    reachableCode ((graphCode G,u.val),v.val)=decide (G.Reachable u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [reachableCode,decide_eq_true_eq,reached_mem_iff]

theorem awayCode_graph (u v root : Fin n) :
    awayCode ((graphCode G,(u.val,v.val)),root.val)=
      (RootedCut.away G u v root).val := by
  unfold awayCode
  rw [deleteGraph_graph,reachableCode_graph]
  simp only [RootedCut.away,decide_eq_true_eq]
  split_ifs <;> rfl

/-- The executed Boolean metadata is the selected root-away cut in the
actual graph, rather than an arbitrary precomputed cut oracle. -/
theorem cutCode_graph (u v root a : Fin n) :
    cutCode (((graphCode G,(u.val,v.val)),root.val),a.val)=
      RootedCut.cut G u v root a := by
  unfold cutCode
  rw [deleteGraph_graph,awayCode_graph,reachableCode_graph]
  apply Bool.eq_iff_iff.mpr
  simp only [RootedCut.cut,MaximumForest.side,decide_eq_true_eq]

theorem canonicalCutCode_graph (u v a : Fin n) :
    canonicalCutCode ((graphCode G,(u.val,v.val)),a.val)=
      RootedCut.cut G u v (FiniteGraphRoots.root G u) a := by
  unfold canonicalCutCode
  rw [rootCode_eq,cutCode_graph]

end ContingencyTables.FiniteGraphCutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCutReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact canonical cut flags in the row-then-column vertex encoding -/

namespace ContingencyTables.RootedCutReindex

open SimpleGraph RootedCompletion
open scoped Classical

variable {V W : Type*}

lemma delete_comap (G : SimpleGraph V) (e : W ≃ V) (u v : W) :
    (G.comap e).deleteEdges {s(u,v)}=(G.deleteEdges {s(e u,e v)}).comap e := by
  ext a b
  simp only [SimpleGraph.deleteEdges_adj,SimpleGraph.comap_adj,Set.mem_singleton_iff,
    Sym2.eq_iff,e.injective.eq_iff]

lemma reachable_comap (G : SimpleGraph V) (e : W ≃ V) (u v : W) :
    (G.comap e).Reachable u v ↔ G.Reachable (e u) (e v) := by
  constructor
  · intro h
    exact h.map (SimpleGraph.Iso.comap e G).toHom
  · intro h
    have hh := h.map (SimpleGraph.Iso.comap e G).symm.toHom
    change (G.comap e).Reachable (e.symm (e u)) (e.symm (e v)) at hh
    simpa only [Equiv.symm_apply_apply] using hh

lemma away_comap (G : SimpleGraph V) (e : W ≃ V) (u v root : W) :
    e (RootedCut.away (G.comap e) u v root)=RootedCut.away G (e u) (e v) (e root) := by
  unfold RootedCut.away
  rw [delete_comap,reachable_comap]
  split_ifs <;> rfl

lemma cut_comap (G : SimpleGraph V) (e : W ≃ V) (u v root a : W) :
    RootedCut.cut (G.comap e) u v root a=RootedCut.cut G (e u) (e v) (e root) (e a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [RootedCut.cut,MaximumForest.side,decide_eq_true_eq]
  rw [delete_comap,reachable_comap,away_comap]

/-- The Boolean program computes exactly the selected-root tree cut
used in the affine coefficient, with the concrete row/column order. -/
lemma canonicalCut_treeCut {m n : ℕ} (T : SimpleGraph (Fin m⊕Fin n))
    [DecidableRel T.Adj] (t : GraphCompletionCounts.TreeCell T) (a : Fin m⊕Fin n) :
    FiniteGraphCutProgram.canonicalCutCode
      ((FiniteGraphRootProgram.graphCode (T.comap finSumFinEquiv.symm),
        ((finSumFinEquiv (m := m) (n := n) (.inl t.val.1)).val,(finSumFinEquiv (m := m) (n := n) (.inr t.val.2)).val)),
        (finSumFinEquiv a).val)=RootedCut.treeCut T (rowColumn T) t a := by
  rw [FiniteGraphCutProgram.canonicalCutCode_graph]
  rw [cut_comap]
  simp only [RootedCut.treeCut,rowColumn_root,Equiv.symm_apply_apply]

end ContingencyTables.RootedCutReindex

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCoefficientProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing signed affine coefficients from the actual forest graph

The tree and cell endpoints are ordinary vertex indices. The program
computes the canonical cut flags, tests the capacity threshold and tree
adjacency, and returns the normalized signed coefficient.
-/

namespace ContingencyTables.RootedCoefficientProgram

open MatchingFPRAS.TreeTyped
open SignedPairProgram FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

lemma signs_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    value (signs (input A t a).1)=RootedIntegerEvaluation.sign A (rowColumn A.T) t a := by
  unfold signs input
  rw [RootedCutReindex.canonicalCut_treeCut,RootedCutReindex.canonicalCut_treeCut]
  cases hr : RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1) <;>
    cases hc : RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2) <;>
    simp [SignedPairProgram.value,bit,RootedIntegerEvaluation.sign,
      RootedIntegerEvaluation.integerIndicator,hr,hc]

lemma treeSigns_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    value (treeSigns (input A t a).1.1)=RootedIntegerEvaluation.sign A (rowColumn A.T) t t.val := by
  change value (signs (input A t t.val).1)=_
  exact signs_input A t t.val

lemma freeTest_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    freeTest (input A t a)=decide (A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)) := by
  have hcut : A.W ≤ A.b a.1 a.2 ↔ A.small a.1 a.2=false := by
    cases hs : A.small a.1 a.2 with
    | false => exact ⟨fun _ => rfl,fun _ => (A.hlarge _ _ hs).1⟩
    | true => simp only [Bool.true_eq_false,iff_false]; exact Nat.not_le.mpr (A.hsmall _ _ hs)
  unfold freeTest input
  rw [adjacent_graph]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,
    SimpleGraph.comap_adj,Equiv.symm_apply_apply,hcut]

/-- The output is the literal signed coefficient, with no supplied
cut-membership or coefficient-correctness assumption. -/
theorem coefficient_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    value (coefficient (input A t a))=RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a := by
  unfold coefficient RootedIntegerEvaluation.coefficient
  rw [freeTest_input]
  by_cases h : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  · simp [h,value_normalize,value_neg,value_times,signs_input,treeSigns_input]
  · simp [h,value]

end ContingencyTables.RootedCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOffsetProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the forest affine offset from the stored cell values

Every summand uses the executed cut flags and coefficient. The input
contains the baseline and the two stored views, rather than an affine
offset supplied by an oracle.
-/

namespace ContingencyTables.RootedOffsetProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped BigOperators Classical

lemma value_weightedDifference (z : WeightedInput) :
    value (weightedDifference z)=(z.1.1:ℤ)*value z.2.1-(z.1.2:ℤ)*value z.2.2 := by
  rw [weightedDifference,value_minus,value_times,value_times]
  rfl

lemma value_parts (z : ℤ) : value (ForestAffineProgram.signedParts z)=z :=
  ForestAffineProgram.signedParts_sub z

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

lemma smallTest_entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : smallTest (entry A t x q a)=A.small a.1 a.2 := by
  unfold smallTest cellInput entry RootedCoefficientProgram.input
  cases hs : A.small a.1 a.2 with
  | false => simp [(A.hlarge _ _ hs).1]
  | true => simp [Nat.not_le.mpr (A.hsmall _ _ hs)]

lemma cutTerm_entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : value (cutTerm (entry A t x q a))=
      integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) := by
  rw [cutTerm,value_weightedDifference]
  dsimp only [shifted,entry,cellInput]
  rw [value_minus,value_minus]
  simp only [value_parts]
  unfold RootedCoefficientProgram.signs RootedCoefficientProgram.input
  rw [RootedCutReindex.canonicalCut_treeCut,RootedCutReindex.canonicalCut_treeCut]
  cases hr : RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1) <;>
    cases hc : RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2) <;>
    simp [RootedCoefficientProgram.bit,integerIndicator]

lemma summand_entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : value (summand (entry A t x q a))=
      (if A.small a.1 a.2 then
        integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2)
        else 0)*sign A (rowColumn A.T) t t.val+
        RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a*A.X a.1 a.2 := by
  rw [summand,value_plus,value_times,value_times]
  have ht := RootedCoefficientProgram.treeSigns_input A t a
  have hc := RootedCoefficientProgram.coefficient_input A t a
  have hb : value (entry A t x q a).2=(A.X a.1 a.2:ℤ) := by
    exact value_parts _
  have hs : value (smallTerm (entry A t x q a))=
      if A.small a.1 a.2 then
        integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2)
        else 0 := by
    rw [smallTerm,smallTest_entry]
    split_ifs
    · exact cutTerm_entry A t x q a
    · rfl
  rw [hs,hb]
  rw [show (cellInput (entry A t x q a))=RootedCoefficientProgram.input A t a by rfl,ht,hc]

/-- The executed normalized pair is the exact manuscript affine offset. -/
theorem offset_data {m n N : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (e : Fin N ≃ Fin m×Fin n) :
    offset (data A t x q e)=ForestAffineProgram.signedParts
      (RootedIntegerEvaluation.offset A (rowColumn A.T) t x q) := by
  have he : (∑ i : Fin N,value (summand (entry A t x q (e i))))=
      ∑ a : Fin m×Fin n,value (summand (entry A t x q a)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [offset,normalize_eq]
  congr 1
  rw [value_minus,value_sum]
  simp only [data,List.map_ofFn,Function.comp_apply,List.sum_ofFn,value_parts]
  rw [he]
  simp only [summand_entry]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  unfold RootedIntegerEvaluation.offset RootedIntegerEvaluation.smallContribution
  ring

end ContingencyTables.RootedOffsetProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestDataProgram
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a tree penalty from executed coefficients and offsets

All signed affine data are computed internally from the graph, capacities,
baseline and two stored views. Only ordinary cell indices and values occur
in the input; no affine coefficient or offset is supplied.
-/

namespace ContingencyTables.RootedForestDataProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped Classical

lemma scale_value (n : ℕ) (z : Signed) :
    scale (n,z)=ForestAffineProgram.signedParts ((n:ℤ)*value z) := by
  rw [scale,normalize_eq,value_times]
  rfl

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation ForestAssignmentSplit

lemma term_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) (v : ℕ) :
    term (RootedCoefficientProgram.input A t a,v)=
      (ForestAffineProgram.signedParts
        (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a*((A.b a.1 a.2:ℤ)+1)),v) := by
  unfold term
  rw [scale_value,RootedCoefficientProgram.coefficient_input]
  simp only [RootedCoefficientProgram.input,Nat.cast_add,Nat.cast_one]
  congr 2
  ring

/-- The generated binary input equals the exact affine tree input used
by the selected-root penalty evaluation. -/
theorem prepare_data {m n nc nf : ℕ} (A : Instance (Fin m) (Fin n))
    (B : ℕ) (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (cells : Fin nc ≃ Fin m×Fin n) (free : Fin nf ≃ FreeCell A.small A.T)
    (v : FreeCell A.small A.T → ℕ) :
    prepare (data A B t x q cells free v)=
      RootedIntegerEvaluation.forestData A (rowColumn A.T) B t x q free v := by
  have ht : (List.ofFn (fun i : Fin nf =>
      (RootedCoefficientProgram.input A t (free i).val,v (free i)))).map term=
      List.ofFn (fun i : Fin nf => (ForestAffineProgram.signedParts
        (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t (free i).val*
          ((A.b (free i).val.1 (free i).val.2:ℤ)+1)),v (free i))) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact term_input A t (free i).val (v (free i))
  unfold prepare numeratorOffset data RootedIntegerEvaluation.forestData ForestAffineProgram.data
  rw [RootedOffsetProgram.offset_data,scale_value,ht]
  simp only [RootedOffsetProgram.value_parts]

end ContingencyTables.RootedForestDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCellDataProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling the affine input from ordinary rectangular cell arrays

The baseline and both stored views are binary natural matrices. The
program reads each cell once, computes its row/column vertex indices,
and constructs the offset evaluator input in row-major order.
-/

namespace ContingencyTables.RootedCellDataProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

open CompanionFactorialApplication RootedCompletion

lemma values_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) :
    values ((data A t x q).2,(i.val,j.val))=
      ((A.b i j,(A.X i j).toNat),(x i j,q i j)) := by
  simp only [values,data,matrixEntry_code]

lemma coefficientInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) :
    coefficientInput (data A t x q,(i.val,j.val))=RootedCoefficientProgram.input A t (i,j) := by
  simp only [coefficientInput,cellValues,values_data]
  simp only [endpoints,data,List.length_ofFn,RootedCoefficientProgram.input,
    finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]

lemma entry_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (i : Fin m) (j : Fin n) :
    entry (data A t x q,(i.val,j.val))=RootedOffsetProgram.entry A t
      (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) (i,j) := by
  have hx : ForestAffineProgram.signedParts (A.X i j)=((A.X i j).toNat,0) := by
    unfold ForestAffineProgram.signedParts
    rw [Int.toNat_of_nonpos (neg_nonpos.mpr (A.hX i j).1)]
  simp only [entry,coefficientInput_data,cellValues,values_data,RootedOffsetProgram.entry]
  rw [hx]
  simp only [ForestAffineProgram.signedParts,Int.toNat_natCast,Int.toNat_neg_natCast]

theorem offsetInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ) :
    offsetInput (data A t x q)=RootedOffsetProgram.data A t
      (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) finProdFinEquiv.symm := by
  have hx : ForestAffineProgram.signedParts (A.X t.val.1 t.val.2)=
      ((A.X t.val.1 t.val.2).toNat,0) := by
    unfold ForestAffineProgram.signedParts
    rw [Int.toNat_of_nonpos (neg_nonpos.mpr (A.hX t.val.1 t.val.2).1)]
  unfold offsetInput RootedOffsetProgram.data
  apply Prod.ext
  · simp only [data,baselineCell,List.length_ofFn,finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd,
      Nat.add_sub_cancel_left,matrixEntry_code,hx]
  · change (cellPairs (List.ofFn (fun i => (A.r i).toNat),
        List.ofFn (fun j => (A.c j).toNat))).map (fun a => entry (data A t x q,a))=_
    rw [DensePrograms.cellPairs_ofFn]
    simp only [List.map_ofFn]
    congr 1
    funext k
    exact entry_data A t x q (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

end ContingencyTables.RootedCellDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedDemandProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the root-demand input from the actual cell arrays

The two natural entries at a vertex encode its signed small-cell
discrepancy. They are formed by rectangular scans and then passed to the
component/root program.
-/

namespace ContingencyTables.RootedDemandProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms SignedPairProgram
open FiniteGraphRootProgram
open scoped BigOperators Classical

open CompanionFactorialApplication RootedCompletion

lemma values_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : ℕ) (i : Fin m) (j : Fin n) :
    values ((data A x q,v),(i.val,j.val))=
      ((A.b i j,(A.X i j).toNat),(x i j,q i j)) := by
  simp only [values,data,RootedForestCatalog.data,RootedCellDataProgram.values,matrixEntry_code]

lemma retainedTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : ℕ) (i : Fin m) (j : Fin n) :
    retainedTest ((data A x q,v),(i.val,j.val))=A.small i j := by
  unfold retainedTest RootedForestCatalog.largeTest
  simp only [data,RootedForestCatalog.data,matrixEntry_code]
  cases hs : A.small i j with
  | false => simp [(A.hlarge _ _ hs).1]
  | true => simp [Nat.not_le.mpr (A.hsmall _ _ hs)]

lemma rowTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (i : Fin m) (j : Fin n) :
    rowTest ((data A x q,(finSumFinEquiv v).val),(i.val,j.val))=decide (v=Sum.inl i) := by
  cases v with
  | inl a =>
    simp only [rowTest,finSumFinEquiv_apply_left,Fin.val_castAdd,Sum.inl.injEq,Fin.ext_iff]
    rfl
  | inr b =>
    have hi : i.val < m := i.isLt
    have hne : m+b.val≠i.val := by omega
    simp only [rowTest,finSumFinEquiv_apply_right,Fin.val_natAdd,hne,
      Sum.inr_ne_inl,decide_false]

lemma columnTest_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (i : Fin m) (j : Fin n) :
    columnTest ((data A x q,(finSumFinEquiv v).val),(i.val,j.val))=decide (v=Sum.inr j) := by
  apply Bool.eq_iff_iff.mpr
  cases v with
  | inl a =>
    simp only [columnTest,data,RootedForestCatalog.data,List.length_ofFn,
      finSumFinEquiv_apply_left,Fin.val_castAdd,decide_eq_true_eq,Sum.inl_ne_inr,iff_false]
    have ha := a.isLt
    omega
  | inr b =>
    simp only [columnTest,data,RootedForestCatalog.data,List.length_ofFn,
      finSumFinEquiv_apply_right,Fin.val_natAdd,decide_eq_true_eq,Sum.inr.injEq,
      Nat.add_left_cancel_iff,Fin.ext_iff]

lemma term_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) (i : Fin m) (j : Fin n) :
    value (term ((data A x q,(finSumFinEquiv v).val),(i.val,j.val)))=
      contribution A x q v (i,j) := by
  rw [term,retainedTest_data,rowTest_data,columnTest_data]
  by_cases hs : A.small i j=true <;> by_cases hr : v=Sum.inl i <;>
    by_cases hc : v=Sum.inr j
  all_goals simp [hs,hr,hc,rowPair,columnPair,values_data,
    contribution,value,SignedPairProgram.plus,Int.toNat_of_nonneg (A.hX i j).1]

lemma contribution_sum {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) :
    (∑ a : Fin m×Fin n,contribution A x q v a)=
      ForestRootPenalty.smallDemand A.small A.X
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) v := by
  cases v with
  | inl i =>
    have ht (k : Fin m) (j : Fin n) : contribution A x q (.inl i) (k,j)=
        if k=i then (if A.small i j then A.X i j-(x i j:ℤ) else 0) else 0 := by
      by_cases hk : k=i
      · subst k; simp [contribution]
      · simp [contribution,hk,Ne.symm hk]
    simp only [Fintype.sum_prod_type,ht]
    simp [ForestRootPenalty.smallDemand]
  | inr j =>
    have ht (i : Fin m) (k : Fin n) : contribution A x q (.inr j) (i,k)=
        if k=j then (if A.small i j then (q i j:ℤ)-A.X i j else 0) else 0 := by
      by_cases hk : k=j
      · subst k; simp [contribution]
      · simp [contribution,hk,Ne.symm hk]
    simp only [Fintype.sum_prod_type,ht]
    simp [ForestRootPenalty.smallDemand]

lemma demand_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) (v : Fin m⊕Fin n) :
    value (demand (data A x q,(finSumFinEquiv v).val))=
      ForestRootPenalty.smallDemand A.small A.X
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) v := by
  have hc : cellPairs (data A x q).1.1.2=
      List.ofFn (fun a : Fin (m*n) =>
        (((finProdFinEquiv : Fin m×Fin n≃Fin (m*n)).symm a).1.val,
          ((finProdFinEquiv : Fin m×Fin n≃Fin (m*n)).symm a).2.val)) :=
    DensePrograms.cellPairs_ofFn _ _
  rw [demand,value_sum,hc]
  simp only [List.map_ofFn,Function.comp_apply,List.sum_ofFn,term_data]
  calc
    _=∑ a : Fin m×Fin n,contribution A x q v a :=
      Fintype.sum_equiv (finProdFinEquiv : Fin m×Fin n≃Fin (m*n)).symm _ _ (fun _ => rfl)
    _=_ := contribution_sum A x q v

lemma demandList_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) :
    demandList (data A x q)=List.ofFn (fun i : Fin (m+n) => demand (data A x q,i.val)) := by
  apply List.ext_getElem
  · simp only [demandList,vertices,vertexCount,data,RootedForestCatalog.data,List.length_map,
      List.length_range,List.length_ofFn]
  · intro i hi hj
    simp only [demandList,vertices,vertexCount,data,RootedForestCatalog.data,List.length_ofFn,
      List.getElem_map,List.getElem_range,List.getElem_ofFn]

/-- The actual binary root program has exactly the selected-root penalty
value; no signed-demand representation assumption is supplied. -/
theorem rootCount_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (x q : Fin m → Fin n → ℕ) :
    rootCount (data A x q)=RootedPenaltyProgram.rootCount A (rowColumn A.T)
      (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) := by
  rw [rootCount,demandList_data]
  change RootedComponentCode.count
    (graphCode (A.T.comap finSumFinEquiv.symm),List.ofFn (fun i : Fin (m+n) =>
      ((demand (data A x q,i.val)).1,(demand (data A x q,i.val)).2)))=_
  rw [RootedComponentCode.count,RootedComponentCode.labels_graph]
  have ht := RootedComponentProgram.total_records_rootCount A (rowColumn A.T)
    (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ)) finSumFinEquiv.symm
    (fun i => (demand (data A x q,i.val)).1) (fun i => (demand (data A x q,i.val)).2)
    (fun i => by
      have h := demand_data A x q (finSumFinEquiv.symm i)
      simpa only [Equiv.apply_symm_apply,value] using h)
  simpa only [rowColumn_root,Equiv.apply_symm_apply,Equiv.symm_apply_apply] using ht

end ContingencyTables.RootedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Building tree-local inputs from the common raw arrays

The graph, capacity array, baseline and stored views are shared across
all tree terms. A term uses only its pair of cell indices; the program
builds its offset frame and reads the free-grid coordinates in catalog
order.
-/

namespace ContingencyTables.RootedTreeInputProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

lemma terms_ofFn {n : ℕ} (frame : RootedCellDataProgram.Input)
    (cells : Fin n → ℕ×ℕ) (v : Fin n → ℕ) :
    terms ((frame,List.ofFn cells),List.ofFn v)=
      List.ofFn (fun i => (RootedCellDataProgram.coefficientInput (frame,cells i),v i)) := by
  apply List.ext_getElem
  · simp only [terms,indices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hin : i<n := by simpa only [List.length_ofFn] using hj
    simp only [terms,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      termAt,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hin,dite_true,Option.getD_some,
      List.getElem_ofFn]

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

theorem treeInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ) :
    treeInput (RootedDemandProgram.data A x q,(t.val.1.val,t.val.2.val))=
      RootedCellDataProgram.data A t x q := by
  simp only [treeInput,edge,metadata,RootedDemandProgram.data,RootedForestCatalog.edge,
    RootedForestCatalog.data,RootedCellDataProgram.data,List.length_ofFn,
    finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_castAdd,Fin.val_natAdd]

theorem terms_data {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (v : FreeCell A.small A.T → ℕ) :
    terms ((treeInput (RootedDemandProgram.data A x q,(t.val.1.val,t.val.2.val)),
      RootedForestCatalog.catalog (RootedForestCatalog.data A,false)),
        List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i)))=
      List.ofFn (fun i =>
        (RootedCoefficientProgram.input A t ((RootedForestCatalog.freeEquiv A) i).val,
          v (RootedForestCatalog.freeEquiv A i))) := by
  have hf := congrArg (fun frame : RootedCellDataProgram.Input =>
    terms ((frame,RootedForestCatalog.catalog (RootedForestCatalog.data A,false)),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))))
    (treeInput_data A t x q)
  have hc := congrArg (fun cells : List (ℕ×ℕ) =>
    terms ((RootedCellDataProgram.data A t x q,cells),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))))
    (freeCatalog_ofFn A)
  refine hf.trans (hc.trans ((terms_ofFn (RootedCellDataProgram.data A t x q)
    (fun i => (((RootedForestCatalog.freeEquiv A) i).val.1.val,
      ((RootedForestCatalog.freeEquiv A) i).val.2.val))
    (fun i => v (RootedForestCatalog.freeEquiv A i))).trans ?_))
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun z => (z,v (RootedForestCatalog.freeEquiv A i)))
    (RootedCellDataProgram.coefficientInput_data A t x q
      ((RootedForestCatalog.freeEquiv A) i).val.1 ((RootedForestCatalog.freeEquiv A) i).val.2)

end ContingencyTables.RootedTreeInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestPrepareProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the whole selected-root forest penalty

The program takes the four cell arrays and the graph. It computes the
root discrepancy, both catalogs, every cut coefficient and every affine
offset before invoking the rational penalty evaluator.
-/

namespace ContingencyTables.RootedForestPrepareProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

theorem forestInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (B : ℕ)
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (v : FreeCell A.small A.T → ℕ) :
    forestInput (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),
        (t.val.1.val,t.val.2.val))=
      RootedForestDataProgram.data A B t (fun i j => (x i j:ℤ))
        (fun i j => (q i j:ℤ)) finProdFinEquiv.symm
        (RootedForestCatalog.freeEquiv A) v := by
  unfold forestInput RootedForestDataProgram.data
  apply Prod.ext
  · apply Prod.ext
    · simp only [widthCapacity,RootedDemandProgram.data,
        RootedForestCatalog.data,matrixEntry_code]
    · rw [treeFrame,RootedTreeInputProgram.treeInput_data,
        RootedCellDataProgram.offsetInput_data]
  · exact RootedTreeInputProgram.terms_data A t x q v

theorem prepareTree_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (B : ℕ)
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℕ)
    (v : FreeCell A.small A.T → ℕ) :
    prepareTree (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),
        (t.val.1.val,t.val.2.val))=
      RootedIntegerEvaluation.forestData A (rowColumn A.T) B t
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (RootedForestCatalog.freeEquiv A) v := by
  rw [prepareTree,forestInput_data,RootedForestDataProgram.prepare_data]

lemma treeCatalog_ofFn {m n : ℕ} (A : Instance (Fin m) (Fin n)) :
    RootedForestCatalog.catalog (RootedForestCatalog.data A,true)=
      List.ofFn (fun i => (((RootedForestCatalog.treeEquiv A) i).val.1.val,
        ((RootedForestCatalog.treeEquiv A) i).val.2.val)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact (RootedForestCatalog.catalogCell_coordinates A true ⟨i,hi⟩).symm

theorem prepare_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    prepare (data A C (CompanionOracleDensity.rationalBinWidth A C) x q v)=
      RootedPenaltyProgram.data A (rowColumn A.T) C
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) v := by
  have ht : prepareTrees (data A C (CompanionOracleDensity.rationalBinWidth A C) x q v)=
      List.ofFn (fun i => RootedIntegerEvaluation.forestData A (rowColumn A.T)
        (CompanionOracleDensity.rationalBinWidth A C) (RootedForestCatalog.treeEquiv A i)
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (RootedForestCatalog.freeEquiv A) v) := by
    change (RootedForestCatalog.catalog (RootedForestCatalog.data A,true)).map
      (fun a => prepareTree
        (((RootedDemandProgram.data A x q,CompanionOracleDensity.rationalBinWidth A C),
          List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a))=_
    have hc := congrArg (fun cells : List (ℕ×ℕ) => cells.map
      (fun a => prepareTree
        (((RootedDemandProgram.data A x q,CompanionOracleDensity.rationalBinWidth A C),
          List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a)))
      (treeCatalog_ofFn A)
    refine hc.trans ?_
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact prepareTree_data A _ (RootedForestCatalog.treeEquiv A i) x q v
  unfold prepare RootedPenaltyProgram.data
  apply Prod.ext
  · exact congrArg (fun r => (C,r)) (RootedDemandProgram.rootCount_data A x q)
  · exact ht

end ContingencyTables.RootedForestPrepareProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root geometric density is the literal completion weight -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedAffine RootedPhysicalCompletion RootedRootPenalty
open ForestScaledPenalty (integerCube intervalCost intervalCost_div )

variable {I J : Type*} [Fintype I] [Fintype J]

lemma free_coefficient_sum (A : Instance I J) (S : Selection A.T)
    (t : TreeCell A.T) (F : I×J → ℝ) :
    (∑ f : FreeCell A.small A.T,coefficient A S t f.val*F f.val)=
      ∑ a : I×J,coefficient A S t a*F a := by
  let p : I×J → Prop := fun a => A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  calc
    _=∑ a ∈ Finset.univ.filter p,coefficient A S t a*F a :=
      (Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun _ => by simp)
        (fun a => coefficient A S t a*F a)).symm
    _=_ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ ha
      have hp : ¬p a := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using ha
      change ¬(A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)) at hp
      simp only [coefficient,hp,ite_false,zero_mul]

theorem scaledTree_integer (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (x q : I → J → ℤ) (f : FreeIndex A.small A.T A.b) (t : TreeCell A.T) :
    scaledTree A S B x q (integerCube A B f) t=
      (solved A S x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
        t.val.1 t.val.2:ℝ)/(A.b t.val.1 t.val.2:ℝ) := by
  let F : I×J → ℝ := fun a => (freeTable A.small A.T A.b f a.1 a.2:ℝ)
  have hterm (a : FreeCell A.small A.T) :
      normalizedCoefficient A S B t a*integerCube A B f a=
        coefficient A S t a.val*F a.val/(A.b t.val.1 t.val.2:ℝ) := by
    have hN : (A.b a.val.1 a.val.2:ℝ)+1≠0 := by positivity
    have hbt : (A.b t.val.1 t.val.2:ℝ)≠0 := by
      exact_mod_cast (Nat.ne_of_gt (A.hlarge _ _ (A.hTG t.property)).2)
    have hF : F a.val=(f a).val := by simp [F,freeTable,a.property]
    rw [hF]
    unfold normalizedCoefficient integerCube
    field_simp [hB.ne',hN,hbt]
  unfold scaledTree AffinePenalty.affineValue normalizedOffset
  simp_rw [hterm]
  rw [←Finset.sum_div,free_coefficient_sum,←add_div]
  have hh := solved_eq_affine A S t x q (fun i j => (freeTable A.small A.T A.b f i j:ℤ))
  unfold affineTree AffinePenalty.affineValue at hh
  apply congrArg (fun z : ℝ => z/(A.b t.val.1 t.val.2:ℝ))
  simpa only [F,Int.cast_natCast] using hh.symm

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source height bounds the entire selected-root density cube -/

namespace ContingencyTables.RootedScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion GraphCompletionCounts ForestAssignmentSplit
open RootedRootPenalty RootedPhysicalCompletion BalancedBox
open ForestScaledPenalty (rowCounts columnCounts rowCounts_bounds columnCounts_bounds
  intervalCost intervalCost_div integerCube integerCube_zero zeroAssignment tree_card_le)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rootConstant_bound (A : Instance I J) (S : Selection A.T)
    (z : View A → ℕ) (hz : InBox (bounds A) z) :
    rootConstant A S (rowCounts A z) (columnCounts A z)≤2*(A.d:ℝ)*A.W := by
  let d := ForestRootPenalty.smallDemand A.small A.X (rowCounts A z) (columnCounts A z)
  have he (a : I⊕J) : (signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)=
      -(∑ v,if S.root v=a then (d v:ℝ) else 0) := by
    rw [signedResidual_eq_small]
    unfold componentTotal
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : S.root v=a <;> simp [hv,d]
  have hrow (i : I) : |((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|≤
      ∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |A.X i j-rowCounts A z i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(rowCounts_bounds A z hz i j hs).1,
          (rowCounts_bounds A z hz i j hs).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hcol (j : J) : |((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|≤
      ∑ i,if A.small i j then (A.b i j:ℝ) else 0 := by
    push_cast
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    by_cases hs : A.small i j=true
    · simp only [hs,ite_true, if_true]
      have hh : |columnCounts A z i j-A.X i j|≤(A.b i j:ℤ) := by
        apply abs_le.mpr
        constructor <;> linarith [(columnCounts_bounds A z i j).1,
          (columnCounts_bounds A z i j).2,(A.hX i j).1,(A.hX i j).2]
      exact_mod_cast hh
    · have hs' : A.small i j=false := Bool.eq_false_iff.mpr hs
      simp [hs']
  have hdemand : (∑ a,|(d a:ℝ)|)≤2*∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ i,|((∑ j,if A.small i j then A.X i j-rowCounts A z i j else 0:ℤ):ℝ)|)+
      (∑ j,|((∑ i,if A.small i j then columnCounts A z i j-A.X i j else 0:ℤ):ℝ)|)≤_
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
    rw [Finset.sum_comm] at hc
    linarith
  have hsmall : (∑ i,∑ j,if A.small i j then (A.b i j:ℝ) else 0)≤(A.d:ℝ)*A.W := by
    calc
      _≤∑ _i : I,∑ _j : J,(A.W:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        cases hs : A.small i j
        · simp only [Bool.false_eq_true,ite_false]
          positivity
        · simp only [ite_true, if_true]
          exact_mod_cast (A.hsmall i j hs).le
      _=(Fintype.card I*Fintype.card J:ℕ)*(A.W:ℝ) := by simp; ring
      _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast A.hcard) (Nat.cast_nonneg _)
  unfold rootConstant
  calc
    _≤∑ a,|(signedResidual A S (rowCounts A z) (columnCounts A z) 0 a:ℝ)| := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs <;> first | exact le_rfl | exact abs_nonneg _
    _=∑ a,|∑ v,if S.root v=a then (d v:ℝ) else 0| := by simp_rw [he,abs_neg]
    _≤∑ v,|(d v:ℝ)| := ForestRootPenalty.sum_abs_componentTotal S.root (fun v => (d v:ℝ))
    _≤_ := hdemand.trans (by linarith)

lemma zero_tree_bound (A : Instance I J) (S : Selection A.T) (B : ℝ) (hB : 0<B)
    (z : View A → ℕ) (hz : InBox (bounds A) z) (t : TreeCell A.T) :
    intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t)≤10*(A.d:ℝ) := by
  have hzero : (fun i j => (freeTable A.small A.T A.b (zeroAssignment A) i j:ℤ))=0 := by
    funext i j
    unfold freeTable zeroAssignment
    split_ifs <;> rfl
  have hinterval := RootedIntervals.solved_in_intervals A S
    (rowCounts A z) (columnCounts A z) 0
    (by intro i j hs; exact ⟨rowCounts_bounds A z hz i j hs,columnCounts_bounds A z i j⟩)
    (by intro i j _ _; exact ⟨le_rfl,Nat.cast_nonneg _⟩)
    t.val.1 t.val.2 t.property
  rw [←integerCube_zero A B,scaledTree_integer A S B hB,hzero,intervalCost_div]
  · have hb : (0:ℝ)<A.b t.val.1 t.val.2 := by exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2
    rw [div_le_iff₀ hb]
    have hlo : -(10*(A.d:ℝ)*A.b t.val.1 t.val.2)≤
        (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ) := by
      exact_mod_cast hinterval.1
    have hup : (solved A S (rowCounts A z) (columnCounts A z) 0 t.val.1 t.val.2:ℝ)≤
        10*(A.d:ℝ)*A.b t.val.1 t.val.2 := by exact_mod_cast hinterval.2
    apply max_le
    · positivity
    · apply max_le <;> linarith
  · exact_mod_cast (A.hlarge _ _ (A.hTG t.property)).2

theorem penalty_cube_bound (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (hB : 0<B) (z : View A → ℕ) (hz : InBox (bounds A) z)
    (v : FreeCell A.small A.T → ℝ) (hv : ∀ f,0≤ v f ∧ v f≤ B) :
    0≤ penalty A S C B (rowCounts A z) (columnCounts A z) v ∧
      penalty A S C B (rowCounts A z) (columnCounts A z) v≤ C*(10*(A.d:ℝ)^2*((A.W:ℝ)+1)) := by
  have hzero : penalty A S C B (rowCounts A z) (columnCounts A z) 0≤
      C*(2*(A.d:ℝ)*A.W+10*(A.d:ℝ)^2) := by
    unfold penalty
    apply mul_le_mul_of_nonneg_left _ hC
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => zero_tree_bound A S B hB z hz t)
    have ht : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B (rowCounts A z) (columnCounts A z) 0 t))≤
        10*(A.d:ℝ)^2 := by
      calc
        _≤(Fintype.card (TreeCell A.T):ℝ)*(10*(A.d:ℝ)) := by simpa using hsum
        _≤(A.d:ℝ)*(10*(A.d:ℝ)) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast tree_card_le A) (by positivity)
        _=_ := by ring
    linarith [rootConstant_bound A S z hz]
  have hchange := (le_abs_self _).trans (penalty_change A S C B hC hB
    (rowCounts A z) (columnCounts A z) v 0 B hB.le (by
      intro f
      simpa only [Pi.zero_apply,sub_zero,abs_of_nonneg (hv f).1] using (hv f).2))
  have hcancel : (2*C*(A.d:ℝ)^2/B)*B=2*C*(A.d:ℝ)^2 := div_mul_cancel₀ _ hB.ne'
  rw [hcancel] at hchange
  have hd : (1:ℝ)≤ A.d := by exact_mod_cast A.hd
  have hW : (2:ℝ)≤ A.W := by exact_mod_cast A.hW
  have hscalar : 2*(A.d:ℝ)*A.W+12*(A.d:ℝ)^2≤10*(A.d:ℝ)^2*((A.W:ℝ)+1) := by
    have hdd : (A.d:ℝ)≤(A.d:ℝ)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hdd (by positivity : (0:ℝ)≤ A.W)
    have hp' := mul_le_mul_of_nonneg_left hW (sq_nonneg (A.d:ℝ))
    nlinarith
  refine ⟨penalty_nonnegative A S C B hC _ _ v,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hscalar hC]

end ContingencyTables.RootedScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root evaluator density on its actual finite bin cube -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit
open CompanionOracleDensity (dimension index pull binWidth height)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem D_bounds (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Fin (dimension A) → ℝ) (hv : ∀ i,0≤ v i ∧ v i≤ binWidth A C) :
    0≤ D A S C z v ∧ D A S C z v≤ height A C := by
  have hh := RootedScaledPenalty.penalty_cube_bound A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC) z hz (pull A v)
    (fun f => hv ((index A).symm f))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  unfold height
  ring

theorem D_change (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0<C)
    (z : View A → ℕ) (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ i,|v i-w i|≤ r) : |D A S C z v-D A S C z w|≤ r/8 := by
  have hh := RootedScaledPenalty.penalty_change A S C (binWidth A C) hC.le
    (CompanionOracleDensity.binWidth_positive A C hC)
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)
    (pull A v) (pull A w) r hr (fun f => hvw ((index A).symm f))
  have hd : (A.d:ℝ)≠0 := by exact_mod_cast (show A.d≠0 by have hh := A.hd; omega)
  have he : (2*C*(A.d:ℝ)^2/binWidth A C)*r=r/8 := by
    unfold binWidth
    field_simp [hC.ne',hd]
    ring
  simpa only [D,he] using hh

theorem exponent_change (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (r : ℝ) (hr : 0≤ r)
    (hvw : ∀ i,|v i-w i|≤ r) :
    |(a/height A C)*D A S C z v-(a/height A C)*D A S C z w|≤ r/8 := by
  have hH := CompanionOracleDensity.height_positive A C hC
  have hf0 : 0≤ a/height A C := div_nonneg ha hH.le
  have hf1 : a/height A C≤1 := (div_le_one hH).mpr haH
  rw [←mul_sub,abs_mul,abs_of_nonneg hf0]
  exact (mul_le_mul_of_nonneg_left (D_change A S C hC z v w r hr hvw) hf0).trans
    (mul_le_of_le_one_left (by positivity) hf1)

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed-root grid weights are exactly dyadic rational values -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts GridBoundary
open CompanionOracleDensity (dimension index height rationalHeight naturalBin)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem exponentCode_grid (A : Instance I J) (S : Selection A.T) (C a : ℕ) (hC : 0<C)
    (z : View A → ℕ) {nt nf K : ℕ} (trees : Fin nt ≃ TreeCell A.T)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : Grid (I := Fin (dimension A)) K) :
    ForestPenaltyProgram.exponentCode ((a,rationalHeight A C),RootedPenaltyProgram.data A S C
      (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)
      trees free (naturalBin A v))=gridExponent A S C a z v := by
  have he : (fun f : FreeCell A.small A.T => (naturalBin A v f:ℚ))=
      (fun f => (corner v ((index A).symm f):ℚ)) := by
    funext f
    exact_mod_cast CompanionOracleDensity.naturalBin_cast A v f
  rw [RootedPenaltyProgram.exponentCode_data A S C a hC]
  unfold gridExponent rationalD
  rw [he]

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyEvaluateProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the actual forest exponent

The bin width and height are computed from the dimension allowance,
capacity scale and phase coefficient. All forest metadata is generated
from the cell arrays by `RootedForestPrepareProgram`.
-/

namespace ContingencyTables.RootedPenaltyEvaluateProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

lemma width_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ) :
    width ((A.d,A.W),(C,a))=CompanionOracleDensity.rationalBinWidth A C := by
  simp only [width,scaledSquare,squareDimension,CompanionOracleDensity.rationalBinWidth,pow_two]
  ring

theorem exponentInput_data {m n : ℕ} (A : Instance (Fin m) (Fin n)) (C a : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    exponentInput (data A C a x q v)=
      ((a,CompanionOracleDensity.rationalHeight A C),
        RootedPenaltyProgram.data A (rowColumn A.T) C
          (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
          (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) v) := by
  unfold exponentInput data forestInput
  rw [width_data,height_data]
  exact congrArg (fun p => ((a,CompanionOracleDensity.rationalHeight A C),p))
    (RootedForestPrepareProgram.prepare_data A C x q v)

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogGrid
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed catalog coordinates for the oracle grid

The executable free-cell order need not agree with `Fintype.equivFin`.
Explicit reindexing identifies the grid exponent evaluated from the
catalog-ordered list.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion
open scoped Classical

noncomputable section
variable {m n : ℕ}

lemma gridEquiv_free (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) (f : FreeCell A.small A.T) :
    gridEquiv A K v ((CompanionOracleDensity.index A).symm f)=
      v ((RootedForestCatalog.freeEquiv A).symm f) := by
  change v ((coordinateEquiv A).symm ((CompanionOracleDensity.index A).symm f))=_
  simp only [coordinateEquiv,Equiv.symm_trans_apply,Equiv.symm_symm,
    Equiv.apply_symm_apply]

theorem naturalBin_grid (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) :
    CompanionOracleDensity.naturalBin A (gridEquiv A K v)=naturalValues A v := by
  funext f
  unfold CompanionOracleDensity.naturalBin naturalValues
  rw [gridEquiv_free]

theorem naturalValues_list (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) :
    List.ofFn (fun i => naturalValues A v (RootedForestCatalog.freeEquiv A i))=
      List.ofFn (fun i => (v i).val.toNat) := by
  apply congrArg List.ofFn
  funext i
  simp only [naturalValues,Equiv.symm_apply_apply]

theorem evaluatorInput_grid (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : Grid (I := Fin (freeCount A)) K) :
    RootedPenaltyEvaluateProgram.data A C a x q (naturalValues A v)=
      (((A.d,A.W),(C,a)),(RootedDemandProgram.data A x q,
        List.ofFn (fun i => (v i).val.toNat))) := by
  unfold RootedPenaltyEvaluateProgram.data
  rw [naturalValues_list]

/-- Catalog-order evaluation is exactly the grid
exponent after reindexing. The runtime code never uses this equivalence. -/
theorem evaluate_grid (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (freeCount A)) K) :
    RootedPenaltyEvaluateProgram.evaluate
      (((A.d,A.W),(C,a)),
        (RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
          (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j),
          List.ofFn (fun i => (v i).val.toNat)))=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z (gridEquiv A K v) := by
  rw [←evaluatorInput_grid]
  rw [RootedPenaltyEvaluateProgram.evaluate,RootedPenaltyEvaluateProgram.exponentInput_data]
  have h := RootedOracleDensity.exponentCode_grid A (rowColumn A.T) C a hC z
    (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) (gridEquiv A K v)
  rw [naturalBin_grid] at h
  exact h

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinPopulationProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact population correction in binary

The program multiplies one interval size and one full-range denominator
per free coordinate. It never lists the integer assignments in a bin.
-/

namespace ContingencyTables.BinPopulationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma output_ofFn {q : ℕ} (K : ℕ) (N beta : Fin q → ℕ) :
    TreeFraction.val (output (List.ofFn (fun i => ((K,N i),beta i))))=
      (K:ℚ)^q*(∏ i : Fin q,(CompanionOracleDensity.intervalSize K (N i) (beta i):ℚ))/
        ∏ i : Fin q,(N i:ℚ) := by
  rw [output,TreeFraction.normalize_val]
  simp only [numerator,denominator,List.map_ofFn,Function.comp_apply,List.prod_ofFn,
    factorNumerator,BinIntervalProgram.intervalSize_eq,TreeFraction.val,
    Nat.cast_prod,Nat.cast_mul,Nat.cast_pow,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin]

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

noncomputable section
variable {m n : ℕ}

theorem output_data (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0<K)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K) :
    TreeFraction.val (output (data A K v))=
      (K:ℚ)^CompanionOracleDensity.dimension A*
        (CompanionOracleDensity.integerFiber A K hK v).card/
          CompanionOracleDensity.assignmentCount A := by
  rw [data,output_ofFn]
  have hc : RootedCatalogGrid.freeCount A=CompanionOracleDensity.dimension A := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (RootedCatalogGrid.coordinateEquiv A)
  have hp : (∏ i : Fin (RootedCatalogGrid.freeCount A),
      (CompanionOracleDensity.intervalSize K
        (CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i))
        (CompanionOracleDensity.naturalBin A v (RootedForestCatalog.freeEquiv A i)):ℚ))=
      ((CompanionOracleDensity.integerFiber A K hK v).card:ℚ) := by
    rw [CompanionOracleDensity.integerFiber_card,Nat.cast_prod]
    apply Fintype.prod_equiv (RootedForestCatalog.freeEquiv A)
    intro i
    have hN : 0<CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i) := by
      exact Nat.succ_pos _
    rw [FairBits.fiber_card hK hN
      (CompanionOracleDensity.naturalBin_lt A v _)]
    rfl
  have hd : (∏ i : Fin (RootedCatalogGrid.freeCount A),
      (CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i):ℚ))=
      (CompanionOracleDensity.assignmentCount A:ℚ) := by
    rw [CompanionOracleDensity.assignmentCount_eq_prod,Nat.cast_prod]
    exact Fintype.prod_equiv (RootedForestCatalog.freeEquiv A) _ _ (fun _ => rfl)
  rw [hp,hd,hc]

theorem output_integerBin (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0<K)
    (f : FreeIndex A.small A.T A.b) :
    TreeFraction.val (output (data A K (CompanionOracleDensity.integerBin A K hK f)))=
      CompanionOracleDensity.rationalPopulation A K hK f :=
  output_data A K hK _

end
end ContingencyTables.BinPopulationProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinVectorProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed independent bin-coordinate draws

Each coordinate reserves a width determined by its full range, and
uses only the prefix needed by the selected interval. The implementation
splits one Boolean list and performs binary arithmetic per coordinate.
-/

namespace ContingencyTables.BinVectorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators

lemma take_ofFn_prefix {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (List.ofFn bits).take k=List.ofFn (FirstSuccess.prefixWord hk bits) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left hk]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,FirstSuccess.prefixWord,Fin.castLE]

theorem output_ofFn {q : ℕ} (frames : Fin q → Frame)
    (bits : Fin (∑ i,reservedWidth (frames i)) → Bool) :
    output (List.ofFn frames,List.ofFn bits)=
      List.ofFn (fun i => coordinate (frames i,List.ofFn (fun j : Fin (reservedWidth (frames i)) =>
        bits (finSigmaFinEquiv ⟨i,j⟩)))) := by
  have hw : widths (List.ofFn frames,List.ofFn bits)=
      List.ofFn (fun i => reservedWidth (frames i)) := by
    simp only [widths,List.map_ofFn,Function.comp_def]
  apply List.ext_getElem
  · simp only [output,indices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hj
    have hiq : i<q := by simpa only [List.length_ofFn] using hj
    have hd := dependentChunk_ofFn (fun i => reservedWidth (frames i)) bits (⟨i,hiq⟩ : Fin q)
    simp only [output,indices,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,item,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hiq,dite_true,
      Option.getD_some,hw]
    exact congrArg (fun b => coordinate (frames ⟨i,hiq⟩,b)) hd

end ContingencyTables.BinVectorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DyadicRootBisection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer implementation of the correction-root bisection

The two interval endpoints share one dyadic denominator. Every comparison
is an inequality between natural powers and products. This is the literal
integer algorithm to which the rational correction analysis is applied.
-/

namespace ContingencyTables.DyadicRootBisection

open MatchingFPRAS

lemma compare_iff (a d p q s : ℕ) (hd : 0<d) (hq : 0<q) :
    ((a:ℚ)/d)^s ≤ (p:ℚ)/q ↔ a^s*q≤p*d^s := by
  rw [div_pow,div_le_div_iff₀ (pow_pos (by exact_mod_cast hd) _)
    (by exact_mod_cast hq)]
  norm_cast

lemma advance_denominator (c : TreeFraction.Fraction) (s : ℕ) (z : State) :
    (advance c s z).2=2*z.2 := by
  unfold advance
  split_ifs <;> rfl

lemma run_denominator (c : TreeFraction.Fraction) (s n : ℕ) :
    (run c s n).2=2^n := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [run,advance_denominator,ih,pow_succ,mul_comm]

lemma value_advance (c : TreeFraction.Fraction) (hc : 0 < c.2)
    (s : ℕ) (z : State) (hz : 0<z.2) :
    value (advance c s z)=
      let ab:=value z
      let mid:=(ab.1+ab.2)/2
      if mid^s≤TreeFraction.val c then (mid,ab.2) else (ab.1,mid) := by
  have hD : (z.2:ℚ)≠0 := by exact_mod_cast hz.ne'
  have hm : (((z.1.1:ℚ)/z.2)+((z.1.2:ℚ)/z.2))/2=
      ((z.1.1+z.1.2:ℕ):ℚ)/((2*z.2:ℕ):ℚ) := by
    push_cast
    field_simp [hD]
  have hleft : ((2*z.1.1:ℕ):ℚ)/((2*z.2:ℕ):ℚ)=(z.1.1:ℚ)/z.2 := by
    push_cast
    field_simp [hD]
  have hright : ((2*z.1.2:ℕ):ℚ)/((2*z.2:ℕ):ℚ)=(z.1.2:ℚ)/z.2 := by
    push_cast
    field_simp [hD]
  have ht:=compare_iff (z.1.1+z.1.2) (2*z.2) c.1 c.2 s (by omega) hc
  dsimp only [value,TreeFraction.val]
  rw [hm]
  by_cases h : (z.1.1+z.1.2)^s*c.2 ≤ c.1*(2*z.2)^s
  · simp only [advance,h,ite_true, if_true,ht.mpr h,hright]
  · have hr := mt ht.mp h
    simp only [advance,h,ite_false,hr,hleft]

/-- Every integer execution is the rational bisection used by the
already proved relative-error estimate. -/
theorem run_value (c : TreeFraction.Fraction) (hc : 0 < c.2) (s n : ℕ) :
    value (run c s n)=RationalRootBisection.interval (TreeFraction.val c) s n := by
  induction n with
  | zero=>norm_num [run,value,RationalRootBisection.interval]
  | succ n ih=>
    rw [run,value_advance c hc s _ (by rw [run_denominator]; positivity),ih]
    rfl

theorem output_value (c : TreeFraction.Fraction) (hc : 0 < c.2) (s n : ℕ) :
    TreeFraction.val (output c s n)=
      RationalRootBisection.midpoint (TreeFraction.val c) s n := by
  have he:=run_value c hc s n
  unfold output
  rw [TreeFraction.normalize_val]
  unfold RationalRootBisection.midpoint
  rw [←he]
  dsimp only [value,TreeFraction.val]
  have hD : ((run c s n).2:ℚ)≠0 := by rw [run_denominator]; positivity
  push_cast
  field_simp [hD]

end ContingencyTables.DyadicRootBisection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicRootProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the rational correction bisection

The root degree is the length of a supplied allowance list. One fixed
depth list controls the outer loop. Thus both natural-power evaluation
and the bisection loop have polynomial cost in the supplied binary data
and the two explicit allowances.
-/

namespace ContingencyTables.DyadicRootProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma markedPower_eq (a : ℕ) (xs : List Bool) : markedPower (a,xs)=a^xs.length :=
  BinaryPowerPrograms.power_eq a xs.length

lemma next_eq (z : State) :
    next z=(z.1,DyadicRootBisection.advance z.1.1 z.1.2.length z.2) := by
  simp only [next,test,leftProduct,rightProduct,markedPower_eq,mid,twiceDenominator,
    DyadicRootBisection.advance,decide_eq_true_eq]

lemma fold_eq (xs : List Bool) (p : Parameters) (z : DyadicRootBisection.State) :
    xs.foldl (fun z a=>advance (a,z)) (p,z)=
      (p,(DyadicRootBisection.advance p.1 p.2.length)^[xs.length] z) := by
  induction xs generalizing z with
  | nil=>rfl
  | cons a xs ih=>
    rw [List.foldl_cons]
    change xs.foldl (fun z a=>advance (a,z)) (next (p,z))=_
    rw [next_eq,ih]
    simp only [List.length_cons,Function.iterate_succ_apply]

theorem output_eq (c : TreeFraction.Fraction) (degree depth : List Bool) :
    output ((c,degree),depth)=DyadicRootBisection.output c degree.length depth.length := by
  have hr (k : ℕ) :
      (DyadicRootBisection.advance c degree.length)^[k] ((0,8),1)=
        DyadicRootBisection.run c degree.length k := by
    induction k with
    | zero=>rfl
    | succ k ih=>rw [Function.iterate_succ_apply',ih,DyadicRootBisection.run]
  simp only [output,execute,fold_eq,hr,finish,mid,twiceDenominator,DyadicRootBisection.output]

theorem output_value (c : TreeFraction.Fraction) (hc : 0 < c.2) (degree depth : List Bool) :
    TreeFraction.val (output ((c,degree),depth))=
      RationalRootBisection.midpoint (TreeFraction.val c) degree.length depth.length := by
  rw [output_eq]
  exact DyadicRootBisection.output_value c hc _ _

end ContingencyTables.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RoundedPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the rounded power used by the correction oracle

The exponent lies in [-2,2]. Clipping the computed signed floor
at twice the supplied degree allowance plus one is therefore inactive
on valid inputs, and keeps every binary execution polynomial even on
arbitrary malformed numerator/denominator data.
-/

namespace ContingencyTables.RoundedPowerProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial SignedPairProgram

lemma floor_bounds (beta : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2) (s : ℕ) :
    -2*(s:ℤ) ≤ ⌊(s:ℚ)*beta⌋ ∧ ⌊(s:ℚ)*beta⌋ ≤ 2*(s:ℤ) := by
  have hL:=mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg s : (0:ℚ) ≤ s)
  have hU:=mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg s : (0:ℚ) ≤ s)
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith
  · have hf: (⌊(s:ℚ)*beta⌋:ℚ) ≤ 2*s:=(Int.floor_le _).trans (by linarith)
    exact_mod_cast hf

lemma clipped_eq (p n d : ℕ) (xs : List Bool)
    (hlo: -2 ≤ ((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d ≤ 2) :
    clipped (((p,n),d),xs)=
      ((⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat,
        (-⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat) := by
  have hb:=floor_bounds _ hlo hhi xs.length
  have hp: (⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat ≤ 2*xs.length+1:=by omega
  have hn: (-⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋:ℤ).toNat ≤ 2*xs.length+1:=by omega
  simp only [clipped,normalized,SignedPairProgram.normalize_eq,SignedFloorProgram.scaledFloor_value,
    ForestAffineProgram.signedParts,cap,min_eq_left hp,min_eq_left hn]

/-- The returned natural fraction is exactly the rational power used
by the approximation, including negative rounded exponents. -/
theorem output_value (p n d : ℕ) (xs : List Bool)
    (hlo: -2 ≤ ((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d ≤ 2) :
    TreeFraction.val (output (((p,n),d),xs))=
      (2:ℚ)^PowerOfTwoApproximation.numerator (((p:ℚ)-n)/d) xs.length := by
  rw [output,TreeFraction.normalize_val]
  simp only [positivePower,negativePower,positiveInput,negativeInput,
    BinaryPowerPrograms.power_eq,clipped_eq p n d xs hlo hhi,TreeFraction.val,Nat.cast_pow,Nat.cast_ofNat]
  let q:ℤ:=⌊(xs.length:ℚ)*(((p:ℚ)-n)/d)⌋
  change (2:ℚ)^q.toNat/(2:ℚ)^(-q).toNat=(2:ℚ)^q
  have he: (q.toNat:ℤ)-(-q).toNat=q:=by omega
  conv_rhs => rw [←he]
  rw [zpow_sub₀ (by norm_num : (2:ℚ)≠0),zpow_natCast,zpow_natCast]

theorem output_denominator_pos (z : Input) : 0<(output z).2 :=
  TreeFraction.normalize_den_pos _

end ContingencyTables.RoundedPowerProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PowerApproximationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed power-of-two approximation used by the weight oracle

Both stages are concrete binary programs: compute the rounded signed
power, then bisect using natural cross-products and shared denominators.
The two allowance lists determine the precision parameters.
-/

namespace ContingencyTables.PowerApproximationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem output_value (p n d : ℕ) (degree depth : List Bool)
    (hlo: -2≤((p:ℚ)-n)/d) (hhi: ((p:ℚ)-n)/d≤2) :
    TreeFraction.val (output (((p,n),d),(degree,depth)))=
      PowerOfTwoApproximation.approximation (((p:ℚ)-n)/d) degree.length depth.length := by
  unfold output prepare
  rw [DyadicRootProgram.output_value _ (RoundedPowerProgram.output_denominator_pos _),
    RoundedPowerProgram.output_value p n d degree hlo hhi]
  rfl

end ContingencyTables.PowerApproximationProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CorrectionValueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary composition of the correction value

The input contains the computed grid exponent, phase ratio, point
penalty, population factor and two precision marker lists. Normalized
fraction multiplication supplies a positive denominator for the signed
exponent passed to the executed power approximation.
-/

namespace ContingencyTables.CorrectionValueProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma weighted_denominator_pos (z : Frame) : 0<(weighted z).2 :=
  TreeFraction.normalize_den_pos _

lemma exponentInput_value (z : Frame) :
    ((exponentInput z).1.1-(exponentInput z).1.2:ℚ)/(exponentInput z).2=
      (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2 := by
  have hd : ((weighted z).2:ℚ)≠0 := by exact_mod_cast (weighted_denominator_pos z).ne'
  have hw : TreeFraction.val (weighted z)=TreeFraction.val z.1.2*TreeFraction.val z.2 :=
    TreeFraction.mul_val _ _
  rw [←hw]
  simp only [exponentInput,Nat.cast_mul,TreeFraction.val]
  field_simp [hd]

theorem output_value (z : Frame) (population : TreeFraction.Fraction)
    (degree depth : List Bool)
    (hlo : -2 ≤ (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2)
    (hhi : (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2 ≤ 2) :
    TreeFraction.val (output ((z,population),(degree,depth)))=
      TreeFraction.val population*PowerOfTwoApproximation.approximation
        ((z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2) degree.length depth.length := by
  have hl := hlo
  have hh := hhi
  rw [←exponentInput_value z] at hl hh
  rw [output,TreeFraction.mul_val]
  unfold power powerInput
  rw [PowerApproximationProgram.output_value _ _ _ degree depth hl hh,exponentInput_value]

theorem output_approximate (z : Frame) (population : TreeFraction.Fraction)
    (degree depth : List Bool) (sigma : ℚ)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma)
    (hlo : -2 ≤ (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2)
    (hhi : (z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2 ≤ 2) :
    TreeFraction.val (output ((z,population),(degree,depth)))=
      TreeFraction.val population*PowerOfTwoApproximation.approximate
        ((z.1.1:ℚ)-TreeFraction.val z.1.2*TreeFraction.val z.2) sigma := by
  rw [output_value z population degree depth hlo hhi,hdegree,hdepth]
  rfl

end ContingencyTables.CorrectionValueProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAggregateProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exact fraction averages and products

These are the arithmetic folds used by the executed weight estimator.
Normalization makes the average valid on every input, including a raw
fraction with denominator zero.
-/

namespace ContingencyTables.FractionAggregateProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

lemma average_value (xs : List TreeFraction.Fraction) :
    TreeFraction.val (average xs)=(xs.map TreeFraction.val).sum/(xs.length:ℚ) := by
  rw [average,TreeFraction.div_val,TreeFraction.sum_val]
  · rw [show TreeFraction.val (xs.length,1)=(xs.length:ℚ) by
      simp only [TreeFraction.val,Nat.cast_one,div_one]]
    simp only [List.map_map,Function.comp_def,TreeFraction.normalize_val]
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact TreeFraction.normalize_den_pos a

private lemma fold_value (xs : List TreeFraction.Fraction) (a : TreeFraction.Fraction) :
    TreeFraction.val (xs.foldl (fun a b => TreeFraction.mul (b,a)) a)=
      TreeFraction.val a*(xs.map TreeFraction.val).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons,ih,TreeFraction.mul_val,List.map_cons,List.prod_cons]
    ring

lemma product_value (xs : List TreeFraction.Fraction) :
    TreeFraction.val (product xs)=(xs.map TreeFraction.val).prod := by
  rw [product,fold_value]
  simp only [TreeFraction.val,Nat.cast_one,div_self (by norm_num : (1:ℚ)≠0),one_mul]

end ContingencyTables.FractionAggregateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedBinDrawLaw.freeCellDecidableEq
private lemma coordinate_scalar (K N beta h d : ℕ) (bits : List Bool) :
    BinVectorProgram.coordinate ((((K,N),beta),(h,d)),bits)=
      FairBits.endpoint K N beta+ProfilePrograms.scaledWordValue
        (intervalSize K N beta,bits.take (offsetBitLength (intervalSize K N beta) h d)) := by
  simp only [BinVectorProgram.coordinate,BinIntervalProgram.draw,BinIntervalProgram.endpoint_eq,
    BinIntervalProgram.intervalSize_eq,BinVectorProgram.activeWidth,offsetBitLength]

private lemma original_value (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K)
    (h : ℕ) (bits : FreeWords A h) (i : Fin (dimension A)) :
    (binWordDraw A K hK hW v h ((originalWordEquiv A h).symm bits) (index A i)).val=
      (intervalEquiv K (freeRange A (index A i)) (naturalBin A v (index A i))
        hK (Nat.succ_pos _) (naturalBin_lt A v _)
        (scaledBitInteger (binSize A K v i) (offsetBitLength (binSize A K v i) h A.d)
          (binSize_positive A K hK hW v i)
          (prefixWord (binBits_le A K hK v h i) (bits (index A i))))).val := by
  change ((Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
    {z : ℕ // z∈FairBits.fiber K (freeRange A t) (naturalBin A v t)}) (index A))
      (fun j => intervalEquiv K (freeRange A (index A j)) (naturalBin A v (index A j))
        hK (Nat.succ_pos _) (naturalBin_lt A v _)
        (scaledBitInteger (binSize A K v j) (offsetBitLength (binSize A K v j) h A.d)
          (binSize_positive A K hK hW v j)
          (prefixWord (binBits_le A K hK v h j)
            ((originalWordEquiv A h).symm bits j)))) (index A i)).val=_
  rw [Equiv.piCongrLeft_apply_apply]
  simp only [originalWordEquiv,Equiv.piCongrLeft_symm_apply]

private lemma original_free_value (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K)
    (h : ℕ) (bits : FreeWords A h) (t : FreeCell A.small A.T)
    (hsize : 0 < intervalSize K (freeRange A t) (naturalBin A v t)) :
    (binWordDraw A K hK hW v h ((originalWordEquiv A h).symm bits) t).val=
      (intervalEquiv K (freeRange A t) (naturalBin A v t)
        hK (Nat.succ_pos _) (naturalBin_lt A v t)
        (scaledBitInteger (intervalSize K (freeRange A t) (naturalBin A v t))
          (offsetBitLength (intervalSize K (freeRange A t) (naturalBin A v t)) h A.d)
          hsize (prefixWord (interval_bits_le K (freeRange A t)
            (naturalBin A v t) h A.d hK (Nat.succ_pos _) (naturalBin_lt A v t))
            (bits t)))).val := by
  obtain ⟨i,rfl⟩ := (index A).surjective t
  simpa only [binSize] using original_value A K hK hW v h bits i

lemma draw_coordinate (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Words A h) (i : Fin (RootedCatalogGrid.freeCount A)) :
    BinVectorProgram.coordinate
      ((((K,freeRange A (RootedForestCatalog.freeEquiv A i)),(v i).val.toNat),(h,A.d)),
        List.ofFn (bits i))=
      (draw A K hK hW v h bits (RootedForestCatalog.freeEquiv A i)).val := by
  let w := RootedCatalogGrid.gridEquiv A K v
  have hb : naturalBin A w (RootedForestCatalog.freeEquiv A i)=(v i).val.toNat := by
    simp only [w,naturalBin,RootedCatalogGrid.gridEquiv_free,Equiv.symm_apply_apply]
  have hp : 0 < intervalSize K (freeRange A (RootedForestCatalog.freeEquiv A i))
      (naturalBin A w (RootedForestCatalog.freeEquiv A i)) := by
    simpa only [binSize,Equiv.apply_symm_apply] using
      binSize_positive A K hK hW w ((index A).symm (RootedForestCatalog.freeEquiv A i))
  have hv := original_free_value A K hK hW w h (freeWordEquiv A h bits)
    (RootedForestCatalog.freeEquiv A i) hp
  let t := RootedForestCatalog.freeEquiv A i
  let M := intervalSize K (freeRange A t) (naturalBin A w t)
  let k := offsetBitLength M h A.d
  have hk : k ≤ offsetBitLength (freeRange A t) h A.d :=
    interval_bits_le K (freeRange A t) (naturalBin A w t) h A.d hK
      (Nat.succ_pos _) (naturalBin_lt A w t)
  have hs := ProfilePrograms.scaledWordValue_ofFn M k hp
    (prefixWord hk (freeWordEquiv A h bits t))
  change (draw A K hK hW v h bits t).val=FairBits.endpoint K (freeRange A t)
    (naturalBin A w t)+(scaledBitInteger M k hp
      (prefixWord hk (freeWordEquiv A h bits t))).val at hv
  rw [←hs,←BinVectorProgram.take_ofFn_prefix hk] at hv
  have hw : freeWordEquiv A h bits (RootedForestCatalog.freeEquiv A i)=bits i :=
    Equiv.piCongrLeft_apply_apply _ _ _ _
  dsimp only [t,M,k] at hv
  rw [hw] at hv
  rw [hb] at hv
  rw [coordinate_scalar]
  exact hv.symm

theorem program_flatDraw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Fin (wordBits A h) → Bool) :
    RootedBinFramesProgram.draw (RootedBinFramesProgram.data A h v,List.ofFn bits)=
      List.ofFn (fun i => (flatDraw A K hK hW v h bits
        (RootedForestCatalog.freeEquiv A i)).val) := by
  unfold RootedBinFramesProgram.draw
  rw [RootedBinFramesProgram.frames_data]
  let frames : Fin (RootedCatalogGrid.freeCount A) → BinVectorProgram.Frame := fun i =>
    (((K,freeRange A (RootedForestCatalog.freeEquiv A i)),(v i).val.toNat),(h,A.d))
  have he := BinVectorProgram.output_ofFn frames bits
  refine he.trans ?_
  apply congrArg List.ofFn
  funext i
  exact draw_coordinate A K hK hW v h (wordEquiv A h bits) i

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma correctionExponent_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    (correctionExponent A R C a z K hK f:ℝ)=
      (gridExponent A R C a z (integerBin A K hK f):ℝ)-
        (a:ℝ)/height A C*D A R C z (integerPoint A C f) := by
  simp only [correctionExponent,Rat.cast_sub,Rat.cast_natCast,Rat.cast_mul,Rat.cast_div,
    rationalHeight_cast,rationalD_cast,rationalIntegerPoint_cast]

/-- The exponent passed to numerical approximation is a bounded rational,
although the original capacities may be arbitrarily large. -/
theorem correctionExponent_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hB : (K:ℝ)=binWidth A C) (f : FreeIndex A.small A.T A.b) :
    -2 ≤ correctionExponent A R C a z K hK f ∧ correctionExponent A R C a z K hK f ≤ 2 := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  have hd := exponent_change A R C a hCR (Nat.cast_nonneg _) haHR z
    (realCorner (integerBin A K hK f)) (integerPoint A C f) 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using integerPoint_distance A C K hK hB f i)
  have he := gridExponent_eq_floor A R C a z (integerBin A K hK f)
  have hlo := Int.floor_le ((a:ℝ)/height A C*D A R C z (realCorner (integerBin A K hK f)))
  have hhi := Int.lt_floor_add_one ((a:ℝ)/height A C*D A R C z (realCorner (integerBin A K hK f)))
  rw [←he] at hlo hhi
  have hbounds : (-2:ℝ) ≤ (correctionExponent A R C a z K hK f:ℝ) ∧
      (correctionExponent A R C a z K hK f:ℝ) ≤ 2 := by
    rw [correctionExponent_cast]
    simp only [Int.cast_natCast] at hlo hhi
    rcases abs_le.mp hd with ⟨hl,hu⟩
    constructor <;> linarith
  constructor
  · exact_mod_cast hbounds.1
  · exact_mod_cast hbounds.2

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleStepProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the catalog-order oracle step

The program uses the computed forest exponent twice, one arithmetic
axis proposal and one independent bounded dyadic acceptance word.
-/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

noncomputable section
variable {m n : ℕ}

lemma evaluate_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    RootedPenaltyEvaluateProgram.evaluate (data A C a K z v).2=
      RootedCatalogGrid.exponent A C a z v :=
  RootedCatalogGrid.evaluate_grid A C a K hC z v

lemma replace_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (z : View A → ℕ) (v w : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    replace ((data A C a K z v).2,gridNatCode w)=(data A C a K z w).2 := rfl

theorem step_pair (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    {p k : ℕ} (proposal : Fin p → Bool) (coins : Fin k → Bool) :
    step (data A C a K z v,(List.ofFn proposal,List.ofFn coins))=
      gridNatCode (match axisCodeStep v (binaryWordEquiv p proposal) with
        | Option.none => v
        | Option.some w => if acceptDyadic
            (RootedCatalogGrid.exponent A C a z w-RootedCatalogGrid.exponent A C a z v)
            k (binaryWordEquiv k coins) then w else v) := by
  have hc : candidate (data A C a K z v,(List.ofFn proposal,List.ofFn coins))=
      (axisCodeStep v (binaryWordEquiv p proposal)).map gridNatCode :=
    axisWordStep_eq v proposal
  unfold step
  rw [hc]
  cases h : axisCodeStep v (binaryWordEquiv p proposal) with
  | none => rfl
  | some w =>
    simp only [Option.map_some,Option.elim_some,acceptCandidate,gap,candidateData,currentData,
      replace_data,evaluate_data A C a K hC,dyadicWordAccept_ofFn,decide_eq_true_eq]
    split_ifs <;> rfl

end
end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single fixed word drives an executed oracle transition -/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

noncomputable section
variable {m n : ℕ}

/-- Exact code agreement for the prescribed finite word, including
unused direction codes and unsuccessful acceptance tests. -/
theorem wordStep_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (bits : Fin (CompanionOracleDensity.oracleStepBits A C) → Bool) :
    wordStep (data A C a K z v,List.ofFn bits)=
      gridNatCode (RootedCatalogGrid.bitStep A C a z v bits) := by
  have ht := ofFn_split_take (p := Nat.clog 2 (8*A.d))
    (k := CompanionOracleDensity.rationalHeight A C) bits
  have hd := ofFn_split_drop (p := Nat.clog 2 (8*A.d))
    (k := CompanionOracleDensity.rationalHeight A C) bits
  have hp : ((List.ofFn bits).take (Nat.clog 2 (8*A.d)),
      (List.ofFn bits).drop (Nat.clog 2 (8*A.d)))=
      (List.ofFn (splitWordEquiv (Nat.clog 2 (8*A.d))
        (CompanionOracleDensity.rationalHeight A C) bits).1,
       List.ofFn (splitWordEquiv (Nat.clog 2 (8*A.d))
        (CompanionOracleDensity.rationalHeight A C) bits).2) := Prod.ext ht hd
  have hsplit := congrArg (fun coins => step (data A C a K z v,coins)) hp
  change step (data A C a K z v,((List.ofFn bits).take (Nat.clog 2 (8*A.d)),
    (List.ofFn bits).drop (Nat.clog 2 (8*A.d))))=_
  refine hsplit.trans ((step_pair A C a K hC z v
    (splitWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).1
    (splitWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).2).trans ?_)
  change gridNatCode (match axisCodeStep v
      (pairWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).1 with
    | Option.none => v
    | Option.some w => if acceptDyadic
        (RootedCatalogGrid.exponent A C a z w-RootedCatalogGrid.exponent A C a z v)
        (CompanionOracleDensity.rationalHeight A C)
        (pairWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).2
      then w else v)=_
  unfold RootedCatalogGrid.bitStep
  dsimp only
  cases axisCodeStep v
    (pairWordEquiv (Nat.clog 2 (8*A.d)) (CompanionOracleDensity.rationalHeight A C) bits).1 with
  | none => rfl
  | some w => rfl

end
end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an oracle walk

The immutable graph and cell arrays are kept separately from the grid
coordinates. A coordinate changes by at most one per transition, which
bounds every accumulator reached by the binary list fold.
-/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess

noncomputable section
variable {m n : ℕ}

lemma advance_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (bits : Fin (CompanionOracleDensity.oracleStepBits A C) → Bool) :
    advance (List.ofFn bits,data A C a K z v)=
      data A C a K z (RootedCatalogGrid.bitStep A C a z v bits) := by
  unfold advance data
  apply Prod.ext
  · rfl
  · exact RootedOracleStepProgram.wordStep_data A C a K hC z v bits

theorem walkWords_ofFn (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (N : ℕ) (bits : Fin N → Fin (CompanionOracleDensity.oracleStepBits A C) → Bool) :
    walkWords (data A C a K z v,List.ofFn (fun i => List.ofFn (bits i)))=
      data A C a K z (wordWalk (RootedCatalogGrid.bitStep A C a z) v N bits) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold walkWords at ih ⊢
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    change advance (List.ofFn (bits (Fin.last N)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun state bits => advance (bits,state)) (data A C a K z v))=_
    rw [ih (Fin.init bits)]
    exact advance_data A C a K hC z _ _

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPointPenaltyProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed penalty evaluation at a sampled integer assignment

At an integer point, the coordinate scale in the affine coefficient
cancels its inverse in the coordinate. The program therefore forms the
unscaled signed affine numerator directly from the sampled integers.
-/

namespace ContingencyTables.RootedPointPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped RootedForestPrepareProgram
open scoped BigOperators Classical

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts

noncomputable section
variable {m n nf nc : ℕ}

lemma coefficient_parts (z : RootedCoefficientProgram.Input) :
    RootedCoefficientProgram.coefficient z=ForestAffineProgram.signedParts
      (SignedPairProgram.value (RootedCoefficientProgram.coefficient z)) := by
  unfold RootedCoefficientProgram.coefficient
  split
  · rw [SignedPairProgram.value_normalize]
    exact SignedPairProgram.normalize_eq _
  · rfl

lemma coefficient_parts_input (A : Instance (Fin m) (Fin n)) (t : TreeCell A.T)
    (a : Fin m×Fin n) :
    RootedCoefficientProgram.coefficient (RootedCoefficientProgram.input A t a)=
      ForestAffineProgram.signedParts (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a) := by
  rw [coefficient_parts,RootedCoefficientProgram.coefficient_input]

lemma tree_data (A : Instance (Fin m) (Fin n)) (B : ℕ) (t : TreeCell A.T)
    (x q : Fin m → Fin n → ℤ) (cells : Fin nc ≃ Fin m×Fin n)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    tree (RootedForestDataProgram.data A B t x q cells free v)=
      ForestAffineProgram.data (RootedIntegerEvaluation.offset A (rowColumn A.T) t x q)
        (fun i => RootedIntegerEvaluation.coefficient A (rowColumn A.T) t (free i).val)
        (fun i => v (free i)) (A.b t.val.1 t.val.2) := by
  unfold tree RootedForestDataProgram.data ForestAffineProgram.data
  rw [RootedOffsetProgram.offset_data]
  simp only [List.map_ofFn,Function.comp_def,term,coefficient_parts_input]

lemma rational_tree_integer (A : Instance (Fin m) (Fin n)) (B : ℕ) (hB : 0<B)
    (t : TreeCell A.T) (x q : Fin m → Fin n → ℤ) (v : FreeCell A.small A.T → ℕ) :
    RootedIntegerEvaluation.rationalScaledTree A (rowColumn A.T) B x q
      (fun f => (B:ℚ)*(v f:ℚ)/((A.b f.val.1 f.val.2:ℚ)+1)) t=
      ((RootedIntegerEvaluation.offset A (rowColumn A.T) t x q:ℚ)+
        ∑ f : FreeCell A.small A.T,
          (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t f.val:ℚ)*(v f:ℚ))/
        A.b t.val.1 t.val.2 := by
  have hBQ : (B:ℚ)≠0 := by exact_mod_cast hB.ne'
  unfold RootedIntegerEvaluation.rationalScaledTree
  rw [add_div,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  have hN : (A.b f.val.1 f.val.2:ℚ)+1≠0 := by positivity
  have ht : (A.b t.val.1 t.val.2:ℚ)≠0 := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one
      (A.hlarge _ _ (A.hTG t.property)).2).ne'
  field_simp [hBQ,hN,ht]

theorem tree_value (A : Instance (Fin m) (Fin n)) (B : ℕ) (hB : 0<B) (t : TreeCell A.T)
    (x q : Fin m → Fin n → ℤ) (cells : Fin nc ≃ Fin m×Fin n)
    (free : Fin nf ≃ FreeCell A.small A.T) (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (ForestAffineProgram.evaluate
      (tree (RootedForestDataProgram.data A B t x q cells free v)))=
      max 0 (max (-RootedIntegerEvaluation.rationalScaledTree A (rowColumn A.T) B x q
        (fun f => (B:ℚ)*(v f:ℚ)/((A.b f.val.1 f.val.2:ℚ)+1)) t)
      (RootedIntegerEvaluation.rationalScaledTree A (rowColumn A.T) B x q
        (fun f => (B:ℚ)*(v f:ℚ)/((A.b f.val.1 f.val.2:ℚ)+1)) t-1)) := by
  have ht : 0<A.b t.val.1 t.val.2 := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (A.hlarge _ _ (A.hTG t.property)).2
  rw [tree_data,ForestAffineProgram.evaluate_data _ _ _ _ ht]
  have he : (∑ i : Fin nf,(RootedIntegerEvaluation.coefficient A (rowColumn A.T) t
      (free i).val:ℚ)*(v (free i):ℚ))=
      ∑ f : FreeCell A.small A.T,
        (RootedIntegerEvaluation.coefficient A (rowColumn A.T) t f.val:ℚ)*(v f:ℚ) :=
    Fintype.sum_equiv free _ _ (fun _ => rfl)
  rw [he,rational_tree_integer A B hB]

lemma trees_data (A : Instance (Fin m) (Fin n)) (C B : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    trees (RootedForestPrepareProgram.data A C B x q v)=
      List.ofFn (fun i => tree (RootedForestDataProgram.data A B
        (RootedForestCatalog.treeEquiv A i) (fun i j => (x i j:ℤ))
        (fun i j => (q i j:ℤ)) finProdFinEquiv.symm (RootedForestCatalog.freeEquiv A) v)) := by
  change (RootedForestCatalog.catalog (RootedForestCatalog.data A,true)).map
    (fun a => prepareTree (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a))=_
  have hc := congrArg (fun cells : List (ℕ×ℕ) => cells.map
    (fun a => prepareTree (((RootedDemandProgram.data A x q,B),
      List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),a)))
    (RootedForestPrepareProgram.treeCatalog_ofFn A)
  refine hc.trans ?_
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change tree (forestInput (((RootedDemandProgram.data A x q,B),
    List.ofFn (fun i => v (RootedForestCatalog.freeEquiv A i))),
      ((RootedForestCatalog.treeEquiv A i).val.1.val,
        (RootedForestCatalog.treeEquiv A i).val.2.val)))=_
  exact congrArg tree (RootedForestPrepareProgram.forestInput_data A B
    (RootedForestCatalog.treeEquiv A i) x q v)

/-- The executed penalty is exactly the source's rational penalty at
the scaled integer assignment, with no numerical approximation. -/
theorem output_data (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0<C)
    (x q : Fin m → Fin n → ℕ) (v : FreeCell A.small A.T → ℕ) :
    TreeFraction.val (output (RootedForestPrepareProgram.data A C
      (CompanionOracleDensity.rationalBinWidth A C) x q v))=
      RootedPenaltyProgram.rationalPenalty A (rowColumn A.T) C
        (fun i j => (x i j:ℤ)) (fun i j => (q i j:ℤ))
        (fun f => (CompanionOracleDensity.rationalBinWidth A C:ℚ)*(v f:ℚ)/
          ((A.b f.val.1 f.val.2:ℚ)+1)) := by
  have hB : 0<CompanionOracleDensity.rationalBinWidth A C := by
    unfold CompanionOracleDensity.rationalBinWidth
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC)
      (pow_pos (lt_of_lt_of_le Nat.zero_lt_one A.hd) _)
  rw [output,ForestPenaltyProgram.penaltyCode_value]
  change (C:ℚ)*((RootedDemandProgram.rootCount (RootedDemandProgram.data A x q):ℚ)+
    ((trees (RootedForestPrepareProgram.data A C
      (CompanionOracleDensity.rationalBinWidth A C) x q v)).map
      (fun t => TreeFraction.val (ForestAffineProgram.evaluate t))).sum)=_
  rw [RootedDemandProgram.rootCount_data,trees_data]
  simp only [List.map_ofFn,Function.comp_apply,List.sum_ofFn]
  unfold RootedPenaltyProgram.rationalPenalty
  congr 2
  exact Fintype.sum_equiv (RootedForestCatalog.treeEquiv A) _ _
    (fun i => tree_value A _ hB (RootedForestCatalog.treeEquiv A i) _ _
      finProdFinEquiv.symm (RootedForestCatalog.freeEquiv A) v)

theorem output_integerPoint (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0<C)
    (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) :
    TreeFraction.val (output (RootedForestPrepareProgram.data A C
      (CompanionOracleDensity.rationalBinWidth A C)
      (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)
      (fun t => (f t).val)))=
      RootedOracleDensity.rationalD A (rowColumn A.T) C z
        (CompanionOracleDensity.rationalIntegerPoint A C f) := by
  have hpoint : (fun t : FreeCell A.small A.T =>
      CompanionOracleDensity.rationalIntegerPoint A C f
        ((CompanionOracleDensity.index A).symm t))=
      (fun t => (CompanionOracleDensity.rationalBinWidth A C:ℚ)*(f t).val/
        ((A.b t.val.1 t.val.2:ℚ)+1)) := by
    funext t
    change (CompanionOracleDensity.rationalBinWidth A C:ℚ)*
      (f (CompanionOracleDensity.index A ((CompanionOracleDensity.index A).symm t))).val/
      CompanionOracleDensity.freeRange A
        (CompanionOracleDensity.index A ((CompanionOracleDensity.index A).symm t))=_
    rw [Equiv.apply_symm_apply]
    simp only [CompanionOracleDensity.freeRange,Nat.cast_add,Nat.cast_one]
  rw [output_data A C hC]
  unfold RootedOracleDensity.rationalD
  rw [hpoint]
  rfl

end
end ContingencyTables.RootedPointPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed correction equals the analysed rational correction -/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary RootedCompletion
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma exponent_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    RootedPenaltyEvaluateProgram.evaluate (exponentInput (data A C a K z v f degree depth))=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) :=
  RootedCatalogGrid.evaluate_grid A C a K hC z v

lemma pointInput_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    pointInput (data A C a K z v f degree depth)=
      RootedForestPrepareProgram.data A C (rationalBinWidth A C)
        (ForestCountIdentification.smallX A.small z)
        (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)
        (fun t => (f t).val) := by
  change (((C,RootedPenaltyEvaluateProgram.width ((A.d,A.W),(C,a))),
    RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
      (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j)),_)=_
  rw [RootedPenaltyEvaluateProgram.width_data]
  rfl

lemma point_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    TreeFraction.val (RootedPointPenaltyProgram.output
      (pointInput (data A C a K z v f degree depth)))=
      RootedOracleDensity.rationalD A (rowColumn A.T) C z (rationalIntegerPoint A C f) := by
  rw [pointInput_data]
  exact RootedPointPenaltyProgram.output_integerPoint A C hC z f

lemma populationInput_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    populationInput (data A C a K z v f degree depth)=
      BinPopulationProgram.data A K (RootedCatalogGrid.gridEquiv A K v) := by
  change (RootedBinFramesProgram.frames (RootedBinFramesProgram.data A 0 v)).map Prod.fst=_
  rw [RootedBinFramesProgram.frames_data,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,RootedCatalogGrid.naturalBin_grid,
    RootedCatalogGrid.naturalValues,Equiv.symm_apply_apply]

lemma population_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hK : 0 < K)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool)
    (hf : integerBin A K hK f=RootedCatalogGrid.gridEquiv A K v) :
    TreeFraction.val (BinPopulationProgram.output
      (populationInput (data A C a K z v f degree depth)))=rationalPopulation A K hK f := by
  rw [populationInput_data,←hf]
  exact BinPopulationProgram.output_integerBin A K hK f

lemma phase_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) :
    TreeFraction.val (phase (data A C a K z v f degree depth))=(a:ℚ)/rationalHeight A C := by
  change (a:ℚ)/RootedPenaltyEvaluateProgram.height ((A.d,A.W),(C,a))=_
  rw [RootedPenaltyEvaluateProgram.height_data]

theorem output_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 0 < K)
    (hB : (K:ℝ)=binWidth A C) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (f : FreeIndex A.small A.T A.b) (degree depth : List Bool) (sigma : ℚ)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma)
    (hf : integerBin A K hK f=RootedCatalogGrid.gridEquiv A K v) :
    TreeFraction.val (output (data A C a K z v f degree depth))=
      RootedOracleDensity.computedCorrection A (rowColumn A.T) C a z K hK sigma f := by
  let input := data A C a K z v f degree depth
  let frame : CorrectionValueProgram.Frame :=
    ((RootedPenaltyEvaluateProgram.evaluate (exponentInput input),phase input),
      RootedPointPenaltyProgram.output (pointInput input))
  let population := BinPopulationProgram.output (populationInput input)
  have hexponent : (frame.1.1:ℚ)-TreeFraction.val frame.1.2*TreeFraction.val frame.2=
      RootedOracleDensity.correctionExponent A (rowColumn A.T) C a z K hK f := by
    dsimp only [frame,input]
    rw [exponent_data A C a K hC,phase_data,point_data A C a K hC,←hf]
    rfl
  have hb := RootedOracleDensity.correctionExponent_bounds A (rowColumn A.T) C a
    hC haH z K hK hB f
  have hlo : -2 ≤ (frame.1.1:ℚ)-TreeFraction.val frame.1.2*TreeFraction.val frame.2 := by
    rw [hexponent]; exact hb.1
  have hhi : (frame.1.1:ℚ)-TreeFraction.val frame.1.2*TreeFraction.val frame.2 ≤ 2 := by
    rw [hexponent]; exact hb.2
  have he := CorrectionValueProgram.output_approximate frame population degree depth sigma
    hdegree hdepth hlo hhi
  change TreeFraction.val (CorrectionValueProgram.output ((frame,population),(degree,depth)))=_
  rw [he,hexponent]
  rw [show TreeFraction.val population=rationalPopulation A K hK f from
    population_data A C a K hK z v f degree depth hf]
  rfl

end
end ContingencyTables.RootedCorrectionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

noncomputable section
variable {m n : ℕ}

lemma stepWidth_pos (A : Instance (Fin m) (Fin n)) (C : ℕ) (hC : 0 < C) :
    0 < CompanionOracleDensity.oracleStepBits A C := by
  have hd : 0 < A.d := lt_of_lt_of_le Nat.zero_lt_one A.hd
  have hh : 0 < CompanionOracleDensity.rationalHeight A C := by
    unfold CompanionOracleDensity.rationalHeight
    positivity
  exact hh.trans_le (Nat.le_add_left _ _)

/-- Every flat input bit is split into the prescribed independent step
words, and the polynomial program computes their literal finite walk. -/
theorem flatWalk_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (N : ℕ) (bits : Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool) :
    flatWalk (data A C a K z v,List.ofFn bits)=
      data A C a K z (wordWalk (RootedCatalogGrid.bitStep A C a z) v N
        (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C) bits)) := by
  unfold flatWalk
  rw [stepWidth_data,wordChunks_ofFn (stepWidth_pos A C hC) bits]
  exact walkWords_ofFn A C a K hC z v N _

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing one selected-root correction sample

Separate finite words drive the grid walk and the integer draw. The
computed final bin and sampled integer are then passed to the exact
population and rational-power correction program.
-/

namespace ContingencyTables.RootedCorrectionSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

attribute [local irreducible] walked

attribute [local irreducible] binFrame

attribute [local irreducible] sampled

attribute [local irreducible] prepare

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FairBits
open scoped BigOperators

noncomputable section
variable {m n : ℕ}

lemma walked_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool) (binBits : List Bool) :
    walked (data A C a K z v h degree depth (List.ofFn walkBits) binBits)=
      RootedOracleWalkProgram.data A C a K z
        (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) := by
  unfold walked data
  exact RootedOracleWalkProgram.flatWalk_data A C a K hC z v N walkBits

lemma binFrame_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool) (binBits : List Bool) :
    binFrame (data A C a K z v h degree depth (List.ofFn walkBits) binBits)=
      RootedBinFramesProgram.data A h
        (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) := by
  unfold binFrame
  rw [walked_data A C a K hC]
  rfl

lemma sampled_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool)
    (binBits : Fin (RootedBinDrawLaw.wordBits A h) → Bool) :
    sampled (data A C a K z v h degree depth (List.ofFn walkBits) (List.ofFn binBits))=
      List.ofFn (fun i => (RootedBinDrawLaw.flatDraw A K hK hW
        (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) h binBits
        (RootedForestCatalog.freeEquiv A i)).val) := by
  unfold sampled
  rw [binFrame_data A C a K hC]
  exact RootedBinDrawLaw.program_flatDraw A K hK hW _ h binBits

lemma bin_flatDraw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Fin (RootedBinDrawLaw.wordBits A h) → Bool) :
    integerBin A K hK (RootedBinDrawLaw.flatDraw A K hK hW v h bits)=
      RootedCatalogGrid.gridEquiv A K v := by
  have hm := binOffsetValue_mem A K hK (RootedCatalogGrid.gridEquiv A K v)
    (fun i => scaledBitInteger (binSize A K (RootedCatalogGrid.gridEquiv A K v) i)
      (offsetBitLength (binSize A K (RootedCatalogGrid.gridEquiv A K v) i) h A.d)
      (binSize_positive A K hK hW _ i)
      (FirstSuccess.prefixWord (binBits_le A K hK _ h i)
        (RootedBinDrawLaw.reindexWords A h (RootedBinDrawLaw.wordEquiv A h bits) i)))
  exact (Finset.mem_filter.mp hm).2

theorem output_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (sigma : ℚ)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool)
    (binBits : Fin (RootedBinDrawLaw.wordBits A h) → Bool) :
    TreeFraction.val (output (data A C a K z v h degree depth
      (List.ofFn walkBits) (List.ofFn binBits)))=
      RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K hK sigma
        (RootedBinDrawLaw.flatDraw A K hK hW
          (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) h binBits) := by
  unfold output prepare
  rw [walked_data A C a K hC,sampled_data A C a K hC hK hW]
  exact RootedCorrectionProgram.output_data A C a K hC haH hK hB z _ _ degree depth sigma
    hdegree hdepth (bin_flatDraw A K hK hW _ h binBits)

end
end ContingencyTables.RootedCorrectionSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the executed correction sample

The two coordinate enumerations need not agree on a fixed bit string.
Their independent finite-word laws agree, which preserves every real
observable of the computed rational sample.
-/

namespace ContingencyTables.RootedCorrectionSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FairBits
open CommonBasesFPRAS FiniteLawMoments
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedCorrectionSampleLaw.freeCellDecidableEq
theorem program_sample (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (z : View A → ℕ)
    (sigma : ℚ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (N h : ℕ) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma) (bits : Words A C N h) :
    MatchingFPRAS.TreeFraction.val (RootedCorrectionSampleProgram.output
      (RootedCorrectionSampleProgram.data A C a K z v h degree depth
        (List.ofFn bits.1) (List.ofFn bits.2)))=
      sample A C a K hK hW z sigma v N h bits :=
  RootedCorrectionSampleProgram.output_data A C a K hC haH (by omega) hW hB z v h
    degree depth sigma hdegree hdepth N bits.1 bits.2

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an adjacent-parameter ratio sample

The exact ratio is either one or one half. The program compares the two
computed integer exponents and never materializes an exponential weight.
-/

namespace ContingencyTables.RootedRatioSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedCompletion
open scoped BigOperators

noncomputable section
variable {m n : ℕ}

private lemma exponent_step (A : Instance (Fin m) (Fin n)) (C a : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z v=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z v ∨
    RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z v=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z v+1 := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hd := RootedOracleDensity.D_bounds A (rowColumn A.T) C hCR z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hi : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hi := (v i).property.2; omega)
      exact hi.trans hKB)
  let x := (a:ℝ)/height A C*RootedOracleDensity.D A (rowColumn A.T) C z (realCorner v)
  let q := RootedOracleDensity.D A (rowColumn A.T) C z (realCorner v)/height A C
  have hheight := height_positive A C hCR
  have hq0 : 0 ≤ q := div_nonneg hd.1 hheight.le
  have hq1 : q ≤ 1 := (div_le_one hheight).mpr hd.2
  have he : (((a+1:ℕ):ℝ)/height A C)*RootedOracleDensity.D A (rowColumn A.T) C z (realCorner v)=x+q := by
    dsimp only [x,q]
    push_cast
    ring
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  have hs : ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by omega
  have h0 := RootedOracleDensity.gridExponent_eq_floor A (rowColumn A.T) C a z v
  have h1 := RootedOracleDensity.gridExponent_eq_floor A (rowColumn A.T) C (a+1) z v
  rw [he] at h1
  rcases hs with hs|hs
  · left
    exact_mod_cast h1.trans (hs.trans h0.symm)
  · right
    have hh : (RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z v:ℤ)=
        (RootedOracleDensity.gridExponent A (rowColumn A.T) C a z v:ℤ)+1 := by
      rw [h1,hs,h0]
    exact_mod_cast hh

lemma ratio_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    TreeFraction.val (ratio (RootedOracleStepProgram.data A C a K z v).2)=
      RootedOracleDensity.rationalRatioObservable A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) := by
  have hb : bump (RootedOracleStepProgram.data A C a K z v).2=
      (RootedOracleStepProgram.data A C (a+1) K z v).2 := rfl
  unfold ratio equalExponents
  rw [hb,RootedOracleStepProgram.evaluate_data A C (a+1) K hC,
    RootedOracleStepProgram.evaluate_data A C a K hC]
  rcases exponent_step A C a hC z hz hKB (RootedCatalogGrid.gridEquiv A K v) with he|he
  · simp only [RootedCatalogGrid.exponent,he,decide_true,ite_true, if_true,TreeFraction.val,
      Nat.cast_one,div_self (by norm_num : (1:ℚ)≠0),
      RootedOracleDensity.rationalRatioObservable,RootedOracleDensity.rationalGridWeight]
    exact (div_self (by positivity)).symm
  · have hn : RootedOracleDensity.gridExponent A (rowColumn A.T) C (a+1) z
        (RootedCatalogGrid.gridEquiv A K v)≠RootedOracleDensity.gridExponent A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) := by omega
    simp only [RootedCatalogGrid.exponent,hn,decide_false,Bool.false_eq_true,ite_false]
    simp only [TreeFraction.val,Nat.cast_one,Nat.cast_ofNat,RootedOracleDensity.rationalRatioObservable,
      RootedOracleDensity.rationalGridWeight,he,pow_succ]
    field_simp

theorem output_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*oracleStepBits A C) → Bool) :
    TreeFraction.val (output (RootedOracleWalkProgram.data A C a K z v,List.ofFn bits))=
      RootedOracleDensity.rationalRatioObservable A (rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K (RootedOracleWalkProgram.flatGridWalk A C a z v N bits)) := by
  unfold output currentInput
  rw [RootedOracleWalkProgram.flatWalk_data A C a K hC z v N bits]
  exact ratio_data A C a K hC z hz hKB _

end
end ContingencyTables.RootedRatioSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed sample blocks and the product weight estimator

The lists contain the actual sample inputs and their disjoint finite
words. Each sample is evaluated by the checked binary program before
its average or product is formed.
-/

namespace ContingencyTables.RootedEstimatorBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

attribute [local irreducible] ratioAverage correctionAverage

lemma ratioAverage_value (xs : RatioBlock) :
    TreeFraction.val (ratioAverage xs)=
      (xs.map (fun z => TreeFraction.val (RootedRatioSampleProgram.output z))).sum/(xs.length:ℚ) := by
  rw [ratioAverage,FractionAggregateProgram.average_value]
  simp only [List.map_map,Function.comp_def,List.length_map]

lemma correctionAverage_value (xs : CorrectionBlock) :
    TreeFraction.val (correctionAverage xs)=
      (xs.map (fun z => TreeFraction.val (RootedCorrectionSampleProgram.output z))).sum/(xs.length:ℚ) := by
  rw [correctionAverage,FractionAggregateProgram.average_value]
  simp only [List.map_map,Function.comp_def,List.length_map]

lemma output_value (z : Input) :
    TreeFraction.val (output z)=(z.1.1:ℚ)*
      (z.1.2.map (fun xs => TreeFraction.val (ratioAverage xs))).prod*
        TreeFraction.val (correctionAverage z.2) := by
  rw [output,TreeFraction.mul_val,factors,TreeFraction.mul_val,ratioProduct,
    FractionAggregateProgram.product_value]
  rw [show TreeFraction.val (z.1.1,1)=(z.1.1:ℚ) by
    simp only [TreeFraction.val,Nat.cast_one,div_one]]
  simp only [List.map_map,Function.comp_def]
  ring

end ContingencyTables.RootedEstimatorBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed ratio sample has the exact analysed law -/

namespace ContingencyTables.RootedRatioSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FiniteLawMoments
open CommonBasesFPRAS FiniteObservableTransport
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma program_sample (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*oracleStepBits A C) → Bool) :
    MatchingFPRAS.TreeFraction.val (RootedRatioSampleProgram.output
      (RootedOracleWalkProgram.data A C a K z v,List.ofFn bits))=sample A C a z v N bits :=
  RootedRatioSampleProgram.output_data A C a K hC z hz hKB v N bits

end
end ContingencyTables.RootedRatioSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorExecution
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal input and output of the executed estimator blocks -/

namespace ContingencyTables.RootedEstimatorExecution

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedComputedEstimator
open MatchingFPRAS FiniteObservableTransport CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma ratioBlock_value (A : Instance (Fin m) (Fin n)) (C K j a : ℕ) (hC : 0 < C)
    (delta failure : ℚ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (hB : (K:ℝ)=binWidth A C) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : RootedComputedEstimator.RatioWords A C K j delta failure) :
    TreeFraction.val (RootedEstimatorBlockProgram.ratioAverage
      (ratioBlock A C K j a delta failure z v draws))=
        RootedComputedEstimator.ratioAverage A C K j a delta failure z v draws := by
  rw [RootedEstimatorBlockProgram.ratioAverage_value]
  simp only [ratioBlock,List.map_ofFn,List.sum_ofFn,List.length_ofFn]
  unfold RootedComputedEstimator.ratioAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact RootedRatioSampleLaw.program_sample A C a K hC z hz hB.le v _ (draws i)

lemma correctionBlock_value (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (draws : RootedComputedEstimator.CorrectionWords A C K j delta failure) :
    TreeFraction.val (RootedEstimatorBlockProgram.correctionAverage
      (correctionBlock A C K j delta failure z v degree depth draws))=
        RootedComputedEstimator.correctionAverage A C K j hK hW delta failure z v draws := by
  rw [RootedEstimatorBlockProgram.correctionAverage_value]
  simp only [correctionBlock,List.map_ofFn,List.sum_ofFn,List.length_ofFn]
  unfold RootedComputedEstimator.correctionAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact RootedCorrectionSampleLaw.program_sample A C j K hC hj hK hW hB z
    (roundingTolerance delta) v _ _ degree depth hdegree hdepth (draws i)

/-- The actual list program returns the exact value of the transported
finite experiment, including unsuccessful statistical outcomes. -/
theorem output_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (draws : Inputs A C K j delta failure) :
    TreeFraction.val (RootedEstimatorBlockProgram.output
      (data A C K j delta failure z v degree depth draws))=
        RootedComputedEstimator.estimate A C K j hK hW delta failure z v draws := by
  rw [RootedEstimatorBlockProgram.output_value]
  simp only [data,List.map_ofFn,List.prod_ofFn]
  rw [correctionBlock_value A C K j hC hj hK hW hB delta failure z v degree depth hdegree hdepth]
  have hp : (∏ a : Fin j,TreeFraction.val (RootedEstimatorBlockProgram.ratioAverage
      (ratioBlock A C K j a.val delta failure z v (draws.1 a))))=
      ∏ a : Fin j,RootedComputedEstimator.ratioAverage A C K j a.val delta failure z v (draws.1 a) := by
    apply Finset.prod_congr rfl
    intro a _
    exact ratioBlock_value A C K j a.val hC delta failure z hz hB v (draws.1 a)
  simp only [Function.comp_apply]
  rw [hp]
  rfl


end
end ContingencyTables.RootedEstimatorExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorLayoutProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] frames

attribute [local irreducible] rangeValue rangeValues

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma assignmentCount_data (A : Instance (Fin m) (Fin n)) (C K j S Tr Tc h : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    assignmentCount (data A C K j S Tr Tc h z v)=CompanionOracleDensity.assignmentCount A := by
  rw [assignmentCount,frames_data,CompanionOracleDensity.assignmentCount_eq_prod]
  simp only [List.map_ofFn,List.prod_ofFn]
  exact Fintype.prod_equiv (RootedForestCatalog.freeEquiv A) _ _ (fun _ => rfl)

end
end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One flat word executes the complete weight estimator

The number of generated rows is bounded by the supplied word length.
The binary schedule therefore remains safe even on malformed inputs.
-/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

attribute [local irreducible] prepare

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma phase_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    phase (RootedOracleWalkProgram.data A C 0 K z v,a)=RootedOracleWalkProgram.data A C a K z v := rfl

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed estimator consumes exactly its independent sample banks -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS RootedEstimatorLayoutProgram
open DensePrograms GridBoundary
open scoped Classical

lemma encodeBanks_recode {j S r t b r' t' b' : ℕ} (hr : r=r') (ht : t=t') (hb : b=b')
    (state : State) (h count : ℕ) (markers : List Bool×List Bool)
    (banks : EstimatorWordBanks.Banks j S r t b) :
    encodeBanks state j h count markers (recodeBanks hr ht hb banks)=
      encodeBanks state j h count markers banks := by
  cases hr
  cases ht
  cases hb
  rfl

private lemma ratioBlock_input (c : Context) (markers : List Bool×List Bool)
    (hr : 0 < ratioWidth c) (bits : Fin (wordWidth c) → Bool) (a : Fin c.2.1.1) :
    ratioBlock (input c markers bits,a.val)=List.ofFn (fun i =>
      (phase (c.1,a.val),List.ofFn ((wordEquiv c bits).1 a i))) := by
  change (DensePrograms.wordChunks (ratioWidth c,
    DensePrograms.wordChunk ((c.2.1.2*ratioWidth c,
      (List.ofFn bits).take (c.2.1.1*(c.2.1.2*ratioWidth c))),a.val))).map
        (fun bs => (phase (c.1,a.val),bs))=_
  have hc := EstimatorWordBanks.ratio_chunks c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c) hr bits a
  have hm := congrArg (List.map (fun bs => (phase (c.1,a.val),bs))) hc
  refine hm.trans ?_
  rw [List.map_ofFn]
  rfl

private lemma ratioBlocks_input (c : Context) (markers : List Bool×List Bool)
    (hs : 0 < c.2.1.2) (hr : 0 < ratioWidth c) (bits : Fin (wordWidth c) → Bool) :
    ratioBlocks (input c markers bits)=List.ofFn (fun a => List.ofFn (fun i =>
      (phase (c.1,a.val),List.ofFn ((wordEquiv c bits).1 a i)))) := by
  have hrows : ratioRows (input c markers bits)=List.range c.2.1.1 :=
    EstimatorWordBanks.ratio_rows _ _ _ _ _ hs hr bits
  unfold ratioBlocks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hi' : i < c.2.1.1 := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact ratioBlock_input c markers hr bits ⟨i,hi'⟩

private lemma correctionBlock_input (c : Context) (markers : List Bool×List Bool)
    (ht : 0 < correctionWidth c) (bits : Fin (wordWidth c) → Bool) :
    correctionBlock (input c markers bits)=List.ofFn (fun i =>
      ((phase (c.1,c.2.1.1),c.2.2.2),
        (markers,(List.ofFn ((wordEquiv c bits).2 i).1,List.ofFn ((wordEquiv c bits).2 i).2)))) := by
  have hw : correctionWords (input c markers bits)=List.ofFn (fun i : Fin c.2.1.2 =>
      List.ofFn (gridWordEquiv c.2.1.2 (correctionWalkWidth c+binWidth c)
        (FairBits.splitWordEquiv (c.2.1.1*(c.2.1.2*ratioWidth c))
          (c.2.1.2*(correctionWalkWidth c+binWidth c)) bits).2 i)) :=
    EstimatorWordBanks.correction_chunks _ _ _ _ _ ht bits
  rw [correctionBlock,hw,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change ((phase (c.1,c.2.1.1),c.2.2.2),
    (markers,((List.ofFn _).take (correctionWalkWidth c),
      (List.ofFn _).drop (correctionWalkWidth c))))=_
  have htake := EstimatorWordBanks.correction_take c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c) bits i
  have hdrop := EstimatorWordBanks.correction_drop c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c) bits i
  exact congrArg (fun ws : List Bool × List Bool =>
    ((phase (c.1,c.2.1.1),c.2.2.2),(markers,ws))) (Prod.ext htake hdrop)

/-- Every input bit belongs to exactly one prescribed sample word.
The positivity conditions merely ensure that complete-word parsing
retains all scheduled sample rows. -/
theorem prepare_input (c : Context) (markers : List Bool×List Bool)
    (hs : 0 < c.2.1.2) (hr : 0 < ratioWidth c) (ht : 0 < correctionWidth c)
    (bits : Fin (wordWidth c) → Bool) :
    prepare (input c markers bits)=bankInput c markers (wordEquiv c bits) := by
  change ((assignmentCount c,ratioBlocks (input c markers bits)),
    correctionBlock (input c markers bits))=_
  rw [ratioBlocks_input c markers hs hr bits,correctionBlock_input c markers ht bits]
  rfl

end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

private lemma oracleTime_positive (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    0 < oracleTime A C K 1 theta := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one A.hd)
  have hk : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hh := height_positive A C (by exact_mod_cast hC)
  have hm : 0 < mixingConstant A K := by unfold mixingConstant; positivity
  have hp : 0 < mixingConstant A K*(height A C+A.d*K+16*1/theta+2) := by positivity
  have hn := Nat.le_ceil (mixingConstant A K*(height A C+A.d*K+16*1/theta+2))
  have hc : (0:ℝ) < oracleTime A C K 1 theta := by
    simpa only [oracleTime,Nat.cast_one] using hp.trans_le hn
  exact_mod_cast hc

/-- Parsing the one flat word produces precisely the sample inputs
used in the independent estimator experiment. -/
theorem prepare_scheduled (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool)
    (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
    prepare (input (scheduledContext A C K j delta failure z v) (degree,depth) bits)=
      RootedEstimatorExecution.data A C K j delta failure z v degree depth
        (scheduledEquiv A C K j delta failure z v bits) := by
  have hdelta : (0:ℝ) < delta := by exact_mod_cast hd
  have hstep := RootedOracleWalkProgram.stepWidth_pos A C hC
  have hrtime := oracleTime_positive A C K hC hK delta hdelta
  have hctime := oracleTime_positive A C K hC hK (correctionTheta delta)
    (by unfold correctionTheta; positivity)
  have hs : 0 < (scheduledContext A C K j delta failure z v).2.1.2 :=
    sampleCount_positive j delta failure hd hf
  have hr : 0 < ratioWidth (scheduledContext A C K j delta failure z v) := by
    rw [scheduledContext,ratioWidth_data]
    exact Nat.mul_pos hrtime hstep
  have ht : 0 < correctionWidth (scheduledContext A C K j delta failure z v) := by
    unfold correctionWidth
    have ht : 0 < correctionWalkWidth (scheduledContext A C K j delta failure z v) := by
      rw [scheduledContext,correctionWalkWidth_data]
      exact Nat.mul_pos hctime hstep
    omega
  rw [prepare_input _ _ hs hr ht]
  unfold bankInput
  have hc := encodeBanks_recode (ratioWidth_data A C K j _ _ _ _ z v)
    (correctionWalkWidth_data A C K j _ _ _ _ z v)
    (binWidth_data A C K j _ _ _ _ z v)
    (scheduledContext A C K j delta failure z v).1
    (scheduledContext A C K j delta failure z v).2.2.2
    (RootedEstimatorLayoutProgram.assignmentCount (scheduledContext A C K j delta failure z v))
    (degree,depth) (wordEquiv (scheduledContext A C K j delta failure z v) bits)
  refine hc.symm.trans ?_
  change encodeBanks (RootedOracleWalkProgram.data A C 0 K z v) j
    (offsetAccuracy A delta) (RootedEstimatorLayoutProgram.assignmentCount
      (scheduledContext A C K j delta failure z v)) (degree,depth)
        (scheduledEquiv A C K j delta failure z v bits)=_
  have hcount : RootedEstimatorLayoutProgram.assignmentCount
      (scheduledContext A C K j delta failure z v)=CompanionOracleDensity.assignmentCount A :=
    assignmentCount_data A C K j _ _ _ _ z v
  rw [hcount]
  unfold encodeBanks RootedEstimatorExecution.data RootedEstimatorExecution.ratioBlock
    RootedEstimatorExecution.correctionBlock RootedCorrectionSampleProgram.data
  simp only [phase_data]

theorem output_scheduled_oai (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
    TreeFraction.val (output (input (scheduledContext A C K j delta failure z v)
      (degree,depth) bits))=RootedComputedEstimator.estimate A C K j hK hW delta failure z v
        (scheduledEquiv A C K j delta failure z v bits) := by
  rw [output,prepare_scheduled A C K j hC hK delta failure hd hf z v degree depth bits]
  exact RootedEstimatorExecution.output_data A C K j hC hj hK hW hB delta failure z hz v
    degree depth hdegree hdepth _

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled_oai := @OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled_oai
