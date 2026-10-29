-- Prove2me | solution 1 for OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:34:16.382999+00:00
-- url     : https://prove2.me/submissions/3bdb3625-6a03-4381-a5a6-f5668c2887e5

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

/-- The product formula is exactly B^e times the integer bin population
divided by the total number of free assignments. -/
lemma population_eq_card (B : ℕ) (N : C → ℕ) (v : C → ℕ) :
    population B N v=(B:ℚ)^Fintype.card C*(Fintype.card (Assignments B N v):ℚ)/
      (∏ c,(N c:ℚ)) := by
  rw [assignment_card]
  simp only [population,coordinatePopulation,Finset.prod_div_distrib,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Nat.cast_prod]

private lemma reverse_bernoulli (u : ℚ) (hu : 0 ≤ u) (n : ℕ) :
    (1+u)^n*(1-(n:ℚ)*u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have haux : (1+u)*(1-((n:ℚ)+1)*u) ≤ 1-(n:ℚ)*u := by
      nlinarith [mul_nonneg (show (0:ℚ) ≤ n+1 by positivity) (sq_nonneg u)]
    calc
      _ = (1+u)^n*((1+u)*(1-((n:ℚ)+1)*u)) := by
        rw [pow_succ,Nat.cast_add,Nat.cast_one]
        ring
      _ ≤ (1+u)^n*(1-(n:ℚ)*u) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
      _ ≤ 1 := ih

/-- The source's alpha_v lies between one half and two, including the
empty-coordinate product. No large interval is enumerated to establish
the bound; its exact cardinality is the proved ceiling difference. -/
theorem population_bounds (B d : ℕ) (N : C → ℕ) (v : C → ℕ)
    (hB : 0 < B) (hd : 1 ≤ d) (hcard : Fintype.card C ≤ d)
    (hN : ∀ c,100*d*B ≤ N c) (hv : ∀ c,v c < B) :
    1/2 ≤ population B N v ∧ population B N v ≤ 2 := by
  let u : ℚ := 1/(100*(d:ℚ))
  have hdQ : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hu1 : u ≤ 1/100 := by
    dsimp only [u]
    rw [div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hcountQ : (Fintype.card C:ℚ) ≤ d := by exact_mod_cast hcard
  have hsum : (Fintype.card C:ℚ)*u ≤ 1/100 := by
    dsimp only [u]
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity : (0:ℚ)<100*d) (by norm_num : (0:ℚ)<100)]
    linarith
  have hfactor (c : C) : 1-u ≤ coordinatePopulation B (N c) (v c) ∧
      coordinatePopulation B (N c) (v c) ≤ 1+u := by
    have hh := abs_le.mp (coordinate_error B (N c) d (v c) hB hd (hN c) (hv c))
    constructor <;> linarith
  have hpos (c : C) : 0 ≤ coordinatePopulation B (N c) (v c) := by
    unfold coordinatePopulation
    positivity
  have hlo : (1-u)^Fintype.card C ≤ population B N v := by
    unfold population
    calc
      _ = ∏ _c : C,(1-u) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by linarith) (fun c _ => (hfactor c).1)
  have hup : population B N v ≤ (1+u)^Fintype.card C := by
    unfold population
    calc
      _ ≤ ∏ _c : C,(1+u) := Finset.prod_le_prod (fun c _ => hpos c) (fun c _ => (hfactor c).2)
      _ = _ := by simp
  have hbern := one_add_mul_le_pow (show (-2:ℚ) ≤ -u by linarith) (Fintype.card C)
  have hreverse := reverse_bernoulli u hu (Fintype.card C)
  have hpower : 0 ≤ (1+u)^Fintype.card C := by positivity
  constructor
  · have hh : 1-(Fintype.card C:ℚ)*u ≤ (1-u)^Fintype.card C := by
      simpa only [mul_neg,sub_eq_add_neg] using hbern
    linarith
  · nlinarith

end ContingencyTables.CompanionBinPopulation

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_add {X : Type*} [Fintype X] (f g : X → ℝ) :
    uniformAverage (fun x => f x+g x)=uniformAverage f+uniformAverage g := by
  simp [uniformAverage,Finset.sum_add_distrib,add_div]
lemma uniformAverage_mul_left {X : Type*} [Fintype X] (r : ℝ) (f : X → ℝ) :
    uniformAverage (fun x => r*f x)=r*uniformAverage f := by
  simp [uniformAverage,← Finset.mul_sum,mul_div_assoc]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

lemma uniformAverage_sum {X J : Type*} [Fintype X] [Fintype J] (f : J → X → ℝ) :
    uniformAverage (fun x => ∑ j,f j x)=∑ j,uniformAverage (f j) := by
  unfold uniformAverage
  rw [Finset.sum_comm,Finset.sum_div]

lemma uniformAverage_mono {X : Type*} [Fintype X] (f g : X → ℝ)
    (hfg : ∀ x,f x≤g x) : uniformAverage f≤uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hfg x)) (Nat.cast_nonneg _)
lemma uniformAverage_sub_const {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (r : ℝ) :
    uniformAverage (fun x => f x-r)=uniformAverage f-r := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib,sub_div]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  field_simp

open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

lemma uniformAverage_mul_const {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    uniformAverage (fun x => f x*c)=uniformAverage f*c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

end CommonBasesFPRAS

open CommonBasesFPRAS

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

lemma intervalCost_combine (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    intervalCost (a*x+b*y) ≤ a*intervalCost x+b*intervalCost y := by
  have hx0 := intervalCost_nonnegative x
  have hy0 := intervalCost_nonnegative y
  have hxl : -x ≤ intervalCost x := (le_max_left _ _).trans (le_max_right _ _)
  have hyl : -y ≤ intervalCost y := (le_max_left _ _).trans (le_max_right _ _)
  have hxu : x-1 ≤ intervalCost x := (le_max_right _ _).trans (le_max_right _ _)
  have hyu : y-1 ≤ intervalCost y := (le_max_right _ _).trans (le_max_right _ _)
  change max 0 (max (-(a*x+b*y)) (a*x+b*y-1)) ≤ a*intervalCost x+b*intervalCost y
  apply max_le
  · exact add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
  · apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hxl ha,mul_le_mul_of_nonneg_left hyl hb]
    · nlinarith [mul_le_mul_of_nonneg_left hxu ha,mul_le_mul_of_nonneg_left hyu hb]

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleCut
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual weighted bin-cut bound for the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication GridBoundary

variable {I J : Type*} [Fintype I] [Fintype J]

lemma closedBin_distances (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (x : Fin (dimension A) → ℝ) (hx : ClosedBin (corner v) x) :
    ∀ i,|x i-realCorner v i| ≤ 1 := by
  intro i
  change |x i-(corner v i:ℝ)| ≤ 1
  apply abs_le.mpr
  constructor <;> linarith [(hx i).1,(hx i).2]

lemma tube_distances (A : Instance I J) {K : ℕ} {Q : (Fin (dimension A) → ℤ) → Prop}
    (edge : CutEdge K Q) (r : ℝ) (x : Fin (dimension A) → ℝ) (hx : x ∈ edgeTube edge r) :
    (∀ i,|x i-realCorner edge.val.1 i| ≤ 1+r) ∧
      (∀ i,|x i-realCorner edge.val.2.1 i| ≤ 1+r) := by
  have hcoord (i : Fin (dimension A)) := hx i (Set.mem_univ i)
  constructor
  · intro i
    have hi := hcoord i
    dsimp [tubeLower,tubeUpper] at hi
    change |x i-(corner edge.val.1 i:ℝ)| ≤ 1+r
    by_cases he : i=edge.val.2.2
    · subst i
      simp only [ite_true, if_true] at hi
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
    · simp only [ite_eq_right he] at hi
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
  · intro i
    have hi := hcoord i
    dsimp [tubeLower,tubeUpper] at hi
    change |x i-(corner edge.val.2.1 i:ℝ)| ≤ 1+r
    by_cases he : i=edge.val.2.2
    · have hadj : (corner edge.val.2.1 i:ℝ)=(corner edge.val.1 i:ℝ)+1 := by
        simpa only [he,Int.cast_add,Int.cast_one] using
          congrArg (fun z : ℤ => (z:ℝ)) edge.property.1.1
      simp only [ite_eq_left he] at hi
      rw [hadj]
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
    · have heq : corner edge.val.2.1 i=corner edge.val.1 i :=
        congrArg Subtype.val (edge.property.1.2 i he)
      simp only [ite_eq_right he] at hi
      rw [heq]
      exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩

lemma interpolation_bounds (d K q : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hq : q ≤ d) :
    0 < denseInterpolation d K ∧ denseInterpolation d K < 1 ∧
      denseInterpolation d K*K ≤ 1/4 ∧
      (q-1:ℕ)*(2*(denseInterpolation d K*K)) ≤ (1/2:ℝ) := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hqR : (q-1:ℕ) ≤ (d:ℝ) := by exact_mod_cast (Nat.sub_le q 1).trans hq
  have hden : (0:ℝ) < 4*d*K := by positivity
  have hr : denseInterpolation d K*K=1/(4*(d:ℝ)) := by
    unfold denseInterpolation
    field_simp [ne_of_gt (show (0:ℝ)<d by linarith),ne_of_gt (show (0:ℝ)<K by linarith)]
  refine ⟨by unfold denseInterpolation; positivity,?_,?_,?_⟩
  · unfold denseInterpolation
    rw [div_lt_one hden]
    nlinarith [mul_le_mul hdR hKR (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ d)]
  · rw [hr,div_le_div_iff₀ (by positivity : (0:ℝ)<4*d) (by norm_num : (0:ℝ)<4)]
    linarith
  · rw [hr]
    have he : (q-1:ℕ)*(2*(1/(4*(d:ℝ))))=((q-1:ℕ):ℝ)/(2*d) := by ring
    rw [he,div_le_div_iff₀ (by positivity : (0:ℝ)<2*d) (by norm_num : (0:ℝ)<2)]
    linarith

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleMixing
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative mixing for the companion's actual evaluator grid -/

namespace ContingencyTables.CompanionOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_grid_card (q K : ℕ) : Fintype.card (Grid (I := Fin q) K)=K^q := by
  have hc : Fintype.card (Set.Icc (0:ℤ) ((K:ℤ)-1))=K := by
    have hh := Int.card_fintype_Icc_of_le 0 ((K:ℤ)-1)
      (show (0:ℤ) ≤ (K:ℤ)-1+1 by omega)
    omega
  simp only [Grid,Fintype.card_fun,Fintype.card_fin,hc]

lemma mixingConstant_ge_one (A : Instance I J) {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ mixingConstant A K := by
  have hd : (1:ℝ) ≤ A.d := by exact_mod_cast A.hd
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hd2 : (1:ℝ) ≤ (A.d:ℝ)^2 := one_le_pow₀ hd
  have hm : (1:ℝ) ≤ 10000*(A.d:ℝ)^2*K := by
    have hh := mul_le_mul hd2 hk (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg (A.d:ℝ))
    nlinarith
  unfold mixingConstant
  nlinarith [sq_nonneg (10000*(A.d:ℝ)^2*K-1)]

lemma cutConstant_lower (A : Instance I J) {K : ℕ} (hK : 1 ≤ K) :
    1/(10000*(A.d:ℝ)^2*K) ≤ cutConstant A K := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hk : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  calc
    _ ≤ 1/(2048*(A.d:ℝ)^2*K) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr; norm_num)
    _ = (1/(16*(A.d:ℝ)))/(128*(A.d:ℝ)*K) := by field_simp [hd.ne',hk.ne']; ring
    _ ≤ cutConstant A K :=
      div_le_div_of_nonneg_right (proposal_bounds A.d A.hd).2.1 (by positivity)

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the literal companion weight -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma ownFiber_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) :
    0 < (integerFiber A K hK (integerBin A K hK f)).card := by
  apply Finset.card_pos.mpr
  exact ⟨f,by simp [integerFiber]⟩

lemma assignmentCount_positive (A : Instance I J) : 0 < assignmentCount A := by
  let : Nonempty (FreeIndex A.small A.T A.b) := ⟨fun _ => 0⟩
  exact Fintype.card_pos


end

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

theorem population_eq_integerFiber (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    CompanionBinPopulation.population K (freeRange A) (naturalBin A v)=
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A := by
  rw [CompanionBinPopulation.population_eq_card,CompanionBinPopulation.assignment_card,
    ←integerFiber_card A K hK,
    assignmentCount_eq_prod]
  simp only [dimension,Nat.cast_prod]

theorem actual_population_bounds (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ≤ 2 := by
  have hh := CompanionBinPopulation.population_bounds K A.d (freeRange A) (naturalBin A v)
    hK A.hd (ForestScaledPenalty.free_card_le A)
    (by
      intro t
      have hb := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega)
    (naturalBin_lt A v)
  simpa only [population_eq_integerFiber A K hK] using hh

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
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
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

/-- The explicitly shifted bounded quotient draws have a uniform error
bound for every bin, including the case of no free coordinates. -/
theorem approximateBinLaw_variation (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    variation (approximateBinLaw A K hK hW v h) (exactBinLaw A K hK hW v) ≤
      (A.d:ℚ)/(2:ℚ)^(4*(h+A.d)) := by
  apply (variation_map _ _ (binOffsetValue A K hK v)).trans
  exact FairBits.dense_offset_product_variation (dimension A) h A.d (binSize A K v)
    (binSize_positive A K hK hW v) (ForestScaledPenalty.free_card_le A)

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit finite mixing schedule of the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_min_mass_exponential (A : Instance I J) (C a : ℝ)
    (ha : 0 ≤ a) (haH : a ≤ height A C) {K : ℕ} (hK : 1 ≤ K) :
    Real.exp (-(height A C+(A.d:ℝ)*K)) ≤ (2:ℝ)^(-a)/(K:ℝ)^dimension A := by
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlK : Real.log (K:ℝ) ≤ K := by
    linarith [Real.log_le_sub_one_of_pos hKR]
  have hdim : (dimension A:ℝ) ≤ A.d := by
    exact_mod_cast ForestScaledPenalty.free_card_le A
  have hsum : a*Real.log 2+(dimension A:ℝ)*Real.log (K:ℝ) ≤
      height A C+(A.d:ℝ)*K := by
    have h1 := mul_le_mul_of_nonneg_left hl2 ha
    have h2 := mul_le_mul_of_nonneg_left hlK (Nat.cast_nonneg (dimension A): (0:ℝ) ≤ dimension A)
    have h3 := mul_le_mul_of_nonneg_right hdim hKR.le
    linarith
  have hpow : (K:ℝ)^dimension A=Real.exp ((dimension A:ℝ)*Real.log (K:ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hKR]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),hpow,←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

lemma oracle_time_error (A : Instance I J) (C a theta : ℝ)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) :
    Real.exp (-(oracleTime A C K Q theta:ℝ)/mixingConstant A K)/
      ((2:ℝ)^(-a)/(K:ℝ)^dimension A) ≤ theta/(8*Q) := by
  have hM : 0 < mixingConstant A K := lt_of_lt_of_le (by norm_num) (mixingConstant_ge_one A hK)
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have htime : height A C+(A.d:ℝ)*K+16*Q/theta+2 ≤
      (oracleTime A C K Q theta:ℝ)/mixingConstant A K := by
    apply (le_div_iff₀ hM).mpr
    rw [mul_comm]
    exact Nat.le_ceil _
  have hr : (0:ℝ) < 16*Q/theta+2 := by positivity
  have hexp : Real.exp (-(16*Q/theta+2)) ≤ 1/(16*Q/theta+2) := by
    rw [Real.exp_neg]
    have hh : 16*Q/theta+2 ≤ Real.exp (16*Q/theta+2) := by
      linarith [Real.add_one_le_exp (16*Q/theta+2)]
    simpa only [one_div] using one_div_le_one_div_of_le hr hh
  have hrecip : 1/(16*Q/theta+2) ≤ theta/(8*Q) := by
    rw [div_le_div_iff₀ hr (by positivity : (0:ℝ)<8*Q)]
    have hcancel : (16*Q/theta)*theta=16*Q := div_mul_cancel₀ _ htheta.ne'
    nlinarith
  calc
    _ ≤ Real.exp (-(oracleTime A C K Q theta:ℝ)/mixingConstant A K)/
        Real.exp (-(height A C+(A.d:ℝ)*K)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
        (oracle_min_mass_exponential A C a ha haH hK)
    _ = Real.exp (-(oracleTime A C K Q theta:ℝ)/mixingConstant A K+
        (height A C+(A.d:ℝ)*K)) := by rw [←Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(16*Q/theta+2)) := Real.exp_le_exp.mpr (by simp only [neg_div]; linarith)
    _ ≤ theta/(8*Q) := hexp.trans hrecip

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded Boolean draws for the companion correction experiment -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The bin-dependent interval length only chooses a prefix of the
fixed per-coordinate word. This preserves the analyzed quotient law. -/
theorem binWordDraw_law (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    mapLaw (uniformLaw (α := BinWords A h)) (binWordDraw A K hK hW v h)=
      approximateBinLaw A K hK hW v h := by
  unfold binWordDraw approximateBinLaw
  rw [←mapLaw_comp,←pi_uniformLaw]
  rw [pi_mapLaw (fun i : Fin (dimension A) =>
    uniformLaw (α := Fin (offsetBitLength (freeRange A (index A i)) h A.d) → Bool))
    (fun i bits => scaledBitInteger (binSize A K v i)
      (offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)
      (prefixWord (binBits_le A K hK v h i) bits))]
  congr 1
  congr 1
  funext i
  rw [padded_draw_law]
  exact scaledBitIntegerLaw_eq _ _ _

lemma flatBinDraw_law (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (binWordBits A h) → Bool)) (flatBinDraw A K hK hW v h)=
      approximateBinLaw A K hK hW v h := by
  unfold flatBinDraw
  rw [←map_equiv (binWordEquiv A h),uniform_equiv,binWordDraw_law]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RationalRootBisection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-depth rational bisection for the correction power of two -/

namespace ContingencyTables.RationalRootBisection

noncomputable section

/-- The target is used only in correctness, never by the algorithm. -/
theorem interval_contains (c : ℚ) (s : ℕ) (hs : 0 < s) (t : ℝ)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hroot : t^s=(c:ℝ)) (n : ℕ) :
    0 ≤ ((interval c s n).1:ℝ) ∧ ((interval c s n).1:ℝ) ≤ t ∧
      t ≤ ((interval c s n).2:ℝ) ∧ ((interval c s n).2:ℝ) ≤ 8 := by
  induction n with
  | zero => simpa only [interval,Rat.cast_zero,Rat.cast_ofNat] using ⟨le_refl 0,ht,ht8,le_refl 8⟩
  | succ n ih =>
    let ab := interval c s n
    let m : ℚ := (ab.1+ab.2)/2
    have hm0 : (0:ℝ) ≤ m := by
      dsimp only [m]
      push_cast
      change 0 ≤ (((interval c s n).1:ℝ)+((interval c s n).2:ℝ))/2
      linarith [ih.1,ih.2.1,ih.2.2.1]
    have hml : ((ab.1:ℚ):ℝ) ≤ m := by
      dsimp only [m,ab]
      push_cast
      linarith [ih.2.1,ih.2.2.1]
    have hmu : (m:ℝ) ≤ ab.2 := by
      dsimp only [m,ab]
      push_cast
      linarith [ih.2.1,ih.2.2.1]
    change 0 ≤ ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).1:ℝ) ∧
      ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).1:ℝ) ≤ t ∧
      t ≤ ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).2:ℝ) ∧
      ((if m^s ≤ c then (m,ab.2) else (ab.1,m)).2:ℝ) ≤ 8
    by_cases h : m^s ≤ c
    · simp only [h,ite_true, if_true]
      have hp : (m:ℝ)^s ≤ t^s := by rw [hroot]; exact_mod_cast h
      exact ⟨hm0,le_of_pow_le_pow_left₀ hs.ne' ht hp,ih.2.2.1,ih.2.2.2⟩
    · simp only [h,ite_false]
      have hp : t^s < (m:ℝ)^s := by rw [hroot]; exact_mod_cast (lt_of_not_ge h)
      exact ⟨ih.1,ih.2.1,(lt_of_pow_lt_pow_left₀ s hm0 hp).le,hmu.trans ih.2.2.2⟩

lemma interval_width (c : ℚ) (s n : ℕ) :
    (interval c s n).2-(interval c s n).1=8/(2:ℚ)^n := by
  induction n with
  | zero => norm_num [interval]
  | succ n ih =>
    simp only [interval,pow_succ]
    split_ifs <;> dsimp only
    all_goals
      have hn : (2:ℚ)^n≠0 := pow_ne_zero _ (by norm_num)
      field_simp [hn] at ih ⊢
      nlinarith

/-- A fixed depth yields an absolute error certificate for every rational
power comparison path. -/
theorem midpoint_error (c : ℚ) (s : ℕ) (hs : 0 < s) (t : ℝ)
    (ht : 0 ≤ t) (ht8 : t ≤ 8) (hroot : t^s=(c:ℝ)) (n : ℕ) :
    |(midpoint c s n:ℝ)-t| ≤ 8/(2:ℝ)^n := by
  have hb := interval_contains c s hs t ht ht8 hroot n
  have hw : ((interval c s n).2:ℝ)-((interval c s n).1:ℝ)=8/(2:ℝ)^n := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) (interval_width c s n)
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using hh
  unfold midpoint
  push_cast
  exact abs_le.mpr ⟨by linarith [hb.2.1,hb.2.2.1],by linarith [hb.2.1,hb.2.2.1]⟩

end

end ContingencyTables.RationalRootBisection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PowerOfTwoApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded rational approximation to the evaluator's power of two -/

namespace ContingencyTables.PowerOfTwoApproximation

open RationalRootBisection

noncomputable section

lemma rounded_bounds (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    rounded beta s ≤ (beta:ℝ) ∧ (beta:ℝ)-rounded beta s ≤ 1/(s:ℝ) := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hlow : (numerator beta s:ℚ) ≤ (s:ℚ)*beta := Int.floor_le _
  have hhigh : (s:ℚ)*beta < (numerator beta s:ℚ)+1 := Int.lt_floor_add_one _
  have hl : (numerator beta s:ℝ) ≤ (s:ℝ)*(beta:ℝ) := by exact_mod_cast hlow
  have hu : (s:ℝ)*(beta:ℝ) < (numerator beta s:ℝ)+1 := by exact_mod_cast hhigh
  constructor
  · exact (div_le_iff₀ hsR).mpr (by simpa only [mul_comm] using hl)
  · unfold rounded
    apply (le_div_iff₀ hsR).mpr
    have he : ((beta:ℝ)-(numerator beta s:ℝ)/(s:ℝ))*(s:ℝ)=
        (s:ℝ)*(beta:ℝ)-(numerator beta s:ℝ) := by field_simp
    rw [he]
    linarith

lemma rounded_power_root (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    ((2:ℝ)^rounded beta s)^s=(((2:ℚ)^numerator beta s:ℚ):ℝ) := by
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
  unfold rounded
  rw [div_mul_cancel₀ _ hsR,Real.rpow_intCast]
  exact (Rat.cast_zpow _ _).symm

/-- Rounding downward loses at most 1/s in relative value. The proof uses
only the tangent bound for exp and log 2 ≤ 1. -/
lemma rounded_power_error (beta : ℚ) (s : ℕ) (hs : 0 < s) :
    0 ≤ (2:ℝ)^(beta:ℝ)-(2:ℝ)^rounded beta s ∧
      (2:ℝ)^(beta:ℝ)-(2:ℝ)^rounded beta s ≤ (2:ℝ)^(beta:ℝ)/(s:ℝ) := by
  have hb := rounded_bounds beta s hs
  have hT : 0 < (2:ℝ)^(beta:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hd : rounded beta s-(beta:ℝ) ≤ 0 := by linarith [hb.1]
  have hmul := mul_le_mul_of_nonpos_right hlog hd
  have he := Real.add_one_le_exp (Real.log 2*(rounded beta s-(beta:ℝ)))
  have hlower : 1-1/(s:ℝ) ≤ (2:ℝ)^rounded beta s/(2:ℝ)^(beta:ℝ) := by
    rw [←Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [hb.2]
  have hprod := (le_div_iff₀ hT).mp hlower
  constructor
  · exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) hb.1)
  · calc
      _ ≤ (2:ℝ)^(beta:ℝ)-(1-1/(s:ℝ))*(2:ℝ)^(beta:ℝ) := by linarith
      _ = _ := by ring

/-- The only non-rational quantity in the proof is the target. The
returned value is the midpoint of a fixed number of rational comparisons. -/
theorem approximation_error (beta : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (s n : ℕ) (hs : 0 < s) (sigma : ℝ)
    (hbudget : 1/(s:ℝ)+32/(2:ℝ)^n ≤ sigma) :
    |(approximation beta s n:ℝ)-(2:ℝ)^(beta:ℝ)| ≤ sigma*(2:ℝ)^(beta:ℝ) := by
  have hb := rounded_bounds beta s hs
  have hp := rounded_power_error beta s hs
  have ht0 : 0 ≤ (2:ℝ)^rounded beta s := (Real.rpow_pos_of_pos (by norm_num) _).le
  have ht8 : (2:ℝ)^rounded beta s ≤ 8 := by
    have hr : rounded beta s ≤ 2 := hb.1.trans (by exact_mod_cast hhi)
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr
    norm_num at hh
    linarith
  have hT : (1/4:ℝ) ≤ (2:ℝ)^(beta:ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (-2:ℝ) ≤ (beta:ℝ) by exact_mod_cast hlo)
    norm_num at hh
    exact hh
  have he := midpoint_error ((2:ℚ)^numerator beta s) s hs ((2:ℝ)^rounded beta s)
    ht0 ht8 (rounded_power_root beta s hs) n
  have hscale : 8/(2:ℝ)^n ≤ (32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ 32/(2:ℝ)^n by positivity)
    convert hh using 1 <;> first | rfl | ring
  have htpos : 0 ≤ (2:ℝ)^(beta:ℝ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ |(approximation beta s n:ℝ)-(2:ℝ)^rounded beta s|+
        |(2:ℝ)^rounded beta s-(2:ℝ)^(beta:ℝ)| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        ((approximation beta s n:ℝ)-(2:ℝ)^rounded beta s)
        ((2:ℝ)^rounded beta s-(2:ℝ)^(beta:ℝ))
    _ ≤ 8/(2:ℝ)^n+(2:ℝ)^(beta:ℝ)/(s:ℝ) := by
      exact add_le_add he (by rw [abs_of_nonpos (by linarith [hp.1])]; linarith [hp.2])
    _ ≤ (32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ)+(2:ℝ)^(beta:ℝ)/(s:ℝ) := add_le_add hscale le_rfl
    _ = (1/(s:ℝ)+32/(2:ℝ)^n)*(2:ℝ)^(beta:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget htpos

lemma degree_positive (sigma : ℚ) (hsigma : 0 < sigma) : 0 < rootDegree sigma := by
  have h := Nat.le_ceil (128/sigma:ℚ)
  have hp : (0:ℚ) < 128/sigma := by positivity
  have hc : (0:ℚ) < rootDegree sigma := lt_of_lt_of_le hp h
  exact_mod_cast hc

lemma error_budget (sigma : ℚ) (hsigma : 0 < sigma) :
    1/(rootDegree sigma:ℝ)+32/(2:ℝ)^depth sigma ≤ (sigma:ℝ) := by
  have hs := degree_positive sigma hsigma
  have hsR : (0:ℝ) < rootDegree sigma := by exact_mod_cast hs
  have hsigmaR : (0:ℝ) < sigma := by exact_mod_cast hsigma
  have hceil : (128:ℝ)/(sigma:ℝ) ≤ rootDegree sigma := by
    have hh := Nat.le_ceil (128/sigma:ℚ)
    exact_mod_cast hh
  have hpow : (rootDegree sigma:ℝ) ≤ (2:ℝ)^depth sigma := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (rootDegree sigma)
  have hrec : 1/(rootDegree sigma:ℝ) ≤ (sigma:ℝ)/128 := by
    rw [div_le_div_iff₀ hsR (by norm_num : (0:ℝ)<128)]
    have hh := (div_le_iff₀ hsigmaR).mp hceil
    nlinarith
  have hrec' : 32/(2:ℝ)^depth sigma ≤ (sigma:ℝ)/4 := by
    apply (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 32) hsR hpow).trans
    rw [div_le_div_iff₀ hsR (by norm_num : (0:ℝ)<4)]
    have hh := (div_le_iff₀ hsigmaR).mp hceil
    nlinarith
  linarith

theorem approximate_error (beta sigma : ℚ) (hlo : -2 ≤ beta) (hhi : beta ≤ 2)
    (hsigma : 0 < sigma) :
    |(approximate beta sigma:ℝ)-(2:ℝ)^(beta:ℝ)| ≤ (sigma:ℝ)*(2:ℝ)^(beta:ℝ) :=
  approximation_error beta hlo hhi _ _ (degree_positive sigma hsigma) _ (error_budget sigma hsigma)

end

end ContingencyTables.PowerOfTwoApproximation

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

lemma rationalPopulation_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (f : FreeIndex A.small A.T A.b) : 0 < rationalPopulation A K hK f := by
  unfold rationalPopulation
  apply div_pos
  · exact mul_pos (pow_pos (by exact_mod_cast hK) _) (by exact_mod_cast ownFiber_positive A K hK f)
  · exact_mod_cast assignmentCount_positive A

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteIndependentAverages
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of averages of actual independent finite experiments -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

omit [Fintype X] [Nonempty X] in
lemma sampleSum_cons (g : X → ℝ) (N : ℕ) (x : X) (xs : Fin N → X) :
    sampleSum g (N+1) (Fin.cons x xs)=g x+sampleSum g N xs := by
  simp only [sampleSum,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma centered_mean (g : X → ℝ) :
    uniformAverage (fun x => g x-uniformAverage g)=0 := by
  rw [uniformAverage_sub_const,sub_self]

lemma sampleSum_mean_zero (g : X → ℝ) (hg : uniformAverage g=0) (N : ℕ) :
    uniformAverage (sampleSum g N)=0 := by
  induction N with
  | zero =>
    change uniformAverage (fun xs : Fin 0 → X => sampleSum g 0 xs)=0
    simp [sampleSum,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ]
    have he (x : X) : uniformAverage (fun xs : Fin N → X => sampleSum g (N+1) (Fin.cons x xs))=g x := by
      simp_rw [sampleSum_cons]
      rw [uniformAverage_add,uniformAverage_const,ih,add_zero]
    simp_rw [he]
    exact hg

/-- Mixed terms vanish because each coordinate is an independent uniform
finite experiment, not because of an assumed concentration oracle. -/
theorem sampleSum_secondMoment (g : X → ℝ) (hg : uniformAverage g=0) (N : ℕ) :
    uniformAverage (fun xs : Fin N → X => (sampleSum g N xs)^2)=
      N*uniformAverage (fun x => (g x)^2) := by
  induction N with
  | zero => simp [sampleSum,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ]
    have he (x : X) :
        uniformAverage (fun xs : Fin N → X => (sampleSum g (N+1) (Fin.cons x xs))^2)=
        (g x)^2+N*uniformAverage (fun y => (g y)^2) := by
      have hfun : (fun xs : Fin N → X => (sampleSum g (N+1) (Fin.cons x xs))^2)=
          fun xs => ((g x)^2+(2*g x)*sampleSum g N xs)+(sampleSum g N xs)^2 := by
        funext xs
        rw [sampleSum_cons]
        ring
      rw [hfun,uniformAverage_add,uniformAverage_add,uniformAverage_const,
        uniformAverage_mul_left,sampleSum_mean_zero g hg N,ih]
      ring
    simp_rw [he]
    rw [uniformAverage_add,uniformAverage_const]
    push_cast
    ring

omit [Nonempty X] in
lemma sampleAverage_centered (g : X → ℝ) (N : ℕ) (hN : 0 < N) (xs : Fin N → X) :
    sampleAverage g N xs-uniformAverage g=
      sampleSum (fun x => g x-uniformAverage g) N xs/N := by
  have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  unfold sampleAverage sampleSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [hNR]

theorem sampleAverage_secondMoment (g : X → ℝ) (N : ℕ) (hN : 0 < N) :
    uniformAverage (fun xs : Fin N → X => (sampleAverage g N xs-uniformAverage g)^2)=
      uniformAverage (fun x => (g x-uniformAverage g)^2)/N := by
  have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  simp_rw [sampleAverage_centered g N hN,div_pow,div_eq_mul_inv]
  rw [uniformAverage_mul_const,sampleSum_secondMoment _ (centered_mean g)]
  field_simp [hNR]

lemma mean_bounds (g : X → ℝ) (L U : ℝ) (hg : ∀ x,L ≤ g x ∧ g x ≤ U) :
    L ≤ uniformAverage g ∧ uniformAverage g ≤ U := by
  constructor
  · simpa only [uniformAverage_const] using uniformAverage_mono (fun _ : X => L) g (fun x => (hg x).1)
  · simpa only [uniformAverage_const] using uniformAverage_mono g (fun _ : X => U) (fun x => (hg x).2)

end

end ContingencyTables.FiniteIndependentAverages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteBiasedAverages
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent finite experiments with an explicitly bounded mean bias -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

theorem sampleAverage_absolute_failure (g : X → ℝ) (N : ℕ) (hN : 0 < N)
    (r : ℝ) (hr : 0 < r) :
    uniformAverage (fun xs : Fin N → X =>
      if r < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
      uniformAverage (fun x => (g x-uniformAverage g)^2)/(N*r^2) := by
  have hp (xs : Fin N → X) :
      (if r < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
        (sampleAverage g N xs-uniformAverage g)^2/r^2 := by
    split_ifs with h
    · rw [le_div_iff₀ (sq_pos_of_pos hr)]
      simpa only [one_mul,sq_abs] using
        (sq_le_sq₀ hr.le (abs_nonneg _)).mpr h.le
    · positivity
  calc
    _ ≤ uniformAverage (fun xs : Fin N → X =>
        (sampleAverage g N xs-uniformAverage g)^2/r^2) := uniformAverage_mono _ _ hp
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [uniformAverage_mul_const,sampleAverage_secondMoment g N hN]
      ring

lemma bounded_variance (g : X → ℝ) (U : ℝ)
    (hg : ∀ x,0 ≤ g x ∧ g x ≤ U) :
    uniformAverage (fun x => (g x-uniformAverage g)^2) ≤ U^2 := by
  have hm := mean_bounds g 0 U hg
  have hU : 0 ≤ U := hm.1.trans hm.2
  have hp (x : X) : (g x-uniformAverage g)^2 ≤ U^2 := by
    have habs : |g x-uniformAverage g| ≤ U := abs_le.mpr ⟨by linarith [(hg x).1],by linarith [(hg x).2]⟩
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hU).mpr habs
  simpa only [uniformAverage_const] using uniformAverage_mono _ (fun _ : X => U^2) hp

/-- The target is an exact mathematical mean; the experiment's own mean
may differ, but only by the displayed deterministic bias. -/
theorem biased_target_failure (g : X → ℝ) (U target delta : ℝ)
    (hg : ∀ x,0 ≤ g x ∧ g x ≤ U) (htarget : 0 < target) (hdelta : 0 < delta)
    (hbias : |uniformAverage g-target| ≤ delta*target/2)
    (N : ℕ) (hN : 0 < N) :
    uniformAverage (fun xs : Fin N → X =>
      if delta*target < |sampleAverage g N xs-target| then (1:ℝ) else 0) ≤
      4*U^2/(N*(delta*target)^2) := by
  have hr : 0 < delta*target/2 := by positivity
  have hp (xs : Fin N → X) :
      (if delta*target < |sampleAverage g N xs-target| then (1:ℝ) else 0) ≤
        if delta*target/2 < |sampleAverage g N xs-uniformAverage g| then 1 else 0 := by
    split_ifs with h h'
    · rfl
    · exfalso
      have hh : |sampleAverage g N xs-target| ≤
          |sampleAverage g N xs-uniformAverage g|+|uniformAverage g-target| := by
        simpa only [sub_add_sub_cancel] using abs_add_le
          (sampleAverage g N xs-uniformAverage g) (uniformAverage g-target)
      have hn := le_of_not_gt h'
      linarith
    · norm_num
    · rfl
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ uniformAverage (fun xs : Fin N → X =>
        if delta*target/2 < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) :=
      uniformAverage_mono _ _ hp
    _ ≤ uniformAverage (fun x => (g x-uniformAverage g)^2)/(N*(delta*target/2)^2) :=
      sampleAverage_absolute_failure g N hN _ hr
    _ ≤ U^2/(N*(delta*target/2)^2) :=
      div_le_div_of_nonneg_right (bounded_variance g U hg) (by positivity)
    _ = _ := by
      field_simp [hNR.ne',hdelta.ne',htarget.ne']; ring

end

end ContingencyTables.FiniteIndependentAverages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawMoments
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma expectation_map [DecidableEq Y] (p : RationalLaw X) (draw : X → Y) (g : Y → ℝ) :
    expectation (mapLaw p draw) g=expectation p (fun x => g (draw x)) := by
  unfold expectation mapLaw
  simp only [Rat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Y,if draw x=y then (p.mass x:ℝ)*g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = _ := by simp

lemma expectation_uniform [Nonempty X] (g : X → ℝ) :
    expectation (uniformLaw (α := X)) g=uniformAverage g := by
  unfold expectation uniformLaw uniformMass uniformAverage
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [←Finset.mul_sum]
  ring

lemma word_expectation [Nonempty X] [DecidableEq Y] (draw : X → Y) (g : Y → ℝ) :
    uniformAverage (fun x => g (draw x))=expectation (mapLaw (uniformLaw (α := X)) draw) g := by
  rw [expectation_map,expectation_uniform]

/-- Bounded real observables may be evaluated after a rational finite
experiment. Their expectation error follows from the actual output TV. -/
theorem expectation_difference (p q : RationalLaw X) (g : X → ℝ) (U : ℝ)
    (hg : ∀ x,|g x| ≤ U) :
    |expectation p g-expectation q g| ≤ 2*U*(variation p q:ℝ) := by
  have he : expectation p g-expectation q g=∑ x,((p.mass x:ℝ)-(q.mass x:ℝ))*g x := by
    unfold expectation
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ x,|((p.mass x:ℝ)-(q.mass x:ℝ))*g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x,|(p.mass x:ℝ)-(q.mass x:ℝ)| * U := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg x) (abs_nonneg _)
    _ = _ := by
      rw [←Finset.sum_mul]
      simp only [variation,Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat]
      ring

lemma expectation_bounds (p : RationalLaw X) (g : X → ℝ) (L U : ℝ)
    (hg : ∀ x,L ≤ g x ∧ g x ≤ U) : L ≤ expectation p g ∧ expectation p g ≤ U := by
  have htotal : ∑ x,(p.mass x:ℝ)=1 := by exact_mod_cast p.total
  unfold expectation
  constructor
  · calc
      L = ∑ x,(p.mass x:ℝ)*L := by rw [←Finset.sum_mul,htotal,one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).1 (by exact_mod_cast p.nonnegative x))
  · calc
      _ ≤ ∑ x,(p.mass x:ℝ)*U := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).2 (by exact_mod_cast p.nonnegative x))
      _ = U := by rw [←Finset.sum_mul,htotal,one_mul]

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawRelativeError
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing deterministic relative error through a finite law -/

namespace ContingencyTables.FiniteLawMoments

open ResidualMixture
open scoped BigOperators

variable {X : Type*} [Fintype X]

lemma expectation_relative_error (p : RationalLaw X) (f g : X → ℝ) (delta : ℝ)
    (herror : ∀ x,|g x-f x| ≤ delta*f x) :
    |expectation p g-expectation p f| ≤ delta*expectation p f := by
  have he : expectation p g-expectation p f=∑ x,(p.mass x:ℝ)*(g x-f x) := by
    unfold expectation
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ x,|(p.mass x:ℝ)*(g x-f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x,(p.mass x:ℝ)*(delta*f x) := by
      apply Finset.sum_le_sum
      intro x _
      have hp : (0:ℝ) ≤ p.mass x := by exact_mod_cast p.nonnegative x
      rw [abs_mul,abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (herror x) hp
    _ = _ := by
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end ContingencyTables.FiniteLawMoments

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

private lemma le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 < 2^n := pow_pos (by decide) _
    rw [pow_succ]
    omega

lemma offsetAccuracy_error (A : Instance I J) (delta : ℚ) (hdelta : 0 < delta) :
    (A.d:ℝ)/(2:ℝ)^(4*(offsetAccuracy A delta+A.d)) ≤ (delta:ℝ)/4096 := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hh : (4096:ℝ)*A.d/(delta:ℝ) ≤ offsetAccuracy A delta := by
    have hb := Nat.le_ceil (4096*(A.d:ℚ)/delta)
    unfold offsetAccuracy
    exact_mod_cast hb
  have he : offsetAccuracy A delta ≤ 2^(4*(offsetAccuracy A delta+A.d)) := by
    exact (le_two_pow _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : (offsetAccuracy A delta:ℝ) ≤ (2:ℝ)^(4*(offsetAccuracy A delta+A.d)) := by exact_mod_cast he
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2^(4*(offsetAccuracy A delta+A.d))) (by norm_num : (0:ℝ)<4096)]
  have hb := (div_le_iff₀ hd).mp hh
  nlinarith [mul_le_mul_of_nonneg_left hp hd.le]

lemma correction_noise_budget (A : Instance I J) (delta : ℚ) (hdelta : 0 < delta) :
    correctionTheta delta/(8*1)+(A.d:ℝ)/(2:ℝ)^(4*(offsetAccuracy A delta+A.d)) ≤
      (delta:ℝ)/1024 := by
  have hh := offsetAccuracy_error A delta hdelta
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  unfold correctionTheta
  linarith

lemma sampleCount_positive (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) : 0 < sampleCount j delta failure := by
  have hh := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
  have hp : (0:ℚ) < sampleCount j delta failure := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast hp

/-- Every one of the j ratio averages and the final correction average
has failure at most this common share. -/
lemma sampleCount_budget (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) :
    16384/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) ≤ (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hf : (0:ℝ) < failure := by exact_mod_cast hfailure
  have hN : (0:ℝ) < sampleCount j delta failure := by
    exact_mod_cast sampleCount_positive j delta failure hdelta hfailure
  have hh : (65536:ℝ)*((j:ℝ)+1)/((failure:ℝ)*(delta:ℝ)^2) ≤ sampleCount j delta failure := by
    have hb := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
    unfold sampleCount
    exact_mod_cast hb
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (sampleCount j delta failure:ℝ)*(delta:ℝ)^2)
    (by positivity : (0:ℝ) < 4*((j:ℝ)+1))]
  have hb := (div_le_iff₀ (show (0:ℝ) < (failure:ℝ)*(delta:ℝ)^2 by positivity)).mp hh
  nlinarith

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteIndependentFailures
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate marginals and a union bound for independent finite blocks -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

lemma uniformAverage_coordinate {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j,Fintype (X j)] [∀ j,Nonempty (X j)] (i : J) (g : X i → ℝ) :
    uniformAverage (fun x : (j : J) → X j => g (x i))=uniformAverage g := by
  have he := uniformAverage_equiv (Equiv.piSplitAt i X) (fun x => g x.1)
  change uniformAverage (fun x : (j : J) → X j => g (x i))=
    uniformAverage (fun x : X i × ((j : {j // j≠i}) → X j.val) => g x.1) at he
  rw [he,uniformAverage_prod]
  simp_rw [uniformAverage_const]

lemma uniform_union_bound {X J : Type*} [Fintype X] [Fintype J]
    (bad : J → X → Prop) :
    uniformAverage (fun x => if ∃ j,bad j x then (1:ℝ) else 0) ≤
      ∑ j,uniformAverage (fun x => if bad j x then (1:ℝ) else 0) := by
  rw [←uniformAverage_sum]
  apply uniformAverage_mono
  intro x
  by_cases h : ∃ j,bad j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    calc
      1 = (if bad j x then (1:ℝ) else 0) := by rw [ite_eq_left hj]
      _ ≤ ∑ k : J,if bad k x then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun k => if bad k x then (1:ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

end

end ContingencyTables.FiniteIndependentAverages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleEstimator
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma rationalAverage_cast {X : Type*} (g : X → ℚ) (N : ℕ) (draws : Fin N → X) :
    (rationalAverage g N draws:ℝ)=sampleAverage (fun x => (g x:ℝ)) N draws := by
  simp only [rationalAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,sampleAverage,sampleSum]

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

lemma average_fintype_irrel {X : Type*} (s t : Fintype X) (f : X → ℝ) :
    @uniformAverage X s f=@uniformAverage X t f := by
  cases Subsingleton.elim s t
  rfl

end

end ContingencyTables.CompanionOracleDensity

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
  intervalCost_combine free_card_le tree_card_le)

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

theorem penalty_convex (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (hC : 0≤ C) (x q : I → J → ℤ) :
    ConvexOn ℝ Set.univ (penalty A S C B x q) := by
  refine ⟨convex_univ,?_⟩
  intro v _ w _ a b ha hb hab
  have hsum : (∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q (a • v+b • w) t))≤
      a*(∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q v t))+
        b*(∑ t : TreeCell A.T,intervalCost (scaledTree A S B x q w t)) := by
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    unfold scaledTree
    rw [AffinePenalty.affineValue_combine _ _ _ _ _ _ hab]
    exact intervalCost_combine _ _ _ _ ha hb hab
  unfold penalty
  have hh := mul_le_mul_of_nonneg_left hsum hC
  simp only [smul_eq_mul]
  nlinarith [congrArg (fun z => C*z*rootConstant A S x q) hab]

theorem penalty_continuous (A : Instance I J) (S : Selection A.T)
    (C B : ℝ) (x q : I → J → ℤ) : Continuous (penalty A S C B x q) := by
  apply continuous_const.mul
  apply continuous_const.add
  apply continuous_finsetSum
  intro t _
  have hs : Continuous (fun v => scaledTree A S B x q v t) := by
    exact continuous_const.add (continuous_finsetSum Finset.univ
      (fun f _ => continuous_const.mul (continuous_apply f)))
  exact continuous_const.max (hs.neg.max (hs.sub continuous_const))

end ContingencyTables.RootedScaledPenalty

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

theorem D_continuous (A : Instance I J) (S : Selection A.T) (C : ℝ)
    (z : View A → ℕ) : Continuous (D A S C z) := by
  have hpull : Continuous (pull A) := continuous_pi (fun f => continuous_apply ((index A).symm f))
  exact (RootedScaledPenalty.penalty_continuous A S C (binWidth A C)
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)).comp hpull

theorem D_convex (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0≤ C)
    (z : View A → ℕ) : ConvexOn ℝ Set.univ (D A S C z) := by
  refine ⟨convex_univ,?_⟩
  intro v _ w _ a b ha hb hab
  exact (RootedScaledPenalty.penalty_convex A S C (binWidth A C) hC
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z)).2
      (Set.mem_univ (pull A v)) (Set.mem_univ (pull A w)) ha hb hab

theorem rho_continuous (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) : Continuous (rho A S C a z) :=
  DenseWeights.density_continuous _ _ (D_continuous A S C z)

theorem rho_positive (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℝ) : 0 < rho A S C a z v :=
  DenseWeights.density_pos _ _ _

theorem rho_logConcave (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (z : View A → ℕ) :
    PublishedInputs.LogConcaveOn (rho A S C a z) Set.univ :=
  DenseWeights.density_logConcave _
    (div_nonneg ha (CompanionOracleDensity.height_positive A C hC).le) _ _
    (D_convex A S C hC.le z)

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

theorem bin_comparison (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (v w : Fin (dimension A) → ℝ) (hvw : ∀ i,|v i-w i|≤1) :
    V A S C a z v/4≤ rho A S C a z w ∧ rho A S C a z w≤2*V A S C a z v := by
  have hh := exponent_change A S C a hC ha haH z w v 1 (by norm_num)
    (fun i => by simpa only [abs_sub_comm] using hvw i)
  exact DenseWeights.bin_density_comparison _ _ w v (hh.trans (by norm_num))

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the computed-root completion count

Integer bins and their executable interval draws are the existing
physical bins.  Only their positive density weights change with the
explicit root selector.  All normalizer identities are finite sums.
-/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GridBoundary
open CompanionOracleDensity (dimension index pull binWidth height integerPoint integerBin integerFiber
  assignmentCount ownFiber_positive assignmentCount_positive )

variable {I J : Type*} [Fintype I] [Fintype J]

lemma gridWeight_positive (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    0<gridWeight A S C a z v := DenseWeights.binWeight_pos _ _ _

theorem correction_bounds (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (hC : 0<C) (ha : 0≤ a) (haH : a≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0<K) (hW : 100*A.d*K≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (f : FreeIndex A.small A.T A.b) :
    1/8≤ correction A S C a z K hK f ∧ correction A S C a z K hK f≤4 := by
  let v := integerBin A K hK f
  have hpQ := CompanionOracleDensity.actual_population_bounds A K hK hW v
  have hp : (1/2:ℝ)≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A≤2 := by
    constructor
    · simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.1
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]
        using (Rat.cast_le (K := ℝ)).mpr hpQ.2
  have hdist : ∀ i,|realCorner v i-integerPoint A C f i|≤1 := by
    intro i
    simpa only [abs_sub_comm] using CompanionOracleDensity.integerPoint_distance A C K hK hB f i
  have hb := bin_comparison A S C a hC ha haH z (realCorner v) (integerPoint A C f) hdist
  have hw := gridWeight_positive A S C a z v
  have hr : (1/4:ℝ)≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v ∧
      rho A S C a z (integerPoint A C f)/gridWeight A S C a z v≤2 := by
    constructor
    · apply (le_div_iff₀ hw).mpr
      simpa only [gridWeight,div_eq_mul_inv,mul_comm,one_mul] using hb.1
    · exact (div_le_iff₀ hw).mpr (by simpa only [gridWeight] using hb.2)
  have he : correction A S C a z K hK f=
      ((K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)*
        (rho A S C a z (integerPoint A C f)/gridWeight A S C a z v) := by
    unfold correction
    ring
  rw [he]
  constructor
  · have hh := mul_le_mul hp.1 hr.1 (by norm_num : (0:ℝ)≤1/4) (by linarith :
        0≤(K:ℝ)^dimension A*(integerFiber A K hK v).card/assignmentCount A)
    norm_num at hh ⊢
    exact hh
  · have hh := mul_le_mul hp.2 hr.2 (by linarith [hr.1] :
        0≤ rho A S C a z (integerPoint A C f)/gridWeight A S C a z v)
      (by norm_num : (0:ℝ)≤2)
    norm_num at hh ⊢
    exact hh

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleCut
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root density satisfies the actual weighted grid cut bound -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication GridBoundary
open CompanionOracleDensity (dimension height closedBin_distances tube_distances interpolation_bounds)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma tube_comparison (A : Instance I J) (S : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} {Q : (Fin (dimension A) → ℤ) → Prop} (edge : CutEdge K Q)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : Fin (dimension A) → ℝ)
    (hx : x ∈ edgeTube edge r) :
    rho A S C a z x ≤ 4*min (V A S C a z (realCorner edge.val.1))
      (V A S C a z (realCorner edge.val.2.1)) := by
  obtain ⟨hlo,hhi⟩ := _root_.OAI.ContingencyTables.CompanionOracleDensity.tube_distances A edge r x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  apply le_min
  · apply DenseWeights.tube_density_comparison
    exact (exponent_change A S C a hC ha haH z x _ (1+r) (by positivity) hlo).trans (by linarith)
  · apply DenseWeights.tube_density_comparison
    exact (exponent_change A S C a hC ha haH z x _ (1+r) (by positivity) hhi).trans (by linarith)

/-- The companion bin weights satisfy the source cut bound directly
from their actual forest density and the precise published PL input. -/
theorem weighted_min_cut (A : Instance I J) (S : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (Q : (Fin (dimension A) → ℤ) → Prop)
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun x => ¬Q x))) :
    (1/(128*(A.d:ℝ)*K))*min
        (∑ v : Selected K Q,V A S C a z (realCorner v.val))
        (∑ v : Selected K (fun x => ¬Q x),V A S C a z (realCorner v.val)) ≤
      ∑ e : CutEdge K Q,min (V A S C a z (realCorner e.val.1))
        (V A S C a z (realCorner e.val.2.1)) := by
  obtain ⟨ht,ht1,hr,hsize⟩ := interpolation_bounds A.d K (dimension A) A.hd hK
    (ForestScaledPenalty.free_card_le A)
  have hh := GridBoundary.weighted_min_cut hPL Q (denseInterpolation A.d K) ht ht1 hr hsize
    (rho A S C a z) (fun v => V A S C a z (realCorner v))
    (fun v => DenseWeights.binWeight_pos _ _ _) (rho_continuous A S C a z).continuousOn
    (fun x _ => rho_positive A S C a z x)
    (fun x _ y _ t ht ht1 => rho_logConcave A S C a hC ha z x (Set.mem_univ _) y (Set.mem_univ _) t ht ht1)
    (fun v x hx => by
      have hclosed : ClosedBin (corner v) x := fun i => ⟨(hx i).1.le,(hx i).2.le⟩
      exact (bin_comparison A S C a hC ha haH z (realCorner v) x
        (fun i => by simpa only [abs_sub_comm] using closedBin_distances A v x hclosed i)).1)
    (fun e x hx => tube_comparison A S C a hC ha haH z e (denseInterpolation A.d K*K)
      (by positivity) (by linarith) x hx.1) hne hne'
  have hg := two_rpow_gain (denseInterpolation A.d K) ht.le
  have hm : 0 ≤ min (∑ v : Selected K Q,V A S C a z (realCorner v.val))
      (∑ v : Selected K (fun x => ¬Q x),V A S C a z (realCorner v.val)) := by
    apply le_min <;> exact Finset.sum_nonneg (fun _ _ => (DenseWeights.binWeight_pos _ _ _).le)
  have he : 1/(128*(A.d:ℝ)*K)=denseInterpolation A.d K/32 := by
    unfold denseInterpolation
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right (by linarith : denseInterpolation A.d K/32 ≤
    ((2:ℝ)^denseInterpolation A.d K-1)/16) hm).trans hh

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleChain
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bin chain for the computed-root forest penalty

All cut geometry is proved from the selected-root density. The only
conditional inputs are the same finite-box Prékopa–Leindler inequality
and finite reversible-chain Cheeger theorem used by the original chain.
-/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height proposal_bounds proposal_degree cutConstant)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracleChain_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    (oracleChain A R C a z hK).π v = gridWeight A R C a z v/
      ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w := rfl

private lemma corner_injective {q K : ℕ} :
    Function.Injective (corner (I := Fin q) (K := K)) := by
  intro a b h
  funext i
  exact Subtype.ext (congrFun h i)

/-- All geometric cut obligations are discharged for the literal forest
penalty. Only finite-box PL and finite-chain Cheeger remain conditional. -/
theorem oracleChain_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    ∀ f, (oracleChain A R C a z hK).variance f ≤
      (2/(cutConstant A K)^2)*(oracleChain A R C a z hK).energy f := by
  classical
  let : DecidableEq (Grid (I := Fin (dimension A)) K) := Classical.decEq _
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  let w := gridWeight A R C a z (K := K)
  have hw : ∀ v,0 < w v := fun _ => DenseWeights.binWeight_pos _ _ _
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hb := (proposal_bounds A.d A.hd).1
  have hk : 0 < cutConstant A K := by unfold cutConstant; positivity
  apply MetropolisChain.poincare_of_weighted_cut w hw Neighbor neighbor_symm
    (binProposal A.d) hb.le (2*dimension A) (fun v => by simpa using neighbor_degree v)
    ((proposal_degree A).trans (by norm_num)) hCheeger (cutConstant A K) hk
  intro S
  change cutConstant A K*min (∑ v ∈ S,w v) (∑ v ∈ Sᶜ,w v) ≤
    binProposal A.d*(∑ v ∈ S,∑ u ∈ Sᶜ,if Neighbor v u then min (w v) (w u) else 0)
  have hS : 0 ≤ ∑ v ∈ S,w v := Finset.sum_nonneg (fun _ _ => (hw _).le)
  have hSc : 0 ≤ ∑ v ∈ Sᶜ,w v := Finset.sum_nonneg (fun _ _ => (hw _).le)
  by_cases hs : S.Nonempty
  · by_cases hsc : Sᶜ.Nonempty
    · let Q : (Fin (dimension A) → ℤ) → Prop := fun x => ∃ v ∈ S,corner v=x
      have hQ (v : Grid (I := Fin (dimension A)) K) : Q (corner v) ↔ v∈S := by
        constructor
        · rintro ⟨u,hu,he⟩
          exact corner_injective he ▸ hu
        · intro hv
          exact ⟨v,hv,rfl⟩
      have hne : Nonempty (Selected K Q) := by
        obtain ⟨v,hv⟩ := hs
        exact ⟨⟨v,(hQ v).mpr hv⟩⟩
      have hne' : Nonempty (Selected K (fun x => ¬Q x)) := by
        obtain ⟨v,hv⟩ := hsc
        exact ⟨⟨v,fun h => (Finset.mem_compl.mp hv) ((hQ v).mp h)⟩⟩
      have hcut := weighted_min_cut A R C a hC ha haH z K hK hPL Q hne hne'
      change (1/(128*(A.d:ℝ)*K))*
        min (∑ v : Selected K Q,w v.val) (∑ v : Selected K (fun x => ¬Q x),w v.val) ≤
          ∑ e : CutEdge K Q,min (w e.val.1) (w e.val.2.1) at hcut
      have hsum : (∑ v : Selected K Q,w v.val)=∑ v∈S,w v := by
        rw [selected_sum_eq_filter Q w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ]
      have hsum' : (∑ v : Selected K (fun x => ¬Q x),w v.val)=∑ v∈Sᶜ,w v := by
        rw [selected_sum_eq_filter (fun x => ¬Q x) w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ,Finset.mem_compl]
      rw [hsum,hsum'] at hcut
      have hflow := cut_faces_le_neighbor_flow Q w (fun v => (hw v).le)
      have hflow' : (∑ e : CutEdge K Q,min (w e.val.1) (w e.val.2.1)) ≤
          ∑ v∈S,∑ u∈Sᶜ,if Neighbor v u then min (w v) (w u) else 0 := by
        convert hflow using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr ?_ ?_
        · ext v
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ]
        · intro v _
          apply Finset.sum_congr ?_ (fun _ _ => rfl)
          ext u
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ,Finset.mem_compl]
      calc
        _ = binProposal A.d*((1/(128*(A.d:ℝ)*K))*min (∑ v∈S,w v) (∑ v∈Sᶜ,w v)) := by
          unfold cutConstant
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcut.trans hflow') hb.le
    · have he : Sᶜ=∅ := Finset.not_nonempty_iff_eq_empty.mp hsc
      rw [he]
      simp only [Finset.sum_empty,min_eq_right hS,mul_zero,Finset.sum_const_zero]
      exact le_rfl
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [he] at hSc ⊢
    simp only [Finset.sum_empty,min_eq_left hSc,mul_zero]
    exact le_rfl

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleMixing
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit point and total-variation mixing for the selected-root grid -/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height binWidth height_positive oracle_grid_card
  mixingConstant mixingConstant_ge_one cutConstant cutConstant_lower oracleTime oracle_time_error)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma gridWeight_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (_haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    (2:ℝ)^(-a) ≤ gridWeight A R C a z v ∧ gridWeight A R C a z v ≤ 1 := by
  have hD := D_bounds A R C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hC
  have he0 : 0 ≤ a/height A C*D A R C z (realCorner v) :=
    mul_nonneg (div_nonneg ha hH.le) hD.1
  have he1 : a/height A C*D A R C z (realCorner v) ≤ a := by
    calc
      _ ≤ a/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg ha hH.le)
      _ = a := div_mul_cancel₀ a hH.ne'
  have hf0 : (0:ℤ) ≤ ⌊a/height A C*D A R C z (realCorner v)⌋ :=
    Int.floor_nonneg.mpr he0
  have hf1 := (Int.floor_le (a/height A C*D A R C z (realCorner v))).trans he1
  unfold gridWeight V DenseWeights.binWeight
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · calc
      _ ≤ (2:ℝ)^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast neg_nonpos.mpr hf0)
      _ = 1 := Real.rpow_zero _

lemma oracleChain_pi_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    (2:ℝ)^(-a)/(K:ℝ)^dimension A ≤ (oracleChain A R C a z hK).π v := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) := ⟨v⟩
  have hsumpos : 0 < ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w :=
    Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hsum : (∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w) ≤
      (K:ℝ)^dimension A := by
    calc
      _ ≤ ∑ _w : Grid (I := Fin (dimension A)) K,(1:ℝ) :=
        Finset.sum_le_sum (fun w _ => (gridWeight_bounds A R C a hC ha haH z hz hKB w).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
          oracle_grid_card,Nat.cast_pow]
  rw [oracleChain_pi]
  exact div_le_div₀ (DenseWeights.binWeight_pos _ _ _).le
    (gridWeight_bounds A R C a hC ha haH z hz hKB v).1 hsumpos hsum

theorem oracleChain_polynomial_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    ∀ f,(oracleChain A R C a z hK).variance f ≤
      mixingConstant A K*(oracleChain A R C a z hK).energy f := by
  intro f
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hk : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlo := cutConstant_lower A hK
  have hb : 2/(cutConstant A K)^2 ≤ mixingConstant A K := by
    calc
      _ ≤ 2/(1/(10000*(A.d:ℝ)^2*K))^2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hlo 2
      _ = _ := by unfold mixingConstant; field_simp [hd.ne',hk.ne']
  exact (oracleChain_poincare A R C a hC ha haH z hK hPL hCheeger f).trans
    (mul_le_mul_of_nonneg_right hb (FiniteChain.energy_nonneg _ f))

/-- Pointwise relative mixing for the implemented dyadic-proposal
Metropolis chain; this also bounds total variation. -/
theorem oracleChain_point_mixing (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (n : ℕ) (v w : Grid (I := Fin (dimension A)) K) :
    |(oracleChain A R C a z hK).iterate n ((oracleChain A R C a z hK).pointDensity w) v-1| ≤
      Real.exp (-(n:ℝ)/mixingConstant A K)/((2:ℝ)^(-a)/(K:ℝ)^dimension A) := by
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  apply FiniteChain.point_mixing_exp
  · exact mixingConstant_ge_one A hK
  · positivity
  · exact oracleChain_pi_lower A R C a hC ha haH z hz hK hKB
  · exact oracleChain_polynomial_poincare A R C a hC ha haH z hK hPL hCheeger

/-- The actual dyadic Metropolis chain attains the per-draw error used
in the evaluator's union bound at the explicit finite source schedule. -/
theorem oracleChain_scheduled_point_mixing (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a theta : ℝ)
    (hC : 0 < C) (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v w : Grid (I := Fin (dimension A)) K) :
    |(oracleChain A R C a z hK).iterate (oracleTime A C K Q theta)
      ((oracleChain A R C a z hK).pointDensity w) v-1| ≤ theta/(8*Q) :=
  (oracleChain_point_mixing A R C a hC ha haH z hz hK hKB hPL hCheeger _ v w).trans
    (oracle_time_error A C a theta ha haH htheta K Q hK hQ)

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational grid transitions for the selected-root evaluator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open CompanionOracleDensity (dimension height binWidth height_positive oracleProposalRat oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem gridExponent_upper (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    gridExponent A R C a z v ≤ a := by
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hD := D_bounds A R C hCR z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hCR
  have hbound : (a:ℝ)/height A C*D A R C z (realCorner v) ≤ a := by
    calc
      _ ≤ (a:ℝ)/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg (Nat.cast_nonneg _) hH.le)
      _ = _ := div_mul_cancel₀ _ hH.ne'
  have he := gridExponent_eq_floor A R C a z v
  have hh := (Int.floor_le ((a:ℝ)/height A C*D A R C z (realCorner v))).trans hbound
  rw [←he] at hh
  exact_mod_cast hh

theorem oracleWalkLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (n : ℕ) (v w : Grid (I := Fin (dimension A)) K) :
    ((oracleWalkLaw A R C a z hK v n).mass w:ℝ)=
      ((oracleChain A R C a z hK).kernel.power n).P v w := by
  induction n generalizing w with
  | zero =>
    simp only [oracleWalkLaw,walkLaw,pointLaw,FiniteKernel.power,FiniteKernel.identity]
    by_cases hvw : v=w
    · subst w; simp
    · simp [hvw,Ne.symm hvw]
  | succ n ih =>
    change ((∑ b,(oracleWalkLaw A R C a z hK v n).mass b*oracleTransition A R C a z b w:ℚ):ℝ)=_
    simp only [Rat.cast_sum,Rat.cast_mul,ih,oracleTransition_cast A R C a z hK,
      FiniteKernel.power,FiniteKernel.comp,FiniteChain.kernel]

theorem oracleStationaryLaw_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    ((oracleStationaryLaw A R C a z hK).mass v:ℝ)=(oracleChain A R C a z hK).π v := by
  change ((rationalGridWeight A R C a z v/
    ∑ w : Grid (I := Fin (dimension A)) K,rationalGridWeight A R C a z w:ℚ):ℝ)=_
  simp only [Rat.cast_div,Rat.cast_sum,rationalGridWeight_cast]
  rfl

/-- The rational finite-walk law inherits the proved source schedule.
No exact real-valued primitive is used to define its transitions. -/
theorem oracleWalkLaw_variation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : (a:ℝ) ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (oracleWalkLaw A R C a z hK v (oracleTime A C K Q theta))
      (oracleStationaryLaw A R C a z hK):ℝ) ≤ theta/(8*Q) := by
  let P := oracleChain A R C a z hK
  let n := oracleTime A C K Q theta
  let delta : ℝ := theta/(8*Q)
  have hpoint (w : Grid (I := Fin (dimension A)) K) :
      |(P.kernel.power n).P v w-P.π w| ≤ P.π w*delta := by
    have hm := oracleChain_scheduled_point_mixing A R C a theta
      (by exact_mod_cast hC) (Nat.cast_nonneg _) haH htheta z hz K Q hK hQ hKB hPL hCheeger v w
    change |P.iterate n (P.pointDensity w) v-1| ≤ delta at hm
    rw [←P.kernel_power_density] at hm
    calc
      _ = P.π w*|(P.kernel.power n).P v w/P.π w-1| := by
        calc
          _ = |P.π w*((P.kernel.power n).P v w/P.π w-1)| := by
            congr 1
            field_simp [(P.positive w).ne']
          _ = _ := by rw [abs_mul,abs_of_pos (P.positive w)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (P.positive w).le
  have hsum := Finset.sum_le_sum (fun w (_ : w∈Finset.univ) => hpoint w)
  rw [←Finset.sum_mul,P.normalized,one_mul] at hsum
  unfold variation
  simp only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat,
    oracleWalkLaw_cast,oracleStationaryLaw_cast]
  change (∑ w,|(P.kernel.power n).P v w-P.π w|)/2 ≤ delta
  have hd : 0 ≤ delta := by dsimp only [delta]; positivity
  linarith

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFiniteStep
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed Boolean words realize the selected-root grid chain -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (dimension binWidth rationalHeight rationalHeight_cast oracleStepBits oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_acceptance_finite_coin (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v w : Grid (I := Fin (dimension A)) K) :
    ((Finset.univ.filter (acceptDyadic
      (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))).card:ℝ)/
        (2:ℝ)^rationalHeight A C=
      min 1 (gridWeight A R C a z w/gridWeight A R C a z v) := by
  rw [acceptDyadic_probability]
  · rw [gridWeight_eq_dyadic,gridWeight_eq_dyadic,dyadic_ratio_min]
  · exact (Nat.sub_le _ _).trans ((gridExponent_upper A R C a hC z hz hKB w).trans haH)

/-- Every valid direction has one code; unused directions, boundary
proposals and failed dyadic tests stay at the starting vertex. -/
theorem finiteOracleStepLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    finiteOracleStepLaw A R C a z v=oracleTransitionLaw A R C a z hK v := by
  apply RationalLaw.eq_of_off_diagonal _ _ v
  intro w hwv
  apply Rat.cast_injective (α := ℝ)
  change ((finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v)
      (rationalHeight A C))).mass w:ℝ)=(oracleTransition A R C a z v w:ℝ)
  rw [finiteAcceptLaw_off_diagonal v w _ _ hwv.symm,
    axisCodeStep_count (dense_proposal_code_bound A.d (dimension A) (ForestScaledPenalty.free_card_le A))]
  simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  push_cast
  rw [Finset.filter_congr_decidable (Finset.univ : Finset (Fin (2^rationalHeight A C)))
    (acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))
    (fun bits => Classical.propDecidable _)]
  rw [oracle_acceptance_finite_coin A R C a hC haH z hz hKB v w]
  unfold oracleTransition
  rw [ite_eq_right hwv.symm,add_zero,oracleMove_cast]
  unfold MetropolisChain.move binProposal
  by_cases hvw : Neighbor v w <;> simp [hvw]

lemma oracleBitStepLaw_eq_finite (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    oracleBitStepLaw A R C a z v=finiteOracleStepLaw A R C a z v := by
  let E := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)
  let f := finiteAcceptStep v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))
  have hf : oracleBitStep A R C a z v=fun bits => f (E bits) := by
    funext bits
    dsimp [oracleBitStep,f,E,finiteAcceptStep]
    simp only [acceptDyadic]
    cases axisCodeStep v ((pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)) bits).1 with
    | none => rfl
    | some w => dsimp only; split_ifs <;> rfl
  unfold oracleBitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8*A.d)+rationalHeight A C) → Bool))
    (fun bits => f (E bits))=_
  rw [←map_equiv E,uniform_equiv,←uniform_product]
  rfl

theorem oracleBitStepLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    oracleBitStepLaw A R C a z v=oracleTransitionLaw A R C a z hK v := by
  rw [oracleBitStepLaw_eq_finite]
  exact finiteOracleStepLaw_eq A R C a hC haH z hz hK hKB v

/-- A fixed rectangular Boolean array realizes the complete independent
finite walk whose mixing estimate was proved for the real chain. -/
theorem oracleBitWalkLaw_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    oracleBitWalkLaw A R C a z v n=oracleWalkLaw A R C a z hK v n := by
  unfold oracleBitWalkLaw oracleWalkLaw
  rw [wordWalkLaw_eq]
  have he : (fun w : Grid (I := Fin (dimension A)) K =>
      mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (oracleBitStep A R C a z w))=
      oracleTransitionLaw A R C a z hK := by
    funext w
    exact oracleBitStepLaw_eq A R C a hC haH z hz hK hKB w
  rw [he]

theorem oracleBitWalkLaw_variation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (oracleBitWalkLaw A R C a z v (oracleTime A C K Q theta))
      (oracleStationaryLaw A R C a z hK):ℝ) ≤ theta/(8*Q) := by
  rw [oracleBitWalkLaw_eq A R C a hC haH z hz hK hKB]
  apply oracleWalkLaw_variation A R C a theta hC _ htheta z hz K Q hK hQ hKB hPL hCheeger v
  rw [←rationalHeight_cast]
  exact_mod_cast haH

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual fixed-word corrected draws for the selected-root count -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Both errors are accounted for once: mixing of the actual bin walk,
then bounded quotient sampling inside its selected bin. -/
theorem sampledIntegerLaw_variation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    (variation (sampledIntegerLaw A R C a z K hK hW v (oracleTime A C K Q theta) h)
      (stationaryIntegerLaw A R C a z K hK hW):ℝ) ≤
      theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)) := by
  have hb := variation_bind_uniform (oracleBitWalkLaw A R C a z v (oracleTime A C K Q theta))
    (oracleStationaryLaw A R C a z hK) (fun w => approximateBinLaw A K (by omega) hW w h)
    (exactBinLaw A K (by omega) hW) ((A.d:ℚ)/(2:ℚ)^(4*(h+A.d)))
    (fun w => approximateBinLaw_variation A K (by omega) hW w h)
  have hbR := (Rat.cast_le (K := ℝ)).mpr hb
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] at hbR
  exact hbR.trans (add_le_add
    (oracleBitWalkLaw_variation A R C a theta hC haH htheta z hz K Q hK hQ hKB hPL hCheeger v) le_rfl)


lemma flatOracleWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool)) (flatOracleWalk A R C a z v n)=
      oracleBitWalkLaw A R C a z v n := by
  unfold flatOracleWalk
  rw [←map_equiv (oracleWalkWordEquiv n (oracleStepBits A C)),uniform_equiv]
  rfl

/-- One fixed Boolean word drives the bin walk and then the integer draw.
The bin-dependent interval length never changes the reserved word length. -/
theorem oracleIntegerDraw_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) :
    mapLaw (uniformLaw (α := Fin (oracleIntegerBits A C n h) → Bool))
      (oracleIntegerDraw A R C a z K hK hW v n h)=sampledIntegerLaw A R C a z K hK hW v n h := by
  unfold oracleIntegerDraw oracleIntegerBits
  dsimp only
  rw [←map_equiv (splitWordEquiv (n*oracleStepBits A C) (binWordBits A h))
    (uniformLaw (α := Fin (n*oracleStepBits A C+binWordBits A h) → Bool))
    (fun draws => flatBinDraw A K (by omega) hW (flatOracleWalk A R C a z v n draws.1) h draws.2),
    uniform_equiv,←uniform_product]
  rw [mapLaw_product_finish
    (uniformLaw (α := Fin (n*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (binWordBits A h) → Bool))
    (flatOracleWalk A R C a z v n) (fun w bits => flatBinDraw A K (by omega) hW w h bits),
    flatOracleWalk_law]
  unfold sampledIntegerLaw
  congr 1
  funext w
  exact flatBinDraw_law A K (by omega) hW w h

end
end ContingencyTables.RootedOracleDensity

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

lemma correction_eq_population_power (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) :
    correction A R C a z K hK f=(rationalPopulation A K hK f:ℝ)*
      (2:ℝ)^(correctionExponent A R C a z K hK f:ℝ) := by
  have hV : gridWeight A R C a z (integerBin A K hK f)=
      (2:ℝ)^(-(gridExponent A R C a z (integerBin A K hK f):ℝ)) := by
    unfold gridWeight V DenseWeights.binWeight
    rw [←gridExponent_eq_floor]
    simp only [Int.cast_natCast]
  have hr : rho A R C a z (integerPoint A C f)/gridWeight A R C a z (integerBin A K hK f)=
      (2:ℝ)^(correctionExponent A R C a z K hK f:ℝ) := by
    rw [hV,correctionExponent_cast]
    unfold rho DenseWeights.density
    rw [←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  unfold correction
  rw [mul_div_assoc,hr]
  congr 1
  simp only [rationalPopulation,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast]

/-- A deterministic pointwise relative-error guarantee for the actual
rational correction returned on every integer assignment. -/
theorem computedCorrection_error (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hB : (K:ℝ)=binWidth A C)
    (sigma : ℚ) (hsigma : 0 < sigma) (f : FreeIndex A.small A.T A.b) :
    |(computedCorrection A R C a z K hK sigma f:ℝ)-correction A R C a z K hK f| ≤
      (sigma:ℝ)*correction A R C a z K hK f := by
  have hb := correctionExponent_bounds A R C a hC haH z K hK hB f
  have he := PowerOfTwoApproximation.approximate_error _ sigma hb.1 hb.2 hsigma
  have hp : (0:ℝ) ≤ rationalPopulation A K hK f := by
    exact_mod_cast (rationalPopulation_positive A K hK f).le
  rw [correction_eq_population_power]
  simp only [computedCorrection,Rat.cast_mul]
  rw [←mul_sub,abs_mul,abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left he hp).trans_eq (by ring)

/-- Positivity and a uniform range hold on all executions, independently
of the statistical event used by the estimator. -/
theorem computedCorrection_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (f : FreeIndex A.small A.T A.b) :
    (1/16:ℝ) ≤ computedCorrection A R C a z K hK sigma f ∧
      (computedCorrection A R C a z K hK sigma f:ℝ) ≤ 8 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  have hb := correction_bounds A R C a (by exact_mod_cast hC) (Nat.cast_nonneg _) haHR z K hK hW hB f
  have he := computedCorrection_error A R C a hC haH z K hK hB sigma hsigma f
  have hsR : (sigma:ℝ) ≤ 1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hsigmaHalf
  have hprod : (sigma:ℝ)*correction A R C a z K hK f ≤ (1/2)*correction A R C a z K hK f :=
    mul_le_mul_of_nonneg_right hsR (by linarith [hb.1])
  rcases abs_le.mp he with ⟨hl,hu⟩
  constructor <;> nlinarith

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence for the actual rational correction samples -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma correctionMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) :
    1/8 ≤ correctionMean A R C a z K hK hW ∧ correctionMean A R C a z K hK hW ≤ 4 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  exact expectation_bounds _ _ _ _ (correction_bounds A R C a (by exact_mod_cast hC)
    (Nat.cast_nonneg _) haHR z K (by omega) hW hB)

lemma correctionSample_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (sigma : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) :
    uniformAverage (fun bits => (correctionSample A R C a z K hK hW sigma v n h bits:ℝ))=
      expectation (sampledIntegerLaw A R C a z K hK hW v n h)
        (fun f => (computedCorrection A R C a z K (by omega) sigma f:ℝ)) := by
  unfold correctionSample
  rw [word_expectation (oracleIntegerDraw A R C a z K hK hW v n h)
    (fun f => (computedCorrection A R C a z K (by omega) sigma f:ℝ)),oracleIntegerDraw_law]

/-- Both finite sampling error and deterministic rational power error
are bounded relative to the literal correction mean. -/
theorem correctionSample_mean_bias (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    |uniformAverage (fun bits =>
      (correctionSample A R C a z K hK hW sigma v (oracleTime A C K Q theta) h bits:ℝ))-
        correctionMean A R C a z K hK hW| ≤
      16*(theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)))+
        (sigma:ℝ)*correctionMean A R C a z K hK hW := by
  let g := fun f => (computedCorrection A R C a z K (by omega) sigma f:ℝ)
  let p := sampledIntegerLaw A R C a z K hK hW v (oracleTime A C K Q theta) h
  let q := stationaryIntegerLaw A R C a z K hK hW
  have hsample : |expectation p g-expectation q g| ≤
      16*(theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d))) := by
    have he := expectation_difference p q g 8 (fun f => by
      have hh := computedCorrection_bounds A R C a hC haH z K (by omega) hW hB sigma hsigma hsigmaHalf f
      rw [abs_of_nonneg (by dsimp only [g]; linarith [hh.1])]
      exact hh.2)
    have hv := sampledIntegerLaw_variation A R C a theta hC haH htheta z hz K Q h hK hQ hW
      hB.le hPL hCheeger v
    exact he.trans (by nlinarith)
  have hround : |expectation q g-correctionMean A R C a z K hK hW| ≤
      (sigma:ℝ)*correctionMean A R C a z K hK hW :=
    expectation_relative_error q (correction A R C a z K (by omega)) g sigma
      (computedCorrection_error A R C a hC haH z K (by omega) hB sigma hsigma)
  rw [correctionSample_mean]
  calc
    _ ≤ |expectation p g-expectation q g|+|expectation q g-correctionMean A R C a z K hK hW| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (expectation p g-expectation q g) (expectation q g-correctionMean A R C a z K hK hW)
    _ ≤ _ := add_le_add hsample hround

/-- Independent finite words give confidence for the computed correction;
the displayed arithmetic tolerances are discharged by the outer schedule. -/
theorem correctionSamples_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta delta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta) (hdelta : 0 < delta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h N : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W) (hN : 0 < N)
    (hB : (K:ℝ)=binWidth A C) (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (hsigmaDelta : (sigma:ℝ) ≤ delta/4)
    (hnoise : theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)) ≤ delta/1024)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin N → (Fin (oracleIntegerBits A C (oracleTime A C K Q theta) h) → Bool) =>
      if delta*correctionMean A R C a z K hK hW <
        |sampleAverage (fun bits =>
          (correctionSample A R C a z K hK hW sigma v (oracleTime A C K Q theta) h bits:ℝ)) N draws-
            correctionMean A R C a z K hK hW| then (1:ℝ) else 0) ≤ 16384/(N*delta^2) := by
  let g := fun bits =>
    (correctionSample A R C a z K hK hW sigma v (oracleTime A C K Q theta) h bits:ℝ)
  have hg bits : 0 ≤ g bits ∧ g bits ≤ 8 := by
    have hh := computedCorrection_bounds A R C a hC haH z K (by omega) hW hB sigma hsigma hsigmaHalf
      (oracleIntegerDraw A R C a z K hK hW v (oracleTime A C K Q theta) h bits)
    exact ⟨by dsimp only [g,correctionSample]; linarith [hh.1],hh.2⟩
  have hb := correctionMean_bounds A R C a hC haH z K hK hW hB
  have hmu : 0 < correctionMean A R C a z K hK hW := by linarith [hb.1]
  have herr := correctionSample_mean_bias A R C a theta hC haH htheta z hz K Q h hK hQ hW hB sigma
    hsigma hsigmaHalf hPL hCheeger v
  have hround := mul_le_mul_of_nonneg_right hsigmaDelta hmu.le
  have hbias : |uniformAverage g-correctionMean A R C a z K hK hW| ≤
      delta*correctionMean A R C a z K hK hW/2 := by
    have hnoise' := mul_le_mul_of_nonneg_left hnoise (by norm_num : (0:ℝ) ≤ 16)
    have hlo := mul_le_mul_of_nonneg_left hb.1 hdelta.le
    dsimp only [g]
    nlinarith
  have hh := biased_target_failure g 8 _ delta hg hmu hdelta hbias N hN
  apply hh.trans
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs : (delta/8)^2 ≤ (delta*correctionMean A R C a z K hK hW)^2 := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg hdelta.le hmu.le)).mpr
    nlinarith [hb.1]
  calc
    4*8^2/((N:ℝ)*(delta*correctionMean A R C a z K hK hW)^2) ≤ 256/(N*(delta/8)^2) :=
      div_le_div₀ (by norm_num) (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hs hNR.le)
    _ = _ := by field_simp [hNR.ne',hdelta.ne']; ring

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma floor_step (x q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  omega

/-- The actual phase observable takes exactly the two source values,
since one annealing step changes its integer exponent by zero or one. -/
theorem ratioObservable_cases (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    ratioObservable A R C a z v=1 ∨ ratioObservable A R C a z v=1/2 := by
  have hD := D_bounds A R C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  let q := D A R C z (realCorner v)/height A C
  have hq0 : 0 ≤ q := div_nonneg hD.1 (height_positive A C hC).le
  have hq1 : q ≤ 1 := (div_le_one (height_positive A C hC)).mpr hD.2
  let x := (a:ℝ)/height A C*D A R C z (realCorner v)
  have he : ((a:ℝ)+1)/height A C*D A R C z (realCorner v)=x+q := by
    dsimp only [x,q]
    ring
  have hr : ratioObservable A R C a z v=(2:ℝ)^(-((⌊x+q⌋:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)) := by
    unfold ratioObservable gridWeight V DenseWeights.binWeight
    rw [he,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    change -((⌊x+q⌋:ℤ):ℝ)- -((⌊x⌋:ℤ):ℝ)=_
    ring
  rcases floor_step x q hq0 hq1 with hf|hf
  · left
    rw [hr,hf]
    simp
  · right
    rw [hr,hf]
    have hh : -(((⌊x⌋:ℤ)+1:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)=(-1:ℝ) := by
      push_cast
      ring
    rw [hh]
    norm_num

lemma rationalRatioObservable_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalRatioObservable A R C a z v:ℝ)=ratioObservable A R C a z v := by
  simp only [rationalRatioObservable,Rat.cast_div,rationalGridWeight_cast,Nat.cast_add,
    Nat.cast_one,ratioObservable]

lemma ratioObservable_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ ratioObservable A R C a z v ∧ ratioObservable A R C a z v ≤ 1 := by
  rcases ratioObservable_cases A R C hC a z hz hKB v with h|h <;> rw [h] <;> norm_num

lemma ratioMean_stationary (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) :
    expectation (oracleStationaryLaw A R C a z hK) (ratioObservable A R C a z)=ratioMean A R C a z K := by
  unfold expectation ratioMean
  apply Finset.sum_congr rfl
  intro v _
  rw [oracleStationaryLaw_cast,oracleChain_pi]
  rfl

lemma ratioMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C) :
    1/2 ≤ ratioMean A R C a z K ∧ ratioMean A R C a z K ≤ 1 := by
  rw [←ratioMean_stationary A R C a z hK]
  exact expectation_bounds _ _ _ _ (ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB)

lemma ratioSample_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) :
    (ratioSample A R C a z v n bits:ℝ)=
      ratioObservable A R C a z (wordWalk (oracleBitStep A R C a z) v n bits) :=
  rationalRatioObservable_cast A R C a z _

lemma ratioSample_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    uniformAverage (fun bits : RatioWords A C n => (ratioSample A R C a z v n bits:ℝ))=
      expectation (oracleBitWalkLaw A R C a z v n) (ratioObservable A R C a z) := by
  simp_rw [ratioSample_cast]
  exact word_expectation (wordWalk (oracleBitStep A R C a z) v n) _

/-- The actual finite walk has small expectation bias for the literal
ratio of consecutive normalizers. -/
theorem ratioSample_mean_bias (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    |uniformAverage (fun bits : RatioWords A C (oracleTime A C K Q theta) =>
      (ratioSample A R C a z v (oracleTime A C K Q theta) bits:ℝ))-ratioMean A R C a z K| ≤
      theta/(4*Q) := by
  rw [ratioSample_mean,←ratioMean_stationary A R C a z hK]
  have hb := expectation_difference
    (oracleBitWalkLaw A R C a z v (oracleTime A C K Q theta))
    (oracleStationaryLaw A R C a z hK) (ratioObservable A R C a z) 1 (fun w => by
      have hw := ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB w
      rw [abs_of_nonneg (by linarith : 0 ≤ ratioObservable A R C a z w)]
      exact hw.2)
  have hm := oracleBitWalkLaw_variation A R C a theta hC haH htheta z hz K Q hK hQ
    hKB hPL hCheeger v
  apply hb.trans
  calc
    _ ≤ 2*1*(theta/(8*Q)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by
      have hQR : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
      field_simp [hQR]
      ring

/-- Independent Boolean arrays give an explicit confidence bound around
its exact annealing ratio, including the finite-walk mean bias. -/
theorem ratioSamples_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q N : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hN : 0 < N)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin N → RatioWords A C (oracleTime A C K Q theta) =>
      if theta*ratioMean A R C a z K <
        |sampleAverage (fun bits => (ratioSample A R C a z v (oracleTime A C K Q theta) bits:ℝ))
          N draws-ratioMean A R C a z K| then (1:ℝ) else 0) ≤ 16/(N*theta^2) := by
  let g := fun bits : RatioWords A C (oracleTime A C K Q theta) =>
    (ratioSample A R C a z v (oracleTime A C K Q theta) bits:ℝ)
  have hg (bits : RatioWords A C (oracleTime A C K Q theta)) : 0 ≤ g bits ∧ g bits ≤ 1 := by
    dsimp only [g]
    rw [ratioSample_cast]
    have hh := ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB
      (wordWalk (oracleBitStep A R C a z) v (oracleTime A C K Q theta) bits)
    exact ⟨by linarith,hh.2⟩
  have hr := ratioMean_bounds A R C a hC z hz hK hKB
  have hQR : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hb : |uniformAverage g-ratioMean A R C a z K| ≤ theta*ratioMean A R C a z K/2 := by
    have hb := ratioSample_mean_bias A R C a theta hC haH htheta z hz K Q hK hQ hKB hPL hCheeger v
    have h1 : theta/(4*(Q:ℝ)) ≤ theta/4 := by
      apply div_le_div_of_nonneg_left htheta.le (by norm_num)
      nlinarith
    exact hb.trans (h1.trans (by nlinarith [hr.1]))
  have hh := biased_target_failure g 1 (ratioMean A R C a z K) theta hg
    (by linarith [hr.1]) htheta hb N hN
  apply hh.trans
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs : (theta/2)^2 ≤ (theta*ratioMean A R C a z K)^2 := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg htheta.le (by linarith [hr.1]))).mpr
    nlinarith [hr.1]
  calc
    4*1^2/((N:ℝ)*(theta*ratioMean A R C a z K)^2) ≤ 4/(N*(theta/2)^2) :=
      div_le_div₀ (by norm_num) (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hs hNR.le)
    _ = _ := by field_simp [hNR.ne',htheta.ne']; ring

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleSchedule
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The concrete correction schedule discharges both arithmetic error
allowances; only the named published PL/Cheeger inputs remain. -/
theorem scheduled_correction_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a j : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (delta failure : ℚ)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hfailure : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin (sampleCount j delta failure) →
        (Fin (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) → Bool) =>
      if (delta:ℝ)*correctionMean A R C a z K hK hW <
        |sampleAverage (fun bits =>
          (correctionSample A R C a z K hK hW (roundingTolerance delta) v
            (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) bits:ℝ))
          (sampleCount j delta failure) draws-correctionMean A R C a z K hK hW| then (1:ℝ) else 0) ≤
      (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hs : (0:ℚ) < roundingTolerance delta := by unfold roundingTolerance; positivity
  have hsHalf : roundingTolerance delta ≤ 1/2 := by unfold roundingTolerance; linarith
  have hsDelta : (roundingTolerance delta:ℝ) ≤ (delta:ℝ)/4 := by
    simp only [roundingTolerance,Rat.cast_div,Rat.cast_ofNat,le_refl]
  exact (correctionSamples_failure A R C a (correctionTheta delta) delta hC haH
    (by unfold correctionTheta; positivity) hd z hz K 1 (offsetAccuracy A delta)
    (sampleCount j delta failure) hK (by decide) hW (sampleCount_positive j delta failure hdelta hfailure)
    hB (roundingTolerance delta) hs hsHalf hsDelta (by simpa only [Nat.cast_one] using correction_noise_budget A delta hdelta)
    hPL hCheeger v).trans (sampleCount_budget j delta failure hdelta hfailure)


theorem scheduled_ratio_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a j : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (delta failure : ℚ)
    (hdelta : 0 < delta) (hfailure : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K : ℕ) (hK : 1 ≤ K) (hB : (K:ℝ)=binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin (sampleCount j delta failure) →
        RatioWords A C (oracleTime A C K 1 delta) =>
      if (delta:ℝ)*ratioMean A R C a z K <
        |sampleAverage (fun bits => (ratioSample A R C a z v (oracleTime A C K 1 delta) bits:ℝ))
          (sampleCount j delta failure) draws-ratioMean A R C a z K| then (1:ℝ) else 0) ≤
      (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hn := sampleCount_positive j delta failure hdelta hfailure
  have hh := ratioSamples_failure A R C a delta hC haH hd z hz K 1 (sampleCount j delta failure)
    hK (by decide) hn hB.le hPL hCheeger v
  apply hh.trans
  calc
    16/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) ≤
        16384/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ _ := sampleCount_budget j delta failure hdelta hfailure

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorConfidence
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma factor_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) (i : Option (Fin j)) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if badFactor A R C z K hK hW j delta failure v i draws then (1:ℝ) else 0) ≤
        (failure:ℝ)/(4*((j:ℝ)+1)) := by
  let : Nonempty (Fin j → RatioBlock A C K j delta failure) := ⟨fun _ _ _ _ => false⟩
  let : Nonempty (CorrectionBlock A C K j delta failure) := ⟨fun _ _ => false⟩
  cases i with
  | none =>
    simp only [badFactor,observedFactor,targetFactor,rationalAverage_cast]
    convert scheduled_correction_failure A R C j j hC hj delta failure hd0 hd1 hf z hz K hK hW hB hPL hCheeger v using 1
    all_goals try with_reducible_and_instances rfl
    rw [uniformAverage_prod]
    dsimp only
    convert uniformAverage_const (X := Fin j → RatioBlock A C K j delta failure)
      (uniformAverage (fun draws : CorrectionBlock A C K j delta failure =>
        if (delta:ℝ)*correctionMean A R C j z K hK hW <
          |sampleAverage (fun bits => (correctionSample A R C j z K hK hW (roundingTolerance delta) v
            (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) bits:ℝ))
            (sampleCount j delta failure) draws-correctionMean A R C j z K hK hW| then 1 else 0)) using 1
    all_goals try with_reducible_and_instances rfl
  | some a =>
    simp only [badFactor,observedFactor,targetFactor,rationalAverage_cast]
    convert scheduled_ratio_failure A R C a.val j hC (by omega) delta failure hd0 hf z hz K hK hB hPL hCheeger v using 1
    all_goals try with_reducible_and_instances rfl
    rw [uniformAverage_prod]
    dsimp only
    have hc (x : Fin j → RatioBlock A C K j delta failure) :=
      uniformAverage_const (X := CorrectionBlock A C K j delta failure)
        (if (delta:ℝ)*ratioMean A R C a.val z K <
          |sampleAverage (fun bits => (ratioSample A R C a.val z v (oracleTime A C K 1 delta) bits:ℝ))
            (sampleCount j delta failure) (x a)-ratioMean A R C a.val z K| then 1 else 0)
    simp_rw [hc]
    convert uniformAverage_coordinate (X := fun _ : Fin j => RatioBlock A C K j delta failure) a (fun draws : RatioBlock A C K j delta failure =>
      if (delta:ℝ)*ratioMean A R C a.val z K <
          |sampleAverage (fun bits => (ratioSample A R C a.val z v (oracleTime A C K 1 delta) bits:ℝ))
            (sampleCount j delta failure) draws-ratioMean A R C a.val z K| then 1 else 0) using 1
    all_goals try with_reducible_and_instances rfl
    exact average_fintype_irrel _ _ _

/-- All ratio and correction block failures share one explicit budget.
The statement concerns the actual bounded Boolean experiment. -/
theorem goodEstimate_failure_oai (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if ¬GoodEstimate A R C z K hK hW j delta failure v draws then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  have he (draws : EstimatorInput A C K j delta failure) :
      (¬GoodEstimate A R C z K hK hW j delta failure v draws) ↔
        ∃ i,badFactor A R C z K hK hW j delta failure v i draws := by
    simp only [GoodEstimate,badFactor,not_forall,not_le]
  simp_rw [he]
  calc
    _ ≤ ∑ i : Option (Fin j),uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
        if badFactor A R C z K hK hW j delta failure v i draws then (1:ℝ) else 0) :=
      uniform_union_bound _
    _ ≤ ∑ _i : Option (Fin j),(failure:ℝ)/(4*((j:ℝ)+1)) :=
      Finset.sum_le_sum (fun i _ => factor_failure A R C hC z hz K hK hW hB j hj delta failure
        hd0 hd1 hf hPL hCheeger v i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      field_simp

end

end ContingencyTables.RootedOracleDensity

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure_oai.{u_1, u_2} := @OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure_oai.{u_1, u_2}
