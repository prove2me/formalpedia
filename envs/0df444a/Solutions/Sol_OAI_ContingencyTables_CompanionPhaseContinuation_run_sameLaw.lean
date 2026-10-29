-- Prove2me | solution 1 for OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:17:09.718997+00:00
-- url     : https://prove2.me/submissions/a5ca7bc1-3abe-4fe6-b5a5-2abe018b2ddb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_RootedEstimatorWordProgram_output_scheduled

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

section MetropolisSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance110 : Fintype Γ] [sectionInstance111 : DecidableEq Γ]
omit sectionInstance110 in
lemma exchangedSet_adjacent [Fintype Γ] (S : Set Γ) (a : ExchangeChoice S) :
    ExchangeAdjacent S (exchangedSet S a) := by
  refine ⟨S\{a.1.val},a.1.val,a.2.val,?_,?_,?_,?_,rfl⟩
  · intro he
    exact a.2.property (he ▸ a.1.property)
  · simp
  · intro hx; exact a.2.property hx.1
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · intro hx; by_cases he : x=a.1.val
      · exact Or.inl he
      · exact Or.inr ⟨hx,he⟩
    · rintro (rfl|⟨hx,_⟩)
      · exact a.1.property
      · exact hx
omit sectionInstance110 in
lemma exchangedSet_left_difference [Fintype Γ] (S : Set Γ) (a : ExchangeChoice S) :
    S\exchangedSet S a={a.1.val} := by
  ext x
  simp only [exchangedSet,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or,not_and]
  constructor
  · rintro ⟨hx,_,ha⟩
    by_contra hh
    exact ha hx hh
  · intro he
    subst x
    refine ⟨a.1.property,?_,fun _ hn => hn rfl⟩
    intro he
    exact a.2.property (he ▸ a.1.property)
omit sectionInstance110 sectionInstance111 in
lemma exchangedSet_right_difference [Fintype Γ] [DecidableEq Γ] (S : Set Γ) (a : ExchangeChoice S) :
    exchangedSet S a\S={a.2.val} := by
  ext x
  simp only [exchangedSet,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hh,hn⟩
    exact hh.resolve_right (fun h => hn h.1)
  · intro he; subst x
    exact ⟨Or.inl rfl,a.2.property⟩
lemma exchangedSet_injective (S : Set Γ) : Function.Injective (exchangedSet S) := by
  intro a b he
  apply Prod.ext
  · apply Subtype.ext
    have h := congrArg (fun T => S\T) he
    rw [exchangedSet_left_difference,exchangedSet_left_difference] at h
    exact Set.singleton_injective h
  · apply Subtype.ext
    have h := congrArg (fun T => T\S) he
    rw [exchangedSet_right_difference,exchangedSet_right_difference] at h
    exact Set.singleton_injective h
end MetropolisSampling
open scoped BigOperators Classical

end

open scoped BigOperators Classical

section ActualSize
open scoped BigOperators Classical
lemma indicator_list_sum {X : Type*} (P : X → Prop) (l : List X) :
    (l.map (fun x => if P x then (1:ℚ) else 0)).sum=(l.countP (fun x => decide (P x)):ℚ) := by
  induction l with
  | nil => simp
  | cons x l ih => by_cases hx : P x <;> simp [hx,ih,add_comm]
end ActualSize

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section CanonicalFair
open scoped BigOperators Classical
lemma uniformAverage_independent_eq {X Y Z : Type*} [Fintype X] [Fintype Y]
    (f : X → Z) (g : Y → Z)
    (h : ∀ φ : Z → ℝ,uniformAverage (fun x => φ (f x))=uniformAverage (fun y => φ (g y)))
    (k : ℕ) (F : (Fin k → Z) → ℝ) :
    uniformAverage (fun xs : Fin k → X => F (fun i => f (xs i)))=
      uniformAverage (fun ys : Fin k → Y => F (fun i => g (ys i))) := by
  induction k with
  | zero =>
    have hf : ∀ xs : Fin 0 → X,(fun i => f (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro xs; funext i; exact Fin.elim0 i
    have hg : ∀ ys : Fin 0 → Y,(fun i => g (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      intro ys; funext i; exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ k ih =>
    have hf (x : X) (xs : Fin k → X) :
        (fun i : Fin (k+1) => f ((Fin.cons x xs : Fin (k+1) → X) i))=Fin.cons (f x) (fun i => f (xs i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin k → Y) :
        (fun i : Fin (k+1) => g ((Fin.cons y ys : Fin (k+1) → Y) i))=Fin.cons (g y) (fun i => g (ys i)) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have hi (x : X) := ih (fun zs => F (Fin.cons (f x) zs))
    simp_rw [hi]
    exact h (fun z => uniformAverage (fun ys : Fin k → Y => F (Fin.cons z (fun i => g (ys i)))))
end CanonicalFair

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures LabelledFactorial

variable {P C : Type*} [Fintype P] [Fintype C]

omit [Fintype P] in
lemma occupancy_single (S : Set (P × Bool)) (p : P) (h : PairSingle (pair p) S) :
    occupancy S p = 1 := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> simp [occupancy,pair] at ha hb ⊢ <;> simp [ha,hb]

omit [Fintype P] in
lemma occupancy_empty (S : Set (P × Bool)) (p : P) (h : PairEmpty (pair p) S) :
    occupancy S p = 0 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

omit [Fintype P] in
lemma occupancy_full (S : Set (P × Bool)) (p : P) (h : PairFull (pair p) S) :
    occupancy S p = 2 := by
  rcases h with ⟨ha,hb⟩
  simp [pair] at ha hb
  simp [occupancy,ha,hb]

lemma defect_occupancy (S : Set (P × Bool)) (p q : P)
    (hS : DefectState pairs (pair p) (pair q) S) (k : P) :
    occupancy S k + (if k=p then 1 else 0) = 1 + (if k=q then 1 else 0) := by
  have hpq : p ≠ q := fun h => hS.2.2.1 (congrArg pair h)
  by_cases hkp : k=p
  · subst k
    rw [occupancy_empty S p hS.2.2.2.1]
    simp [hpq]
  · by_cases hkq : k=q
    · subst k
      rw [occupancy_full S q hS.2.2.2.2.1]
      simp [hkp]
    · rw [occupancy_single S k (hS.2.2.2.2.2 _ (pair_mem k)
        (fun h => hkp (pair_injective h)) (fun h => hkq (pair_injective h)))]
      simp [hkp,hkq]

end ContingencyTables.TwoLiftStates

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

variable {I J : Type*} [Fintype I] [Fintype J]

lemma innerTolerance_pos (epsilon : ℚ) (j : ℕ) (he : 0 < epsilon) :
    0 < innerTolerance epsilon j := by unfold innerTolerance; positivity

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionWeightOracle
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.CompanionWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma profile_inBox (A : Instance I J) (S : Set (Labels A×Bool)) :
    BalancedBox.InBox (bounds A) (profile A S) := by
  rw [←label_capacity]
  exact SliceFactorial.groupCount_inBox _ _

end

end ContingencyTables.CompanionWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRationalUpdates
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational multiplier updates of the outer annealing run -/

namespace ContingencyTables.CompanionRationalUpdates

open CompanionFactorialApplication
open CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma plainCount_le (A : Instance I J) (l : List (Set (Labels A×Bool))) :
    plainCount A l ≤ l.length := List.countP_le_length

lemma rationalLearn_counts (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (l : List (Set (Labels A×Bool))) (hl : 0 < l.length) (p q : Pair A) :
    rationalLearn pairs w l p q=
      if p∈pairs ∧ q∈pairs ∧ p≠q then w p q*(plainCount A l:ℚ)/(defectCount A l p q:ℚ)
      else w p q := by
  have hN : (l.length:ℚ)≠0 := by exact_mod_cast hl.ne'
  unfold rationalLearn rationalEmpirical rationalPlain rationalDefect plainCount defectCount
  simp only [indicator_list_sum]
  split_ifs <;> simp only [div_div_div_cancel_right₀ hN,mul_div_assoc]

end

end ContingencyTables.CompanionRationalUpdates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBooleanPhase
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion phase walk driven by disjoint bounded Boolean words -/

namespace ContingencyTables.CompanionBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma proposal_mass (A : Instance I J) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact subsetBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (State A)))
    (fun T : State A => ExchangeAdjacent S.val T.val) (proposalBits A) (proposal_codes A S) T

end

end ContingencyTables.CompanionBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeBits
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData

lemma bits_length (A : List Bool) : (encode (bits A)).length≤4*A.length+1 := by
  induction A with
  | nil => simp [encode]
  | cons b A ih => cases b <;> simp only [bits_cons,encode,bit,Bool.false_eq_true,↓reduceIte,
      List.length_cons,List.length_append,List.length_nil] <;> omega
end MatchingFPRAS.TreeData

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

lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

lemma weight_bits (bs : List Bool) : weight bs≤4*bs.length+1 := TreeData.bits_length bs
lemma weight_nat (n : ℕ) : weight n=weight n.bits := rfl
lemma weight_nat_le (n : ℕ) : weight n≤4*n.size+1 := by
  rw [weight_nat,←Nat.size_eq_bits_len]; exact weight_bits _
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialLists
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
omit [Codec A] in
lemma weight_map_bound {f : A → B} {as : List A} {N : ℕ}
    (h : ∀ a∈as,weight (f a)≤N) : weight (as.map f)≤as.length*(N+1)+1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ht:=ih (fun b hb=>h b (by simp [hb]))
    have ha:=h a (by simp)
    simp only [List.map_cons,weight_cons,List.length_cons]
    nlinarith
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryExchangeProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial enumeration of exchanges of a binary profile

The program scans at most the square of the list length. It retains only
an absent receiving coordinate and a present donating coordinate, so every
retained natural-number update is again a binary profile.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

theorem mem_binaryExchangeIndices (xs : List ℕ) (i j : ℕ) :
    (i,j)∈binaryExchangeIndices xs ↔
      i<xs.length ∧ j<xs.length ∧ xs.getD i 0=0 ∧ xs.getD j 0=1 := by
  simp only [binaryExchangeIndices,List.mem_filter,mem_cellPairs,binaryExchangeTest,
    decide_eq_true_eq]
  tauto

theorem binaryExchangeIndices_nodup (xs : List ℕ) : (binaryExchangeIndices xs).Nodup :=
  (cellPairs_nodup xs xs).filter _

lemma setProfile_injective {n : ℕ} : Function.Injective (setProfile (n := n)) := by
  intro S T he
  ext i
  have hi := congrFun he i
  by_cases hs : i∈S <;> by_cases ht : i∈T <;> simp_all [setProfile]

/-- On an absent/present coordinate pair, the natural update is exactly
set removal followed by set insertion. -/
theorem exchange_setProfile {n : ℕ} (S : Set (Fin n)) (i j : Fin n)
    (hi : i∉S) (hj : j∈S) :
    IntegerWeightedTransport.exchangeTarget (setProfile S) i j=
      setProfile (insert i (S\{j})) := by
  have hij : i≠j := fun he => hi (he ▸ hj)
  funext a
  by_cases hai : a=i
  · subst a
    simp [IntegerWeightedTransport.exchangeTarget,setProfile,hi,hij]
  · by_cases haj : a=j
    · subst a
      simp [IntegerWeightedTransport.exchangeTarget,setProfile,hj,hai]
    · by_cases ha : a∈S <;>
        simp [IntegerWeightedTransport.exchangeTarget,setProfile,hai,haj,ha]

/-- Every program output is a genuine binary exchange, and all such
exchanges are listed. No enumeration of the set of states is involved. -/
theorem mem_binaryExchanges_setProfile {n : ℕ} (S : Set (Fin n)) (ys : List ℕ) :
    ys∈binaryExchanges (List.ofFn (setProfile S)) ↔
      ∃ i j : Fin n,i∉S ∧ j∈S ∧ ys=List.ofFn (setProfile (insert i (S\{j}))) := by
  simp only [binaryExchanges,List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩,hij,rfl⟩
    have h := (mem_binaryExchangeIndices _ i j).mp hij
    have hi : i<n := by simpa only [List.length_ofFn] using h.1
    have hj : j<n := by simpa only [List.length_ofFn] using h.2.1
    let a : Fin n := ⟨i,hi⟩
    let b : Fin n := ⟨j,hj⟩
    have hget (k : Fin n) : (List.ofFn (setProfile S)).getD k.val 0=setProfile S k := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
      simp only [Option.getD_some,List.getElem_ofFn]
    have ha : a∉S := by
      have hh := h.2.2.1
      rw [hget a] at hh
      intro ha
      simp [setProfile,ha] at hh
    have hb : b∈S := by
      have hh := h.2.2.2
      rw [hget b] at hh
      by_contra hn
      simp [setProfile,hn] at hh
    refine ⟨a,b,ha,hb,?_⟩
    exact (listExchange_ofFn (setProfile S) a b).trans
      (congrArg List.ofFn (exchange_setProfile S a b ha hb))
  · rintro ⟨i,j,hi,hj,rfl⟩
    refine ⟨(i.val,j.val),?_,?_⟩
    · apply (mem_binaryExchangeIndices _ _ _).mpr
      refine ⟨by simp,by simp,?_,?_⟩ <;>
        simp [List.getD_eq_getElem?_getD,setProfile,hi,hj]
    · exact ((listExchange_ofFn (setProfile S) i j).trans
        (congrArg List.ofFn (exchange_setProfile S i j hi hj)))

lemma getD_setProfile {n : ℕ} (S : Set (Fin n)) (i : Fin n) :
    (List.ofFn (setProfile S)).getD i.val 0=setProfile S i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,List.getElem_ofFn]

lemma binaryIndex_specs {n : ℕ} (S : Set (Fin n)) (ij : ℕ×ℕ)
    (h : ij∈binaryExchangeIndices (List.ofFn (setProfile S))) :
    ∃ i j : Fin n,ij=(i.val,j.val) ∧ i∉S ∧ j∈S := by
  have hh := (mem_binaryExchangeIndices _ ij.1 ij.2).mp h
  have hi : ij.1<n := by simpa only [List.length_ofFn] using hh.1
  have hj : ij.2<n := by simpa only [List.length_ofFn] using hh.2.1
  let i : Fin n := ⟨ij.1,hi⟩
  let j : Fin n := ⟨ij.2,hj⟩
  refine ⟨i,j,rfl,?_,?_⟩
  · intro hm
    have he := hh.2.2.1
    rw [getD_setProfile S i] at he
    simp [setProfile,hm] at he
  · by_contra hm
    have he := hh.2.2.2
    rw [getD_setProfile S j] at he
    simp [setProfile,hm] at he

/-- Distinct eligible coordinate pairs give distinct binary profiles. -/
theorem binaryExchanges_nodup {n : ℕ} (S : Set (Fin n)) :
    (binaryExchanges (List.ofFn (setProfile S))).Nodup := by
  apply (binaryExchangeIndices_nodup _).map_on
  intro a ha b hb he
  obtain ⟨i,j,rfl,hi,hj⟩ := binaryIndex_specs S a ha
  obtain ⟨u,v,rfl,hu,hv⟩ := binaryIndex_specs S b hb
  rw [listExchange_ofFn,listExchange_ofFn,exchange_setProfile S i j hi hj,
    exchange_setProfile S u v hu hv] at he
  have hs := setProfile_injective (List.ofFn_injective he)
  change CommonBasesFPRAS.exchangedSet S (⟨j,hj⟩,⟨i,hi⟩)=
    CommonBasesFPRAS.exchangedSet S (⟨v,hv⟩,⟨u,hu⟩) at hs
  have hp := CommonBasesFPRAS.exchangedSet_injective S hs
  have h1 : i=u := congrArg (fun a : CommonBasesFPRAS.ExchangeChoice S => a.2.val) hp
  have h2 : j=v := congrArg (fun a : CommonBasesFPRAS.ExchangeChoice S => a.1.val) hp
  subst u
  subst v
  rfl

end ContingencyTables.ProfilePrograms

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
lemma sum_val (xs : List Fraction) (hx : ∀ b∈xs,0<b.2) :
    val (sum xs)=(xs.map val).sum := by
  rw [sum,fold_val xs (0,1) (by decide) hx]
  simp [val]

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

omit [Codec A] [Inhabited A] in
/-- The literal binary program has the previously proved dyadic proposal
law, including all unused indices that return `none`. -/
theorem listWordChoice_mass [Fintype A] [DecidableEq A]
    (xs : List A) (hxs : xs.Nodup) (k : ℕ) (hk : xs.length≤2^k) (a : A) :
    (FirstSuccess.mapLaw
      (FirstSuccess.uniformLaw (α := Fin k → Bool))
      (fun bits => listWordChoice (xs,List.ofFn bits))).mass (some a)=
        if a∈xs then 1/(2:ℚ)^k else 0 := by
  simp_rw [listWordChoice_ofFn]
  exact FairBits.listBitDraw_mass xs hxs k hk a

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionArithmeticProposal
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit coordinate-list proposal for the companion chain

Only ordered coordinates are enumerated. The arithmetic binary-profile
program generates the possible exchanges, after which the actual chain
state predicate removes disallowed states. A dyadic list index has exactly
the same proposal law as the abstract injection.
-/

namespace ContingencyTables.CompanionArithmeticProposal
open CommonBasesFPRAS ProfilePrograms FirstSuccess ResidualMixture FairBits
open CompanionFactorialApplication CompanionBooleanPhase TwoLiftStates
open scoped BigOperators Classical

noncomputable section

section Coordinates
variable {Γ : Type*} [Fintype Γ] {n : ℕ} (e : Γ ≃ Fin n)

omit [Fintype Γ] in
lemma adjacent_preimage {Δ : Type*} [Fintype Δ] (f : Γ ≃ Δ) (S T : Set Δ)
    (h : ExchangeAdjacent S T) : ExchangeAdjacent (f ⁻¹' S) (f ⁻¹' T) := by
  obtain ⟨B,a,b,hab,ha,hb,rfl,rfl⟩ := h
  refine ⟨f ⁻¹' B,f.symm a,f.symm b,fun he => hab (f.symm.injective he),?_,?_,?_,?_⟩
  · simpa using ha
  · simpa using hb
  · ext x
    simp only [Set.mem_preimage,Set.mem_insert_iff]
    rw [←f.eq_symm_apply]
  · ext x
    simp only [Set.mem_preimage,Set.mem_insert_iff]
    rw [←f.eq_symm_apply]

lemma adjacent_coordinate_iff (S T : Set Γ) :
    ExchangeAdjacent (coordinateSet e S) (coordinateSet e T) ↔ ExchangeAdjacent S T := by
  constructor
  · intro h
    have hh : ExchangeAdjacent (physicalSet e (coordinateSet e S))
        (physicalSet e (coordinateSet e T)) := adjacent_preimage e _ _ h
    simpa only [physical_coordinate] using hh
  · exact adjacent_preimage e.symm S T

omit [Fintype Γ] in
@[simp] lemma decode_encode (S : Set Γ) : decodeSet e (encodeSet e S)=S := by
  ext a
  simp only [decodeSet,Set.mem_ofPred_eq,encodeSet,getD_setProfile,setProfile,
    coordinateSet,Set.mem_preimage,Equiv.symm_apply_apply]
  by_cases ha : a∈S <;> simp [ha]

omit [Fintype Γ] in
lemma encode_physical (U : Set (Fin n)) :
    encodeSet e (physicalSet e U)=List.ofFn (setProfile U) := by
  simp only [encodeSet,coordinate_physical]

/-- The executable integer update enumerates exactly the set exchanges. -/
theorem mem_raw_codes (S : Set Γ) (xs : List ℕ) :
    xs∈binaryExchanges (encodeSet e S) ↔
      ∃ T : Set Γ,ExchangeAdjacent S T ∧ xs=encodeSet e T := by
  rw [encodeSet,mem_binaryExchanges_setProfile]
  constructor
  · rintro ⟨i,j,hi,hj,rfl⟩
    let U := insert i (coordinateSet e S\{j})
    have hU : ExchangeAdjacent (coordinateSet e S) U :=
      exchangedSet_adjacent _ (⟨j,hj⟩,⟨i,hi⟩)
    refine ⟨physicalSet e U,?_,(encode_physical e U).symm⟩
    apply (adjacent_coordinate_iff e S _).mp
    simpa only [coordinate_physical] using hU
  · rintro ⟨T,hST,rfl⟩
    obtain ⟨j,hj,i,hi,he⟩ := ((adjacent_coordinate_iff e S T).mpr hST).move
    exact ⟨i,j,hi,hj,by rw [encodeSet,he]⟩

lemma mem_neighborSets (S T : Set Γ) : T∈neighborSets e S ↔ ExchangeAdjacent S T := by
  simp only [neighborSets,List.mem_map,mem_raw_codes]
  constructor
  · rintro ⟨xs,⟨U,hU,rfl⟩,he⟩
    have he' : U=T := by simpa only [decode_encode] using he
    exact he' ▸ hU
  · intro h
    exact ⟨encodeSet e T,⟨T,h,rfl⟩,decode_encode e T⟩

lemma neighborSets_nodup (S : Set Γ) : (neighborSets e S).Nodup := by
  apply (binaryExchanges_nodup (coordinateSet e S)).map_on
  intro xs hxs ys hys he
  obtain ⟨T,hT,rfl⟩ := (mem_raw_codes e S xs).mp hxs
  obtain ⟨U,hU,rfl⟩ := (mem_raw_codes e S ys).mp hys
  simpa only [decode_encode] using congrArg (encodeSet e) he

omit [Fintype Γ] in
lemma stateFilter_eq_some (gs : List (Γ×Γ)) (T : Set Γ) (U : ChainIndex gs) :
    (if h : ChainState gs T then some (⟨T,h⟩ : ChainIndex gs) else none)=some U ↔ T=U.val := by
  by_cases h : ChainState gs T
  · simp only [dite_eq_left h,Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [dite_eq_right h,reduceCtorEq,false_iff]
    intro he
    exact h (he.symm ▸ U.property)

lemma mem_neighborStates (gs : List (Γ×Γ)) (S T : ChainIndex gs) :
    T∈neighborStates e gs S ↔ ExchangeAdjacent S.val T.val := by
  simp only [neighborStates,List.mem_filterMap,stateFilter_eq_some]
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (mem_neighborSets e S.val T.val).mp hU
  · intro h
    exact ⟨T.val,(mem_neighborSets e S.val T.val).mpr h,rfl⟩

lemma neighborStates_nodup (gs : List (Γ×Γ)) (S : ChainIndex gs) :
    (neighborStates e gs S).Nodup := by
  apply List.Nodup.filterMap _ (neighborSets_nodup e S.val)
  intro T U V hT hU
  have hTV := (stateFilter_eq_some gs T V).mp (Option.mem_def.mp hT)
  have hUV := (stateFilter_eq_some gs U V).mp (Option.mem_def.mp hU)
  exact hTV.trans hUV.symm

end Coordinates

variable {I J : Type} [Fintype I] [Fintype J]

@[simp] theorem mem_neighbors (A : Instance I J) (S T : State A) :
    T∈neighbors A S ↔ ExchangeAdjacent S.val T.val :=
  mem_neighborStates _ _ _ _

theorem neighbors_nodup (A : Instance I J) (S : State A) : (neighbors A S).Nodup :=
  neighborStates_nodup _ _ _

theorem neighbors_length (A : Instance I J) (S : State A) :
    (neighbors A S).length≤2^proposalBits A := by
  have he : (neighbors A S).toFinset=Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val) := by
    ext T
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,mem_neighbors]
  rw [←List.toFinset_card_of_nodup (neighbors_nodup A S),he]
  simpa only [Fintype.card_subtype] using proposal_codes A S

theorem proposal_mass (A : Instance I J) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact (listWordChoice_mass (neighbors A S) (neighbors_nodup A S)
    (proposalBits A) (neighbors_length A S) T).trans (by simp only [mem_neighbors])

/-- The explicit arithmetic enumeration changes no proposal probabilities,
including the unused-code outcome. -/
theorem proposal_law (A : Instance I J) (S : State A) :
    mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)=
      mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
        (CompanionBooleanPhase.proposal A S) := by
  let p := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (proposal A S)
  let q := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
    (CompanionBooleanPhase.proposal A S)
  have hs (T : State A) : p.mass (some T)=q.mass (some T) :=
    (proposal_mass A S T).trans (CompanionBooleanPhase.proposal_mass A S T).symm
  change p=q
  apply RationalLaw.ext
  funext T
  cases T with
  | some T => exact hs T
  | none =>
    have hp := p.total
    have hq := q.total
    simp only [Fintype.sum_option] at hp hq
    simp_rw [hs] at hp
    linarith

end
end ContingencyTables.CompanionArithmeticProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionChainValidator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial validation of paired binary states

The bounded-profile arithmetic test specializes to width one.
Thus the companion's state filter is a concrete list program on the two
coordinates of every labelled pair.
-/

namespace ContingencyTables.CompanionChainValidator
open CommonBasesFPRAS TwoLiftStates ProfilePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

noncomputable section

variable {P : Type*} [Fintype P]

omit [Fintype P] in
lemma single_iff_occupancy (S : Set (P×Bool)) (p : P) :
    PairSingle (pair p) S ↔ occupancy S p=1 := by
  unfold PairSingle TwoLiftStates.pair occupancy
  by_cases h0 : (p,false)∈S <;> by_cases h1 : (p,true)∈S <;> simp [h0,h1]

omit [Fintype P] in
lemma empty_iff_occupancy (S : Set (P×Bool)) (p : P) :
    PairEmpty (pair p) S ↔ occupancy S p=0 := by
  unfold PairEmpty TwoLiftStates.pair occupancy
  by_cases h0 : (p,false)∈S <;> by_cases h1 : (p,true)∈S <;> simp [h0,h1]

omit [Fintype P] in
lemma full_iff_occupancy (S : Set (P×Bool)) (p : P) :
    PairFull (pair p) S ↔ occupancy S p=2 := by
  unfold PairFull TwoLiftStates.pair occupancy
  by_cases h0 : (p,false)∈S <;> by_cases h1 : (p,true)∈S <;> simp [h0,h1]

lemma plain_iff_occupancy (S : Set (P×Bool)) :
    PlainState pairs S ↔ ∀ p,occupancy S p=1 := by
  constructor
  · intro h p
    exact (single_iff_occupancy S p).mp (h (pair p) (pair_mem p))
  · intro h p hp
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    exact (single_iff_occupancy S q).mpr (h q)

lemma defect_iff_occupancy (S : Set (P×Bool)) (p q : P) :
    DefectState pairs (pair p) (pair q) S ↔ p≠q ∧
      ∀ i,occupancy S i+(if i=p then 1 else 0)=1+(if i=q then 1 else 0) := by
  constructor
  · intro h
    exact ⟨fun he => h.2.2.1 (congrArg pair he),defect_occupancy S p q h⟩
  · rintro ⟨hpq,h⟩
    refine ⟨pair_mem p,pair_mem q,fun he => hpq (pair_injective he),?_,?_,?_⟩
    · apply (empty_iff_occupancy S p).mpr
      have hh := h p
      simp only [ite_true, if_true,hpq,ite_false] at hh
      omega
    · apply (full_iff_occupancy S q).mpr
      have hh := h q
      simp only [ite_true, if_true,Ne.symm hpq,ite_false,Nat.add_zero] at hh
      omega
    · intro t ht htp htq
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
      apply (single_iff_occupancy S i).mpr
      have hip : i≠p := fun he => htp (congrArg pair he)
      have hiq : i≠q := fun he => htq (congrArg pair he)
      simpa only [hip,hiq,ite_false,Nat.add_zero] using h i

lemma chain_iff_occupancy (S : Set (P×Bool)) :
    ChainState pairs S ↔ (∀ i,occupancy S i=1) ∨
      ∃ p q : P,p≠q ∧ ∀ i,occupancy S i+(if i=p then 1 else 0)=1+(if i=q then 1 else 0) := by
  constructor
  · rintro (h|⟨p,q,h⟩)
    · exact Or.inl ((plain_iff_occupancy S).mp h)
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp h.1
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp h.2.1
      exact Or.inr ⟨a,b,(defect_iff_occupancy S a b).mp h⟩
  · rintro (h|⟨p,q,h⟩)
    · exact Or.inl ((plain_iff_occupancy S).mpr h)
    · exact Or.inr ⟨pair p,pair q,(defect_iff_occupancy S p q).mpr h⟩

/-- Width one is exactly the companion's labelled paired-state test. -/
theorem paired_pattern_iff {m : ℕ} (e : Fin m ≃ P) (S : Set (P×Bool)) :
    patternTest ((List.ofFn (fun i => if (e i,false)∈S then 1 else 0),
      List.ofFn (fun i => if (e i,true)∈S then 1 else 0)),1)=true ↔ ChainState pairs S := by
  rw [patternTest_ofFn,chain_iff_occupancy]
  change (∀ i,occupancy S (e i)=1) ∨
    (∃ p q : Fin m,p≠q ∧ ∀ i,occupancy S (e i)+(if i=p then 1 else 0)=
      1+(if i=q then 1 else 0)) ↔ _
  constructor
  · rintro (h|⟨p,q,hpq,h⟩)
    · exact Or.inl (fun i => by simpa using h (e.symm i))
    · refine Or.inr ⟨e p,e q,fun he => hpq (e.injective he),?_⟩
      intro i
      simpa only [Equiv.apply_symm_apply,e.symm_apply_eq] using h (e.symm i)
  · rintro (h|⟨p,q,hpq,h⟩)
    · exact Or.inl (fun i => h (e i))
    · refine Or.inr ⟨e.symm p,e.symm q,fun he => hpq (e.symm.injective he),?_⟩
      intro i
      simpa only [←e.eq_symm_apply] using h (e i)

end

end ContingencyTables.CompanionChainValidator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOrderedProposal
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with a specified coordinate order

The coordinate scan and its paired-state validator work with the same
explicit order used by the initializer. Its dyadic proposal law is
independent of this order, including unused proposal words.
-/

namespace ContingencyTables.CompanionOrderedProposal

open CommonBasesFPRAS TwoLiftStates CompanionFactorialApplication
open CompanionArithmeticProposal CompanionChainValidator CompanionNeighborProgram
open CompanionBooleanPhase FirstSuccess ResidualMixture ProfilePrograms
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {m p : ℕ}

lemma mem_orderedNeighbors (e : (Labels A×Bool) ≃ Fin m) (S T : State A) :
    T∈orderedNeighbors A e S ↔ ExchangeAdjacent S.val T.val :=
  mem_neighborStates e pairs S T

lemma orderedNeighbors_nodup (e : (Labels A×Bool) ≃ Fin m) (S : State A) :
    (orderedNeighbors A e S).Nodup := neighborStates_nodup e pairs S

lemma orderedNeighbors_length (e : (Labels A×Bool) ≃ Fin m) (S : State A) :
    (orderedNeighbors A e S).length≤2^proposalBits A := by
  have he : (orderedNeighbors A e S).toFinset=
      Finset.univ.filter (fun T : State A => ExchangeAdjacent S.val T.val) := by
    ext T
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,
      mem_orderedNeighbors]
  rw [←List.toFinset_card_of_nodup (orderedNeighbors_nodup A e S),he]
  simpa only [Fintype.card_subtype] using proposal_codes A S

lemma orderedProposal_mass (e : (Labels A×Bool) ≃ Fin m) (S T : State A) :
    (mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
      (orderedProposal A e S)).mass (some T)=
      if ExchangeAdjacent S.val T.val then 1/(2:ℚ)^proposalBits A else 0 := by
  exact (listWordChoice_mass (orderedNeighbors A e S) (orderedNeighbors_nodup A e S)
    (proposalBits A) (orderedNeighbors_length A e S) T).trans
      (by simp only [mem_orderedNeighbors])

/-- Every complete coordinate order has the analysed proposal law. -/
theorem orderedProposal_law (e : (Labels A×Bool) ≃ Fin m) (S : State A) :
    mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (orderedProposal A e S)=
      mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
        (CompanionBooleanPhase.proposal A S) := by
  let u := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool)) (orderedProposal A e S)
  let v := mapLaw (uniformLaw (α := Fin (proposalBits A) → Bool))
    (CompanionBooleanPhase.proposal A S)
  have hs (T : State A) : u.mass (some T)=v.mass (some T) :=
    (orderedProposal_mass A e S T).trans (CompanionBooleanPhase.proposal_mass A S T).symm
  change u=v
  apply RationalLaw.ext
  funext T
  cases T with
  | some T => exact hs T
  | none =>
    have hu := u.total
    have hv := v.total
    simp only [Fintype.sum_option] at hu hv
    simp_rw [hs] at hu
    linarith

lemma pairedStateTest_ordered (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m)
    (S : Set (Labels A×Bool)) :
    pairedStateTest (orderedCatalog A g e,encodeSet e S)=true ↔ ChainState pairs S := by
  unfold pairedStateTest orderedCatalog
  simp only [List.map_ofFn]
  change patternTest ((List.ofFn (fun i : Fin p =>
      (encodeSet e S).getD (e (g i,false)).val 0),
    List.ofFn (fun i : Fin p => (encodeSet e S).getD (e (g i,true)).val 0)),1)=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  exact paired_pattern_iff g S

lemma validExchanges_ordered (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m)
    (S : State A) :
    validExchanges (orderedCatalog A g e,encodeSet e S.val)=
      (orderedNeighbors A e S).map (fun T => encodeSet e T.val) := by
  unfold validExchanges orderedNeighbors neighborStates neighborSets
  rw [List.map_filterMap,List.filterMap_map,←List.filterMap_eq_filter]
  apply List.filterMap_congr
  intro xs hxs
  obtain ⟨T,hT,rfl⟩ := (mem_raw_codes e S.val xs).mp hxs
  simp only [Function.comp_apply,decode_encode]
  by_cases h : ChainState pairs T
  · have hp : pairedStateTest (orderedCatalog A g e,encodeSet e T)=true :=
      (pairedStateTest_ordered A g e T).mpr h
    simp only [dite_eq_left h,Option.map_some,Option.guard,hp,ite_true, if_true]
  · have hp : pairedStateTest (orderedCatalog A g e,encodeSet e T)=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact h ((pairedStateTest_ordered A g e T).mp ht)
    simp only [dite_eq_right h,Option.map_none,Option.guard,hp,Bool.false_eq_true,ite_false]

/-- The polynomial list program returns exactly the encoded state drawn
by the ordered proposal; no enumeration of all chain states is needed. -/
theorem codeProposal_ordered (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin m)
    (S : State A) (bits : Fin (proposalBits A) → Bool) :
    codeProposal ((orderedCatalog A g e,encodeSet e S.val),List.ofFn bits)=
      (orderedProposal A e S bits).map (fun T => encodeSet e T.val) := by
  rw [codeProposal,validExchanges_ordered]
  simp only [listWordChoice,orderedProposal,List.getElem?_map]

end
end ContingencyTables.CompanionOrderedProposal

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CanonicalInitialEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical paired-label order for the initial binary program

The order is the explicit list of cells, then their copies, then the
two sides of each pair. The code is obtained directly from the sampled
Boolean rows, so no enumeration of the set-valued state space occurs.
-/

namespace ContingencyTables.CanonicalInitialEncoding

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CommonBasesFPRAS InitialTransversals FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators Classical

noncomputable section
variable {q : ℕ} (b : Fin q → ℕ)

lemma coordinateOrder : List.ofFn (coordinateEquiv b).symm=pairOrder b := by
  change List.ofFn (pairOrder b).get=pairOrder b
  exact List.ofFn_get (pairOrder b)

lemma encodeSet_eq_map (S : Set (Copy b×Bool)) :
    CompanionArithmeticProposal.encodeSet (coordinateEquiv b) S=
      (pairOrder b).map (fun p => if p∈S then 1 else 0) := by
  have h := congrArg (List.map (fun p => if p∈S then (1:ℕ) else 0)) (coordinateOrder b)
  rw [List.map_ofFn] at h
  exact h

end
end ContingencyTables.CanonicalInitialEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma capacities_eq (A : Instance (Fin m) (Fin n)) :
    capacities (input A)=List.ofFn (fun i => A.b ((cellEquiv A) i).val.1 ((cellEquiv A) i).val.2) := by
  apply List.ext_getElem
  · simp only [capacities,List.length_map,List.length_ofFn]
  · intro i hi hj
    have hi' : i<(catalog (input A)).length := by simpa only [List.length_ofFn] using hj
    simp only [capacities,List.getElem_map,List.getElem_ofFn]
    have he := catalogCell_coordinates A ⟨i,hi'⟩
    change entry (input A,(catalog (input A))[i]'hi')=
      A.b (catalogCell A ⟨i,hi'⟩).val.1 (catalogCell A ⟨i,hi'⟩).val.2
    rw [←he]
    exact entry_input A _ _

end
end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedInitial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates CommonBasesFPRAS
open CompanionArithmeticProposal
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma encodeSet_reindex (S : Set (Labels A×Bool)) :
    encodeSet (coordinateOrder A) S=
      encodeSet (CanonicalInitialEncoding.coordinateEquiv (capacities A))
        ((pairOrder A).symm ⁻¹' S) := rfl

end
end ContingencyTables.CompanionComputedInitial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

lemma pairList_product {α : Type*} (xs : List α) : pairList xs=xs.product [false,true] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (a,false)::(a,true)::pairList xs=(a,false)::(a,true)::xs.product [false,true]
    rw [ih]

lemma pairList_get_even {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    (pairList xs)[2*i]'(by rw [pairList_length]; omega)=(xs[i],false) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [pairList,Nat.mul_succ,List.getElem_cons_succ] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma pairList_get_odd {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    (pairList xs)[2*i+1]'(by rw [pairList_length]; omega)=(xs[i],true) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [pairList,Nat.mul_succ,List.getElem_cons_succ,Nat.add_assoc] using
        ih i (Nat.lt_of_succ_lt_succ hi)

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open scoped Classical
variable {q : ℕ} (b : Fin q → ℕ)

lemma coordinate_false (i : Fin (copyOrder b).length) :
    (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,false)).val=2*i.val := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  let k : Fin (pairOrder b).length := ⟨2*i.val,by rw [hl]; omega⟩
  have hk : (CanonicalInitialEncoding.coordinateEquiv b).symm k=(labelOrder b i,false) := by
    change (pairOrder b)[k.val]=((copyOrder b)[i.val],false)
    simpa only [pairOrder,←pairList_product,k] using pairList_get_even (copyOrder b) i.val i.isLt
  have he := congrArg (fun a => (CanonicalInitialEncoding.coordinateEquiv b a).val) hk
  simpa only [Equiv.apply_symm_apply,k] using he.symm

lemma coordinate_true (i : Fin (copyOrder b).length) :
    (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,true)).val=2*i.val+1 := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  let k : Fin (pairOrder b).length := ⟨2*i.val+1,by rw [hl]; omega⟩
  have hk : (CanonicalInitialEncoding.coordinateEquiv b).symm k=(labelOrder b i,true) := by
    change (pairOrder b)[k.val]=((copyOrder b)[i.val],true)
    simpa only [pairOrder,←pairList_product,k] using pairList_get_odd (copyOrder b) i.val i.isLt
  have he := congrArg (fun a => (CanonicalInitialEncoding.coordinateEquiv b a).val) hk
  simpa only [Equiv.apply_symm_apply,k] using he.symm

/-- Every state encoded in the canonical order has exactly the pair
catalog computed by the polynomial consecutive-coordinate scan. -/
theorem catalog_encode (S : Set (Copy b×Bool)) :
    catalog (encodeSet (CanonicalInitialEncoding.coordinateEquiv b) S)=
      List.ofFn (fun i : Fin (copyOrder b).length =>
        ((CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,false)).val,
          (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,true)).val)) := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  simp only [catalog,encodeSet,List.length_ofFn,hl]
  rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,indexPair,
      coordinate_false,coordinate_true]

end
end ContingencyTables.PairedCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with computed metadata

The executable proposal receives only a binary profile and fresh bits.
It computes the consecutive-pair catalog itself and scans coordinate
exchanges. Its semantic law is the same ordered proposal law.
-/

namespace ContingencyTables.CompanionComputedProposal

open MatchingFPRAS.TreeTyped CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionNeighborProgram
open CompanionBooleanPhase
open scoped Classical

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma pair_coordinate (i : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length)
    (side : Bool) :
    coordinateOrder A (pairLabels A i,side)=
      CanonicalInitialEncoding.coordinateEquiv (capacities A)
        (PairedCatalogProgram.labelOrder (capacities A) i,side) := by
  simp [coordinateOrder,pairOrder,pairLabels]

lemma generated_catalog (S : Set (Labels A×Bool)) :
    PairedCatalogProgram.catalog (encodeSet (coordinateOrder A) S)=
      orderedCatalog A (pairLabels A) (coordinateOrder A) := by
  have he : encodeSet (coordinateOrder A) S=
      encodeSet (CanonicalInitialEncoding.coordinateEquiv (capacities A))
        ((pairOrder A).symm ⁻¹' S) := rfl
  rw [he,PairedCatalogProgram.catalog_encode]
  unfold orderedCatalog
  apply congrArg List.ofFn
  funext i
  rw [pair_coordinate,pair_coordinate]

/-- Every proposed code is the encoding of the actual ordered proposal
state, and unused binary indices give precisely the same `none` result. -/
theorem proposalProgram_eq (S : State A) (bits : Fin (proposalBits A) → Bool) :
    proposalProgram (encodeSet (coordinateOrder A) S.val,List.ofFn bits)=
      (orderedProposal A (coordinateOrder A) S bits).map
        (fun T => encodeSet (coordinateOrder A) T.val) := by
  unfold proposalProgram
  rw [generated_catalog]
  exact codeProposal_ordered A (pairLabels A) (coordinateOrder A) S bits

end
end ContingencyTables.CompanionComputedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrajectory
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The observed Boolean trajectory has the source path law

The finite history stores the visited prefix. Its exact real reference
expectation is the manuscript's list-path expectation, so the row error
controls events involving all empirical observations simultaneously.
-/

namespace ContingencyTables.CompanionPhaseTrajectory

open CommonBasesFPRAS RealKernelApproximation CompanionBooleanPhase
open FirstSuccess ResidualMixture FiniteLawMoments
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {X : Type*}

lemma read_put {N : ℕ} (a : PathState X N) (x : X) : pathRead (pathPut a x)=x := by
  simp [pathRead,pathPut]

lemma position_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    (pathPut a x).1.val=a.1.val+1 := by
  simp only [pathPut,nextPosition,min_eq_left (Nat.succ_le_of_lt h)]

lemma prefix_put {N : ℕ} (a : PathState X N) (x : X) (h : a.1.val<N) :
    historyPrefix (pathPut a x)=historyPrefix a++[x] := by
  rcases a with ⟨⟨i,hi⟩,v⟩
  change i<N at h
  have hh : i+1≤N := by omega
  simp only [historyPrefix,pathPut,nextPosition,min_eq_left hh]
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext k
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      have hv' : k.val=i+1 := by simpa only [Fin.cast,Fin.castSucc,Fin.castAdd,Fin.castLE] using hv
      exact (Nat.ne_of_lt k.isLt) hv')]
    exact congrArg v (Fin.ext rfl)
  · simp only [List.singleton_inj]
    exact Function.update_self _ _ _

lemma prefix_initial (N : ℕ) (x : X) : historyPrefix (pathInitial N x)=[x] := by
  simp [historyPrefix,pathInitial,List.ofFn_succ]

end

end ContingencyTables.CompanionPhaseTrajectory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseCounts
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable counts in an outer counting phase

The stored trajectory is scanned directly. Both the transversal count
and each labelled defect count use the actual polynomial occupancy
tests. No set-state enumeration is performed.
-/

namespace ContingencyTables.CompanionPhaseCounts

open MatchingFPRAS.TreeTyped ProfilePrograms CompanionChainValidator
open CompanionTraceProgram CompanionOrderedProposal CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase
open CommonBasesFPRAS TwoLiftStates
open scoped Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

lemma plainTest_ordered (S : Set (Labels A×Bool)) :
    pairedPlainTest (orderedCatalog A g e,encodeSet e S)=true ↔ PlainState pairs S := by
  unfold pairedPlainTest orderedCatalog
  simp only [List.map_ofFn]
  change balancedTest ((List.ofFn (fun i : Fin p => (encodeSet e S).getD (e (g i,false)).val 0),
    List.ofFn (fun i : Fin p => (encodeSet e S).getD (e (g i,true)).val 0)),1)=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  rw [balancedTest_ofFn,plain_iff_occupancy]
  change (∀ i,occupancy S (g i)=1) ↔ ∀ a,occupancy S a=1
  constructor
  · intro h a
    simpa only [Equiv.apply_symm_apply] using h (g.symm a)
  · intro h i
    exact h (g i)

lemma defectTest_ordered (S : Set (Labels A×Bool)) (i j : Fin p) :
    pairedDefectTest ((orderedCatalog A g e,encodeSet e S),(i.val,j.val))=true ↔
      DefectState pairs (pair (g i)) (pair (g j)) S := by
  classical
  unfold pairedDefectTest orderedCatalog
  simp only [List.map_ofFn]
  change defectTest (((List.ofFn (fun k : Fin p => (encodeSet e S).getD (e (g k,false)).val 0),
    List.ofFn (fun k : Fin p => (encodeSet e S).getD (e (g k,true)).val 0)),1),
    (i.val,j.val))=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  rw [defectTest_ofFn,defect_iff_occupancy]
  constructor
  · rintro ⟨hij,h⟩
    refine ⟨fun he => hij (g.injective he),fun a => ?_⟩
    have hh := h (g.symm a)
    by_cases hai : a=g i <;> by_cases haj : a=g j
    all_goals simpa only [occupancy,Equiv.apply_symm_apply,Equiv.symm_apply_eq,
      hai,haj,ite_true, if_true,ite_false] using hh
  · rintro ⟨hij,h⟩
    refine ⟨fun he => hij (congrArg g he),fun k => ?_⟩
    simpa only [occupancy,Equiv.apply_eq_iff_eq] using h (g k)

theorem plainCount_code (states : List (Set (Labels A×Bool))) :
    plainCountCode (orderedCatalog A g e,states.map (encodeSet e))=
      CompanionRationalUpdates.plainCount A states := by
  unfold plainCountCode CompanionRationalUpdates.plainCount
  rw [List.filter_map,List.length_map,List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro S _
  exact Bool.eq_iff_iff.mpr (by simp only [Function.comp_apply,plainTest_ordered,decide_eq_true_eq])

theorem defectCount_code (states : List (Set (Labels A×Bool))) (i j : Fin p) :
    defectCountCode ((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val))=
      CompanionRationalUpdates.defectCount A states (pair (g i)) (pair (g j)) := by
  unfold defectCountCode CompanionRationalUpdates.defectCount
  rw [List.filter_map,List.length_map,List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro S _
  exact Bool.eq_iff_iff.mpr (by simp only [Function.comp_apply,defectTest_ordered,decide_eq_true_eq])

end
end ContingencyTables.CompanionPhaseCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary rational program for each learned multiplier

The two observed frequencies have the same trajectory length, which
cancels before division. Thus one multiplication by the ratio of the
actual integer counts implements the exact rational update, including
the zero-denominator behavior on unsuccessful histories.
-/

namespace ContingencyTables.CompanionMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionPhaseCounts CompanionFactorialApplication CompanionRationalUpdates
open CompanionOrderedProposal CompanionArithmeticProposal CommonBasesFPRAS
open scoped Classical

lemma updateCode_value (z : UpdateInput) :
    TreeFraction.val (updateCode z)=
      if z.1.2.1=z.1.2.2 then TreeFraction.val z.2
      else TreeFraction.val z.2*(plainCountCode z.1.1:ℚ)/(defectCountCode z.1:ℚ) := by
  unfold updateCode
  split_ifs
  · rfl
  · rw [TreeFraction.mul_val]
    simp only [countRatio,TreeFraction.val,mul_div_assoc]

end ContingencyTables.CompanionMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open CommonBasesFPRAS
open scoped Classical

lemma positiveCounts_iff (z : ReturnInput) :
    positiveCounts z=true ↔ 0<plainCountCode z ∧
      ∀ i∈indices z,∀ j∈indices z,i=j ∨ 0<defectCountCode (z,(i,j)) := by
  unfold positiveCounts
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨of_decide_eq_true hp,fun i hi j hj => ?_⟩
    have hr : positiveRow (z,i)=true := List.all_eq_true.mp h i hi
    have he : positiveEntry (z,(i,j))=true := List.all_eq_true.mp hr j hj
    exact of_decide_eq_true he
  · rintro ⟨hp,h⟩
    refine ⟨decide_eq_true hp,List.all_eq_true.mpr (fun i hi => ?_)⟩
    apply List.all_eq_true.mpr
    intro j hj
    exact decide_eq_true (h i hi j hj)

noncomputable section
open TwoLiftStates
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

lemma readEntry_code (w : Fin p → Fin p → TreeFraction.Fraction) (i j : Fin p) :
    readEntry (matrixCode w,(i.val,j.val))=w i j := by
  simp only [readEntry,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta]

theorem updateEntry_code (states : List (Set (Labels A×Bool)))
    (w : Fin p → Fin p → TreeFraction.Fraction) (i j : Fin p) :
    updateEntry (((orderedCatalog A g e,states.map (encodeSet e)),matrixCode w),(i.val,j.val))=
      updateCode (((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val)),w i j) := by
  simp only [updateEntry,readEntry_code]

lemma positiveCounts_code (states : List (Set (Labels A×Bool))) :
    positiveCounts (orderedCatalog A g e,states.map (encodeSet e))=true ↔
      CountsPositive A states := by
  have he : positiveCounts (orderedCatalog A g e,states.map (encodeSet e))=true ↔
      0<plainCount A states ∧ ∀ i j : Fin p,i≠j →
        0<defectCount A states (pair (g i)) (pair (g j)) := by
    rw [positiveCounts_iff,plainCount_code A g e states]
    have hi : indices (orderedCatalog A g e,states.map (encodeSet e))=List.range p := by
      simp only [indices,orderedCatalog,List.length_ofFn]
    rw [hi]
    simp only [List.mem_range]
    constructor
    · rintro ⟨hp,h⟩
      refine ⟨hp,fun i j hij => ?_⟩
      have hh := h i.val i.isLt j.val j.isLt
      have hn : i.val≠j.val := fun h => hij (Fin.ext h)
      simp only [hn,false_or] at hh
      rw [defectCount_code A g e states i j] at hh
      exact hh
    · rintro ⟨hp,h⟩
      refine ⟨hp,fun i hi j hj => ?_⟩
      by_cases hij : i=j
      · exact Or.inl hij
      · right
        have hh := h ⟨i,hi⟩ ⟨j,hj⟩ (fun he => hij (congrArg Fin.val he))
        rw [←defectCount_code A g e states ⟨i,hi⟩ ⟨j,hj⟩] at hh
        exact hh
  rw [he]
  unfold CountsPositive
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun a ha b hb hab => ?_⟩
    obtain ⟨a',_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b',_,rfl⟩ := List.mem_map.mp hb
    obtain ⟨i,rfl⟩ := g.surjective a'
    obtain ⟨j,rfl⟩ := g.surjective b'
    exact h i j (fun he => hab (congrArg (fun k => pair (g k)) he))
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun i j hij => ?_⟩
    exact h _ (pair_mem _) _ (pair_mem _)
      (fun he => hij (g.injective (pair_injective he)))

/-- The executable update contains exactly one entry for every ordered
pair of labels, in the same order as the executable proposal catalog. -/
theorem updateMatrix_code (states : List (Set (Labels A×Bool)))
    (w : Fin p → Fin p → TreeFraction.Fraction) :
    updateMatrix ((orderedCatalog A g e,states.map (encodeSet e)),matrixCode w)=
      matrixCode (fun i j => updateCode
        (((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val)),w i j)) := by
  unfold updateMatrix matrixCode
  have hi : indices (orderedCatalog A g e,states.map (encodeSet e))=List.range p := by
    simp only [indices,orderedCatalog,List.length_ofFn]
  rw [hi]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi' _
    have hip : i<p := by simpa only [List.length_map,List.length_range] using hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold updateRow
    rw [hi]
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro j hj' _
      have hjp : j<p := by simpa only [List.length_map,List.length_range] using hj'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,rowEntry]
      exact updateEntry_code A g e states w ⟨i,hip⟩ ⟨j,hjp⟩

end
end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStateMultiplierProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the multiplier of an actual encoded chain state

The at most quadratic list of labelled defect types is searched using
the proved occupancy test. Uniqueness of defect labels identifies the
selected matrix entry with the mathematical chain multiplier.
-/

namespace ContingencyTables.CompanionStateMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionChainValidator CompanionPhaseCounts CompanionMultiplierMatrixProgram

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal CompanionOrderedProposal
open CommonBasesFPRAS TwoLiftStates
open scoped Classical
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A) (e : (Labels A × Bool) ≃ Fin m)

lemma candidates_mem (S : Set (Labels A × Bool)) (ij : ℕ × ℕ) :
    ij ∈ candidates (orderedCatalog A g e,encodeSet e S) ↔ ij.1 < p ∧ ij.2 < p := by
  rcases ij with ⟨i,j⟩
  unfold candidates
  rw [mem_cellPairs]
  simp only [coordinates,orderedCatalog,List.length_map,List.length_ofFn]

lemma found_mem (S : Set (Labels A × Bool)) (ij : ℕ × ℕ) :
    ij ∈ found (orderedCatalog A g e,encodeSet e S) ↔
      ∃ (i j : Fin p), (i.val,j.val)=ij ∧ DefectState pairs (pair (g i)) (pair (g j)) S := by
  rw [found,List.mem_filter,candidates_mem]
  constructor
  · rintro ⟨⟨hi,hj⟩,ht⟩
    refine ⟨⟨ij.1,hi⟩,⟨ij.2,hj⟩,rfl,?_⟩
    exact (defectTest_ordered A g e S _ _).mp ht
  · rintro ⟨i,j,hij,ht⟩
    cases hij
    exact ⟨⟨i.isLt,j.isLt⟩,(defectTest_ordered A g e S i j).mpr ht⟩

lemma found_exists (S : Set (Labels A × Bool)) :
    found (orderedCatalog A g e,encodeSet e S) ≠ [] ↔
      ∃ a b,DefectState pairs a b S := by
  constructor
  · intro hn
    obtain ⟨ij,hij⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨i,j,_,hd⟩ := (found_mem A g e S ij).mp hij
    exact ⟨pair (g i),pair (g j),hd⟩
  · rintro ⟨a,b,hd⟩ hn
    obtain ⟨u,_,hu⟩ := List.mem_map.mp hd.1
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hd.2.1
    have hm : ((g.symm u).val,(g.symm v).val) ∈ found (orderedCatalog A g e,encodeSet e S) := by
      apply (found_mem A g e S _).mpr
      refine ⟨g.symm u,g.symm v,rfl,?_⟩
      simpa only [Equiv.apply_symm_apply,hu,hv] using hd
    simp only [hn,List.not_mem_nil] at hm

theorem output_code (S : Set (Labels A × Bool)) (w : Fin p → Fin p → TreeFraction.Fraction) :
    TreeFraction.val (output (CompanionMultiplierMatrixProgram.matrixCode w,
      (orderedCatalog A g e,encodeSet e S)))=
        rationalMultiplier pairs
          (fun a b => TreeFraction.val (w (g.symm a.1.1) (g.symm b.1.1))) S := by
  by_cases h : ∃ a b,DefectState pairs a b S
  · have hn := (found_exists A g e S).mpr h
    have hm : (found (orderedCatalog A g e,encodeSet e S)).getD 0 (0,0) ∈
        found (orderedCatalog A g e,encodeSet e S) := by
      cases hl : found (orderedCatalog A g e,encodeSet e S) with
      | nil => exact (hn hl).elim
      | cons a as => simp only [List.getD_cons_zero,List.mem_cons,true_or]
    obtain ⟨i,j,hij,hd⟩ := (found_mem A g e S _).mp hm
    have he := hd.unique h.choose_spec.choose_spec
    unfold output noDefect readDefect
    have heNonempty : (found (orderedCatalog A g e,encodeSet e S)).isEmpty=false := by
      cases hl : found (orderedCatalog A g e,encodeSet e S) with
      | nil => exact (hn hl).elim
      | cons a as => rfl
    rw [heNonempty]
    simp only [Bool.false_eq_true,ite_false]
    rw [←hij,readEntry_code]
    have hi : g i=h.choose.1.1 := congrArg (fun a => a.1.1) he.1
    have hj : g j=h.choose_spec.choose.1.1 := congrArg (fun a => a.1.1) he.2
    have hi' : i=g.symm h.choose.1.1 := by
      simpa only [Equiv.symm_apply_apply] using congrArg g.symm hi
    have hj' : j=g.symm h.choose_spec.choose.1.1 := by
      simpa only [Equiv.symm_apply_apply] using congrArg g.symm hj
    rw [rationalMultiplier,dite_eq_left h]
    rw [←hi',←hj']
  · have hn : found (orderedCatalog A g e,encodeSet e S)=[] := by
      by_contra hn
      exact h ((found_exists A g e S).mp hn)
    simp only [output,noDefect,hn,List.isEmpty_nil,ite_true, if_true,TreeFraction.val,
      Nat.cast_one,div_one,rationalMultiplier,dite_eq_right h]

end
end ContingencyTables.CompanionStateMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixSubtractProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entrywise natural subtraction on a supplied matrix shape -/

namespace ContingencyTables.MatrixSubtractProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

theorem matrix_code {m n : ℕ} (B Y : Fin m → Fin n → ℕ) :
    matrix (matrixCode B,matrixCode Y)=matrixCode (fun i j => B i j-Y i j) := by
  simp only [matrix,indices,matrixCode,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  simp only [row,columns,sourceRow,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,dite_true,Option.getD_some,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,Function.comp_def,entry]
  apply congrArg List.ofFn
  funext j
  exact congrArg₂ Nat.sub (matrixEntry_code B i j) (matrixEntry_code Y i j)

end ContingencyTables.MatrixSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SparseViewMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materializing a sparse retained-cell view in a rectangular matrix -/

namespace ContingencyTables.SparseViewMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial ProfilePrograms DensePrograms

theorem matrix_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (catalog : List (ℕ × ℕ)) (values : List ℕ) :
    matrix ((List.ofFn r,List.ofFn c),(catalog,values))=
      matrixCode (fun i : Fin m => fun j : Fin n =>
        lookupView ((catalog,values),(i.val,j.val))) := by
  simp only [matrix,rowIndices,row,columns,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn,Function.comp_def,entry,matrixCode]

end ContingencyTables.SparseViewMatrixProgram

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

/-- The compiled decision agrees on every Boolean word with the
rational threshold used in the proved companion transition law. -/
theorem acceptCode_ofFn (q : TreeFraction.Fraction) (B : ℕ) (bits : Fin B → Bool) :
    acceptCode (q,List.ofFn bits)=decide (FairBits.rationalThresholdAccept B (TreeFraction.val q) bits) := by
  simp only [acceptCode,threshold,scaledNumerator,bitDenominator_eq,List.length_ofFn,
    bitValue_eq_word,FairBits.rationalThresholdAccept,fraction_threshold]

end
end ContingencyTables.FractionAcceptanceProgram

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

end ContingencyTables.RootedOracleDensity

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

lemma gridEquiv_apply (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) (i : Fin (freeCount A)) :
    gridEquiv A K v (coordinateEquiv A i)=v i := by
  change v ((coordinateEquiv A).symm (coordinateEquiv A i))=v i
  rw [Equiv.symm_apply_apply]

lemma gridEdge_iff (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v w : Grid (I := Fin (freeCount A)) K) (i : Fin (freeCount A)) :
    IsGridEdge (gridEquiv A K v,gridEquiv A K w,coordinateEquiv A i) ↔
      IsGridEdge (v,w,i) := by
  constructor
  · rintro ⟨hstep,hrest⟩
    refine ⟨?_,?_⟩
    · simpa only [corner,gridEquiv_apply] using hstep
    · intro j hj
      have hji : coordinateEquiv A j≠coordinateEquiv A i :=
        fun h => hj ((coordinateEquiv A).injective h)
      simpa only [gridEquiv_apply] using hrest (coordinateEquiv A j) hji
  · rintro ⟨hstep,hrest⟩
    refine ⟨?_,?_⟩
    · simpa only [corner,gridEquiv_apply] using hstep
    · intro j hj
      have hji : (coordinateEquiv A).symm j≠i := by
        intro h
        exact hj ((Equiv.apply_symm_apply (coordinateEquiv A) j).symm.trans
          (congrArg (coordinateEquiv A) h))
      exact hrest ((coordinateEquiv A).symm j) hji

theorem neighbor_iff (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v w : Grid (I := Fin (freeCount A)) K) :
    Neighbor (gridEquiv A K v) (gridEquiv A K w) ↔ Neighbor v w := by
  constructor
  · rintro ⟨i,side,hi⟩
    refine ⟨(coordinateEquiv A).symm i,side,?_⟩
    cases side with
    | false =>
      change IsGridEdge (gridEquiv A K w,gridEquiv A K v,i) at hi
      apply (gridEdge_iff A K w v ((coordinateEquiv A).symm i)).mp
      simpa only [Equiv.apply_symm_apply] using hi
    | true =>
      change IsGridEdge (gridEquiv A K v,gridEquiv A K w,i) at hi
      apply (gridEdge_iff A K v w ((coordinateEquiv A).symm i)).mp
      simpa only [Equiv.apply_symm_apply] using hi
  · rintro ⟨i,side,hi⟩
    refine ⟨coordinateEquiv A i,side,?_⟩
    cases side with
    | false => exact (gridEdge_iff A K w v i).mpr hi
    | true => exact (gridEdge_iff A K v w i).mpr hi

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleKernel
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

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual oracle transition in computed catalog order

Axis proposals are uniform over a bounded dyadic code space. Changing
the coordinate order preserves their frequencies, even though it need
not preserve the value obtained from an individual proposal word.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (oracleStepBits rationalHeight)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma freeCount_eq (A : Instance (Fin m) (Fin n)) :
    freeCount A=CompanionOracleDensity.dimension A := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (RootedForestCatalog.freeEquiv A)

lemma freeCount_le (A : Instance (Fin m) (Fin n)) : freeCount A≤A.d := by
  rw [freeCount_eq]
  exact ForestScaledPenalty.free_card_le A

theorem finiteStepLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    finiteStepLaw A C a z v=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.finiteOracleStepLaw A (rowColumn A.T) C a z (gridEquiv A K v)) := by
  apply RationalLaw.eq_of_off_diagonal _ _ v
  intro w hw
  have hvw : v≠w := Ne.symm hw
  have he : gridEquiv A K v≠gridEquiv A K w :=
    fun h => hvw ((gridEquiv A K).injective h)
  change (finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun b => acceptDyadic (exponent A C a z b-exponent A C a z v)
      (rationalHeight A C))).mass w=
    (RootedOracleDensity.finiteOracleStepLaw A (rowColumn A.T) C a z
      (gridEquiv A K v)).mass (gridEquiv A K w)
  rw [finiteAcceptLaw_off_diagonal v w _ _ hvw,
    RootedOracleDensity.finiteOracleStepLaw,
    finiteAcceptLaw_off_diagonal (gridEquiv A K v) (gridEquiv A K w) _ _ he,
    axisCodeStep_count (dense_proposal_code_bound A.d (freeCount A) (freeCount_le A)),
    axisCodeStep_count (dense_proposal_code_bound A.d (CompanionOracleDensity.dimension A)
      (ForestScaledPenalty.free_card_le A)),neighbor_iff]
  rfl

lemma bitStepLaw_eq_finite (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    bitStepLaw A C a z v=finiteStepLaw A C a z v := by
  let E := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)
  let f := finiteAcceptStep v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (exponent A C a z w-exponent A C a z v) (rationalHeight A C))
  have hf : bitStep A C a z v=fun bits => f (E bits) := by
    funext bits
    dsimp [bitStep,f,E,finiteAcceptStep]
    simp only [acceptDyadic]
    cases axisCodeStep v ((pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C)) bits).1 with
    | none => rfl
    | some w => dsimp only; split_ifs <;> rfl
  unfold bitStepLaw
  rw [hf]
  change mapLaw (uniformLaw (α := Fin (Nat.clog 2 (8*A.d)+rationalHeight A C) → Bool))
    (fun bits => f (E bits))=_
  rw [←map_equiv E,uniform_equiv,←uniform_product]
  rfl

/-- The actual catalog-order finite-word experiment has the exact
transition law of the oracle mixing theorem. -/
theorem bitStepLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) :
    bitStepLaw A C a z v=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK (gridEquiv A K v)) := by
  rw [bitStepLaw_eq_finite,finiteStepLaw_eq,
    RootedOracleDensity.finiteOracleStepLaw_eq A (rowColumn A.T) C a hC haH z hz hK hKB]

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NaturalBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded scans of natural-number blocks

Numeric widths select bounded slices of the supplied list. They never
control an allocation, so malformed widths preserve polynomial cost.
-/

namespace ContingencyTables.NaturalBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma block_splitLengths (widths values : List ℕ) (i : ℕ) :
    block ((widths,values),i)=(widths.splitLengths values).getD i [] := by
  induction widths generalizing values i with
  | nil => simp [block,start]
  | cons w ws ih =>
    cases i with
    | zero => simp [block,start,List.splitLengths_cons]
    | succ i =>
      simpa only [block,start,List.take_succ_cons,List.sum_cons,List.getD_cons_succ,
        List.splitLengths_cons,List.drop_drop,Nat.add_comm] using ih (values.drop w) i

theorem blocks_eq_splitLengths (widths values : List ℕ) :
    blocks (widths,values)=widths.splitLengths values := by
  apply List.ext_getElem
  · simp [blocks,indices]
  · intro i hi hj
    have hiw : i < widths.length := by
      simpa only [blocks,indices,List.length_map,List.length_range] using hi
    simp only [blocks,indices,List.getElem_map,List.getElem_range]
    have h := block_splitLengths widths values i
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using h

lemma splitLengths_flatten (rows : List (List ℕ)) :
    (rows.map List.length).splitLengths rows.flatten=rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simpa only [List.map_cons,List.flatten_cons,List.splitLengths_cons,
      List.take_left,List.drop_left] using congrArg (List.cons row) ih

/-- A literal list of rows is recovered exactly from its stored row
lengths and its flattened code, including rows of length zero. -/
theorem blocks_flatten (rows : List (List ℕ)) :
    blocks (rows.map List.length,rows.flatten)=rows := by
  rw [blocks_eq_splitLengths,splitLengths_flatten]

end ContingencyTables.NaturalBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma interleave_get_even (xs : List (ℕ × ℕ)) (i : ℕ) (hi : i < xs.length) :
    (interleave xs)[2*i]'(by rw [interleave_length]; omega)=xs[i].1 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [interleave,Nat.mul_succ,List.getElem_cons_succ] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma interleave_get_odd (xs : List (ℕ × ℕ)) (i : ℕ) (hi : i < xs.length) :
    (interleave xs)[2*i+1]'(by rw [interleave_length]; omega)=xs[i].2 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [interleave,Nat.mul_succ,List.getElem_cons_succ,Nat.add_assoc] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma sideEntries_interleave (xs : List (ℕ × ℕ)) (side : Bool) :
    sideEntries (interleave xs,side)=
      xs.map (fun p => min (if side then p.2 else p.1) 1) := by
  apply List.ext_getElem
  · simp only [sideEntries,PairedCatalogProgram.catalog,List.length_map,List.length_range,
      interleave_length,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  · intro i hi _
    have hii : i < xs.length := by
      simpa only [sideEntries,PairedCatalogProgram.catalog,List.length_map,List.length_range,
        interleave_length,Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using hi
    simp only [sideEntries,PairedCatalogProgram.catalog,List.getElem_map,List.getElem_range,
      sideValue,PairedCatalogProgram.indexPair]
    cases side with
    | false =>
      have hidx : 2*i < (interleave xs).length := by rw [interleave_length]; omega
      simp only [Bool.false_eq_true,ite_false,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx,Option.getD_some,interleave_get_even xs i hii]
    | true =>
      have hidx : 2*i+1 < (interleave xs).length := by rw [interleave_length]; omega
      simp only [ite_true, if_true,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx,Option.getD_some,interleave_get_odd xs i hii]

lemma interleave_flatMap (xs : List (ℕ × ℕ)) :
    interleave xs=xs.flatMap (fun p => [p.1,p.2]) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change p.1 :: p.2 :: interleave xs=p.1 :: p.2 :: xs.flatMap (fun p => [p.1,p.2])
    rw [ih]

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PairedProfileSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed paired counts are the manuscript's literal profile -/

namespace ContingencyTables.PairedProfileSemantics

open PairedProfileProgram CanonicalInitialEncoding InitialTransversals
open CompanionArithmeticProposal CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {q : ℕ} (b : Fin q → ℕ)

lemma cellRows_lengths (S : Set (Copy b × Bool)) :
    (cellRows b S).map List.length=(List.ofFn b).map width := by
  simp only [cellRows,List.map_ofFn,Function.comp_def,interleave_length,List.length_ofFn,width]

lemma cellRows_flatten (S : Set (Copy b × Bool)) :
    (cellRows b S).flatten=encodeSet (coordinateEquiv b) S := by
  rw [encodeSet_eq_map]
  simp only [cellRows,interleave_flatMap,pairOrder,copyOrder,List.sigma,List.product,
    List.ofFn_eq_map,List.flatten_eq_flatMap,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,List.map_map]
  apply List.flatMap_congr
  intro i _
  simp only [id_eq,Function.comp_def]
  apply List.flatMap_congr
  intro k _
  rfl

lemma rows_encode (S : Set (Copy b × Bool)) :
    rows (List.ofFn b,encodeSet (coordinateEquiv b) S)=cellRows b S := by
  rw [rows,←cellRows_lengths b S,←cellRows_flatten b S]
  exact NaturalBlockProgram.blocks_flatten _

lemma counts_cellRow (S : Set (Copy b × Bool)) (i : Fin q) :
    counts (interleave (List.ofFn (fun k : Fin (b i) =>
      (if (⟨i,k⟩,false) ∈ S then 1 else 0,
       if (⟨i,k⟩,true) ∈ S then 1 else 0))))=
      ((∑ k : Fin (b i), if (⟨i,k⟩,false) ∈ S then 1 else 0),
       (∑ k : Fin (b i), if (⟨i,k⟩,true) ∈ S then 1 else 0)) := by
  simp only [counts,sideCount,sideEntries_interleave,List.map_ofFn,Function.comp_def,ite_false,ite_true, if_true,
    Bool.false_eq_true,List.sum_ofFn]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> split_ifs <;> simp_all

theorem profileRows_encode (S : Set (Copy b × Bool)) :
    profileRows (List.ofFn b,encodeSet (coordinateEquiv b) S)=List.ofFn (fun i =>
      ((∑ k : Fin (b i), if (⟨i,k⟩,false) ∈ S then 1 else 0),
       (∑ k : Fin (b i), if (⟨i,k⟩,true) ∈ S then 1 else 0))) := by
  rw [profileRows,rows_encode]
  simp only [cellRows,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact counts_cellRow b S i

lemma copy_viewCount (S : Set (Copy b × Bool)) (i : Fin q) (side : Bool) :
    TwoLiftStates.viewCount (fun p : Copy b => p.1) S i side=
      ∑ k : Fin (b i), if (⟨i,k⟩,side) ∈ S then 1 else 0 := by
  unfold TwoLiftStates.viewCount
  rw [Fintype.sum_sigma]
  calc
    _=∑ x : Fin q, if x=i then
        (∑ k : Fin (b x), if (⟨x,k⟩,side) ∈ S then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x=i
      · subst x
        simp
      · simp [hx]
    _=_ := by simp

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma physical_profile_reindex (S : Set (Labels A × Bool)) (s : SmallCell A) (side : Bool) :
    CompanionWeightOracle.profile A S (s,side)=
      TwoLiftStates.viewCount (fun p : Copy (CompanionComputedInitial.capacities A) => p.1)
        ((CompanionComputedInitial.pairOrder A).symm ⁻¹' S)
        (CompanionComputedInitial.cellOrder A s) side := by
  rw [CompanionWeightOracle.profile,TwoLiftStates.groupCount_eq_viewCount]
  unfold TwoLiftStates.viewCount
  exact Fintype.sum_equiv (CompanionComputedInitial.copyOrder A) _ _ (fun p => by
    have he : (CompanionComputedInitial.copyOrder A p).1=
        CompanionComputedInitial.cellOrder A p.1 := rfl
    simp only [Set.mem_preimage,CompanionComputedInitial.pairOrder,Equiv.prodCongr_symm,
      Equiv.prodCongr_apply,Prod.map_apply,
      Equiv.refl_symm,Equiv.refl_apply,Equiv.symm_apply_apply,
      he,Equiv.apply_eq_iff_eq,CompanionFactorialApplication.labelCell]
    split_ifs <;> simp_all)

/-- The executed rows use the catalog's actual order, with one pair of
counts per retained physical cell. -/
theorem profileRows_physical (S : Set (Labels A × Bool)) :
    profileRows (List.ofFn (CompanionComputedInitial.capacities A),
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
      List.ofFn (fun i =>
        (CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,false),
         CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,true))) := by
  rw [CompanionComputedInitial.encodeSet_reindex,profileRows_encode]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · change _=CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,false)
    exact ((physical_profile_reindex A S _ false).trans
      (by rw [Equiv.apply_symm_apply,copy_viewCount])).symm
  · change _=CompanionWeightOracle.profile A S ((CompanionComputedInitial.cellOrder A).symm i,true)
    exact ((physical_profile_reindex A S _ true).trans
      (by rw [Equiv.apply_symm_apply,copy_viewCount])).symm

end
end ContingencyTables.PairedProfileSemantics

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedDemandProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal PairedProfileSemantics
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles SmallGraphProfiles

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma cells_data (x q : Fin m → Fin n → ℕ) (code : List ℕ) :
    cells (RootedDemandProgram.data A x q,code)=CompanionCellCatalog.input A := rfl

lemma catalog_eq :
    CompanionCellCatalog.catalog (CompanionCellCatalog.input A)=
      cellCatalog A.small (CompanionCellCatalog.cellEquiv A) := by
  rw [cellCatalog]
  symm
  calc
    List.ofFn (fun i =>
        ((CompanionCellCatalog.cellEquiv A i).val.1.val,
          (CompanionCellCatalog.cellEquiv A i).val.2.val))=
        List.ofFn (fun i : Fin (CompanionCellCatalog.catalog
          (CompanionCellCatalog.input A)).length =>
            (CompanionCellCatalog.catalog (CompanionCellCatalog.input A))[i.val]) := by
      apply congrArg List.ofFn
      funext i
      exact CompanionCellCatalog.catalogCell_coordinates A i
    _=_ := List.ofFn_get _

lemma values_data (x q : Fin m → Fin n → ℕ) (S : Set (Labels A × Bool)) (side : Bool) :
    values ((RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S),side)=
        viewList A.small (CompanionCellCatalog.cellEquiv A)
          (CompanionWeightOracle.profile A S) side := by
  unfold values counts
  rw [cells_data,CompanionCellCatalog.capacities_eq]
  change (PairedProfileProgram.profileRows
      (List.ofFn (CompanionComputedInitial.capacities A),
        encodeSet (CompanionComputedInitial.coordinateOrder A) S)).map _=_
  rw [profileRows_physical]
  simp only [List.map_ofFn,Function.comp_def,viewList,sideEntry]
  cases side <;> rfl

lemma viewMatrix_data (x q : Fin m → Fin n → ℕ) (S : Set (Labels A × Bool)) (side : Bool) :
    viewMatrix ((RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S),side)=
        matrixCode (smallView A.small (CompanionWeightOracle.profile A S) side) := by
  let z : Input := (RootedDemandProgram.data A x q,
    encodeSet (CompanionComputedInitial.coordinateOrder A) S)
  have hi : viewInput (z,side)=
      ((List.ofFn (fun i => (A.r i).toNat),List.ofFn (fun j => (A.c j).toNat)),
        (cellCatalog A.small (CompanionCellCatalog.cellEquiv A),
          viewList A.small (CompanionCellCatalog.cellEquiv A)
            (CompanionWeightOracle.profile A S) side)) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (congrArg CompanionCellCatalog.catalog (cells_data A x q _)).trans (catalog_eq A)
      · exact values_data A x q S side
  change SparseViewMatrixProgram.matrix (viewInput (z,side))=_
  rw [hi]
  rw [SparseViewMatrixProgram.matrix_ofFn]
  apply congrArg matrixCode
  funext i j
  exact lookupView_eq A.small (CompanionCellCatalog.cellEquiv A)
    (CompanionWeightOracle.profile A S) side i j

/-- The current code replaces both demand arrays; the old demand only
provides the immutable graph, capacities, margins and baseline. -/
theorem output_data (x q : Fin m → Fin n → ℕ) (S : Set (Labels A × Bool)) :
    output (RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
        RootedDemandProgram.data A
          (ForestCountIdentification.smallX A.small (CompanionWeightOracle.profile A S))
          (fun i j => A.b i j-
            ForestCountIdentification.smallY A.small (CompanionWeightOracle.profile A S) i j) := by
  have hq : complement (RootedDemandProgram.data A x q,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
      matrixCode (fun i j => A.b i j-
        smallView A.small (CompanionWeightOracle.profile A S) true i j) := by
    change MatrixSubtractProgram.matrix (matrixCode A.b,viewMatrix
      ((RootedDemandProgram.data A x q,
        encodeSet (CompanionComputedInitial.coordinateOrder A) S),true))=_
    rw [viewMatrix_data]
    exact MatrixSubtractProgram.matrix_code _ _
  unfold output
  rw [viewMatrix_data,hq]
  rfl

end
end ContingencyTables.PairedDemandProgram

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedFactorialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact factorial multiplier from the encoded paired state

Every factorial argument is bounded by the supplied code length. In a
valid code each cell block has length twice its capacity, so the computed
denominator is exactly the manuscript's capacity factorial.
-/

namespace ContingencyTables.PairedFactorialProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial PairedProfileProgram
open scoped BigOperators Classical

lemma rowRatio_value (xs : List ℕ) :
    TreeFraction.val (rowRatio xs)=
      ((sideCount (xs,false)).factorial:ℚ)*(sideCount (xs,true)).factorial /
        (xs.length/2).factorial := by
  rw [rowRatio,TreeFraction.normalize_val]
  simp only [TreeFraction.val,numerator,sideFactor,denominator,pairCount,Nat.cast_mul]

noncomputable section
open PairedProfileSemantics InitialTransversals CanonicalInitialEncoding
open CompanionArithmeticProposal CompanionFactorialApplication

variable {q : ℕ} (b : Fin q → ℕ)

theorem output_canonical (S : Set (Copy b × Bool)) :
    TreeFraction.val (output (List.ofFn b,encodeSet (coordinateEquiv b) S))=
      ∏ i : Fin q,
        ((∑ k : Fin (b i), if ((⟨i,k⟩ : Copy b),false) ∈ S then 1 else 0).factorial:ℚ)*
          (∑ k : Fin (b i), if ((⟨i,k⟩ : Copy b),true) ∈ S then 1 else 0).factorial /
            (b i).factorial := by
  rw [output,FractionAggregateProgram.product_value,rows_encode]
  simp only [cellRows,List.map_ofFn,List.prod_ofFn,Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [rowRatio_value]
  have hc := counts_cellRow b S i
  have hfalse := congrArg Prod.fst hc
  have htrue := congrArg Prod.snd hc
  change sideCount (_,false)=_ at hfalse
  change sideCount (_,true)=_ at htrue
  rw [hfalse,htrue,interleave_length,List.length_ofFn,
    Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

/-- The multiplier used by the executed weight oracle is the literal
factorial ratio, for every subset, not just transversal states. -/
theorem output_physical (S : Set (Labels A × Bool)) :
    TreeFraction.val (output (List.ofFn (CompanionComputedInitial.capacities A),
      encodeSet (CompanionComputedInitial.coordinateOrder A) S))=
        CompanionWeightOracle.factorialRatio A S := by
  rw [CompanionComputedInitial.encodeSet_reindex,output_canonical]
  have hp (i) (side : Bool) :=
    (physical_profile_reindex A S ((CompanionComputedInitial.cellOrder A).symm i) side).trans
      (by rw [Equiv.apply_symm_apply,copy_viewCount])
  simp_rw [←hp]
  symm
  unfold CompanionWeightOracle.factorialRatio CompanionWeightOracle.factorialNumerator
    CompanionWeightOracle.factorialDenominator
  simp only [Nat.cast_prod,Fintype.prod_prod_type,Fintype.prod_bool,Nat.cast_mul]
  rw [←Finset.prod_div_distrib]
  exact Fintype.prod_equiv (CompanionComputedInitial.cellOrder A) _ _ (fun s => by
    simp only [Equiv.symm_apply_apply,CompanionComputedInitial.capacities]
    ring)

end
end ContingencyTables.PairedFactorialProgram

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

lemma insert_fold (q : Fraction) (xs : List Fraction) :
    xs.reverse.foldl (fun s x => step (x,s)) (q,([],[q])) = (q,(xs,insertRaw q xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil]
    rfl

lemma insert_eq (q : Fraction) (xs : List Fraction) : insert (q,xs)=insertRaw q xs := by
  unfold insert
  rw [insert_fold]

lemma insert_pos (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) : ∀ y∈insertRaw q xs,0 < y.2 := by
  induction xs with
  | nil => simpa only [insertRaw,List.mem_singleton] using fun y hy => hy ▸ hq
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw]
    split <;> intro y hy <;> simp only [List.mem_cons] at hy
    · rcases hy with rfl|hy
      · exact hxx
      · exact ht y hy
    · rcases hy with rfl|rfl|hy
      · exact hq
      · exact hxx
      · exact hx y (by simp [hy])

lemma insert_map (q : Fraction) (xs : List Fraction) (hq : 0 < q.2)
    (hx : ∀ x∈xs,0 < x.2) :
    (insertRaw q xs).map val=(xs.map val).orderedInsert (·≤·) (val q) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    simp only [insertRaw,List.map_cons,List.orderedInsert_cons,TreeFraction.less_val x q hxx hq]
    by_cases h : val x < val q
    · simp [h,not_le.mpr h,ht]
    · simp [h,le_of_not_gt h]

lemma sort_cons (x : Fraction) (xs : List Fraction) : sort (x::xs)=insert (x,sort xs) := by
  simp only [sort,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma sort_pos (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) : ∀ y∈sort xs,0 < y.2 := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
    rw [sort_cons,insert_eq]
    exact insert_pos x (sort xs) (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))

lemma sort_map (xs : List Fraction) (hx : ∀ x∈xs,0 < x.2) :
    (sort xs).map val=(xs.map val).mergeSort (·≤·) := by
  rw [List.mergeSort_eq_insertionSort]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ y∈xs,0 < y.2 := fun y hy => hx y (by simp [hy])
    rw [sort_cons,insert_eq,insert_map x (sort xs) (hx x (by simp)) (sort_pos xs ht),ih ht]
    rfl

lemma median_val (xs : List Fraction) :
    val (median xs)=CommonBasesFPRAS.rationalMedian (xs.map val) := by
  have hs := sort_map (xs.map TreeFraction.normalize) (by
    intro y hy
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
    exact normalize_den_pos x)
  have hm : (xs.map TreeFraction.normalize).map val=xs.map val := by
    simp only [List.map_map,Function.comp_def,normalize_val]
  rw [hm] at hs
  unfold median CommonBasesFPRAS.rationalMedian
  rw [←hs,List.length_map]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (sort (xs.map TreeFraction.normalize))[xs.length/2]? <;> simp only [Option.getD_none,Option.map_none,Option.getD_some,Option.map_some,val, Nat.cast_zero,zero_div]

end ContingencyTables.MedianFractionProgram

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
lemma wordBits_eq (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    wordBits A h=binWordBits A h := by
  unfold wordBits binWordBits
  apply Fintype.sum_equiv (RootedCatalogGrid.coordinateEquiv A)
  intro i
  simp only [RootedCatalogGrid.coordinateEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply]

lemma draw_law (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) :
    mapLaw (uniformLaw (α := Words A h)) (draw A K hK hW v h)=
      approximateBinLaw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h := by
  have he := binWordDraw_law A K hK hW (RootedCatalogGrid.gridEquiv A K v) h
  unfold draw
  rw [←FairBits.map_equiv (reindexWords A h),FairBits.uniform_equiv]
  apply RationalLaw.ext
  funext f
  exact congrArg (fun p => p.mass f) he

theorem flatDraw_law (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (wordBits A h) → Bool)) (flatDraw A K hK hW v h)=
      approximateBinLaw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h := by
  unfold flatDraw
  rw [←FairBits.map_equiv (wordEquiv A h),FairBits.uniform_equiv,draw_law]

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixing of the executed catalog-order oracle walk -/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess
open CompanionOracleDensity (rationalHeight oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem walkLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) (N : ℕ) :
    FirstSuccess.walkLaw (bitStepLaw A C a z) v N=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK (gridEquiv A K v) N) := by
  induction N with
  | zero =>
    apply RationalLaw.ext
    funext w
    simp only [RootedOracleDensity.oracleWalkLaw,FirstSuccess.walkLaw,equivLaw,pointLaw,
      Equiv.symm_symm,Equiv.apply_eq_iff_eq]
  | succ N ih =>
    have hm (b : Grid (I := Fin (freeCount A)) K) :
        (FirstSuccess.walkLaw (bitStepLaw A C a z) v N).mass b=
          (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK
            (gridEquiv A K v) N).mass (gridEquiv A K b) :=
      congrArg (fun p => p.mass b) ih
    have hk (b w : Grid (I := Fin (freeCount A)) K) :
        (bitStepLaw A C a z b).mass w=
          (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK
            (gridEquiv A K b)).mass (gridEquiv A K w) :=
      congrArg (fun p => p.mass w) (bitStepLaw_eq A C a hC haH z hz hK hKB b)
    apply RationalLaw.ext
    funext w
    change (∑ b,(FirstSuccess.walkLaw (bitStepLaw A C a z) v N).mass b*
        (bitStepLaw A C a z b).mass w)=
      ∑ b,(RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK
        (gridEquiv A K v) N).mass b*
        (RootedOracleDensity.oracleTransitionLaw A (rowColumn A.T) C a z hK b).mass
          (gridEquiv A K w)
    simp_rw [hm,hk]
    exact Fintype.sum_equiv (gridEquiv A K) _ _ (fun _ => rfl)

theorem wordWalkLaw_eq (A : Instance (Fin m) (Fin n)) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1≤K) (hKB : (K:ℝ)≤CompanionOracleDensity.binWidth A C)
    (v : Grid (I := Fin (freeCount A)) K) (N : ℕ) :
    FirstSuccess.wordWalkLaw (bitStep A C a z) v N=
      equivLaw (gridEquiv A K).symm
        (RootedOracleDensity.oracleWalkLaw A (rowColumn A.T) C a z hK (gridEquiv A K v) N) := by
  rw [FirstSuccess.wordWalkLaw_eq]
  exact walkLaw_eq A C a hC haH z hz hK hKB v N

end
end ContingencyTables.RootedCatalogGrid

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

lemma flatGridWalk_law (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ) :
    mapLaw (uniformLaw (α := Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool))
      (flatGridWalk A C a z v N)=wordWalkLaw (RootedCatalogGrid.bitStep A C a z) v N := by
  unfold flatGridWalk
  rw [←FairBits.map_equiv (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C)),
    FairBits.uniform_equiv]
  rfl

end
end ContingencyTables.RootedOracleWalkProgram

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
private lemma bind_equiv {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (p : RationalLaw X) (e : X ≃ Y) (f : Y → RationalLaw Z) :
    bindLaw (equivLaw e p) f=bindLaw p (fun x => f (e x)) := by
  apply RationalLaw.ext
  funext z
  change (∑ y,p.mass (e.symm y)*(f y).mass z)=∑ x,p.mass x*(f (e x)).mass z
  symm
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Equiv.symm_apply_apply])

lemma integerDraw_law (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hKB : (K:ℝ) ≤ binWidth A C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ) :
    mapLaw (uniformLaw (α := Words A C N h)) (integerDraw A C a K hK hW z v N h)=
      RootedOracleDensity.sampledIntegerLaw A (RootedCompletion.rowColumn A.T) C a z K hK hW
        (RootedCatalogGrid.gridEquiv A K v) N h := by
  unfold integerDraw
  rw [←uniform_product]
  rw [mapLaw_product_finish
    (uniformLaw (α := Fin (N*oracleStepBits A C) → Bool))
    (uniformLaw (α := Fin (RootedBinDrawLaw.wordBits A h) → Bool))
    (RootedOracleWalkProgram.flatGridWalk A C a z v N)
    (fun w bits => RootedBinDrawLaw.flatDraw A K (by omega) hW w h bits)]
  rw [RootedOracleWalkProgram.flatGridWalk_law]
  have hb (w : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :=
    RootedBinDrawLaw.flatDraw_law A K (by omega) hW w h
  simp_rw [hb]
  rw [RootedCatalogGrid.wordWalkLaw_eq A C a hC haH z hz hK hKB]
  rw [bind_equiv]
  unfold RootedOracleDensity.sampledIntegerLaw
  rw [RootedOracleDensity.oracleBitWalkLaw_eq A (RootedCompletion.rowColumn A.T)
    C a hC haH z hz hK hKB]
  congr 1
  funext w
  simp only [Equiv.apply_symm_apply]

/-- Equality for arbitrary observables is exact equality in distribution
of the executed rational sample and the analysed correction sample. -/
theorem sample_average (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hKB : (K:ℝ) ≤ binWidth A C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z) (sigma : ℚ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ) (g : ℚ → ℝ) :
    uniformAverage (fun bits : Words A C N h => g (sample A C a K hK hW z sigma v N h bits))=
      uniformAverage (fun bits : Fin (oracleIntegerBits A C N h) → Bool =>
        g (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T) C a z K
          hK hW sigma (RootedCatalogGrid.gridEquiv A K v) N h bits)) := by
  let obs := fun f : FreeIndex A.small A.T A.b =>
    g (RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K
      (by omega) sigma f)
  have hleft := word_expectation (integerDraw A C a K hK hW z v N h) obs
  have hright := word_expectation
    (RootedOracleDensity.oracleIntegerDraw A (RootedCompletion.rowColumn A.T) C a z K hK hW
      (RootedCatalogGrid.gridEquiv A K v) N h) obs
  rw [integerDraw_law A C a K hC haH hK hW hKB z hz v N h] at hleft
  rw [RootedOracleDensity.oracleIntegerDraw_law] at hright
  exact hleft.trans hright.symm

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableTransport
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of finite experiments with rational outputs

Output values need not form a finite type. Equality against every real
observable is preserved by deterministic postprocessing and by the
independent arrays used in the counting estimator.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

lemma SameLaw.map {f : X → Z} {g : Y → Z} (h : SameLaw f g) (F : Z → W) :
    SameLaw (fun x => F (f x)) (fun y => F (g y)) := by
  intro phi
  exact h (fun z => phi (F z))

lemma SameLaw.prod {f : X → Z} {g : Y → Z} {a : U → W} {b : V → W}
    (hfg : SameLaw f g) (hab : SameLaw a b) :
    SameLaw (fun x : X×U => (f x.1,a x.2)) (fun y : Y×V => (g y.1,b y.2)) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hinner (x : X) :
      uniformAverage (fun u : U => phi (f x,a u))=
        uniformAverage (fun v : V => phi (f x,b v)) :=
    hab (fun w => phi (f x,w))
  simp_rw [hinner]
  exact hfg (fun z => uniformAverage (fun v : V => phi (z,b v)))

lemma SameLaw.independent {f : X → Z} {g : Y → Z} (h : SameLaw f g) (N : ℕ) :
    SameLaw (fun xs : Fin N → X => fun i => f (xs i))
      (fun ys : Fin N → Y => fun i => g (ys i)) := by
  intro phi
  exact uniformAverage_independent_eq f g h N phi

lemma indexed (N : ℕ) (f : Fin N → X → Z) (g : Fin N → Y → Z)
    (h : ∀ i,SameLaw (f i) (g i)) :
    SameLaw (fun xs : Fin N → X => fun i => f i (xs i))
      (fun ys : Fin N → Y => fun i => g i (ys i)) := by
  intro phi
  induction N with
  | zero =>
    have hf (xs : Fin 0 → X) : (fun i => f i (xs i))=(fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    have hg (ys : Fin 0 → Y) : (fun i => g i (ys i))=(fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    simp_rw [hf,hg,uniformAverage_const]
  | succ N ih =>
    have hf (x : X) (xs : Fin N → X) :
        (fun i => f i ((Fin.cons x xs : Fin (N+1) → X) i))=Fin.cons (f 0 x) (fun i => f i.succ (xs i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hg (y : Y) (ys : Fin N → Y) :
        (fun i => g i ((Fin.cons y ys : Fin (N+1) → Y) i))=Fin.cons (g 0 y) (fun i => g i.succ (ys i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp_rw [hf,hg]
    have htail (x : X) := ih (fun i => f i.succ) (fun i => g i.succ)
      (fun i => h i.succ) (fun zs => phi (Fin.cons (f 0 x) zs))
    simp_rw [htail]
    exact h 0 (fun z => uniformAverage (fun ys : Fin N → Y =>
      phi (Fin.cons z (fun i => g i.succ (ys i)))))

end
end ContingencyTables.FiniteObservableTransport

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

private lemma expectation_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : RationalLaw X) (f : Y → ℝ) :
    expectation (equivLaw e p) f=expectation p (fun x => f (e x)) := by
  unfold expectation equivLaw
  symm
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Equiv.symm_apply_apply])

theorem sameLaw (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ) :
    SameLaw (sample A C a z v N)
      (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T) C a z
        (RootedCatalogGrid.gridEquiv A K v) N) := by
  intro g
  let obs := fun w : Grid (I := Fin (dimension A)) K =>
    g (RootedOracleDensity.rationalRatioObservable A (RootedCompletion.rowColumn A.T) C a z w)
  have hl := word_expectation (RootedOracleWalkProgram.flatGridWalk A C a z v N)
    (fun w => obs (RootedCatalogGrid.gridEquiv A K w))
  rw [RootedOracleWalkProgram.flatGridWalk_law,
    RootedCatalogGrid.wordWalkLaw_eq A C a hC haH z hz hK hKB,expectation_equiv] at hl
  simp only [Equiv.apply_symm_apply] at hl
  have hr := word_expectation
    (wordWalk (RootedOracleDensity.oracleBitStep A (RootedCompletion.rowColumn A.T) C a z)
      (RootedCatalogGrid.gridEquiv A K v) N) obs
  change uniformAverage (fun bits => g (RootedOracleDensity.ratioSample A
    (RootedCompletion.rowColumn A.T) C a z (RootedCatalogGrid.gridEquiv A K v) N bits))=
      expectation (RootedOracleDensity.oracleBitWalkLaw A (RootedCompletion.rowColumn A.T)
        C a z (RootedCatalogGrid.gridEquiv A K v) N) obs at hr
  rw [RootedOracleDensity.oracleBitWalkLaw_eq A (RootedCompletion.rowColumn A.T)
    C a hC haH z hz hK hKB] at hr
  exact hl.trans hr.symm

end
end ContingencyTables.RootedRatioSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComputedEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed blocks have the complete estimator law

Only the physical sample programs differ from the original enumeration.
Exact independent-observable transport identifies their whole product
estimator, including every event used by the confidence proof.
-/

namespace ContingencyTables.RootedComputedEstimator

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

private lemma ratioAverage_law (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (a : Fin j) :
    SameLaw (ratioAverage A C K j a.val delta failure z v)
      (fun draws : CompanionOracleDensity.RatioBlock A C K j delta failure =>
        rationalAverage (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T)
          C a.val z (RootedCatalogGrid.gridEquiv A K v) (oracleTime A C K 1 delta))
            (sampleCount j delta failure) draws) := by
  have hsample := RootedRatioSampleLaw.sameLaw A C a.val K hC
    (show a.val ≤ rationalHeight A C from Nat.le_trans (Nat.le_of_lt a.isLt) hj)
    hK hB.le z hz v (oracleTime A C K 1 delta)
  exact (hsample.independent (sampleCount j delta failure)).map
    (fun qs : Fin (sampleCount j delta failure) → ℚ => (∑ i,qs i)/sampleCount j delta failure)

private lemma correctionAverage_law (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    SameLaw (correctionAverage A C K j hK hW delta failure z v)
      (fun draws : CompanionOracleDensity.CorrectionBlock A C K j delta failure =>
        rationalAverage (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T)
          C j z K hK hW (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
          (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
            (sampleCount j delta failure) draws) := by
  have hsample : SameLaw
      (RootedCorrectionSampleLaw.sample A C j K hK hW z (roundingTolerance delta) v
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T) C j z K hK hW
        (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) :=
    RootedCorrectionSampleLaw.sample_average A C j K hC hj hK hW hB.le z hz
      (roundingTolerance delta) v _ _
  exact (hsample.independent (sampleCount j delta failure)).map
    (fun qs : Fin (sampleCount j delta failure) → ℚ => (∑ i,qs i)/sampleCount j delta failure)

/-- Exact equality of the whole rational estimator law; no extra oracle
or confidence hypothesis is introduced at the implementation boundary. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (delta failure : ℚ)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    SameLaw (estimate A C K j hK hW delta failure z v)
      (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
        delta failure (RootedCatalogGrid.gridEquiv A K v)) := by
  let originalRatio := fun (a : Fin j) (draws : CompanionOracleDensity.RatioBlock A C K j delta failure) =>
    rationalAverage (RootedOracleDensity.ratioSample A (RootedCompletion.rowColumn A.T) C a.val z
      (RootedCatalogGrid.gridEquiv A K v) (oracleTime A C K 1 delta))
      (sampleCount j delta failure) draws
  let originalCorrection := fun draws : CompanionOracleDensity.CorrectionBlock A C K j delta failure =>
    rationalAverage (RootedOracleDensity.correctionSample A (RootedCompletion.rowColumn A.T)
      C j z K hK hW (roundingTolerance delta) (RootedCatalogGrid.gridEquiv A K v)
      (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (sampleCount j delta failure) draws
  have hr := FiniteObservableTransport.indexed j
    (fun a : Fin j => ratioAverage A C K j a.val delta failure z v) originalRatio
    (fun a => ratioAverage_law A C K j hC hj hK hB delta failure z hz v a)
  have hc := correctionAverage_law A C K j hC hj hK hW hB delta failure z hz v
  have ht := (hr.prod hc).map (fun p : (Fin j → ℚ)×ℚ => (assignmentCount A:ℚ)*(∏ a,p.1 a)*p.2)
  have ho (draws : EstimatorInput A C K j delta failure) :
      (assignmentCount A:ℚ)*(∏ a,originalRatio a (draws.1 a))*originalCorrection draws.2=
        RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
          delta failure (RootedCatalogGrid.gridEquiv A K v) draws := by
    rw [RootedOracleDensity.estimateValue,Fintype.prod_option]
    simp only [RootedOracleDensity.observedFactor,originalRatio,originalCorrection]
    ring
  intro phi
  have hh := ht phi
  change uniformAverage (fun draws : Inputs A C K j delta failure =>
      phi (estimate A C K j hK hW delta failure z v draws)) =
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      phi ((assignmentCount A:ℚ)*(∏ a,originalRatio a (draws.1 a))*
        originalCorrection draws.2)) at hh
  exact hh.trans (congrArg uniformAverage (funext (fun draws => congrArg phi (ho draws))))

end
end ContingencyTables.RootedComputedEstimator

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

lemma scheduledWordWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    wordWidth (scheduledContext A C K j delta failure z v)=
      estimatorWordBits A C K j delta failure := by
  change j*(sampleCount j delta failure*ratioWidth
    (scheduledContext A C K j delta failure z v))+
    sampleCount j delta failure*(correctionWalkWidth
      (scheduledContext A C K j delta failure z v)+
        RootedEstimatorLayoutProgram.binWidth (scheduledContext A C K j delta failure z v))=_
  simp only [scheduledContext,ratioWidth_data,correctionWalkWidth_data,binWidth_data,
    RootedBinDrawLaw.wordBits_eq,estimatorWordBits,oracleIntegerBits]

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

theorem scheduledWidth_positive (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hK : 1 ≤ K) (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    0 < wordWidth (scheduledContext A C K j delta failure z v) := by
  have hdelta : (0:ℝ) < delta := by exact_mod_cast hd
  have htime := oracleTime_positive A C K hC hK (correctionTheta delta)
    (by unfold correctionTheta; positivity)
  have hstep := RootedOracleWalkProgram.stepWidth_pos A C hC
  have hs := sampleCount_positive j delta failure hd hf
  have ht : 0 < correctionWalkWidth (scheduledContext A C K j delta failure z v) := by
    rw [scheduledContext,correctionWalkWidth_data]
    exact Nat.mul_pos htime hstep
  have hc : 0 < correctionWidth (scheduledContext A C K j delta failure z v) := by
    unfold correctionWidth
    omega
  have hp := Nat.mul_pos hs hc
  change 0 < _ + sampleCount j delta failure*
    correctionWidth (scheduledContext A C K j delta failure z v)
  omega

theorem sameLaw_estimateValue (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta)) :
    FiniteObservableTransport.SameLaw
      (fun bits => TreeFraction.val (output (input
        (scheduledContext A C K j delta failure z v) (degree,depth) bits)))
      (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T) C z K hK hW j
        delta failure (RootedCatalogGrid.gridEquiv A K v)) := by
  intro phi
  let test := fun draws : RootedComputedEstimator.Inputs A C K j delta failure =>
    phi (RootedComputedEstimator.estimate A C K j hK hW delta failure z v draws)
  have hp := output_scheduled A C K j hC hj hK hW hB delta failure hd hf z hz v
    degree depth hdegree hdepth
  have he := uniformAverage_equiv (scheduledEquiv A C K j delta failure z v) test
  have ho : uniformAverage (fun bits => phi (TreeFraction.val (output (input
      (scheduledContext A C K j delta failure z v) (degree,depth) bits))))=
      uniformAverage (fun bits => test (scheduledEquiv A C K j delta failure z v bits)) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hp bits)
  exact ho.trans (he.trans (RootedComputedEstimator.sameLaw A C K j hC hj hK hW hB
    delta failure z hz v phi))

theorem sameLaw_word (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon failure : ℚ) (he : 0 < epsilon) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance epsilon j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance epsilon j))) :
    FiniteObservableTransport.SameLaw
      (fun bits => TreeFraction.val (output (input
        (scheduledContext A C K j (innerTolerance epsilon j) failure z v) (degree,depth) bits)))
      (RootedOracleDensity.wordEstimate A (RootedCompletion.rowColumn A.T) C z K hK hW j
        epsilon failure (RootedCatalogGrid.gridEquiv A K v)) := by
  intro phi
  have hs := sameLaw_estimateValue A C K j hC hj hK hW hB (innerTolerance epsilon j)
    failure (innerTolerance_pos epsilon j he) hf z hz v degree depth hdegree hdepth phi
  have he := uniformAverage_equiv (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure)
    (fun draws => phi (RootedOracleDensity.estimateValue A (RootedCompletion.rowColumn A.T)
      C z K hK hW j (innerTolerance epsilon j) failure (RootedCatalogGrid.gridEquiv A K v) draws))
  exact hs.trans he.symm

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing independent complete estimators and their rational median -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

attribute [local irreducible] samples

open GridBoundary CommonBasesFPRAS
open scoped Classical

theorem output_ofFn (c : Context) (R : ℕ) (hw : 0 < wordWidth c)
    (markers : List Bool×List Bool) (bits : Fin (R*wordWidth c) → Bool) :
    TreeFraction.val (output ((c,R),(markers,List.ofFn bits)))=
      rationalMedian (List.ofFn (fun i : Fin R => TreeFraction.val
        (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input c markers
          (gridWordEquiv R (wordWidth c) bits i))))) := by
  rw [output,MedianFractionProgram.median_val]
  have hwords : words ((c,R),(markers,List.ofFn bits))=
      List.ofFn (fun i : Fin R => List.ofFn (gridWordEquiv R (wordWidth c) bits i)) := by
    change (wordChunks (wordWidth c,List.ofFn bits)).take R=_
    rw [wordChunks_ofFn hw]
    exact List.take_of_length_le (by simp)
  unfold samples
  rw [hwords]
  simp only [List.map_ofFn]
  rfl

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed inner median is the analysed amplified weight oracle -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open FiniteObservableTransport
open scoped Classical

noncomputable section
variable {m n : ℕ}

/-- Exact observable transport, including the outputs on inaccurate
sample histories, lets the original median analysis apply unchanged. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon delta : ℚ) (he : 0 < epsilon)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance (epsilon/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance (epsilon/2) j))) :
    SameLaw (value A C K j epsilon delta z v degree depth)
      (RootedOracleDensity.medianEstimate A (RootedCompletion.rowColumn A.T) C z K hK hW j
        epsilon delta (RootedCatalogGrid.gridEquiv A K v)) := by
  have heh : 0 < epsilon/2 := by positivity
  have hs := RootedEstimatorWordProgram.sameLaw_word A C K j hC hj hK hW hB
    (epsilon/2) 1 heh (by norm_num) z hz v degree depth hdegree hdepth
  have hp := (hs.independent (repetitionCount delta)).map
    (fun qs : Fin (repetitionCount delta) → ℚ => rationalMedian (List.ofFn qs))
  have hw := RootedEstimatorWordProgram.scheduledWidth_positive A C K j hC hK
    (innerTolerance (epsilon/2) j) 1 (innerTolerance_pos (epsilon/2) j heh)
      (by norm_num) z v
  intro phi
  have hleft := uniformAverage_equiv
    (gridWordEquiv (repetitionCount delta) (wordWidth (context A C K j epsilon z v)))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => TreeFraction.val
      (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input
        (context A C K j epsilon z v) (degree,depth) (xs i)))))))
  have hright := uniformAverage_equiv
    (oracleWalkWordEquiv (repetitionCount delta)
      (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1))
    (fun xs => phi (rationalMedian (List.ofFn (fun i => RootedOracleDensity.wordEstimate A
      (RootedCompletion.rowColumn A.T) C z K hK hW j (epsilon/2) 1
        (RootedCatalogGrid.gridEquiv A K v) (xs i)))))
  have hout : uniformAverage (fun bits => phi (value A C K j epsilon delta z v degree depth bits))=
      uniformAverage (fun bits => phi (rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
        TreeFraction.val (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input
          (context A C K j epsilon z v) (degree,depth)
            (gridWordEquiv (repetitionCount delta) (wordWidth (context A C K j epsilon z v)) bits i))))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (output_ofFn (context A C K j epsilon z v) (repetitionCount delta)
      hw (degree,depth) bits)
  exact hout.trans (hleft.trans ((hp phi).trans hright.symm))

end
end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLabelWeightProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weight oracle at a current paired state

The immutable schedule and graph are shared. Each call reconstructs the
two small-cell views from its actual state, runs the independent median
estimator, and multiplies by the exact factorial ratio.
-/

namespace ContingencyTables.RootedLabelWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open RootedEstimatorLayoutProgram

attribute [local irreducible] medianInput factorialInput

attribute [local irreducible] medianResult factorialResult

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal GridBoundary
open CompanionOracleDensity FiniteObservableTransport CommonBasesFPRAS
open scoped Classical
variable {m n : ℕ}

lemma replaceState_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (S : Set (Labels A × Bool)) :
    replaceState (RootedOracleWalkProgram.data A C a K z v,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
        RootedOracleWalkProgram.data A C a K (CompanionWeightOracle.profile A S) v := by
  unfold replaceState RootedOracleWalkProgram.data
  rw [PairedDemandProgram.output_data]

lemma context_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth bits : List Bool) (S : Set (Labels A × Bool)) :
    context (config A C K j epsilon delta z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,bits))=
        RootedEstimatorMedianProgram.context A C K j epsilon (CompanionWeightOracle.profile A S) v := by
  unfold context stateInput config RootedEstimatorMedianProgram.context
    RootedEstimatorWordProgram.scheduledContext RootedEstimatorLayoutProgram.data
  rw [replaceState_data]

lemma output_value (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (S : Set (Labels A × Bool))
    (bits : Fin (repetitionCount delta*wordWidth
      (RootedEstimatorMedianProgram.context A C K j epsilon (CompanionWeightOracle.profile A S) v)) → Bool) :
    TreeFraction.val (output (config A C K j epsilon delta z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits)))=
      RootedEstimatorMedianProgram.value A C K j epsilon delta
        (CompanionWeightOracle.profile A S) v degree depth bits * CompanionWeightOracle.factorialRatio A S := by
  rw [output,TreeFraction.mul_val]
  unfold medianResult factorialResult
  have hf : factorialInput (config A C K j epsilon delta z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits))=
        (List.ofFn (CompanionComputedInitial.capacities A),
          encodeSet (CompanionComputedInitial.coordinateOrder A) S) := by
    unfold factorialInput demandInput stateInput config RootedEstimatorMedianProgram.context
      RootedEstimatorWordProgram.scheduledContext RootedEstimatorLayoutProgram.data
      RootedOracleWalkProgram.data
    rw [PairedDemandProgram.cells_data,CompanionCellCatalog.capacities_eq]
    rfl
  rw [hf,PairedFactorialProgram.output_physical]
  apply congrArg (fun q : ℚ => q*CompanionWeightOracle.factorialRatio A S)
  unfold medianInput
  rw [context_data]
  rfl

theorem sameLaw_weight (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (S : Set (Labels A × Bool)) :
    SameLaw (fun bits : Fin (repetitionCount xi*wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool =>
      TreeFraction.val (output (config A C K j xi xi z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits))))
      (RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T) C K hK hW j xi
        (RootedCatalogGrid.gridEquiv A K v) S) := by
  have h := (RootedEstimatorMedianProgram.sameLaw A C K j hC hj hK hW hB xi xi hxi
    (CompanionWeightOracle.profile A S) (CompanionWeightOracle.profile_inBox A S)
    v degree depth hdegree hdepth).map (fun q => q*CompanionWeightOracle.factorialRatio A S)
  intro phi
  have hl : (fun bits : Fin (repetitionCount xi*wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool =>
      phi (TreeFraction.val (output (config A C K j xi xi z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits)))))=
      (fun bits => phi (RootedEstimatorMedianProgram.value A C K j xi xi
        (CompanionWeightOracle.profile A S) v degree depth bits*CompanionWeightOracle.factorialRatio A S)) := by
    funext bits
    rw [output_value]
  rw [hl]
  exact h phi

end
end ContingencyTables.RootedLabelWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEvaluatedWeightProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed multiplier times labelled weight

Both factors are computed from the supplied current state. The matrix
lookup and the oracle consume no hidden finite-state enumeration.
-/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

attribute [local irreducible] weightInput RootedLabelWeightProgram.output

attribute [local irreducible] multiplier weight

attribute [local irreducible] output

noncomputable section
open CompanionRationalUpdates
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal GridBoundary CompanionOracleDensity CommonBasesFPRAS TwoLiftStates
open FiniteObservableTransport
open scoped Classical
variable {m n : ℕ}

lemma multiplier_code (A : Instance (Fin m) (Fin n))
    (cfg : RootedLabelWeightProgram.Config) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool)) (bits : List Bool) :
    TreeFraction.val (multiplier (((cfg,matrixCode w),encodeSet (coordinateOrder A) S),bits))=
      CommonBasesFPRAS.rationalMultiplier pairs (sourceWeights A w) S := by
  unfold multiplier multiplierInput
  rw [CompanionComputedProposal.generated_catalog]
  exact CompanionStateMultiplierProgram.output_code A (pairLabels A) (coordinateOrder A) S w

/-- Arbitrary observables of the executed weighted query agree with the
proved mathematical oracle, including outcomes on its failure event. -/
theorem sameLaw_evaluated (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A × Bool)) :
    SameLaw (fun bits : Fin (repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool =>
      TreeFraction.val (output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),List.ofFn bits)))
      (RootedOracleAcceptance.evaluatedWeight A (RootedCompletion.rowColumn A.T) C K j hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S) := by
  have hw := RootedLabelWeightProgram.sameLaw_weight A C K j hC hj hK hW hB xi hxi z v
    degree depth hdegree hdepth S
  intro phi
  have he (bits : Fin (repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool) :
      TreeFraction.val (output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),List.ofFn bits))=
      CommonBasesFPRAS.rationalMultiplier pairs (sourceWeights A w) S *
        TreeFraction.val (RootedLabelWeightProgram.output
          (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
            (encodeSet (coordinateOrder A) S,List.ofFn bits))) := by
    rw [output,TreeFraction.mul_val,multiplier_code]
    unfold weight weightInput
    rfl
  simp_rw [he]
  exact hw (fun q => phi (CommonBasesFPRAS.rationalMultiplier pairs (sourceWeights A w) S*q))

end
end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionMetropolisProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped rational Metropolis acceptance as a binary program -/

namespace ContingencyTables.FractionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

attribute [local irreducible] probability

lemma probability_value (x y : TreeFraction.Fraction) (bits : List Bool) :
    TreeFraction.val (probability ((x,y),bits))=min 1 (TreeFraction.val y/TreeFraction.val x) := by
  have hd : 0 < (ratio ((x,y),bits)).2 := TreeFraction.normalize_den_pos _
  have hr : TreeFraction.val (ratio ((x,y),bits))=TreeFraction.val y/TreeFraction.val x :=
    TreeFraction.div_val y x
  unfold probability belowOne
  rw [TreeFraction.less_val _ _ hd (by decide)]
  have hone : TreeFraction.val (1,1)=(1:ℚ) := by norm_num [TreeFraction.val]
  rw [hone]
  by_cases h : TreeFraction.val (ratio ((x,y),bits)) < 1
  · simp only [h,decide_true,ite_true, if_true]
    rw [hr]
    exact (min_eq_right (by simpa only [hr] using h.le)).symm
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,hone]
    exact (min_eq_left (by simpa only [hr] using le_of_not_gt h)).symm

lemma accept_ofFn (x y : TreeFraction.Fraction) (B : ℕ) (bits : Fin B → Bool) :
    accept ((x,y),List.ofFn bits)=
      decide (FairBits.rationalThresholdAccept B (min 1 (TreeFraction.val y/TreeFraction.val x)) bits) := by
  rw [accept,FractionAcceptanceProgram.acceptCode_ofFn,probability_value]

noncomputable section
open FiniteObservableTransport
open scoped Classical

/-- Independent exact observable laws suffice for the implemented coin;
no finite type of rational weight values is required. -/
theorem sameLaw_accept {X Y U V : Type*} [Fintype X] [Fintype Y] [Fintype U] [Fintype V]
    (current : X → TreeFraction.Fraction) (target : U → TreeFraction.Fraction)
    (f : Y → ℚ) (g : V → ℚ)
    (hf : SameLaw (fun x => TreeFraction.val (current x)) f)
    (hg : SameLaw (fun u => TreeFraction.val (target u)) g) (B : ℕ) :
    SameLaw (fun z : (X × U) × (Fin B → Bool) =>
      accept ((current z.1.1,target z.1.2),List.ofFn z.2))
      (fun z : (Y × V) × (Fin B → Bool) =>
        decide (FairBits.rationalThresholdAccept B (min 1 (g z.1.2/f z.1.1)) z.2)) := by
  have hid : SameLaw (fun x : Fin B → Bool => x) (fun x : Fin B → Bool => x) := fun _ => rfl
  have hs := (hf.prod hg).prod hid
  intro phi
  simp_rw [accept_ofFn]
  exact hs (fun z => phi (decide (FairBits.rationalThresholdAccept B (min 1 (z.1.2/z.1.1)) z.2)))

end

end ContingencyTables.FractionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma capView_weight (q U : ℕ) (xs : List ℕ) :
    weight (capView ((q,U),xs))≤q*(4*U.size+2)+1 := by
  have hw := weight_map_bound (f := fun a => min a U) (as := xs.take q) (N := 4*U.size+1)
    (fun a _ => (weight_nat_le _).trans (by
      have hs := Nat.size_le_size (min_le_right a U)
      omega))
  change weight (capView ((q,U),xs))≤(xs.take q).length*(4*U.size+2)+1 at hw
  exact hw.trans (by
    have hl : (xs.take q).length≤q := by simp only [List.length_take]; exact min_le_left _ _
    gcongr)

lemma capView_eq (q U : ℕ) (xs : List ℕ) (hq : xs.length=q)
    (hU : ∀ a∈xs,a≤U) : capView ((q,U),xs)=xs := by
  unfold capView
  rw [←hq,List.take_length]
  calc
    xs.map (fun a => min a U)=xs.map id := List.map_congr_left (fun a ha => min_eq_left (hU a ha))
    _ = xs := List.map_id xs

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableReindex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-observable transports at word and law boundaries -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped Classical
noncomputable section

lemma SameLaw.word_length {a b : ℕ} (h : a=b) {Y Z : Type*} [Fintype Y]
    (f : List Bool → Z) (g : Y → Z)
    (hf : SameLaw (fun xs : Fin a → Bool => f (List.ofFn xs)) g) :
    SameLaw (fun xs : Fin b → Bool => f (List.ofFn xs)) g := by
  cases h
  exact hf

lemma SameLaw.of_mapLaw_eq {X Y Z : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] [Fintype Z] [DecidableEq Z]
    (f : X → Z) (g : Y → Z)
    (h : mapLaw (uniformLaw (α := X)) f=mapLaw (uniformLaw (α := Y)) g) :
    SameLaw f g := by
  intro phi
  rw [FiniteLawMoments.word_expectation,FiniteLawMoments.word_expectation,h]

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEvaluatedWeightLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-width laws for the two physical Metropolis weight calls -/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionMultiplierMatrixProgram GridBoundary CommonBasesFPRAS FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma queryWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi z v)=medianEstimatorBits A C K j xi xi := by
  rw [RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  rfl

theorem sameLaw_fixed (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A × Bool)) :
    SameLaw (fun bits : WeightWord A C K j xi =>
      TreeFraction.val (output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),List.ofFn bits)))
      (RootedOracleAcceptance.evaluatedWeight A (RootedCompletion.rowColumn A.T) C K j hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S) := by
  exact SameLaw.word_length (queryWidth A C K j xi (CompanionWeightOracle.profile A S) v)
    (fun bs => TreeFraction.val (output
      (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),bs))) _
    (sameLaw_evaluated A C K j hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S)

theorem acceptance_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S T : Set (Labels A × Bool)) :
    SameLaw (fun b : (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool) =>
      FractionMetropolisProgram.accept
        ((output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
              encodeSet (coordinateOrder A) S),List.ofFn b.1.1),
          output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
              encodeSet (coordinateOrder A) T),List.ofFn b.1.2)),List.ofFn b.2))
      (fun b : (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool) =>
        decide (FairBits.rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A (RootedCompletion.rowColumn A.T) C K j hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S T b.1) b.2)) := by
  exact FractionMetropolisProgram.sameLaw_accept _ _ _ _
    (sameLaw_fixed A C K j hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S)
    (sameLaw_fixed A C K j hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w T) k

end
end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteAdaptiveObservable
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observable laws under adaptive finite-word calls

The stored state may include rational estimates and is not assumed
finite. Each fresh word is finite; equality of every conditional call
therefore suffices for equality of the entire executed history.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section

variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

theorem SameLaw.bind {f : X → Z} {g : Y → Z} (hfg : SameLaw f g)
    (F : Z → U → W) (G : Z → V → W) (h : ∀ z,SameLaw (F z) (G z)) :
    SameLaw (fun xu : X × U => F (f xu.1) xu.2)
      (fun yv : Y × V => G (g yv.1) yv.2) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hi (x : X) := h (f x) phi
  simp_rw [hi]
  exact hfg (fun z => uniformAverage (fun v : V => phi (G z v)))

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteMetropolisTransport
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact observable transport of optional proposals and acceptance -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical
noncomputable section

variable {X P Q U V : Type*} [Fintype P] [Fintype Q] [Fintype U] [Fintype V]

/-- The proposed state and fresh acceptance experiment can both be
replaced by experiments with the same observable law. -/
theorem proposedMove_sameLaw (start : X) (pick : P → Option X) (pick' : Q → Option X)
    (accept : X → U → Bool) (accept' : X → V → Bool)
    (hp : SameLaw pick pick') (ha : ∀ next,SameLaw (accept next) (accept' next)) :
    SameLaw (fun z : P × U => proposedMove start (pick z.1) accept z.2)
      (fun z : Q × V => proposedMove start (pick' z.1) accept' z.2) := by
  apply hp.bind (fun o u => proposedMove start o accept u)
    (fun o v => proposedMove start o accept' v)
  intro o
  cases o with
  | none => exact (ha start).map (fun _ : Bool => start)
  | some next => exact (ha next).map (fun flag : Bool => if flag then next else start)

/-- An independent holding flag is preserved by the replacement. -/
theorem holding_sameLaw {A B : Type*} [Fintype A] [Fintype B]
    (start : X) (f : A → X) (g : B → X) (h : SameLaw f g) :
    SameLaw (fun z : (Fin 1 → Bool) × A => if z.1 0 then start else f z.2)
      (fun z : (Fin 1 → Bool) × B => if z.1 0 then start else g z.2) := by
  have hid : SameLaw (fun b : Fin 1 → Bool => b 0) (fun b : Fin 1 → Bool => b 0) := fun _ => rfl
  exact (hid.prod h).map (fun z : Bool × X => if z.1 then start else z.2)

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual computed proposal and two oracle calls have the phase law -/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionBooleanPhase (State)
open CompanionArithmeticProposal CompanionOrderedProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma output_programInput (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (cfg : RootedLabelWeightProgram.Config)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : State A) (b : Fields A C K j k xi) :
    output (programInput A C K j k xi cfg w S b)=
      encodeSet (coordinateOrder A)
        (if b.1 0 then S else proposedMove S (orderedProposal A (coordinateOrder A) S b.2.1)
          (codeAccept A C K j k xi cfg w S) b.2.2).val := by
  cases hb : b.1 0 with
  | true => simp only [output,programInput,hb,ite_true, if_true]
  | false =>
    cases hp : orderedProposal A (coordinateOrder A) S b.2.1 with
    | none =>
      simp only [output,programInput,hb,Bool.false_eq_true,ite_false,accepted,acceptanceInput,
        currentValue,targetValue,currentInput,targetInput,candidate,proposed,
        CompanionComputedProposal.proposalProgram_eq,hp,Option.map_none,Option.getD_none,proposedMove]
      split_ifs <;> simp_all
    | some T =>
      simp only [output,programInput,hb,Bool.false_eq_true,ite_false,accepted,acceptanceInput,
        currentValue,targetValue,currentInput,targetInput,candidate,proposed,
        CompanionComputedProposal.proposalProgram_eq,hp,Option.map_some,Option.getD_some,proposedMove,
        codeAccept]
      split_ifs <;> simp_all

/-- Every computed step has the complete reference phase-step law. The
proposal and both query outcomes are transported, including failures. -/
theorem sameLaw_fields (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : State A) :
    SameLaw (fun b : Fields A C K j k xi => output (programInput A C K j k xi
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S b))
      (fun b : Fields A C K j k xi => encodeSet (coordinateOrder A)
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S
            ((CompanionBooleanPhase.stepWordEquiv A C K j k xi).symm b)).val) := by
  let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
  let refAccept := fun T : State A => fun b :
      (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool) =>
    decide (FairBits.rationalThresholdAccept k
      (RootedOracleAcceptance.acceptance A (RootedCompletion.rowColumn A.T) C K j hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S.val T.val b.1) b.2)
  have hp : SameLaw (orderedProposal A (coordinateOrder A) S) (CompanionBooleanPhase.proposal A S) :=
    SameLaw.of_mapLaw_eq _ _ (orderedProposal_law A (coordinateOrder A) S)
  have ha (T : State A) : SameLaw (codeAccept A C K j k xi cfg w S T) (refAccept T) :=
    acceptance_sameLaw A C K j k hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S.val T.val
  have hm := proposedMove_sameLaw S _ _ _ _ hp ha
  have hh := (holding_sameLaw S _ _ hm).map (fun T : State A => encodeSet (coordinateOrder A) T.val)
  intro phi
  have hleft : (fun b : Fields A C K j k xi => phi (output (programInput A C K j k xi cfg w S b)))=
      (fun b : Fields A C K j k xi => phi (encodeSet (coordinateOrder A)
        (if b.1 0 then S else proposedMove S (orderedProposal A (coordinateOrder A) S b.2.1)
          (codeAccept A C K j k xi cfg w S) b.2.2).val)) := by
    funext b
    rw [output_programInput]
  rw [hleft]
  have he := hh phi
  refine he.trans ?_
  apply congrArg uniformAverage
  funext b
  apply congrArg phi
  unfold RootedBooleanPhase.step
  dsimp only
  simp only [Equiv.apply_symm_apply]
  cases hb : b.1 0 <;> cases hp : CompanionBooleanPhase.proposal A S b.2.1
  all_goals simp only [proposedMove,Bool.false_eq_true,ite_false,ite_true, if_true,refAccept,
    decide_eq_true_eq]

end
end ContingencyTables.CompanionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bounded list slices of a finite Boolean word -/

namespace ContingencyTables.FiniteWordSlices

open FairBits

lemma slice_ofFn {N : ℕ} (bits : Fin N → Bool) (start count : ℕ)
    (h : start+count ≤ N) :
    ((List.ofFn bits).drop start).take count=
      List.ofFn (fun i : Fin count => bits ⟨start+i.val,by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]

lemma first_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop 1).take p=List.ofFn (split p q k bits).2.1 := by
  rw [slice_ofFn bits 1 p (by omega)]
  apply congrArg List.ofFn
  funext i
  rfl

lemma current_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop (1+p)).take q=List.ofFn (split p q k bits).2.2.1.1 := by
  rw [slice_ofFn bits (1+p) q (by omega)]
  apply congrArg List.ofFn
  funext i
  apply congrArg bits
  apply Fin.ext
  change 1+p+i.val=1+(p+i.val)
  omega

lemma target_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop (1+p+q)).take q=List.ofFn (split p q k bits).2.2.1.2 := by
  rw [slice_ofFn bits (1+p+q) q (by omega)]
  apply congrArg List.ofFn
  funext i
  apply congrArg bits
  apply Fin.ext
  change 1+p+q+i.val=1+(p+(q+i.val))
  omega

lemma coin_slice (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    ((List.ofFn bits).drop (1+p+q+q)).take k=List.ofFn (split p q k bits).2.2.2 := by
  rw [slice_ofFn bits (1+p+q+q) k (by omega)]
  apply congrArg List.ofFn
  funext i
  apply congrArg bits
  apply Fin.ext
  change 1+p+q+q+i.val=1+(p+((q+q)+i.val))
  omega

lemma holding_bit (p q k : ℕ) (bits : Fin (1+(p+((q+q)+k))) → Bool) :
    (List.ofFn bits).getD 0 false=(split p q k bits).1 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp only [show 0 < 1+(p+((q+q)+k)) by omega,dite_true,Option.getD_some]
  rfl

end ContingencyTables.FiniteWordSlices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisWordSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The flat physical transition has the proved phase-step law -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma fields_ofFn (frame : CompanionMetropolisProgram.Frame) (k p q : ℕ) (code : List ℕ)
    (bits : Fin (1+(p+((q+q)+k))) → Bool)
    (hp : proposalWidth (packed frame k code (List.ofFn bits))=p)
    (hq : queryWidth (packed frame k code (List.ofFn bits))=q) :
    fields (packed frame k code (List.ofFn bits))=
      ((FiniteWordSlices.split p q k bits).1 0,
        (List.ofFn (FiniteWordSlices.split p q k bits).2.1,
          ((List.ofFn (FiniteWordSlices.split p q k bits).2.2.1.1,
            List.ofFn (FiniteWordSlices.split p q k bits).2.2.1.2),
            List.ofFn (FiniteWordSlices.split p q k bits).2.2.2))) := by
  let inp := packed frame k code (List.ofFn bits)
  change ((List.ofFn bits).getD 0 false,
    (((List.ofFn bits).drop 1).take (proposalWidth inp),
      ((((List.ofFn bits).drop (1+proposalWidth inp)).take (queryWidth inp),
        ((List.ofFn bits).drop (1+proposalWidth inp+queryWidth inp)).take (queryWidth inp)),
        ((List.ofFn bits).drop (1+proposalWidth inp+queryWidth inp+queryWidth inp)).take k)))=_
  change proposalWidth inp=p at hp
  change queryWidth inp=q at hq
  rw [hp,hq,FiniteWordSlices.holding_bit,FiniteWordSlices.first_slice,
    FiniteWordSlices.current_slice,FiniteWordSlices.target_slice,FiniteWordSlices.coin_slice]

lemma proposalWidth_code (A : Instance (Fin m) (Fin n))
    (frame : CompanionMetropolisProgram.Frame) (k : ℕ) (S : Set (Labels A × Bool)) (bits : List Bool) :
    proposalWidth (packed frame k (encodeSet (coordinateOrder A) S) bits)=
      CompanionBooleanPhase.proposalBits A := by
  have hc := Fintype.card_congr (coordinateOrder A)
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hc
  have hd : (CanonicalInitialEncoding.pairOrder (capacities A)).length/2=Fintype.card (Labels A) := by omega
  simp only [proposalWidth,packed,encodeSet,List.length_ofFn,hd,CompanionBooleanPhase.proposalBits]

lemma queryWidth_config (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : FractionMatrix) (code : List ℕ) (bits : List Bool) :
    queryWidth (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,w) k code bits)=
      medianEstimatorBits A C K j xi xi := by
  exact CompanionEvaluatedWeightProgram.queryWidth A C K j xi z v

lemma output_ofFn (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : State A) (bits : Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) :
    output (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))=
      CompanionMetropolisProgram.output (CompanionMetropolisProgram.programInput A C K j k xi
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S
        (CompanionBooleanPhase.stepWordEquiv A C K j k xi bits)) := by
  have hf := fields_ofFn
    (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w) k
    (CompanionBooleanPhase.proposalBits A) (medianEstimatorBits A C K j xi xi)
    (encodeSet (coordinateOrder A) S.val) bits
    (proposalWidth_code A _ k S.val _) (queryWidth_config A C K j k xi z v degree depth _ _ _)
  have hi : stepInput (packed
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))=
      CompanionMetropolisProgram.programInput A C K j k xi
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S
        (CompanionBooleanPhase.stepWordEquiv A C K j k xi bits) := by
    exact congrArg (fun fs =>
      (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S.val),fs)) hf
  exact congrArg CompanionMetropolisProgram.output hi

/-- The actual polynomial flat-step implementation has exactly the
reference kernel used by the trajectory and return estimates. -/
theorem sameLaw_flat (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : State A) :
    SameLaw (fun bits : Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      output (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
        k (encodeSet (coordinateOrder A) S.val) (List.ofFn bits)))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val) := by
  let f := fun b : CompanionMetropolisProgram.Fields A C K j k xi =>
    CompanionMetropolisProgram.output (CompanionMetropolisProgram.programInput A C K j k xi
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S b)
  let g := fun b : CompanionMetropolisProgram.Fields A C K j k xi =>
    encodeSet (coordinateOrder A)
      (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S
          ((CompanionBooleanPhase.stepWordEquiv A C K j k xi).symm b)).val
  have hfg : SameLaw f g := CompanionMetropolisProgram.sameLaw_fields A C K j k hC hj hK hW hB
    xi hxi z v degree depth hdegree hdepth w S
  intro phi
  simp_rw [output_ofFn]
  have hf := uniformAverage_equiv (CompanionBooleanPhase.stepWordEquiv A C K j k xi)
    (fun b => phi (f b))
  have hg := uniformAverage_equiv (CompanionBooleanPhase.stepWordEquiv A C K j k xi)
    (fun b => phi (g b))
  refine hf.trans ((hfg phi).trans ?_)
  simpa only [g,Equiv.symm_apply_apply] using hg.symm

end
end ContingencyTables.CompanionMetropolisWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteEncodedHistory
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete histories under an encoded transition law -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

lemma traceAfter_map {C U V : Type*} (F : C → U → C) (f : V → U)
    (vs : List V) (c : C) :
    traceAfter F c (vs.map f)=traceAfter (fun c v => F c (f v)) c vs := by
  induction vs generalizing c with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons,traceAfter,ih]

lemma traceStates_map {C U V : Type*} (F : C → U → C) (f : V → U)
    (vs : List V) (c : C) :
    traceStates F c (vs.map f)=traceStates (fun c v => F c (f v)) c vs := by
  unfold traceStates
  rw [traceAfter_map]

noncomputable section
variable {C Z U V : Type*} [Fintype U] [Fintype V]

/-- Equality of the encoded row laws transfers the whole finite history,
including observables depending on every visited state. -/
theorem traceStates_sameLaw (F : C → U → C) (G : Z → V → Z) (e : Z → C)
    (h : ∀ z,SameLaw (F (e z)) (fun v => e (G z v))) (z : Z) (N : ℕ) :
    SameLaw (fun us : Fin N → U => traceStates F (e z) (List.ofFn us))
      (fun vs : Fin N → V => (traceStates G z (List.ofFn vs)).map e) := by
  intro phi
  induction N generalizing z phi with
  | zero => simp only [List.ofFn_zero,traceStates,traceAfter,List.map_cons,List.map_nil,
      uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [List.ofFn_cons,traceStates,traceAfter,List.map_cons]
    have he := h z (fun c => uniformAverage (fun us : Fin N → U =>
      phi (e z::traceStates F c (List.ofFn us))))
    refine he.trans ?_
    apply congrArg uniformAverage
    funext v
    exact ih (G z v) (fun cs => phi (e z::cs))

omit [Fintype U] in
/-- The reverse accumulator used by a bounded fold has precisely the
chronological history after reversing its stored list. -/
lemma traceAfter_fold (F : C → U → C) (us : List U) (c : C) (history : List C) :
    (us.foldl (fun s u => let d := F s.1 u; (d,d::s.2)) (c,history)).2.reverse=
      history.reverse++traceAfter F c us := by
  induction us generalizing c history with
  | nil => simp only [List.foldl_nil,traceAfter,List.append_nil]
  | cons u us ih =>
    simp only [List.foldl_cons,traceAfter]
    rw [ih,List.reverse_cons,List.append_assoc]
    rfl

omit [Fintype U] in
lemma traceStates_fold (F : C → U → C) (us : List U) (c : C) :
    (us.foldl (fun s u => let d := F s.1 u; (d,d::s.2)) (c,[c])).2.reverse=
      traceStates F c us := by
  rw [traceAfter_fold]
  rfl

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBoundedWalkSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded physical recorder preserves the complete phase history -/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical

lemma recordFold_eq (fixed : Fixed) (words : List (List Bool)) (code : List ℕ)
    (past : List (List ℕ)) :
    words.foldl (fun state bits => recordAdvance (bits,state)) ((fixed,code),past)=
      let out := words.foldl (fun state bits =>
        let d := codeStep fixed state.1 bits; (d,d::state.2)) (code,past)
      ((fixed,out.1),out.2) := by
  induction words generalizing code past with
  | nil => rfl
  | cons word words ih =>
    simpa only [List.foldl_cons,recordAdvance,advance,codeStep] using
      ih (next (word,(fixed,code))) (next (word,(fixed,code))::past)

lemma history_eq_trace (fixed : Fixed) (code : List ℕ) (words : List (List Bool)) :
    history ((fixed,code),words)=traceStates (codeStep fixed) code words := by
  unfold history recordWalk initialRecord
  rw [recordFold_eq]
  exact traceStates_fold (codeStep fixed) words code

noncomputable section
variable {m n : ℕ}

lemma cap_encode (A : Instance (Fin m) (Fin n)) (S T : Set (Labels A × Bool)) :
    ProfilePrograms.capView (((encodeSet (coordinateOrder A) S).length,1),
      encodeSet (coordinateOrder A) T)=encodeSet (coordinateOrder A) T := by
  apply ProfilePrograms.capView_eq
  · simp only [encodeSet,List.length_ofFn]
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    unfold ProfilePrograms.setProfile
    split_ifs <;> omega

/-- The all-input clipping has no effect on a valid encoded transition;
in particular its full row law agrees with the reference phase step. -/
theorem codeStep_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S₀ S : CompanionBooleanPhase.State A) :
    let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
    let fixed : Fixed := (((cfg,matrixCode w),k),encodeSet (coordinateOrder A) S₀.val)
    SameLaw (fun bits : Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      codeStep fixed (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A)
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits).val) := by
  dsimp only
  have h := CompanionMetropolisWordProgram.sameLaw_flat A C K j k hC hj hK hW hB
    xi hxi z v degree depth hdegree hdepth w S
  have hm := h.map (fun code => ProfilePrograms.capView
    (((encodeSet (coordinateOrder A) S₀.val).length,1),code))
  intro phi
  simpa only [codeStep,next,bound,candidate,transitionInput,CompanionMetropolisWordProgram.packed,
    cap_encode] using hm phi

/-- The physical list recorder and the full reference state history have
the same law, before any first-return scan or phase statistic is applied. -/
theorem history_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : CompanionBooleanPhase.State A) (N : ℕ) :
    let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
    let fixed : Fixed := (((cfg,matrixCode w),k),encodeSet (coordinateOrder A) S.val)
    SameLaw (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
      history ((fixed,encodeSet (coordinateOrder A) S.val),List.ofFn (fun i => List.ofFn (words i))))
      (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) => (traceStates
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S (List.ofFn words)).map
          (fun T => encodeSet (coordinateOrder A) T.val)) := by
  dsimp only
  let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
  let fixed : Fixed := (((cfg,matrixCode w),k),encodeSet (coordinateOrder A) S.val)
  have ht := traceStates_sameLaw
    (fun code bits => codeStep fixed code (List.ofFn bits))
    (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
      (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w))
    (fun T : CompanionBooleanPhase.State A => encodeSet (coordinateOrder A) T.val)
    (codeStep_sameLaw A C K j k hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S) S N
  intro phi
  rw [show (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
      phi (history ((fixed,encodeSet (coordinateOrder A) S.val),List.ofFn (fun i => List.ofFn (words i)))))=
      (fun words => phi (traceStates (fun code bits => codeStep fixed code (List.ofFn bits))
        (encodeSet (coordinateOrder A) S.val) (List.ofFn words))) by
    funext words
    rw [history_eq_trace]
    have hm : List.ofFn (fun i => List.ofFn (words i))=(List.ofFn words).map List.ofFn := by
      rw [List.map_ofFn]
      rfl
    rw [hm,traceStates_map]]
  exact ht phi

end
end ContingencyTables.CompanionBoundedWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseFinishProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the observed ratio and learned phase update

The supplied pairs contain the current and next weight queries for every
observed state. Only plain states contribute to the ratio. The same actual
trajectory supplies the plain/defect counts and the abort test.
-/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionTraceProgram CompanionMultiplierMatrixProgram CompanionPhaseCounts

lemma term_den_pos (z : TermInput) : 0 < (term z).2 := by
  unfold term
  split_ifs
  · exact TreeFraction.normalize_den_pos _
  · decide

attribute [local irreducible] trajectory terms

attribute [local irreducible] ratio

attribute [local irreducible] next

end ContingencyTables.CompanionPhaseFinishProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposal_mass proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem recordedWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (recordedWalk A R C K j k N n hK hW xi v w S)=
      walkLaw (liftRational (transitionLaw A R C K j k hK hW xi v w) pathRead pathPut)
        (pathInitial N S) n := by
  unfold recordedWalk
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  rw [show mapLaw (uniformLaw (α := Fin n → Fin (stepBits A C K j k xi) → Bool))
      (wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n)=wordWalkLaw
          (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
          (pathInitial N S) n from rfl,wordWalkLaw_eq]
  apply congrArg (fun Q => walkLaw Q (pathInitial N S) n)
  funext a
  exact (mapLaw_comp (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
    (step A R C K j k hK hW xi v w (pathRead a)) (pathPut a)).symm

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedArithmeticStep
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed coordinate proposals for the selected-root phase walk -/

namespace ContingencyTables.RootedArithmeticStep

open CommonBasesFPRAS FirstSuccess ResidualMixture FairBits GridBoundary
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open RootedBooleanPhase RealKernelApproximation
open CompanionBooleanPhase (State stepBits proposalBits stepWordEquiv)
open CompanionArithmeticStep (RestWord)
open scoped BigOperators Classical

noncomputable section

private lemma word_finish_law {B P Q X Z : Type*}
    [Fintype B] [Fintype P] [Fintype Q] [Fintype X] [Fintype Z]
    [Nonempty B] [Nonempty P] [Nonempty Q] [DecidableEq X] [DecidableEq Z]
    (E : B ≃ P×Q) (draw : P → X) (finish : X → Q → Z) :
    mapLaw (uniformLaw (α := B)) (fun b => finish (draw (E b).1) (E b).2)=
      bindLaw (mapLaw (uniformLaw (α := P)) draw)
        (fun x => mapLaw (uniformLaw (α := Q)) (finish x)) := by
  have he := map_equiv E (uniformLaw (α := B)) (fun b : P×Q => finish (draw b.1) b.2)
  rw [uniform_equiv,←uniform_product] at he
  exact he.symm.trans (mapLaw_product_finish _ _ draw finish)

variable {I J : Type} [Fintype I] [Fintype J]

private lemma source_step_eq_finish (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    (fun bits => finish A R C K j k hK hW xi v w S
      (CompanionBooleanPhase.proposal A S (wordSplit A C K j k xi bits).1)
      (wordSplit A C K j k xi bits).2)=
      RootedBooleanPhase.step A R C K j k hK hW xi v w S := by
  funext bits
  simp only [finish,wordSplit,regroup,RootedBooleanPhase.step,Equiv.trans_apply,Equiv.coe_fn_mk]
  by_cases hlazy : (stepWordEquiv A C K j k xi bits).1 0 = true
  · simp only [hlazy,ite_true, if_true]
  · simp only [hlazy]
    cases CompanionBooleanPhase.proposal A S
      (stepWordEquiv A C K j k xi bits).2.1 with
    | none => simp only
    | some T =>
      simp only
      by_cases haccept : rationalThresholdAccept k
        (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val
          (stepWordEquiv A C K j k xi bits).2.2.1)
        (stepWordEquiv A C K j k xi bits).2.2.2
      · simp only [haccept,ite_true, if_true]
      · simp only [haccept,ite_false]

/-- Exact equality of complete one-step laws, including all holding
probability. Weight calls and the acceptance coin have not been reused. -/
theorem step_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    mapLaw (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
      (step A R C K j k hK hW xi v w S)=
        transitionLaw A R C K j k hK hW xi v w S := by
  have hnew := word_finish_law (wordSplit A C K j k xi)
    (CompanionArithmeticProposal.proposal A S) (finish A R C K j k hK hW xi v w S)
  have hold := word_finish_law (wordSplit A C K j k xi)
    (CompanionBooleanPhase.proposal A S) (finish A R C K j k hK hW xi v w S)
  change mapLaw _ (fun bits => finish A R C K j k hK hW xi v w S
    (CompanionArithmeticProposal.proposal A S (wordSplit A C K j k xi bits).1)
    (wordSplit A C K j k xi bits).2)=_
  rw [hnew,CompanionArithmeticProposal.proposal_law]
  rw [source_step_eq_finish] at hold
  exact hold.symm

theorem recordedWalk_law (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) :
    mapLaw (uniformLaw (α := Fin (n*stepBits A C K j k xi) → Bool))
      (recordedWalk A R C K j k N n hK hW xi v w S)=
        pathLaw A R C K j k N n hK hW xi v w S := by
  unfold recordedWalk pathLaw
  rw [←map_equiv (oracleWalkWordEquiv n (stepBits A C K j k xi)),uniform_equiv]
  rw [show mapLaw (uniformLaw (α := Fin n → Fin (stepBits A C K j k xi) → Bool))
      (wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n)=
      wordWalkLaw (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
        (pathInitial N S) n from rfl,wordWalkLaw_eq]
  congr 1
  funext a
  rw [←mapLaw_comp,step_law]
  rfl

end
end ContingencyTables.RootedArithmeticStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseExperiment
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the selected-root executed finite-word phase history -/

namespace ContingencyTables.RootedPhaseExperiment

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionRationalUpdates RootedAnnealing RootedMultiplierUpdate
open RootedTraceWords TwoLiftStates GridBoundary
open CompanionPhaseTrajectory (position_put historyPrefix)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (State stepBits)
open scoped BigOperators Classical

noncomputable section

private lemma wordWalk_position {X : Type*} {k : ℕ}
    (step : X → (Fin k → Bool) → X) (N n : ℕ) (x : X) :
    n≤N → ∀ bits : Fin n → Fin k → Bool,
      (wordWalk (fun a b => pathPut a (step (pathRead a) b))
        (pathInitial N x) n bits).1.val=n := by
  induction n with
  | zero => intro _ bits; rfl
  | succ n ih =>
    intro hn bits
    let a := wordWalk (fun a b => pathPut a (step (pathRead a) b))
      (pathInitial N x) n (Fin.init bits)
    have ha : a.1.val=n := ih (by omega) (Fin.init bits)
    have hlt : a.1.val<N := by omega
    change (pathPut a (step (pathRead a) (bits (Fin.last n)))).1.val=n+1
    rw [position_put a _ hlt,ha]

private lemma full_prefix {X : Type*} {N : ℕ} (a : PathState X N)
    (ha : a.1.val=N) : historyPrefix a=List.ofFn a.2 := by
  unfold historyPrefix
  simp only [ha]
  congr 1

variable {I J : Type} [Fintype I] [Fintype J]

theorem observedStates_list (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    List.ofFn (observedStates A R C K j k N hK hW xi v w S bits)=
      (historyPrefix (RootedArithmeticStep.recordedWalk
        A R C K j k N N hK hW xi v w S bits)).map Subtype.val := by
  have hp := wordWalk_position (RootedArithmeticStep.step A R C K j k hK hW xi v w)
    N N S le_rfl (oracleWalkWordEquiv N (stepBits A C K j k xi) bits)
  change (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits).1.val=N at hp
  rw [full_prefix _ hp,List.map_ofFn]
  rfl

end
end ContingencyTables.RootedPhaseExperiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTransitionWidth
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the exact companion transition word length -/

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CompanionMetropolisWordProgram

attribute [local irreducible] proposalWidth queryWidth

lemma width_eq (z : Input) : width z=1+(proposalWidth z+((queryWidth z+queryWidth z)+z.1.1.2)) := by
  rfl

noncomputable section
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle GridBoundary
variable {m n : ℕ}

theorem width_config (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : CompanionMultiplierMatrixProgram.FractionMatrix)
    (S : Set (Labels A × Bool)) (bits : List Bool) :
    width (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,w)
      k (encodeSet (coordinateOrder A) S) bits)=CompanionBooleanPhase.stepBits A C K j k xi := by
  rw [width_eq,proposalWidth_code,queryWidth_config]
  rfl

end
end ContingencyTables.CompanionTransitionWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionFlatReturnProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded flat word for the actual capped-return program -/

namespace ContingencyTables.CompanionFlatReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

noncomputable section
open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open CompanionTraceWords CompanionCappedReturn TwoLiftStates GridBoundary
open scoped Classical
variable {m n : ℕ}

lemma words_data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A)
    (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi) → Bool) :
    words (data A C K j k N xi z v degree depth w S (List.ofFn bits))=
      List.ofFn (fun i : Fin N => List.ofFn
        (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits i)) := by
  unfold words width widthInput data stateData
  dsimp only
  change (wordChunks (CompanionTransitionWidth.width (CompanionMetropolisWordProgram.packed
    (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) []),List.ofFn bits)).take N=_
  rw [CompanionTransitionWidth.width_config]
  rw [wordChunks_ofFn (by unfold CompanionBooleanPhase.stepBits; omega)]
  exact List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl)

end
end ContingencyTables.CompanionFlatReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrajectoryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The flat executed observation trajectory, including its initial state -/
namespace ContingencyTables.CompanionTrajectoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (S : CompanionBooleanPhase.State A) :
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
      output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits)))
      (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
        (traceStates (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S
            (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))).map
              (fun T => encodeSet (coordinateOrder A) T.val)) := by
  let state := CompanionFlatReturnProgram.stateData A C K j k xi z v degree depth w S
  have hs := CompanionBoundedWalkProgram.history_sameLaw A C K j k hC hj hK hW hB xi hxi
    z v degree depth hdegree hdepth w S N
  dsimp only at hs
  intro phi
  have hl := uniformAverage_equiv (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi))
    (fun ws => phi (CompanionBoundedWalkProgram.history
      (state,List.ofFn (fun i => List.ofFn (ws i)))))
  have hr := uniformAverage_equiv (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi))
    (fun ws => phi ((traceStates (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T)
      C K j k hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S
        (List.ofFn ws)).map (fun T => encodeSet (coordinateOrder A) T.val)))
  have ho (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
      output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))=
        CompanionBoundedWalkProgram.history (state,List.ofFn (fun i => List.ofFn
          (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits i))) := by
    change CompanionBoundedWalkProgram.history
      (state,CompanionFlatReturnProgram.words
        (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits)))=_
    rw [CompanionFlatReturnProgram.words_data]
  have he : uniformAverage (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
      phi (output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))))=
      uniformAverage (fun bits => phi (CompanionBoundedWalkProgram.history
        (state,List.ofFn (fun i => List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits i))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (ho bits)
  exact he.trans (hl.trans ((hs phi).trans hr.symm))

end
end ContingencyTables.CompanionTrajectoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCodeBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoded profile bounds independent of learned multiplier sizes -/
namespace ContingencyTables.CompanionCodeBounds
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma walk_next (bits : List Bool) (s : CompanionBoundedWalkProgram.State) :
    weight (CompanionBoundedWalkProgram.next (bits,s)) ≤ 6*s.1.2.length+1 := by
  simpa only [CompanionBoundedWalkProgram.next,CompanionBoundedWalkProgram.bound,Nat.size_one,Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using
    ProfilePrograms.capView_weight s.1.2.length 1 (CompanionBoundedWalkProgram.candidate (bits,s))

lemma record_bound (words : List (List Bool)) (s : CompanionBoundedWalkProgram.RecordState)
    (B : ℕ) (hc : weight s.1.2 ≤ B) (hf : 6*s.1.1.2.length+1 ≤ B)
    (hh : ∀ code∈s.2,weight code ≤ B) :
    let out := words.foldl (fun s bits => CompanionBoundedWalkProgram.recordAdvance (bits,s)) s
    (∀ code∈out.2,weight code ≤ B) ∧ out.2.length=s.2.length+words.length := by
  induction words generalizing s with
  | nil => exact ⟨hh,by simp⟩
  | cons word words ih =>
    have hn := (walk_next word s.1).trans hf
    have h := ih (CompanionBoundedWalkProgram.recordAdvance (word,s)) hn hf (by
      intro code hcode
      rcases List.mem_cons.mp hcode with he | he
      · subst code; exact hn
      · exact hh code he)
    exact ⟨h.1,by simpa only [List.foldl_cons,CompanionBoundedWalkProgram.recordAdvance,
      List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩

lemma history_bound (s : CompanionBoundedWalkProgram.State) (words : List (List Bool))
    (B : ℕ) (hc : weight s.2 ≤ B) (hf : 6*s.1.2.length+1 ≤ B) :
    (∀ code∈CompanionBoundedWalkProgram.history (s,words),weight code ≤ B) ∧
      (CompanionBoundedWalkProgram.history (s,words)).length=words.length+1 := by
  have h := record_bound words (s,[s.2]) B hc hf (by simpa only [List.mem_singleton] using
    fun code he => he ▸ hc)
  constructor
  · intro code hcode
    exact h.1 code (List.mem_reverse.mp hcode)
  · simpa only [CompanionBoundedWalkProgram.history,CompanionBoundedWalkProgram.recordWalk,
      CompanionBoundedWalkProgram.initialRecord,List.length_reverse,List.length_cons,List.length_nil,
      Nat.add_comm] using h.2

end ContingencyTables.CompanionCodeBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierAgreement
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only canonical pair entries affect the executed chain

The finite matrix stores one entry per pair of labels. Values of the
mathematical multiplier on arbitrary noncanonical coordinate pairs
do not affect any weight call, acceptance decision, or capped return.
-/

namespace ContingencyTables.CompanionMultiplierAgreement

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open CompanionBooleanPhase (State stepBits)
open scoped Classical

noncomputable section

lemma rationalMultiplier_congr {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (gs : List (Γ × Γ)) (w w' : (Γ × Γ) → (Γ × Γ) → ℚ)
    (hw : ∀ p ∈ gs, ∀ q ∈ gs, w p q=w' p q) (S : Set Γ) :
    rationalMultiplier gs w S=rationalMultiplier gs w' S := by
  unfold rationalMultiplier
  split_ifs with h
  · exact hw _ h.choose_spec.choose_spec.1 _ h.choose_spec.choose_spec.2.1
  · rfl

variable {I J : Type} [Fintype I] [Fintype J]

lemma agree_on_pairs (A : Instance I J) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    ∀ p ∈ (pairs : List (Pair A)), ∀ q ∈ (pairs : List (Pair A)), w p q=w' p q := by
  intro p hp q hq
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hp
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hq
  exact hw a b

lemma multiplier_eq (A : Instance I J) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') (S : Set (Labels A × Bool)) :
    rationalMultiplier pairs w S=rationalMultiplier pairs w' S :=
  rationalMultiplier_congr pairs w w' (agree_on_pairs A w w' hw) S

lemma evaluatedWeight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') (S : Set (Labels A × Bool)) (bits : WeightWord A C K j xi) :
    RootedOracleAcceptance.evaluatedWeight A R C K j hK hW xi v w S bits=
      RootedOracleAcceptance.evaluatedWeight A R C K j hK hW xi v w' S bits := by
  unfold RootedOracleAcceptance.evaluatedWeight
  rw [multiplier_eq A w w' hw]

lemma acceptance_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedOracleAcceptance.acceptance A R C K j hK hW xi v w=
      RootedOracleAcceptance.acceptance A R C K j hK hW xi v w' := by
  funext S T bits
  unfold RootedOracleAcceptance.acceptance
  rw [evaluatedWeight_eq A R C K j hK hW xi v w w' hw,
    evaluatedWeight_eq A R C K j hK hW xi v w w' hw]

lemma arithmeticFinish_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.finish A R C K j k hK hW xi v w=
      RootedArithmeticStep.finish A R C K j k hK hW xi v w' := by
  funext S U bits
  unfold RootedArithmeticStep.finish
  rw [acceptance_eq A R C K j hK hW xi v w w' hw]

lemma arithmeticStep_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.step A R C K j k hK hW xi v w=
      RootedArithmeticStep.step A R C K j k hK hW xi v w' := by
  funext S bits
  unfold RootedArithmeticStep.step
  rw [arithmeticFinish_eq A R C K j k hK hW xi v w w' hw]

lemma recordedWalk_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k N n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.recordedWalk A R C K j k N n hK hW xi v w=
      RootedArithmeticStep.recordedWalk A R C K j k N n hK hW xi v w' := by
  funext S bits
  unfold RootedArithmeticStep.recordedWalk
  rw [arithmeticStep_eq A R C K j k hK hW xi v w w' hw]

end
end ContingencyTables.CompanionMultiplierAgreement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservationQueriesLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent laws for the executed observation queries -/
namespace ContingencyTables.CompanionObservationQueriesProgram
open MatchingFPRAS DensePrograms GridBoundary FairBits CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle
open scoped Classical
noncomputable section
attribute [local irreducible] queryWidth queryPair RootedLabelWeightProgram.output
  RootedLabelWeightProgram.config RootedEstimatorMedianProgram.context RootedEstimatorLayoutProgram.wordWidth

lemma queryPair_ofFn (cs : Config×Config) (code : List ℕ)
    (bits : Fin (blockWidth cs)→Bool) :
    queryPair (cs,(code,List.ofFn bits))=
      (RootedLabelWeightProgram.output (cs.1,(code,List.ofFn (splitWordEquiv _ _ bits).1)),
       RootedLabelWeightProgram.output (cs.2,(code,List.ofFn (splitWordEquiv _ _ bits).2))) := by
  unfold queryPair currentInput nextInput
  dsimp only
  rw [ofFn_split_take,ofFn_split_drop]
  rw [List.take_of_length_le (show (List.ofFn (splitWordEquiv (queryWidth cs.1)
    (queryWidth cs.2) bits).2).length ≤ queryWidth cs.2 by simp only [List.length_ofFn,le_refl])]

lemma output_ofFn {N : ℕ} (cs : Config×Config) (codes : Fin N→List ℕ)
    (bits : Fin (N*blockWidth cs)→Bool) :
    output (cs,(List.ofFn codes,List.ofFn bits))=
      List.ofFn (fun i => queryPair
        (cs,(codes i,List.ofFn (gridWordEquiv N (blockWidth cs) bits i)))) := by
  unfold output indices
  simp only [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi' : i < N := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,indexedPair,indexedInput,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi',dite_true,Option.getD_some]
    have hw := wordChunk_ofFn bits ⟨i,hi'⟩
    exact congrArg (fun bs => queryPair (cs,(codes ⟨i,hi'⟩,bs))) hw

/-- Each trajectory position gets its own independent current and next query. -/
theorem sameLaw {N : ℕ} {U V : Type*} [Fintype U] [Fintype V]
    (cs : Config×Config) (codes : Fin N→List ℕ) (f : Fin N→U→ℚ) (g : Fin N→V→ℚ)
    (hf : ∀ i,SameLaw (fun bits : Fin (queryWidth cs.1)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output (cs.1,(codes i,List.ofFn bits)))) (f i))
    (hg : ∀ i,SameLaw (fun bits : Fin (queryWidth cs.2)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output (cs.2,(codes i,List.ofFn bits)))) (g i)) :
    SameLaw (fun bits : Fin (N*blockWidth cs)→Bool =>
      values (output (cs,(List.ofFn codes,List.ofFn bits))))
      (fun bits : Fin N→U×V => List.ofFn (fun i => (f i (bits i).1,g i (bits i).2))) := by
  have h := (FiniteObservableTransport.indexed N _ _ (fun i => (hf i).prod (hg i))).map List.ofFn
  let e : (Fin (N*blockWidth cs)→Bool) ≃
      (Fin N→(Fin (queryWidth cs.1)→Bool)×(Fin (queryWidth cs.2)→Bool)) :=
    (gridWordEquiv N (blockWidth cs)).trans (Equiv.piCongrRight (fun _ => splitWordEquiv _ _))
  intro phi
  have he := uniformAverage_equiv e (fun xs => phi (List.ofFn (fun i =>
    (TreeFraction.val (RootedLabelWeightProgram.output (cs.1,(codes i,List.ofFn (xs i).1))),
      TreeFraction.val (RootedLabelWeightProgram.output (cs.2,(codes i,List.ofFn (xs i).2)))))))
  have hout : (fun bits : Fin (N*blockWidth cs)→Bool =>
      phi (values (output (cs,(List.ofFn codes,List.ofFn bits)))))=
      (fun bits => phi (List.ofFn (fun i =>
        (TreeFraction.val (RootedLabelWeightProgram.output (cs.1,(codes i,List.ofFn (e bits i).1))),
          TreeFraction.val (RootedLabelWeightProgram.output (cs.2,(codes i,List.ofFn (e bits i).2))))))) := by
    funext bits
    rw [output_ofFn]
    simp only [values,List.map_ofFn,queryPair_ofFn]
    rfl
  rw [hout]
  exact he.trans (h phi)

variable {m n : ℕ}
lemma queryWidth_config (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) :
    queryWidth (RootedLabelWeightProgram.config A C K j xi xi z v degree depth)=
      medianEstimatorBits A C K j xi xi := by
  unfold queryWidth RootedLabelWeightProgram.config
  exact CompanionEvaluatedWeightProgram.queryWidth A C K j xi z v

lemma sameLaw_query (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (S : Set (Labels A×Bool)) :
    SameLaw (fun bits : Fin (queryWidth
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth))→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
          (encodeSet (coordinateOrder A) S,List.ofFn bits))))
      (RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T) C K hK hW j xi
        (RootedCatalogGrid.gridEquiv A K v) S) := by
  have h := RootedLabelWeightProgram.sameLaw_weight A C K j hC hj hK hW hB xi hxi z v
    degree depth hdegree hdepth S
  exact SameLaw.word_length
    ((CompanionEvaluatedWeightProgram.queryWidth A C K j xi (profile A S) v).trans
      (queryWidth_config A C K j xi z v degree depth).symm) (fun bs => TreeFraction.val (RootedLabelWeightProgram.output
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
          (encodeSet (coordinateOrder A) S,bs)))) _ h

end
end ContingencyTables.CompanionObservationQueriesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseFinishSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact semantics of the stored phase update -/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS CompanionFactorialApplication CompanionTraceProgram CompanionPhaseCounts
open CompanionMultiplierMatrixProgram CompanionMultiplierProgram CompanionOrderedProposal
open CompanionArithmeticProposal CompanionRationalUpdates CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p q N : ℕ} (g : Fin p ≃ Labels A) (e : (Labels A×Bool) ≃ Fin q)

lemma termInput_data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) (i : Fin N) :
    termInput (data A g e states w E values,i.val)=
      ((orderedCatalog A g e,encodeSet e (states i)),values i) := by
  simp only [termInput,data,trajectory,List.map_ofFn,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta,Function.comp_apply]

lemma term_value (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) (i : Fin N) :
    TreeFraction.val (indexedTerm (data A g e states w E values,i.val))=
      if PlainState pairs (states i) then TreeFraction.val (values i).2/TreeFraction.val (values i).1 else 0 := by
  rw [indexedTerm,termInput_data]
  have hp : pairedPlainTest (orderedCatalog A g e,encodeSet e (states i))=
      decide (PlainState pairs (states i)) :=
    Bool.eq_iff_iff.mpr (by simp only [plainTest_ordered,decide_eq_true_eq])
  unfold term
  rw [hp]
  by_cases h : PlainState pairs (states i)
  · simp only [h,decide_true,ite_true, if_true,TreeFraction.div_val]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false,TreeFraction.val,
      Nat.cast_zero,Nat.cast_one,zero_div]

lemma terms_data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) :
    terms (data A g e states w E values)=
      List.ofFn (fun i : Fin N => indexedTerm (data A g e states w E values,i.val)) := by
  unfold terms indices trajectory data
  simp only [List.length_map,List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.length_map,List.length_range] at hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

lemma terms_den_pos (z : Input) (x : Fraction) (hx : x∈terms z) : 0 < x.2 := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  exact term_den_pos _

lemma ratio_data (states : Fin N→Set (Labels A×Bool))
    (w : Fin p→Fin p→Fraction) (E : Fraction) (values : Fin N→Fraction×Fraction) :
    TreeFraction.val (ratio (data A g e states w E values))=
      (∑ i,if PlainState pairs (states i) then TreeFraction.val (values i).2/TreeFraction.val (values i).1 else 0)/
        (plainCount A (List.ofFn states):ℚ) := by
  rw [ratio,TreeFraction.div_val,total,TreeFraction.sum_val _ (terms_den_pos _)]
  rw [terms_data]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,term_value]
  have hc : TreeFraction.val (count (data A g e states w E values))=
      (plainCount A (List.ofFn states):ℚ) := by
    unfold count trajectory data
    rw [plainCount_code]
    simp only [TreeFraction.val,Nat.cast_one,div_one]
  rw [hc]

lemma updated_entry (states : Fin N→Set (Labels A×Bool)) (hl : 0 < N)
    (w : Fin p→Fin p→Fraction) (old : CompanionPhaseWords.Stored A)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (g i)) (pair (g j))) (i j : Fin p) :
    TreeFraction.val (readEntry
      (updateMatrix ((orderedCatalog A g e,(List.ofFn states).map (encodeSet e)),matrixCode w),(i.val,j.val)))=
      rationalLearn pairs old.multiplier (List.ofFn states) (pair (g i)) (pair (g j)) := by
  rw [updateMatrix_code,readEntry_code,updateCode_value,
    plainCount_code,defectCount_code,hw]
  rw [rationalLearn_counts A old.multiplier (List.ofFn states) (by simpa only [List.length_ofFn] using hl)]
  have hp : pair (g i)∈(pairs : List (Pair A)) := pair_mem _
  have hq : pair (g j)∈(pairs : List (Pair A)) := pair_mem _
  have he : pair (g i)=pair (g j) ↔ i=j :=
    ⟨fun h => g.injective (pair_injective h),fun h => congrArg (fun k => pair (g k)) h⟩
  by_cases hij : i=j
  · subst j
    simp only [hp,ne_eq,not_true_eq_false,and_false,ite_false,ite_true, if_true]
  · have hv : i.val≠j.val := fun h => hij (Fin.ext h)
    have hpq : pair (g i)≠pair (g j) := fun h => hij (he.mp h)
    simp only [hv,hp,hq,true_and,ite_false]
    exact (ite_eq_left hpq).symm

lemma output_values (states : Fin N→Set (Labels A×Bool))
    (old : CompanionPhaseWords.Stored A) (w : Fin p→Fin p→Fraction) (E : Fraction)
    (values : Fin N→Fraction×Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (g i)) (pair (g j)))
    (hE : TreeFraction.val E=old.estimate) :
    (output (data A g e states w E values)).map (view (p := p))=
      rationalResult A g states old (List.ofFn (fun i =>
        (TreeFraction.val (values i).1,TreeFraction.val (values i).2))) := by
  have ht : positiveCounts (trajectory (data A g e states w E values))=true ↔
      CountsPositive A (List.ofFn states) := positiveCounts_code A g e (List.ofFn states)
  by_cases hp : CountsPositive A (List.ofFn states)
  · have hN : 0 < N := by
      simpa only [List.length_ofFn] using hp.1.trans_le (plainCount_le A (List.ofFn states))
    simp only [output,ht.mpr hp,ite_true, if_true,Option.map_some,rationalResult,hp]
    apply congrArg Option.some
    apply Prod.ext
    · funext i k
      exact updated_entry A g e states hN w old hw i k
    · change TreeFraction.val (estimate (data A g e states w E values))=_
      rw [estimate,TreeFraction.mul_val,ratio_data]
      dsimp only [data]
      rw [hE]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  · have htest : positiveCounts (trajectory (data A g e states w E values))=false :=
      Bool.eq_false_iff.mpr (fun h => hp (ht.mp h))
    simp only [output,htest,Bool.false_eq_true,ite_false,Option.map_none,rationalResult,hp]

lemma rationalResult_phase (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : GridBoundary.Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (old : CompanionPhaseWords.Stored A) (states : Fin N→Set (Labels A×Bool))
    (bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool) :
    rationalResult A g states old (List.ofFn (fun i =>
      (RootedWeightOracle.evaluate A R C K hK hW j xi v (states i)
        (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).1,
       RootedWeightOracle.evaluate A R C K hK hW (j+1) xi v (states i)
        (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).2)))=
      (RootedPhaseWords.update A R C K j N hK hW xi v old states bits).map (storedView A g) := by
  by_cases hp : CountsPositive A (List.ofFn states)
  · simp only [rationalResult,RootedPhaseWords.update,hp,ite_true, if_true,Option.map_some,storedView]
    apply congrArg Option.some
    apply Prod.ext
    · rfl
    · change old.estimate * _ = old.estimate * _
      unfold RootedPhaseWords.observedRatio
      apply congrArg (fun t : ℚ => old.estimate*(t/(plainCount A (List.ofFn states):ℚ)))
      apply Finset.sum_congr rfl
      intro i _
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
      rfl
  · simp only [rationalResult,RootedPhaseWords.update,hp,ite_false,Option.map_none]

end
end ContingencyTables.CompanionPhaseFinishProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservedUpdateLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observable law of the physically executed phase update -/
namespace ContingencyTables.CompanionObservedUpdateProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionMultiplierMatrixProgram
open FiniteObservableTransport CompanionComputedProposal TwoLiftStates
open scoped Classical
noncomputable section
variable {m n N : ℕ} (A : Instance (Fin m) (Fin n))

attribute [local irreducible] CompanionObservationQueriesProgram.output
  CompanionPhaseFinishProgram.output CompanionPhaseFinishProgram.rationalResult

theorem output_values (cs : Configs) (states : Fin N→Set (Labels A×Bool))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate)
    (bits : Fin (N*CompanionObservationQueriesProgram.blockWidth cs)→Bool) :
    (output (data A cs states w E (List.ofFn bits))).map CompanionPhaseFinishProgram.view=
      CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
        (CompanionObservationQueriesProgram.values (CompanionObservationQueriesProgram.output
          (cs,(List.ofFn (fun i => encodeSet (coordinateOrder A) (states i)),List.ofFn bits)))) := by
  have hq := CompanionObservationQueriesProgram.output_ofFn cs
    (fun i => encodeSet (coordinateOrder A) (states i)) bits
  have ho : output (data A cs states w E (List.ofFn bits))=
      CompanionPhaseFinishProgram.output
        ((((orderedCatalog A (pairLabels A) (coordinateOrder A),
          (List.ofFn states).map (encodeSet (coordinateOrder A))),matrixCode w),E),
          CompanionObservationQueriesProgram.output
            (cs,(List.ofFn (fun i => encodeSet (coordinateOrder A) (states i)),List.ofFn bits))) := by
    simp only [output,finishInput,queryInput,data,List.map_ofFn,Function.comp_def]
  rw [ho,hq]
  simpa only [CompanionPhaseFinishProgram.data,CompanionObservationQueriesProgram.values,List.map_ofFn,Function.comp_def] using
    (CompanionPhaseFinishProgram.output_values A (pairLabels A) (coordinateOrder A)
      states old w E (fun i => CompanionObservationQueriesProgram.queryPair
        (cs,(encodeSet (coordinateOrder A) (states i),List.ofFn
          (GridBoundary.gridWordEquiv N (CompanionObservationQueriesProgram.blockWidth cs) bits i)))) hw hE)

theorem sameLaw {U V : Type*} [Fintype U] [Fintype V]
    (cs : Configs) (states : Fin N→Set (Labels A×Bool))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (f : Fin N→U→ℚ) (g : Fin N→V→ℚ)
    (hf : ∀ i,SameLaw (fun bits : Fin (CompanionObservationQueriesProgram.queryWidth cs.1)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output
        (cs.1,(encodeSet (coordinateOrder A) (states i),List.ofFn bits)))) (f i))
    (hg : ∀ i,SameLaw (fun bits : Fin (CompanionObservationQueriesProgram.queryWidth cs.2)→Bool =>
      TreeFraction.val (RootedLabelWeightProgram.output
        (cs.2,(encodeSet (coordinateOrder A) (states i),List.ofFn bits)))) (g i)) :
    SameLaw (fun bits : Fin (N*CompanionObservationQueriesProgram.blockWidth cs)→Bool =>
      (output (data A cs states w E (List.ofFn bits))).map CompanionPhaseFinishProgram.view)
      (fun bits : Fin N→U×V => CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
        (List.ofFn (fun i => (f i (bits i).1,g i (bits i).2)))) := by
  have h := (CompanionObservationQueriesProgram.sameLaw cs
    (fun i => encodeSet (coordinateOrder A) (states i)) f g hf hg).map
      (CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old)
  intro phi
  simp_rw [output_values A cs states old w E hw hE]
  exact h phi

open GridBoundary CommonBasesFPRAS CompanionWeightOracle CompanionOracleDensity

/-- The complete executed observation-and-update has the actual phase law. -/
theorem sameLaw_phase (C K j : ℕ)
    (hC : 0 < C) (hj : j+1 ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (states : Fin N→Set (Labels A×Bool)) (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : Fin (N*CompanionObservationQueriesProgram.blockWidth cs)→Bool =>
      (output (data A cs states w E (List.ofFn bits))).map CompanionPhaseFinishProgram.view)
      (fun bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool =>
        (RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old states bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
  let f := fun i : Fin N => RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T)
    C K hK hW j xi (RootedCatalogGrid.gridEquiv A K v) (states i)
  let g := fun i : Fin N => RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T)
    C K hK hW (j+1) xi (RootedCatalogGrid.gridEquiv A K v) (states i)
  have h := sameLaw A cs states old w E hw hE f g
    (fun i => CompanionObservationQueriesProgram.sameLaw_query A C K j hC (by omega)
      hK hW hB xi hxi z v degree depth hdegree hdepth (states i))
    (fun i => CompanionObservationQueriesProgram.sameLaw_query A C K (j+1) hC hj
      hK hW hB xi hxi z v nextDegree nextDepth hnextDegree hnextDepth (states i))
  dsimp only
  intro phi
  have he := uniformAverage_equiv (CompanionPhaseWords.phaseWordEquiv A C K j N xi)
    (fun xs => phi (CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
      (List.ofFn (fun i => (f i (xs i).1,g i (xs i).2)))))
  have hr : CommonBasesFPRAS.uniformAverage
      (fun bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool =>
        phi (CompanionPhaseFinishProgram.rationalResult A (pairLabels A) states old
          (List.ofFn (fun i =>
            (f i (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).1,
             g i (CompanionPhaseWords.phaseWordEquiv A C K j N xi bits i).2)))))=
      CommonBasesFPRAS.uniformAverage (fun bits : Fin (CompanionPhaseWords.phaseBits A C K j N xi)→Bool =>
        phi ((RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old states bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A)))) := by
    apply congrArg CommonBasesFPRAS.uniformAverage
    funext bits
    exact congrArg phi (CompanionPhaseFinishProgram.rationalResult_phase A (pairLabels A)
      (RootedCompletion.rowColumn A.T) C K j hK hW xi (RootedCatalogGrid.gridEquiv A K v) old states bits)
  exact (h phi).trans (he.symm.trans hr)

end
end ContingencyTables.CompanionObservedUpdateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRecordedHistory
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed-capacity recorder stores the chronological word history -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionBooleanPhase CompanionPhaseTrajectory

lemma traceStates_snoc {X U : Type*} (F : X → U → X) (us : List U) (c : X) (u : U) :
    traceStates F c (us++[u])=
      traceStates F c us++[F (us.foldl F c) u] := by
  induction us generalizing c with
  | nil => rfl
  | cons a us ih =>
    change c::traceStates F (F c a) (us++[u])=
      c::(traceStates F (F c a) us++[F (us.foldl F (F c a)) u])
    rw [ih]

lemma recorded_position {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X)
    (N : ℕ) (c : X) (n : ℕ) (hn : n ≤ N) (words : Fin n → Fin k → Bool) :
    (recorded F N c n words).1.val=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (pathPut (recorded F N c n (Fin.init words))
      (F (pathRead (recorded F N c n (Fin.init words))) (words (Fin.last n)))).1.val=n+1
    rw [position_put]
    · rw [ih (by omega)]
    · rw [ih (by omega)]
      omega

lemma recorded_read {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X)
    (N : ℕ) (c : X) (n : ℕ) (words : Fin n → Fin k → Bool) :
    pathRead (recorded F N c n words)=(List.ofFn words).foldl F c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pathRead (pathPut (recorded F N c n (Fin.init words))
      (F (pathRead (recorded F N c n (Fin.init words))) (words (Fin.last n))))=_
    rw [read_put,ih,List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    rfl

theorem recorded_prefix {X : Type*} {k : ℕ} (F : X → (Fin k → Bool) → X)
    (N : ℕ) (c : X) (n : ℕ) (hn : n ≤ N) (words : Fin n → Fin k → Bool) :
    historyPrefix (recorded F N c n words)=traceStates F c (List.ofFn words) := by
  induction n with
  | zero => exact prefix_initial N c
  | succ n ih =>
    change historyPrefix (pathPut (recorded F N c n (Fin.init words))
      (F (pathRead (recorded F N c n (Fin.init words))) (words (Fin.last n))))=_
    rw [prefix_put]
    · rw [ih (by omega),recorded_read,List.ofFn_succ',List.concat_eq_append,traceStates_snoc]
      rfl
    · rw [recorded_position F N c n (by omega)]
      omega

end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrajectoryLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed observation trajectory has the selected-root source law -/
namespace ContingencyTables.CompanionTrajectoryProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess ResidualMixture FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionPhaseTrajectory
open CompanionBooleanPhase (State)
open RealKernelApproximation GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem observations_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (S : State A) :
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
      output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits)))
      (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
        (List.ofFn (RootedPhaseExperiment.observedStates A (RootedCompletion.rowColumn A.T)
          C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits)).map
            (encodeSet (coordinateOrder A))) := by
  let R := RootedCompletion.rowColumn A.T
  let v' := RootedCatalogGrid.gridEquiv A K v
  let sw := sourceWeights A w
  let F := RootedBooleanPhase.step A R C K j k hK hW xi v' sw
  let ret := fun a : PathState (State A) N =>
    (historyPrefix a).map (fun T => encodeSet (coordinateOrder A) T.val)
  have hb := RootedBooleanPhase.recordedWalk_law A R C K j k N N hK hW xi v' sw S
  have ha := RootedArithmeticStep.recordedWalk_law A R C K j k N N hK hW xi v' sw S
  have hm := (SameLaw.of_mapLaw_eq
    (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S)
    (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v' sw S)
    (hb.trans ha.symm)).map ret
  have hleft (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
      ret (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S bits)=
        (traceStates F S (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))).map
          (fun T => encodeSet (coordinateOrder A) T.val) := by
    unfold ret
    rw [show historyPrefix (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S bits)=
      traceStates F S (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits)) from
      recorded_prefix F N S N le_rfl _]
  have hright (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
      ret (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v' sw S bits)=
        (List.ofFn (RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v' sw S bits)).map
          (encodeSet (coordinateOrder A)) := by
    rw [RootedPhaseExperiment.observedStates_list]
    simp only [ret,List.map_map,Function.comp_def]
  intro phi
  have h := output_sameLaw A C K j k N hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S phi
  have hl : uniformAverage (fun bits => phi (ret
      (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S bits)))=
      uniformAverage (fun bits => phi ((traceStates F S
        (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))).map
          (fun T => encodeSet (coordinateOrder A) T.val))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hleft bits)
  have hr : uniformAverage (fun bits => phi (ret
      (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v' sw S bits)))=
      uniformAverage (fun bits => phi ((List.ofFn (RootedPhaseExperiment.observedStates A R
        C K j k N hK hW xi v' sw S bits)).map (encodeSet (coordinateOrder A)))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hright bits)
  exact h.trans (hl.symm.trans ((hm phi).trans hr))

end
end ContingencyTables.CompanionTrajectoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteEncodedBind
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing exact laws through a noninjective state encoding -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem encoded_bind {A B U V C Z W : Type*}
    [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (f : A → C) (g : B → Z) (e : Z → C) (F : C → U → W) (G : Z → V → W)
    (hinit : SameLaw f (fun b => e (g b))) (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun p : A×U => F (f p.1) p.2) (fun p : B×V => G (g p.1) p.2) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hi := hinit (fun c => uniformAverage (fun u : U => phi (F c u)))
  refine hi.trans ?_
  apply congrArg uniformAverage
  funext b
  exact hstep (g b) phi

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restart histories depend only on stored canonical pair entries -/

namespace ContingencyTables.CompanionMultiplierAgreement
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open CompanionBooleanPhase (State stepBits)
open TwoLiftStates GridBoundary
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem observedStates_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k N : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v w=
      RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v w' := by
  funext S bits i
  unfold RootedPhaseExperiment.observedStates
  rw [recordedWalk_eq A R C K j k N N hK hW xi v w w' hw]

end
end ContingencyTables.CompanionMultiplierAgreement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrialLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed trajectory and fresh queries form the source phase trial -/
namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionOrderedProposal CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle CompanionMultiplierMatrixProgram
open CompanionEvaluatedWeightProgram FiniteObservableTransport GridBoundary TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma output_data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (walkBits queryBits : List Bool) :
    output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S walkBits queryBits)=
      CompanionObservedUpdateProgram.output
        ((CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth,
          (((orderedCatalog A (pairLabels A) (coordinateOrder A),
            CompanionTrajectoryProgram.output
              (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S walkBits)),
            matrixCode w),E)),queryBits) := by
  simp only [output,updateInput,storedInput,returnInput,catalogue,trajectory,data,
    CompanionFlatReturnProgram.data,CompanionFlatReturnProgram.stateData]
  rw [generated_catalog]

/-- Before changing multiplier representation, this law uses the canonical
matrix's source weights for the trajectory and the given stored value for the update. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
        (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool) =>
      (output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        (RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j (N+1) hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old
          (RootedPhaseExperiment.observedStates A (RootedCompletion.rowColumn A.T)
            C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits.1)
          bits.2).map (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  dsimp only
  let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
  let f := fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
    CompanionTrajectoryProgram.output
      (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))
  let g := RootedPhaseExperiment.observedStates A (RootedCompletion.rowColumn A.T)
    C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S
  let e := fun states : Fin (N+1)→Set (Labels A×Bool) =>
    (List.ofFn states).map (encodeSet (coordinateOrder A))
  let F := fun codes : List (List ℕ) => fun bits : Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool =>
    (CompanionObservedUpdateProgram.output
      ((cs,(((orderedCatalog A (pairLabels A) (coordinateOrder A),codes),matrixCode w),E)),
        List.ofFn bits)).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))
  let G := fun states : Fin (N+1)→Set (Labels A×Bool) =>
    fun bits : Fin (CompanionPhaseWords.phaseBits A C K j (N+1) xi)→Bool =>
      (RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j (N+1) hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) old states bits).map
          (CompanionPhaseFinishProgram.storedView A (pairLabels A))
  have hi : SameLaw f (fun bits => e (g bits)) :=
    CompanionTrajectoryProgram.observations_sameLaw A C K j k N hC (by omega) hK hW hB
      xi hxi z v degree depth hdegree hdepth w S
  have hs : ∀ states,SameLaw (F (e states)) (G states) := by
    intro states
    exact CompanionObservedUpdateProgram.sameLaw_phase A C K j hC hj hK hW hB xi hxi z v
      degree depth nextDegree nextDepth hdegree hdepth hnextDegree hnextDepth states old w E hw hE
  have h := encoded_bind f g e F G hi hs
  intro phi
  have hl : (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
      (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool) => phi ((output (data A C K j k N xi z v degree depth nextDegree nextDepth
      w E S (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))))=
      (fun bits => phi (F (f bits.1) bits.2)) := by
    funext bits
    rw [output_data]
  rw [hl]
  exact h phi

theorem trial_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
        (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool) =>
      (output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        (RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old S bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  have hag : CompanionMultiplierAgreement.Agree A (sourceWeights A w) old.multiplier := by
    intro a b
    simpa only [sourceWeights,pair,Equiv.apply_symm_apply] using
      hw ((pairLabels A).symm a) ((pairLabels A).symm b)
  have h := sameLaw A C K j k N hC hj hK hW hB xi hxi z v degree depth nextDegree nextDepth
    hdegree hdepth hnextDegree hnextDepth old w E hw hE S
  dsimp only at h ⊢
  rw [CompanionMultiplierAgreement.observedStates_eq A (RootedCompletion.rowColumn A.T)
    C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) old.multiplier hag] at h
  exact h

end
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservationPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observation programs ignore their unused suffix -/
namespace ContingencyTables.DensePrograms
lemma wordChunk_take_blocks (n k : ℕ) (bits : List Bool) (i : ℕ) (hi : i<n) :
    wordChunk ((k,bits.take (n*k)),i)=wordChunk ((k,bits),i) := by
  have h := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hi)
  unfold wordChunk
  dsimp only
  rw [List.drop_take,List.take_take,min_eq_left]
  exact Nat.le_sub_of_add_le (by simpa only [Nat.succ_mul,Nat.add_comm] using h)
end ContingencyTables.DensePrograms

namespace ContingencyTables.CompanionObservationQueriesProgram
open DensePrograms
attribute [local irreducible] queryWidth queryPair output RootedLabelWeightProgram.output

lemma output_take (cs : Config×Config) (codes : List (List ℕ)) (bits : List Bool) :
    output (cs,(codes,bits.take (codes.length*blockWidth cs)))=output (cs,(codes,bits)) := by
  unfold output indices
  apply List.map_congr_left
  intro i hi
  apply congrArg queryPair
  change (cs,(codes.getD i [],wordChunk ((blockWidth cs,bits.take (codes.length*blockWidth cs)),i)))=
    (cs,(codes.getD i [],wordChunk ((blockWidth cs,bits),i)))
  rw [wordChunk_take_blocks codes.length (blockWidth cs) bits i (List.mem_range.mp hi)]

end ContingencyTables.CompanionObservationQueriesProgram

namespace ContingencyTables.CompanionObservedUpdateProgram
attribute [local irreducible] output queryInput finishInput
lemma output_take (cs : Configs) (base : Base) (bits : List Bool) :
    output ((cs,base),bits.take (base.1.1.2.length*CompanionObservationQueriesProgram.blockWidth cs))=
      output ((cs,base),bits) := by
  unfold output finishInput queryInput
  rw [CompanionObservationQueriesProgram.output_take]
end ContingencyTables.CompanionObservedUpdateProgram

namespace ContingencyTables.CompanionPhaseTrialProgram
attribute [local irreducible] output updateInput trajectory
  CompanionObservedUpdateProgram.output CompanionTrajectoryProgram.output
lemma output_take (base : Frame×CompanionTrajectoryProgram.Input) (bits : List Bool) :
    output (base,bits.take ((CompanionTrajectoryProgram.output base.2).length*
      CompanionObservationQueriesProgram.blockWidth base.1.1))=output (base,bits) := by
  unfold output updateInput storedInput returnInput trajectory catalogue
  dsimp only
  exact CompanionObservedUpdateProgram.output_take base.1.1
    (((PairedCatalogProgram.catalog base.2.1.1.2,CompanionTrajectoryProgram.output base.2),
      base.1.2.1),base.1.2.2) bits
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrialPadding
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The phase trial with an unused query suffix -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem SameLaw.right_padding {U V Z : Type*} [Fintype U] [Fintype V] {n : ℕ}
    {f : U×(Fin n→Bool)→Z} {g : V→Z} (h : SameLaw f g) (padding : ℕ) :
    SameLaw (fun p : U×(Fin (n+padding)→Bool) => f (p.1,(splitWordEquiv n padding p.2).1)) g := by
  intro phi
  have hh := h phi
  rw [uniformAverage_prod] at hh ⊢
  refine Eq.trans ?_ hh
  apply congrArg uniformAverage
  funext u
  have he := uniformAverage_equiv (splitWordEquiv n padding)
    (fun p : (Fin n→Bool)×(Fin padding→Bool) => phi (f (u,p.1)))
  rw [uniformAverage_prod] at he
  simpa only [uniformAverage_const] using he

end
end ContingencyTables.FiniteObservableTransport

namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma trajectory_length_data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
    (CompanionTrajectoryProgram.output
      (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))).length=N+1 := by
  let state := CompanionFlatReturnProgram.stateData A C K j k xi z v degree depth w S
  let words := CompanionFlatReturnProgram.words
    (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))
  have h := (CompanionCodeBounds.history_bound state words
    (TreeTyped.weight state.2+6*state.1.2.length+1) (by omega) (by omega)).2
  change (CompanionTrajectoryProgram.output
      (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))).length=
      words.length+1 at h
  dsimp only [words] at h
  rw [CompanionFlatReturnProgram.words_data,List.length_ofFn] at h
  exact h

lemma output_data_take (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (walkBits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool)
    (queryBits : List Bool) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
      (List.ofFn walkBits) (queryBits.take ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)))=
    output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
      (List.ofFn walkBits) queryBits) := by
  dsimp only
  have h := output_take
    ((data A C K j k N xi z v degree depth nextDegree nextDepth w E S (List.ofFn walkBits) queryBits).1)
    queryBits
  dsimp only [data] at h
  rw [trajectory_length_data] at h
  exact h


theorem trial_padded_sameLaw (padding : ℕ) (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
        (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs+padding)→Bool) =>
      (output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        (RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old S bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  dsimp only
  have h := trial_sameLaw A C K j k N hC hj hK hW hB xi hxi z v degree depth nextDegree nextDepth
    hdegree hdepth hnextDegree hnextDepth old w E hw hE S
  dsimp only at h
  have hp := h.right_padding padding
  intro phi
  have he (bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
      (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth
        (CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth)+padding)→Bool)) :
      output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))=
      output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn (FairBits.splitWordEquiv _ padding bits.2).1)) := by
    rw [←output_data_take A C K j k N xi z v degree depth nextDegree nextDepth w E S bits.1
      (List.ofFn bits.2),DensePrograms.ofFn_split_take]
  simp_rw [he]
  exact hp phi

end
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContinuation
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuing an adaptive phase from its initialized profile -/
namespace ContingencyTables.CompanionPhaseContinuation
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section

lemma view_getD {p : ℕ} (o : Option Stored) (s : Stored) :
    CompanionPhaseFinishProgram.view (p := p) (o.getD s)=
      (o.map CompanionPhaseFinishProgram.view).getD (CompanionPhaseFinishProgram.view s) := by
  cases o <;> rfl

variable {m n : ℕ}

lemma input_encoded (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (tail : List Bool) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    input cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) tail=
      CompanionPhaseTrialProgram.data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (tail.take (N*CompanionBooleanPhase.stepBits A C K j k xi))
        (tail.drop (N*CompanionBooleanPhase.stepBits A C K j k xi)) := by
  dsimp only
  unfold input width
  change (((_,_),((_,N),tail.take (N*CompanionTransitionWidth.width
    (CompanionMetropolisWordProgram.packed
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) [])))),
    tail.drop (N*CompanionTransitionWidth.width
      (CompanionMetropolisWordProgram.packed
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
        k (encodeSet (coordinateOrder A) S.val) [])))=_
  rw [CompanionTransitionWidth.width_config]
  rfl


theorem run_sameLaw_oai (padding : ℕ) (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi+
        ((N+1)*CompanionObservationQueriesProgram.blockWidth cs+padding))→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        CompanionPhaseFinishProgram.storedView A (pairLabels A)
          ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) old S bits).getD old)) := by
  dsimp only
  let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
  let t := N*CompanionBooleanPhase.stepBits A C K j k xi
  let q := (N+1)*CompanionObservationQueriesProgram.blockWidth cs
  let project := CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
  let oldView := CompanionPhaseFinishProgram.storedView A (pairLabels A) old
  have hold : project (matrixCode w,E)=oldView := by
    apply Prod.ext
    · funext i j
      exact (congrArg TreeFraction.val (readEntry_code w i j)).trans (hw i j)
    · exact hE
  have h := CompanionPhaseTrialProgram.trial_padded_sameLaw padding A C K j k N hC hj hK hW hB
    xi hxi z v degree depth nextDegree nextDepth hdegree hdepth hnextDegree hnextDepth old w E hw hE S
  dsimp only at h
  have hm := h.map (fun o => o.getD oldView)
  intro phi
  have he := uniformAverage_equiv (FairBits.splitWordEquiv t (q+padding))
    (fun p => phi (((CompanionPhaseTrialProgram.output (CompanionPhaseTrialProgram.data A C K j k N
      xi z v degree depth nextDegree nextDepth w E S (List.ofFn p.1) (List.ofFn p.2))).map project).getD oldView))
  have hleft (bits : Fin (t+(q+padding))→Bool) :
      project (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))=
      (((CompanionPhaseTrialProgram.output (CompanionPhaseTrialProgram.data A C K j k N xi z v
        degree depth nextDegree nextDepth w E S
        (List.ofFn (FairBits.splitWordEquiv t (q+padding) bits).1)
        (List.ofFn (FairBits.splitWordEquiv t (q+padding) bits).2))).map project).getD oldView) := by
    unfold run
    rw [input_encoded]
    dsimp only [project] at hold ⊢
    rw [view_getD,hold,DensePrograms.ofFn_split_take,DensePrograms.ofFn_split_drop]
  have hright (bits : RootedPhaseTrial.TrialWords A C K j k N xi) :
      ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) old S bits).map
          (CompanionPhaseFinishProgram.storedView A (pairLabels A))).getD oldView=
      CompanionPhaseFinishProgram.storedView A (pairLabels A)
        ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old S bits).getD old) := by
    cases RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
      (RootedCatalogGrid.gridEquiv A K v) old S bits <;> rfl
  have hl : uniformAverage (fun bits : Fin (t+(q+padding))→Bool =>
      phi (project (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))))=
      uniformAverage (fun p : (Fin t→Bool)×(Fin (q+padding)→Bool) => phi (((CompanionPhaseTrialProgram.output (CompanionPhaseTrialProgram.data A C K j k N
        xi z v degree depth nextDegree nextDepth w E S (List.ofFn p.1) (List.ofFn p.2))).map project).getD oldView)) := by
    simp_rw [hleft]
    exact he
  exact hl.trans ((hm phi).trans (by simp_rw [hright]))

end
end ContingencyTables.CompanionPhaseContinuation

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw_oai := @OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw_oai
