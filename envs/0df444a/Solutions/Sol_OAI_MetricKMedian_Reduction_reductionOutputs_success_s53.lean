-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.reductionOutputs_success_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:22:09.842729+00:00
-- url     : https://prove2.me/submissions/f8ebf32a-7697-4c51-9435-7fceadb1c3d6

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K041
import Theorems.Thm_OAI_MetricKMedian_Reduction_completion_branch_exists_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalInstanceCost
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem nearest_antitone (I : Instance) (j : Fin I.n)
    {S T : Finset (Fin I.n)} (hS : S.Nonempty) (hST : S ⊆ T) :
    nearest I j T ≤ nearest I j S := by
  obtain ⟨i,hi,he⟩ := I.nearest_attained j S hS
  rw [he]
  exact I.nearest_le j (hST hi)

theorem cost_antitone (I : Instance) {S T : Finset (Fin I.n)}
    (hS : S.Nonempty) (hST : S ⊆ T) : cost I T ≤ cost I S :=
  sum_le_sum (fun j _ => I.nearest_antitone j hS hST)

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalThreshold
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem representative_threshold (Q : Finset ℚ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ∈ insert 0 Q, 0 ≤ r ∧ (r:ℝ) ≤ B ∧
      ∀ q ∈ Q, ((q:ℝ) ≤ B ↔ q ≤ r) := by
  classical
  let A : Finset ℚ := insert 0 (Q.filter (fun q : ℚ => (q:ℝ) ≤ B))
  have hA : A.Nonempty := insert_nonempty _ _
  let r := A.max' hA
  have hr : r ∈ A := max'_mem A hA
  have hrB : (r:ℝ) ≤ B := by
    rcases mem_insert.mp hr with hr | hr
    · rw [hr,Rat.cast_zero]; exact hB
    · exact (mem_filter.mp hr).2
  refine ⟨r,?_,?_,hrB,?_⟩
  · rcases mem_insert.mp hr with hr | hr
    · exact mem_insert.mpr (Or.inl hr)
    · exact mem_insert_of_mem (mem_filter.mp hr).1
  · exact le_max' A 0 (mem_insert_self _ _)
  · intro q hq
    constructor
    · intro hqB
      exact le_max' A q (mem_insert_of_mem (mem_filter.mpr ⟨hq,hqB⟩))
    · intro hqr
      exact (show (q:ℝ) ≤ (r:ℝ) by exact_mod_cast hqr).trans hrB

theorem mem_deletionChoices {I : Type} [DecidableEq I] (T D : Finset I) (c : ℕ) :
    D ∈ deletionChoices T c ↔ D ⊆ T ∧ D.card ≤ c := by
  simp only [deletionChoices,mem_biUnion,mem_range,mem_powersetCard]
  constructor
  · rintro ⟨m,hm,hsub,hcard⟩
    exact ⟨hsub,by omega⟩
  · rintro ⟨hsub,hcard⟩
    exact ⟨D.card,by omega,hsub,rfl⟩

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RadiusPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem radius_packing {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (D : Finset X) (r : X → ℝ) (hpos : ∀ i ∈ D, 0 < r i) :
    ∃ P : Finset X, P ⊆ D ∧
      (∀ i ∈ P, ∀ j ∈ P, i ≠ j → r i ≤ dist i j) ∧
      (∀ i ∈ D, ∃ p ∈ P, dist i p < r p ∧ r i ≤ r p) := by
  classical
  revert hpos
  refine D.strongInductionOn ?_
  intro D ih hpos
  by_cases hD : D.Nonempty
  · obtain ⟨i,hi,hmax⟩ := D.exists_max_image r hD
    let E := D.filter (fun j => r i ≤ dist i j)
    have hED : E ⊆ D := filter_subset _ _
    have hiE : i ∉ E := by
      intro hh
      have ht := (mem_filter.mp hh).2
      rw [dist_self] at ht
      exact (hpos i hi).not_ge ht
    have hstrict : E ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hED,by
      intro hh
      exact hiE (hh ▸ hi)⟩
    obtain ⟨P,hPE,hsep,hcover⟩ := ih E hstrict (fun j hj => hpos j (hED hj))
    refine ⟨insert i P,insert_subset hi (hPE.trans hED),?_,?_⟩
    · intro a ha b hb hab
      obtain rfl | haP := mem_insert.mp ha
      · obtain rfl | hbP := mem_insert.mp hb
        · exact (hab rfl).elim
        · exact (mem_filter.mp (hPE hbP)).2
      · obtain rfl | hbP := mem_insert.mp hb
        · have hd := (mem_filter.mp (hPE haP)).2
          rw [dist_comm] at hd
          exact (hmax a (hED (hPE haP))).trans hd
        · exact hsep a haP b hbP hab
    · intro a ha
      by_cases haE : a ∈ E
      · obtain ⟨p,hp,hap,hr⟩ := hcover a haE
        exact ⟨p,mem_insert_of_mem hp,hap,hr⟩
      · have hdist : dist a i < r i := by
          have hn : ¬r i ≤ dist i a := by
            intro hh
            exact haE (mem_filter.mpr ⟨ha,hh⟩)
          simpa only [dist_comm] using lt_of_not_ge hn
        exact ⟨i,mem_insert_self _ _,hdist,hmax a ha⟩
  · refine ⟨∅,empty_subset _,?_,?_⟩
    · simp
    · intro i hi
      exact (hD ⟨i,hi⟩).elim

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_Sparsification
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

attribute [local instance] OAI.MetricKMedian.Reduction.sparsificationPseudoMetricSpace
theorem nearest_triangle {O : Finset (Fin I.n)} (hO : O.Nonempty) (i j : Fin I.n) :
    nearest I i O ≤ dist i j+nearest I j O := by
  obtain ⟨o,ho,he⟩ := I.nearest_attained j O hO
  rw [he]
  exact (I.nearest_le i ho).trans (dist_triangle i j o)

theorem denseBall_cost {O : Finset (Fin I.n)} (hO : O.Nonempty) (i : Fin I.n) :
    nearest I i O*(denseBall (I:=I) O i).card ≤
      (3/2:ℝ)*∑ j ∈ denseBall (I:=I) O i, nearest I j O := by
  have hp : ∀ j ∈ denseBall (I:=I) O i, nearest I i O ≤ (3/2:ℝ)*nearest I j O := by
    intro j hj
    have hnear := (mem_filter.mp hj).2
    have hh := nearest_triangle hO i j
    rw [dist_comm i j] at hh
    linarith only [hnear,hh]
  have hs := sum_le_sum hp
  simp only [sum_const,nsmul_eq_mul,← mul_sum] at hs
  simpa only [mul_comm (nearest I i O)] using hs

theorem denseBall_disjoint {O : Finset (Fin I.n)} {i p : Fin I.n}
    (hi : nearest I i O ≤ dist i p) (hp : nearest I p O ≤ dist i p) :
    Disjoint (denseBall (I:=I) O i) (denseBall (I:=I) O p) := by
  apply disjoint_left.mpr
  intro j hj1 hj2
  have h1 := (mem_filter.mp hj1).2
  have h2 := (mem_filter.mp hj2).2
  have ht := dist_triangle i j p
  rw [dist_comm i j] at ht
  have hn := dist_nonneg (x:=i) (y:=p)
  linarith only [hi,hp,h1,h2,ht,hn]

theorem sparsify (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hcost : 0 < cost I O) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ P : Finset (Fin I.n), P ⊆ F ∧ (P.card:ℝ)*ρ ≤ 3/2 ∧
      let F' := F.filter (fun i => ∀ p ∈ P, nearest I p O ≤ dist p i)
      O ⊆ F' ∧ Sparse (I:=I) F' O ρ := by
  classical
  let D := F.filter (fun i => ρ*cost I O < nearest I i O*(denseBall (I:=I) O i).card)
  have hpos : ∀ i ∈ D, 0 < nearest I i O := by
    intro i hi
    have hd := (mem_filter.mp hi).2
    have hh : 0 < nearest I i O*(denseBall (I:=I) O i).card := (mul_pos hρ hcost).trans hd
    exact (mul_pos_iff.mp hh).elim (fun h => h.1) (fun h => (h.2.not_ge (Nat.cast_nonneg _)).elim)
  obtain ⟨P,hPD,hsep,hcover⟩ := radius_packing D (fun i => nearest I i O) hpos
  have hPF : P ⊆ F := hPD.trans (filter_subset _ _)
  have hdisj : Set.PairwiseDisjoint (↑P) (denseBall (I:=I) O) := by
    intro i hi p hp hip
    have h1 := hsep i hi p hp hip
    have h2 := hsep p hp i hi (Ne.symm hip)
    rw [dist_comm p i] at h2
    exact denseBall_disjoint h1 h2
  have hpoint : ∀ p ∈ P, ρ*cost I O ≤ (3/2:ℝ)*∑ j ∈ denseBall (I:=I) O p, nearest I j O := by
    intro p hp
    exact (mem_filter.mp (hPD hp)).2.le.trans (denseBall_cost hO p)
  have hsum := sum_le_sum hpoint
  simp only [sum_const,nsmul_eq_mul,← mul_sum,← sum_biUnion hdisj] at hsum
  have hJ : P.biUnion (denseBall (I:=I) O) ⊆ I.clients := by
    intro j hj
    obtain ⟨p,_,hp⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hp).1
  have hcostUnion : (∑ j ∈ P.biUnion (denseBall (I:=I) O), nearest I j O) ≤ cost I O :=
    sum_le_sum_of_subset_of_nonneg hJ (fun j _ _ => I.nearest_nonneg j O)
  have hcount : (P.card:ℝ)*ρ ≤ 3/2 := by
    apply (mul_le_mul_iff_left₀ hcost).mp
    have hh := hsum.trans (mul_le_mul_of_nonneg_left hcostUnion (by norm_num : (0:ℝ) ≤ 3/2))
    nlinarith only [hh]
  refine ⟨P,hPF,hcount,?_,?_⟩
  · intro o ho
    exact mem_filter.mpr ⟨hOF ho,fun p _ => I.nearest_le p ho⟩
  · intro i hi
    by_contra hn
    have hiD : i ∈ D := mem_filter.mpr ⟨(mem_filter.mp hi).1,lt_of_not_ge hn⟩
    obtain ⟨p,hp,hclose,_⟩ := hcover i hiD
    have hfar := (mem_filter.mp hi).2 p hp
    rw [dist_comm i p] at hclose
    exact hclose.not_ge hfar

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_SparsifyEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem sparseBranches_sub (I : Instance) (F : Finset (Fin I.n)) (b : ℕ)
    {F' : Finset (Fin I.n)} (h : F' ∈ sparseBranches I F b) : F' ⊆ F := by
  obtain ⟨P,_,rfl⟩ := mem_image.mp h
  exact filter_subset _ _

variable {I : Instance}

attribute [local instance] OAI.MetricKMedian.Reduction.sparsifyEnumerationPseudoMetricSpace
theorem sparse_branch_exists (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hcost : 0 < cost I O) (ρ : ℝ) (hρ : 0 < ρ) (b : ℕ) (hb : (3/2:ℝ) ≤ b*ρ) :
    ∃ F' ∈ sparseBranches I F b, O ⊆ F' ∧ Sparse (I:=I) F' O ρ := by
  classical
  obtain ⟨P,hPF,hcount,hOP,hsp⟩ := sparsify F O hOF hO hcost ρ hρ
  have hcard : P.card ≤ b := by
    have hh : (P.card:ℝ) ≤ b := (mul_le_mul_iff_left₀ hρ).mp (hcount.trans hb)
    exact_mod_cast hh
  choose q hq he using fun p : Fin I.n => I.nearest_attained p O hO
  let W := P.image (fun p => (p,q p))
  have hWsub : W ⊆ F ×ˢ F := by
    intro w hw
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
    exact mem_product.mpr ⟨hPF hp,hOF (hq p)⟩
  have hWcard : W.card ≤ b := (card_image_le).trans hcard
  have hWeq : witnessedRestriction I F W=F.filter (fun i => ∀ p ∈ P, nearest I p O ≤ dist p i) := by
    ext i
    simp only [witnessedRestriction,mem_filter]
    constructor
    · rintro ⟨hi,hh⟩
      refine ⟨hi,fun p hp => ?_⟩
      have hqdist := hh (p,q p) (mem_image_of_mem _ hp)
      change I.distance p (q p) ≤ I.distance p i at hqdist
      rw [he p]
      change (I.distance p (q p):ℝ) ≤ (I.distance p i:ℝ)
      exact_mod_cast hqdist
    · rintro ⟨hi,hh⟩
      refine ⟨hi,fun w hw => ?_⟩
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hw
      have hd := hh p hp
      rw [he p] at hd
      change (I.distance p (q p):ℝ) ≤ (I.distance p i:ℝ) at hd
      exact_mod_cast hd
  refine ⟨_,mem_image_of_mem _ ((mem_deletionChoices _ _ _).mpr ⟨hWsub,hWcard⟩),?_,?_⟩
  · rw [hWeq]; exact hOP
  · rw [hWeq]; exact hsp

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionHistory
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem deletion_value_mem (I : Instance) (T U : Finset (Fin I.n)) (c : ℕ)
    (hUT : U ⊆ T) (hcount : T.card-U.card ≤ c) {i : Fin I.n} (hi : i ∈ U) :
    rationalCost I (U.erase i)-rationalCost I U ∈ deletionValues I T c := by
  have hd : T \ U ∈ deletionChoices T c := (mem_deletionChoices T (T \ U) c).mpr
    ⟨sdiff_subset,by rw [card_sdiff_of_subset hUT]; exact hcount⟩
  have he : T \ (T \ U)=U := by
    ext a
    simp only [mem_sdiff]
    exact ⟨fun h => by tauto,fun h => ⟨hUT h,by tauto⟩⟩
  exact mem_biUnion.mpr ⟨T \ U,hd,mem_image.mpr ⟨i,hUT hi,by rw [he]⟩⟩

theorem deleteStep_cases (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    deleteStep I B U=U ∨ ∃ i ∈ U, deleteStep I B U=U.erase i := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · right
    refine ⟨_,?_,rfl⟩
    exact (mem_filter.mp (min'_mem _ he)).1
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem deleteStep_subset (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    deleteStep I B U ⊆ U := by
  rcases deleteStep_cases I B U with he | ⟨i,_,he⟩
  · rw [he]
  · rw [he]; exact erase_subset _ _

theorem deleteStep_card (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    U.card ≤ (deleteStep I B U).card+1 := by
  rcases deleteStep_cases I B U with he | ⟨i,hi,he⟩
  · rw [he]; omega
  · rw [he,card_erase_add_one hi]

theorem deleteStep_congr (I : Instance) (B B' : ℝ) (U : Finset (Fin I.n))
    (htest : ∀ i ∈ U,
      (((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B ↔
       ((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B')) :
    deleteStep I B U=deleteStep I B' U := by
  classical
  have he : eligible I B U=eligible I B' U := by
    ext i
    simp only [eligible,mem_filter]
    exact and_congr_right (htest i)
  unfold deleteStep
  rw [he]

theorem history_bounds (I : Instance) (B : ℝ) (T : Finset (Fin I.n)) (t : ℕ) :
    deletionHistory I B T t ⊆ T ∧ T.card ≤ (deletionHistory I B T t).card+t := by
  induction t with
  | zero => exact ⟨Subset.rfl,le_rfl⟩
  | succ t ih =>
    refine ⟨(deleteStep_subset I B _).trans ih.1,?_⟩
    have hc := deleteStep_card I B (deletionHistory I B T t)
    change T.card ≤ (deleteStep I B (deletionHistory I B T t)).card+(t+1)
    omega

theorem enumerate_ideal_history (I : Instance) (T : Finset (Fin I.n)) (c : ℕ)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ∈ insert 0 (deletionValues I T c),
      ∀ t ≤ c, deletionHistory I B T t=deletionHistory I (r:ℝ) T t := by
  obtain ⟨r,hr,_,_,htest⟩ := representative_threshold (deletionValues I T c) hB
  refine ⟨r,hr,?_⟩
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro htc
    have ht : t ≤ c := by omega
    have hist := ih ht
    simp only [deletionHistory]
    apply (deleteStep_congr I B (r:ℝ) (deletionHistory I B T t) ?_).trans
      (congrArg (deleteStep I (r:ℝ)) hist)
    intro i hi
    have hb := history_bounds I B T t
    have hm := deletion_value_mem I T (deletionHistory I B T t) c hb.1 (by omega) hi
    exact (htest _ hm).trans (by exact_mod_cast (Iff.rfl :
      rationalCost I ((deletionHistory I B T t).erase i)-rationalCost I (deletionHistory I B T t) ≤ r ↔
      rationalCost I ((deletionHistory I B T t).erase i)-rationalCost I (deletionHistory I B T t) ≤ r))

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionEndpoint
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)

theorem step_cost {B : ℝ} (hB : 0 ≤ B) (U : Finset (Fin I.n)) :
    cost I (deleteStep I B U) ≤ cost I U+B := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · have hmem := mem_filter.mp (min'_mem (eligible I B U) he)
    have hh := hmem.2
    rw [Rat.cast_sub,I.cast_rationalCost,I.cast_rationalCost] at hh
    linarith only [hh]
  · linarith only [hB]
  · linarith only [hB]

theorem step_budget_lower (B : ℝ) (U : Finset (Fin I.n)) (hU : I.k ≤ U.card) :
    I.k ≤ (deleteStep I B U).card := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · have hi := (mem_filter.mp (min'_mem (eligible I B U) he)).1
    rw [card_erase_of_mem hi]
    omega
  · exact hU
  · exact hU

theorem history_budget_lower (B : ℝ) (T : Finset (Fin I.n)) (hT : I.k ≤ T.card) (t : ℕ) :
    I.k ≤ (deletionHistory I B T t).card := by
  induction t with
  | zero => exact hT
  | succ t ih => exact step_budget_lower I B _ ih

theorem history_cost {B : ℝ} (hB : 0 ≤ B) (T : Finset (Fin I.n)) (t : ℕ) :
    cost I (deletionHistory I B T t) ≤ cost I T+(t:ℝ)*B := by
  induction t with
  | zero => simp only [deletionHistory,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ t ih =>
    have hh := step_cost I hB (deletionHistory I B T t)
    change cost I (deletionHistory I B T (t+1)) ≤ _ at hh
    push_cast
    linarith only [ih,hh]

theorem history_fixed (B : ℝ) (T : Finset (Fin I.n))
    (hfix : deleteStep I B T=T) (t : ℕ) : deletionHistory I B T t=T := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [deletionHistory,ih,hfix]

theorem history_succ_left (B : ℝ) (T : Finset (Fin I.n)) (t : ℕ) :
    deletionHistory I B T (t+1)=deletionHistory I B (deleteStep I B T) t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [deletionHistory] using congrArg (deleteStep I B) ih

theorem history_endpoint (B : ℝ) (T : Finset (Fin I.n)) (c : ℕ)
    (hT : T.card ≤ I.k+c) :
    let U := deletionHistory I B T c
    U.card ≤ I.k ∨ ∀ i ∈ U, B < cost I (U.erase i)-cost I U := by
  classical
  dsimp only
  induction c generalizing T with
  | zero =>
    left
    simpa only [deletionHistory,Nat.add_zero] using hT
  | succ c ih =>
    by_cases hk : I.k < T.card
    · by_cases he : (eligible I B T).Nonempty
      · let i := (eligible I B T).min' he
        have hi : i ∈ T := (mem_filter.mp (min'_mem _ he)).1
        have hstep : deleteStep I B T=T.erase i := by
          simp only [deleteStep,ite_eq_left hk,dite_eq_left he,i]
        have hcard : (deleteStep I B T).card ≤ I.k+c := by
          rw [hstep,card_erase_of_mem hi]
          omega
        rw [history_succ_left]
        exact ih _ hcard
      · have hfix : deleteStep I B T=T := by simp only [deleteStep,ite_eq_left hk,dite_eq_right he]
        rw [history_fixed I B T hfix (c+1)]
        right
        intro i hi
        have hn : ¬ ((rationalCost I (T.erase i)-rationalCost I T:ℚ):ℝ) ≤ B := by
          intro hh
          exact he ⟨i,mem_filter.mpr ⟨hi,hh⟩⟩
        rw [Rat.cast_sub,I.cast_rationalCost,I.cast_rationalCost] at hn
        exact lt_of_not_ge hn
    · have hfix : deleteStep I B T=T := by simp only [deleteStep,ite_eq_right hk]
      rw [history_fixed I B T hfix (c+1)]
      exact Or.inl (le_of_not_gt hk)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalDeletion
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem cast_rationalEligible (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    rationalEligible I B U=eligible I (B:ℝ) U := by
  ext i
  simp only [rationalEligible,eligible,mem_filter,Rat.cast_le]

theorem cast_rationalStep (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    rationalDeleteStep I B U=deleteStep I (B:ℝ) U := by
  simp only [rationalDeleteStep,deleteStep,cast_rationalEligible]

theorem cast_rationalHistory (I : Instance) (B : ℚ) (T : Finset (Fin I.n)) (t : ℕ) :
    rationalHistory I B T t=deletionHistory I (B:ℝ) T t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [rationalHistory,deletionHistory,cast_rationalStep,ih]

theorem ideal_endpoint_mem (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    deletionHistory I B T c ∈ deletionEndpoints I T c := by
  obtain ⟨r,hr,hh⟩ := enumerate_ideal_history I T c hB
  exact mem_image.mpr ⟨r,hr,(cast_rationalHistory I r T c).trans (hh c le_rfl).symm⟩

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseReduction
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

local instance sparseReductionPseudoMetric_rbc3878_1 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
theorem sparse_outcome_exists (F O T : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hTF : T ⊆ F) (hT : T.Nonempty)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I T ≤ α*cost I O) (hcard : T.card ≤ I.k+c)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hfactor : 1+12*(δ:ℝ) ≤ α+η) (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ sparseOutcomes I F T δ c b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*cost I O := by
  classical
  by_cases hTk : T.card ≤ I.k
  · refine ⟨T,mem_insert_self _ _,hTF,hT,hTk,?_⟩
    have hηC := mul_nonneg hη.le hC.le
    nlinarith only [hcost,hηC]
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  let B := η*cost I O/c
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hη.le hC.le) hcR.le
  let U := deletionHistory I B T c
  have hUc : I.k ≤ U.card := history_budget_lower I B T (by omega) c
  have hUne : U.Nonempty := card_pos.mp (I.k_pos.trans hUc)
  have hUF : U ⊆ F := (history_bounds I B T c).1.trans hTF
  have hUcst : cost I U ≤ (α+η)*cost I O := by
    have hhistory := history_cost I hB T c
    have hcancel : (c:ℝ)*B=η*cost I O := by dsimp only [B]; field_simp
    rw [hcancel] at hhistory
    nlinarith only [hhistory,hcost]
  have hUm : U ∈ deletionEndpoints I T c := ideal_endpoint_mem I T c hB
  obtain hUk | hstuck := history_endpoint I B T c hcard
  · refine ⟨U,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_self _ _⟩),hUF,hUne,hUk,hUcst⟩
  · by_cases hUk : U.card ≤ I.k
    · exact ⟨U,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_self _ _⟩),hUF,hUne,hUk,hUcst⟩
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := completion_branch_exists_s53 F O U hOF hO hk hUF
      (by omega) (α+η) η δ c b hc hδ hsmall hη hC hUcst hsp (fun i hi => (hstuck i hi).le) hb
    refine ⟨S,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_of_mem hS⟩),hSF,hSne,hSk,?_⟩
    exact hSc.trans (mul_le_mul_of_nonneg_right hfactor hC.le)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_BudgetReduction
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem padded_optimum (I : Instance) :
    ∃ O, O ⊆ I.facilities ∧ O.Nonempty ∧ O.card=I.k ∧ cost I O=optimum I := by
  obtain ⟨S,hSF,hS,hSk,hSc⟩ := I.optimum_attained
  obtain ⟨O,hSO,hOF,hOk⟩ := exists_subsuperset_card_eq hSF hSk I.k_le
  have hO := hS.mono hSO
  refine ⟨O,hOF,hO,hOk,le_antisymm ?_ (I.optimum_le hOF hO hOk.le)⟩
  exact (I.cost_antitone hS hSO).trans_eq hSc

theorem restrict_optimum (I : Instance) (F O : Finset (Fin I.n))
    (hF : I.k ≤ F.card) (hFF : F ⊆ I.facilities) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hOk : O.card ≤ I.k) (hcost : cost I O=optimum I) :
    optimum (I.restrictFacilities F hF)=optimum I := by
  apply le_antisymm
  · exact ((I.restrictFacilities F hF).optimum_le hOF hO hOk).trans_eq hcost
  · obtain ⟨S,hS,hSne,hSk,hSc⟩ := (I.restrictFacilities F hF).optimum_attained
    exact (I.optimum_le (hS.trans hFF) hSne hSk).trans_eq hSc

end Instance

namespace Reduction

theorem reductionOutputs_success_s53_oai
    (pseudo : (I : Instance) → Finset (Fin I.n)) (α η : ℝ) (δ : ℚ) (c a b : ℕ)
    (hc : 0 < c) (hδ : 0 < (δ:ℝ)) (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η)
    (hfactor : 1+12*(δ:ℝ) ≤ α+η)
    (ha : (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)))
    (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ))
    (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I)
    (I : Instance) (hopt : 0 < optimum I) :
    ∃ S ∈ reductionOutputs pseudo I δ c a b,
      S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*optimum I := by
  let : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
  obtain ⟨O,hOF,hO,hOk,hOc⟩ := I.padded_optimum
  have hC : 0 < cost I O := by rwa [hOc]
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hρ : 0 < (δ:ℝ)*η/(2*c) := div_pos (mul_pos hδ hη) (by positivity)
  obtain ⟨F,hF,hOF',hsp⟩ := sparse_branch_exists I.facilities O hOF hO hC
    ((δ:ℝ)*η/(2*c)) hρ a ha
  have hFk : I.k ≤ F.card := hOk.symm.le.trans (card_le_card hOF')
  have hFF := sparseBranches_sub I I.facilities a hF
  have hop : optimum (I.restrictFacilities F hFk)=optimum I :=
    I.restrict_optimum F O hFk hFF hOF' hO hOk.le hOc
  obtain ⟨hTF,hT,hTc,hTv⟩ := hpseudo (I.restrictFacilities F hFk)
  change cost I (pseudo (I.restrictFacilities F hFk)) ≤ α*optimum (I.restrictFacilities F hFk) at hTv
  rw [hop,← hOc] at hTv
  obtain ⟨S,hSm,hSF,hS,hSk,hSc⟩ := sparse_outcome_exists F O
    (pseudo (I.restrictFacilities F hFk)) hOF' hO hOk hTF hT α η δ c b hc hδ hsmall hη
    hC hTv hTc hsp hfactor hb
  refine ⟨S,mem_biUnion.mpr ⟨F,hF,?_⟩,hSF.trans hFF,hS,hSk,?_⟩
  · simp only [dite_eq_left hFk]
    exact hSm
  · rwa [hOc] at hSc

end Reduction
end MetricKMedian
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Reduction.reductionOutputs_success_s53_oai := @OAI.MetricKMedian.Reduction.reductionOutputs_success_s53_oai
