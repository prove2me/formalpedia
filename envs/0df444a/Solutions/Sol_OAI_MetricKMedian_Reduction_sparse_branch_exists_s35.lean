-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.sparse_branch_exists_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:13:54.600154+00:00
-- url     : https://prove2.me/submissions/a31177ce-830d-4de8-b816-2059199b93f1

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K036

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RadiusPacking
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_Sparsification
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_SparsifyEnumeration
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

attribute [local instance] OAI.MetricKMedian.Reduction.sparsifyEnumerationPseudoMetricSpace
theorem sparse_branch_exists_s35_oai (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
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

theorem solution : type_of% @OAI.MetricKMedian.Reduction.sparse_branch_exists_s35_oai := @OAI.MetricKMedian.Reduction.sparse_branch_exists_s35_oai
