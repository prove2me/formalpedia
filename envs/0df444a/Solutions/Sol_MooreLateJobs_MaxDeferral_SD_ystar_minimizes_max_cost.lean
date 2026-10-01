-- Prove2me | solution 1 for MooreLateJobs.MaxDeferral.SD_ystar_minimizes_max_cost
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:42:07.614202+00:00
-- url     : https://prove2.me/submissions/1c473e25-1c6e-4a31-a188-5f19642946a3

import Definitions.Def_MooreLateJobs_MaxDeferral_NoLateAt
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.BigOperators.Group.List
import Definitions.Def_MooreLateJobs_MaxDeferral_maxCost
import Mathlib.Data.List.Permutation
section

open MooreLateJobs Shared MaxDeferral Finset
namespace CMoore
variable {ι : Type*} [DecidableEq ι]

theorem completion_cons (t : ι → ℝ) (a j : ι) (l : List ι) (h : a ≠ j) :
    completionTime t (a::l) j = t a + completionTime t l j := by
  simp [completionTime, completionAt, List.idxOf_cons_ne _ h]

theorem selected_total_le (t : ι → ℝ) (l : List ι) (K : Finset ι)
    (hK : K.Nonempty) (hKl : ∀ j ∈ K, j ∈ l) (ht : ∀ j ∈ l, 0 ≤ t j)
    (c : ℝ) (B : EReal) (hb : ∀ j ∈ K, ((c+completionTime t l j : ℝ) : EReal) ≤ B) :
    ((c+∑ j ∈ K, t j : ℝ) : EReal) ≤ B := by
  classical
  induction l generalizing K c with
  | nil => obtain ⟨j,hj⟩ := hK; simpa using hKl j hj
  | cons a l ih =>
    have hKt : ∀ j ∈ K.erase a, j ∈ l := by
      intro j hj
      have hx := hKl j (Finset.mem_of_mem_erase hj)
      exact (List.mem_cons.mp hx).resolve_left (Finset.ne_of_mem_erase hj)
    by_cases he : (K.erase a).Nonempty
    · have hh := ih (K.erase a) he hKt (fun j hj => ht j (List.mem_cons_of_mem _ hj)) (c+t a) (by
        intro j hj
        have h := hb j (Finset.mem_of_mem_erase hj)
        rw [completion_cons t a j l (Finset.ne_of_mem_erase hj).symm] at h
        simpa only [add_assoc] using h)
      by_cases ha : a ∈ K
      · rw [← Finset.add_sum_erase K t ha]
        simpa only [add_assoc] using hh
      · rw [Finset.erase_eq_of_notMem ha] at hh
        exact le_trans (EReal.coe_le_coe_iff.mpr (by linarith [ht a List.mem_cons_self])) hh
    · have hKe : K.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      have hKa : K = {a} := by
        ext j
        constructor
        · intro hj
          have : j = a := by by_contra h; have hx := Finset.mem_erase.mpr ⟨h,hj⟩; rw [hKe] at hx; exact Finset.notMem_empty _ hx
          simpa [this]
        · intro hj
          have hja : j=a := Finset.mem_singleton.mp hj
          obtain ⟨k,hk⟩ := hK
          have hka : k=a := by by_contra h; have hx := Finset.mem_erase.mpr ⟨h,hk⟩; rw [hKe] at hx; exact Finset.notMem_empty _ hx
          simpa [hja,hka] using hk
      have hh := hb a (by simp [hKa])
      simpa [hKa,completionTime,completionAt] using hh

theorem prefix_deadline (D : ι → EReal) (l : List ι) (hs : l.Pairwise (fun a b => D a ≤ D b))
    (j : ι) (hj : j ∈ l) : ∀ k ∈ l.take (l.idxOf j+1), D k ≤ D j := by
  induction l with
  | nil => simp at hj
  | cons a l ih =>
    rcases List.pairwise_cons.mp hs with ⟨ha,hl⟩
    by_cases he : a=j
    · subst a
      simpa using (show ∀ k ∈ [j], D k ≤ D j by simp)
    · have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm he)
      rw [List.idxOf_cons_ne _ he, List.take_succ_cons]
      intro k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact ha j hjl
      · exact ih hl hjl k hk

theorem sorted_feasible (t : ι → ℝ) (D : ι → EReal) (J : Finset ι)
    (ht : ∀ i ∈ J, 0 ≤ t i) (l s : List ι)
    (hl : IsSchedule J l) (hs : IsSchedule J s) (hsl : s.Pairwise (fun a b => D a ≤ D b))
    (hf : NoLate t D l) : NoLate t D s := by
  intro j hj
  apply not_lt.mpr
  let K := (s.take (s.idxOf j+1)).toFinset
  have hKj : j ∈ K := by
    apply List.mem_toFinset.mpr
    exact (List.mem_take_iff_idxOf_lt hj).mpr (by omega)
  have hKl : ∀ k ∈ K, k ∈ l := by
    intro k hk
    exact (hl.2 k).mpr ((hs.2 k).mp (List.mem_of_mem_take (List.mem_toFinset.mp hk)))
  have hb : ∀ k ∈ K, ((0+completionTime t l k : ℝ) : EReal) ≤ D j := by
    intro k hk
    simp only [zero_add]
    exact (not_lt.mp (hf k (hKl k hk))).trans
      (prefix_deadline D s hsl j hj k (List.mem_toFinset.mp hk))
  have hh := selected_total_le t l K ⟨j,hKj⟩ hKl (fun k hk => ht k ((hl.2 k).mp hk)) 0 (D j) hb
  simpa only [zero_add, K, List.sum_toFinset _ (hs.1.take), completionTime, completionAt] using hh

theorem exists_sorted (J : Finset ι) (D : ι → EReal) :
    ∃ s : List ι, IsSchedule J s ∧ s.Pairwise (fun a b => D a ≤ D b) := by
  classical
  let s := J.toList.mergeSort (fun a b => decide (D a ≤ D b))
  have hp : s.Perm J.toList := List.mergeSort_perm _ _
  refine ⟨s,⟨hp.nodup_iff.mpr J.nodup_toList, fun j => hp.mem_iff.trans Finset.mem_toList⟩,?_⟩
  apply List.pairwise_mergeSort'

theorem jackson (J : Finset ι) (t : ι → ℝ) (D : ι → EReal) (ht : ∀ i ∈ J, 0 ≤ t i) :
    (∃ S : List ι, IsSchedule J S ∧ NoLate t D S) ↔
      ∀ S : List ι, IsSchedule J S → S.Pairwise (fun a b => D a ≤ D b) → NoLate t D S := by
  constructor
  · rintro ⟨l,hl,hf⟩ s hs hsl
    exact sorted_feasible t D J ht l s hl hs hsl hf
  · intro h
    obtain ⟨s,hs,hsl⟩ := exists_sorted J D
    exact ⟨s,hs,h s hs hsl⟩

end CMoore
end

section

open MooreLateJobs Shared MaxDeferral
namespace CMoore

theorem pstar_nonneg (f : ℝ → ℝ) (y : ℝ) : (0 : EReal) ≤ Pstar f y := by
  classical
  unfold Pstar
  split_ifs with h hb hall
  · obtain ⟨s,hs,hsy⟩ := h
    exact le_trans (by exact_mod_cast hs) (EReal.coe_le_coe_iff.mpr (le_csSup hb ⟨hs,hsy⟩))
  · exact le_top
  · exact le_rfl
  · exact le_top

theorem pstar_iff (f : ℝ → ℝ) (hf : Continuous f) (hm : Monotone f) (y s : ℝ) (hs : 0 ≤ s) :
    (s : EReal) ≤ Pstar f y ↔ s=0 ∨ f s ≤ y := by
  classical
  by_cases hs0 : s=0
  · simp [hs0,pstar_nonneg]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hzero : ¬ (s : EReal) ≤ 0 := by exact_mod_cast (not_le.mpr hspos)
  by_cases hlev : ∃ u, 0 ≤ u ∧ f u=y
  · obtain ⟨u,hu,huy⟩ := hlev
    by_cases hb : BddAbove {u | 0 ≤ u ∧ f u=y}
    · have hc : IsClosed {u | 0 ≤ u ∧ f u=y} :=
        (isClosed_le continuous_const continuous_id).inter (isClosed_eq hf continuous_const)
      have hmax := hc.csSup_mem ⟨u,hu,huy⟩ hb
      rw [Pstar, if_pos ⟨u,hu,huy⟩, if_pos hb, EReal.coe_le_coe_iff]
      simp only [hs0,false_or]
      constructor
      · intro h
        exact (hm h).trans_eq hmax.2
      · intro h
        by_cases he : f s=y
        · exact le_csSup hb ⟨hs,he⟩
        · have hsu : s ≤ u := by
            by_contra hlt
            have := hm (le_of_lt (lt_of_not_ge hlt))
            rw [huy] at this
            exact he (le_antisymm h this)
          exact hsu.trans (le_csSup hb ⟨hu,huy⟩)
    · rw [Pstar,if_pos ⟨u,hu,huy⟩,if_neg hb]
      simp only [le_top,true_iff,hs0,false_or]
      obtain ⟨v,hv,hsv⟩ := not_bddAbove_iff.mp hb s
      exact (hm hsv.le).trans_eq hv.2
  · by_cases hall : ∀ u, 0 ≤ u → y < f u
    · rw [Pstar,if_neg hlev,if_pos hall]
      simp only [hzero,hs0,false_or,false_iff,not_le]
      exact hall s hs
    · rw [Pstar,if_neg hlev,if_neg hall]
      simp only [le_top,true_iff,hs0,false_or]
      push_neg at hall
      obtain ⟨u,hu,huy⟩ := hall
      by_contra hbad
      have hys : y < f s := lt_of_not_ge hbad
      have hus : u ≤ s := by
        by_contra h
        have := hm (le_of_lt (lt_of_not_ge h))
        linarith
      obtain ⟨v,hv,hvy⟩ := intermediate_value_Icc hus hf.continuousOn ⟨huy,hys.le⟩
      exact hlev ⟨v,hu.trans hv.1,hvy⟩

variable {ι : Type*} [DecidableEq ι]

theorem completion_nonneg (t : ι → ℝ) (l : List ι) (ht : ∀ i ∈ l, 0 ≤ t i) (j : ι) :
    0 ≤ completionTime t l j := by
  unfold completionTime completionAt
  apply List.sum_nonneg
  intro x hx
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
  exact ht k (List.mem_of_mem_take hk)

theorem noLateAt_iff (t : ι → ℝ) (P : ι → ℝ → ℝ) (l : List ι)
    (ht : ∀ i ∈ l, 0 ≤ t i) (hc : ∀ i ∈ l, Continuous (P i))
    (hm : ∀ i ∈ l, Monotone (P i)) (y : ℝ) :
    NoLateAt t P y l ↔ ∀ j ∈ l, completionTime t l j=0 ∨ P j (completionTime t l j) ≤ y := by
  unfold NoLateAt NoLate IsLate dueDates
  simp only [not_lt]
  exact forall₂_congr fun j hj => pstar_iff (P j) (hc j hj) (hm j hj) y _ (completion_nonneg t l ht j)

end CMoore
end

section

open MooreLateJobs Shared MaxDeferral Finset
namespace CMoore
variable {ι : Type*} [DecidableEq ι]

theorem max_deferral (J : Finset ι) (hJ : J.Nonempty) (t : ι → ℝ) (P : ι → ℝ → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (hc : ∀ i ∈ J, Continuous (P i)) (hm : ∀ i ∈ J, Monotone (P i))
    (SD : ℝ → List ι) (hSD : ∀ y, 0 < y → IsSchedule J (SD y) ∧
      (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y))
    (v : ℝ) (hv : 0 < v) (h1 : NoLateAt t P v (SD v))
    (h2 : ∀ y, 0 < y → y < v → ¬ NoLateAt t P y (SD y)) :
    ∀ l : List ι, IsSchedule J l → maxCost t P J hJ (SD v) ≤ maxCost t P J hJ l := by
  intro l hl
  have hsv := (hSD v hv).1
  have hchar := (noLateAt_iff t P (SD v) (fun i hi => ht i ((hsv.2 i).mp hi))
    (fun i hi => hc i ((hsv.2 i).mp hi)) (fun i hi => hm i ((hsv.2 i).mp hi)) v).mp h1
  apply Finset.sup'_le
  intro j hj
  have hlower : P j (completionTime t l j) ≤ maxCost t P J hJ l :=
    Finset.le_sup' (fun j => P j (completionTime t l j)) hj
  rcases hchar j ((hsv.2 j).mpr hj) with he|hle
  · rw [he]
    exact (hm j hj (completion_nonneg t l (fun i hi => ht i ((hl.2 i).mp hi)) j)).trans hlower
  · have hvle : v ≤ maxCost t P J hJ l := by
      by_contra hbad
      have hbad : maxCost t P J hJ l < v := lt_of_not_ge hbad
      let y := (max 0 (maxCost t P J hJ l)+v)/2
      have hy : 0 < y := by dsimp [y]; linarith [le_max_left 0 (maxCost t P J hJ l)]
      have hyv : y < v := by dsimp [y]; have := max_lt hv hbad; linarith
      have hmy : maxCost t P J hJ l ≤ y := by
        dsimp [y]
        have := le_max_right 0 (maxCost t P J hJ l)
        have := max_lt hv hbad
        linarith
      have hly : NoLateAt t P y l := by
        apply (noLateAt_iff t P l (fun i hi => ht i ((hl.2 i).mp hi))
          (fun i hi => hc i ((hl.2 i).mp hi)) (fun i hi => hm i ((hl.2 i).mp hi)) y).mpr
        intro i hi
        exact Or.inr ((Finset.le_sup' (fun j => P j (completionTime t l j)) ((hl.2 i).mp hi)).trans hmy)
      have hsy : NoLateAt t P y (SD y) :=
        sorted_feasible t (dueDates P y) J ht l (SD y) hl (hSD y hy).1 (hSD y hy).2 hly
      exact h2 y hy hyv hsy
    exact hle.trans hvle

theorem finite_schedules (J : Finset ι) : {l : List ι | IsSchedule J l}.Finite := by
  classical
  apply (J.toList.permutations.toFinset.finite_toSet).subset
  intro l hl
  apply List.mem_toFinset.mpr
  apply List.mem_permutations.mpr
  apply (List.perm_ext_iff_of_nodup hl.1 J.nodup_toList).mpr
  intro j
  exact (hl.2 j).trans Finset.mem_toList.symm

theorem feasible_levels_closed (J : Finset ι) (t : ι → ℝ) (P : ι → ℝ → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (hc : ∀ i ∈ J, Continuous (P i)) (hm : ∀ i ∈ J, Monotone (P i)) :
    IsClosed {y : ℝ | ∃ l : List ι, IsSchedule J l ∧ NoLateAt t P y l} := by
  have he : {y : ℝ | ∃ l : List ι, IsSchedule J l ∧ NoLateAt t P y l} =
      ⋃ l ∈ {l : List ι | IsSchedule J l}, {y : ℝ | NoLateAt t P y l} := by ext y; simp
  rw [he]
  apply (finite_schedules J).isClosed_biUnion
  intro l hl
  have he' : {y : ℝ | NoLateAt t P y l} =
      ⋂ j ∈ l, {y : ℝ | completionTime t l j=0 ∨ P j (completionTime t l j) ≤ y} := by
    ext y
    simp only [Set.mem_setOf_eq,Set.mem_iInter]
    exact noLateAt_iff t P l (fun i hi => ht i ((hl.2 i).mp hi))
      (fun i hi => hc i ((hl.2 i).mp hi)) (fun i hi => hm i ((hl.2 i).mp hi)) y
  rw [he']
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro hj
  by_cases heq : completionTime t l j=0
  · simp [heq]
  · simpa [heq, Set.Ici] using (isClosed_Ici : IsClosed (Set.Ici (P j (completionTime t l j))))

theorem exists_threshold (J : Finset ι) (t : ι → ℝ) (P : ι → ℝ → ℝ)
    (ht : ∀ i ∈ J, 0 ≤ t i) (hc : ∀ i ∈ J, Continuous (P i)) (hm : ∀ i ∈ J, Monotone (P i))
    (SD : ℝ → List ι) (hSD : ∀ y, 0 < y → IsSchedule J (SD y) ∧
      (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y))
    (hfeas : ∃ y, 0 < y ∧ NoLateAt t P y (SD y))
    (hinf : ∃ y, 0 < y ∧ ¬ NoLateAt t P y (SD y)) :
    ∃ v, 0 < v ∧ NoLateAt t P v (SD v) ∧ ∀ y, 0 < y → y < v → ¬ NoLateAt t P y (SD y) := by
  classical
  let A : Set ℝ := {y | ∃ l : List ι, IsSchedule J l ∧ NoLateAt t P y l}
  obtain ⟨y0,hy0,hno⟩ := hinf
  obtain ⟨y1,hy1,hyes⟩ := hfeas
  have hne : A.Nonempty := ⟨y1,SD y1,(hSD y1 hy1).1,hyes⟩
  have hlo : ∀ y ∈ A, y0 ≤ y := by
    rintro y ⟨l,hl,hy⟩
    by_contra hbad
    have hyy : y ≤ y0 := le_of_lt (lt_of_not_ge hbad)
    have hly0 : NoLateAt t P y0 l := by
      rw [noLateAt_iff t P l (fun i hi => ht i ((hl.2 i).mp hi))
        (fun i hi => hc i ((hl.2 i).mp hi)) (fun i hi => hm i ((hl.2 i).mp hi))] at hy ⊢
      intro j hj
      exact (hy j hj).imp_right (fun h => h.trans hyy)
    apply hno
    exact sorted_feasible t (dueDates P y0) J ht l (SD y0) hl (hSD y0 hy0).1 (hSD y0 hy0).2 hly0
  have hbd : BddBelow A := ⟨y0,hlo⟩
  have hmin : sInf A ∈ A := (feasible_levels_closed J t P ht hc hm).csInf_mem hne hbd
  have hv : 0 < sInf A := hy0.trans_le (le_csInf hne hlo)
  refine ⟨sInf A,hv,?_,?_⟩
  · obtain ⟨l,hl,hf⟩ := hmin
    exact sorted_feasible t (dueDates P (sInf A)) J ht l (SD (sInf A)) hl
      (hSD (sInf A) hv).1 (hSD (sInf A) hv).2 hf
  · intro y hy hyv h
    exact (not_le_of_gt hyv) (csInf_le hbd ⟨SD y,(hSD y hy).1,h⟩)

end CMoore
end

open MooreLateJobs Shared MaxDeferral


theorem solution {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (hJ : J.Nonempty) (t : ι → ℝ) (P : ι → ℝ → ℝ) (ht : ∀ i ∈ J, 0 ≤ t i)
    (hcont : ∀ i ∈ J, Continuous (P i)) (hbdd : ∀ i ∈ J, ∃ M, ∀ s, |P i s| ≤ M)
    (hmono : ∀ i ∈ J, Monotone (P i)) (SD : ℝ → List ι)
    (hSD : ∀ y, 0 < y →
      Shared.IsSchedule J (SD y) ∧ (SD y).Pairwise (fun a b => Pstar (P a) y ≤ Pstar (P b) y))
    (ystar : ℝ) (hystar : 0 < ystar) (h1 : NoLateAt t P ystar (SD ystar))
    (h2 : ∀ y, 0 < y → y < ystar → ¬ NoLateAt t P y (SD y)) :
    ∀ l : List ι, Shared.IsSchedule J l → maxCost t P J hJ (SD ystar) ≤ maxCost t P J hJ l := by
  exact CMoore.max_deferral J hJ t P ht hcont hmono SD hSD ystar hystar h1 h2


