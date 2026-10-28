-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:07:56.952996+00:00
-- url     : https://prove2.me/submissions/5a3b9154-511f-4103-b00f-1a42cb1cd478

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K023
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K025
import Definitions.Def_OAIQ035K026

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalInstanceCost
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

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionGeometry
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

namespace CloseCenters
variable {I} {G O : Finset (Fin I.n)} {δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.completionGeometryPseudoMetricSpace
theorem match_injective (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ < 1/2) :
    Function.Injective C.matchTo := by
  intro t u he
  by_contra htu
  have ht := C.close t
  have hu := C.close u
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have hh := dist_triangle t.val (C.matchTo t) u.val
  rw [he] at ht
  rw [he,dist_comm (C.matchTo u) u.val] at hh
  have hm1 := mul_le_mul_of_nonneg_left hrt hδ
  have hm2 := mul_le_mul_of_nonneg_left hru hδ
  have hd := dist_nonneg (x:=t.val) (y:=u.val)
  have hp := mul_nonneg (show 0 ≤ 1-2*δ by linarith) hd
  linarith only [ht,hu,hh,hm1,hm2,hp]

theorem near_unique (C : CloseCenters I G O δ)
    {t u : ↥G} {j : Fin I.n} (ht : dist j t.val ≤ C.radius t/3)
    (hu : dist j u.val ≤ C.radius u/3) : t=u := by
  by_contra htu
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have htri := dist_triangle t.val j u.val
  rw [dist_comm t.val j] at htri
  have hd0 : dist t.val u.val=0 := by nlinarith only [hrt,hru,htri,ht,hu,dist_nonneg (x:=t.val) (y:=u.val)]
  have hrt0 : C.radius t=0 := by linarith only [hrt,hd0,C.radius_nonneg t]
  have hcl := C.close t
  rw [hrt0,mul_zero] at hcl
  exact (dist_nonneg (x:=t.val) (y:=C.matchTo t)).not_gt hcl

theorem near_match_best (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    {t u : ↥G} {j : Fin I.n} (ht : dist j t.val ≤ C.radius t/3) :
    dist j (C.matchTo t) ≤ dist j (C.matchTo u) := by
  by_cases htu : t=u
  · rw [htu]
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have hct := (C.close t).le
  have hcu := (C.close u).le
  have h1 := dist_triangle j t.val (C.matchTo t)
  have h2 := dist_triangle t.val j (C.matchTo u)
  have h3 := dist_triangle t.val (C.matchTo u) u.val
  rw [dist_comm t.val j] at h2
  rw [dist_comm (C.matchTo u) u.val] at h3
  have hm1 := mul_le_mul_of_nonneg_left hrt hδ
  have hm2 := mul_le_mul_of_nonneg_left hru hδ
  have hm3 := mul_nonneg (show 0 ≤ 1/3-2*δ by linarith)
    (dist_nonneg (x:=t.val) (y:=u.val))
  linarith only [ht,hrt,hct,hcu,h1,h2,h3,hm1,hm2,hm3]

theorem outside_connection (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (t : ↥G) {j a : Fin I.n} (houter : C.radius t/3 ≤ dist j t.val)
    (ha : dist t.val a ≤ δ*C.radius t) :
    dist j a ≤ (1+12*δ)*dist j (C.matchTo t) := by
  have hct := (C.close t).le
  have h1 := dist_triangle j (C.matchTo t) t.val
  rw [dist_comm (C.matchTo t) t.val] at h1
  have h2 := dist_triangle j t.val a
  have hr : C.radius t ≤ 6*dist j (C.matchTo t) := by
    have hm := mul_nonneg (show 0 ≤ 1/6-δ by linarith) (C.radius_nonneg t)
    linarith only [houter,hct,h1,hm]
  have h3 : dist j t.val ≤ dist j (C.matchTo t)+δ*C.radius t := by linarith only [h1,hct]
  have hm := mul_le_mul_of_nonneg_left hr hδ
  nlinarith only [h2,h3,ha,hm]

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_LocalCompletion
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

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

theorem matched_sub (C : CloseCenters I G O δ) : C.matched ⊆ O := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact C.match_mem t

theorem optimal_mem (C : CloseCenters I G O δ) {i : Fin I.n} (hi : i ∈ O) :
    i ∈ C.backup ∨ ∃ t, C.matchTo t=i := by
  by_cases hm : i ∈ C.matched
  · right
    obtain ⟨t,_,he⟩ := mem_image.mp hm
    exact ⟨t,he⟩
  · exact Or.inl (mem_sdiff.mpr ⟨hi,hm⟩)

attribute [local instance] OAI.MetricKMedian.Reduction.localCompletionPseudoMetricSpace
theorem region_disjoint (C : CloseCenters I G O δ) {t u : ↥G} (htu : t ≠ u) :
    Disjoint (C.region t) (C.region u) := by
  apply disjoint_left.mpr
  intro j hjt hju
  exact htu (C.near_unique (mem_filter.mp hjt).2 (mem_filter.mp hju).2)

theorem region_reference (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (hO : O.Nonempty) (t : ↥G) {j : Fin I.n} (hj : j ∈ C.region t) :
    nearest I j (insert (C.matchTo t) C.backup) ≤ nearest I j O := by
  obtain ⟨i,hi,he⟩ := I.nearest_attained j O hO
  rw [he]
  obtain hb | ⟨u,rfl⟩ := C.optimal_mem hi
  · exact I.nearest_le j (mem_insert_of_mem hb)
  · exact (I.nearest_le j (mem_insert_self _ _)).trans
      (C.near_match_best hδ hsmall (mem_filter.mp hj).2)

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionSelection
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

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

attribute [local instance] OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN
theorem complete_of_choices_s35_oai (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
    (a : ↥G → Fin I.n) (ha : ∀ t, a t ∈ F) (hclose : ∀ t, dist t.val (a t) ≤ δ*C.radius t)
    (hloc : ∀ t, (∑ j ∈ C.region t, nearest I j (insert (a t) C.backup)) ≤
      ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup)) :
    let S := C.backup ∪ univ.image a
    S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*δ)*cost I O := by
  classical
  dsimp only
  let S := C.backup ∪ univ.image a
  have hbS : C.backup ⊆ S := subset_union_left
  have haS : ∀ t, a t ∈ S := fun t => mem_union_right _ (mem_image_of_mem a (mem_univ t))
  have hinsert : ∀ t, insert (a t) C.backup ⊆ S := fun t => insert_subset (haS t) hbS
  have hSF : S ⊆ F := by
    intro i hi
    obtain hb | hm := mem_union.mp hi
    · exact hOF (mem_sdiff.mp hb).1
    · obtain ⟨t,_,rfl⟩ := mem_image.mp hm
      exact ha t
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hO
    obtain hb | ⟨t,_⟩ := C.optimal_mem hi
    · exact ⟨i,hbS hb⟩
    · exact ⟨a t,haS t⟩
  have hmcard : C.matched.card=G.card := by
    rw [matched,card_image_of_injective _ (C.match_injective hδ (by linarith)),card_univ,
      Fintype.card_coe]
  have hbudget : S.card ≤ O.card := by
    have he : C.backup.card+G.card=O.card := by
      rw [← hmcard]
      exact card_sdiff_add_card_eq_card C.matched_sub
    calc
      S.card ≤ C.backup.card+(univ.image a).card := card_union_le _ _
      _ ≤ C.backup.card+G.card := by
        apply Nat.add_le_add_left
        simpa only [card_univ,Fintype.card_coe] using card_image_le (f:=a) (s:=univ)
      _ = O.card := he
  refine ⟨hSF,hS,hbudget,?_⟩
  have hlocal : ∀ t, (∑ j ∈ C.region t, nearest I j S) ≤
      ∑ j ∈ C.region t, nearest I j O := by
    intro t
    calc
      _ ≤ ∑ j ∈ C.region t, nearest I j (insert (a t) C.backup) :=
        sum_le_sum (fun j _ => I.nearest_antitone j (insert_nonempty _ _) (hinsert t))
      _ ≤ ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup) := hloc t
      _ ≤ _ := sum_le_sum (fun j hj => C.region_reference hδ hsmall hO t hj)
  let L := univ.biUnion C.region
  have hLsub : L ⊆ I.clients := by
    intro j hj
    obtain ⟨t,_,ht⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp ht).1
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset ↥G)) C.region := by
    intro t _ u _ htu
    exact C.region_disjoint htu
  have hnear : (∑ j ∈ L, nearest I j S) ≤ ∑ j ∈ L, nearest I j O := by
    simp only [L,sum_biUnion hdisj]
    exact sum_le_sum (fun t _ => hlocal t)
  have hfar : ∀ j ∈ I.clients \ L, nearest I j S ≤ (1+12*δ)*nearest I j O := by
    intro j hj
    obtain ⟨hjJ,hjL⟩ := mem_sdiff.mp hj
    obtain ⟨i,hi,he⟩ := I.nearest_attained j O hO
    obtain hb | ⟨t,rfl⟩ := C.optimal_mem hi
    · calc
        nearest I j S ≤ nearest I j O := by rw [he]; exact I.nearest_le j (hbS hb)
        _ ≤ (1+12*δ)*nearest I j O := by
          nlinarith only [I.nearest_nonneg j O,mul_nonneg hδ (I.nearest_nonneg j O)]
    · have hout : C.radius t/3 ≤ dist j t.val := by
        have hn : ¬dist j t.val ≤ C.radius t/3 := by
          intro hn
          exact hjL (mem_biUnion.mpr ⟨t,mem_univ _,mem_filter.mpr ⟨hjJ,hn⟩⟩)
        exact (lt_of_not_ge hn).le
      rw [he]
      exact (I.nearest_le j (haS t)).trans (C.outside_connection hδ hsmall t hout (hclose t))
  have hfarSum : (∑ j ∈ I.clients \ L, nearest I j S) ≤
      (1+12*δ)*∑ j ∈ I.clients \ L, nearest I j O := by
    rw [mul_sum]
    exact sum_le_sum hfar
  have hnearSum : (∑ j ∈ L, nearest I j S) ≤ (1+12*δ)*∑ j ∈ L, nearest I j O := by
    apply hnear.trans
    have hnp : 0 ≤ ∑ j ∈ L, nearest I j O := sum_nonneg (fun j _ => I.nearest_nonneg j O)
    have hp := mul_nonneg hδ hnp
    nlinarith only [hp]
  change (∑ j ∈ I.clients, nearest I j S) ≤ (1+12*δ)*∑ j ∈ I.clients, nearest I j O
  calc
    _ = (∑ j ∈ I.clients \ L, nearest I j S)+(∑ j ∈ L, nearest I j S) := (sum_sdiff hLsub).symm
    _ ≤ (1+12*δ)*(∑ j ∈ I.clients \ L, nearest I j O)+
        (1+12*δ)*(∑ j ∈ L, nearest I j O) := add_le_add hfarSum hnearSum
    _ = _ := by rw [← mul_add,sum_sdiff hLsub]

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices_s35_oai := @OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices_s35_oai
