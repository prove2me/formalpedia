-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:13:09.054971+00:00
-- url     : https://prove2.me/submissions/29aac1a3-1a30-44ad-8cf4-b37dfb2b458e

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K032
import Definitions.Def_OAIQ035K036
import Theorems.Thm_OAI_MetricKMedian_Reduction_CloseCenters_complete_of_choices_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalLocalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem pickSingleton_spec {X : Type*} [LinearOrder X] (K : Finset X) (w : X → ℚ)
    (hK : K.Nonempty) : ∃ a ∈ K, pickSingleton K w={a} ∧ ∀ b ∈ K, w a ≤ w b := by
  let m := (K.image w).min' (hK.image w)
  let A := K.filter (fun a => w a=m)
  have hA : A.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (K.image w) (hK.image w))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  let a := A.min' hA
  have ha := mem_filter.mp (min'_mem A hA)
  refine ⟨a,ha.1,?_,?_⟩
  · simp only [pickSingleton,dite_eq_left hK,a,A,m]
  · intro b hb
    rw [show w a=m from ha.2]
    exact min'_le _ _ (mem_image_of_mem w hb)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalCompletion
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
variable {G O : Finset (Fin I.n)} {δ : ℚ}

attribute [local instance] OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN_1
theorem rationalRegion_eq (C : CloseCenters I G O (δ:ℝ)) (r : Fin I.n → ℚ)
    (hr : ∀ t, C.radius t=(r t.val:ℝ)) (t : ↥G) :
    rationalRegion I r t.val=C.region t := by
  ext j
  simp only [rationalRegion,region,mem_filter]
  apply and_congr_right
  intro _
  rw [hr t]
  change 3*I.distance j t.val ≤ r t.val ↔ (I.distance j t.val:ℝ) ≤ (r t.val:ℝ)/3
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<3)]
  constructor
  · intro h
    have hh : (3:ℝ)*(I.distance j t.val:ℝ) ≤ (r t.val:ℝ) := by exact_mod_cast h
    linarith only [hh]
  · intro h
    have hh : (3:ℝ)*(I.distance j t.val:ℝ) ≤ (r t.val:ℝ) := by linarith only [h]
    exact_mod_cast hh

theorem cast_localWeight (C : CloseCenters I G O (δ:ℝ)) (r : Fin I.n → ℚ)
    (hr : ∀ t, C.radius t=(r t.val:ℝ)) (t : ↥G) (a : Fin I.n) :
    (localWeight I r C.backup t.val a:ℝ)=∑ j ∈ C.region t, nearest I j (insert a C.backup) := by
  simp only [localWeight,Rat.cast_sum,I.cast_rationalNearest,C.rationalRegion_eq r hr]

theorem completionSet_spec_s35_oai (C : CloseCenters I G O (δ:ℝ)) (hδ : 0 ≤ (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
    (r : Fin I.n → ℚ) (hr : ∀ t, C.radius t=(r t.val:ℝ)) :
    let S := completionSet I F C.backup G r δ
    S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O := by
  classical
  have hm : ∀ t : ↥G, C.matchTo t ∈ rationalCandidates I F r δ t.val := by
    intro t
    refine mem_filter.mpr ⟨hOF (C.match_mem t),?_⟩
    have hc := (C.close t).le
    rw [hr t] at hc
    change (I.distance t.val (C.matchTo t):ℝ) ≤ (δ:ℝ)*(r t.val:ℝ) at hc
    exact_mod_cast hc
  have hs := fun t : ↥G => pickSingleton_spec (rationalCandidates I F r δ t.val)
    (localWeight I r C.backup t.val) ⟨C.matchTo t,hm t⟩
  choose a ha he hmin using hs
  have hF : ∀ t, a t ∈ F := fun t => (mem_filter.mp (ha t)).1
  have hclose : ∀ t, dist t.val (a t) ≤ (δ:ℝ)*C.radius t := by
    intro t
    rw [hr t]
    change (I.distance t.val (a t):ℝ) ≤ (δ:ℝ)*(r t.val:ℝ)
    exact_mod_cast (mem_filter.mp (ha t)).2
  have hloc : ∀ t, (∑ j ∈ C.region t, nearest I j (insert (a t) C.backup)) ≤
      ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup) := by
    intro t
    rw [← C.cast_localWeight r hr t (a t),← C.cast_localWeight r hr t (C.matchTo t)]
    exact_mod_cast hmin t (C.matchTo t) (hm t)
  have heq : G.biUnion (localChoice I F C.backup r δ)=univ.image a := by
    ext i
    constructor
    · intro hi
      obtain ⟨t,ht,hi⟩ := mem_biUnion.mp hi
      change i ∈ pickSingleton _ _ at hi
      rw [he ⟨t,ht⟩,mem_singleton] at hi
      exact mem_image.mpr ⟨⟨t,ht⟩,mem_univ _,hi.symm⟩
    · intro hi
      obtain ⟨t,_,rfl⟩ := mem_image.mp hi
      apply mem_biUnion.mpr
      refine ⟨t.val,t.property,?_⟩
      change a t ∈ pickSingleton _ _
      rw [he t]
      exact mem_singleton_self _
  dsimp only
  simp only [completionSet,heq]
  exact C.complete_of_choices_s35 hδ hsmall hO F hOF a hF hclose hloc

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s35_oai := @OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s35_oai
