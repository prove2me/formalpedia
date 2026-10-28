-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:34:14.432196+00:00
-- url     : https://prove2.me/submissions/594dc0a5-dc49-4e1d-82e0-8e1647aecc6e

import Mathlib
import Definitions.Def_OAIQ035K062
import Theorems.Thm_OAI_MetricKMedian_Preparation_RationalUnitInput_scan_spec_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset RationalIntervals
variable {I J : Type} [Fintype I] [Fintype J]

theorem cost_assignment (y : I → ℚ) (x : J → I → ℚ) (hx0 : ∀ j i, 0 ≤ x j i)
    (j : J) (d : I → ℝ) :
    (∑ a ∈ assignment y x j, (weight y x a:ℝ)*d a.1)=∑ i, (x j i:ℝ)*d i := by
  rw [assignment,sum_filter,Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  have he : (∑ q : ↥(cuts y x i), if q.val ≤ x j i then (length (cuts y x i) q.val:ℝ) else 0)=(x j i:ℝ) := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) (assigned_fiber y x hx0 j i)
    push_cast at hh
    simpa only [apply_ite, Rat.cast_zero] using hh
  calc
    _ = (∑ q : ↥(cuts y x i), if q.val ≤ x j i then (length (cuts y x i) q.val:ℝ) else 0)*d i := by
      rw [sum_mul]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp only [weight,zero_mul]
    _ = _ := by rw [he]

end MetricKMedian.Preparation.RationalSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalSplitEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset RationalIntervals
variable {f j : ℕ}

theorem sum_fiber_nonneg (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hx : ∀ c i, x c i≤y i) (i : Fin f) :
    (∑ q : ↥(cuts y x i), length (cuts y x i) q.val)=y i := by
  by_cases h : 0<y i
  · rw [sum_coe_sort,sum_lengths _ (cuts_pos y x i)]
    exact height_eq _ (y i) (mem_filter.mpr ⟨mem_insert_self _ _,h⟩) h.le (cuts_le y x hx i)
  · have hz : y i=0 := le_antisymm (le_of_not_gt h) (hy i)
    have he : cuts y x i=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hle := cuts_le y x hx i q hq
      have hp := cuts_pos y x i q hq
      linarith only [hle,hp,hz]
    rw [sum_coe_sort,he,sum_empty,hz]

theorem sum_weight_nonneg (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hx : ∀ c i, x c i≤y i) :
    (∑ a, weight y x a)=∑ i, y i := by
  rw [Fintype.sum_sigma]
  exact sum_congr rfl (fun i _ => sum_fiber_nonneg y x hy hx i)

theorem weights_sum (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hy : ∀ i, 0≤y i) (hx : ∀ c i, x c i≤y i) :
    (∑ a, weights y x a)=∑ i, y i :=
  ((index y x).sum_comp (weight y x)).trans (sum_weight_nonneg y x hy hx)

end MetricKMedian.Preparation.RationalSplitting
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalSplitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Preparation.RationalSplitting
open Finset
variable {f j : ℕ}

 theorem cost_assigned (y : Fin f → ℚ) (x : Fin j → Fin f → ℚ)
    (hx0 : ∀ c i, 0≤x c i) (dc : Fin j → Fin f → ℚ) (c : Fin j) :
    (∑ a ∈ assigned y x c, weights y x a*dc c (original y x a))=∑ i, x c i*dc c i := by
  change (∑ a ∈ assigned y x c, (fun a : Piece y x => weight y x a*dc c a.1) (index y x a))=_
  rw [assigned_sum y x c (fun a : Piece y x => weight y x a*dc c a.1)]
  have hh := cost_assignment y x hx0 c (fun i => (dc c i:ℝ))
  exact_mod_cast hh

end MetricKMedian.Preparation.RationalSplitting
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalFractionalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

 theorem input_mass (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    (∑ b, (unitInput a k ha hj dc dd df hdc hdd hds).y b)≤(k:ℚ)+1 := by
  change (∑ b, RationalSplitting.weights (y a) (x a k ha hj dc) b)≤_
  exact (RationalSplitting.weights_sum (y a) (x a k ha hj dc) (fun i => (ha.1 i).1)
    (fun c i => ((x_spec a k ha hj dc).1 c i).2)).trans_le ha.2.2.2

 theorem input_cost (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    (∑ c, (unitInput a k ha hj dc dd df hdc hdd hds).V c)≤a.value dc := by
  have he : ∀ c, (unitInput a k ha hj dc dd df hdc hdd hds).V c=
      ∑ i, x a k ha hj dc c i*dc c i := fun c => RationalSplitting.cost_assigned (y a) (x a k ha hj dc)
        (fun c i => ((x_spec a k ha hj dc).1 c i).1) dc c
  simp_rw [he]
  exact (x_spec a k ha hj dc).2.2.2

end FractionalRefinement
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalImageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational
open Finset
variable {F H : Type} [DecidableEq H] {j : ℕ}

theorem score_image (d : Fin j → H → ℚ) (f : F → H) (O : Finset F) :
    score d (O.image f)=score (fun c a => d c (f a)) O := by
  unfold score
  apply sum_congr rfl
  intro c _
  by_cases hO : O.Nonempty
  · rw [dite_eq_left (hO.image f),dite_eq_left hO]
    simp only [image_image]
    rfl
  · have hI : ¬(O.image f).Nonempty := by simpa only [image_nonempty] using hO
    rw [dite_eq_right hO,dite_eq_right hI]

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalFractionalScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c b, dist (client c) (i b)=(dc c b:ℝ))
    (hcc : ∀ c c', dist (client c) (client c')=(dd c c':ℝ))
    {η τ : ℝ} (p : RationalAllParameters η τ)

theorem scan_spec_s35_oai (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin f), scan a k ha hj dc dd df hdc hdd hds i client hdf hc hcc p (k+C)=some O ∧
      O.Nonempty ∧ O.card≤k+C ∧ (Completion.Rational.score dc O:ℝ) ≤
        ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value dc:ℝ) := by
  classical
  let U := unitInput a k ha hj dc dd df hdc hdd hds
  let R := realization a k ha hj dc dd df hdc hdd hds i client hdf hc hcc
  have hm : (∑ b, (U.y b:ℝ))≤(k:ℝ)+1 := by
    exact_mod_cast input_mass a k ha hj dc dd df hdc hdd hds
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := U.scan_spec_s35 R p hτ0 hτ hj ((k:ℚ)+C) (by
    push_cast
    linarith only [hm,hC])
  refine ⟨O.image (original a k ha hj dc),?_,hOn.image _,?_,?_⟩
  · change (U.scan R p ((k:ℚ)+C)).map (fun O => O.image (original a k ha hj dc))=_
    rw [hO]
    rfl
  · have hOk : O.card≤k+C := by exact_mod_cast hOc
    exact (card_image_le).trans hOk
  · rw [Completion.Rational.score_image]
    change (Completion.Rational.score U.dc O:ℝ)≤_
    exact hOs.trans (mul_le_mul_of_nonneg_left
      (show (∑ c, (U.V c:ℝ))≤(a.value dc:ℝ) by
        exact_mod_cast input_cost a k ha hj dc dd df hdc hdd hds)
      (mul_nonneg (div_nonneg (by positivity) (by linarith only [hτ])) (by linarith only [hη])))

end MetricKMedian.Preparation.FractionalRefinement
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35_oai := @OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec_s35_oai
