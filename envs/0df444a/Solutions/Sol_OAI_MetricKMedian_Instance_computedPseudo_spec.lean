-- Prove2me | solution 1 for OAI.MetricKMedian.Instance.computedPseudo_spec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:54:21.615998+00:00
-- url     : https://prove2.me/submissions/c5f92725-d818-491b-9a55-50f800608874
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K062
import Theorems.Thm_OAI_MetricKMedian_Preparation_FractionalRefinement_scan_spec

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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalIndexedCost
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Instance
open Finset

 theorem indexed_score (I : Instance) (S : Finset (Fin I.n)) :
    Completion.Rational.score (fun c : Fin I.clients.card => I.distance (I.clients.orderEmbOfFin rfl c)) S
      = rationalCost I S := by
  unfold Completion.Rational.score
  calc
    _ = ∑ c : Fin I.clients.card, rationalNearest I (I.clients.orderEmbOfFin rfl c) S := rfl
    _ = ∑ c : ↥I.clients, rationalNearest I c.val S :=
      (I.clients.orderIsoOfFin rfl).toEquiv.sum_comp (fun c => rationalNearest I c.val S)
    _ = rationalCost I S := sum_coe_sort I.clients (fun c => rationalNearest I c S)

 theorem indexed_score_image (I : Instance) (O : Finset (Fin I.facilities.card)) :
    Completion.Rational.score I.indexedDistance O=
      rationalCost I (O.image (I.facilities.orderEmbOfFin rfl)) := by
  rw [← indexed_score,Completion.Rational.score_image]
  rfl

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceFractionalRound
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 theorem fractionalRound_spec (I : Instance) (a : TruncatedLP.FractionalData I.facilities.card I.clients.card)
    (ha : a.Valid I.k) (hj : I.clients.Nonempty) {η τ : ℝ} (p : RationalAllParameters η τ)
    (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin I.n), I.fractionalRound a ha hj p C=some O ∧
      O⊆I.facilities ∧ O.Nonempty ∧ O.card≤I.k+C ∧
       cost I O≤((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value I.indexedDistance:ℝ) := by
  let := I.pseudoMetric
  obtain ⟨O,hO,hOn,hOc,hCost⟩ := FractionalRefinement.scan_spec a I.k ha (card_pos.mpr hj)
    I.indexedDistance I.clientDistance I.facilityDistance I.indexedDistance_nonneg
    I.clientDistance_self I.clientDistance_comm (I.facilities.orderEmbOfFin rfl) (I.clients.orderEmbOfFin rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p hη hτ0 hτ C hC
  refine ⟨O.image (I.facilities.orderEmbOfFin rfl),?_,?_,hOn.image _,card_image_le.trans hOc,?_⟩
  · unfold fractionalRound
    rw [hO]
    rfl
  · intro b hb
    obtain ⟨u,_,rfl⟩ := mem_image.mp hb
    exact I.facilities.orderEmbOfFin_mem rfl u
  · rw [I.indexed_score_image, I.cast_rationalCost] at hCost
    exact hCost

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceComputedPseudo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Instance
open Finset Preparation

 theorem nonzeroRound_spec (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin I.n), I.nonzeroRound h r hr p C=some O ∧
      O⊆I.facilities ∧ O.Nonempty ∧ O.card≤I.k+C ∧
      cost I O≤(((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(1+3/(r:ℝ)))*optimum I := by
  obtain ⟨O,hO,hOF,hOn,hOk,hCost⟩ := I.fractionalRound_spec _
    (I.nonzeroFractional_spec h r hr).1 (I.nonzero_clients h) p hη hτ0 hτ C hC
  refine ⟨O,hO,hOF,hOn,hOk,hCost.trans ?_⟩
  rw [mul_assoc _ (1+3/(r:ℝ))]
  apply mul_le_mul_of_nonneg_left (I.nonzeroFractional_spec h r hr).2
  exact mul_nonneg (div_nonneg (by positivity) (by linarith only [hτ])) (by linarith only [hη])

 theorem computedPseudo_spec_oai (I : Instance) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
      (I.computedPseudo r hr p C).card≤I.k+C ∧
      cost I (I.computedPseudo r hr p C)≤
        (((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(1+3/(r:ℝ)))*optimum I := by
  unfold computedPseudo
  split_ifs with h
  · obtain ⟨hOF,hOn,hOk,hCost⟩ := I.zeroOutput_spec h
    refine ⟨hOF,hOn,hOk.trans (Nat.le_add_right _ _),?_⟩
    rw [hCost,(I.zeroTest_iff.mp h),mul_zero]
  · obtain ⟨O,hO,hOF,hOn,hOk,hCost⟩ := I.nonzeroRound_spec h r hr p hη hτ0 hτ C hC
    rw [hO]
    exact ⟨hOF,hOn,hOk,hCost⟩

end MetricKMedian.Instance
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Instance.computedPseudo_spec_oai := @OAI.MetricKMedian.Instance.computedPseudo_spec_oai
