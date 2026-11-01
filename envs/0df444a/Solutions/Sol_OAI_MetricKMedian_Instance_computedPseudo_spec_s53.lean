-- Prove2me | solution 1 for OAI.MetricKMedian.Instance.computedPseudo_spec_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:40:17.791902+00:00
-- url     : https://prove2.me/submissions/58de322f-20dc-42ec-926c-a7a5568ce574

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K058
import Theorems.Thm_OAI_MetricKMedian_Preparation_RationalBundles_scan_geometry_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalSplitting
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalSplitEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

theorem representative_cover (M : ℚ) (hM : 0≤M) (c : Fin j) :
    ∃ t, U.V (U.ridx M t)≤U.V c ∧ U.dd c (U.ridx M t)≤M*U.V c := by
  obtain ⟨s,hs,hV,hd⟩ :=
    (RationalRepresentatives.representatives_spec U.dd U.V M U.hdd U.hsymm hM U.V_nonneg).2 c
  let t := ((U.representatives M).orderIsoOfFin rfl).symm ⟨s,hs⟩
  have ht : U.ridx M t=s := congrArg Subtype.val
    (((U.representatives M).orderIsoOfFin rfl).apply_symm_apply ⟨s,hs⟩)
  exact ⟨t,ht ▸ hV,ht ▸ hd⟩

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalSplitInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalFractionalInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalImageCost
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitScan
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

theorem scan_spec (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j) (B : ℚ)
    (hB : (∑ a, (U.y a:ℝ))+3*(p.round.g:ℝ)+(p.round.allowance:ℝ) ≤ (B:ℝ)) :
    ∃ O : Finset (Fin f), U.scan R p B=some O ∧ O.Nonempty ∧ (O.card:ℝ)≤(B:ℝ) ∧
      (Completion.Rational.score U.dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(∑ c, (U.V c:ℝ)) := by
  classical
  choose rep hV hd using U.representative_cover p.M p.hM.le
  obtain ⟨O,hO,hOn,hOc,hCost⟩ := RationalBundles.scan_geometry_s53 p.round p.even hτ0 hτ hj
    (fun t => U.F (U.ridx p.M t)) U.F U.y (fun t => R.c (U.ridx p.M t)) R.i R.c
    (fun t u => U.dd (U.ridx p.M t) (U.ridx p.M u)) (fun t a => U.dc (U.ridx p.M t) a)
    U.df U.dc (fun t => U.V (U.ridx p.M t)) U.V rep p.M p.δ p.γ p.T₁ B
    (fun t u => R.hdd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => R.hdc (U.ridx p.M t) a) R.hdf R.hdc U.hy U.hy1
    p.hM p.hδ p.hδ1 p.hθ p.hγ p.hγ1 p.hT p.hα p.failure hB
    (fun t => U.hu (U.ridx p.M t)) (fun _ => rfl) U.hu (fun _ => rfl)
    (U.representative_separation p.M p.hM.le)
    (fun t => U.hnear (U.ridx p.M t)) hV
    (fun c => by rw [R.hdd]; exact_mod_cast hd c)
  refine ⟨O,hO,hOn,hOc,hCost.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun c _ => by exact_mod_cast U.V_nonneg c))
  apply mul_le_mul_of_nonneg_left p.error
  exact div_nonneg (by positivity) (by linarith only [hτ])

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalFractionalScan
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem scan_spec (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin f), scan a k ha hj dc dd df hdc hdd hds i client hdf hc hcc p (k+C)=some O ∧
      O.Nonempty ∧ O.card≤k+C ∧ (Completion.Rational.score dc O:ℝ) ≤
        ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value dc:ℝ) := by
  classical
  let U := unitInput a k ha hj dc dd df hdc hdd hds
  let R := realization a k ha hj dc dd df hdc hdd hds i client hdf hc hcc
  have hm : (∑ b, (U.y b:ℝ))≤(k:ℝ)+1 := by
    exact_mod_cast input_mass a k ha hj dc dd df hdc hdd hds
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := U.scan_spec R p hτ0 hτ hj ((k:ℚ)+C) (by
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

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalIndexedCost
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceFractionalRound
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceComputedPseudo
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

 theorem computedPseudo_spec_s53_oai (I : Instance) (r : ℕ) (hr : 0 < r)
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

theorem solution : type_of% @OAI.MetricKMedian.Instance.computedPseudo_spec_s53_oai := @OAI.MetricKMedian.Instance.computedPseudo_spec_s53_oai
