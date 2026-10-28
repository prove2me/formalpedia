-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:32:01.91198+00:00
-- url     : https://prove2.me/submissions/9b20d165-d7be-4b1e-835b-367af8e78b94

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_dilation_balance_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
lemma measurePreserving_torusIter (k : ℝ) (i : ℤ) : MeasurePreserving (torusIter k i) area area := by
  cases i with
  | ofNat n =>
      change MeasurePreserving (torusIter k (n : ℤ)) area area
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (measurePreserving_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (measurePreserving_torusStep_symm k).iterate (n+1)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology Classical
namespace StandardMapEntropy
lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
lemma epsilon_pos (i : ℕ) : 0 < S.epsilon i := (criticalTheta_pos S.offset i).trans (S.threshold i)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RescaledArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma continuous_sampleArray (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) : Continuous (fun z => sampleArray k hk z n hn) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact (continuous_productDistance k hk _ _).div_const _
lemma sampleArray_translate (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    arrayTranslate r (sampleArray k hk z n hn)=sampleArray k hk (torusIter k a z) n hn := by
  apply Subtype.ext
  funext s t
  change productDistance k z ⌊(n:ℝ)*(↑(s+r):ℝ)⌋ ⌊(n:ℝ)*(↑(t+r):ℝ)⌋/(n:ℝ)=
    productDistance k (torusIter k a z) ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋/(n:ℝ)
  rw [productDistance_shift]
  simp only [AddSubgroup.coe_add,mul_add,ha,Int.floor_add_intCast]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SampleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
instance sampleLawProbability (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    IsProbabilityMeasure (sampleLaw k hk n hn) := by
  unfold sampleLaw
  exact (Measure.isProbabilityMeasure_map_iff (continuous_sampleArray k hk n hn).measurable.aemeasurable).2 inferInstance
lemma integral_sampleLaw (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) (F : DistanceArray → ℝ)
    (hF : Continuous F) :
    (∫ d,F d ∂sampleLaw k hk n hn)=∫ z,F (sampleArray k hk z n hn) ∂area :=
  integral_map_of_stronglyMeasurable (continuous_sampleArray k hk n hn).measurable hF.stronglyMeasurable
lemma sampleLaw_translate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    (sampleLaw k hk n hn).map (arrayTranslate r)=sampleLaw k hk n hn := by
  unfold sampleLaw
  rw [Measure.map_map (continuous_arrayTranslate r).measurable (continuous_sampleArray k hk n hn).measurable]
  have he : (arrayTranslate r) ∘ (fun z => sampleArray k hk z n hn)=
      (fun z => sampleArray k hk z n hn) ∘ (torusIter k a) := by
    funext z; exact sampleArray_translate k hk z n hn r a ha
  rw [he,← Measure.map_map (continuous_sampleArray k hk n hn).measurable (continuous_torusIter k a).measurable,
    (measurePreserving_torusIter k a).map_eq]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable instance scaleLawFinite (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) :
    IsFiniteMeasure (scaleLaw k hk p l ε) := by
  unfold scaleLaw
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top
lemma integral_scaleLaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (F : DistanceArray → ℝ) (hF : Continuous F) :
    (∫ d,F d ∂scaleLaw k hk p l ε)=(∑ i∈Finset.range l,∫ d,F d ∂sampleLaw k hk (2^(p+i)) (by positivity))/ε := by
  rw [scaleLaw,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/ε)]
  rw [integral_finsetSum_measure]
  · simp only [smul_eq_mul]; ring
  · intro i hi
    exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma scaleLaw_translate (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (r : DyadicTime)
    (a : ℤ) (ha : ((2^p:ℕ):ℝ)*(r:ℝ)=(a:ℝ)) :
    (scaleLaw k hk p l ε).map (arrayTranslate r)=scaleLaw k hk p l ε := by
  unfold scaleLaw
  rw [Measure.map_smul,Measure.map_finset_sum (continuous_arrayTranslate r).measurable.aemeasurable]

  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply sampleLaw_translate k hk _ _ r (a*2^i)
  push_cast at ha ⊢
  rw [pow_add]
  calc
    _ = (((2:ℝ)^p)*(r:ℝ))*(2:ℝ)^i := by ring
    _ = _ := by rw [ha]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleTestBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma dyadic_aligned_eventually (s : DyadicTime) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀≤p → ∃ a : ℤ, ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ) := by
  obtain ⟨p₀,a,ha⟩ := dyadicTime_mem s
  refine ⟨p₀,fun p hp => ⟨a*2^(p-p₀),?_⟩⟩
  push_cast
  have he : (2:ℝ)^p=(2:ℝ)^p₀*2^(p-p₀) := by rw [← pow_add,Nat.add_sub_of_le hp]
  rw [ha,he]
  field_simp
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
instance initialLaw_finite (i : ℕ) : IsFiniteMeasure (S.initialLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance terminalLaw_finite (i : ℕ) : IsFiniteMeasure (S.terminalLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance multiLaw_finite (i : ℕ) : IsFiniteMeasure (S.multiLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
lemma lowerExponent_tendsto : Tendsto (criticalLowerExponent S.offset) atTop atTop := by
  apply tendsto_atTop_mono (f := fun i : ℕ => i) _ tendsto_id
  intro i
  unfold criticalLowerExponent
  omega
lemma exponent_tendsto : Tendsto S.exponent atTop atTop := tendsto_atTop_mono (fun i => (S.lower_lt i).le) S.lowerExponent_tendsto
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTestExtend_affine (g : C_c(NonAffineArray,ℝ)) (d : DistanceArray) (hd : d∈affineLocus) :
    arrayTestExtend g d=0 := by
  apply Function.extend_apply' _ _ _
  rintro ⟨u,rfl⟩
  exact u.property hd
lemma integral_arrayTestExtend (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (g : C_c(NonAffineArray,ℝ)) : (∫ d,arrayTestExtend g d ∂μ)=∫ d,g d ∂nonaffinePart μ := by
  have he : (∫ d,g d ∂nonaffinePart μ)=∫ d in affineLocusᶜ,arrayTestExtend g d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet (arrayTestExtend g) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [arrayTestExtend_apply]
    rfl
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro d hd
  exact arrayTestExtend_affine g d (not_not.mp hd)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LimitActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTestExtend_translate (g : C_c(NonAffineArray,ℝ)) (r : DyadicTime) (d : DistanceArray) :
    arrayTestExtend (g.comp (nonaffineTranslation r).toCocompactMap) d=
      arrayTestExtend g (arrayTranslate r d) := by
  by_cases hd : d∈affineLocus
  · rw [arrayTestExtend_affine _ d hd,arrayTestExtend_affine _ _ ((arrayTranslate_mem_affine_iff r d).mpr hd)]
  · exact (arrayTestExtend_apply _ ⟨d,hd⟩).trans (arrayTestExtend_apply g (nonaffineTranslation r ⟨d,hd⟩)).symm
lemma integral_translate_nonaffine (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (r : DyadicTime) (hμ : μ.map (arrayTranslate r)=μ) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart μ)=
      ∫ d,g d ∂nonaffinePart μ := by
  rw [← integral_arrayTestExtend,← integral_arrayTestExtend]
  simp_rw [arrayTestExtend_translate]
  rw [← integral_map (f := fun d => arrayTestExtend g d) (continuous_arrayTranslate r).measurable.aemeasurable (arrayTestExtend g).continuous.aestronglyMeasurable,hμ]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma multiLaw_translate_eventually (r : DyadicTime) :
    ∀ᶠ i in atTop, (S.multiLaw i).map (arrayTranslate r)=S.multiLaw i := by
  obtain ⟨p,hp⟩ := dyadic_aligned_eventually r
  filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p] with i hi
  obtain ⟨a,ha⟩ := hp _ hi
  exact scaleLaw_translate _ _ _ _ _ r a ha
lemma terminalLaw_translate_eventually (r : DyadicTime) :
    ∀ᶠ i in atTop, (S.terminalLaw i).map (arrayTranslate r)=S.terminalLaw i := by
  obtain ⟨p,hp⟩ := dyadic_aligned_eventually r
  filter_upwards [S.exponent_tendsto.eventually_ge_atTop p] with i hi
  obtain ⟨a,ha⟩ := hp _ hi
  exact scaleLaw_translate _ _ _ _ _ r a ha
lemma multi_integral_translate (r : DyadicTime) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineTranslation r d) ∂L.multi)=∫ d,g d ∂L.multi := by
  have hh : (fun i => ∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart (S.multiLaw i))
      =ᶠ[L.filter] (fun i => ∫ d,g d ∂nonaffinePart (S.multiLaw i)) := by
    filter_upwards [L.refines (S.multiLaw_translate_eventually r)] with i hi
    exact integral_translate_nonaffine (S.multiLaw i) r hi g
  exact tendsto_nhds_unique (L.multi_converges (g.comp (nonaffineTranslation r).toCocompactMap))
    ((L.multi_converges g).congr' hh.symm)
lemma terminal_integral_translate (r : DyadicTime) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineTranslation r d) ∂L.terminal)=∫ d,g d ∂L.terminal := by
  have hh : (fun i => ∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart (S.terminalLaw i))
      =ᶠ[L.filter] (fun i => ∫ d,g d ∂nonaffinePart (S.terminalLaw i)) := by
    filter_upwards [L.refines (S.terminalLaw_translate_eventually r)] with i hi
    exact integral_translate_nonaffine (S.terminalLaw i) r hi g
  exact tendsto_nhds_unique (L.terminal_converges (g.comp (nonaffineTranslation r).toCocompactMap))
    ((L.terminal_converges g).congr' hh.symm)
lemma multi_translate (r : DyadicTime) : L.multi.map (nonaffineTranslation r)=L.multi := by
  let := Measure.Regular.map (μ := L.multi) (nonaffineTranslation r)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) (nonaffineTranslation r).continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  exact S.multi_integral_translate L r g
lemma terminal_translate (r : DyadicTime) : L.terminal.map (nonaffineTranslation r)=L.terminal := by
  let := Measure.Regular.map (μ := L.terminal) (nonaffineTranslation r)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) (nonaffineTranslation r).continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  exact S.terminal_integral_translate L r g
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_VagueSupport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma open_null_of_integral_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (μ : Measure X) [μ.Regular] {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) → ∫ x,g x ∂μ=0) : μ U=0 := by
  rw [hU.measure_eq_iSup_isCompact μ]
  apply le_antisymm _ bot_le
  simp only [iSup_le_iff]
  intro K hKU hK
  obtain ⟨⟨f,hfc⟩,hfK,hfU,hfs,hfr⟩ := exists_continuous_one_zero_of_isCompact
    hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  let g : C_c(X,ℝ) := ⟨⟨f,hfc⟩,hfs⟩
  have hint := hzero g (fun x => (hfr x).1) (fun x hx => hfU hx)
  have hb := (hfc.integrable_of_hasCompactSupport hfs (μ := μ)).measure_le_integral
    (Eventually.of_forall fun x => (hfr x).1) (fun x hx => (hfK hx).ge)
  change μ K ≤ ENNReal.ofReal (∫ x,g x ∂μ) at hb
  rw [hint,ENNReal.ofReal_zero] at hb
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
lemma vague_open_null {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) (ν : Measure X) [ν.Regular]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) →
      Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 0)) : ν U=0 := by
  apply open_null_of_integral_zero ν hU
  intro g hg hz
  exact tendsto_nhds_unique (hconv g) (hzero g hg hz)
lemma ae_le_zero_of_positive_rational_null {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hn : ∀ q : ℚ,0<q → μ {x | (q:ℝ)<f x}=0) : ∀ᵐ x ∂μ, f x ≤ 0 := by
  have hh : ∀ q : ℚ,0<q → ∀ᵐ x ∂μ,¬(q:ℝ)<f x := fun q hq => ae_iff.mpr (by simpa using hn q hq)
  have h := ae_all_iff.mpr (fun q : ℚ => ae_all_iff.mpr (hh q))
  filter_upwards [h] with x hx
  by_contra hpos
  obtain ⟨q,hq,hqx⟩ := exists_rat_btwn (lt_of_not_ge hpos)
  exact hx q (by exact_mod_cast hq) hqx
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayLimitSupport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma integral_nonaffine_scale_zero (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ))
    (hz : ∀ j∈Finset.range l,∀ z,arrayTestExtend g (sampleArray k hk z (2^(p+j)) (by positivity))=0) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  rw [←integral_arrayTestExtend,integral_scaleLaw k hk p l ε hε (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
  have hs : (∑ j∈Finset.range l,∫ d,arrayTestExtend g d ∂sampleLaw k hk (2^(p+j)) (by positivity))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_sampleLaw _ _ _ _ (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
    simp_rw [hz j hj]
    simp
  rw [hs,zero_div]
lemma integral_nonaffine_scale_zero_of_bound (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ)) (f : DistanceArray → ℝ) (q : ℝ)
    (hg : ∀ d : NonAffineArray, f d.val ≤ q → g d=0)
    (hf : ∀ j∈Finset.range l,∀ z,f (sampleArray k hk z (2^(p+j)) (by positivity)) ≤ q) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  apply integral_nonaffine_scale_zero k hk p l ε hε g
  intro j hj z
  let d := sampleArray k hk z (2^(p+j)) (by positivity)
  by_cases hd : d∈affineLocus
  · exact arrayTestExtend_affine g d hd
  · exact (arrayTestExtend_apply g ⟨d,hd⟩).trans (hg ⟨d,hd⟩ (hf j hj z))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma power_lower_tendsto : Tendsto (fun i => (2:ℝ)^(criticalLowerExponent S.offset i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.lowerExponent_tendsto
lemma power_terminal_tendsto : Tendsto (fun i => (2:ℝ)^(S.exponent i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.exponent_tendsto
lemma sample_constraint_aemulti (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.multi, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(criticalLowerExponent S.offset i)<q :=
    (tendsto_const_nhds.div_atTop S.power_lower_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (criticalLowerExponent S.offset i) j))).trans hi.le)
lemma sample_constraint_aeterminal (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.terminal, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(S.exponent i)<q :=
    (tendsto_const_nhds.div_atTop S.power_terminal_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (S.exponent i) j))).trans hi.le)
lemma unit_aemulti : ∀ᵐ d ∂L.multi, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.multi,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aemulti L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
lemma unit_aeterminal : ∀ᵐ d ∂L.terminal, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.terminal,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aeterminal L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayHalf
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology Classical
namespace StandardMapEntropy
lemma map_half_dilate (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineDilate).map nonaffineHalf=μ := by
  rw [Measure.map_map measurable_nonaffineHalf continuous_nonaffineDilate.measurable]
  calc
    μ.map (nonaffineHalf ∘ nonaffineDilate)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineHalf_dilate d hd))
    _=μ := Measure.map_id
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma half_balance : L.multi=L.multi.map nonaffineHalf+L.terminal.map nonaffineHalf := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineHalf) (S.dilation_balance_q44 L)
  rw [map_half_dilate L.multi (S.unit_aemulti L),Measure.map_add] at hh <;> try exact measurable_nonaffineHalf
  exact hh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_HalfDecomposition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal
namespace StandardMapEntropy
lemma sub_add_cancel_sigma {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite ν]
    (h : ν≤μ) : μ-ν+ν=μ := by
  have hr : ∀n:ℕ,(μ-ν+ν).restrict (spanningSets ν n)=μ.restrict (spanningSets ν n) := by
    intro n
    rw [Measure.restrict_add,Measure.restrict_sub_eq_restrict_sub_restrict (measurableSet_spanningSets ν n)]
    have : IsFiniteMeasure (ν.restrict (spanningSets ν n)) := isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top ν n).ne
    exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl h)
  have hh := Measure.restrict_iUnion_congr.mpr hr
  rwa [iUnion_spanningSets,Measure.restrict_univ,Measure.restrict_univ] at hh
lemma map_iterate_succ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map (f^[n])).map f=μ.map (f^[n+1]) := by
  rw [Measure.map_map hf (hf.iterate n)]
  congr 1
  exact funext (fun x => (Function.iterate_succ_apply' f n x).symm)
lemma map_iterate_succ' {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map f).map (f^[n])=μ.map (f^[n+1]) := by
  rw [Measure.map_map (hf.iterate n) hf]
  congr 1
lemma renewal_partial {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) (n : ℕ) :
    μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := congrArg (fun m : Measure X => m.map (f^[n])) hb
    rw [Measure.map_add _ _ (hf.iterate n),map_iterate_succ' μ f hf n,map_iterate_succ' ν f hf n] at hh
    rw [Finset.sum_range_succ]
    calc
      μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := ih
      _=μ.map (f^[n+1])+(∑j∈Finset.range n,ν.map (f^[j+1])+ν.map (f^[n+1])) := by rw [hh]; ac_rfl
lemma renewal_sum_le {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) : (Measure.sum (fun j : ℕ => ν.map (f^[j+1])))≤μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.sum_apply _ hs]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have hh : (∑j∈Finset.range n,ν.map (f^[j+1]))≤μ := by
    rw [renewal_partial μ ν f hf hb n]
    exact Measure.le_add_left le_rfl
  simpa only [Measure.finsetSum_apply] using hh s
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RemainderLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma arrayTranslate_unit (r : DyadicTime) (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayTranslate r d) := by
  intro s t
  change d.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
  have hh := hu (s+r) (t+r)
  change d.val (s+r) (t+r)≤|((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))| at hh
  simpa only [add_sub_add_right_eq_sub] using hh
lemma dyadicHalf_add (s t : DyadicTime) : dyadicHalf (s+t)=dyadicHalf s+dyadicHalf t := by
  apply Subtype.ext; change ((s:ℝ)+(t:ℝ))/2=(s:ℝ)/2+(t:ℝ)/2; ring
lemma half_translate (r : DyadicTime) (d : NonAffineArray) (hu : UnitArray d.val) :
    nonaffineTranslation r (nonaffineHalf d)=nonaffineHalf (nonaffineTranslation (dyadicHalf r) d) := by
  have hu' : UnitArray (nonaffineTranslation (dyadicHalf r) d).val := arrayTranslate_unit _ _ hu
  rw [nonaffineHalf,dite_eq_left hu,nonaffineHalf,dite_eq_left hu']
  apply Subtype.ext; apply Subtype.ext; funext s t
  change 2*d.val.val (dyadicHalf (s+r)) (dyadicHalf (t+r))=
    2*d.val.val (dyadicHalf s+dyadicHalf r) (dyadicHalf t+dyadicHalf r)
  rw [dyadicHalf_add,dyadicHalf_add]
lemma unit_half_map (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val) :
    ∀ᵐd ∂μ.map nonaffineHalf,UnitArray d.val := by
  apply (ae_map_iff measurable_nonaffineHalf.aemeasurable
    ((isClosed_unitArray.preimage continuous_subtype_val).measurableSet)).mpr
  exact hu.mono (fun d hd => nonaffineHalf_unit d hd)
lemma half_map_translation_invariant (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val)
    (ht : ∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r : DyadicTime) :
    (μ.map nonaffineHalf).map (nonaffineTranslation r)=μ.map nonaffineHalf := by
  rw [Measure.map_map (nonaffineTranslation r).continuous.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineTranslation r ∘ nonaffineHalf)=μ.map (nonaffineHalf ∘ nonaffineTranslation (dyadicHalf r)) :=
      Measure.map_congr (hu.mono (fun d hd => half_translate r d hd))
    _=(μ.map (nonaffineTranslation (dyadicHalf r))).map nonaffineHalf := by
      rw [Measure.map_map measurable_nonaffineHalf (nonaffineTranslation _).continuous.measurable]
    _=μ.map nonaffineHalf := by rw [ht]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma backwardLaw_zero : S.backwardLaw L 0=L.terminal := by simp [backwardLaw]
lemma backwardLaw_succ (n : ℕ) : S.backwardLaw L (n+1)=(S.backwardLaw L n).map nonaffineHalf :=
  (map_iterate_succ L.terminal nonaffineHalf measurable_nonaffineHalf n).symm
lemma backwardLaw_unit (n : ℕ) : ∀ᵐd ∂S.backwardLaw L n,UnitArray d.val := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.unit_aeterminal L
  | succ n ih => rw [S.backwardLaw_succ L]; exact unit_half_map _ ih
lemma backwardLaw_translate (n : ℕ) (r : DyadicTime) : (S.backwardLaw L n).map (nonaffineTranslation r)=S.backwardLaw L n := by
  induction n generalizing r with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_translate L r
  | succ n ih => rw [S.backwardLaw_succ L]; exact half_map_translation_invariant _ (S.backwardLaw_unit L n) ih r
lemma backwardSum_le : S.backwardSum L≤L.multi := renewal_sum_le _ _ _ measurable_nonaffineHalf (S.half_balance L)
lemma backwardSum_translate (r : DyadicTime) : (S.backwardSum L).map (nonaffineTranslation r)=S.backwardSum L := by
  rw [backwardSum,Measure.map_sum (nonaffineTranslation r).continuous.measurable.aemeasurable]
  congr 1; funext n; exact S.backwardLaw_translate L (n+1) r
lemma backward_decomposition : S.remainderLaw L+S.backwardSum L=L.multi := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  have : SigmaFinite (S.backwardSum L) := Measure.sigmaFinite_of_le L.multi (S.backwardSum_le L)
  exact sub_add_cancel_sigma L.multi (S.backwardSum L) (S.backwardSum_le L)
lemma remainder_translate_q44_oai (r : DyadicTime) : (S.remainderLaw L).map (nonaffineTranslation r)=S.remainderLaw L := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  have : SigmaFinite (S.backwardSum L) := Measure.sigmaFinite_of_le L.multi (S.backwardSum_le L)
  apply (Measure.add_left_inj (S.backwardSum L) _ _).mp
  calc
    (S.remainderLaw L).map (nonaffineTranslation r)+S.backwardSum L=
        (S.remainderLaw L+S.backwardSum L).map (nonaffineTranslation r) := by
      rw [Measure.map_add _ _ (nonaffineTranslation r).continuous.measurable,S.backwardSum_translate L r]
    _=L.multi := by rw [S.backward_decomposition L,S.multi_translate L r]
    _=S.remainderLaw L+S.backwardSum L := (S.backward_decomposition L).symm
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44_oai
