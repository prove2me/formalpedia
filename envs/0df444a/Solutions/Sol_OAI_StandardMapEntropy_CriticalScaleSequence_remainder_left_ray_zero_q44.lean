-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.remainder_left_ray_zero_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:30:07.93362+00:00
-- url     : https://prove2.me/submissions/575d3cb7-9a01-4f12-8a4e-bcf3afc93a36

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_dilation_balance_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_shape_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_translate_q44

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
-- module Solutions.OAIQ44_CM.StandardMap_RealArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma unitArray_diff (d : DistanceArray) (hd : UnitArray d) (s t u v : DyadicTime) :
    |d.val s t-d.val u v| ≤ |(s:ℝ)-(u:ℝ)|+|(t:ℝ)-(v:ℝ)| := by
  have ht := d.property.2.2.2.1
  have hsy := d.property.2.2.1
  have h1 := ht s u t
  have h2 := ht u v t
  have h3 := ht u s v
  have h4 := ht s t v
  have hsu := hd s u
  have htv := hd t v
  rw [abs_sub_comm] at hsu htv
  have hste : d.val u s=d.val s u := hsy _ _
  have hvte : d.val v t=d.val t v := hsy _ _
  rw [abs_le]
  constructor <;> linarith
lemma unitArray_lipschitz (d : DistanceArray) (hd : UnitArray d) :
    LipschitzWith 2 (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := unitArray_diff d hd p.1 p.2 q.1 q.2
  rw [Real.dist_eq,Prod.dist_eq]
  change |d.val p.1 p.2-d.val q.1 q.2| ≤ (2:ℝ)*max |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|
  linarith [le_max_left |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|,
    le_max_right |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|]
@[simp] lemma realArray_coe (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) :
    realArray d (s:ℝ) (t:ℝ)=d.val s t :=
  uniformly_extend_of_ind
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous (s,t)
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
lemma map_dilate_half (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineHalf).map nonaffineDilate=μ := by
  rw [Measure.map_map continuous_nonaffineDilate.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineDilate ∘ nonaffineHalf)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineDilate_half d hd))
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
lemma renewal_sum_balance {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → X) (hf : Measurable f) :
    Measure.sum (fun j : ℕ => ν.map (f^[j+1]))=
      (Measure.sum (fun j : ℕ => ν.map (f^[j+1]))).map f+ν.map f := by
  rw [Measure.map_sum hf.aemeasurable]
  ext s hs
  simp_rw [Measure.add_apply,Measure.sum_apply _ hs,map_iterate_succ ν f hf]
  rw [add_comm]
  exact tsum_eq_zero_add' ENNReal.summable
lemma renewal_remainder_invariant {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ]
    (f : X → X) (hf : Measurable f) (hb : μ=μ.map f+ν.map f) :
    let σ:=Measure.sum (fun j : ℕ => ν.map (f^[j+1])); (μ-σ).map f=μ-σ := by
  dsimp only
  let σ:=Measure.sum (fun j : ℕ => ν.map (f^[j+1]))
  have hσ : σ≤μ := renewal_sum_le μ ν f hf hb
  have : SigmaFinite σ := Measure.sigmaFinite_of_le μ hσ
  have he : μ-σ+σ=μ := sub_add_cancel_sigma μ σ hσ
  have hs : σ=σ.map f+ν.map f := renewal_sum_balance ν f hf
  apply (Measure.add_left_inj σ _ _).mp
  calc
    (μ-σ).map f+σ=(μ-σ).map f+σ.map f+ν.map f := by calc
      (μ-σ).map f+σ=(μ-σ).map f+(σ.map f+ν.map f) := congrArg ((μ-σ).map f+·) hs
      _=_ := (add_assoc _ _ _).symm
    _=(μ-σ+σ).map f+ν.map f := by rw [Measure.map_add _ _ hf]
    _=μ := by rw [he]; exact hb.symm
    _=μ-σ+σ := he.symm
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma remainder_le : S.remainderLaw L≤L.multi := Measure.sub_le
lemma remainder_unit : ∀ᵐd ∂S.remainderLaw L,UnitArray d.val := ae_mono (S.remainder_le L) (S.unit_aemulti L)
lemma remainder_half : (S.remainderLaw L).map nonaffineHalf=S.remainderLaw L := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  exact renewal_remainder_invariant _ _ _ measurable_nonaffineHalf (S.half_balance L)
lemma remainder_dilate : (S.remainderLaw L).map nonaffineDilate=S.remainderLaw L := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineDilate) (S.remainder_half L)
  rw [map_dilate_half _ (S.remainder_unit L)] at hh
  exact hh.symm
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointDefinition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy

lemma measurable_leftEndpoint : Measurable leftEndpoint := by
  apply Measurable.iInf; intro s
  apply Measurable.iInf; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma measurable_rightEndpoint : Measurable rightEndpoint := by
  apply Measurable.iSup; intro s
  apply Measurable.iSup; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma leftEndpoint_le_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : leftEndpoint d≤((max (s:ℝ) (t:ℝ)):EReal) := by
  unfold leftEndpoint
  exact (iInf_le_of_le s (iInf_le_of_le t (by rw [ite_eq_left h])))
lemma le_rightEndpoint_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : ((min (s:ℝ) (t:ℝ)):EReal) ≤ rightEndpoint d := by
  unfold rightEndpoint
  exact (le_iSup_of_le s (le_iSup_of_le t (by rw [ite_eq_left h])))
lemma le_leftEndpoint_iff (d : DistanceArray) (a : EReal) : a≤leftEndpoint d ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → a≤((max (s:ℝ) (t:ℝ)):EReal) := by
  simp only [leftEndpoint,le_iInf_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact le_top
lemma rightEndpoint_le_iff (d : DistanceArray) (a : EReal) : rightEndpoint d≤a ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → ((min (s:ℝ) (t:ℝ)):EReal)≤a := by
  simp only [rightEndpoint,iSup_le_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact bot_le
lemma leftEndpoint_lower_ray (d : DistanceArray) {a : ℝ}
    (h : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) : (a:EReal)≤leftEndpoint d := by
  apply (le_leftEndpoint_iff d a).mpr
  intro s t hn
  have hh : a < max (s:ℝ) (t:ℝ) := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t ((le_max_left _ _).trans hm') ((le_max_right _ _).trans hm'))
  exact EReal.coe_le_coe_iff.mpr hh.le
lemma rightEndpoint_upper_ray (d : DistanceArray) {b : ℝ}
    (h : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) : rightEndpoint d≤(b:EReal) := by
  apply (rightEndpoint_le_iff d b).mpr
  intro s t hn
  have hh : min (s:ℝ) (t:ℝ)<b := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t (hm'.trans (min_le_left _ _)) (hm'.trans (min_le_right _ _)))
  exact EReal.coe_le_coe_iff.mpr hh.le
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointShapes
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma dyadic_between {a b : ℝ} (hab : a < b) : ∃s : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < b := by
  obtain ⟨x,⟨s,rfl⟩,ha,hb⟩ := dyadicTime_dense.exists_between hab
  exact ⟨s,ha,hb⟩
lemma dyadic_pair_between {a b : ℝ} (hab : a < b) :
    ∃s t : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < (t:ℝ) ∧ (t:ℝ) < b := by
  obtain ⟨s,has,hsb⟩ := dyadic_between hab
  obtain ⟨t,hst,htb⟩ := dyadic_between hsb
  exact ⟨s,t,has,hst,htb⟩
lemma nonunit_of_slow {d : DistanceArray} {c : ℝ} (hc : c < 1) {s t : DyadicTime}
    (hst : (s:ℝ) < (t:ℝ)) (h : d.val s t ≤ c*((t:ℝ)-(s:ℝ))) : d.val s t ≠ |(t:ℝ)-(s:ℝ)| := by
  rw [abs_of_pos (sub_pos.mpr hst)]
  intro he
  have hp := mul_lt_mul_of_pos_right hc (sub_pos.mpr hst)
  nlinarith
lemma leftEndpoint_le_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d ≤ (a:EReal) := by
  by_contra hn
  obtain ⟨r,har,hr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have har' : a < r := EReal.coe_lt_coe_iff.mp har
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (lt_min har' hab)
  have htb' := (lt_min_iff.mp htb).2
  have htr := (lt_min_iff.mp htb).1
  have hs := h s t ⟨has.le,(hst.trans htb').le⟩ ⟨(has.trans hst).le,htb'.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := leftEndpoint_le_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [max_eq_right (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) (hu.trans (EReal.coe_le_coe_iff.mpr htr.le))
lemma rightEndpoint_ge_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    (b:EReal) ≤ rightEndpoint d := by
  by_contra hn
  obtain ⟨r,hr,hrb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hrb' : r < b := EReal.coe_lt_coe_iff.mp hrb
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (max_lt hrb' hab)
  have has' := (max_lt_iff.mp has).2
  have hrs := (max_lt_iff.mp has).1
  have hs := h s t ⟨has'.le,(hst.trans htb).le⟩ ⟨(has'.trans hst).le,htb.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := le_rightEndpoint_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [min_eq_left (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr hrs.le).trans hu)
lemma endpoints_slow {d : DistanceArray} {c : ℝ} (hc : c < 1)
    (h : ∀s t:DyadicTime,d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) : leftEndpoint d=⊥ ∧ rightEndpoint d=⊤ := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (leftEndpoint_le_of_slow_interval (a := r) (b := r+1) (by linarith) hc (fun s t _ _ => h s t))
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (rightEndpoint_ge_of_slow_interval (a := r-1) (b := r) (by linarith) hc (fun s t _ _ => h s t))
lemma endpoints_left_ray {d : DistanceArray} {a c : ℝ} (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=⊤ := by
  constructor
  · exact le_antisymm (leftEndpoint_le_of_slow_interval (b := a+1) (by linarith) hc (fun s t hp hq => hs s t hp.1 hq.1))
      (leftEndpoint_lower_ray d hl)
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    have he := rightEndpoint_ge_of_slow_interval (d := d) (a := max r a) (b := max r a+1) (by linarith) hc
      (fun s t hp hq => hs s t ((le_max_right _ _).trans hp.1) ((le_max_right _ _).trans hq.1))
    exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr (by linarith [le_max_left r a])).trans he)
lemma endpoints_right_ray {d : DistanceArray} {b c : ℝ} (hc : c < 1)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=⊥ ∧ rightEndpoint d=(b:EReal) := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr'⟩ := EReal.exists_between_coe_real hh
    have he := leftEndpoint_le_of_slow_interval (d := d) (a := min r b-1) (b := min r b) (by linarith) hc
      (fun s t hp hq => hs s t (hp.2.trans (min_le_right _ _)) (hq.2.trans (min_le_right _ _)))
    exact (not_le_of_gt hr') (he.trans (EReal.coe_le_coe_iff.mpr (by linarith [min_le_left r b])))
  · exact le_antisymm (rightEndpoint_upper_ray d hr)
      (rightEndpoint_ge_of_slow_interval (a := b-1) (by linarith) hc (fun s t hp hq => hs s t hp.2 hq.2))
lemma endpoints_two_rays {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=(b:EReal) :=
  ⟨le_antisymm (leftEndpoint_le_of_slow_interval hab hc hs) (leftEndpoint_lower_ray d hl),
   le_antisymm (rightEndpoint_upper_ray d hr) (rightEndpoint_ge_of_slow_interval hab hc hs)⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCovariance
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma endpoints_reindex (d d' : DistanceArray) (e : ℝ ≃o ℝ) (b : DyadicTime ≃ DyadicTime)
    (hb : ∀s:DyadicTime,(b s:ℝ)=e (s:ℝ))
    (he : ∀s t:DyadicTime,d'.val (b s) (b t)≠|(b t:ℝ)-(b s:ℝ)| ↔ d.val s t≠|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d'=erealOrderIso e (leftEndpoint d) ∧ rightEndpoint d'=erealOrderIso e (rightEndpoint d) := by
  constructor
  · unfold leftEndpoint
    rw [←b.iInf_comp]
    simp_rw [←b.iInf_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((max (b _:ℝ) (t:ℝ)):EReal) else ⊤)]
    simp only [OrderIso.map_iInf]
    apply iInf_congr; intro s
    apply iInf_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
  · unfold rightEndpoint
    rw [←b.iSup_comp]
    simp_rw [←b.iSup_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((min (b _:ℝ) (t:ℝ)):EReal) else ⊥)]
    simp only [OrderIso.map_iSup]
    apply iSup_congr; intro s
    apply iSup_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [min_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [min_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
lemma endpoints_translate (r : DyadicTime) (d : DistanceArray) :
    leftEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (leftEndpoint d) ∧
    rightEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ (Equiv.addRight (-r))
  · intro s; rfl
  · intro s t
    change d.val (s+-r+r) (t+-r+r)≠|((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))| ↔ _
    rw [show s+-r+r=s by abel,show t+-r+r=t by abel]
    rw [show ((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))=(t:ℝ)-(s:ℝ) by ring]
lemma endpoints_dilate (d : DistanceArray) :
    leftEndpoint (arrayDilate d)=erealOrderIso (OrderIso.mulRight₀ (1/2:ℝ) (by norm_num)) (leftEndpoint d) ∧
    rightEndpoint (arrayDilate d)=erealOrderIso (OrderIso.mulRight₀ (1/2:ℝ) (by norm_num)) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ dyadicHalfEquiv
  · intro s; change (s:ℝ)/2=(s:ℝ)*(1/2); ring
  · intro s t
    change (d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2≠|(t:ℝ)/2-(s:ℝ)/2|) ↔ _
    rw [dyadicHalf_add_self,dyadicHalf_add_self,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact not_congr (div_left_inj' (by norm_num))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointClasses
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma measurable_endpointLeft : Measurable endpointLeft := measurable_ereal_toReal.comp measurable_leftEndpoint
lemma measurableSet_leftRayClass : MeasurableSet leftRayClass :=
  ((measurable_leftEndpoint (measurableSet_singleton ⊥)).compl).inter
    (((measurable_leftEndpoint (measurableSet_singleton ⊤)).compl).inter (measurable_rightEndpoint (measurableSet_singleton ⊤)))
lemma slowShape_dyadic {d : DistanceArray} {c:ℝ} (hu:UnitArray d) (h:SlowShape (realArray d) c) :
    (∀s t:DyadicTime,d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) ∨
    (∃a:ℝ,(∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃b:ℝ,(∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃a b:ℝ,a<b ∧
      (∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) := by
  rcases h with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · exact Or.inl (fun s t => by simpa only [realArray_coe d hu] using hs s t)
  · exact Or.inr (Or.inl ⟨a,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,b,hab,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
lemma leftRay_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈leftRayClass) :
    (∀s t:DyadicTime,(s:ℝ)≤endpointLeft d → (t:ℝ)≤endpointLeft d → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,endpointLeft d≤(s:ℝ) → endpointLeft d≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) := by
  rcases slowShape_dyadic hu hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,hl,hr,hs⟩
  · exact (hd.1 (endpoints_slow hc hs).1).elim
  · have he := (endpoints_left_ray hc hl hs).1
    have ha : endpointLeft d=a := by simp only [endpointLeft,he,EReal.toReal_coe]
    simpa only [ha] using And.intro hl hs
  · exact (hd.1 (endpoints_right_ray hc hr hs).1).elim
  · have he := (endpoints_two_rays hab hc hl hr hs).2
    exact (EReal.coe_ne_top b (he.symm.trans hd.2.2)).elim
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointActions
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma erealOrderIso_eq_bot (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊥ ↔ x=⊥ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_bot] using h
  · intro h; rw [h,erealOrderIso_bot]
lemma erealOrderIso_eq_top (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊤ ↔ x=⊤ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_top] using h
  · intro h; rw [h,erealOrderIso_top]
lemma leftRayClass_translate (r:DyadicTime) (d:DistanceArray) : arrayTranslate r d∈leftRayClass ↔ d∈leftRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _=⊤) ↔ _
  rw [(endpoints_translate r d).1,(endpoints_translate r d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma leftRayClass_dilate (d:DistanceArray) : arrayDilate d∈leftRayClass ↔ d∈leftRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _=⊤) ↔ _
  rw [(endpoints_dilate d).1,(endpoints_dilate d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma endpointLeft_translate (r:DyadicTime) (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayTranslate r d)=endpointLeft d-(r:ℝ) := by
  unfold endpointLeft
  rw [(endpoints_translate r d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  rfl
lemma endpointLeft_dilate (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayDilate d)=endpointLeft d/2 := by
  unfold endpointLeft
  rw [(endpoints_dilate d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  simp only [OrderIso.mulRight₀_apply]
  ring
lemma map_restrict_invariant {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→X) (hf:Measurable f)
    (hm:μ.map f=μ) (A:Set X) (hA:MeasurableSet A) (hfA:f⁻¹'A=A) : (μ.restrict A).map f=μ.restrict A := by
  rw [←hfA,←Measure.restrict_map hf hA,hm,hfA]
lemma push_invariant {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ:Measure X)
    (f:X→X) (hf:Measurable f) (hm:μ.map f=μ) (e:X→Y) (he:Measurable e) (g:Y→Y) (hg:Measurable g)
    (hc:∀ᵐx ∂μ,g (e x)=e (f x)) : (μ.map e).map g=μ.map e := by
  rw [Measure.map_map hg he]
  calc
    μ.map (g ∘ e)=μ.map (e ∘ f) := Measure.map_congr hc
    _=(μ.map f).map e := (Measure.map_map he hf).symm
    _=μ.map e := by rw [hm]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCompact
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma separated_secants_compact (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ))
    (c:ℝ) (hc:c<1) : IsCompact {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v ≤ c*((v:ℝ)-(u:ℝ))} := by
  let K:Set DistanceArray := {d | d.val p q=(q:ℝ)-(p:ℝ) ∧ d.val u v ≤ c*((v:ℝ)-(u:ℝ))}
  have hK : IsCompact K := ((isClosed_eq (continuous_arrayEval p q) continuous_const).inter
    (isClosed_le (continuous_arrayEval u v) continuous_const)).isCompact
  have hsub : K⊆(affineLocus)ᶜ := by
    intro d hd ⟨w,hw⟩
    subst d
    have h1 : w.val*((q:ℝ)-(p:ℝ))=(q:ℝ)-(p:ℝ) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr hpq)] using hd.1
    have hw1 : w.val=1 := by nlinarith [sub_pos.mpr hpq]
    have h2 : w.val*((v:ℝ)-(u:ℝ)) ≤ c*((v:ℝ)-(u:ℝ)) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr huv)] using hd.2
    rw [hw1,one_mul] at h2
    exact (not_le_of_gt (mul_lt_of_lt_one_left (sub_pos.mpr huv) hc)) h2
  have hsub' : K⊆Set.range ((↑):NonAffineArray→DistanceArray) := fun d hd => ⟨⟨d,hsub hd⟩,rfl⟩
  exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hsub'
lemma separated_secants_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ)) (c:ℝ) (hc:c<1) :
    μ {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v ≤ c*((v:ℝ)-(u:ℝ))}<∞ :=
  (separated_secants_compact p q u v hpq huv c hc).measure_lt_top
lemma one_left_interface_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hu:∀ᵐd ∂μ,UnitArray d.val) (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000)) :
    μ {d:NonAffineArray | d.val∈leftRayClass ∧ endpointLeft d.val∈Ico (0:ℝ) 1}<∞ := by
  apply lt_of_le_of_lt (measure_mono_ae ?_) (separated_secants_finite μ (dyadicInt (-1)) 0 (dyadicInt 1) (dyadicInt 2) (by norm_num) (by norm_num) (999/1000) (by norm_num))
  filter_upwards [hu,hs] with d hud hsd
  rintro ⟨hd,ha⟩
  obtain ⟨hl,hslow⟩ := leftRay_properties hud (by norm_num) hsd hd
  refine ⟨?_,?_⟩
  · have hh := hl (dyadicInt (-1)) 0 (by norm_num; linarith [ha.1]) (by exact ha.1)
    simpa only [dyadicInt_val,Int.cast_neg,Int.cast_one,ZeroMemClass.coe_zero,sub_neg_eq_add,zero_add,abs_of_pos (by norm_num : (0:ℝ)<1)] using hh
  · have hh := hslow (dyadicInt 1) (dyadicInt 2) (by norm_num; exact ha.2.le) (by norm_num; linarith [ha.2])
    simpa only [dyadicInt_val,Int.cast_one,Int.cast_ofNat,abs_of_pos (by norm_num : (0:ℝ)<2-1)] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointIntensity
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
lemma preimage_sub_Ico (a b r:ℝ) : (fun x:ℝ => x-r)⁻¹'Ico a b=Ico (a+r) (b+r) := by
  ext x; simp only [mem_preimage,mem_Ico]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
lemma invariant_Ico_translate (μ:Measure ℝ) (r:ℝ) (h:μ.map (fun x:ℝ => x-r)=μ) (a b:ℝ) :
    μ (Ico (a+r) (b+r))=μ (Ico a b) := by
  rw [←preimage_sub_Ico,←Measure.map_apply (show Measurable (fun x:ℝ => x-r) from measurable_id.sub measurable_const) measurableSet_Ico,h]
lemma measure_Ico_split (μ:Measure ℝ) {a b c:ℝ} (hab:a≤b) (hbc:b ≤ c) :
    μ (Ico a c)=μ (Ico a b)+μ (Ico b c) := by
  have hu : Ico a c=Ico a b∪Ico b c := by
    ext x; simp only [mem_Ico,mem_union]; constructor
    · rintro ⟨ha,hc⟩; by_cases h:x<b
      · exact Or.inl ⟨ha,h⟩
      · exact Or.inr ⟨le_of_not_gt h,hc⟩
    · rintro (⟨ha,hb⟩|⟨hb,hc⟩)
      · exact ⟨ha,hb.trans_le hbc⟩
      · exact ⟨hab.trans hb,hc⟩
  rw [hu,measure_union (by rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy.1) hx.2) measurableSet_Ico]
lemma stationary_Ico_nat (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (a:ℤ) (n:ℕ) :
    μ (Ico (a:ℝ) ((a:ℝ)+(n:ℝ)))=(n:ℝ≥0∞)*μ (Ico 0 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n+1:ℕ)))=μ (Ico 0 1) := by
      have hh := invariant_Ico_translate μ (dyadicInt (a+n):ℝ) (ht (dyadicInt (a+n))) 0 1
      convert! hh using 2 ; simp only [dyadicInt_val,Int.cast_add,Int.cast_natCast,Nat.cast_add,Nat.cast_one] ; ring_nf
    rw [show ((a:ℝ)+(n+1:ℕ))=(a:ℝ)+(n:ℝ)+1 by push_cast; ring,
      measure_Ico_split μ (show (a:ℝ)≤(a:ℝ)+(n:ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg n)) (by linarith),ih]
    have he' : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n:ℝ)+1))=μ (Ico 0 1) := by convert! he using 2 ; push_cast ; ring_nf
    rw [he',Nat.cast_add,Nat.cast_one,add_mul,one_mul]
lemma stationary_scaling_zero (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ)
    (hs:μ.map (fun x:ℝ => x/2)=μ) (hf:μ (Ico 0 1)<∞) : μ=0 := by
  have htwo : μ (Ico 0 2)=μ (Ico 0 1) := by
    have he : (fun x:ℝ => x/2)⁻¹'Ico 0 1=Ico 0 2 := by ext x; simp only [mem_preimage,mem_Ico]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [←he,←Measure.map_apply (show Measurable (fun x:ℝ => x/2) from measurable_id.div_const 2) measurableSet_Ico,hs]
  have h1 : μ (Ico 1 2)=μ (Ico 0 1) := by
    convert! invariant_Ico_translate μ (dyadicInt 1:ℝ) (ht (dyadicInt 1)) 0 1 using 2 ; norm_num
  have hz : μ (Ico 0 1)=0 := by
    rw [measure_Ico_split μ (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2),h1] at htwo
    apply (ENNReal.add_left_inj hf.ne).mp
    simpa only [zero_add] using htwo
  apply Measure.measure_univ_eq_zero.mp
  have he : (univ:Set ℝ)=⋃n:ℤ,Ico (n:ℝ) ((n:ℝ)+1) := by
    ext x; simp only [mem_univ,mem_iUnion,true_iff]
    exact ⟨⌊x⌋,Int.floor_le x,Int.lt_floor_add_one x⟩
  rw [he]
  apply measure_iUnion_null
  intro n
  have hh := stationary_Ico_nat μ ht n 1
  simpa only [Nat.cast_one,hz,mul_zero] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_OneRayZero
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma invariant_interface_zero (μ:Measure NonAffineArray)
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (hs:μ.map nonaffineDilate=μ)
    (A:Set NonAffineArray) (hA:MeasurableSet A) (e:NonAffineArray→ℝ) (he:Measurable e)
    (hAT:∀r:DyadicTime,(nonaffineTranslation r)⁻¹'A=A) (hAS:nonaffineDilate⁻¹'A=A)
    (hET:∀r:DyadicTime,∀d∈A,e (nonaffineTranslation r d)=e d-(r:ℝ))
    (hES:∀d∈A,e (nonaffineDilate d)=e d/2)
    (hf:μ (A∩e⁻¹'Ico 0 1)<∞) : μ A=0 := by
  let κ:=μ.restrict A
  let lam:=κ.map e
  have htκ (r:DyadicTime) : κ.map (nonaffineTranslation r)=κ :=
    map_restrict_invariant μ _ (nonaffineTranslation r).continuous.measurable (ht r) A hA (hAT r)
  have hsκ : κ.map nonaffineDilate=κ := map_restrict_invariant μ _ continuous_nonaffineDilate.measurable hs A hA hAS
  have htlam (r:DyadicTime) : lam.map (fun x:ℝ => x-(r:ℝ))=lam :=
    push_invariant κ _ (nonaffineTranslation r).continuous.measurable (htκ r) e he _ (measurable_id.sub measurable_const)
      ((ae_restrict_mem hA).mono (fun d hd => (hET r d hd).symm))
  have hslam : lam.map (fun x:ℝ => x/2)=lam :=
    push_invariant κ _ continuous_nonaffineDilate.measurable hsκ e he _ (measurable_id.div_const 2)
      ((ae_restrict_mem hA).mono (fun d hd => (hES d hd).symm))
  have hflam : lam (Ico 0 1)<∞ := by
    rw [Measure.map_apply he measurableSet_Ico,Measure.restrict_apply (he measurableSet_Ico),inter_comm]
    exact hf
  have hz : lam=0 := stationary_scaling_zero lam htlam hslam hflam
  have hh : lam univ=μ A := by rw [Measure.map_apply he MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ]
  rw [←hh,hz]; simp
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma remainder_local : IsFiniteMeasureOnCompacts (S.remainderLaw L) := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  exact ⟨fun K hK => (S.remainder_le L K).trans_lt hK.measure_lt_top⟩
lemma remainder_left_ray_zero_q44_oai : (S.remainderLaw L) {d:NonAffineArray | d.val∈leftRayClass}=0 := by
  have := S.remainder_local L
  apply invariant_interface_zero _ (S.remainder_translate_q44 L) (S.remainder_dilate L)
    {d:NonAffineArray | d.val∈leftRayClass} (measurableSet_leftRayClass.preimage measurable_subtype_coe)
    (fun d => endpointLeft d.val) (measurable_endpointLeft.comp measurable_subtype_coe)
  · intro r; ext d; exact leftRayClass_translate r d.val
  · ext d; exact leftRayClass_dilate d.val
  · intro r d hd; exact endpointLeft_translate r d.val hd.2.1 hd.1
  · intro d hd; exact endpointLeft_dilate d.val hd.2.1 hd.1
  · exact one_left_interface_finite _ (S.remainder_unit L) (S.remainder_shape_q44 L)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_left_ray_zero_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_left_ray_zero_q44_oai
