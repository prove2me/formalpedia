-- Prove2me | solution 1 for OAI.DirectionalTransience.OperationalConstants.bad_limit_averaged_survival
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:33.693127+00:00
-- url     : https://prove2.me/submissions/6f9a5ec8-7f11-4146-9801-c4cc2e63bfa8

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma hit_concatenation {d : ℕ} {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) :
    (⋃ n, HitAt S₁ T₁ n ∩ FutureEvent (fun _ => Hit S₂ T₂) n) ⊆ Hit S T₂ := by
  rintro X hX
  obtain ⟨n, hn, hfuture⟩ := Set.mem_iUnion.mp hX
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hfuture
  apply Set.mem_iUnion.mpr
  refine ⟨n + m, hm.1, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · exact h₁ (hn.2 j hjn)
  · have hn : n ≤ j := by omega
    have hsub : j - n < m := by omega
    have := h₂ (hm.2 (j - n) hsub)
    simpa only [Nat.add_sub_of_le hn] using this

lemma hitKernel_comp_le {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S₁ T₁ S₂ T₂ S : Set (Lattice d)}
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (hST : Disjoint S T₂)
    (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel S₂ T₂ (ω, y) U ∂hitKernel S₁ T₁ (ω, x)) ≤
      hitKernel S T₂ (ω, x) U := by
  simp_rw [hitKernel_apply_eq_hit hST₂ U]
  rw [hitKernel_future ω x hST₁ (fun _ => Hit S₂ (T₂ ∩ U))
    (fun _ => measurableSet_hit _ _), hitKernel_apply_eq_hit hST U]
  exact measure_mono (hit_concatenation h₁ h₂)

lemma mass_smul_normalizedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    μ Set.univ • normalizedMeasure μ = μ := by
  by_cases hμ : μ Set.univ = 0
  · have hzero : μ = 0 := Measure.measure_univ_eq_zero.mp hμ
    simp [hzero, normalizedMeasure]
  · rw [normalizedMeasure, smul_smul,
      ENNReal.mul_inv_cancel hμ (measure_ne_top μ Set.univ), one_smul]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BadCrossingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma badCrossingEvent_pos {d : ℕ} (e : Direction d) (N : ℕ) (β D : ℝ)
    (P : Measure (Environment d)) (hN : 0<N)
    (hmass : (N:ℝ)^(-D) ≤ P.real (badCrossingEvent e N β)) :
    P (badCrossingEvent e N β) ≠ 0 := by
  have hr : 0<P.real (badCrossingEvent e N β) :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).trans_le hmass
  exact ENNReal.toReal_pos_iff.mp hr |>.1.ne'

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CoordinateKernelComp
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma coordinate_raw_kernel_comp_le {d : ℕ} (e : Direction d) (k m : ℕ)
    (ω : Environment d) (x : Lattice d) (U : Set (Lattice d)) :
    (∫⁻ y, hitKernel (Strip (realPosition (step e)) y m) (Upper (realPosition (step e)) y m) (ω,y) U
      ∂hitKernel (Strip (realPosition (step e)) x k) (Upper (realPosition (step e)) x k) (ω,x)) ≤
      hitKernel (Strip (realPosition (step e)) x (k+m)) (Upper (realPosition (step e)) x (k+m)) (ω,x) U := by
  let ℓ := realPosition (step e)
  let b := dot (realPosition x) ℓ+(k:ℝ)
  let c := dot (realPosition x) ℓ+((k+m:ℕ):ℝ)
  let S₂ : Set (Lattice d) := {y | b ≤ dot (realPosition y) ℓ ∧ dot (realPosition y) ℓ < c}
  let T₂ : Set (Lattice d) := {y | c ≤ dot (realPosition y) ℓ}
  have he : (∫⁻ y, hitKernel (Strip ℓ y m) (Upper ℓ y m) (ω,y) U
      ∂hitKernel (Strip ℓ x k) (Upper ℓ x k) (ω,x)) =
      ∫⁻ y, hitKernel S₂ T₂ (ω,y) U ∂hitKernel (Strip ℓ x k) (Upper ℓ x k) (ω,x) := by
    apply lintegral_congr_ae
    filter_upwards [coordinate_hitKernel_supported e x k ω] with y hy
    have hproj : dot (realPosition y) ℓ=b := by
      dsimp [ℓ,b]
      rw [signedHeight_projection,signedHeight_projection]
      exact_mod_cast hy
    have hS : Strip ℓ y m=S₂ := by
      ext z
      simp only [Strip,Set.mem_ofPred_eq,S₂,hproj,b,c,Nat.cast_add,add_assoc]
    have hT : Upper ℓ y m=T₂ := by
      ext z
      simp only [Upper,Set.mem_ofPred_eq,T₂,hproj,b,c,Nat.cast_add,add_assoc]
    rw [hS,hT]
  rw [he]
  have hd : Disjoint S₂ T₂ := Set.disjoint_left.mpr (fun y hy hz => (not_lt_of_ge hz) hy.2)
  have hT : T₂=Upper ℓ x (k+m) := by
    simp only [T₂,Upper,c,Nat.cast_add]
  have hk : Strip ℓ x k ⊆ Strip ℓ x (k+m) := by
    intro y hy
    refine ⟨hy.1,?_⟩
    dsimp [Strip] at hy ⊢
    have := Nat.cast_nonneg (α := ℝ) m
    linarith [hy.2]
  have hm : S₂ ⊆ Strip ℓ x (k+m) := by
    intro y hy
    refine ⟨?_,by simpa only [c,Nat.cast_add] using hy.2⟩
    dsimp [S₂,b,Strip] at hy ⊢
    have := Nat.cast_nonneg (α := ℝ) k
    linarith [hy.1]
  have hh := hitKernel_comp_le ω x (disjoint_strip_upper ℓ x k) hd
    (hT ▸ disjoint_strip_upper ℓ x (k+m)) hk hm U
  simpa only [hT] using hh
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetNormalize
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalizeOr_mass {α : Type*} [MeasurableSpace α] (μ ρ : Measure α)
    [IsFiniteMeasure μ] : μ Set.univ • normalizeOr μ ρ = μ := by
  by_cases h : μ Set.univ=0
  · rw [h,zero_smul]; exact (Measure.measure_univ_eq_zero.mp h).symm
  · rw [normalizeOr,ite_eq_right h,mass_smul_normalizedMeasure]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

omit [DiscreteTopology H] [Countable H] [CompactSpace R] [T2Space R]
  [SecondCountableTopology R] in
lemma shift_continuous : Continuous (shift : EpisodeArray H R → EpisodeArray H R) := by
  unfold shift
  fun_prop

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalEndpointProfile_mass {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    crossingQuenched (realPosition (step e)) 0 H ω • globalEndpointProfile e H ω=
      variableHitKernel (realPosition (step e)) H (ω,0) := by
  have he : crossingQuenched (realPosition (step e)) 0 H ω=
      variableHitKernel (realPosition (step e)) H (ω,0) Set.univ := by
    simpa only [variableHitKernel,Kernel.coe_mk] using crossingQuenched_eq_hitKernel (realPosition (step e)) 0 H ω
  rw [he]
  exact normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeInjection
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_progress {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    min i N ≤ episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [episodeBoundary]
    split
    · have hh := episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω
      omega
    · omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalHorizontalCoordinate_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : (Environment d×ℕ)×HorizontalSpace e =>
      globalHorizontalCoordinate e p.1.2 p.1.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro z
  apply Measurable.subtype_mk
  exact (((Measure.measurable_coe (measurableSet_singleton z)).comp
    (globalHorizontalProfile_joint_measurable e)).ennreal_toReal)

lemma episodeCost_measurable {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (i : ℤ) : Measurable (fun ω => episodeCost e t ω i) := by
  have hm : Measurable (fun p : Environment d×ℕ => crossingQuenched (realPosition (step e)) 0 p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (crossingQuenched (realPosition (step e)) 0 (n : ℝ))
    exact measurable_crossingQuenched _ _ _
  exact (((hm.comp (measurable_id.prodMk (ht i))).ennreal_toReal.log).sub
    ((hm.comp (measurable_id.prodMk (ht (i+1)))).ennreal_toReal.log)).ennreal_ofReal

lemma episodeSplicedRow_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m a l : ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => episodeSplicedRow e t X i m a l z) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 (i,a)) :=
    (measurable_pi_apply (i,a)).comp (measurable_snd.comp measurable_fst)
  have hx : Measurable (fun X : EpisodeInput e => horizontalLift e (t X.1.1 i+l) (X.1.2 (i,a)+z)) :=
    (measurable_of_countable (fun p : ℕ×HorizontalSpace e => horizontalLift e (p.1+l) (p.2+z))).comp
      (((ht i).comp hw).prodMk hU)
  unfold episodeSplicedRow
  apply Measurable.ite (measurableSet_lt measurable_const (((ht (i+m)).comp hw).sub ((ht i).comp hw)))
  · exact measurable_current_row.comp (hw.prodMk hx)
  · have hev : Measurable (fun p : (((ℕ×HorizontalSpace e) → Row d)×(ℕ×HorizontalSpace e)) => p.1 p.2) :=
      measurable_from_prod_countable_left (fun q => measurable_pi_apply q)
    exact hev.comp ((((measurable_pi_apply (i,m)).comp measurable_snd).prodMk
      (measurable_const.prodMk (hU.add_const z))))

lemma actualArrayCoordinate_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 p+z)) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  have ha : Measurable (fun X : EpisodeInput e => ((X.1.1,t X.1.1 j),X.1.2 p+z)) :=
    (hw.prodMk ((ht j).comp hw)).prodMk (hU.add_const z)
  have hm := (globalHorizontalCoordinate_joint_measurable e).comp ha
  simpa only [Function.comp_def] using hm

lemma actualArrayMap_measurable {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) : Measurable (actualArrayMap e t J) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU (p : ℤ×ℕ) : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  refine Measurable.prodMk (Measurable.of_eval fun i => ?_)
    (Measurable.prodMk (Measurable.of_eval fun p => ?_)
      (Measurable.prodMk (Measurable.of_eval fun p => ?_) (Measurable.of_eval fun p => ?_)))
  · have hc : Measurable (fun n : ℕ => (n : ℕ∞)) := measurable_of_countable _
    exact (hc.comp (((ht (i+1)).comp hw).sub ((ht i).comp hw))).prodMk
      ((hc.comp ((hJ i).comp hw)).prodMk ((episodeCost_measurable e t ht i).comp hw))
  · exact OnePoint.continuous_coe.measurable.comp ((hU p.2).sub (hU p.1))
  · exact actualArrayCoordinate_measurable e t ht _ _ _
  · exact episodeSplicedRow_measurable e t ht _ _ _ _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma restrict_compProd_fst {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [SFinite Q] (K : Kernel Ω A) [IsSFiniteKernel K]
    (s : Set Ω) (hs : MeasurableSet s) :
    (Q.compProd K).restrict (Prod.fst ⁻¹' s)=(Q.restrict s).compProd K := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.compProd_apply (hB.inter (hs.preimage measurable_fst)),
    Measure.compProd_apply hB,←lintegral_indicator hs]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈s
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (Set.univ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_mem hω,he]
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (∅ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_notMem hω,he]

lemma episodeInputLaw_restrict {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (s : Set (Environment d)) (hs : MeasurableSet s) :
    (episodeInputLaw e ν Q t ht).restrict {X | X.1.1∈s}=
      episodeInputLaw e ν (Q.restrict s) t ht := by
  unfold episodeInputLaw
  rw [←restrict_compProd_fst Q (globalEpisodeAnchors e t ht) s hs,
    Measure.restrict_prod_eq_prod_univ]
  congr 1
  ext X
  simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryCompact
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma sum_indicator_range (N M : ℕ) (hM : M ≤ N) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (if i < M then G i else 0)) = ∑ i ∈ Finset.range M, G i := by
  have he : (Finset.range N).filter (fun i => i < M) = Finset.range M := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [←Finset.sum_filter, he]

lemma episodeOccupationRaw_integral (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T)
    (F : Y →ᵇ ℝ) :
    (∫ y, F y ∂episodeOccupationRaw N μ A M T) =
      ∫ x, ∑ i ∈ Finset.range (M x), F (T^[i] (A x)) ∂μ := by
  have hi (i : ℕ) : Integrable (fun x => F (T^[i] (A x))) μ := by
    apply (integrable_const ‖F‖).mono' ((F.continuous.measurable.comp
      ((hT.iterate i).comp hA)).aestronglyMeasurable)
    exact Eventually.of_forall fun x => F.norm_coe_le_norm _
  have hm (i : ℕ) : MeasurableSet {x | i < M x} := measurableSet_lt measurable_const hM
  rw [episodeOccupationRaw]
  rw [integral_finsetSum_measure (fun i _ =>
    BoundedContinuousFunction.integrable ((μ.restrict {x | i < M x}).map
      (fun x => T^[i] (A x))) F)]
  calc (∑ i ∈ Finset.range N, ∫ y, F y ∂(μ.restrict {x | i < M x}).map
        (fun x => T^[i] (A x)))
      = ∑ i ∈ Finset.range N, ∫ x,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_indicator (hm i)]
          exact integral_map ((hT.iterate i).comp hA).aemeasurable
            F.continuous.aestronglyMeasurable
    _ = ∫ x, ∑ i ∈ Finset.range N,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ :=
          (integral_finsetSum _ (fun i _ => (hi i).indicator (hm i))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [Set.indicator_apply,Set.mem_ofPred_eq]
        exact sum_indicator_range N (M x) (hMN x) _

lemma episodeOccupationRaw_mass (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T) :
    (episodeOccupationRaw N μ A M T).real Set.univ = ∫ x, (M x : ℝ) ∂μ := by
  simpa using episodeOccupationRaw_integral N μ A hA M hM hMN T hT
    (BoundedContinuousFunction.const Y (1:ℝ))

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeGlobalRetention
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma coordinate_survival_lower {d : ℕ} (e : Direction d) (ω : Environment d)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) (H : ℕ) :
    (κ : ℝ≥0∞)^H ≤ crossingQuenched (realPosition (step e)) 0 H ω := by
  induction H with
  | zero => simp [crossingQuenched_zero]
  | succ H ih =>
    have hh := crossingQuenched_lower_step (realPosition (step e)) ω 0 e hκ (H:=H) (by positivity)
    rw [signed_direction_unit] at hh
    simpa only [Nat.cast_add,Nat.cast_one,pow_succ',Nat.succ_eq_add_one] using
      (mul_le_mul_right ih (κ : ℝ≥0∞)).trans hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRecordedAtlas
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma count_event (A : EpisodeRecordedAtlas q J F) (m j h : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} := by
  have := A.countable
  have he : {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} =
      ⋃ l : {l : A.Label // (A.chart l).height=m ∧ A.stages l=j ∧ A.failures l=h}, (A.chart l.val).event := by
    ext ω
    constructor
    · rintro ⟨hm,hj,hf⟩
      obtain ⟨l,hl⟩ := A.cover ω
      refine Set.mem_iUnion.mpr ⟨⟨l,?_,?_,?_⟩,hl⟩
      · rw [A.correct l ω hl] at hm
        exact hm
      · exact (A.stages_correct l ω hl).symm.trans hj
      · exact (A.failures_correct l ω hl).symm.trans hf
    · intro hh
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hh
      change (q ω).height=m ∧ J ω=j ∧ F ω=h
      rw [A.correct l ω hl,A.stages_correct l ω hl,A.failures_correct l ω hl]
      exact l.property
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event
  rwa [l.property.1] at hm

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCounterChain
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeRun_stopped {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : N ≤ q.height) (n : ℕ) :
    episodeRun e f hef r fexp g χ b sfloor N q ω n=q ∧
    episodeSteps e f hef r fexp g χ b sfloor N q ω n=0 ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω (episodeStageFails e f r fexp g χ b N) n=0 := by
  have hnr : ¬EpisodeReady e f r sfloor N q := fun h => (Nat.not_lt_of_ge hq) h.1
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    simp only [episodeRun,episodeSteps,episodeCount,ih.1,ih.2.1,ih.2.2,hnr,ite_false, if_false,false_and,add_zero,and_self]

lemma episodeCounterChain_actual {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    (T<N → p.state=episodeInitial e f hef r sfloor hR T ω) ∧
    (N≤T → N≤p.state.height) ∧
    p.stages=EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i ∧
    p.failures=EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
      (episodeStageFails e f r fexp g χ b N) i := by
  dsimp only
  induction i with
  | zero => exact ⟨fun _ => rfl,fun h => h.trans (Nat.zero_le _),rfl,rfl⟩
  | succ i ih =>
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    by_cases ht : T<N
    <;> dsimp only [T] at ht
    · have he := ih.1 ht
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,he,ite_eq_left ht]
      refine ⟨fun _ => rfl,?_,?_,?_⟩
      · intro hh
        exact hh.trans (Nat.le_add_right _ 1)
      · rw [ih.2.2.1]
      · rw [ih.2.2.2]
    · have hp := ih.2.1 (Nat.le_of_not_lt ht)
      have hz := episodeRun_stopped e f hef r fexp g χ b sfloor N p.state ω hp N
      dsimp only [p] at hz
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,ite_eq_right ht,
        hz.1,hz.2.1,hz.2.2,add_zero]
      refine ⟨fun h => False.elim (ht h),?_,ih.2.2.1,ih.2.2.2⟩
      intro _
      exact hp.trans (Nat.le_add_right _ 1)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma measurable_counts (A : EpisodeRecordedAtlas q J F) : Measurable (fun ω => (J ω,F ω)) := by
  apply measurable_to_countable'
  intro z
  have he : (fun ω => (J ω,F ω)) ⁻¹' {z} =
      ⋃ m : ℕ, {ω | (q ω).height=m ∧ J ω=z.1 ∧ F ω=z.2} := by
    ext ω
    constructor
    · intro h
      have hh : J ω=z.1 ∧ F ω=z.2 := Prod.mk.inj h
      exact Set.mem_iUnion.mpr ⟨(q ω).height,rfl,hh⟩
    · intro h
      obtain ⟨m,hm,hj,hf⟩ := Set.mem_iUnion.mp h
      exact Prod.ext hj hf
  rw [he]
  exact MeasurableSet.iUnion fun m => (rowSigma_le _) _ (A.count_event m z.1 z.2)

end EpisodeRecordedAtlas

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "Fail" => episodeStageFails (k:=k) e f r fexp g χ b N
local notation "J" => fun ω i => steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i
local notation "C" => fun ω i => count (k:=k) e f hef r fexp g χ b sfloor hR N ω Fail i

lemma measurable_counts (i : ℕ) : Measurable (fun ω => (J ω i,C ω i)) := by
  have he : (fun ω => ((episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages,
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures)) =
      (fun ω => (J ω i,C ω i)) := by
    funext ω
    have hh := episodeCounterChain_actual (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    exact Prod.ext hh.2.2.1 hh.2.2.2
  rw [←he]
  exact (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).measurable_counts

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeNumber
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ) (ω : Environment d) :
    Monotone (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [episodeBoundary]
  split
  · exact (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N _ ω).le
  · exact le_refl _

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_le (ω : Environment d) (n : ℕ) : M ω n ≤ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => rw [number]; split <;> omega

lemma number_measurable (n : ℕ) : Measurable (fun ω => M ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.add (Measurable.ite (measurableSet_lt
      (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n) measurable_const)
      measurable_const measurable_const)

lemma number_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (n : ℕ) :
    Integrable (fun ω => (M ω n:ℝ)) Q := by
  apply Entropy.integrable_of_bounded ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n))
  refine ⟨n,fun ω => ?_⟩
  dsimp only [Function.comp_def]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω n

end EpisodeChainLedger
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_mono (ω : Environment d) : Monotone (M ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [number]
  exact Nat.le_add_right _ _

lemma number_active (ω : Environment d) (i : ℕ) (ha : T ω i<N) : M ω i=i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hprev : T ω i<N := lt_of_le_of_lt
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_succ i)) ha
    rw [number,ite_eq_left hprev,ih hprev]

lemma number_stopped (ω : Environment d) (i : ℕ) (hi : N ≤ T ω i) (j : ℕ) : M ω (i+j)=M ω i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hn : ¬T ω (i+j)<N := not_lt.mpr (hi.trans
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_add_right _ _)))
    rw [Nat.add_succ,number,ite_eq_right hn,add_zero,ih]

lemma active_iff_lt_number (ω : Environment d) (i : ℕ) : T ω i<N ↔ i<M ω N := by
  constructor
  · intro ha
    have hi := episodeBoundary_progress (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    have hin : i<N := by omega
    have hm : M ω (i+1)=i+1 := by rw [number,ite_eq_left ha,number_active (k:=k) e f hef r fexp g χ b sfloor hR N ω i ha]
    have hh := number_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.succ_le_of_lt hin)
    change M ω (i+1) ≤ M ω N at hh
    rw [hm] at hh
    exact Nat.lt_of_succ_le hh
  · intro hm
    by_contra ha
    have hi : i<N := lt_of_lt_of_le hm (number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N)
    have hh := number_stopped (k:=k) e f hef r fexp g χ b sfloor hR N ω i (Nat.le_of_not_lt ha) (N-i)
    rw [Nat.add_sub_of_le hi.le] at hh
    have hu := number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    omega

lemma number_positive (ω : Environment d) (hN : 0<N) : 0<M ω N :=
  (active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω 0).mp hN

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeDropLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_sub (ω : Environment d) (i : ℕ) : j ω i=J ω (i+1)-J ω i := by
  rw [steps,Nat.add_sub_cancel_left]
  rfl

lemma stepMark_measurable (i : ℕ) : Measurable (fun ω => j ω i) := by
  have hi := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i).fst
  have hj := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N (i+1)).fst
  have h : Measurable (fun ω => J ω (i+1)-J ω i) := hj.sub hi
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact funext (fun ω => stepMark_sub (k:=k) e f hef r fexp g χ b sfloor hR N ω i)

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadCrossingEpisodes
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma episodeInputLaw_environment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).map (fun X => X.1.1)=Q := by
  change Measure.map (Prod.fst ∘ Prod.fst) _=Q
  rw [←Measure.map_map measurable_fst measurable_fst]
  unfold episodeInputLaw
  rw [Measure.map_fst_prod,measure_univ,one_smul]
  exact Measure.fst_compProd Q (globalEpisodeAnchors e t ht)

lemma episodeInputLaw_env_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (F : Environment d → ℝ) (hF : Measurable F) :
    (∫ X, F X.1.1 ∂episodeInputLaw e ν Q t ht)=(∫ ω, F ω ∂Q) := by
  have hh := integral_map ((measurable_fst.comp measurable_fst).aemeasurable)
    hF.aestronglyMeasurable (μ:=episodeInputLaw e ν Q t ht)
  change (∫ y, F y ∂Measure.map (fun X => X.1.1) (episodeInputLaw e ν Q t ht)) = _ at hh
  rw [episodeInputLaw_environment] at hh
  exact hh.symm

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "t" => arrayTime (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "s" => arrayStages (k:=k) e f hef r fexp g χ b sfloor hR N

lemma arrayStages_measurable (i : ℤ) : Measurable (fun ω => s ω i) := by
  unfold arrayStages
  split
  · exact measurable_const
  · exact stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat

lemma operational_raw_mass (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    (actualOccupationRaw e ν Q t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N) N (fun ω => M ω N)).real Set.univ=
      ∫ ω, (M ω N:ℝ) ∂Q := by
  unfold actualOccupationRaw
  have hM : Measurable (fun X : EpisodeInput e => M X.1.1 N) :=
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N).comp (measurable_fst.comp measurable_fst)
  rw [StationaryCompact.episodeOccupationRaw_mass N _ _
    (actualArrayMap_measurable e t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)
      (arrayStages_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)) _
    hM
    (fun X => number_le (k:=k) e f hef r fexp g χ b sfloor hR N X.1.1 N) _ StationaryCompact.shift_continuous.measurable]
  exact episodeInputLaw_env_integral e ν Q t _ _
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N))

lemma operational_mass_positive (Q : Measure (Environment d)) [IsProbabilityMeasure Q] (hN : 0<N) :
    0<∫ ω, (M ω N:ℝ) ∂Q := by
  have hh := integral_mono (integrable_const (1:ℝ))
    (number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N) (fun ω => by
      change (1:ℝ) ≤ (M ω N:ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (number_positive (k:=k) e f hef r fexp g χ b sfloor hR N ω hN)))
  simp only [integral_const,probReal_univ,one_smul] at hh
  exact lt_of_lt_of_le zero_lt_one hh

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BadOccupationLimit
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

omit [IsProbabilityMeasure ν] in
lemma paddedStages_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) : Measurable (fun ω => C.paddedStages hef N ω i) :=
  EpisodeChainLedger.arrayStages_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

omit [IsProbabilityMeasure ν] in
lemma activeCount_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Measurable (C.activeCount hef N) :=
  EpisodeChainLedger.number_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N N

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundedAnchorAverage
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
namespace DirectionalTransience

lemma sampleAverage_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ a, Measurable (X a)) (hB : ∀ a ω, |X a ω|≤1)
    (hi : iIndepFun X μ) (n : ℕ) (hn : 0<n) (B ε : ℝ)
    (hmean : ∀ a, (∫ ω, X a ω ∂μ)≤B) (hε : 0<ε) :
    μ {ω | B+ε < sampleAverage X n ω} ≤ ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) := by
  have hM (a : ℕ) : Integrable (X a) μ :=
    (integrable_const (1:ℝ)).mono' (hX a).aestronglyMeasurable (Eventually.of_forall (hB a))
  have hm : (∫ ω, sampleAverage X n ω ∂μ) ≤ B := by
    unfold sampleAverage
    rw [integral_const_mul,integral_finsetSum _ (fun a _ => hM a)]
    calc _ ≤ (n:ℝ)⁻¹*∑ _a∈Finset.range n, B :=
           mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hmean a) (inv_nonneg.mpr (Nat.cast_nonneg n))
         _ = B := by simp [hn.ne']
  have he : {ω | B+ε < sampleAverage X n ω} ⊆
      {ω | ε≤|sampleAverage X n ω-∫ ω, sampleAverage X n ω ∂μ|} := by
    intro ω hω
    have hle := le_abs_self (sampleAverage X n ω-∫ ω, sampleAverage X n ω ∂μ)
    dsimp at hω ⊢
    linarith
  exact (measure_mono he).trans ((meas_ge_le_variance_div_sq
    (sampleAverage_memLp μ X hX hB n) hε).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (sampleAverage_variance_le μ X hX hB hi n hn) (sq_nonneg _))))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalContinuation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma globalEndpointProfile_supported {d : ℕ} (e : Direction d) (k : ℕ) (ω : Environment d) :
    ∀ᵐ x ∂globalEndpointProfile e k ω, signedHeight e x=k := by
  apply normalizeOr_ae
  · simpa [variableHitKernel,signedHeight] using
      coordinate_hitKernel_supported e (0:Lattice d) k ω
  · apply (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
    have hh := signedHeight_zsmul_step e (k:ℤ)
    simpa only [natCast_zsmul] using hh

lemma globalHorizontalProfile_lift {d : ℕ} (e : Direction d) (k : ℕ) (ω : Environment d) :
    (globalHorizontalProfile e k ω).map (horizontalLift e k)=globalEndpointProfile e k ω := by
  rw [globalHorizontalProfile,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  calc
    _ = (globalEndpointProfile e k ω).map id := by
      apply Measure.map_congr
      filter_upwards [globalEndpointProfile_supported e k ω] with x hx
      dsimp only [Function.comp_def,id_eq]
      rw [←hx,horizontalLift_projection]
    _ = _ := Measure.map_id

lemma globalEndpointProfile_continuation {d : ℕ} (e : Direction d) (k m : ℕ) (ω : Environment d)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) (U : Set (Lattice d)) :
    (∫⁻ x, variableHitKernel (realPosition (step e)) m (ω,x) U ∂globalEndpointProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 (k+m) ω /
        crossingQuenched (realPosition (step e)) 0 k ω)*globalEndpointProfile e (k+m) ω U := by
  have ha : crossingQuenched (realPosition (step e)) 0 k ω≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  apply (ENNReal.mul_le_mul_iff_right hk ha).mp
  rw [←mul_assoc,ENNReal.mul_div_cancel hk ha]
  have hh := coordinate_raw_kernel_comp_le e k m ω 0 U
  simp only [←Nat.cast_add] at hh ⊢
  change (∫⁻ x, variableHitKernel (realPosition (step e)) m (ω,x) U
    ∂variableHitKernel (realPosition (step e)) k (ω,0)) ≤
      variableHitKernel (realPosition (step e)) (k+m) (ω,0) U at hh
  rw [←globalEndpointProfile_mass e k ω,lintegral_smul_measure,
    ←globalEndpointProfile_mass e (k+m) ω,Measure.smul_apply,smul_eq_mul] at hh
  exact hh

lemma globalHorizontalProfile_continuation {d : ℕ} (e : Direction d) (k m : ℕ) (ω : Environment d)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) (U : Set (HorizontalSpace e)) :
    (∫⁻ z, variableHitKernel (realPosition (step e)) m (ω,horizontalLift e k z)
      (horizontalProjection e ⁻¹' U) ∂globalHorizontalProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 (k+m) ω /
        crossingQuenched (realPosition (step e)) 0 k ω)*globalHorizontalProfile e (k+m) ω U := by
  have hh := globalEndpointProfile_continuation e k m ω hk (horizontalProjection e ⁻¹' U)
  rw [←globalHorizontalProfile_lift e k ω,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)] at hh
  simpa only [globalHorizontalProfile,Measure.map_apply (measurable_of_countable _) (Set.to_countable U).measurableSet] using hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_KernelTranslation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma hitKernel_translation {d : ℕ} (ω : Environment d) (z x : Lattice d)
    (S T U : Set (Lattice d)) :
    hitKernel ((fun y => z+y) ⁻¹' S) ((fun y => z+y) ⁻¹' T) ((fun y => ω (z+y)),x) U =
      hitKernel S T (ω,z+x) ((fun y => y-z) ⁻¹' U) := by
  simp only [hitKernel_apply]
  apply tsum_congr
  intro n
  rw [←quenched_translation ω z x,
    Measure.map_apply (by fun_prop) (measurableSet_hitAt _ _ _)]
  congr 1
  ext X
  simp only [Set.mem_preimage,HitAt,Set.mem_ofPred_eq,Set.mem_inter_iff]
  simp only [add_sub_cancel]

lemma strip_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) (H : ℝ) :
    (fun y => z+y) ⁻¹' Strip ℓ (z+x) H=Strip ℓ x H := by
  ext y
  simp only [Set.mem_preimage,Strip,Set.mem_ofPred_eq,dot_realPosition_add]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma upper_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) (H : ℝ) :
    (fun y => z+y) ⁻¹' Upper ℓ (z+x) H=Upper ℓ x H := by
  ext y
  simp only [Set.mem_preimage,Upper,Set.mem_ofPred_eq,dot_realPosition_add]
  constructor <;> intro h <;> linarith

lemma variableHitKernel_translation {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (z x : Lattice d) (U : Set (Lattice d)) :
    variableHitKernel ℓ H ((fun y => ω (z+y)),x) U =
      variableHitKernel ℓ H (ω,z+x) ((fun y => y-z) ⁻¹' U) := by
  simpa only [variableHitKernel,Kernel.coe_mk,strip_translation,upper_translation] using
    hitKernel_translation ω z x (Strip ℓ (z+x) H) (Upper ℓ (z+x) H) U

lemma horizontalProjection_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    horizontalProjection e (x-y)=horizontalProjection e x-horizontalProjection e y := by
  apply Subtype.ext
  funext j
  by_cases hj : j=e.1
  · subst j
    simp [horizontalProjection]
  · simp [horizontalProjection,Function.update_of_ne hj]

lemma horizontalLift_add {d : ℕ} (e : Direction d) (a b : ℤ) (x y : HorizontalSpace e) :
    horizontalLift e a x+horizontalLift e b y=horizontalLift e (a+b) (x+y) := by
  simp only [horizontalLift,AddSubgroup.coe_add,add_zsmul]
  abel

lemma episodeSpliced_kernel {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (X : EpisodeInput e) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    upperHorizontalKernel e (t X.1.1 (i+m)-t X.1.1 i)
      (fun p => episodeSplicedRow e t X i m a p.1 p.2) z A =
    variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
      (X.1.1,horizontalLift e (t X.1.1 i) (X.1.2 (i,a)+z))
      {y | horizontalProjection e y-X.1.2 (i,a)∈A} := by
  let b := horizontalLift e (t X.1.1 i) (X.1.2 (i,a))
  let H := t X.1.1 (i+m)-t X.1.1 i
  have he : hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
      (upperEnvironment e (fun p => episodeSplicedRow e t X i m a p.1 p.2),horizontalLift e 0 z)=
    hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
      ((fun y => X.1.1 (b+y)),horizontalLift e 0 z) := by
    apply hitKernel_congr
    intro y hy
    have hy0 : 0 ≤ signedHeight e y := by
      have := hy.1
      simp only [signedHeight_projection,signedHeight_horizontalLift,Int.cast_zero] at this
      exact_mod_cast this
    have hyH : (signedHeight e y).toNat<H := by
      have := hy.2
      simp only [signedHeight_projection,signedHeight_horizontalLift,Int.cast_zero,zero_add] at this
      have hylt : signedHeight e y<(H:ℤ) := by exact_mod_cast this
      omega
    change episodeSplicedRow e t X i m a (signedHeight e y).toNat (horizontalProjection e y)=_
    rw [episodeSplicedRow,ite_eq_left hyH]
    simp only [Int.toNat_of_nonneg hy0]
    apply congrArg X.1.1
    calc
      _ = horizontalLift e (t X.1.1 i) (X.1.2 (i,a))+
          horizontalLift e (signedHeight e y) (horizontalProjection e y) :=
        (horizontalLift_add e _ _ _ _).symm
      _ = b+y := by rw [horizontalLift_projection]
  rw [upperHorizontalKernel_apply,he]
  change variableHitKernel (realPosition (step e)) H ((fun y => X.1.1 (b+y)),horizontalLift e 0 z)
    (horizontalProjection e ⁻¹' A)=_
  rw [variableHitKernel_translation]
  dsimp only [b]
  rw [horizontalLift_add,add_zero]
  congr 1
  ext y
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,horizontalProjection_sub,horizontalProjection_lift]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayWindowMarks
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma arrayWindowHeight_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Continuous (arrayWindowHeight e i m) := by unfold arrayWindowHeight; fun_prop
lemma arrayWindowCost_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Continuous (arrayWindowCost e i m) := by unfold arrayWindowCost; fun_prop

lemma expNeg_continuous : Continuous expNeg :=
  ENNReal.continuous_exp.comp (continuous_coe_ennreal_ereal.neg)
lemma expNeg_toReal_continuous : Continuous (fun C => (expNeg C).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro C
  exact (ENNReal.continuousAt_toReal (expNeg_ne_top C)).comp expNeg_continuous.continuousAt

lemma arrayWindowHeight_actual {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1)) (i : ℤ) (m : ℕ) :
    arrayWindowHeight e i m (actualArrayMap e t J X)=(t X.1.1 (i+m)-t X.1.1 i:ℕ) := by
  have hs : (∑ r∈Finset.range m, (t X.1.1 (i+r+1)-t X.1.1 (i+r)))=
      t X.1.1 (i+m)-t X.1.1 i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,ih]
      have h₁ := hmono (show i ≤ i+(m:ℤ) by omega)
      have h₂ := hmono (show i+(m:ℤ) ≤ i+m+1 by omega)
      have hx : i+(m+1:ℕ)=i+(m:ℤ)+1 := by omega
      rw [hx]
      omega
  simpa only [arrayWindowHeight,actualArrayMap,Nat.cast_sum] using congrArg (fun n : ℕ => (n:ℕ∞)) hs

lemma episodeCost_nonneg_real {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ω : Environment d) (hmono : Monotone (t ω))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0) (i : ℤ) :
    0≤Real.log (crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal-
      Real.log (crossingQuenched (realPosition (step e)) 0 (t ω (i+1)) ω).toReal := by
  apply sub_nonneg.mpr
  apply Real.log_le_log (ENNReal.toReal_pos (hpos _) (crossingQuenched_ne_top _ _ _ _))
  apply ENNReal.toReal_mono (crossingQuenched_ne_top _ _ _ _)
  exact crossingQuenched_antitone _ _ _ (by exact_mod_cast hmono (show i ≤ i+1 by omega))

lemma arrayWindowCost_actual {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0) (i : ℤ) (m : ℕ) :
    arrayWindowCost e i m (actualArrayMap e t J X)=ENNReal.ofReal
      (Real.log (crossingQuenched (realPosition (step e)) 0 (t X.1.1 i) X.1.1).toReal-
      Real.log (crossingQuenched (realPosition (step e)) 0 (t X.1.1 (i+m)) X.1.1).toReal) := by
  unfold arrayWindowCost
  simp only [actualArrayMap,episodeCost]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun (r : ℕ) _ => episodeCost_nonneg_real e t X.1.1 hmono hpos (i+(r:ℤ)))]
  congr 1
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    have hx : i+(m+1:ℕ)=i+(m:ℤ)+1 := by omega
    rw [hx]
    ring

lemma expNeg_log_ratio (a b : ℝ≥0∞) (ha : a≠0) (hat : a≠⊤)
    (hb : b≠0) (hbt : b≠⊤) (hba : b≤a) :
    expNeg (ENNReal.ofReal (Real.log a.toReal-Real.log b.toReal))=b/a := by
  have hnonneg : 0≤Real.log a.toReal-Real.log b.toReal := sub_nonneg.mpr
    (Real.log_le_log (ENNReal.toReal_pos hb hbt) (ENNReal.toReal_mono hat hba))
  unfold expNeg
  rw [EReal.coe_ennreal_ofReal, max_eq_left hnonneg]
  simp only [←EReal.coe_neg,EReal.exp_coe]
  rw [neg_sub,Real.exp_sub,Real.exp_log (ENNReal.toReal_pos hb hbt),Real.exp_log (ENNReal.toReal_pos ha hat)]
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos ha hat),ENNReal.ofReal_toReal hbt,ENNReal.ofReal_toReal hat]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArraySurvival
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arraySurvivalSum_lowerSemicontinuous {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ) :
    LowerSemicontinuous (arraySurvivalSum e i m H n) := by
  apply lowerSemicontinuous_sum
  intro a ha
  exact (upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).comp
    (arrayUpperRows_continuous e i m a)

lemma arraySurvivalThreshold_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ) :
    Continuous (arraySurvivalThreshold e i m n ε) :=
  ENNReal.continuous_ofReal.comp (continuous_const.mul
    ((expNeg_toReal_continuous.comp (arrayWindowCost_continuous e i m)).add continuous_const))

lemma survivalViolation_open {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ) :
    IsOpen (survivalViolation e i m n ε) := by
  simp only [survivalViolation,Set.ofPred_exists]
  apply isOpen_iUnion
  intro H
  have he : IsOpen {Y : ActualEpisodeArray e | arrayWindowHeight e i m Y=(H:ℕ∞)} :=
    (ENat.isOpen_singleton (by simp)).preimage (arrayWindowHeight_continuous e i m)
  have hc : IsClosed {Y : ActualEpisodeArray e | arraySurvivalSum e i m H n Y ≤
      arraySurvivalThreshold e i m n ε Y} :=
    (arraySurvivalSum_lowerSemicontinuous e i m H n).isClosed_epigraph.preimage
      (continuous_id.prodMk (arraySurvivalThreshold_continuous e i m n ε))
  simpa only [Set.compl_ofPred,not_le,Set.ofPred_and] using he.inter hc.isOpen_compl

lemma localSurvival_le_one {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (z : HorizontalSpace e) : localSurvival e ω k H z ≤ 1 := by
  change hitKernel (Strip (realPosition (step e)) (horizontalLift e k z) H)
    (Upper (realPosition (step e)) (horizontalLift e k z) H) (ω,horizontalLift e k z) Set.univ ≤ 1
  exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _
lemma localSurvival_ne_top {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (z : HorizontalSpace e) : localSurvival e ω k H z≠⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (localSurvival_le_one e ω k H z)

lemma actual_arraySurvivalSum {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (i : ℤ) (m n : ℕ) :
    arraySurvivalSum e i m (t X.1.1 (i+m)-t X.1.1 i) n (actualArrayMap e t J X)=
      ENNReal.ofReal (∑ a∈Finset.range n, (localSurvival e X.1.1 (t X.1.1 i)
        (t X.1.1 (i+m)-t X.1.1 i) (X.1.2 (i,a))).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [ENNReal.ofReal_toReal (localSurvival_ne_top _ _ _ _ _)]
  change upperHorizontalKernel e _ (fun p => episodeSplicedRow e t X i m a p.1 p.2) 0 Set.univ=_
  rw [episodeSpliced_kernel]
  simp only [Set.mem_univ,Set.ofPred_true,add_zero,localSurvival]

lemma localSurvival_mean {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (hk : crossingQuenched (realPosition (step e)) 0 k ω≠0) :
    (∫ z, (localSurvival e ω k H z).toReal ∂globalHorizontalProfile e k ω) ≤
      (crossingQuenched (realPosition (step e)) 0 ((k+H:ℕ):ℝ) ω /
        crossingQuenched (realPosition (step e)) 0 k ω).toReal := by
  rw [integral_toReal (measurable_of_countable _).aemeasurable
    (Eventually.of_forall (fun z => lt_top_iff_ne_top.mpr (localSurvival_ne_top _ _ _ _ z)))]
  apply ENNReal.toReal_mono (ENNReal.div_ne_top (crossingQuenched_ne_top _ _ _ _) hk)
  have hh := globalHorizontalProfile_continuation e k H ω hk Set.univ
  simpa only [localSurvival,Set.preimage_univ,measure_univ,mul_one,Nat.cast_add] using hh

lemma actual_survivalViolation_iff {d : ℕ} (e : Direction d) (t J : Environment d → ℤ → ℕ)
    (X : EpisodeInput e) (hmono : Monotone (t X.1.1))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k X.1.1≠0)
    (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    actualArrayMap e t J X∈survivalViolation e i m n ε ↔
      (crossingQuenched (realPosition (step e)) 0 (t X.1.1 (i+m)) X.1.1 /
        crossingQuenched (realPosition (step e)) 0 (t X.1.1 i) X.1.1).toReal+ε <
      sampleAverage (fun a E => (localSurvival e X.1.1 (t X.1.1 i)
        (t X.1.1 (i+m)-t X.1.1 i) (E (i,a))).toReal) n X.1.2 := by
  have hik := hmono (show i ≤ i+(m:ℤ) by omega)
  simp only [survivalViolation,Set.mem_ofPred_eq,arrayWindowHeight_actual e t J X hmono,
    Nat.cast_inj,exists_eq_left',actual_arraySurvivalSum]
  unfold arraySurvivalThreshold
  rw [arrayWindowCost_actual e t J X hmono hpos,expNeg_log_ratio _ _ (hpos _)
    (crossingQuenched_ne_top _ _ _ _) (hpos _) (crossingQuenched_ne_top _ _ _ _)
    (crossingQuenched_antitone _ _ _ (by exact_mod_cast hik)),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
  unfold sampleAverage
  rw [show (n:ℝ)⁻¹*∑ a∈Finset.range n, _ = (∑ a∈Finset.range n, _)/(n:ℝ) by ring,
    lt_div_iff₀ (by exact_mod_cast hn)]
  rw [mul_comm]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadArraySampling
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_raw_mass_pos (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    0<(actualOccupationRaw e ν ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)).real Set.univ := by
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hpos := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) hN0
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
  exact hpos.trans_eq he.symm

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivalConditional
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma conditional_survivalViolation_bound {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (hmono : Monotone (t ω))
    (hpos : ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0)
    (A : EpisodeAuxiliary e) (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    globalEpisodeAnchors e t ht ω {E | actualArrayMap e t J ((ω,E),A)∈survivalViolation e i m n ε}
      ≤ ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) := by
  let v : HorizontalSpace e → ℝ := fun z => (localSurvival e ω (t ω i) (t ω (i+m)-t ω i) z).toReal
  let μ := globalEpisodeAnchors e t ht ω
  have hm : Measurable v := measurable_of_countable _
  have hle (z : HorizontalSpace e) : |v z|≤1 := by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (localSurvival_le_one _ _ _ _ _)).trans_eq ENNReal.toReal_one
  have hi : iIndepFun (fun a (E : EpisodeAnchors e) => v (E (i,a))) μ := by
    have h := iIndepFun_infinitePi (P:=fun p : ℤ×ℕ => episodeProfile e t ω p.1)
      (X:=fun (_p : ℤ×ℕ) z => v z) (fun _ => hm)
    exact h.precomp (fun a b hab => Prod.mk.inj hab |>.2)
  have hmean (a : ℕ) : (∫ E, v (E (i,a)) ∂μ) ≤
      (crossingQuenched (realPosition (step e)) 0 (t ω (i+m)) ω /
        crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal := by
    have hmp := measurePreserving_eval_infinitePi (fun p : ℤ×ℕ => episodeProfile e t ω p.1) (i,a)
    have he : (∫ E, v (E (i,a)) ∂μ)=∫ z, v z ∂episodeProfile e t ω i := by
      rw [←hmp.map_eq,integral_map hmp.measurable.aemeasurable hm.aestronglyMeasurable]
      rfl
    rw [he]
    have hh := localSurvival_mean e ω (t ω i) (t ω (i+m)-t ω i) (hpos _)
    have hadd : t ω i+(t ω (i+m)-t ω i)=t ω (i+m) :=
      Nat.add_sub_of_le (hmono (by omega))
    simpa only [hadd,episodeProfile,v] using hh
  have he : {E : EpisodeAnchors e | actualArrayMap e t J ((ω,E),A)∈survivalViolation e i m n ε}=
      {E | (crossingQuenched (realPosition (step e)) 0 (t ω (i+m)) ω /
        crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal+ε <
        sampleAverage (fun a E => v (E (i,a))) n E} := by
    ext E
    exact actual_survivalViolation_iff e t J ((ω,E),A) hmono hpos i m n hn ε hε
  rw [he]
  exact sampleAverage_upper_tail μ _ (fun a => hm.comp (measurable_pi_apply _))
    (fun a E => hle (E (i,a))) hi n hn _ ε hmean hε

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma paddedTimes_int_mono [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : Monotone (C.paddedTimes hef N ω) := by
  intro i j hij
  exact episodeBoundary_mono (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω (Int.toNat_le_toNat hij)

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma survivalViolation_shift {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ)
    (Y : ActualEpisodeArray e) :
    StationaryCompact.shift Y∈survivalViolation e i m n ε ↔ Y∈survivalViolation e (i+1) m n ε := by
  simp only [survivalViolation,Set.mem_ofPred_eq,arrayWindowHeight,arraySurvivalThreshold,
    arrayWindowCost,arraySurvivalSum,StationaryCompact.shift,add_right_comm i _ 1]
  rfl

lemma survivalViolation_iterate {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ) (ε : ℝ)
    (Y : ActualEpisodeArray e) (j : ℕ) :
    StationaryCompact.shift^[j] Y∈survivalViolation e i m n ε ↔ Y∈survivalViolation e (i+j) m n ε := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',survivalViolation_shift,ih]
    rw [show i+1+(j:ℤ)=i+(j+1:ℕ) by omega]

lemma input_survivalViolation_bound {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i)
    (hgood : ∀ᵐ ω ∂Q, Monotone (t ω) ∧ ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0)
    (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    episodeInputLaw e ν Q t ht {X | actualArrayMap e t J X∈survivalViolation e i m n ε} ≤
      ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)*Q Set.univ := by
  have hs : MeasurableSet {X : EpisodeInput e | actualArrayMap e t J X∈survivalViolation e i m n ε} :=
    (survivalViolation_open e i m n ε).measurableSet.preimage (actualArrayMap_measurable e t J ht hJ)
  rw [episodeInputLaw,Measure.prod_apply_symm hs]
  calc
    _ ≤ ∫⁻ _A, ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)*Q Set.univ ∂episodeAuxiliaryLaw e ν := by
      apply lintegral_mono
      intro A
      dsimp only
      have hsa : MeasurableSet {x : Environment d × EpisodeAnchors e |
          actualArrayMap e t J (x,A) ∈ survivalViolation e i m n ε} :=
        hs.preimage (measurable_id.prodMk measurable_const)
      change (Q ⊗ₘ globalEpisodeAnchors e t ht) {x | actualArrayMap e t J (x,A) ∈ survivalViolation e i m n ε} ≤ _
      rw [Measure.compProd_apply hsa]
      calc
        _ ≤ ∫⁻ _ω, ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) ∂Q := by
          apply lintegral_mono_ae
          filter_upwards [hgood] with ω hω
          exact conditional_survivalViolation_bound e t J ht ω hω.1 hω.2 A i m n hn ε hε
        _ = _ := by simp
    _ = _ := by simp

lemma input_env_mass {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    episodeInputLaw e ν Q t ht Set.univ=Q Set.univ := by
  rw [episodeInputLaw,←Set.univ_prod_univ,Measure.prod_prod]
  simp only [measure_univ,mul_one,Measure.compProd_apply_univ]

lemma actualOccupation_survivalViolation_bound {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (hgood : ∀ᵐ ω ∂Q, Monotone (t ω) ∧ ∀ k : ℕ, crossingQuenched (realPosition (step e)) 0 k ω≠0)
    (i : ℤ) (m n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    (actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε) ≤
      ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) := by
  let s := survivalViolation e i m n ε
  let c := ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)
  have hs : MeasurableSet s := (survivalViolation_open e i m n ε).measurableSet
  have hraw : actualOccupationRaw e ν Q t J ht N M s ≤ c*actualOccupationRaw e ν Q t J ht N M Set.univ := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [Measure.finsetSum_apply _ _ _,Measure.finsetSum_apply _ _ _,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hmap := (StationaryCompact.shift_continuous.measurable.iterate j).comp
      (actualArrayMap_measurable e t J ht hJ)
    change Measurable (fun x => StationaryCompact.shift^[j] (actualArrayMap e t J x)) at hmap
    rw [Measure.map_apply hmap hs,Measure.map_apply hmap MeasurableSet.univ,Set.preimage_univ]
    have hr := episodeInputLaw_restrict e ν Q t ht {ω | j<M ω} (measurableSet_lt measurable_const hM)
    change (episodeInputLaw e ν Q t ht).restrict {x | j < (fun X => M X.1.1) x} = _ at hr
    rw [hr,input_env_mass]
    have he : (fun X : EpisodeInput e => StationaryCompact.shift^[j] (actualArrayMap e t J X)) ⁻¹' s=
        {X | actualArrayMap e t J X∈survivalViolation e (i+j) m n ε} := by
      ext X
      exact survivalViolation_iterate e i m n ε (actualArrayMap e t J X) j
    rw [he]
    exact input_survivalViolation_bound e ν (Q.restrict {ω | j<M ω}) t J ht hJ
      (ae_restrict_of_ae hgood) (i+j) m n hn ε hε
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hmass : (ρ : Measure (ActualEpisodeArray e)) Set.univ≠0 := by
    exact ENNReal.toReal_ne_zero.mp hpos.ne' |>.1
  have hρ : ρ≠0 := by
    intro hz
    exact hmass (by rw [hz]; rfl)
  change (ρ.normalize : Measure (ActualEpisodeArray e)) s ≤ c
  rw [ρ.toMeasure_normalize_eq_of_nonzero hρ,Measure.smul_apply]
  rw [ENNReal.smul_def,ENNReal.coe_inv (ρ.mass_nonzero_iff.mpr hρ)]
  have he : (ρ.mass : ℝ≥0∞)=(ρ : Measure (ActualEpisodeArray e)) Set.univ := by simp
  rw [he,smul_eq_mul]
  calc
    _ ≤ ((ρ : Measure (ActualEpisodeArray e)) Set.univ)⁻¹ *
        (c * (ρ : Measure (ActualEpisodeArray e)) Set.univ) := mul_le_mul
          le_rfl hraw (by positivity) (by positivity)
    _ = c := by rw [mul_left_comm,ENNReal.inv_mul_cancel hmass (measure_ne_top _ _),mul_one]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivalLimit
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma survivalViolation_weak_bound {d : ℕ} (e : Direction d)
    (μ : ℕ → ProbabilityMeasure (ActualEpisodeArray e)) (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto μ atTop (𝓝 ρ)) (i : ℤ) (m n : ℕ) (ε : ℝ) (c : ℝ≥0∞)
    (hμ : ∀ k, (μ k : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε) ≤ c) :
    (ρ : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε) ≤ c := by
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (survivalViolation_open e i m n ε)).trans
  exact (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hμ))

lemma arraySurvivalAverage_nonneg {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e) : 0≤arraySurvivalAverage e i m H n Y := by
  unfold arraySurvivalAverage
  positivity

lemma arraySurvivalAverage_le_of_notMem {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (hn : 0<n) (ε : ℝ) (hε : 0≤ε) (Y : ActualEpisodeArray e)
    (hH : arrayWindowHeight e i m Y=H) (hnot : Y∉survivalViolation e i m n ε) :
    arraySurvivalAverage e i m H n Y≤(expNeg (arrayWindowCost e i m Y)).toReal+ε := by
  have hs : arraySurvivalSum e i m H n Y ≤ arraySurvivalThreshold e i m n ε Y := by
    by_contra h
    exact hnot ⟨H,hH,not_le.mp h⟩
  have hh := ENNReal.toReal_mono (show arraySurvivalThreshold e i m n ε Y≠⊤ from ENNReal.ofReal_ne_top) hs
  rw [arraySurvivalThreshold,ENNReal.toReal_ofReal (by positivity)] at hh
  unfold arraySurvivalAverage
  calc
    _ ≤ (n:ℝ)⁻¹*((n:ℝ)*((expNeg (arrayWindowCost e i m Y)).toReal+ε)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hn.ne'),one_mul]

lemma arrayAveragedSurvival_of_bounds {d : ℕ} (e : Direction d)
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hb : ∀ (i : ℤ) (m n : ℕ), 0<n → ∀ ε : ℝ, 0<ε →
      (ρ : Measure (ActualEpisodeArray e)) (survivalViolation e i m n ε) ≤ ENNReal.ofReal ((n:ℝ)⁻¹/ε^2)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayAveragedSurvival e Y := by
  have hbc (i : ℤ) (m k : ℕ) : ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
      ∀ᶠ r : ℕ in atTop, Y∉survivalViolation e i m (2^r) (1/(k+1:ℝ)) := by
    apply ae_eventually_notMem
    have hs : Summable (fun r : ℕ => ((2^r:ℕ):ℝ)⁻¹/(1/(k+1:ℝ))^2) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat,←inv_pow] using
        (summable_geometric_of_norm_lt_one (show ‖(2:ℝ)⁻¹‖<1 by norm_num)).div_const ((1/(k+1:ℝ))^2)
    exact ne_top_of_le_ne_top hs.tsum_ofReal_lt_top.ne
      (ENNReal.tsum_le_tsum (fun r => hb i m (2^r) (by positivity) _ (by positivity)))
  have hall : ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ (i : ℤ) (m k : ℕ),
      ∀ᶠ r : ℕ in atTop, Y∉survivalViolation e i m (2^r) (1/(k+1:ℝ)) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun m => ae_all_iff.mpr fun k => hbc i m k
  filter_upwards [hall] with Y hY
  intro i m H hH
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun r => arraySurvivalAverage_nonneg e i m H (2^r) Y))
  filter_upwards [hY i m k] with r hr
  exact (arraySurvivalAverage_le_of_notMem e i m H (2^r) (by positivity) _ (by positivity) Y hH hr).trans
    (add_le_add_right hk.le _)

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_averaged_survival_oai (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ArrayAveragedSurvival e Y := by
  apply arrayAveragedSurvival_of_bounds e ρ
  intro i m n hn ε hε
  apply survivalViolation_weak_bound e _ ρ hlim i m n ε _
  intro k
  apply actualOccupation_survivalViolation_bound e ν _
    (C.paddedTimes hef (Ns k)) (C.paddedStages hef (Ns k))
    (C.paddedTimes_measurable hef (Ns k)) (C.paddedStages_measurable hef (Ns k)) (Ns k)
    (C.activeCount hef (Ns k)) (C.activeCount_measurable hef (Ns k))
    (C.bad_raw_mass_pos hef (Ns k) (hN k) (hmass k)) _ i m n hn ε hε
  have hQ := (cond_absolutelyContinuous (μ:=environmentLaw ν)
    (s:=badCrossingEvent e (Ns k) (1/2))).ae_le C.rows
  filter_upwards [hQ] with ω hω
  refine ⟨C.paddedTimes_int_mono hef (Ns k) ω,?_⟩
  intro H
  exact ne_of_gt ((ENNReal.pow_pos (show (0:ℝ≥0∞)<C.κ by exact_mod_cast C.hκ0) H).trans_le
    (coordinate_survival_lower e ω C.κ (fun y => hω y e) H))

end OperationalConstants
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.OperationalConstants.bad_limit_averaged_survival_oai := @OAI.DirectionalTransience.OperationalConstants.bad_limit_averaged_survival_oai
