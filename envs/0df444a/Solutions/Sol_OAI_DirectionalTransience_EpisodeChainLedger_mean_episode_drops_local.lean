-- Prove2me | solution 1 for OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:32.111084+00:00
-- url     : https://prove2.me/submissions/061c2dd6-bac0-48ab-9ece-210fc6b57923

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal004
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero
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

lemma wordWeight_lower {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (x : Lattice d) (w : List (Direction d)) :
    (κ : ℝ) ^ w.length ≤ wordWeight ω x w := by
  induction w generalizing x with
  | nil => simp [wordWeight]
  | cons e w ih =>
    simp only [List.length_cons, pow_succ', wordWeight]
    exact mul_le_mul (by exact_mod_cast hκ x e) (ih _)
      (pow_nonneg κ.coe_nonneg _) (NNReal.coe_nonneg _)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CoordinateKernelComp
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.variablePairHitKernel_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TupleEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma fin_tsum_product {A : Type*} (n : ℕ) (f : Fin n → A → ℝ≥0∞) :
    (∑' x : Fin n → A, ∏ j, f j (x j)) = ∏ j, ∑' x : A, f j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

lemma measure_le_of_singletons {A : Type*} [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] (μ ν : Measure A)
    (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  intro s
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  conv_rhs => rw [← Measure.sum_smul_dirac ν]
  simp only [Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul_left (h x) _

lemma countable_pi_mono {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (n : ℕ) (μ ν : Fin n → Measure A)
    [∀ j, SigmaFinite (μ j)] [∀ j, SigmaFinite (ν j)]
    (h : ∀ j, μ j ≤ ν j) : Measure.pi μ ≤ Measure.pi ν := by
  apply measure_le_of_singletons
  intro x
  simp only [Measure.pi_singleton]
  exact Finset.prod_le_prod' fun j _ => h j {x j}

lemma countable_pi_bind {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (n : ℕ) (μ : Fin n → Measure A) (K : Fin n → A → Measure B)
    [∀ j, SigmaFinite (μ j)] [∀ j x, SigmaFinite (K j x)]
    [∀ j, SigmaFinite ((μ j).bind (K j))] :
    (Measure.pi μ).bind (fun x => Measure.pi (fun j => K j (x j))) =
      Measure.pi (fun j => (μ j).bind (K j)) := by
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.pi_singleton,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable',Measure.pi_singleton,← Finset.prod_mul_distrib]
  exact fin_tsum_product n (fun j a => K j a {y j} * μ j {a})

end TupleKernel

lemma rawTupleEndpointLaw_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    rawTupleMixture (realPosition (step e)) m
      (rawTupleEndpointLaw (realPosition (step e)) h ω x) ω ≤
        rawTupleEndpointLaw (realPosition (step e)) (h+m) ω x := by
  let ℓ := realPosition (step e)
  let K := fun (n : ℕ) (y : Lattice d) => variableHitKernel ℓ n (ω,y)
  have hcomp (y : Lattice d) : (K h y).bind (K m) ≤ K (h+m) y := by
    intro U
    rw [Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable]
    change (∫⁻ a, hitKernel (Strip ℓ a (m : ℝ)) (Upper ℓ a (m : ℝ)) (ω,a) U
      ∂hitKernel (Strip ℓ y (h : ℝ)) (Upper ℓ y (h : ℝ)) (ω,y)) ≤
      hitKernel (Strip ℓ y ((h+m : ℕ) : ℝ)) (Upper ℓ y ((h+m : ℕ) : ℝ)) (ω,y) U
    simpa only [ℓ, Nat.cast_add] using coordinate_raw_kernel_comp_le e h m ω y U
  let : ∀ y, IsFiniteMeasure ((K h y).bind (K m)) := fun y =>
    ⟨lt_of_le_of_lt (hcomp y Set.univ) (measure_lt_top _ _)⟩
  change (Measure.pi (fun j => K h (x j))).bind (fun y => Measure.pi (fun j => K m (y j))) ≤
    Measure.pi (fun j => K (h+m) (x j))
  rw [TupleKernel.countable_pi_bind]
  exact TupleKernel.countable_pi_mono k _ _ (fun j => hcomp (x j))

end DirectionalTransience

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_StageSeedProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedSeparatedRaw_univ {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    seedSeparatedRaw e f H G π ω Set.univ=
      rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f G y} := by
  simp [seedSeparatedRaw]

lemma seedSeparatedProfile_mass {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a G : ℝ) (H : ℕ) (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    seedSeparatedRaw e f H G π.val ω Set.univ •
      (seedSeparatedProfile e f hef a G H π ω).val=seedSeparatedRaw e f H G π.val ω :=
  normalizeOr_mass _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferRestorationScript
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma hitWord_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S T : Set (Lattice d)} (_ : Disjoint S T) (w : HitWord x S T) :
    ENNReal.ofReal (wordWeight ω x w.val) • Measure.dirac (wordPath x w.val w.val.length) ≤
      hitKernel S T (ω,x) := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  rw [Measure.smul_apply,smul_eq_mul]
  by_cases hu : wordPath x w.val w.val.length ∈ U
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_mem hu,Pi.one_apply,mul_one]
    rw [hitKernel_apply]
    apply le_trans _ (ENNReal.le_tsum w.val.length)
    rw [←quenched_wordCylinder]
    apply measure_mono
    intro X hX
    exact ⟨⟨(hitWord_prefix x S T w hX).1,by simpa only [hX _ le_rfl] using hu⟩,
      (hitWord_prefix x S T w hX).2⟩
  · rw [Measure.dirac_apply' _ hU,Set.indicator_of_notMem hu,mul_zero]
    exact bot_le

lemma elliptic_hitWord_dirac_le_hitKernel {d : ℕ} (ω : Environment d) (x : Lattice d)
    {κ : ℝ≥0} (hκ : ∀ y e, κ ≤ (ω y).1 e)
    {S T : Set (Lattice d)} (hST : Disjoint S T) (w : HitWord x S T) :
    (κ : ℝ≥0∞)^w.val.length • Measure.dirac (wordPath x w.val w.val.length) ≤
      hitKernel S T (ω,x) := by
  have hw := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hκ x w.val)
  simp only [ENNReal.ofReal_pow κ.coe_nonneg,ENNReal.ofReal_coe_nnreal] at hw
  intro U
  exact (mul_le_mul_left hw ((Measure.dirac _) U)).trans ((hitWord_dirac_le_hitKernel ω x hST w) U)

lemma elliptic_lateral_script {d : ℕ} (ω : Environment d) (e f : Direction d)
    (hef : e.1 ≠ f.1) (x : Lattice d) (m : ℕ) {κ : ℝ≥0}
    (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(m+1) • Measure.dirac (x+m • step f+step e) ≤
      hitKernel (Strip (realPosition (step e)) x 1) (Upper (realPosition (step e)) x 1) (ω,x) := by
  have hh := elliptic_hitWord_dirac_le_hitKernel ω x hκ (disjoint_strip_upper _ _ _)
    (bufferRestoreWord e f hef x m)
  simpa only [bufferRestoreWord,List.length_append,List.length_replicate,List.length_cons,
    List.length_nil,zero_add,wordPath_lateral_script_end] using hh
end DirectionalTransience

end

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalTuple
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalTupleProfile_mass {d k : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) :
    (crossingQuenched (realPosition (step e)) 0 H ω)^k •
      (globalTupleProfile (k:=k) e H ω).val =
      rawTupleEndpointLaw (realPosition (step e)) H ω (fun _ : Fin k => 0) := by
  apply Measure.ext_of_singleton
  intro x
  have hm (j : Fin k) := congrArg (fun μ : Measure (Lattice d) => μ {x j})
    (globalEndpointProfile_mass e H ω)
  simp only [Measure.smul_apply,smul_eq_mul] at hm ⊢
  change _ * (Measure.pi (fun _ : Fin k => globalEndpointProfile e H ω)) {x} = _
  rw [Measure.pi_singleton,rawTupleEndpointLaw_singleton]
  simp_rw [←hm]
  rw [Finset.prod_mul_distrib]
  simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageStopping
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
namespace DirectionalTransience

lemma before_stageStop_pass {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d)
    {h : ℕ} (hh : 0<h) (hlt : h < stageStop e f a Gminus Gplus B π H R ω) :
    ENNReal.ofReal (Real.exp (-B))≤ stageEndpointMass e f a Gminus π h ω := by
  have hp := notMem_of_lt_hittingBtwn hlt hh
  change ¬ stageTestMass e f a Gminus Gplus π H h ω<ENNReal.ofReal (Real.exp (-B)) at hp
  have hp := le_of_not_gt hp
  simp only [stageTestMass,ite_eq_right (Nat.ne_of_gt hh)] at hp
  split at hp
  · exact hp.trans (min_le_left _ _)
  · exact hp

lemma stage_pass_retains {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H h : ℕ) (ω : Environment d)
    (hh : 0<h) (hp : ENNReal.ofReal (Real.exp (-B))≤ stageTestMass e f a Gminus Gplus π H h ω) :
    ENNReal.ofReal (Real.exp (-B))≤ stageEndpointMass e f a Gminus π h ω ∧
      (h=H → ENNReal.ofReal (Real.exp (-B))≤ stageEndpointMass e f a Gplus π h ω) := by
  simp only [stageTestMass,ite_eq_right (Nat.ne_of_gt hh)] at hp
  by_cases hH : h=H
  · simp only [ite_eq_left hH,le_min_iff] at hp
    exact ⟨hp.1,fun _ => hp.2⟩
  · simp only [ite_eq_right hH] at hp
    exact ⟨hp,fun he => (hH he).elim⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RetainedComposition
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma rawTupleMixture_mono {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) {μ ν : Measure (Fin k → Lattice d)} (h : μ≤ν) :
    rawTupleMixture ℓ H μ ω ≤ rawTupleMixture ℓ H ν ω := by
  apply Measure.le_iff.mpr
  intro U hU
  rw [rawTupleMixture_apply,rawTupleMixture_apply]
  exact lintegral_mono' h le_rfl

lemma rawTupleMixture_smul {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (c : ℝ≥0∞) (μ : Measure (Fin k → Lattice d)) :
    rawTupleMixture ℓ H (c•μ) ω=c•rawTupleMixture ℓ H μ ω :=
  Measure.bind_smul c μ _

lemma rawTupleMixture_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    rawTupleMixture (realPosition (step e)) m
      (rawTupleMixture (realPosition (step e)) h π ω) ω≤
        rawTupleMixture (realPosition (step e)) (h+m) π ω := by
  unfold rawTupleMixture
  rw [Measure.bind_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.bind_apply hU (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hU (measurable_of_countable _).aemeasurable]
  apply lintegral_mono
  intro x
  exact rawTupleEndpointLaw_comp_le e h m ω x U

lemma rawTupleEndpointLaw_zero {d k : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Fin k → Lattice d) : rawTupleEndpointLaw ℓ 0 ω x=Measure.dirac x := by
  apply Measure.ext_of_singleton
  intro y
  rw [rawTupleEndpointLaw_singleton]
  have hz (j : Fin k) : variableHitKernel ℓ 0 (ω,x j)=Measure.dirac (x j) := by
    simpa only [variableHitKernel, Kernel.coe_mk, Nat.cast_zero] using hitKernel_height_zero ℓ (x j) ω
  simp_rw [hz]
  by_cases h : x=y
  · subst y
    simp
  · obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := by
      by_contra! hn
      exact h (funext hn)
    simp only [Measure.dirac_apply', measurableSet_singleton, Set.indicator_apply,
      Pi.one_apply, Set.mem_singleton_iff, h, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

lemma rawTupleMixture_zero {d k : ℕ} (ℓ : Vector d) (π : Measure (Fin k → Lattice d))
    (ω : Environment d) : rawTupleMixture ℓ 0 π ω=π := by
  unfold rawTupleMixture
  have hz : rawTupleEndpointLaw (k:=k) ℓ 0 ω=Measure.dirac := funext (rawTupleEndpointLaw_zero ℓ ω)
  rw [hz,Measure.bind_dirac]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma upwardEndpoint_atom {d : ℕ} (e : Direction d) (ω : Environment d) (x : Lattice d) :
    ((ω x).val e : ℝ≥0∞) ≤ variableHitKernel (realPosition (step e)) 1 (ω,x) {x+step e} := by
  rw [←rawWordLaw_endpoint (realPosition (step e)) 1 ω x,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hm := measure_mono (μ:=rawWordLaw (realPosition (step e)) 1 ω x)
    (show {[e]} ⊆ (fun w => wordPath x w w.length) ⁻¹' {x+step e} by
      intro w hw; rcases Set.mem_singleton_iff.mp hw with rfl; simp [wordPath])
  rw [rawWordLaw_singleton,ite_eq_left (upwardWord_successful e x)] at hm
  simpa only [wordWeight,mul_one,ENNReal.ofReal_coe_nnreal] using hm

lemma tupleUpwardEndpoint_atom {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k ≤ rawTupleEndpointLaw (realPosition (step e)) 1 ω x {tupleShiftUp e 1 x} := by
  rw [rawTupleEndpointLaw_singleton]
  calc
    (κ : ℝ≥0∞)^k = ∏ _j : Fin k, (κ : ℝ≥0∞) := by simp
    _ ≤ _ := Finset.prod_le_prod' fun j _ =>
      (ENNReal.coe_le_coe.mpr (hκ (x j))).trans (by simpa only [tupleShiftUp,one_nsmul] using upwardEndpoint_atom e ω (x j))

lemma tupleUpwardEndpoint_le {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k • Measure.dirac (tupleShiftUp e 1 x) ≤ rawTupleEndpointLaw (realPosition (step e)) 1 ω x := by
  have h : (κ : ℝ≥0∞)^k • Measure.dirac (tupleShiftUp e 1 x) ≤
      rawTupleEndpointLaw (realPosition (step e)) 1 ω x {tupleShiftUp e 1 x} • Measure.dirac (tupleShiftUp e 1 x) := by
    intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_left (tupleUpwardEndpoint_atom e ω x κ hκ) _
  rw [←Measure.restrict_singleton] at h
  exact h.trans Measure.restrict_le_self

lemma tupleUpwardMixture_le {d k : ℕ} (e : Direction d) (ω : Environment d)
    (μ : Measure (Fin k → Lattice d)) (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k • μ.map (tupleShiftUp e 1) ≤ rawTupleMixture (realPosition (step e)) 1 μ ω := by
  rw [←Measure.bind_dirac_eq_map μ (measurable_of_countable _),
    ←Measure.bind_smul _ _ _]
  apply Measure.le_iff.mpr
  intro U hU
  rw [Measure.bind_apply hU (measurable_of_countable _).aemeasurable,rawTupleMixture_apply,
    lintegral_smul_measure,smul_eq_mul]
  rw [←lintegral_const_mul _ (measurable_of_countable _)]
  apply lintegral_mono
  intro x
  exact tupleUpwardEndpoint_le e ω x κ hκ U

lemma stage_separated_mass_upward {d k : ℕ} (e f : Direction d) (H : ℕ) (G : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (κ : ℝ≥0) (hκ : ∀ y, κ≤(ω y).val e) :
    (κ : ℝ≥0∞)^k * rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f G y} ≤
      rawTupleMixture (realPosition (step e)) (H+1) π ω {y | TupleSeparated f G y} := by
  let μ := (rawTupleMixture (realPosition (step e)) H π ω).restrict {y | TupleSeparated f G y}
  have hm := (tupleUpwardMixture_le e ω μ κ hκ).trans
    ((rawTupleMixture_mono (realPosition (step e)) 1 ω (show μ ≤ rawTupleMixture (realPosition (step e)) H π ω from Measure.restrict_le_self)).trans
      (rawTupleMixture_comp_le e H 1 π ω))
  have he : μ.map (tupleShiftUp e 1) {y | TupleSeparated f G y}=μ Set.univ := by
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    apply measure_congr
    have hs : ∀ᵐ x ∂μ,TupleSeparated f G x := ae_restrict_mem (Set.to_countable _).measurableSet
    filter_upwards [hs] with x hx
    apply propext
    apply iff_true_intro
    intro i j hij
    change G≤|signedCoordinate f (x i+1 • step e)-signedCoordinate f (x j+1 • step e)|
    simp only [one_nsmul,signedCoordinate_add,add_sub_add_right_eq_sub]
    exact hx i j hij
  have hb := hm {y | TupleSeparated f G y}
  rw [Measure.smul_apply,smul_eq_mul,he] at hb
  simpa only [μ,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hb

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma stageStop_pos {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (ω : Environment d) :
    0 < stageStop e f a Gminus Gplus B π H R ω := by
  change 1 ≤ stageStop e f a Gminus Gplus B π H R ω
  exact le_hittingBtwn (n:=1) (le_min hH hR) ω

lemma stageStop_le {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) :
    stageStop e f a Gminus Gplus B π H R ω  ≤  min H R := hittingBtwn_le ω

lemma stageStop_traversal_lower {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (hB : 0 ≤ B) (ω : Environment d)
    (hπ : ∀ᵐ x ∂(π ω).val,TupleSeparated f Gminus x)
    (κ : ℝ≥0) (hκ : ∀ y,κ ≤ (ω y).val e) :
    (κ : ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-B))  ≤
      stageEndpointMass e f a Gminus π (stageStop e f a Gminus Gplus B π H R ω) ω := by
  let n := stageStop e f a Gminus Gplus B π H R ω
  have hn : 0<n := stageStop_pos e f a Gminus Gplus B π H R hH hR ω
  have hp : ENNReal.ofReal (Real.exp (-B))  ≤  stageEndpointMass e f a Gminus π (n-1) ω := by
    by_cases hz : n-1=0
    · rw [hz,stageEndpointMass,rawTupleMixture_zero]
      have hfull : (π ω).val {x | TupleSeparated f Gminus x}=1 := by
        calc
          _ = (π ω).val Set.univ := by
            apply measure_congr
            filter_upwards [hπ] with x hx
            apply propext
            exact iff_true_intro hx
          _ = 1 := measure_univ
      rw [hfull]
      exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hB))
    · exact before_stageStop_pass e f a Gminus Gplus B π H R ω (Nat.pos_of_ne_zero hz) (by dsimp [n]; omega)
  have hu := stage_separated_mass_upward e f (n-1) Gminus (π ω).val ω κ hκ
  have he : n-1+1=n := by omega
  rw [he] at hu
  exact (mul_le_mul_right hp _).trans hu

lemma stageOutput_retained_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (H R : ℕ) (ω : Environment d) :
    stageRetainedMass e f a Gminus Gplus B π H R ω •
      (stageOutput e f hef a Gminus Gplus B π H R ω).val  ≤
      rawTupleMixture (realPosition (step e)) (stageStop e f a Gminus Gplus B π H R ω) (π ω).val ω := by
  unfold stageRetainedMass stageEndpointMass stageOutput
  rw [←seedSeparatedRaw_univ,seedSeparatedProfile_mass]
  exact Measure.restrict_le_self

lemma stageRetainedMass_lower {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ)
    (hH : 0<H) (hR : 0<R) (hB : 0 ≤ B) (ω : Environment d)
    (hπ : ∀ᵐ x ∂(π ω).val,TupleSeparated f Gminus x)
    (κ : ℝ≥0) (hκ : ∀ y,κ ≤ (ω y).val e) :
    (κ : ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-B))  ≤
      stageRetainedMass e f a Gminus Gplus B π H R ω := by
  unfold stageRetainedMass stageRetainedGap
  dsimp only
  split
  · rename_i hpass
    have hp := (stage_pass_retains e f a Gminus Gplus B π H _ ω
      (stageStop_pos e f a Gminus Gplus B π H R hH hR ω) hpass.2).2 hpass.1
    have hk1 : (κ : ℝ≥0∞) ≤ 1 := (ENNReal.coe_le_coe.mpr (hκ 0)).trans (by exact_mod_cast row_entry_le_one (ω 0) e)
    exact (mul_le_of_le_one_left' (pow_le_one' hk1 _)).trans hp
  · exact stageStop_traversal_lower e f a Gminus Gplus B π H R hH hR hB ω hπ κ hκ

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_OperationalEpisode
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStageNext_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height ≤ N := by
  have hs := stageStop_le e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  change episodeStageLength e f r fexp g χ b N q ω  ≤  _ at hs
  rw [episodeStageNext_height]
  omega

lemma episodeRun_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : q.height ≤ N) (n : ℕ) :
    (episodeRun e f hef r fexp g χ b sfloor N q ω n).height ≤ N := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    rw [episodeRun]
    split
    · exact episodeStageNext_le e f hef r fexp g χ b N _ ω ih
    · exact ih

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma episodeStageNext_retained_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (N : ℕ)
    (_ : 0 ≤ fexp) (hb : 0 ≤ b) (_ : 0 < sfloor)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (hq : EpisodeReady e f r sfloor N q)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).val e) :
    ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) •
      (episodeStageNext e f hef r fexp g χ b N q ω).profile.val ≤
      rawTupleMixture (realPosition (step e)) (episodeStageLength e f r fexp g χ b N q ω)
        q.profile.val ω := by
  have hg : r (q.scale*Real.exp (-fexp*b)) ≤ r q.scale := hr q.scale hq.2
  have hp : ∀ᵐ x ∂q.profile.val,TupleSeparated f (r (q.scale*Real.exp (-fexp*b))) x :=
    q.profile.property.2.mono fun x hx => tupleSeparated_mono f hg x hx.2
  have hm := stageRetainedMass_lower e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) (hH _ hq.2) (Nat.sub_pos_of_lt hq.1)
    (mul_nonneg (Nat.cast_nonneg _) hb) ω hp κ hκ
  have ho := stageOutput_retained_le e f hef q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  have hi : ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) •
      (episodeStageNext e f hef r fexp g χ b N q ω).profile.val ≤
      stageRetainedMass e f q.height (r (q.scale*Real.exp (-fexp*b)))
        (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
        (episodeStageH χ b q.scale) (N-q.height) ω •
        (episodeStageNext e f hef r fexp g χ b N q ω).profile.val := by
    intro U
    simpa only [Measure.smul_apply,smul_eq_mul,mul_comm] using
      mul_le_mul_right hm ((episodeStageNext e f hef r fexp g χ b N q ω).profile.val U)
  exact hi.trans ho

theorem episodeRun_retained_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (N : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).val e) (n : ℕ) :
    ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeSteps e f hef r fexp g χ b sfloor N q ω n) •
      (episodeRun e f hef r fexp g χ b sfloor N q ω n).profile.val ≤
      rawTupleMixture (realPosition (step e))
        ((episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height)
        q.profile.val ω := by
  change ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
      (episodeSteps e f hef r fexp g χ b sfloor N q ω n) •
      episodeMeasure (episodeRun e f hef r fexp g χ b sfloor N q ω n) ≤ _
  induction n with
  | zero => simp only [episodeMeasure,episodeSteps,episodeRun,pow_zero,one_smul,Nat.sub_self,rawTupleMixture_zero,le_refl]
  | succ n ih =>
    rw [episodeSteps,episodeRun]
    by_cases hp : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hp,ite_eq_left hp,pow_succ,mul_smul]
      have ht := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω n
      have hs := smul_le_smul_left
        (((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
          (episodeSteps e f hef r fexp g χ b sfloor N q ω n))
        (episodeStageNext_retained_local e f hef r fexp g χ b sfloor hr N hf hb hsfloor _ ω hH hp κ hκ)
      rw [←rawTupleMixture_smul] at hs
      have hm := rawTupleMixture_mono (realPosition (step e))
        (episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω) ω ih
      have hc := rawTupleMixture_comp_le e
        ((episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height)
        (episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω)
        q.profile.val ω
      have he : (episodeStageNext e f hef r fexp g χ b N
          (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω).height-q.height =
          (episodeRun e f hef r fexp g χ b sfloor N q ω n).height-q.height +
            episodeStageLength e f r fexp g χ b N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω := by
        rw [episodeStageNext_height]
        omega
      convert hs.trans (hm.trans hc) using 1
      · rfl
      · exact congrArg (fun h => rawTupleMixture (realPosition (step e)) h q.profile.val ω) he
    · simp only [ite_eq_right hp,add_zero]
      exact ih

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
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience.BoundedInjection

lemma injectionOffset_le {d k : ℕ} (f : Direction d) (R : ℝ) (hR : 0 ≤ R)
    (x : Fin k → Lattice d) (j : Fin k) : injectionOffset f R hR x j ≤ injectionMultiplier R*k := by
  exact Nat.mul_le_mul_left _ (injectionChoice f R hR x j).isLt

lemma injectTuple_kernel_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (ω : Environment d) (x : Fin k → Lattice d)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1)) • Measure.dirac (injectTuple e f R hR x) ≤
      rawTupleEndpointLaw (realPosition (step e)) 1 ω x := by
  apply TupleKernel.measure_le_of_singletons
  intro y
  by_cases hy : y=injectTuple e f R hR x
  · subst y
    simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_singleton _),mul_one,
      rawTupleEndpointLaw_singleton]
    have hc : (κ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hκ1
    calc
      _ = ∏ _j : Fin k, (κ : ℝ≥0∞)^(injectionMultiplier R*k+1) := by
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,Nat.mul_comm]
      _ ≤ ∏ j, variableHitKernel (realPosition (step e)) 1 (ω,x j) {injectTuple e f R hR x j} := by
        apply Finset.prod_le_prod'
        intro j _
        have hp := elliptic_lateral_script ω e f hef (x j) (injectionOffset f R hR x j) hκ
        have hb : (κ : ℝ≥0∞)^(injectionMultiplier R*k+1) ≤
            (κ : ℝ≥0∞)^(injectionOffset f R hR x j+1) :=
          pow_le_pow_of_le_one bot_le hc (Nat.add_le_add_right (injectionOffset_le f R hR x j) 1)
        apply hb.trans
        simp only [variableHitKernel, Kernel.coe_mk, Nat.cast_one]
        change (κ : ℝ≥0∞)^(injectionOffset f R hR x j+1) ≤
          hitKernel (Strip (realPosition (step e)) (x j) 1) (Upper (realPosition (step e)) (x j) 1) (ω,x j) {injectTuple e f R hR x j}
        simpa only [Measure.smul_apply,smul_eq_mul,injectTuple,
          Measure.dirac_apply_of_mem (Set.mem_singleton _),mul_one] using hp {injectTuple e f R hR x j}
  · simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply',measurableSet_singleton,
      Set.indicator_apply,Set.mem_singleton_iff]
    simp [Ne.symm hy]

lemma injectionProfile_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R : ℝ) (hR : 0 ≤ R) (a : ℝ) (π : LayerTupleProfile (k:=k) e a)
    (ω : Environment d) (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1)) • (injectionProfile e f hef R hR a π).val ≤
      rawTupleMixture (realPosition (step e)) 1 π.val ω := by
  intro U
  have hU := (Set.to_countable U).measurableSet
  change (κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1))*(π.val.map (injectTuple e f R hR)) U ≤ _
  rw [Measure.map_apply (measurable_of_countable _) hU,rawTupleMixture_apply]
  calc
    _ = ∫⁻ x, ((κ : ℝ≥0∞)^(k*(injectionMultiplier R*k+1)) • Measure.dirac (injectTuple e f R hR x)) U ∂π.val := by
      simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hU]
      rw [lintegral_const_mul _ (measurable_of_countable _)]
      congr 1
      rw [←lintegral_indicator_one ((measurable_of_countable _) hU)]
      apply lintegral_congr
      intro x
      by_cases hx : injectTuple e f R hR x ∈ U <;> simp [hx]
    _ ≤ _ := lintegral_mono fun x => (injectTuple_kernel_le e f hef R hR ω x κ hκ1 hκ) U

end DirectionalTransience.BoundedInjection

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma episodeInitial_retained {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) (ω : Environment d)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (crossingQuenched (realPosition (step e)) 0 t ω)^k •
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) •
      episodeMeasure (episodeInitial (k:=k) e f hef r sfloor hR t ω) ≤
      rawTupleEndpointLaw (realPosition (step e)) (t+1) ω (fun _ : Fin k => 0) := by
  have hi := BoundedInjection.injectionProfile_retained e f hef (r sfloor) hR t
    (globalTupleProfile (k:=k) e t ω) ω κ hκ1 hκ
  have hi := smul_le_smul_left ((crossingQuenched (realPosition (step e)) 0 t ω)^k) hi
  rw [←rawTupleMixture_smul,globalTupleProfile_mass] at hi
  exact hi.trans (rawTupleEndpointLaw_comp_le e t 1 ω (fun _ : Fin k => 0))

lemma episodeFinal_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) (ht : t<N) :
    (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ≤ N :=
  episodeRun_le e f hef r fexp g χ b sfloor N _ ω (Nat.succ_le_of_lt ht) N

lemma episodeBoundary_le {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) : episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i ≤ N := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [episodeBoundary]
    split
    · exact episodeFinal_le e f hef r fexp g χ b sfloor hR N _ ω ‹_›
    · exact ih

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

theorem episodeBoundary_complete {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) : episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω N=N := by
  have hu := episodeBoundary_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  have hl := episodeBoundary_progress (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  omega

end DirectionalTransience

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
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma rawTupleEndpointLaw_origin_mass {d k : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    rawTupleEndpointLaw (realPosition (step e)) H ω (fun _ : Fin k => 0) Set.univ =
      (crossingQuenched (realPosition (step e)) 0 H ω)^k := by
  have hh := congrArg (fun μ : Measure (Fin k → Lattice d) => μ Set.univ)
    (globalTupleProfile_mass (k:=k) e H ω)
  simpa only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using hh.symm

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience
theorem episodeFinal_global_retained_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    ((crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) *
      ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω)) •
      episodeMeasure (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω) ≤
      rawTupleEndpointLaw (realPosition (step e))
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω (fun _ : Fin k => 0) := by
  let q := episodeInitial (k:=k) e f hef r sfloor hR t ω
  let p := episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω
  let c := (crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1))
  have hi : c • episodeMeasure q ≤ rawTupleEndpointLaw (realPosition (step e)) (t+1) ω (fun _ : Fin k => 0) := by
    rw [mul_smul]
    exact episodeInitial_retained e f hef r sfloor hR t ω κ hκ1 hκ
  have hs := episodeRun_retained_local e f hef r fexp g χ b sfloor hr N hf hb hsfloor q ω hH κ (fun y => hκ y e) N
  have hs := smul_le_smul_left c hs
  rw [←rawTupleMixture_smul] at hs
  have hm := rawTupleMixture_mono (realPosition (step e)) (p.height-q.height) ω hi
  have hc := rawTupleEndpointLaw_comp_le e (t+1) (p.height-q.height) ω (fun _ : Fin k => 0)
  have ht : t+1 ≤ p.height := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω N
  have hh : (t+1)+(p.height-q.height)=p.height := by change (t+1)+(p.height-(t+1))=p.height; omega
  rw [hh] at hc
  simpa only [c,p,q,episodeStageCount,episodeFinal,episodeMeasure,mul_smul] using hs.trans (hm.trans hc)

lemma episode_survival_lower_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (crossingQuenched (realPosition (step e)) 0 t ω)^k *
      (κ : ℝ≥0∞)^(k*(BoundedInjection.injectionMultiplier (r sfloor)*k+1)) *
      ((κ:ℝ≥0∞)^k * ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^
        (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) ≤
      (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω)^k := by
  have hh := episodeFinal_global_retained_local (k:=k) e f hef r fexp g χ b sfloor hr hR N t hf hb hsfloor ω hH κ hκ1 hκ Set.univ
  simpa only [Measure.smul_apply,smul_eq_mul,episodeMeasure,measure_univ,mul_one,
    rawTupleEndpointLaw_origin_mass] using hh

end DirectionalTransience

end

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

lemma episode_log_algebra {A C : ℝ≥0∞} (hA : A ≠ ⊤) (hC : C ≠ ⊤)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (κ : ℝ≥0) (hκ : 0 < κ)
    (b : ℝ) (k L J : ℕ) (hk : 0 < k)
    (h : A^k*(κ:ℝ≥0∞)^(k*L)*
      ((κ:ℝ≥0∞)^k*ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))^J ≤ C^k) :
    Real.log A.toReal-Real.log C.toReal ≤
      (L:ℝ)*(-Real.log κ)+(b-Real.log κ)*(J:ℝ) := by
  have hAf : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hCf : 0 < C.toReal := ENNReal.toReal_pos hC0 hC
  have hκf : 0 < (κ:ℝ) := hκ
  have ht := ENNReal.toReal_mono (ENNReal.pow_ne_top hC) h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht
  have hl := Real.log_le_log (by positivity : 0 < A.toReal^k*(κ:ℝ)^(k*L)*
      ((κ:ℝ)^k*Real.exp (-((k:ℝ)*b)))^J) ht
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_pow,Real.log_exp,Real.log_pow] at hl
  have hkf : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  push_cast at hl
  nlinarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_LocalEpisodeLog
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
theorem episode_log_bound_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (hk : 0 < k) (hbκ : -Real.log κ ≤ b) :
    0 ≤ Real.log (crossingQuenched (realPosition (step e)) 0 t ω).toReal -
      Real.log (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω).toReal ∧
    Real.log (crossingQuenched (realPosition (step e)) 0 t ω).toReal -
      Real.log (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω).toReal ≤
      (BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)+
      2*b*(episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) := by
  let T := (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height
  have hpos (h : ℕ) : crossingQuenched (realPosition (step e)) 0 h ω ≠ 0 :=
    ne_of_gt ((ENNReal.pow_pos (ENNReal.coe_pos.mpr hκ0) h).trans_le
      (coordinate_survival_lower e ω κ (fun y => hκ y e) h))
  have hfinite (h : ℕ) := crossingQuenched_ne_top (realPosition (step e)) 0 h ω
  have hl := episode_log_algebra (hfinite t) (hfinite T) (hpos t) (hpos T) κ hκ0 b k
    (BoundedInjection.injectionMultiplier (r sfloor)*k+1)
    (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) hk
    (episode_survival_lower_local e f hef r fexp g χ b sfloor hr hR N t hf hb hsfloor ω hH κ hκ1 hκ)
  constructor
  · have hm := crossingQuenched_antitone (realPosition (step e)) 0 ω
      (a:= (t:ℝ)) (b:= (T:ℝ)) (by exact_mod_cast (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N t ω).le)
    exact sub_nonneg.mpr (Real.log_le_log (ENNReal.toReal_pos (hpos T) (hfinite T))
      (ENNReal.toReal_mono (hfinite t) hm))
  · have hj : 0 ≤ (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω : ℝ) := by positivity
    dsimp only [T] at hl
    push_cast at hl ⊢
    nlinarith

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

lemma episode_counts_le_loops {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r)
    (ω : Environment d) (test : EpisodeState (k:=k) e f r → Environment d → Prop) (n : ℕ) :
    episodeSteps e f hef r fexp g χ b sfloor N q ω n ≤ n ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω test n ≤ n := by
  induction n with
  | zero => exact ⟨le_refl _,le_refl _⟩
  | succ n ih =>
    rw [episodeSteps,episodeCount]
    constructor <;> split <;> omega

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

lemma counts_bounded (ω : Environment d) (i : ℕ) : J ω i ≤ i*N ∧ C ω i ≤ i*N := by
  induction i with
  | zero => simp only [steps,count,Nat.zero_mul,le_refl,and_self]
  | succ i ih =>
    have hh := episode_counts_le_loops e f hef r fexp g χ b sfloor N
      (episodeInitial (k:=k) e f hef r sfloor hR
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω) ω Fail N
    dsimp only at ih ⊢
    rw [steps,count,Nat.succ_mul]
    constructor <;> split <;> omega

lemma counts_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (i : ℕ) :
    Integrable (fun ω => (J ω i:ℝ)) Q ∧ Integrable (fun ω => (C ω i:ℝ)) Q := by
  have hm := measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i
  have hcast : Measurable (fun n : ℕ => (n:ℝ)) := measurable_of_countable _
  constructor
  · apply Entropy.integrable_of_bounded (hcast.comp hm.fst)
    refine ⟨(i*N:ℕ),fun ω => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.comp_def]
    exact_mod_cast (counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i).1
  · apply Entropy.integrable_of_bounded (hcast.comp hm.snd)
    refine ⟨(i*N:ℕ),fun ω => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.comp_def]
    exact_mod_cast (counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i).2

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

lemma episodeSteps_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    Monotone (episodeSteps e f hef r fexp g χ b sfloor N q ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [episodeSteps]
  exact Nat.le_add_right _ _

lemma episodeSteps_pos_of_ready {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hq : EpisodeReady e f r sfloor N q) (n : ℕ) (hn : 0 < n) :
    0 < episodeSteps e f hef r fexp g χ b sfloor N q ω n := by
  have hm := episodeSteps_mono e f hef r fexp g χ b sfloor N q ω (Nat.succ_le_of_lt hn)
  have he : episodeSteps e f hef r fexp g χ b sfloor N q ω 1=1 := by
    simp only [episodeSteps,episodeRun,hq,ite_true, if_true,zero_add]
  rw [he] at hm
  omega

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N

local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_sum (ω : Environment d) (n : ℕ) :
    M ω n=∑ i ∈ Finset.range n, if T ω i<N then 1 else 0 := by
  induction n with
  | zero => simp only [number,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [number,Finset.sum_range_succ,ih]

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

lemma number_stage_bound (ω : Environment d) (n : ℕ) : M ω n ≤ J ω n+1 ∧
    (T ω n<N → M ω n ≤ J ω n) := by
  induction n with
  | zero => exact ⟨by simp only [number,steps]; omega,fun _ => le_refl _⟩
  | succ n ih =>
    rw [number,steps,episodeBoundary]
    by_cases ht : T ω n<N
    · simp only [ite_eq_left ht]
      have hm := ih.2 ht
      constructor
      · omega
      · intro hp
        have hheight := episodeRun_height_mono e f hef r fexp g χ b sfloor N
          (episodeInitial (k:=k) e f hef r sfloor hR (T ω n) ω) ω N
        have hready : EpisodeReady e f r sfloor N
            (episodeInitial (k:=k) e f hef r sfloor hR (T ω n) ω) := ⟨lt_of_le_of_lt hheight hp,le_refl _⟩
        have hj := episodeSteps_pos_of_ready e f hef r fexp g χ b sfloor N _ ω hready N (Nat.zero_lt_of_lt ht)
        omega
    · simp only [ite_eq_right ht,add_zero]
      exact ⟨ih.1,fun h => False.elim (ht h)⟩

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
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

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

lemma dropMark_measurable (i : ℕ) : Measurable (fun ω => c ω i) := by
  have hm : Measurable (fun p : Environment d×ℕ => crossingQuenched (realPosition (step e)) 0 p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro n
    simpa only [Prod.fst,Prod.snd] using (measurable_crossingQuenched (realPosition (step e)) 0 (n:ℝ))
  exact (((hm.comp (measurable_id.prodMk (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i))).ennreal_toReal.log).sub
    ((hm.comp (measurable_id.prodMk (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N (i+1)))).ennreal_toReal.log))

lemma stepMark_sum (ω : Environment d) (n : ℕ) : ∑ i ∈ Finset.range n, j ω i=J ω n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,steps]
  | succ n ih => rw [Finset.sum_range_succ,ih,steps]; rfl

lemma dropMark_sum (ω : Environment d) (n : ℕ) :
    ∑ i ∈ Finset.range n, c ω i = -Real.log (crossingQuenched (realPosition (step e)) 0 (T ω n) ω).toReal := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,episodeBoundary,Nat.cast_zero,
      crossingQuenched_zero,ENNReal.toReal_one,Real.log_one,neg_zero]
  | succ n ih => rw [Finset.sum_range_succ,ih,dropMark]; ring

lemma dropMark_total (ω : Environment d) :
    ∑ i ∈ Finset.range N, c ω i = -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal := by
  rw [dropMark_sum,episodeBoundary_complete]

end DirectionalTransience.EpisodeChainLedger

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_le (ω : Environment d) (i : ℕ) : j ω i ≤ N := by
  unfold stepMark
  split
  · exact (episode_counts_le_loops e f hef r fexp g χ b sfloor N _ ω
      (episodeStageFails e f r fexp g χ b N) N).1
  · exact Nat.zero_le _

lemma injection_cost_nonneg (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    0 ≤ ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) := by
  have hlog : Real.log (κ:ℝ) ≤ 0 := Real.log_nonpos hκ0.le hκ1
  exact mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.mpr hlog)

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeMeanDrop
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
namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "c" => dropMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma dropMark_bounds_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) (i : ℕ) :
    0 ≤ c ω i ∧ c ω i ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*
        (if T ω i<N then 1 else 0)+2*b*(j ω i) := by
  by_cases ha : T ω i<N
  · have hh := episode_log_bound_local e f hef r fexp g χ b sfloor hr hR N (T ω i)
      hf hb hs ω hH κ hκ0 hκ1 hκ hk hbκ
    simpa only [dropMark,stepMark,episodeBoundary,ite_eq_left ha,mul_one,episodeStageCount] using hh
  · simp only [dropMark,stepMark,episodeBoundary,ite_eq_right ha,sub_self,mul_zero,Nat.cast_zero,add_zero,le_refl,and_self]

lemma total_drop_bound_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(M ω N)+2*b*(J ω N) := by
  rw [←dropMark_total]
  have hh := Finset.sum_le_sum (s:=Finset.range N) (fun i _ =>
    (dropMark_bounds_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hκ i).2)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hh
  have hm : (∑ i ∈ Finset.range N, if T ω i<N then (1:ℝ) else 0)=(M ω N:ℝ) := by
    exact_mod_cast (number_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N).symm
  have hj : (∑ i ∈ Finset.range N, (j ω i:ℝ))=(J ω N:ℝ) := by
    exact_mod_cast stepMark_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  rw [hm,hj] at hh
  exact hh

lemma long_drop_bound_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) (L : ℕ) (hL : 0<L) :
    (∑ i ∈ Finset.range N, if L<j ω i then c ω i else 0) ≤
      (((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))/(L:ℝ)+2*b)*(J ω N) := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  have hA : 0 ≤ A := injection_cost_nonneg (k:=k) r sfloor κ hκ0 hκ1
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hp : 0 ≤ A/(L:ℝ)+2*b := by positivity
  have hpoint (i : ℕ) : (if L<j ω i then c ω i else 0) ≤ (A/(L:ℝ)+2*b)*(j ω i) := by
    split
    · rename_i hij
      have hjr : (L:ℝ) ≤ (j ω i:ℝ) := by exact_mod_cast hij.le
      have hratio : 1 ≤ (j ω i:ℝ)/(L:ℝ) := (one_le_div hLr).mpr hjr
      have hcharge : A ≤ A/(L:ℝ)*(j ω i:ℝ) := by
        have := mul_le_mul_of_nonneg_left hratio hA
        calc A = A*1 := (mul_one _).symm
             _ ≤ A*((j ω i:ℝ)/(L:ℝ)) := this
             _ = _ := by ring
      have hc := (dropMark_bounds_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hκ i).2
      have hai : A*(if T ω i<N then (1:ℝ) else 0) ≤ A := by split <;> simp_all only [mul_one,mul_zero,le_refl]
      change c ω i ≤ A*(if T ω i<N then 1 else 0)+2*b*(j ω i) at hc
      nlinarith only [hc,hai,hcharge]
    · exact mul_nonneg hp (Nat.cast_nonneg _)
  have h := Finset.sum_le_sum (s:=Finset.range N) (fun i _ => hpoint i)
  rw [←Finset.mul_sum] at h
  have hj : (∑ i ∈ Finset.range N, (j ω i:ℝ))=(J ω N:ℝ) := by
    exact_mod_cast stepMark_sum (k:=k) e f hef r fexp g χ b sfloor hR N ω N
  rw [hj] at h
  exact h

lemma dropMark_integrable_local (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) (i : ℕ) : Integrable (fun ω => c ω i) Q := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  apply Integrable.of_bound (dropMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i).aestronglyMeasurable (A+2*b*N)
  filter_upwards [hκ] with ω hω
  have hc := dropMark_bounds_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb hs hH κ hκ0 hκ1 hk hbκ ω hω i
  rw [Real.norm_eq_abs,abs_of_nonneg hc.1]
  have hA : 0 ≤ A := injection_cost_nonneg (k:=k) r sfloor κ hκ0 hκ1
  have hj : (j ω i:ℝ) ≤ N := by exact_mod_cast stepMark_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
  have hai : A*(if T ω i<N then (1:ℝ) else 0) ≤ A := by split <;> simp_all only [mul_one,mul_zero,le_refl]
  have hc' : c ω i ≤ A*(if T ω i<N then 1 else 0)+2*b*(j ω i) := hc.2
  have := mul_le_mul_of_nonneg_left hj (show 0≤2*b by positivity)
  linarith

theorem mean_episode_drops_local_oai (hr : StageRadiusOrder r fexp b sfloor) (hf : 0 ≤ fexp) (hb : 0 < b) (hs : 0 < sfloor)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hk : 0 < k) (hbκ : -Real.log κ ≤ b)
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hκ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u)
    (β : ℝ) (hbad : ∀ᵐ ω ∂Q, β*Real.log (N:ℝ) ≤ -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal)
    (hstages : 2*b*(∫ ω, (J ω N:ℝ) ∂Q) ≤ β/4*Real.log (N:ℝ))
    (L : ℕ) (hL : 0<L)
    (hcharge : ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) ≤ 2*b*L) :
    (3*β/4*Real.log (N:ℝ) ≤
      ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))*(∫ ω, (M ω N:ℝ) ∂Q)) ∧
    ((∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1) ∧
    (β/2*Real.log (N:ℝ) ≤ ∫ ω, ∑ i ∈ Finset.range N, if j ω i ≤ L then c ω i else 0 ∂Q) := by
  let A : ℝ := ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ))
  let S : Environment d → ℝ := fun ω => ∑ i ∈ Finset.range N, if j ω i≤L then c ω i else 0
  let B : Environment d → ℝ := fun ω => ∑ i ∈ Finset.range N, if L<j ω i then c ω i else 0
  let D : Environment d → ℝ := fun ω => -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal
  have hc (i : ℕ) := dropMark_integrable_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ Q hκ i
  have hsum : Integrable D Q := by
    have hh := integrable_finsetSum (s:=Finset.range N) (fun i _ => hc i)
    simpa only [dropMark_total] using hh
  have hS : Integrable S Q := by
    apply integrable_finsetSum
    intro i _
    convert (hc i).indicator (s:={ω | j ω i≤L}) (measurableSet_le (stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i) measurable_const) using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  have hB : Integrable B Q := by
    apply integrable_finsetSum
    intro i _
    convert (hc i).indicator (s:={ω | L<j ω i}) (measurableSet_lt measurable_const (stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i)) using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  have hJ := (counts_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N).1
  have hM := number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N
  have hdrop : β*Real.log (N:ℝ) ≤ ∫ ω, D ω ∂Q := by
    have := integral_mono_ae (integrable_const (β*Real.log (N:ℝ))) hsum hbad
    simpa only [integral_const,probReal_univ,one_smul] using this
  have htotal : (∫ ω, D ω ∂Q) ≤ A*(∫ ω, (M ω N:ℝ) ∂Q)+2*b*(∫ ω, (J ω N:ℝ) ∂Q) := by
    have hh := integral_mono_ae hsum ((hM.const_mul A).add (hJ.const_mul (2*b)))
      (hκ.mono (fun ω hω => total_drop_bound_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ ω hω))
    change (∫ ω, D ω ∂Q) ≤ (∫ ω, A*(M ω N:ℝ)+2*b*(J ω N:ℝ) ∂Q) at hh
    rw [integral_add (f:=fun ω => A*(M ω N:ℝ)) (g:=fun ω => 2*b*(J ω N:ℝ)) (hM.const_mul _) (hJ.const_mul _),
      integral_const_mul,integral_const_mul] at hh
    exact hh
  have hlower : 3*β/4*Real.log (N:ℝ) ≤ A*(∫ ω, (M ω N:ℝ) ∂Q) := by linarith
  have hupper : (∫ ω, (M ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b)+1 := by
    have hcount := integral_mono hM (hJ.add (integrable_const 1)) (fun ω => by
      change (M ω N:ℝ) ≤ (J ω N:ℝ)+1
      exact_mod_cast (number_stage_bound (k:=k) e f hef r fexp g χ b sfloor hR N ω N).1)
    change (∫ ω, (M ω N:ℝ) ∂Q) ≤ (∫ ω, (J ω N:ℝ)+1 ∂Q) at hcount
    rw [integral_add (f:=fun ω => (J ω N:ℝ)) (g:=fun _ => (1:ℝ)) hJ (integrable_const _)] at hcount
    simp only [integral_const,probReal_univ,one_smul] at hcount
    have hjle : (∫ ω, (J ω N:ℝ) ∂Q) ≤ β*Real.log (N:ℝ)/(8*b) := by
      apply (le_div_iff₀ (show 0<8*b by positivity)).mpr
      nlinarith only [hstages]
    linarith
  have hlong : (∫ ω, B ω ∂Q) ≤ β/2*Real.log (N:ℝ) := by
    have hl : (∫ ω, B ω ∂Q) ≤ (A/(L:ℝ)+2*b)*(∫ ω, (J ω N:ℝ) ∂Q) := by
      have hh := integral_mono_ae hB (hJ.const_mul (A/(L:ℝ)+2*b))
        (hκ.mono (fun ω hω => long_drop_bound_local (k:=k) e f hef r fexp g χ b sfloor hR N hr hf hb.le hs hH κ hκ0 hκ1 hk hbκ ω hω L hL))
      rw [integral_const_mul] at hh
      exact hh
    have hcoeff : A/(L:ℝ) ≤ 2*b := (div_le_iff₀ (Nat.cast_pos.mpr hL)).mpr hcharge
    have hnon : 0 ≤ ∫ ω, (J ω N:ℝ) ∂Q := integral_nonneg (fun _ => Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hcoeff hnon
    nlinarith only [hl,hm,hstages]
  have hsplit : (∫ ω, S ω ∂Q)+(∫ ω, B ω ∂Q)=(∫ ω, D ω ∂Q) := by
    rw [←integral_add hS hB]
    apply integral_congr_ae
    filter_upwards [] with ω
    change S ω+B ω=D ω
    dsimp only [S,B,D]
    rw [←Finset.sum_add_distrib,←dropMark_total (k:=k) e f hef r fexp g χ b sfloor hR N ω]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hh : j ω i≤L
    · simp only [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · simp only [ite_eq_right hh,ite_eq_left (Nat.lt_of_not_ge hh),zero_add]
  exact ⟨hlower,hupper,by change β/2*Real.log (N:ℝ) ≤ ∫ ω, S ω ∂Q; linarith⟩

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local_oai := @OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local_oai
