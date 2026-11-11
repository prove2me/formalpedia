-- Prove2me | solution 1 for OAI.DirectionalTransience.curvePolicy_real_tube_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:59:08.432166+00:00
-- url     : https://prove2.me/submissions/5866dda4-bb73-46c5-afa4-05992ff272ea

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePolicyPMF
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma pmf_map_cons {G : Type*} (p : PMF (List G)) (u v : G) (w : List G) :
    (p.map (List.cons u)) (v::w) = if v=u then p w else 0 := by
  rw [PMF.map_apply]
  by_cases huv : v=u
  · subst v
    simp only [List.cons.injEq,true_and]
    simp only [ite_true, if_true,eq_comm (a := w)]
    exact tsum_ite_eq w fun a => p a
  · simp [huv]

lemma finitePolicyPMF_cons {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x u : G) (n : ℕ) (w : List G) :
    finitePolicyPMF Q ω i x (n+1) (u::w) =
      Q i ω x u * finitePolicyPMF Q ω (i+1) (x+u) n w := by
  simp only [finitePolicyPMF,PMF.bind_apply,pmf_map_cons,mul_ite,mul_zero]
  simpa only [eq_comm (a := u)] using
    (tsum_ite_eq u fun a => Q i ω x a * finitePolicyPMF Q ω (i+1) (x+a) n w)

lemma finitePolicyPMF_nil_succ {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ) :
    finitePolicyPMF Q ω i x (n+1) [] = 0 := by
  simp [finitePolicyPMF,PMF.bind_apply,PMF.map_apply]

lemma finitePolicyPMF_length {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ) (w : List G)
    (hw : w.length ≠ n) : finitePolicyPMF Q ω i x n w = 0 := by
  induction n generalizing i x w with
  | zero =>
    have he : w ≠ [] := by intro h; subst w; exact hw rfl
    simp [finitePolicyPMF,PMF.pure_apply,he]
  | succ n ih =>
    cases w with
    | nil => exact finitePolicyPMF_nil_succ Q ω i x n
    | cons u w =>
      rw [finitePolicyPMF_cons,ih]
      · simp
      · simpa using hw

lemma finitePolicyPMF_measurable_atom {Ω G : Type*} [MeasurableSpace Ω] [Add G]
    (Q : ℕ → Ω → G → PMF G) (hQ : ∀ i x u, Measurable (fun ω => Q i ω x u))
    (i : ℕ) (x : G) (n : ℕ) (w : List G) :
    Measurable (fun ω => finitePolicyPMF Q ω i x n w) := by
  induction n generalizing i x w with
  | zero => exact measurable_const
  | succ n ih =>
    cases w with
    | nil => simpa only [finitePolicyPMF_nil_succ] using (measurable_const (a := (0:ℝ≥0∞)))
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      exact (hQ i x u).mul (ih (i+1) (x+u) w)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshPolicyIndependence
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.wordPath_zero
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

lemma futureRows_mono {d : ℕ} (S : ℕ → Set (Lattice d)) {i j : ℕ}
    (h : i ≤ j) : futureRows S j ⊆ futureRows S i := by
  intro x hx
  obtain ⟨k,hk,hx⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨k,h.trans hk,hx⟩

lemma rows_subset_futureRows {d : ℕ} (S : ℕ → Set (Lattice d)) (i : ℕ) :
    S i ⊆ futureRows S i := by
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨i,(show i ≤ i from le_rfl),hx⟩

lemma finitePolicyPMF_local {d : ℕ} {G : Type*} [Add G]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (i : ℕ) (x : G) (n : ℕ) (w : List G) :
    @Measurable _ _ (rowSigma (futureRows S i)) _ (fun ω => finitePolicyPMF Q ω i x n w) := by
  induction n generalizing i x w with
  | zero => exact measurable_const
  | succ n ih =>
    cases w with
    | nil =>
      simp only [finitePolicyPMF_nil_succ]
      exact measurable_const
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      exact ((hQ i x u).mono (rowSigma_mono (rows_subset_futureRows S i)) le_rfl).mul
        ((ih (i+1) (x+u) w).mono (rowSigma_mono (futureRows_mono S (by omega))) le_rfl)

lemma disjoint_rows_future {d : ℕ} (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (i : ℕ) :
    Disjoint (S i) (futureRows S (i+1)) := by
  simp only [futureRows,Set.disjoint_iUnion_right]
  intro j hj
  change i+1 ≤ j at hj
  exact hS (by omega)

lemma finitePolicyPMF_annealed {d : ℕ} {G : Type*} [Add G]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (p : PMF G) (havg : ∀ i x u, (∫⁻ ω, Q i ω x u ∂environmentLaw ν) = p u)
    (i : ℕ) (x : G) (n : ℕ) (w : List G) :
    (∫⁻ ω, finitePolicyPMF Q ω i x n w ∂environmentLaw ν) =
      finitePolicyPMF (fun _ (_ : Unit) _ => p) () i x n w := by
  induction n generalizing i x w with
  | zero => simp [finitePolicyPMF]
  | succ n ih =>
    cases w with
    | nil => simp only [finitePolicyPMF_nil_succ,lintegral_zero]
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      have hp := finitePolicyPMF_local Q S hQ (i+1) (x+u) n w
      have hind := indepFun_of_disjoint_rows ν (disjoint_rows_future S hS i)
        (fun ω => Q i ω x u) (fun ω => finitePolicyPMF Q ω (i+1) (x+u) n w)
        (hQ i x u) hp
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        ((hQ i x u).mono (rowSigma_le _) le_rfl).aemeasurable
        (hp.mono (rowSigma_le _) le_rfl).aemeasurable hind,havg,ih]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma strictRecord_suffix_iff {d : ℕ} (ℓ : Vector d) (X : Path d) {n j : ℕ}
    (hn : StrictRecord ℓ X n) (hj : 0 < j) :
    StrictRecord ℓ (fun k => X (n + k) - X n) j ↔ StrictRecord ℓ X (n + j) := by
  simp only [StrictRecord, dot_realPosition_sub, sub_lt_sub_iff_right]
  constructor
  · intro h k hk
    by_cases hkn : k < n
    · exact (hn k hkn).trans (by simpa using h 0 hj)
    · have hle : n ≤ k := by omega
      simpa only [Nat.add_sub_of_le hle] using h (k - n) (by omega)
  · intro h k hk
    exact h (n + k) (by omega)

lemma recordCount_add {d : ℕ} (ℓ : Vector d) (X : Path d) {n : ℕ}
    (hn : StrictRecord ℓ X n) (m : ℕ) :
    recordCount ℓ X (n + m) = recordCount ℓ X n +
      recordCount ℓ (fun j => X (n + j) - X n) m := by
  classical
  rw [recordCount, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.add_assoc, strictRecord_suffix_iff ℓ X hn (Nat.succ_pos j)]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordTemplate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma independent_past_current {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (W : ℕ → Ω → β) (hW : ∀ i, Measurable (W i))
    (hInd : iIndepFun W μ) (i : ℕ) :
    IndepFun (fun x => fun j : Fin i => W j x) (W i) μ := by
  have hd : Disjoint (Finset.range i) {i} := by simp
  have hh := hInd.indepFun_finset (Finset.range i) {i} hd hW
  have hc := hh.comp
    (show Measurable (fun f : (j : ↑(Finset.range i)) → β =>
      fun j : Fin i => f ⟨j, Finset.mem_range.mpr j.2⟩) by fun_prop)
    (show Measurable (fun f : (j : ↑({i} : Finset ℕ)) → β =>
      f ⟨i, Finset.mem_singleton.mpr rfl⟩) by fun_prop)
  exact hc

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma firstLayerHit_record {d : ℕ} (ℓ : Vector d) (h : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (h x : ℝ)) (H : ℤ) (n : ℕ)
    (X : Path d) (hX : X ∈ FirstLayerHit h H n) : StrictRecord ℓ X n := by
  intro j hj
  rw [hproj,hproj,hX.1]
  exact_mod_cast hX.2 j hj

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma recordCount_integer_height {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (X : Path d)
    (hstep : ∀ n, height (X (n+1)) ≤ height (X n)+1) (n : ℕ) :
    (∀ j ≤ n, height (X j) ≤ height (X 0) + (recordCount ℓ X n : ℤ)) ∧
    ∃ j ≤ n, height (X j) = height (X 0) + (recordCount ℓ X n : ℤ) := by
  classical
  induction n with
  | zero => simp [recordCount]
  | succ n ih =>
    have he : recordCount ℓ X (n+1) = recordCount ℓ X n +
      (if StrictRecord ℓ X (n+1) then 1 else 0) := recordCount_succ ℓ X n
    rw [he]
    by_cases hr : StrictRecord ℓ X (n+1)
    · rw [ite_eq_left hr]
      obtain ⟨j,hj,heq⟩ := ih.2
      have hlt := hr j (by omega)
      rw [hproj,hproj] at hlt
      have hlt' : height (X j) < height (X (n+1)) := by exact_mod_cast hlt
      have hb : height (X (n+1)) ≤ height (X 0)+(recordCount ℓ X n : ℤ)+1 := by
        have := hstep n; have := ih.1 n le_rfl; omega
      have hend : height (X (n+1)) = height (X 0)+(recordCount ℓ X n : ℤ)+1 := by omega
      constructor
      · intro k hk
        by_cases hk' : k ≤ n
        · have := ih.1 k hk'; push_cast; omega
        · have hk' : k = n+1 := by omega
          rw [hk',hend]; push_cast; omega
      · exact ⟨n+1,le_rfl,by rw [hend]; push_cast; omega⟩
    · rw [ite_eq_right hr,Nat.add_zero]
      have hb : height (X (n+1)) ≤ height (X 0)+(recordCount ℓ X n : ℤ) := by
        simp only [StrictRecord] at hr
        push Not at hr
        obtain ⟨j,hj,hj'⟩ := hr
        rw [hproj,hproj] at hj'
        have hle : height (X (n+1)) ≤ height (X j) := by exact_mod_cast hj'
        exact hle.trans (ih.1 j (by omega))
      refine ⟨fun k hk => ?_, ?_⟩
      · by_cases hk' : k ≤ n
        · exact ih.1 k hk'
        · have : k = n+1 := by omega
          simpa only [this,Nat.add_zero] using hb
      · obtain ⟨j,hj,he⟩ := ih.2
        exact ⟨j,by omega,he⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordWidth
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma recordCount_eq_height_at_record {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (X : Path d)
    (hstep : ∀ n, height (X (n+1)) ≤ height (X n)+1) {n : ℕ}
    (hn : StrictRecord ℓ X n) :
    height (X n) = height (X 0) + (recordCount ℓ X n : ℤ) := by
  obtain ⟨hb,j,hj,he⟩ := recordCount_integer_height ℓ height hproj X hstep n
  by_cases hjn : j = n
  · simpa only [hjn] using he
  · have hh := hn j (lt_of_le_of_ne hj hjn)
    rw [hproj,hproj] at hh
    have hlt : height (X j) < height (X n) := by exact_mod_cast hh
    have := hb n le_rfl
    omega

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma realPartialSum_succ (X : ℕ → ℝ) (n : ℕ) :
    realPartialSum X (n+1) = realPartialSum X n+X n := by simp [realPartialSum,Finset.sum_range_succ]

lemma partialSumMax_nonneg (X : ℕ → ℝ) (n : ℕ) : 0 ≤ partialSumMax X n := by
  induction n with
  | zero => rfl
  | succ n _ => exact (abs_nonneg _).trans (le_max_right _ _)

lemma abs_partialSum_le_max (X : ℕ → ℝ) (n : ℕ) : |realPartialSum X n| ≤ partialSumMax X n := by
  cases n with
  | zero => simp [realPartialSum,partialSumMax]
  | succ n => exact le_max_right _ _

lemma partialSumMax_mono (X : ℕ → ℝ) : Monotone (partialSumMax X) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

lemma partialSumMax_bound (X : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hX : ∀ k, |X k| ≤ z) (n : ℕ) :
    partialSumMax X n ≤ n*z := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    apply max_le
    · simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using ih.trans (le_add_of_nonneg_right hz)
    · rw [realPartialSum_succ]
      calc
        |realPartialSum X n+X n| ≤ |realPartialSum X n|+|X n| := abs_add_le _ _
        _ ≤ n*z+z := add_le_add ((abs_partialSum_le_max X n).trans ih) (hX n)
        _ = (n+1:ℕ)*z := by push_cast <;> ring

lemma abs_absSlope (t : ℝ) : |absSlope t| = 1 := by
  unfold absSlope
  split <;> simp

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

lemma abs_supporting (t x : ℝ) : absSlope t*x ≤ |t+x|-|t| := by
  by_cases ht : 0 ≤ t
  · rw [absSlope,ite_eq_left ht,one_mul,abs_of_nonneg ht]
    linarith [le_abs_self (t+x)]
  · rw [absSlope,ite_eq_right ht,neg_one_mul,abs_of_neg (lt_of_not_ge ht)]
    linarith [neg_le_abs (t+x)]

lemma max_square_increment {m a : ℝ} : (max m |a|)^2-m^2 ≤ 2*|a| * (max m |a|-m) := by
  by_cases h : |a| ≤ m
  · rw [max_eq_left h]; ring_nf; rfl
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith [sq_nonneg (|a|-m)]

lemma partialSumMax_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^2 ≤ 2*partialSumMax X n*|realPartialSum X n|-
      2*∑ k ∈ Finset.range n, partialSumMax X k*absSlope (realPartialSum X k)*X k := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    have hincr := max_square_increment (m := partialSumMax X n) (a := realPartialSum X (n+1))
    have hs := mul_le_mul_of_nonneg_left (abs_supporting (realPartialSum X n) (X n))
      (partialSumMax_nonneg X n)
    rw [← realPartialSum_succ] at hs
    rw [Finset.sum_range_succ]
    change (max (partialSumMax X n) |realPartialSum X (n+1)|)^2 ≤ _
    change _ ≤ 2*max (partialSumMax X n) |realPartialSum X (n+1)| * |realPartialSum X (n+1)|-_
    nlinarith

lemma partialSumMax_square_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^2 ≤ 4*(realPartialSum X n)^2-
      4*∑ k ∈ Finset.range n, partialSumMax X k*absSlope (realPartialSum X k)*X k := by
  have h := partialSumMax_pathwise X n
  nlinarith [sq_nonneg (partialSumMax X n-2*|realPartialSum X n|),sq_abs (realPartialSum X n)]

lemma measurable_realPartialSum {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => realPartialSum (fun k => X k ω) n) := by
  unfold realPartialSum
  fun_prop

lemma measurable_partialSumMax {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => partialSumMax (fun k => X k ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_realPartialSum X hX (n+1)).abs

lemma measurable_absSlope : Measurable absSlope :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hC ω)

lemma realPartialSum_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    realPartialSum X n = realPartialSum Y n := by
  exact Finset.sum_congr rfl fun k hk => hXY k (Finset.mem_range.mp hk)

lemma partialSumMax_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    partialSumMax X n = partialSumMax Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialSumMax,partialSumMax,ih (fun k hk => hXY k (hk.trans (Nat.lt_succ_self _))),
      realPartialSum_congr (n+1) hXY]

lemma independent_max_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => partialSumMax (fun k => X k ω) n*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  let Y (v : Fin n → ℝ) (k : ℕ) := if h : k < n then v ⟨k,h⟩ else 0
  have hY : ∀ k, Measurable (fun v => Y v k) := by
    intro k
    by_cases h : k < n <;> simp only [Y,h,↓reduceDIte] <;> fun_prop
  have hm : Measurable (fun v => partialSumMax (Y v) n*absSlope (realPartialSum (Y v) n)) :=
    (measurable_partialSumMax (fun k v => Y v k) hY n).mul
      (measurable_absSlope.comp (measurable_realPartialSum (fun k v => Y v k) hY n))
  have hh := (independent_past_current μ X hX hind n).comp hm measurable_id
  convert hh using 1
  · funext ω
    have heq : ∀ k < n, X k ω = Y (fun j : Fin n => X j ω) k := fun k hk => by simp [Y,hk]
    rw [partialSumMax_congr n heq,realPartialSum_congr n heq]
    rfl
  · rfl

lemma integrable_partialSumMax_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^2) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_partialSumMax X hX n).pow_const 2) ((n*z)^2)
  intro ω
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz (fun k => hbound k ω) n) 2

lemma integrable_realPartialSum_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    Integrable (fun ω => (realPartialSum (fun k => X k ω) n)^2) μ := by
  apply (integrable_partialSumMax_square μ X hX hz hbound n).mono'
    ((measurable_realPartialSum X hX n).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have := abs_partialSum_le_max (fun k => X k ω) n
    rw [← sq_abs (realPartialSum (fun k => X k ω) n)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma integral_partialSumMax_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ := by
  let C (k : ℕ) (ω : Ω) := partialSumMax (fun j => X j ω) k*absSlope (realPartialSum (fun j => X j ω) k)
  have hC (k : ℕ) : Measurable (C k) := (measurable_partialSumMax X hX k).mul
    (measurable_absSlope.comp (measurable_realPartialSum X hX k))
  have hCI (k : ℕ) : Integrable (fun ω => C k ω*X k ω) μ := by
    apply integrable_of_abs_bound μ _ ((hC k).mul (hX k)) (k*z*z)
    intro ω
    dsimp [C]
    rw [abs_mul,abs_mul,abs_absSlope,mul_one,abs_of_nonneg (partialSumMax_nonneg _ _)]
    exact mul_le_mul (partialSumMax_bound _ hz (fun j => hbound j ω) k) (hbound k ω)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hz)
  have hzero (k : ℕ) : ∫ ω, C k ω*X k ω ∂μ = 0 := by
    rw [(independent_max_transform μ X hX hind k).integral_fun_mul_eq_mul_integral
      (hC k).aestronglyMeasurable (hX k).aestronglyMeasurable,hmean,mul_zero]
  have hm := integral_mono (integrable_partialSumMax_square μ X hX hz hbound n)
    (((integrable_realPartialSum_square μ X hX hz hbound n).const_mul 4).sub
      ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4))
    (fun ω => partialSumMax_square_pathwise (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((integrable_realPartialSum_square μ X hX hz hbound n).const_mul 4)
    ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun k _ => hCI k)] at hm
  simpa only [hzero,Finset.sum_const_zero,mul_zero,sub_zero] using hm

lemma integral_partialSum_square_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  have hLp (k : ℕ) : MemLp (X k) 2 μ := MemLp.of_bound (hX k).aestronglyMeasurable z
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound k ω)
  have hI (k : ℕ) : Integrable (X k) μ := (hLp k).integrable (by norm_num)
  have hsum : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => hI k)]
    simp only [hmean,Finset.sum_const_zero]
  have hv := IndepFun.variance_sum (s := Finset.range n) (fun k _ => hLp k)
    (fun i _ j _ hij => hind.indepFun hij)
  have heq : (∑ k ∈ Finset.range n, X k) = (fun ω => realPartialSum (fun k => X k ω) n) := by
    ext ω
    simp only [realPartialSum,Finset.sum_apply]
  rw [heq,variance_eq_integral (measurable_realPartialSum X hX n).aemeasurable,hsum] at hv
  simpa only [variance_eq_integral (hX _).aemeasurable,hmean,sub_zero] using hv

lemma integral_partialSumMax_square_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  rw [← integral_partialSum_square_eq_sum μ X hX hind hmean hbound n]
  exact integral_partialSumMax_square_le μ X hX hind hmean hz hbound n

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitPairGap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordIndexTime_zero {d : ℕ} (ℓ : Vector d) (X : Path d) : recordIndexTime ℓ 0 X = 0 := by
  classical
  have hn : ¬ ∃ n, X ∈ RecordIndexPrefix ℓ 0 n := by
    rintro ⟨n,hn,hr,hc,_⟩
    have hh := recordCount_lt_of_strictRecord ℓ X hn hr
    simp only [recordCount_zero,hc,lt_self_iff_false] at hh
  simp only [recordIndexTime,dite_eq_right hn]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordOrZeroPrefix_time {d : ℕ} (ℓ : Vector d) {r n : ℕ} {X : Path d}
    (hX : X ∈ RecordOrZeroPrefix ℓ r n) : recordIndexTime ℓ r X = n := by
  by_cases hr : r = 0
  · subst r
    have : n = 0 := by simpa [RecordOrZeroPrefix] using hX
    rw [this,recordIndexTime_zero]
  · exact recordIndexTime_eq ℓ r n X (by simpa [RecordOrZeroPrefix,hr] using hX)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedPrefixDeterminedFuture
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma quenched_prefixDetermined_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    (n : ℕ) (A : Set (Path d)) (hA : PrefixDetermined n A)
    (B : Lattice d → Set (Path d)) (hB : ∀ y, MeasurableSet (B y)) :
    quenchedKernel (ω,x) (A ∩ FutureEvent B n) =
      ∫⁻ X in A, quenchedKernel (ω,X n) (B (X n)) ∂quenchedKernel (ω,x) := by
  let C : Set ((i : Finset.Iic n) → Lattice d) := {f | extendPrefix n f ∈ A}
  have he : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' C = A := by
    ext X
    exact hA (extendPrefix n (Preorder.frestrictLe n X)) X
      (fun j hj => by rw [extendPrefix_apply _ _ _ hj]; rfl)
  simpa only [he] using quenched_past_future ω x n C B hB

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossTranslation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma cross_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    (fun X : Path d => fun n => X n-x) ⁻¹' Cross ℓ 0 H = Cross ℓ x H := by
  ext X
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  simp only [Cross,Set.mem_preimage,Set.mem_ofPred_eq,hzero,zero_add,dot_realPosition_sub]
  constructor
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedHeightSub
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma signedHeight_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x-y) = signedHeight e x-signedHeight e y := by
  simp only [signedHeight,Pi.sub_apply]
  split <;> omega

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordOrPrefixAdd
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordOrZeroPrefix_add {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0=0)
    (s n k a : ℕ) (hpre : X ∈ RecordOrZeroPrefix ℓ s n)
    (hpost : (fun j => X (n+j)-X n) ∈ RecordOrZeroPrefix ℓ k a) :
    X ∈ RecordOrZeroPrefix ℓ (s+k) (n+a) := by
  by_cases hk : k=0
  · have ha : a=0 := by simpa [RecordOrZeroPrefix,hk] using hpost
    simpa only [hk,ha,Nat.add_zero] using hpre
  have hpost' : (fun j => X (n+j)-X n) ∈ RecordIndexPrefix ℓ k a := by
    simpa only [RecordOrZeroPrefix,ite_eq_right hk] using hpost
  have hpreR : StrictRecord ℓ X n := by
    by_cases hs : s=0
    · have hn : n=0 := by simpa [RecordOrZeroPrefix,hs] using hpre
      subst n
      exact fun j hj => by omega
    · exact (show X ∈ RecordIndexPrefix ℓ s n by simpa only [RecordOrZeroPrefix,ite_eq_right hs] using hpre).2.1
  have hpreC : recordCount ℓ X n = s := by
    by_cases hs : s=0
    · have hn : n=0 := by simpa [RecordOrZeroPrefix,hs] using hpre
      simp only [hn,hs,recordCount_zero]
    · exact (show X ∈ RecordIndexPrefix ℓ s n by simpa only [RecordOrZeroPrefix,ite_eq_right hs] using hpre).2.2.1
  have hpreD (j : ℕ) (hj : j ≤ n) : dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X j)) ℓ := by
    by_cases hs : s=0
    · have hn : n=0 := by simpa [RecordOrZeroPrefix,hs] using hpre
      have hj0 : j=0 := by omega
      rw [hj0,h0]
    · exact (show X ∈ RecordIndexPrefix ℓ s n by simpa only [RecordOrZeroPrefix,ite_eq_right hs] using hpre).2.2.2 j hj
  rw [RecordOrZeroPrefix,ite_eq_right (show s+k ≠ 0 by omega)]
  have ha0 := hpost'.1
  refine ⟨by omega,(strictRecord_suffix_iff ℓ X hpreR hpost'.1).mp hpost'.2.1,?_,?_⟩
  · rw [recordCount_add ℓ X hpreR a,hpreC,hpost'.2.2.1]
  · intro j hj
    by_cases hjn : j ≤ n
    · exact hpreD j hjn
    · have hh := hpost'.2.2.2 (j-n) (by omega)
      change dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X (n+(j-n))-X n)) ℓ at hh
      rw [Nat.add_sub_of_le (show n ≤ j by omega),dot_realPosition_sub] at hh
      have hz : dot (realPosition (0:Lattice d)) ℓ=0 := by simp [dot,realPosition]
      have hnd := hpreD n le_rfl
      rw [hz] at hh hnd ⊢
      linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_EndpointPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma coordinate_hitAt_record {d : ℕ} (e : Direction d) (x : Lattice d) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f) {H n : ℕ} (hH : 0 < H)
    (hX : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n) :
    recordIndexPosition (realPosition (step e)) H (fun j => X j-x)=X n-x := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0=0 := by simp [Y,h0]
  have hheight := coordinate_hitAt_exact e x X h0 hnn H n hX
  have hadd (u v : Lattice d) : signedHeight e (u-v)=signedHeight e u-signedHeight e v := by
    simp only [signedHeight,Pi.sub_apply]
    split_ifs <;> ring
  have hfirst : Y ∈ FirstLayerHit (signedHeight e) H n := by
    refine ⟨?_,?_⟩
    · simp only [Y,hadd,hheight,add_sub_cancel_left]
    · intro j hj
      have hh := (hX.2 j hj).2
      change dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(H:ℝ) at hh
      rw [signedHeight_projection,signedHeight_projection] at hh
      change signedHeight e (X j-x) < (H:ℤ)
      rw [hadd]
      exact_mod_cast (show (signedHeight e (X j):ℝ)-(signedHeight e x:ℝ) < (H:ℝ) by linarith)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    have hh := hfirst.1
    rw [hn0,hy0] at hh
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero] at hh
    omega
  have hrec := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) H n Y hfirst
  have hsteps (j : ℕ) : signedHeight e (Y (j+1)) ≤ signedHeight e (Y j)+1 := by
    obtain ⟨g,hg⟩ := hnn j
    have he : Y (j+1)=Y j+step g := by dsimp [Y]; rw [hg]; abel
    rw [he]
    exact signedHeight_step_le e _ g
  have hcount := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Y hsteps hrec
  rw [hfirst.1,hy0,show signedHeight e (0:Lattice d)=0 by simp [signedHeight],zero_add] at hcount
  have hr : Y ∈ RecordIndexPrefix ℓ H n := by
    refine ⟨hn,hrec,by exact_mod_cast hcount.symm,?_⟩
    intro j hj
    have hh : dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (hX.2 j hj).1
      · have hh := hX.1
        change dot (realPosition x) ℓ+(H:ℝ) ≤ dot (realPosition (X j)) ℓ at hh
        linarith [show (0:ℝ) ≤ H by positivity]
    change dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X j-x)) ℓ
    rw [dot_realPosition_sub]
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,sub_nonneg] using hh
  change X (recordIndexTime ℓ H Y)-x=X n-x
  rw [recordIndexTime_eq ℓ H n Y hr]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedMomentTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_medianDeviation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) : Measurable (medianDeviation ℓ f b H) := by
  induction H with
  | zero => exact (((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ 0)).sub_const (b 0)).abs
  | succ H ih => exact ih.max ((((measurable_of_countable (signedCoordinate f)).comp
      (measurable_recordIndexPosition ℓ (H+1))).sub_const (b (H+1))).abs)

lemma medianDeviation_tail {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (z : ℝ) :
    {X | z < medianDeviation ℓ f b H X} = MedianTubeFailure ℓ f b H z := by
  ext X
  induction H with
  | zero => simp [medianDeviation,MedianTubeFailure]
  | succ H ih =>
    change z < max _ _ ↔ ∃ j ≤ H+1, z < _
    change z < medianDeviation ℓ f b H X ↔ ∃ j ≤ H, z < _ at ih
    rw [lt_max_iff,ih]
    constructor
    · rintro (⟨j,hj,h⟩ | h)
      · exact ⟨j,by omega,h⟩
      · exact ⟨H+1,le_rfl,h⟩
    · rintro ⟨j,hj,h⟩
      by_cases he : j = H+1
      · exact Or.inr (he ▸ h)
      · exact Or.inl ⟨j,by omega,h⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curveEndpoint_future {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) :
    (∫⁻ y, quenchedKernel (ω,y) (B y) ∂curveEndpoint ℓ f x b z s ω) =
      quenchedKernel (ω,x) (⋃ n, CurvePrefixAt ℓ f x b z s n ∩ FutureEvent B n) := by
  rw [curveEndpoint,lintegral_sum_measure]
  rw [measure_iUnion (fun n m hnm => (curvePrefixAt_disjoint ℓ f x b z s hnm).mono
    Set.inter_subset_left Set.inter_subset_left)
    (fun n => (measurableSet_curvePrefixAt ℓ f x b z s n).inter (measurableSet_futureEvent B hB n))]
  apply tsum_congr; intro n
  rw [lintegral_map (measurable_of_countable _) (measurable_pi_apply n)]
  exact (quenched_prefixDetermined_future ω x n _ (curvePrefixAt_prefix ℓ f x b z s n) B hB).symm

lemma measurableSet_curveWordEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (x : Lattice d) (w : List (Lattice d)) :
    MeasurableSet (curveWordEvent ℓ f b B H x w) := by
  induction w generalizing x with
  | nil => exact MeasurableSet.univ
  | cons u w ih =>
    apply MeasurableSet.iUnion; intro n
    exact (measurableSet_curvePrefixAt ℓ f x b B H n).inter
      (measurableSet_futureEvent _ (fun y => by split_ifs; exact ih y; exact MeasurableSet.empty) n)

lemma curveWordEvent_cons_mass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) (x u : Lattice d) (w : List (Lattice d)) :
    quenchedKernel (ω,x) (curveWordEvent ℓ f b B H x (u::w)) =
      curveEndpoint ℓ f x b B H ω {x+u} *
        quenchedKernel (ω,x+u) (curveWordEvent ℓ f b B H (x+u) w) := by
  rw [curveWordEvent,← curveEndpoint_future ℓ f x b B H ω _
    (fun y => by split_ifs; exact measurableSet_curveWordEvent ℓ f b B H y w; exact MeasurableSet.empty)]
  have he : (fun y => quenchedKernel (ω,y)
      (if y=x+u then curveWordEvent ℓ f b B H y w else ∅)) =
      ({x+u} : Set (Lattice d)).indicator
        (fun _ => quenchedKernel (ω,x+u) (curveWordEvent ℓ f b B H (x+u) w)) := by
    funext y
    by_cases hy : y=x+u
    · subst y; simp
    · simp [hy,Set.indicator_of_notMem]
  rw [he,lintegral_indicator (measurableSet_singleton _),lintegral_const,Measure.restrict_apply_univ]
  exact mul_comm _ _

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveWordDisjoint
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curveWordEvent_cons_mem {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (x u : Lattice d) (w : List (Lattice d)) (X : Path d) :
    X ∈ curveWordEvent ℓ f b B H x (u::w) ↔ ∃ n,
      X ∈ CurvePrefixAt ℓ f x b B H n ∧ X n=x+u ∧
      (fun k => X (n+k)) ∈ curveWordEvent ℓ f b B H (x+u) w := by
  simp only [curveWordEvent,Set.mem_iUnion,Set.mem_inter_iff,FutureEvent,Set.mem_ofPred_eq]
  apply exists_congr; intro n
  by_cases hn : X n=x+u
  · simp [hn]
  · simp [hn]

lemma curveWordEvent_disjoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (x : Lattice d) (w v : List (Lattice d))
    (hlen : w.length=v.length) (hne : w≠v) :
    Disjoint (curveWordEvent ℓ f b B H x w) (curveWordEvent ℓ f b B H x v) := by
  induction w generalizing x v with
  | nil => cases v <;> simp_all
  | cons u w ih =>
    cases v with
    | nil => simp at hlen
    | cons u' w' =>
      apply Set.disjoint_left.mpr
      intro X hX hY
      obtain ⟨n,hn,hxu,hxt⟩ := (curveWordEvent_cons_mem ℓ f b B H x u w X).mp hX
      obtain ⟨m,hm,hxu',hxt'⟩ := (curveWordEvent_cons_mem ℓ f b B H x u' w' X).mp hY
      have hnm : n=m := by
        by_contra h
        exact Set.disjoint_left.mp (curvePrefixAt_disjoint ℓ f x b B H h) hn hm
      subst m
      have huu : u=u' := add_left_cancel (hxu.symm.trans hxu')
      subst u'
      exact Set.disjoint_left.mp (ih (x+u) w' (by simpa using hlen)
        (fun h => hne (congrArg (List.cons u) h))) hxt hxt'

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma coordinate_hitAt_recordPrefix {d : ℕ} (e : Direction d) (x : Lattice d) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ f, X (n+1)=X n+step f) {H n : ℕ} (hH : 0 < H)
    (hX : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n) :
    (fun j => X j-x) ∈ RecordIndexPrefix (realPosition (step e)) H n := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0=0 := by simp [Y,h0]
  have hheight := coordinate_hitAt_exact e x X h0 hnn H n hX
  have hadd (u v : Lattice d) : signedHeight e (u-v)=signedHeight e u-signedHeight e v := by
    simp only [signedHeight,Pi.sub_apply]
    split_ifs <;> ring
  have hfirst : Y ∈ FirstLayerHit (signedHeight e) H n := by
    refine ⟨?_,?_⟩
    · simp only [Y,hadd,hheight,add_sub_cancel_left]
    · intro j hj
      have hh := (hX.2 j hj).2
      change dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(H:ℝ) at hh
      rw [signedHeight_projection,signedHeight_projection] at hh
      change signedHeight e (X j-x) < (H:ℤ)
      rw [hadd]
      exact_mod_cast (show (signedHeight e (X j):ℝ)-(signedHeight e x:ℝ) < (H:ℝ) by linarith)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n=0 := by omega
    have hh := hfirst.1
    rw [hn0,hy0] at hh
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero] at hh
    omega
  have hrec := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) H n Y hfirst
  have hsteps (j : ℕ) : signedHeight e (Y (j+1)) ≤ signedHeight e (Y j)+1 := by
    obtain ⟨g,hg⟩ := hnn j
    have he : Y (j+1)=Y j+step g := by dsimp [Y]; rw [hg]; abel
    rw [he]
    exact signedHeight_step_le e _ g
  have hcount := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Y hsteps hrec
  rw [hfirst.1,hy0,show signedHeight e (0:Lattice d)=0 by simp [signedHeight],zero_add] at hcount
  have hr : Y ∈ RecordIndexPrefix ℓ H n := by
    refine ⟨hn,hrec,by exact_mod_cast hcount.symm,?_⟩
    intro j hj
    have hh : dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ := by
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (hX.2 j hj).1
      · have hh := hX.1
        change dot (realPosition x) ℓ+(H:ℝ) ≤ dot (realPosition (X j)) ℓ at hh
        linarith [show (0:ℝ) ≤ H by positivity]
    change dot (realPosition (0:Lattice d)) ℓ ≤ dot (realPosition (X j-x)) ℓ
    rw [dot_realPosition_sub]
    simpa only [dot,realPosition,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero,sub_nonneg] using hh
  exact hr

lemma recordPrefix_lower {d : ℕ} (ℓ : Vector d) (X : Path d) {H n j : ℕ}
    (hX : X ∈ RecordIndexPrefix ℓ H n) (hj : j ≤ H) :
    ∃ a ≤ n, X ∈ RecordOrZeroPrefix ℓ j a := by
  classical
  by_cases hj0 : j = 0
  · exact ⟨0,Nat.zero_le _,by simp [RecordOrZeroPrefix,hj0]⟩
  have hex : ∃ a, j ≤ recordCount ℓ X a := ⟨n,by rw [hX.2.2.1]; exact hj⟩
  let a := Nat.find hex
  have ha : j ≤ recordCount ℓ X a := Nat.find_spec hex
  have han : a ≤ n := Nat.find_min' hex (by rw [hX.2.2.1]; exact hj)
  have ha0 : 0 < a := by
    by_contra! hn
    have he : a = 0 := Nat.eq_zero_of_le_zero hn
    simp only [he,recordCount_zero] at ha
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha0)
  have hklt : recordCount ℓ X k < j := Nat.lt_of_not_ge
    (Nat.find_min hex (by omega))
  have hrec : StrictRecord ℓ X a := by
    by_contra hn
    rw [hk,recordCount_succ,ite_eq_right (by simpa only [hk,Nat.succ_eq_add_one] using hn),Nat.add_zero] at ha
    omega
  have hc : recordCount ℓ X a = j := by
    rw [hk,recordCount_succ,ite_eq_left (by simpa only [hk,Nat.succ_eq_add_one] using hrec)]
    rw [hk,recordCount_succ,ite_eq_left (by simpa only [hk,Nat.succ_eq_add_one] using hrec)] at ha
    omega
  refine ⟨a,han,?_⟩
  rw [RecordOrZeroPrefix,ite_eq_right hj0]
  exact ⟨ha0,hrec,hc,fun k hk => hX.2.2.2 k (hk.trans han)⟩

lemma curvePrefix_iff {d : ℕ} (e f : Direction d) (x : Lattice d) (b : ℕ → ℝ)
    (z : ℝ) {H : ℕ} (hH : 0 < H) (X : Path d)
    (h0 : X 0 = x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g) :
    X ∈ CurvePrefix (realPosition (step e)) f x b z H ↔
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      ∀ j ≤ H, |signedCoordinate f (recordIndexPosition (realPosition (step e)) j
        (fun k => X k-x))-b j| ≤ z := by
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    refine ⟨Set.mem_iUnion.mpr ⟨n,hn.1⟩,?_⟩
    intro j hj
    obtain ⟨a,ha,hr,hb⟩ := hn.2 j hj
    have ht := recordOrZeroPrefix_time _ hr
    simpa only [recordIndexPosition,ht] using hb
  · rintro ⟨hX,hbound⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    refine Set.mem_iUnion.mpr ⟨n,hn,?_⟩
    intro j hj
    obtain ⟨a,ha,hr⟩ := recordPrefix_lower _ (fun k => X k-x)
      (coordinate_hitAt_recordPrefix e x X h0 hnn hH hn) hj
    refine ⟨a,ha,hr,?_⟩
    have ht := recordOrZeroPrefix_time _ hr
    simpa only [recordIndexPosition,ht] using hbound j hj

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveEndpointLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma medianDeviation_le_iff {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (X : Path d) (B : ℝ) :
    medianDeviation ℓ f b H X ≤ B ↔
      ∀ j ≤ H, |signedCoordinate f (recordIndexPosition ℓ j X)-b j| ≤ B := by
  rw [← not_lt]
  change X ∉ {X | B < medianDeviation ℓ f b H X} ↔ _
  rw [medianDeviation_tail]
  simp [MedianTubeFailure]

lemma curvePrefix_ae_eq {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    CurvePrefix (realPosition (step e)) f x b B H =ᵐ[quenchedKernel (ω,x)]
      (Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∩
      {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} : Set (Path d)) := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  change X ∈ (CurvePrefix (realPosition (step e)) f x b B H : Set (Path d)) ↔ X ∈ (Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∩
      {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B} : Set (Path d))
  rw [curvePrefix_iff e f x b B hH X h0 hnn,Set.mem_inter_iff,Set.mem_ofPred_eq,
    medianDeviation_le_iff]

lemma curveEndpoint_eq_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    curveEndpoint (realPosition (step e)) f x b B H ω =
      ((quenchedKernel (ω,x)).restrict (CurvePrefix (realPosition (step e)) f x b B H)).map
        (fun X => x+recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) := by
  let ℓ := realPosition (step e)
  let Y := fun X : Path d => x+recordIndexPosition ℓ H (fun j => X j-x)
  have hY : Measurable Y := (measurable_const.add
    ((measurable_recordIndexPosition ℓ H).comp (by fun_prop)))
  ext U hU
  rw [curveEndpoint_apply,Measure.map_apply hY hU,Measure.restrict_apply (hY hU)]
  change (∑' n, quenchedKernel (ω,x) ((fun X => X n) ⁻¹' U ∩ CurvePrefixAt ℓ f x b B H n)) =
    quenchedKernel (ω,x) (Y ⁻¹' U ∩ ⋃ n, CurvePrefixAt ℓ f x b B H n)
  rw [Set.inter_iUnion,measure_iUnion]
  · apply tsum_congr; intro n
    apply measure_congr
    filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
    apply propext
    have he (hX : X ∈ CurvePrefixAt ℓ f x b B H n) : Y X = X n := by
      dsimp [Y]
      rw [coordinate_hitAt_record e x X h0 hnn hH hX.1]
      abel
    constructor
    · rintro ⟨hu,hn⟩
      exact ⟨by simpa only [Set.mem_preimage,he hn] using hu,hn⟩
    · rintro ⟨hu,hn⟩
      exact ⟨by simpa only [Set.mem_preimage,he hn] using hu,hn⟩
  · intro n m hnm
    exact (curvePrefixAt_disjoint ℓ f x b B H hnm).mono Set.inter_subset_right Set.inter_subset_right
  · intro n
    exact (hY hU).inter (measurableSet_curvePrefixAt ℓ f x b B H n)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma hitAt_translate_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (n : ℕ) :
    (fun X : Path d => fun j => X j-x) ⁻¹' HitAt (Strip ℓ 0 H) (Upper ℓ 0 H) n =
      HitAt (Strip ℓ x H) (Upper ℓ x H) n := by
  ext X
  simp only [Set.mem_preimage,HitAt,Strip,Upper,Set.mem_ofPred_eq,dot_realPosition_sub]
  have hz : dot (realPosition (0:Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  simp only [hz,zero_add]
  constructor
  · rintro ⟨h,h'⟩
    refine ⟨by linarith,fun j hj => ?_⟩
    have hh := h' j hj
    constructor <;> linarith [hh.1,hh.2]
  · rintro ⟨h,h'⟩
    refine ⟨by linarith,fun j hj => ?_⟩
    have hh := h' j hj
    constructor <;> linarith [hh.1,hh.2]

lemma curvePrefixAt_translate_zero {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H n : ℕ) :
    (fun X : Path d => fun j => X j-x) ⁻¹' CurvePrefixAt ℓ f 0 b B H n =
      CurvePrefixAt ℓ f x b B H n := by
  unfold CurvePrefixAt
  rw [Set.preimage_inter,hitAt_translate_zero]
  simp only [sub_zero,Set.preimage_ofPred_eq]

lemma curveEndpoint_increment_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    (curveEndpoint ℓ f x b B H ω).map (fun y => y-x) =
      curveEndpoint ℓ f 0 b B H (fun y => ω (x+y)) := by
  have hm : Measurable (fun X : Path d => fun j => X j-x) := by fun_prop
  have hmap : (quenchedKernel (ω,x)).map (fun X : Path d => fun j => X j-x) =
      quenchedKernel ((fun y => ω (x+y)),0) := by
    simpa only [add_zero] using quenched_translation ω x 0
  ext U hU
  rw [Measure.map_apply (measurable_of_countable _) hU,curveEndpoint_apply,curveEndpoint_apply]
  apply tsum_congr; intro n
  rw [← hmap,Measure.map_apply hm
    (((measurable_pi_apply n) hU).inter (measurableSet_curvePrefixAt ℓ f 0 b B H n)),
    Set.preimage_inter,curvePrefixAt_translate_zero]
  rfl

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_SelectedFiniteKernel
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma normalizeFinite_domination {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {δ : ℝ≥0∞} (_ : δ ≠ 0) (hm : δ ≤ μ Set.univ) :
    normalizeFinite μ ≤ δ⁻¹ • μ := by
  apply Measure.le_iff.mpr
  intro U hU
  simp only [normalizeFinite,Measure.smul_apply,smul_eq_mul]
  gcongr

lemma selectedFiniteKernel_domination {α : Type*} [MeasurableSpace α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    (hf : ¬failure) (hD : δ ≤ D Set.univ) (hE : strict → δ ≤ D E) :
    selectedFiniteKernel D E dummy failure strict ≤ δ⁻¹ • D := by
  simp only [selectedFiniteKernel,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    exact (normalizeFinite_domination _ hδ (by simpa using hE hs)).trans
      (by
        apply Measure.le_iff.mpr
        intro U hU
        simp only [Measure.smul_apply,smul_eq_mul]
        gcongr
        exact Measure.restrict_le_self)
  · simp only [ite_eq_right hs]
    exact normalizeFinite_domination D hδ hD

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_domination {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d)
    (hf : δ ≤ curveIncrement ℓ f x b B H ω Set.univ) :
    curvePolicy ℓ f x b B H E δ α dummy ω ≤
      (α*δ)⁻¹ • curveIncrement ℓ f x b B H ω := by
  apply selectedFiniteKernel_domination _ _ _ _ _ (mul_ne_zero hα.ne' hδ.ne') (not_lt.mpr hf)
  · exact (mul_le_of_le_one_left' hα1).trans hf
  · intro hs
    apply le_trans ?_ hs
    gcongr
    exact hf.trans (curveIncrement_le_crossing ℓ f x b B H ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    curveIncrement ℓ f x b B H ω = curveIncrement ℓ f 0 b B H (fun y => ω (x+y)) := by
  unfold curveIncrement
  rw [curveEndpoint_increment_translation]
  simp only [sub_zero]
  exact (Measure.map_id).symm

lemma crossingQuenched_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω = crossingQuenched ℓ 0 H (fun y => ω (x+y)) := by
  have hm : Measurable (fun X : Path d => fun j => X j-x) := by fun_prop
  have he := congrArg (fun μ : Measure (Path d) => μ (Cross ℓ 0 H)) (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_cross _ _ _),cross_translation] at he
  simpa only [add_zero,crossingQuenched] using he

lemma curvePolicy_translation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (ω : Environment d) :
    curvePolicy ℓ f x b B H E δ α dummy ω =
      curvePolicy ℓ f 0 b B H E δ α dummy (fun y => ω (x+y)) := by
  unfold curvePolicy
  rw [curveIncrement_translation,crossingQuenched_translation]

lemma curvePolicy_annealed_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (b : ℕ → ℝ) (B : ℝ)
    {H : ℕ} (hH : 0 < H) (E : Set (Lattice d)) (δ α : ℝ≥0∞)
    (dummy : Lattice d) (U : Set (Lattice d)) :
    (∫⁻ ω, curvePolicy ℓ f x b B H E δ α dummy ω U ∂environmentLaw ν) =
      ∫⁻ ω, curvePolicy ℓ f 0 b B H E δ α dummy ω U ∂environmentLaw ν := by
  simp_rw [curvePolicy_translation ℓ f x]
  have hm : Measurable (fun ω : Environment d => fun y => ω (x+y)) := by fun_prop
  have hp := ((Measure.measurable_coe U.to_countable.measurableSet).comp
    ((curvePolicy_rows ℓ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl))
  change (∫⁻ ω, ((fun μ => μ U) ∘ curvePolicy ℓ f 0 b B H E δ α dummy)
    ((fun ω : Environment d => fun y => ω (x+y)) ω) ∂environmentLaw ν) = _
  rw [← lintegral_map hp hm,environment_translation]
  rfl

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyLateral
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_eq_success_map {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    curveIncrement (realPosition (step e)) f x b B H ω =
      ((quenchedKernel (ω,x)).restrict
        (Cross (realPosition (step e)) x H ∩
          {X | medianDeviation (realPosition (step e)) f b H (fun j => X j-x) ≤ B})).map
        (fun X => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) := by
  rw [curveIncrement,curveEndpoint_eq_map e f x b B hH ω,Measure.map_map]
  · simp only [Function.comp_def,add_sub_cancel_left]
    congr 1
    apply Measure.restrict_congr_set
    simpa only [cross_eq_hit] using curvePrefix_ae_eq e f x b B hH ω
  · exact measurable_of_countable _
  · exact measurable_const.add ((measurable_recordIndexPosition _ _).comp (by fun_prop))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveEndpoint_supported {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂curveEndpoint (realPosition (step e)) f x b B H ω,
      signedHeight e y = signedHeight e x+H := by
  rw [ae_iff,curveEndpoint_apply]
  apply ENNReal.tsum_eq_zero.mpr; intro n
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  rintro ⟨hbad,hCurve⟩
  exact hbad (coordinate_hitAt_exact e x X h0 hnn H n hCurve.1)

lemma curveIncrement_supported {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    ∀ᵐ y ∂curveIncrement (realPosition (step e)) f x b B H ω, signedHeight e y = H := by
  rw [curveIncrement,ae_map_iff (measurable_of_countable _).aemeasurable
    (Set.to_countable _ |>.measurableSet)]
  filter_upwards [curveEndpoint_supported e f x b B H ω] with y hy
  rw [signedHeight_sub,hy]
  omega

lemma selectedFiniteKernel_supported {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] (P : α → Prop)
    (hd : P dummy) (hD : ∀ᵐ u ∂D, P u) :
    ∀ᵐ u ∂selectedFiniteKernel D E dummy failure strict, P u := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,ite_eq_left hf,ae_dirac_eq,Filter.eventually_pure]
    exact hd
  simp only [selectedFiniteKernel,ite_eq_right hf,normalizeFinite]
  rw [ae_iff,Measure.smul_apply,smul_eq_mul]
  have he : ∀ᵐ u ∂(if strict then D.restrict E else D), P u := by
    split_ifs
    · exact hD.filter_mono (ae_mono Measure.restrict_le_self)
    · exact hD
  rw [ae_iff.mp he,mul_zero]

lemma curvePolicy_supported {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (hd : signedHeight e dummy = H) (ω : Environment d) :
    ∀ᵐ y ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
      signedHeight e y = H :=
  selectedFiniteKernel_supported _ _ _ _ _ _ hd (curveIncrement_supported e f x b B H ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveIncrement_lateral_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    ∀ᵐ u ∂curveIncrement (realPosition (step e)) f x b B H ω,
      |signedCoordinate f u-b H| ≤ B := by
  have hm : Measurable (fun X : Path d => recordIndexPosition (realPosition (step e)) H (fun j => X j-x)) :=
    (measurable_recordIndexPosition _ _).comp (by fun_prop)
  rw [curveIncrement_eq_success_map e f x b B hH ω,
    ae_map_iff hm.aemeasurable (Set.to_countable _ |>.measurableSet)]
  filter_upwards [ae_restrict_mem (measurableSet_cross _ _ _ |>.inter
    (measurableSet_le ((measurable_medianDeviation _ f b H).comp (by fun_prop)) measurable_const))]
    with X hX
  exact (medianDeviation_le_iff _ f b H _ B).mp hX.2 H le_rfl

lemma curvePolicy_lateral_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) (δ α : ℝ≥0∞) (dummy : Lattice d)
    (hd : signedCoordinate f dummy = b H) (ω : Environment d) :
    ∀ᵐ u ∂curvePolicy (realPosition (step e)) f x b B H E δ α dummy ω,
      |signedCoordinate f u-b H| ≤ B :=
  selectedFiniteKernel_supported _ _ _ _ _ _ (by simpa [hd] using hB)
    (curveIncrement_lateral_bound e f x b B hH ω)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_AlignedSlabs
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma signedHeight_align {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d) :
    signedHeight e (alignHeight e a x) = a := by
  rw [alignHeight,signedHeight_add,signedHeight_zsmul_step]
  omega

lemma alignHeight_eq_self {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d)
    (hx : signedHeight e x = a) : alignHeight e a x = x := by
  simp [alignHeight,hx]

lemma blockRows_pairwise {d : ℕ} (e : Direction d) (H : ℕ) :
    Pairwise (fun i j => Disjoint (blockRows e H i) (blockRows e H j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  change (i:ℤ)*H ≤ signedHeight e x ∧ signedHeight e x < (i:ℤ)*H+H at hx
  change (j:ℤ)*H ≤ signedHeight e x ∧ signedHeight e x < (j:ℤ)*H+H at hy
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i:ℤ)+1 ≤ j := by exact_mod_cast h
    nlinarith [Int.natCast_nonneg H]
  · have hh : (j:ℤ)+1 ≤ i := by exact_mod_cast h
    nlinarith [Int.natCast_nonneg H]

lemma strip_align_blockRows {d : ℕ} (e : Direction d) (H i : ℕ) (x : Lattice d) :
    Strip (realPosition (step e)) (alignHeight e ((i:ℤ)*H) x) H = blockRows e H i := by
  ext y
  simp only [Strip,Set.mem_ofPred_eq,signedHeight_projection,signedHeight_align,blockRows]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyPMF
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicyPMF_apply {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy u : Lattice d) (ω : Environment d) :
    curvePolicyPMF ℓ f x b B H E hδ hα dummy ω u = curvePolicy ℓ f x b B H E δ α dummy ω {u} := rfl

lemma curvePolicyPMF_average {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy u : Lattice d) :
    (∫⁻ ω, curvePolicyPMF ℓ f x b B H E hδ hα dummy ω u ∂environmentLaw ν) =
      curvePolicy_average ν ℓ f b B hH E hδ hα dummy u := by
  simp only [curvePolicyPMF_apply]
  rw [curvePolicy_annealed_translation ν ℓ f x b B hH E δ α dummy]
  symm
  change ((environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy)) {u} = _
  exact Measure.bind_apply (measurableSet_singleton u)
    ((curvePolicy_rows ℓ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl).aemeasurable

lemma alignedCurvePolicy_rows {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d)) {δ α : ℝ≥0∞}
    (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (i : ℕ) (x u : Lattice d) :
    @Measurable _ _ (rowSigma (blockRows e H i)) _
      (fun ω => alignedCurvePolicy e f b B H E hδ hα dummy i ω x u) := by
  have hm := (Measure.measurable_coe (measurableSet_singleton u)).comp
    (curvePolicy_rows (realPosition (step e)) f (alignHeight e ((i:ℤ)*H) x) b B hH E δ α dummy)
  rwa [strip_align_blockRows] at hm

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma curveIncrement_singleton {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) (u : Lattice d) :
    curveIncrement ℓ f x b B H ω {u} = curveEndpoint ℓ f x b B H ω {x+u} := by
  rw [curveIncrement,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton u)]
  congr 1
  ext y
  simp only [Set.mem_preimage,Set.mem_singleton_iff]
  constructor
  · intro h; rw [sub_eq_iff_eq_add] at h; simpa only [add_comm] using h
  · intro h; rw [h]; abel

lemma curvePolicyPMF_atom_domination {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (u : Lattice d)
    (hf : δ ≤ curveIncrement ℓ f x b B H ω Set.univ) :
    curvePolicyPMF ℓ f x b B H E hδ hα dummy ω u ≤
      (α*δ)⁻¹ * curveEndpoint ℓ f x b B H ω {x+u} := by
  have h := Measure.le_iff'.mp (curvePolicy_domination ℓ f x b B H E hδ hα hα1 dummy ω hf)
    {u}
  simpa only [curvePolicyPMF_apply,Measure.smul_apply,smul_eq_mul,curveIncrement_singleton] using h

lemma curvePolicy_word_density {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (w : List (Lattice d))
    (hs : policySafe (fun y => δ ≤ curveIncrement ℓ f y b B H ω Set.univ) x w) :
    finitePolicyPMF (fun _ ω x => curvePolicyPMF ℓ f x b B H E hδ hα dummy ω) ω i x w.length w ≤
      ((α*δ)⁻¹)^w.length * quenchedKernel (ω,x) (curveWordEvent ℓ f b B H x w) := by
  induction w generalizing i x with
  | nil => simp [finitePolicyPMF,curveWordEvent]
  | cons u w ih =>
    rw [List.length_cons,finitePolicyPMF_cons,curveWordEvent_cons_mass]
    have h₁ := curvePolicyPMF_atom_domination ℓ f x b B H E hδ hα hα1 dummy ω u hs.1
    have h₂ := ih (i+1) (x+u) hs.2
    apply (mul_le_mul' h₁ h₂).trans_eq
    rw [pow_succ]
    ring

attribute [local instance] OAI.DirectionalTransience.instMeasurableSpaceListLattice
local instance instMeasurableSingletonClassListLattice {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_event_density {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (n : ℕ)
    (S : Set (List (Lattice d))) (hlen : ∀ w ∈ S, w.length=n)
    (hs : ∀ w ∈ S, policySafe (fun y => δ ≤ curveIncrement ℓ f y b B H ω Set.univ) x w) :
    (finitePolicyPMF (fun _ ω x => curvePolicyPMF ℓ f x b B H E hδ hα dummy ω) ω i x n).toMeasure S ≤
      ((α*δ)⁻¹)^n * quenchedKernel (ω,x) (⋃ w ∈ S, curveWordEvent ℓ f b B H x w) := by
  let A (w : List (Lattice d)) : Set (Path d) := if w ∈ S then curveWordEvent ℓ f b B H x w else ∅
  have ha : ∀ w, MeasurableSet (A w) := by
    intro w; dsimp [A]; split_ifs; exact measurableSet_curveWordEvent ℓ f b B H x w; exact MeasurableSet.empty
  have haDis : Pairwise (fun w v => Disjoint (A w) (A v)) := by
    intro w v hwv
    dsimp [A]
    split_ifs with hw hv hv
    · exact curveWordEvent_disjoint ℓ f b B H x w v ((hlen w hw).trans (hlen v hv).symm) hwv
    all_goals simp
  have he : (⋃ w ∈ S, curveWordEvent ℓ f b B H x w) = ⋃ w, A w := by
    ext X
    simp only [Set.mem_iUnion,A,Set.mem_ite_empty_right]
    constructor <;> rintro ⟨w,hw,hX⟩ <;> exact ⟨w,hw,hX⟩
  rw [he,measure_iUnion haDis ha,← ENNReal.tsum_mul_left,PMF.toMeasure_apply _ S.to_countable.measurableSet]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw,A,ite_eq_left hw]
    simpa only [hlen w hw] using curvePolicy_word_density ℓ f b B H E hδ hα hα1 dummy ω i x w (hs w hw)
  · simp [A,hw]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyAlignment
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicyPMF_zero {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (hd : signedHeight e dummy = H) (ω : Environment d) (u : Lattice d)
    (hu : signedHeight e u ≠ H) :
    curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω u = 0 := by
  rw [curvePolicyPMF_apply]
  apply measure_mono_null (show {u} ⊆ {u | ¬signedHeight e u = H} by simpa)
  exact ae_iff.mp (curvePolicy_supported e f x b B H E δ α dummy hd ω)

lemma curvePolicy_alignment {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (hd : signedHeight e dummy = H) (ω : Environment d) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) (w : List (Lattice d)) :
    finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n w = finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x n w := by
  induction n generalizing i x w with
  | zero => rfl
  | succ n ih =>
    cases w with
    | nil => simp only [finitePolicyPMF_nil_succ]
    | cons u w =>
      rw [finitePolicyPMF_cons,finitePolicyPMF_cons]
      have he : alignedCurvePolicy e f b B H E hδ hα dummy i ω x =
          curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω := by
        simp only [alignedCurvePolicy,alignHeight_eq_self e _ x hx]
      rw [he]
      by_cases hu : signedHeight e u = H
      · rw [ih (i+1) (x+u) (by rw [signedHeight_add,hx,hu]; push_cast <;> ring)]
      · rw [curvePolicyPMF_zero e f x b B H E hδ hα dummy hd ω u hu]
        simp

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma iidListPMF_ofFn {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (p : PMF G) (n : ℕ) (f : Fin n → G) :
    iidListPMF p n (List.ofFn f) = ∏ i, p (f i) := by
  rw [iidListPMF,PMF.map_apply]
  simp only [List.ofFn_injective.eq_iff]
  rw [tsum_ite_eq' f]
  change Measure.pi (fun _ : Fin n => p.toMeasure) {f} = _
  rw [Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i _
  exact p.toMeasure_apply_singleton (f i) (measurableSet_singleton _)

lemma iidListPMF_length {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (p : PMF G) (n : ℕ) (w : List G) (hw : w.length ≠ n) :
    iidListPMF p n w = 0 := by
  rw [iidListPMF,PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro f
  have hf : w ≠ List.ofFn f := fun h => hw (by rw [h,List.length_ofFn])
  simp only [ite_eq_right hf]

lemma finitePolicyPMF_const_ofFn {G : Type*} [Add G] (p : PMF G)
    (n i : ℕ) (x : G) (f : Fin n → G) :
    finitePolicyPMF (fun _ (_ : Unit) _ => p) () i x n (List.ofFn f) = ∏ j, p (f j) := by
  induction n generalizing i x with
  | zero => simp [List.ofFn_zero,finitePolicyPMF]
  | succ n ih =>
    rw [List.ofFn_succ,finitePolicyPMF_cons,ih,Fin.prod_univ_succ]

lemma iidListPMF_eq_const {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] [Add G] (p : PMF G) (n i : ℕ) (x : G) :
    iidListPMF p n = finitePolicyPMF (fun _ (_ : Unit) _ => p) () i x n := by
  ext w
  by_cases hw : w.length=n
  · subst n
    rw [← List.ofFn_get w]
    simp only [List.length_ofFn]
    rw [iidListPMF_ofFn,finitePolicyPMF_const_ofFn]
  · rw [iidListPMF_length p n w hw,finitePolicyPMF_length _ _ _ _ _ w hw]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finitePolicyPMF_annealed_event {d : ℕ} {G : Type*} [Add G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (p : PMF G) (havg : ∀ i x u, (∫⁻ ω, Q i ω x u ∂environmentLaw ν) = p u)
    (i : ℕ) (x : G) (n : ℕ) (B : Set (List G)) :
    (∫⁻ ω, (finitePolicyPMF Q ω i x n).toMeasure B ∂environmentLaw ν) = (iidListPMF p n).toMeasure B := by
  simp only [PMF.toMeasure_apply _ B.to_countable.measurableSet]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro w
    simp only [Set.indicator_apply]
    split_ifs with h
    · rw [finitePolicyPMF_annealed ν Q S hS hQ p havg,iidListPMF_eq_const p n i x]
    · simp
  · intro w
    simp only [Set.indicator_apply]
    split_ifs
    · exact (finitePolicyPMF_measurable_atom Q
        (fun j x u => (hQ j x u).mono (rowSigma_le _) le_rfl) i x n w).aemeasurable
    · exact aemeasurable_const

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IidListProcess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma iid_list_hasLaw {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : PMF G) (X : ℕ → Ω → G)
    (hX : ∀ k, Measurable (X k)) (hLaw : ∀ k, HasLaw (X k) p.toMeasure μ)
    (hind : iIndepFun X μ) (n : ℕ) :
    HasLaw (fun ω => List.ofFn (fun i : Fin n => X i ω)) (iidListPMF p n).toMeasure μ := by
  have hfin := hind.precomp (f := X) (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have hm : Measurable (fun ω => fun i : Fin n => X i ω) := Measurable.of_eval (fun index => hX index)
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin n => (hX i).aemeasurable)).mp hfin
  simp only [(hLaw _).map_eq] at he
  constructor
  · exact ((measurable_of_countable List.ofFn).comp hm).aemeasurable
  · rw [iidListPMF,← PMF.toMeasure_map _ _ (measurable_of_countable List.ofFn),Measure.toPMF_toMeasure,
      ← he,Measure.map_map (measurable_of_countable List.ofFn) hm]
    rfl

lemma partialSumMax_initial_congr (X Y : ℕ → ℝ) (n : ℕ) (h : ∀ k < n, X k=Y k) :
    partialSumMax X n = partialSumMax Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [partialSumMax]
    rw [ih (fun k hk => h k (by omega))]
    congr 1
    congr 1
    exact Finset.sum_congr rfl (fun k hk => h k (Finset.mem_range.mp hk))

lemma listCenteredMax_ofFn {G : Type*} (F : G → ℝ) (c : ℝ) (X : ℕ → G) (n : ℕ) :
    listCenteredMax F c (List.ofFn (fun i : Fin n => X i)) =
      partialSumMax (fun k => F (X k)-c) n := by
  unfold listCenteredMax
  simp only [List.length_ofFn]
  apply partialSumMax_initial_congr
  intro k hk
  simp only [dite_eq_left hk,List.get_ofFn,Fin.val_cast]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_apply (w : ℝ≥0) (z : ℝ) : symmetricClip w z = max (-(w:ℝ)) (min (w:ℝ) z) := rfl

lemma symmetricClip_bound (w : ℝ≥0) (z : ℝ) : |symmetricClip w z| ≤ w := by
  rw [symmetricClip_apply,abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [w.coe_nonneg]) (min_le_left _ _)⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_eq_self (w : ℝ≥0) {z : ℝ} (hz : |z|≤w) : symmetricClip w z=z := by
  obtain ⟨hl,hr⟩ := abs_le.mp hz
  simp only [symmetricClip_apply,min_eq_right hr,max_eq_right hl]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AeMaximalSquare
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
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

lemma integral_partialSumMax_square_le_sum_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  let w : ℝ≥0 := ⟨z,hz⟩
  let Y := fun k ω => symmetricClip w (X k ω)
  have hY (k) : Measurable (Y k) := (symmetricClip w).continuous.measurable.comp (hX k)
  have he (k) : Y k =ᵐ[μ] X k := by
    filter_upwards [hbound k] with ω hω
    exact symmetricClip_eq_self w hω
  have hYe := ae_all_iff.mpr he
  have hInd : iIndepFun Y μ := hind.comp (fun _ => symmetricClip w) (fun _ => (symmetricClip w).continuous.measurable)
  have hm (k) : ∫ ω, Y k ω ∂μ = 0 := (integral_congr_ae (he k)).trans (hmean k)
  have hc := integral_partialSumMax_square_le_sum μ Y hY hInd hm hz
    (fun k ω => symmetricClip_bound w _) n
  have hleft : (∫ ω, (partialSumMax (fun k => Y k ω) n)^2 ∂μ) =
      ∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hYe] with ω hω
    rw [funext hω]
  have hright (k) : (∫ ω, (Y k ω)^2 ∂μ) = ∫ ω, (X k ω)^2 ∂μ :=
    integral_congr_ae ((he k).fun_comp fun x => x^2)
  simpa only [hleft,hright] using hc

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma integrable_abs_sub_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (b B : ℝ) (hb : ∀ᵐ ω ∂μ, |F ω-b| ≤ B) : Integrable F μ := by
  apply Integrable.of_bound hF.aestronglyMeasurable (B+|b|)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs]
  calc |F ω| = |(F ω-b)+b| := by congr 1; ring
       _ ≤ |F ω-b|+|b| := abs_add_le _ _
       _ ≤ B+|b| := add_le_add hω le_rfl

lemma abs_mean_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (b B : ℝ) (hb : ∀ᵐ ω ∂μ, |F ω-b| ≤ B) : |(∫ ω, F ω ∂μ)-b| ≤ B := by
  have hi := integrable_abs_sub_bounded μ F hF b B hb
  have he : (∫ ω, F ω-b ∂μ) = (∫ ω, F ω ∂μ)-b := by
    rw [integral_sub hi (integrable_const b),integral_const,probReal_univ,one_smul]
  rw [← he,← Real.norm_eq_abs]
  have hn := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => F ω-b)
    (C := B) (by simpa only [Real.norm_eq_abs] using hb)
  simpa only [probReal_univ,mul_one] using hn

lemma integral_centered_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F) (b : ℝ) :
    (∫ ω, (F ω-(∫ x, F x ∂μ))^2 ∂μ) ≤ ∫ ω, (F ω-b)^2 ∂μ := by
  rw [← variance_eq_integral hF.aemeasurable,← variance_sub_const hF.aestronglyMeasurable b]
  exact variance_le_expectation_sq (hF.sub_const b).aestronglyMeasurable

lemma iidList_integral_max_square_le {G : Type*} [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (p : PMF G) (F : G → ℝ) (b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ u ∂p.toMeasure, |F u-b| ≤ B) (n : ℕ) :
    (∫ w, (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2 ∂(iidListPMF p n).toMeasure) ≤
      4*(n:ℝ)*(∫ u, (F u-b)^2 ∂p.toMeasure) := by
  obtain ⟨Ω,mΩ,μ,X,hX,hLaw,hind,hprob⟩ := exists_iid ℕ p.toMeasure
  let := mΩ
  let := hprob
  let c := ∫ u, F u ∂p.toMeasure
  let Y := fun k ω => F (X k ω)-c
  have hF : Measurable F := measurable_of_countable F
  have hFB := integrable_abs_sub_bounded p.toMeasure F hF b B hbound
  have hcb : |c-b| ≤ B := abs_mean_sub_le p.toMeasure F hF b B hbound
  have hY (k) : Measurable (Y k) := (hF.comp (hX k)).sub_const c
  have hYB (k) : ∀ᵐ ω ∂μ, |Y k ω| ≤ 2*B := by
    have hb : ∀ᵐ ω ∂μ, |F (X k ω)-b| ≤ B :=
      (hLaw k).ae_iff (by fun_prop) |>.mpr hbound
    filter_upwards [hb] with ω hω
    calc |Y k ω| = |(F (X k ω)-b)-(c-b)| := by congr 1; dsimp [Y]; ring
         _ ≤ |F (X k ω)-b|+|c-b| := abs_sub _ _
         _ ≤ 2*B := by linarith
  have hYi (k) : Integrable (fun ω => F (X k ω)) μ := by
    have hi : Integrable F (μ.map (X k)) := by rw [(hLaw k).map_eq]; exact hFB
    exact hi.comp_measurable (hX k)
  have hmean (k) : ∫ ω, Y k ω ∂μ = 0 := by
    change (∫ ω, F (X k ω)-c ∂μ) = 0
    rw [integral_sub (hYi k) (integrable_const c),integral_const,probReal_univ,one_smul]
    have he := (hLaw k).integral_comp hF.aestronglyMeasurable
    simp only [Function.comp_apply] at he
    rw [he]; exact sub_self _
  have hInd : iIndepFun Y μ := hind.comp (fun _ u => F u-c) (fun _ => hF.sub_const c)
  have hm := integral_partialSumMax_square_le_sum_ae μ Y hY hInd hmean (by positivity) hYB n
  have hs (k) : (∫ ω, (Y k ω)^2 ∂μ) ≤ ∫ u, (F u-b)^2 ∂p.toMeasure := by
    change (∫ ω, (F (X k ω)-c)^2 ∂μ) ≤ _
    have he := (hLaw k).integral_comp (by fun_prop : AEStronglyMeasurable (fun u => (F u-c)^2) p.toMeasure)
    simp only [Function.comp_apply] at he
    rw [he]
    exact integral_centered_square_le p.toMeasure F hF b
  have hl := iid_list_hasLaw μ p X hX hLaw hind n
  have he := hl.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun w => (listCenteredMax F c w)^2) (iidListPMF p n).toMeasure)
  simp only [Function.comp_apply] at he
  have he2 : (∫ ω, (partialSumMax (fun k => Y k ω) n)^2 ∂μ) =
      ∫ w, (listCenteredMax F c w)^2 ∂(iidListPMF p n).toMeasure := by
    rw [← he]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => congrArg (fun x : ℝ => x^2)
      (listCenteredMax_ofFn F c (fun k => X k ω) n).symm)
  rw [← he2]
  calc _ ≤ 4*∑ k ∈ Finset.range n, ∫ ω, (Y k ω)^2 ∂μ := hm
       _ ≤ 4*∑ _k ∈ Finset.range n, ∫ u, (F u-b)^2 ∂p.toMeasure :=
         mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hs k)) (by norm_num)
       _ = 4*(n:ℝ)*(∫ u, (F u-b)^2 ∂p.toMeasure) := by
         simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] <;> ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma integrable_partialSumMax_pow_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^p) μ := by
  apply Integrable.of_bound ((measurable_partialSumMax X hX n).pow_const p).aestronglyMeasurable ((n*z)^p)
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz hω n) p

lemma iidList_integrable_max_square {G : Type*} [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (p : PMF G) (F : G → ℝ) (b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ u ∂p.toMeasure, |F u-b| ≤ B) (n : ℕ) :
    Integrable (fun w => (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2) (iidListPMF p n).toMeasure := by
  obtain ⟨Ω,mΩ,μ,X,hX,hLaw,hind,hprob⟩ := exists_iid ℕ p.toMeasure
  let := mΩ
  let := hprob
  let c := ∫ u, F u ∂p.toMeasure
  let Y := fun k ω => F (X k ω)-c
  have hF : Measurable F := measurable_of_countable F
  have hcb : |c-b| ≤ B := abs_mean_sub_le p.toMeasure F hF b B hbound
  have hY (k) : Measurable (Y k) := (hF.comp (hX k)).sub_const c
  have hYB (k) : ∀ᵐ ω ∂μ, |Y k ω| ≤ 2*B := by
    have hb : ∀ᵐ ω ∂μ, |F (X k ω)-b| ≤ B :=
      (hLaw k).ae_iff (by fun_prop) |>.mpr hbound
    filter_upwards [hb] with ω hω
    calc |Y k ω| = |(F (X k ω)-b)-(c-b)| := by congr 1; dsimp [Y]; ring
         _ ≤ |F (X k ω)-b|+|c-b| := abs_sub _ _
         _ ≤ 2*B := by linarith
  have hi := integrable_partialSumMax_pow_ae μ Y hY (by positivity) hYB n 2
  have hl := iid_list_hasLaw μ p X hX hLaw hind n
  change Integrable (fun w => (listCenteredMax F c w)^2) (iidListPMF p n).toMeasure
  rw [← hl.map_eq]
  apply (integrable_map_measure (by fun_prop) hl.aemeasurable).mpr
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  exact congrArg (fun x : ℝ => x^2) (listCenteredMax_ofFn F c (fun k => X k ω) n)

lemma iidList_max_tail {G : Type*} [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (p : PMF G) (F : G → ℝ) (b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ u ∂p.toMeasure, |F u-b| ≤ B) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (iidListPMF p n).toMeasure.real {w | r ≤ listCenteredMax F (∫ u, F u ∂p.toMeasure) w} ≤
      (4*(n:ℝ)*(∫ u, (F u-b)^2 ∂p.toMeasure))/r^2 := by
  have hi := iidList_integrable_max_square p F b hB hbound n
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := (iidListPMF p n).toMeasure)
    (f := fun w => (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2)
    (Eventually.of_forall fun _ => sq_nonneg _) hi (r^2)
  have he : {w | r^2 ≤ (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2} =
      {w | r ≤ listCenteredMax F (∫ u, F u ∂p.toMeasure) w} := by
    ext w
    exact sq_le_sq₀ hr.le (partialSumMax_nonneg _ _)
  rw [he] at hm
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  rw [mul_comm]
  exact hm.trans (iidList_integral_max_square_le p F b hB hbound n)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_CurvePolicyKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_average_toMeasure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) :
    (curvePolicy_average ν ℓ f b B hH E hδ hα dummy).toMeasure =
      (environmentLaw ν).bind (curvePolicy ℓ f 0 b B H E δ α dummy) := by
  have := curvePolicy_average_probability ν ℓ f b B hH E hδ hα dummy
  exact Measure.toPMF_toMeasure _

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyMaximal
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curvePolicy_average_lateral_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    ∀ᵐ u ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure,
      |signedCoordinate f u-b H| ≤ B := by
  rw [curvePolicy_average_toMeasure,ae_iff,Measure.bind_apply (Set.to_countable _ |>.measurableSet)
    ((curvePolicy_rows _ f 0 b B hH E δ α dummy).mono (rowSigma_le _) le_rfl).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact Eventually.of_forall (fun ω => ae_iff.mp (curvePolicy_lateral_bound e f 0 b hB hH E δ α dummy hd ω))

attribute [local instance] OAI.DirectionalTransience.CurvePolicyMaximalMs
local instance CurvePolicyMaximalSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_event_iid {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy = H) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) (S : Set (List (Lattice d))) :
    (∫⁻ ω, (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure S ∂environmentLaw ν) =
      (iidListPMF (curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy) n).toMeasure S := by
  have he (ω : Environment d) :
      finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n =
      finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x n := by
    ext w
    exact curvePolicy_alignment e f b B H E hδ hα dummy hd ω i x hx n w
  simp_rw [he]
  apply finitePolicyPMF_annealed_event ν _ (blockRows e H) (blockRows_pairwise e H)
    (alignedCurvePolicy_rows e f b B hH E hδ hα dummy)
  intro j y u
  exact curvePolicyPMF_average ν (realPosition (step e)) f _ b B hH E hδ hα dummy u

lemma curvePolicy_maximal_tail {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy = H)
    (hdb : signedCoordinate f dummy = b H) (i : ℕ) (x : Lattice d)
    (hx : signedHeight e x = (i:ℤ)*H) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    let p := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
    let c := ∫ u, signedCoordinate f u ∂p.toMeasure
    (∫⁻ ω, (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure {w | r ≤ listCenteredMax (signedCoordinate f) c w} ∂environmentLaw ν).toReal ≤
      (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂p.toMeasure))/r^2 := by
  dsimp only
  rw [curvePolicy_event_iid ν e f b B hH E hδ hα dummy hd i x hx n]
  exact iidList_max_tail _ _ (b H) hB
    (curvePolicy_average_lateral_bound ν e f b hB hH E hδ hα dummy hdb) n hr

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma policySafe_iff {G : Type*} [AddMonoid G] (Good : G → Prop) (x : G) (w : List G) :
    policySafe Good x w ↔ ∀ j < w.length, Good (x+(w.take j).sum) := by
  induction w generalizing x with
  | nil => simp [policySafe]
  | cons u w ih =>
    rw [policySafe,ih]
    constructor
    · rintro ⟨hx,hw⟩ j hj
      cases j with
      | zero => simpa using hx
      | succ j => simpa only [List.take_succ_cons,List.sum_cons,← add_assoc] using (hw j (by simpa using hj))
    · intro h
      refine ⟨by simpa using h 0 (by simp),?_⟩
      intro j hj
      simpa only [List.take_succ_cons,List.sum_cons,← add_assoc] using h (j+1) (by simpa using hj)

lemma curvePolicy_word_height {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (hd : signedHeight e dummy = H) (ω : Environment d) (i : ℕ) (x : Lattice d)
    (n : ℕ) (w : List (Lattice d))
    (hw : finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n w ≠ 0) : ∀ u ∈ w, signedHeight e u=H := by
  induction n generalizing i x w with
  | zero =>
    have he : w=[] := by
      by_contra he
      exact hw (finitePolicyPMF_length _ ω i x 0 w (by simpa using he))
    simp [he]
  | succ n ih =>
    cases w with
    | nil => simp
    | cons u w =>
      rw [finitePolicyPMF_cons] at hw
      have hu := (mul_ne_zero_iff.mp hw).1
      have ht := ih (i+1) (x+u) w (mul_ne_zero_iff.mp hw).2
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · by_contra hh
        exact hu (curvePolicyPMF_zero e f x b B H E hδ hα dummy hd ω v hh)
      · exact ht v hv

lemma signedHeight_sum_of_constant {d : ℕ} (e : Direction d) (H : ℤ) (w : List (Lattice d))
    (hw : ∀ u ∈ w, signedHeight e u=H) : signedHeight e w.sum=(w.length:ℤ)*H := by
  induction w with
  | nil => simp [signedHeight]
  | cons u w ih =>
    rw [List.sum_cons,signedHeight_add,hw u (by simp),ih (fun v hv => hw v (by simp [hv]))]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finitePolicyPMF_take {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (m n : ℕ) :
    (finitePolicyPMF Q ω i x (m+n)).map (List.take m) = finitePolicyPMF Q ω i x m := by
  induction m generalizing i x with
  | zero =>
    rw [Nat.zero_add]
    have he : List.take 0 = Function.const (List G) [] := by funext w; simp
    rw [he,PMF.map_const]
    rfl
  | succ m ih =>
    rw [show m+1+n = (m+n)+1 by omega]
    rw [finitePolicyPMF,PMF.map_bind,finitePolicyPMF]
    congr 1
    funext u
    rw [PMF.map_comp]
    have he : List.take (m+1) ∘ List.cons u = List.cons u ∘ List.take m := by
      funext w; simp
    rw [he,← PMF.map_comp,ih]

lemma finitePolicyPMF_prior_local {d : ℕ} {G : Type*} [Add G]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (i : ℕ) (x : G) (n t : ℕ) (hnt : i+n ≤ t) (w : List G) :
    @Measurable _ _ (rowSigma (priorRows S t)) _ (fun ω => finitePolicyPMF Q ω i x n w) := by
  induction n generalizing i x w with
  | zero => exact measurable_const
  | succ n ih =>
    cases w with
    | nil => simp only [finitePolicyPMF_nil_succ]; exact measurable_const
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      have hs : S i ⊆ priorRows S t := by
        intro y hy
        exact Set.mem_iUnion₂.mpr ⟨i,(show i<t by omega),hy⟩
      exact ((hQ i x u).mono (rowSigma_mono hs) le_rfl).mul
        (ih (i+1) (x+u) (by omega) w)

lemma disjoint_prior_rows {d : ℕ} (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (t : ℕ) :
    Disjoint (priorRows S t) (S t) := by
  simp only [priorRows,Set.disjoint_iUnion_left]
  intro j hj
  exact hS (ne_of_lt hj)

lemma finitePolicyPMF_fresh_test {d : ℕ} {G : Type*} [AddMonoid G] [Countable G]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (B : Environment d → G → ℝ≥0∞) (i n : ℕ) (x : G)
    (hB : ∀ y, @Measurable _ _ (rowSigma (S (i+n))) _ (fun ω => B ω y))
    (b : ℝ≥0∞) (havg : ∀ y, (∫⁻ ω, B ω y ∂environmentLaw ν) = b) :
    (∫⁻ ω, ∑' w : List G, finitePolicyPMF Q ω i x n w * B ω (x+w.sum) ∂environmentLaw ν) = b := by
  have hp (w : List G) := finitePolicyPMF_prior_local Q S hQ i x n (i+n) le_rfl w
  rw [lintegral_tsum]
  · have he (w : List G) :
        (∫⁻ ω, finitePolicyPMF Q ω i x n w * B ω (x+w.sum) ∂environmentLaw ν) =
          (∫⁻ ω, finitePolicyPMF Q ω i x n w ∂environmentLaw ν)*b := by
      have hind := indepFun_of_disjoint_rows ν (disjoint_prior_rows S hS (i+n))
        (fun ω => finitePolicyPMF Q ω i x n w) (fun ω => B ω (x+w.sum)) (hp w) (hB _)
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        ((hp w).mono (rowSigma_le _) le_rfl).aemeasurable
        ((hB _).mono (rowSigma_le _) le_rfl).aemeasurable hind,havg]
    simp_rw [he]
    rw [ENNReal.tsum_mul_right,← lintegral_tsum]
    · simp only [PMF.tsum_coe,lintegral_one,measure_univ,one_mul]
    · intro w; exact ((hp w).mono (rowSigma_le _) le_rfl).aemeasurable
  · intro w
    exact (((hp w).mono (rowSigma_le _) le_rfl).mul
      ((hB _).mono (rowSigma_le _) le_rfl)).aemeasurable

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurveCenter
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_mean_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedCoordinate f dummy = b H) :
    |(∫ u, signedCoordinate f u ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure)-b H| ≤ B :=
  abs_mean_sub_le _ _ (measurable_of_countable _) _ _
    (curvePolicy_average_lateral_bound ν e f b hB hH E hδ hα dummy hd)

lemma median_line_mean_bound (b : ℕ → ℝ) {H : ℕ} (hH : 0 < H) {m B D : ℝ}
    (hB : 0 ≤ B) (hm : |m-b H| ≤ B)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*b H/H| ≤ D) :
    ∀ j ≤ H, |b j-(j:ℝ)*(m/H)| ≤ D+B := by
  intro j hj
  have hHp : (0:ℝ)<H := by exact_mod_cast hH
  have hratio : 0 ≤ (j:ℝ)/H := by positivity
  have hratio1 : (j:ℝ)/H ≤ 1 := (div_le_one hHp).mpr (by exact_mod_cast hj)
  calc
    _ = |(b j-(j:ℝ)*b H/H)+((j:ℝ)/H)*(b H-m)| := by congr 1; ring
    _ ≤ |b j-(j:ℝ)*b H/H|+|((j:ℝ)/H)*(b H-m)| := abs_add_le _ _
    _ = |b j-(j:ℝ)*b H/H|+((j:ℝ)/H)*|m-b H| := by rw [abs_mul,abs_of_nonneg hratio,abs_sub_comm (b H) m]
    _ ≤ D+B := add_le_add (hb j hj) ((mul_le_mul_of_nonneg_left hm hratio).trans (mul_le_of_le_one_left hB hratio1))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePolicyFailure
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma finitePolicyPMF_prefix_event {Ω G : Type*} [AddMonoid G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) {j N : ℕ} (hj : j ≤ N)
    (B : G → Prop) :
    (finitePolicyPMF Q ω i x N).toMeasure {w | B (x+(w.take j).sum)} =
      (finitePolicyPMF Q ω i x j).toMeasure {w | B (x+w.sum)} := by
  have he := congrArg (fun p : PMF (List G) => p.toMeasure {w | B (x+w.sum)})
    (finitePolicyPMF_take Q ω i x j (N-j))
  rw [Nat.add_sub_of_le hj,PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _)
    (Set.to_countable _ |>.measurableSet)] at he
  exact he

lemma finitePolicyPMF_fresh_failure {d : ℕ} {G : Type*} [AddMonoid G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (Bad : Environment d → G → Prop) (i n : ℕ) (x : G)
    (hB : ∀ y, @MeasurableSet _ (rowSigma (S (i+n))) {ω | Bad ω y})
    (p : ℝ≥0∞) (havg : ∀ y, environmentLaw ν {ω | Bad ω y} = p) :
    (∫⁻ ω, (finitePolicyPMF Q ω i x n).toMeasure {w | Bad ω (x+w.sum)} ∂environmentLaw ν) = p := by
  simp_rw [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
  have he (ω : Environment d) (w : List G) :
      ({w | Bad ω (x+w.sum)}.indicator (finitePolicyPMF Q ω i x n)) w =
        finitePolicyPMF Q ω i x n w * (if Bad ω (x+w.sum) then 1 else 0) := by
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
    split_ifs <;> simp
  simp_rw [he]
  apply finitePolicyPMF_fresh_test ν Q S hS hQ (fun ω y => if Bad ω y then 1 else 0) i n x
    (fun y => Measurable.ite (hB y) measurable_const measurable_const) p
  intro y
  have hm := (rowSigma_le _) _ (hB y)
  change (∫⁻ ω, ({ω | Bad ω y}.indicator (fun _ => (1:ℝ≥0∞))) ω ∂environmentLaw ν) = p
  rw [lintegral_indicator hm]
  simpa only [lintegral_one,Measure.restrict_apply_univ] using havg y

lemma finitePolicyPMF_failure_union {d : ℕ} {G : Type*} [AddMonoid G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (Bad : ℕ → Environment d → G → Prop)
    (hB : ∀ j y, @MeasurableSet _ (rowSigma (S j)) {ω | Bad j ω y})
    (p : ℝ≥0∞) (havg : ∀ j y, environmentLaw ν {ω | Bad j ω y} = p)
    (i N : ℕ) (x : G) :
    (∫⁻ ω, (finitePolicyPMF Q ω i x N).toMeasure
      {w | ∃ j < N, Bad (i+j) ω (x+(w.take j).sum)} ∂environmentLaw ν) ≤ (N:ℝ≥0∞)*p := by
  have hpt (ω : Environment d) :
      (finitePolicyPMF Q ω i x N).toMeasure {w | ∃ j < N, Bad (i+j) ω (x+(w.take j).sum)} ≤
        ∑ j ∈ Finset.range N, (finitePolicyPMF Q ω i x j).toMeasure {w | Bad (i+j) ω (x+w.sum)} := by
    rw [show {w : List G | ∃ j < N, Bad (i+j) ω (x+(w.take j).sum)} =
      ⋃ j ∈ Finset.range N, {w | Bad (i+j) ω (x+(w.take j).sum)} by ext w; simp]
    apply (measure_biUnion_finset_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    exact (finitePolicyPMF_prefix_event Q ω i x (Finset.mem_range.mp hj).le (Bad (i+j) ω)).le
  apply (lintegral_mono hpt).trans
  rw [lintegral_finsetSum]
  · simp_rw [finitePolicyPMF_fresh_failure ν Q S hS hQ _ i _ x (hB _) p (havg _)]
    simp
  · intro j hj
    simp only [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
    apply Measurable.tsum
    intro w
    exact Measurable.ite ((rowSigma_le _) _ (hB _ _))
      (finitePolicyPMF_measurable_atom Q (fun j x u => (hQ j x u).mono (rowSigma_le _) le_rfl) i x j w)
      measurable_const

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curveFailure_rows {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (δ : ℝ≥0∞) (j : ℕ) (y : Lattice d) :
    @MeasurableSet _ (rowSigma (blockRows e H j))
      {ω | curveIncrement (realPosition (step e)) f (alignHeight e ((j:ℤ)*H) y) b B H ω Set.univ < δ} := by
  have hm := (Measure.measurable_coe MeasurableSet.univ).comp
    (curveIncrement_rows (realPosition (step e)) f (alignHeight e ((j:ℤ)*H) y) b B hH)
  rw [strip_align_blockRows] at hm
  exact measurableSet_lt hm measurable_const

lemma curveFailure_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x : Lattice d) (b : ℕ → ℝ) (B : ℝ)
    {H : ℕ} (hH : 0 < H) (δ : ℝ≥0∞) :
    environmentLaw ν {ω | curveIncrement ℓ f x b B H ω Set.univ < δ} =
      environmentLaw ν {ω | curveIncrement ℓ f 0 b B H ω Set.univ < δ} := by
  have hm : MeasurableSet {ω | curveIncrement ℓ f 0 b B H ω Set.univ < δ} :=
    measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
      ((curveIncrement_rows ℓ f 0 b B hH).mono (rowSigma_le _) le_rfl)) measurable_const
  have hshift : Measurable (fun ω : Environment d => fun y => ω (x+y)) := by fun_prop
  have he := congrArg (fun μ : Measure (Environment d) => μ {ω | curveIncrement ℓ f 0 b B H ω Set.univ < δ})
    (environment_translation ν x)
  rw [Measure.map_apply hshift hm] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext ω
  simp only [Set.mem_preimage,Set.mem_ofPred_eq]
  exact (congrArg (fun D : Measure (Lattice d) => D Set.univ < δ) (curveIncrement_translation ℓ f x b B H ω)).to_iff

attribute [local instance] OAI.DirectionalTransience.CurvePolicyFailureMs
local instance CurvePolicyFailureSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma alignedCurvePolicy_failure_union {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (i N : ℕ) (x : Lattice d) :
    (∫⁻ ω, (finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x N).toMeasure
      {w | ∃ j < N, curveIncrement (realPosition (step e)) f
        (alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum)) b B H ω Set.univ < δ} ∂environmentLaw ν) ≤
      (N:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} := by
  apply finitePolicyPMF_failure_union ν _ (blockRows e H) (blockRows_pairwise e H)
    (alignedCurvePolicy_rows e f b B hH E hδ hα dummy) _
    (curveFailure_rows e f b B hH δ)
  intro j y
  exact curveFailure_translation ν (realPosition (step e)) f _ b B hH δ

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
attribute [local instance] OAI.DirectionalTransience.CurveActualFailureMs
local instance CurveActualFailureSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_actual_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) (B : ℝ) {H : ℕ} (hH : 0 < H)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (i N : ℕ) (x : Lattice d)
    (hx : signedHeight e x=(i:ℤ)*H) :
    (∫⁻ ω, (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x N).toMeasure {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w}
      ∂environmentLaw ν) ≤
      (N:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} := by
  have he (ω : Environment d) :
      (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
        ω i x N).toMeasure {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w} =
      (finitePolicyPMF (alignedCurvePolicy e f b B H E hδ hα dummy) ω i x N).toMeasure
        {w | ∃ j < N, curveIncrement (realPosition (step e)) f
          (alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum)) b B H ω Set.univ < δ} := by
    simp only [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
    apply tsum_congr; intro w
    have hal := curvePolicy_alignment e f b B H E hδ hα dummy hd ω i x hx N w
    by_cases hw : finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
        ω i x N w = 0
    · simp [Set.indicator_apply,← hal,hw]
    · have hlen : w.length=N := by
        by_contra h; exact hw (finitePolicyPMF_length _ ω i x N w h)
      have hheight := curvePolicy_word_height e f b B H E hδ hα dummy hd ω i x N w hw
      have halt (j : ℕ) (hj : j < N) :
          alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum) = x+(w.take j).sum := by
        apply alignHeight_eq_self
        rw [signedHeight_add,hx,signedHeight_sum_of_constant e H (w.take j)
          (fun u hu => hheight u (List.mem_of_mem_take hu)),List.length_take,hlen,min_eq_left hj.le]
        ring
      have hpred : (¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w) ↔
          ∃ j < N, curveIncrement (realPosition (step e)) f (alignHeight e (((i+j):ℤ)*H) (x+(w.take j).sum)) b B H ω Set.univ < δ := by
        rw [policySafe_iff]
        simp only [not_forall,not_le,hlen]
        constructor <;> rintro ⟨j,hj,h⟩ <;> refine ⟨j,hj,?_⟩
        · simpa only [halt j hj] using h
        · simpa only [halt j hj] using h
      simp only [Set.indicator_apply,Set.mem_ofPred_eq,hpred,hal]
  simp_rw [he]
  exact alignedCurvePolicy_failure_union ν e f b B hH E hδ hα dummy i N x

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ListPrefixSum
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma realPartialSum_list {G : Type*} (F : G → ℝ) (c : ℝ) (w : List G) {k : ℕ} (hk : k ≤ w.length) :
    realPartialSum (fun j => if h : j < w.length then F (w.get ⟨j,h⟩)-c else 0) k =
      ((w.take k).map F).sum-(k:ℝ)*c := by
  induction k with
  | zero => simp [realPartialSum]
  | succ k ih =>
    rw [realPartialSum_succ,ih (by omega)]
    have hkl : k < w.length := by omega
    rw [dite_eq_left hkl]
    rw [List.take_add_one,List.getElem?_eq_getElem hkl]
    simp only [List.get_eq_getElem,Option.toList_some,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,Nat.cast_add,Nat.cast_one]
    ring

lemma signedCoordinate_list_sum {d : ℕ} (f : Direction d) (w : List (Lattice d)) :
    (w.map (signedCoordinate f)).sum=signedCoordinate f w.sum := by
  induction w with
  | nil => simp [signedCoordinate]
  | cons u w ih => simp only [List.map_cons,List.sum_cons,signedCoordinate_add,ih]

lemma listCenteredMax_prefix {d : ℕ} (f : Direction d) (c : ℝ) (w : List (Lattice d))
    {k : ℕ} (hk : k ≤ w.length) :
    |signedCoordinate f (w.take k).sum-(k:ℝ)*c| ≤ listCenteredMax (signedCoordinate f) c w := by
  rw [← signedCoordinate_list_sum]
  rw [← realPartialSum_list _ c w hk]
  exact (abs_partialSum_le_max _ k).trans (partialSumMax_mono _ hk)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PolicyGoodMass
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma measurable_pmf_dependent_event {Ω G : Type*} [MeasurableSpace Ω]
    [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    (p : Ω → PMF G) (hp : ∀ w, Measurable (fun ω => p ω w))
    (S : Ω → Set G) (hS : ∀ w, MeasurableSet {ω | w ∈ S ω}) :
    Measurable (fun ω => (p ω).toMeasure (S ω)) := by
  simp only [PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
  apply Measurable.tsum
  intro w
  change Measurable (fun ω => Set.indicator {ω | w ∈ S ω} (fun ω => p ω w) ω)
  exact (hp w).indicator (hS w)

lemma finitePolicy_length_mass {Ω G : Type*} [Add G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)] [Countable G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ) :
    ∀ᵐ w ∂(finitePolicyPMF Q ω i x n).toMeasure, w.length=n := by
  rw [ae_iff,PMF.toMeasure_apply _ (Set.to_countable _ |>.measurableSet)]
  apply ENNReal.tsum_eq_zero.mpr
  intro w
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  split_ifs with h
  · rfl
  · exact finitePolicyPMF_length Q ω i x n w h

lemma probability_three_cover {G : Type*} [MeasurableSpace G] (μ : Measure G)
    [IsProbabilityMeasure μ] (A B C : Set G)
    (hc : ∀ᵐ w ∂μ, w ∈ A ∨ w ∈ B ∨ w ∈ C) :
    1 ≤ μ A + (μ B+μ C) := by
  calc
    1 = μ Set.univ := (measure_univ).symm
    _ ≤ μ (A ∪ (B ∪ C)) := measure_mono_ae (hc.mono (fun w hw _ => hw))
    _ ≤ μ A + μ (B ∪ C) := measure_union_le _ _
    _ ≤ μ A + (μ B+μ C) := add_le_add_right (measure_union_le _ _) _

lemma ennreal_half_good {a b : ℝ≥0∞} (hab : 1 ≤ a+b) (hb : b < (1:ℝ≥0∞)/2) :
    (1:ℝ≥0∞)/2 ≤ a := by
  by_contra h
  have ha : a < (1:ℝ≥0∞)/2 := lt_of_not_ge h
  have ht : a+b < (1:ℝ≥0∞)/2 + (1:ℝ≥0∞)/2 := ENNReal.add_lt_add ha hb
  rw [ENNReal.add_halves] at ht
  exact (not_lt_of_ge hab) ht

lemma policy_good_mass {Ω G : Type*} [AddMonoid G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)] [Countable G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ)
    (Good : G → Prop) (M : List G → ℝ) (r : ℝ)
    (hcost : (finitePolicyPMF Q ω i x n).toMeasure {w | ¬policySafe Good x w} +
      (finitePolicyPMF Q ω i x n).toMeasure {w | r ≤ M w} < (1:ℝ≥0∞)/2) :
    (1:ℝ≥0∞)/2 ≤ (finitePolicyPMF Q ω i x n).toMeasure
      {w | w.length=n ∧ policySafe Good x w ∧ M w ≤ r} := by
  apply ennreal_half_good (probability_three_cover _ _ _ _ ?_) hcost
  filter_upwards [finitePolicy_length_mass Q ω i x n] with w hw
  by_cases hgood : policySafe Good x w
  · by_cases hm : M w ≤ r
    · exact Or.inl ⟨hw,hgood,hm⟩
    · exact Or.inr (Or.inr (le_of_lt (lt_of_not_ge hm)))
  · exact Or.inr (Or.inl hgood)

lemma low_mass_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cost mass : Ω → ℝ≥0∞) (hc : AEMeasurable cost μ) (c : ℝ≥0∞)
    (hgood : ∀ ω, cost ω < (1:ℝ≥0∞)/2 → c ≤ mass ω) :
    μ {ω | mass ω < c} ≤ 2*(∫⁻ ω, cost ω ∂μ) := by
  have hs : {ω | mass ω < c} ⊆ {ω | (1:ℝ≥0∞)/2 ≤ cost ω} := by
    intro ω hw
    by_contra h
    exact (not_lt_of_ge (hgood ω (lt_of_not_ge h))) hw
  calc
    μ {ω | mass ω < c} ≤ μ {ω | (1:ℝ≥0∞)/2 ≤ cost ω} := measure_mono hs
    _ ≤ (∫⁻ ω, cost ω ∂μ)/((1:ℝ≥0∞)/2) := meas_ge_le_lintegral_div hc (by norm_num) (by norm_num)
    _ = 2*(∫⁻ ω, cost ω ∂μ) := by simp [div_eq_mul_inv,mul_comm]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
attribute [local instance] OAI.DirectionalTransience.CurvePolicyMeasurableMs
local instance CurvePolicyMeasurableSingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma policySafe_measurable {Ω G : Type*} [MeasurableSpace Ω] [Add G]
    (Good : Ω → G → Prop) (hG : ∀ x, MeasurableSet {ω | Good ω x}) (x : G) (w : List G) :
    MeasurableSet {ω | policySafe (Good ω) x w} := by
  induction w generalizing x with
  | nil => exact MeasurableSet.univ
  | cons u w ih => exact (hG x).inter (ih (x+u))

lemma curvePolicy_atom_measurable {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (i : ℕ) (x : Lattice d) (n : ℕ) (w : List (Lattice d)) :
    Measurable (fun ω => finitePolicyPMF (fun _ ω x => curvePolicyPMF
      (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n w) := by
  apply finitePolicyPMF_measurable_atom
  intro _ x u
  exact (Measure.measurable_coe (measurableSet_singleton u)).comp
    ((curvePolicy_rows (realPosition (step e)) f x b B hH E δ α dummy).mono (rowSigma_le _) le_rfl)

lemma curvePolicy_failure_measurable {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (i : ℕ) (x : Lattice d) (n : ℕ) :
    Measurable (fun ω => (finitePolicyPMF (fun _ ω x => curvePolicyPMF
      (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n).toMeasure
        {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w}) := by
  apply measurable_pmf_dependent_event _ (curvePolicy_atom_measurable e f b B hH E hδ hα dummy i x n)
  intro w
  apply MeasurableSet.compl
  apply policySafe_measurable
  intro y
  apply measurableSet_le measurable_const
  exact (Measure.measurable_coe MeasurableSet.univ).comp
    ((curveIncrement_rows (realPosition (step e)) f y b B hH).mono (rowSigma_le _) le_rfl)

lemma curvePolicy_fixed_event_measurable {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) {H : ℕ} (hH : 0 < H) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d)
    (i : ℕ) (x : Lattice d) (n : ℕ) (S : Set (List (Lattice d))) :
    Measurable (fun ω => (finitePolicyPMF (fun _ ω x => curvePolicyPMF
      (realPosition (step e)) f x b B H E hδ hα dummy ω) ω i x n).toMeasure S) :=
  measurable_pmf_dependent_event _ (curvePolicy_atom_measurable e f b B hH E hδ hα dummy i x n)
    (fun _ => S) (fun w => MeasurableSet.const (w ∈ S))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ShiftedCurveConcatenation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma shiftedCurvePrefixAt_concatenate {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ a z : ℝ) {s : ℕ} (hs : 0 < s) (n k m : ℕ) (X : Path d) (h0 : X 0=x)
    (hnn : ∀ j, ∃ g, X (j+1)=X j+step g)
    (hpre : X ∈ CurvePrefixAt (realPosition (step e)) f x (fun j => (j:ℝ)*θ-a) z s n)
    (hpost : (fun j => X (n+j)) ∈ CurvePrefixAt (realPosition (step e)) f (X n)
      (fun j => (j:ℝ)*θ-(a+signedCoordinate f (X n-x)-(s:ℝ)*θ)) z k m) :
    X ∈ CurvePrefixAt (realPosition (step e)) f x (fun j => (j:ℝ)*θ-a) z (s+k) (n+m) := by
  let ℓ := realPosition (step e)
  have hheight : dot (realPosition (X n)) ℓ = dot (realPosition x) ℓ+(s:ℝ) := by
    have hh := coordinate_hitAt_exact e x X h0 hnn s n hpre.1
    simp only [ℓ,signedHeight_projection,hh,Int.cast_add,Int.cast_natCast]
  have hrec : (fun j => X j-x) ∈ RecordOrZeroPrefix ℓ s n := by
    simpa only [RecordOrZeroPrefix,ite_eq_right (Nat.ne_of_gt hs)] using
      coordinate_hitAt_recordPrefix e x X h0 hnn hs hpre.1
  refine ⟨⟨?_,?_⟩,?_⟩
  · have hh := hpost.1.1
    change dot (realPosition (X n)) ℓ+(k:ℝ) ≤ dot (realPosition (X (n+m))) ℓ at hh
    change dot (realPosition x) ℓ+((s+k:ℕ):ℝ) ≤ dot (realPosition (X (n+m))) ℓ
    rw [hheight,Nat.cast_add] at *
    linarith
  · intro j hj
    change dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ ∧
      dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+((s+k:ℕ):ℝ)
    rw [Nat.cast_add]
    by_cases hjn : j<n
    · have hh := hpre.1.2 j hjn
      change dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ ∧
        dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(s:ℝ) at hh
      exact ⟨hh.1,by linarith [hh.2,show (0:ℝ) ≤ k by positivity]⟩
    · have hh := hpost.1.2 (j-n) (by omega)
      change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j-n)))) ℓ ∧
        dot (realPosition (X (n+(j-n)))) ℓ < dot (realPosition (X n)) ℓ+(k:ℝ) at hh
      rw [Nat.add_sub_of_le (show n ≤ j by omega),hheight] at hh
      exact ⟨by linarith [hh.1,show (0:ℝ) ≤ s by positivity],by linarith [hh.2]⟩
  · intro j hj
    by_cases hjs : j ≤ s
    · obtain ⟨a,ha,hra,hga⟩ := hpre.2 j hjs
      exact ⟨a,by omega,hra,hga⟩
    · obtain ⟨a,ha,hra,hga⟩ := hpost.2 (j-s) (by omega)
      refine ⟨n+a,by omega,?_,?_⟩
      · have hh := recordOrZeroPrefix_add ℓ (fun b => X b-x) (by rw [h0,sub_self]) s n (j-s) a hrec
          (by convert hra using 1; ext b; dsimp; abel)
        simpa only [Nat.add_sub_of_le (show s ≤ j by omega)] using hh
      · have he : X (n+a)-x = (X n-x)+(X (n+a)-X n) := by abel
        have hadd (u v : Lattice d) : signedCoordinate f (u+v)=signedCoordinate f u+signedCoordinate f v := by
          simp only [signedCoordinate,Pi.add_apply,Int.cast_add]
          split_ifs <;> ring
        have hcast : (j:ℝ)=(s:ℝ)+((j-s:ℕ):ℝ) := by exact_mod_cast (Nat.add_sub_of_le (show s ≤ j by omega)).symm
        dsimp only at hga ⊢
        rw [he,hadd,hcast]
        convert hga using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CurveWordTube
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma curvePrefixAt_center_comparison {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b c : ℕ → ℝ) (B D : ℝ) (H n : ℕ) (X : Path d)
    (hc : ∀ j ≤ H, |b j-c j| ≤ D) (hX : X ∈ CurvePrefixAt ℓ f x b B H n) :
    X ∈ CurvePrefixAt ℓ f x c (B+D) H n := by
  refine ⟨hX.1,?_⟩
  intro j hj
  obtain ⟨a,ha,hr,hg⟩ := hX.2 j hj
  refine ⟨a,ha,hr,?_⟩
  calc
    _ = |(signedCoordinate f (X a-x)-b j)+(b j-c j)| := by congr 1; ring
    _ ≤ |signedCoordinate f (X a-x)-b j|+|b j-c j| := abs_add_le _ _
    _ ≤ B+D := add_le_add hg (hc j hj)

lemma curveWordEvent_shifted_tube {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {H : ℕ} (hH : 0 < H)
    (θ a r : ℝ) (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (w : List (Lattice d))
    (hp : ∀ k ≤ w.length, |a+signedCoordinate f (w.take k).sum-(k:ℝ)*(H:ℝ)*θ| ≤ r)
    (X : Path d) (h0 : X 0=x) (hnn : ∀ j, ∃ g, X (j+1)=X j+step g)
    (hX : X ∈ curveWordEvent (realPosition (step e)) f b B H x w) :
    ∃ n, X ∈ CurvePrefixAt (realPosition (step e)) f x
      (fun j => (j:ℝ)*θ-a) (r+B+D) (w.length*H) n := by
  induction w generalizing x X a with
  | nil =>
    have ha : |a| ≤ r := by simpa [signedCoordinate] using hp 0 le_rfl
    refine ⟨0,⟨?_,?_⟩,?_⟩
    · simp [Upper,h0]
    · intro j hj; omega
    · intro j hj
      have hj0 : j=0 := by simpa using hj
      subst j
      refine ⟨0,le_rfl,?_,?_⟩
      · simp [RecordOrZeroPrefix]
      · simpa [h0,signedCoordinate] using ha.trans (by linarith : r ≤ r+B+D)
  | cons u w ih =>
    obtain ⟨n,hn,hnu,hnt⟩ := (curveWordEvent_cons_mem _ f b B H x u w X).mp hX
    let a' := a+signedCoordinate f u-(H:ℝ)*θ
    have hp' : ∀ k ≤ w.length, |a'+signedCoordinate f (w.take k).sum-(k:ℝ)*(H:ℝ)*θ| ≤ r := by
      intro k hk
      have hh := hp (k+1) (by simp only [List.length_cons]; omega)
      simp only [List.take_succ_cons,List.sum_cons,signedCoordinate_add,Nat.cast_add,Nat.cast_one] at hh
      dsimp [a']
      convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
    have hnt' : (fun j => X (n+j)) ∈ curveWordEvent (realPosition (step e)) f b B H (X n) w := by simpa only [hnu] using hnt
    obtain ⟨m,hm⟩ := ih (X n) a' hp' (fun j => X (n+j)) (by simp)
      (fun j => by simpa only [Nat.add_assoc] using hnn (n+j)) hnt'
    have ha : |a| ≤ r := by simpa [signedCoordinate] using hp 0 (Nat.zero_le _)
    have hc : ∀ j ≤ H, |b j-((j:ℝ)*θ-a)| ≤ D+r := by
      intro j hj
      calc
        _ = |(b j-(j:ℝ)*θ)+a| := by congr 1; ring
        _ ≤ |b j-(j:ℝ)*θ|+|a| := abs_add_le _ _
        _ ≤ D+r := add_le_add (hb j hj) ha
    have hn' := curvePrefixAt_center_comparison _ f x b (fun j => (j:ℝ)*θ-a) B (D+r) H n X hc hn
    have hn'' : X ∈ CurvePrefixAt (realPosition (step e)) f x (fun j => (j:ℝ)*θ-a) (r+B+D) H n := by
      simpa only [add_comm,add_left_comm,add_assoc] using hn'
    have ha' : a'=a+signedCoordinate f (X n-x)-(H:ℝ)*θ := by
      simp only [a',hnu,add_sub_cancel_left]
    rw [ha'] at hm
    have hh := shiftedCurvePrefixAt_concatenate e f x θ a (r+B+D) hH n (w.length*H) m X h0 hnn hn'' hm
    refine ⟨n+m,?_⟩
    simpa only [List.length_cons,Nat.add_mul,one_mul,Nat.add_comm] using hh

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CurvePolicyTubeMass
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

attribute [local instance] OAI.DirectionalTransience.CurvePolicyTubeMassMs
local instance CurvePolicyTubeMassSingleton_r9ced5b_1 {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩
lemma curvePolicy_tube_density {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {H : ℕ} (hH : 0 < H)
    (θ r : ℝ) (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (n : ℕ) :
    (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure {w | w.length=n ∧
        policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w ∧
        listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w ≤ r} ≤
      ((α*δ)⁻¹)^n * quenchedKernel (ω,x)
        (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)) := by
  let S : Set (List (Lattice d)) := {w | w.length=n ∧
        policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w ∧
        listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w ≤ r}
  have hd := curvePolicy_event_density (realPosition (step e)) f b B H E hδ hα hα1 dummy ω i x n S
    (fun _ h => h.1) (fun _ h => h.2.1)
  apply hd.trans
  apply mul_le_mul_right
  apply measure_mono_ae
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hX
  obtain ⟨w,hX⟩ := Set.mem_iUnion.mp hX
  obtain ⟨hw,hX⟩ := Set.mem_iUnion.mp hX
  have hmax := hw.2.2
  have hp : ∀ k ≤ w.length, |(0:ℝ)+signedCoordinate f (w.take k).sum-(k:ℝ)*(H:ℝ)*θ| ≤ r := by
    intro k hk
    simpa only [zero_add,mul_assoc] using (listCenteredMax_prefix f ((H:ℝ)*θ) w hk).trans hmax
  obtain ⟨m,hm⟩ := curveWordEvent_shifted_tube e f x b hB hD hH θ 0 r hb w hp X h0 hnn hX
  apply Set.mem_iUnion.mpr
  refine ⟨m,?_⟩
  simpa only [hw.1,sub_zero,CurvePrefixAt,TubePrefixAt] using hm

lemma curvePolicy_tube_mass {d : ℕ} (e f : Direction d)
    (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {H : ℕ} (hH : 0 < H)
    (θ r : ℝ) (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (ω : Environment d) (i : ℕ) (x : Lattice d) (n : ℕ) :
    (α*δ)^n *
      (finitePolicyPMF (fun _ ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω)
      ω i x n).toMeasure {w | w.length=n ∧
        policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w ∧
        listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w ≤ r} ≤
      quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)) := by
  have hd := mul_le_mul_right (curvePolicy_tube_density e f b hB hD hH θ r hb E hδ hα hα1 dummy ω i x n) ((α*δ)^n)
  have hne : α*δ ≠ 0 := mul_ne_zero hα.ne' hδ.ne'
  have ht : α*δ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (by simpa using mul_le_mul' hα1 hδ1) ENNReal.one_lt_top)
  simpa only [← mul_assoc,← mul_pow,ENNReal.mul_inv_cancel hne ht,one_pow,one_mul] using hd

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
attribute [local instance] OAI.DirectionalTransience.CurvePolicyTubeProbabilityMs
local instance CurvePolicyTubeProbabilitySingleton {d : ℕ} : MeasurableSingletonClass (List (Lattice d)) := ⟨fun _ => trivial⟩

lemma curvePolicy_tube_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    {H : ℕ} (hH : 0 < H) (θ : ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (hdb : signedCoordinate f dummy=b H)
    (i n : ℕ) (x : Lattice d) (hx : signedHeight e x=(i:ℤ)*H)
    (hc : (H:ℝ)*θ = ∫ u, signedCoordinate f u
      ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure) :
    environmentLaw ν {ω | quenchedKernel (ω,x)
      (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)) < (α*δ)^n/2} ≤
      2*((n:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} +
        ENNReal.ofReal ((4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2
          ∂(curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy).toMeasure))/r^2)) := by
  let Q := fun (_ : ℕ) ω x => curvePolicyPMF (realPosition (step e)) f x b B H E hδ hα dummy ω
  let F := fun ω => (finitePolicyPMF Q ω i x n).toMeasure
    {w | ¬policySafe (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ) x w}
  let M := fun ω => (finitePolicyPMF Q ω i x n).toMeasure
    {w | r ≤ listCenteredMax (signedCoordinate f) ((H:ℝ)*θ) w}
  have hF : Measurable F := curvePolicy_failure_measurable e f b B hH E hδ hα dummy i x n
  have hM : Measurable M := curvePolicy_fixed_event_measurable e f b B hH E hδ hα dummy i x n _
  have hlow := low_mass_probability (environmentLaw ν) (fun ω => F ω+M ω)
    (fun ω => quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ (r+B+D) (n*H)))
    (hF.add hM).aemeasurable ((α*δ)^n/2) (by
      intro ω hcost
      have hp := policy_good_mass Q ω i x n
        (fun y => δ ≤ curveIncrement (realPosition (step e)) f y b B H ω Set.univ)
        (listCenteredMax (signedCoordinate f) ((H:ℝ)*θ)) r hcost
      have ht := curvePolicy_tube_mass e f b hB hD hH θ r hb E hδ hα hδ1 hα1 dummy ω i x n
      have hs := (mul_le_mul_right hp ((α*δ)^n)).trans ht
      simpa only [div_eq_mul_inv,one_mul] using hs)
  apply hlow.trans
  apply mul_le_mul_right
  rw [lintegral_add_left hF]
  apply add_le_add (curvePolicy_actual_failure ν e f b B hH E hδ hα dummy hd i n x hx)
  have hMt : (∫⁻ ω, M ω ∂environmentLaw ν) ≠ ⊤ := by
    have hbnd : (∫⁻ ω, M ω ∂environmentLaw ν) ≤ 1 := by
      calc
        _ ≤ ∫⁻ ω, (1:ℝ≥0∞) ∂environmentLaw ν := lintegral_mono (fun ω => prob_le_one)
        _ = 1 := by simp
    exact ne_of_lt (hbnd.trans_lt ENNReal.one_lt_top)
  rw [← ENNReal.ofReal_toReal hMt]
  apply ENNReal.ofReal_le_ofReal
  simpa only [M,Q,hc] using curvePolicy_maximal_tail ν e f b hB hH E hδ hα dummy hd hdb i x hx n hr

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubeHeightMono
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma tubePrefix_eq_curvePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (θ z : ℝ) (H : ℕ) :
    TubePrefix ℓ f x θ z H = CurvePrefix ℓ f x (fun j => (j:ℝ)*θ) z H := rfl

lemma tubePrefix_mono_height_ae {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H K : ℕ} (hH : 0 < H) (hHK : H ≤ K) (ω : Environment d) :
    TubePrefix (realPosition (step e)) f x θ z K ≤ᵐ[quenchedKernel (ω,x)]
      TubePrefix (realPosition (step e)) f x θ z H := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hX
  rw [tubePrefix_eq_curvePrefix] at hX ⊢
  have hX := (curvePrefix_iff e f x _ z (hH.trans_le hHK) X h0 hnn).mp hX
  apply (curvePrefix_iff e f x _ z hH X h0 hnn).mpr
  refine ⟨?_,fun j hj => hX.2 j (hj.trans hHK)⟩
  have hh := hX.1
  rw [←cross_eq_hit] at hh ⊢
  exact cross_antitone _ x (by exact_mod_cast hHK) hh

lemma quenchedTube_mono_height {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H K : ℕ} (hH : 0 < H) (hHK : H ≤ K) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z K) ≤
      quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) :=
  measure_mono_ae (tubePrefix_mono_height_ae e f x θ z hH hHK ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma curvePolicy_real_tube_probability_oai {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    {H : ℕ} (hH : 0 < H) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*b H/H| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (hdb : signedCoordinate f dummy=b H)
    (n : ℕ) {K : ℕ} (hK : 0 < K) (hKn : K ≤ n*H) :
    let μ := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
    let θ := (∫ u, signedCoordinate f u ∂μ.toMeasure)/(H:ℝ)
    (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 θ (r+2*B+D) K) < (α*δ)^n/2} ≤
      2*((n:ℝ)*(environmentLaw ν).real {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} +
        (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure))/r^2) := by
  dsimp only
  let μ := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
  let m := ∫ u, signedCoordinate f u ∂μ.toMeasure
  have hm : |m-b H| ≤ B := curvePolicy_mean_bound ν e f b hB hH E hδ hα dummy hdb
  have hθ : (H:ℝ)*(m/(H:ℝ))=m := by field_simp
  have hh := curvePolicy_tube_probability ν e f b hB (add_nonneg hD hB) hH (m/H) hr
    (median_line_mean_bound b hH hB hm hb) E hδ hα hδ1 hα1 dummy hd hdb 0 n 0
    (by simp [signedHeight]) hθ
  have hl : environmentLaw ν {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 (m/H) (r+2*B+D) K) < (α*δ)^n/2} ≤
      environmentLaw ν {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 (m/H) (r+B+(D+B)) (n*H)) < (α*δ)^n/2} := by
    apply measure_mono
    intro ω hω
    have he : r+B+(D+B)=r+2*B+D := by ring
    rw [he]
    exact (quenchedTube_mono_height e f 0 (m/H) _ hK hKn ω).trans_lt hω
  have hV : 0 ≤ 4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure)/r^2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  have hrhs : 2*((n:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ}+
      ENNReal.ofReal (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure)/r^2)) ≠ ⊤ := by
    finiteness
  have hh := ENNReal.toReal_mono hrhs (hl.trans hh)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hV] at hh
  exact hh

end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.curvePolicy_real_tube_probability_oai := @OAI.DirectionalTransience.curvePolicy_real_tube_probability_oai
