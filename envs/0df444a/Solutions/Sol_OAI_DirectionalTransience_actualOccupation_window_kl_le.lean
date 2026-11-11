-- Prove2me | solution 1 for OAI.DirectionalTransience.actualOccupation_window_kl_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:33.5166+00:00
-- url     : https://prove2.me/submissions/63ca8bf0-a74a-4454-a3a6-5e1369ced51a

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StoppedSplice
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.wordPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stoppedRowGraft_measurable {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    Measurable (fun p : Environment d×Environment d => stoppedRowGraft S τ p.1 p.2) := by
  have hm : Measurable (fun p : (Environment d×Environment d)×ℕ =>
      rowGraft (S p.2) p.1.1 p.1.2) :=
    measurable_from_prod_countable_left (fun n => rowGraft_measurable (S n))
  exact hm.comp (measurable_id.prodMk (hτ.comp measurable_fst))

theorem stoppedRowGraft_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ η, ∫⁻ ξ, f (stoppedRowGraft S τ η ξ) ∂environmentLaw ν ∂environmentLaw ν)=
      ∫⁻ ω, f ω ∂environmentLaw ν := by
  let G (n : ℕ) (η ξ : Environment d) := {ω | τ ω=n}.indicator
    (fun ω => f (rowGraft (S n) ω ξ)) η
  have hG (n : ℕ) : Measurable (Function.uncurry (G n)) := by
    change Measurable ((Prod.fst ⁻¹' {ω | τ ω=n}).indicator
      (fun p : Environment d×Environment d => f (rowGraft (S n) p.1 p.2)))
    exact (hf.comp (rowGraft_measurable (S n))).indicator
      (((rowSigma_le _) _ (hτ n)).preimage measurable_fst)
  have he (η ξ : Environment d) : f (stoppedRowGraft S τ η ξ)=∑' n, G n η ξ := by
    rw [tsum_eq_single (τ η)]
    · simp [G,stoppedRowGraft]
    · intro n hn
      simp [G,Ne.symm hn]
  simp_rw [he]
  have hin (η : Environment d) :
      (∫⁻ ξ, ∑' n, G n η ξ ∂environmentLaw ν)=
        ∑' n, ∫⁻ ξ, G n η ξ ∂environmentLaw ν :=
    lintegral_tsum (fun n => ((hG n).comp (measurable_const.prodMk measurable_id)).aemeasurable)
  simp_rw [hin]
  rw [lintegral_tsum (fun n => (hG n).lintegral_prod_right.aemeasurable)]
  simp_rw [show ∀ n, (∫⁻ η, ∫⁻ ξ, G n η ξ ∂environmentLaw ν ∂environmentLaw ν)=
      ∫⁻ ω, {ω | τ ω=n}.indicator f ω ∂environmentLaw ν from
    fun n => rowGraft_event_lintegral ν (S n) _ (hτ n) f hf]
  rw [←lintegral_tsum (fun n => (hf.indicator ((rowSigma_le _) _ (hτ n))).aemeasurable)]
  apply lintegral_congr
  intro ω
  rw [tsum_eq_single (τ ω)]
  · simp
  · intro n hn
    simp [Ne.symm hn]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma rowSigma_eq_comap {d : ℕ} (S : Set (Lattice d)) :
    rowSigma S=MeasurableSpace.comap (fun ω : Environment d => S.domRestrict ω) inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hr : @Measurable (Environment d) (S → Row d)
        (MeasurableSpace.comap (fun ω : Environment d => S.domRestrict ω) inferInstance) inferInstance
        (fun ω => S.domRestrict ω) := Measurable.of_comap_le le_rfl
    exact ((measurable_pi_apply (⟨x,hx⟩ : S)).comp hr).comap_le
  · apply Measurable.comap_le
    exact @Measurable.of_eval (Environment d) S (fun _ => Row d) (rowSigma S)
      (fun _ => inferInstance) (fun ω => S.domRestrict ω) (fun x => measurable_row_on x.property)

lemma rowSigma_event_congr {d : ℕ} (S : Set (Lattice d)) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma S] A) {η ξ : Environment d}
    (hrows : ∀ x∈S, η x=ξ x) : η∈A ↔ ξ∈A := by
  rw [rowSigma_eq_comap] at hA
  obtain ⟨B,_,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have he : S.domRestrict η=S.domRestrict ξ := funext fun x => hrows x.val x.property
  change S.domRestrict η∈B ↔ S.domRestrict ξ∈B
  rw [he]

lemma rowGraft_rows {d : ℕ} (S : Set (Lattice d)) (η ξ : Environment d) :
    ∀ x∈S, rowGraft S η ξ x=η x := by intro x hx; simp [rowGraft,hx]

lemma stoppedRowGraft_stop {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n}) (η ξ : Environment d) :
    τ (stoppedRowGraft S τ η ξ)=τ η := by
  exact (rowSigma_event_congr (S (τ η)) _ (hτ (τ η))
    (rowGraft_rows (S (τ η)) η ξ)).mpr rfl

lemma stoppedRowGraft_event {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (A : Set (Environment d)) (hA : StoppedRowsEvent S τ A) (η ξ : Environment d) :
    stoppedRowGraft S τ η ξ∈A ↔ η∈A := by
  have hh := rowSigma_event_congr (S (τ η)) _ (hA (τ η))
    (rowGraft_rows (S (τ η)) η ξ)
  change (stoppedRowGraft S τ η ξ∈A ∧ τ (stoppedRowGraft S τ η ξ)=τ η) ↔
    (η∈A ∧ τ η=τ η) at hh
  simpa only [stoppedRowGraft_stop S τ hτ η ξ,and_true] using hh

lemma stoppedRowGraft_observable {d : ℕ} {D : Type*} [MeasurableSpace D]
    [MeasurableSingletonClass D] (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (U : Environment d → D)
    (hU : ∀ B, MeasurableSet B → StoppedRowsEvent S τ (U ⁻¹' B)) (η ξ : Environment d) :
    U (stoppedRowGraft S τ η ξ)=U η := by
  exact (stoppedRowGraft_event S τ hτ _ (hU {U η} (measurableSet_singleton _)) η ξ).mpr rfl

theorem stoppedRowGraft_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n}) :
    ((environmentLaw ν).prod (environmentLaw ν)).map
      (fun p => stoppedRowGraft S τ p.1 p.2)=environmentLaw ν := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ))]
  have hm : Measurable (fun p : Environment d×Environment d => f (stoppedRowGraft S τ p.1 p.2)) :=
    hf.comp (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ))
  exact (lintegral_prod _ hm.aemeasurable).trans (stoppedRowGraft_lintegral ν S τ hτ f hf)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_StoppedFreshField
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stoppedRowsEvent_mono {d : ℕ} (S : ℕ → Set (Lattice d)) (hS : Monotone S)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (A : Set (Environment d)) (hA : StoppedRowsEvent S τ A) : StoppedRowsEvent S σ A := by
  intro n
  have he : A∩{ω | σ ω=n}=
      (⋃ k : Fin (n+1), A∩{ω | τ ω=k.val})∩{ω | σ ω=n} := by
    ext ω
    constructor
    · rintro ⟨ha,hs⟩
      refine ⟨Set.mem_iUnion.mpr ⟨⟨τ ω,by have hh := hτσ ω; change σ ω = n at hs; omega⟩,ha,rfl⟩,hs⟩
    · rintro ⟨hk,hs⟩
      obtain ⟨k,ha,_⟩ := Set.mem_iUnion.mp hk
      exact ⟨ha,hs⟩
  rw [he]
  have hAk (k : Fin (n+1)) : MeasurableSet[rowSigma (S n)] (A∩{ω | τ ω=k.val}) := by
    have hk : k.val≤n := Nat.le_of_lt_succ k.isLt
    exact (rowSigma_mono (hS hk)) _ (hA k.val)
  exact (MeasurableSet.iUnion hAk).inter (hσ n)

theorem stopped_fresh_joint_map {d : ℕ} {D F : Type*} [MeasurableSpace D] [MeasurableSpace F]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (U : Environment d → D) (hUm : Measurable U)
    (hU : ∀ B, MeasurableSet B → StoppedRowsEvent S τ (U ⁻¹' B))
    (V : ℕ → Environment d → F)
    (hV : ∀ n, @Measurable _ _ (rowSigma (S n)ᶜ) _ (V n))
    (R : Measure F) [IsProbabilityMeasure R]
    (hR : ∀ n, (environmentLaw ν).map (V n)=R) :
    (environmentLaw ν).map (fun ω => (U ω,V (τ ω) ω))=((environmentLaw ν).map U).prod R := by
  have hVm (n : ℕ) : Measurable (V n) := (hV n).mono (rowSigma_le _) le_rfl
  have hVm' : Measurable (fun p : Environment d×ℕ => V p.2 p.1) :=
    measurable_from_prod_countable_left hVm
  have hmap : Measurable (fun ω => (U ω,V (τ ω) ω)) :=
    hUm.prodMk (hVm'.comp (measurable_id.prodMk (measurable_of_stop_events S τ hτ)))
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hmap (hA.prod hB),Measure.prod_prod,Measure.map_apply hUm hA]
  let E (n : ℕ) := (U ⁻¹' A)∩{ω | τ ω=n}
  let K (n : ℕ) := E n∩(V n ⁻¹' B)
  have hE (n : ℕ) : MeasurableSet[rowSigma (S n)] (E n) := hU A hA n
  have hEm (n : ℕ) : MeasurableSet (E n) := (rowSigma_le _) _ (hE n)
  have hK (n : ℕ) : MeasurableSet (K n) := (hEm n).inter (hB.preimage (hVm n))
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro n m hnm
    exact Set.disjoint_left.mpr fun ω hn hm => hnm (hn.2.symm.trans hm.2)
  have hKd : Pairwise (Function.onFun Disjoint K) := by
    intro n m hnm
    exact (hEd hnm).mono Set.inter_subset_left Set.inter_subset_left
  have he : (fun ω => (U ω,V (τ ω) ω)) ⁻¹' (A ×ˢ B)=⋃ n, K n := by
    ext ω
    constructor
    · rintro ⟨ha,hb⟩
      exact Set.mem_iUnion.mpr ⟨τ ω,⟨ha,rfl⟩,hb⟩
    · intro h
      obtain ⟨n,⟨ha,hn⟩,hb⟩ := Set.mem_iUnion.mp h
      refine ⟨ha,?_⟩
      change τ ω=n at hn
      change V n ω∈B at hb
      simpa only [hn] using hb
  rw [he,measure_iUnion hKd hK]
  have hfactor (n : ℕ) : environmentLaw ν (K n)=environmentLaw ν (E n)*R B := by
    have hind := (Indep_iff _ _ _).mp (environment_indep_rows ν (S:=S n)
      (T:=(S n)ᶜ) disjoint_compl_right) (E n) (V n ⁻¹' B) (hE n) ((hV n) hB)
    rw [←Measure.map_apply (hVm n) hB,hR n] at hind
    exact hind
  simp_rw [hfactor]
  rw [ENNReal.tsum_mul_right,←measure_iUnion hEd hEm]
  have he' : (⋃ n, E n)=U ⁻¹' A := by ext ω; simp [E]
  rw [he']

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TwoStopSplice
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stop_observable {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (B : Set ℕ) : StoppedRowsEvent S τ (τ ⁻¹' B) := by
  intro n
  by_cases hn : n∈B
  · have he : (τ ⁻¹' B)∩{ω | τ ω=n}={ω | τ ω=n} := by
      ext ω; simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq]
      exact ⟨And.right,fun h => ⟨h ▸ hn,h⟩⟩
    rw [he]; exact hτ n
  · have he : (τ ⁻¹' B)∩{ω | τ ω=n}=∅ := by
      ext ω; simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨hb,h⟩; exact hn (h ▸ hb)
    rw [he]; exact @MeasurableSet.empty _ (rowSigma (S n))

lemma upperField_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : Environment d×ℕ => upperField e p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro n
  exact (upperField_measurable_rows e n).mono (rowSigma_le _) le_rfl

lemma belowHeight_mono {d : ℕ} (e : Direction d) :
    Monotone (fun n : ℕ => BelowHeight (realPosition (step e)) n) := by
  intro n m h x hx
  change dot (realPosition x) (realPosition (step e))<(n:ℝ) at hx
  change dot (realPosition x) (realPosition (step e))<(m:ℝ)
  exact lt_of_lt_of_le hx (by exact_mod_cast h)

theorem twoStopSplice_fresh {d : ℕ} {D : Type*} [MeasurableSpace D]
    [MeasurableSingletonClass D] (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (U : Environment d → D) (hUm : Measurable U)
    (hU : ∀ B, MeasurableSet B →
      StoppedRowsEvent (fun n => BelowHeight (realPosition (step e)) n) τ (U ⁻¹' B)) :
    ((environmentLaw ν).prod (environmentLaw ν)).map
      (fun p => (U p.1,upperField e (τ p.1)
        (stoppedRowGraft (fun n => BelowHeight (realPosition (step e)) n) σ p.1 p.2))) =
    ((environmentLaw ν).map U).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  let G : Environment d×Environment d → Environment d := fun p => stoppedRowGraft S σ p.1 p.2
  have hUσ : ∀ B, MeasurableSet B → StoppedRowsEvent S σ (U ⁻¹' B) := by
    intro B hB
    exact stoppedRowsEvent_mono S (belowHeight_mono e) τ σ hτσ hσ _ (hU B hB)
  have hτσobs : ∀ B, MeasurableSet B → StoppedRowsEvent S σ (τ ⁻¹' B) := by
    intro B _
    exact stoppedRowsEvent_mono S (belowHeight_mono e) τ σ hτσ hσ _ (stop_observable S τ hτ B)
  have hUG (p : Environment d×Environment d) : U (G p)=U p.1 :=
    stoppedRowGraft_observable S σ hσ U hUσ p.1 p.2
  have hτG (p : Environment d×Environment d) : τ (G p)=τ p.1 :=
    stoppedRowGraft_observable S σ hσ τ hτσobs p.1 p.2
  have hFm : Measurable (fun ω => (U ω,upperField e (τ ω) ω)) :=
    hUm.prodMk ((upperField_joint_measurable e).comp
      (measurable_id.prodMk (measurable_of_stop_events S τ hτ)))
  have hGm : Measurable G := stoppedRowGraft_measurable S σ (measurable_of_stop_events S σ hσ)
  calc
    _ = ((environmentLaw ν).prod (environmentLaw ν)).map
        ((fun ω => (U ω,upperField e (τ ω) ω)) ∘ G) := by
      congr 1
      funext p
      simp only [Function.comp_apply,hUG,hτG]
      rfl
    _ = (((environmentLaw ν).prod (environmentLaw ν)).map G).map
        (fun ω => (U ω,upperField e (τ ω) ω)) := (Measure.map_map hFm hGm).symm
    _ = (environmentLaw ν).map (fun ω => (U ω,upperField e (τ ω) ω)) := by
      rw [show ((environmentLaw ν).prod (environmentLaw ν)).map G=environmentLaw ν from
        stoppedRowGraft_map ν S σ hσ]
    _ = _ := stopped_fresh_joint_map ν S τ hτ U hUm hU (upperField e)
      (upperField_measurable_rows e) _ (upperField_map e ν)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma stoppedObservation_measurable {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (filler : Environment d) : Measurable (stoppedObservation S τ filler) :=
  (stoppedRowGraft_measurable S τ (measurable_of_stop_events S τ hτ)).comp
    (measurable_id.prodMk measurable_const)

lemma rowGraft_fixed_measurable_rows {d : ℕ} (S : Set (Lattice d))
    (filler : Environment d) :
    @Measurable (Environment d) (Environment d) (rowSigma S) inferInstance
      (fun ω => rowGraft S ω filler) :=
  (rowGraft_measurable_rows S).comp (measurable_id.prodMk measurable_const)

lemma stoppedObservation_observable {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (filler : Environment d) (B : Set (Environment d)) (hB : MeasurableSet B) :
    StoppedRowsEvent S τ (stoppedObservation S τ filler ⁻¹' B) := by
  intro n
  have he : (stoppedObservation S τ filler ⁻¹' B) ∩ {ω | τ ω=n} =
      ((fun ω => rowGraft (S n) ω filler) ⁻¹' B) ∩ {ω | τ ω=n} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨hb, hn⟩ <;> refine ⟨?_, hn⟩
    · simpa only [stoppedObservation, stoppedRowGraft, hn] using hb
    · simpa only [stoppedObservation, stoppedRowGraft, hn] using hb
  rw [he]
  exact (hB.preimage (rowGraft_fixed_measurable_rows (S n) filler)).inter (hτ n)

lemma stoppedObservation_nested {d : ℕ} (S : ℕ → Set (Lattice d)) (hS : Monotone S)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (filler η ξ : Environment d) :
    stoppedObservation S τ filler (stoppedRowGraft S σ η ξ) =
      stoppedObservation S τ filler η := by
  apply stoppedRowGraft_observable S σ hσ
  intro B hB
  exact stoppedRowsEvent_mono S hS τ σ hτσ hσ _
    (stoppedObservation_observable S τ hτ filler B hB)

lemma stoppedObservation_nested_stop {d : ℕ} (S : ℕ → Set (Lattice d)) (hS : Monotone S)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n})
    (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (filler η : Environment d) : τ (stoppedObservation S σ filler η)=τ η := by
  apply stoppedRowGraft_observable S σ hσ
  intro B _
  exact stoppedRowsEvent_mono S hS τ σ hτσ hσ _ (stop_observable S τ hτ B)

lemma stoppedObservation_regraft {d : ℕ} (S : ℕ → Set (Lattice d))
    (σ : Environment d → ℕ) (hσ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | σ ω=n})
    (filler η ξ : Environment d) :
    stoppedRowGraft S σ (stoppedObservation S σ filler η) ξ = stoppedRowGraft S σ η ξ := by
  have ht : σ (stoppedObservation S σ filler η)=σ η :=
    stoppedRowGraft_stop S σ hσ η filler
  change rowGraft (S (σ (stoppedObservation S σ filler η)))
    (stoppedObservation S σ filler η) ξ = rowGraft (S (σ η)) η ξ
  rw [ht]
  funext x
  by_cases hx : x ∈ S (σ η) <;> simp [rowGraft, hx, stoppedObservation, stoppedRowGraft]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_AnchorEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace StoppedWindow
variable {A B F : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace F]

lemma parallel_lower_fst (μ : Measure (A × F)) [IsFiniteMeasure μ]
    (K : Kernel A B) [IsMarkovKernel K] :
    ((K ∥ₖ Kernel.id) ∘ₘ μ).fst = K ∘ₘ μ.fst := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.bind_apply (measurable_fst hs) (Kernel.aemeasurable _),
    Measure.bind_apply hs K.aemeasurable, Measure.fst, lintegral_map (K.measurable_coe hs) measurable_fst]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply]
  rw [← Measure.map_apply measurable_fst hs, Measure.map_fst_prod, measure_univ, one_smul]

theorem parallel_lower_kl_le (μ : Measure (A × F)) [IsFiniteMeasure μ]
    (π : Measure F) [IsProbabilityMeasure π]
    (K : Kernel A B) [IsMarkovKernel K] :
    let out := (K ∥ₖ Kernel.id) ∘ₘ μ
    klDiv out (out.fst.prod π) ≤ klDiv μ (μ.fst.prod π) := by
  have h := klDiv_comp_right_le μ (μ.fst.prod π) (K ∥ₖ Kernel.id)
  rw [← Measure.prod_comp_left, ← parallel_lower_fst μ K] at h
  exact h

end StoppedWindow

lemma currentStoppedProfile_observable {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (B : Set (Measure (HorizontalSpace e))) (hB : MeasurableSet B) :
    StoppedRowsEvent (fun n => BelowHeight (realPosition (step e)) n) τ
      (currentStoppedProfile e τ ⁻¹' B) := by
  intro n
  have he : (currentStoppedProfile e τ ⁻¹' B) ∩ {ω | τ ω=n} =
      (globalHorizontalProfile e n ⁻¹' B) ∩ {ω | τ ω=n} := by
    ext ω
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq]
    constructor <;> rintro ⟨hb,hn⟩ <;> exact ⟨by simpa only [currentStoppedProfile,hn] using hb,hn⟩
  rw [he]
  exact (hB.preimage (globalHorizontalProfile_measurable_below e n)).inter (hτ n)

lemma currentStoppedProfile_observation {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler ω : Environment d) :
    currentStoppedProfile e τ
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) =
      currentStoppedProfile e τ ω := by
  ext s hs
  apply stoppedRowGraft_observable _ τ hτ
    (fun ω => currentStoppedProfile e τ ω s)
  intro B hB
  exact currentStoppedProfile_observable e τ hτ _
    (hB.preimage (Measure.measurable_coe hs))

lemma currentAnchorKernel_observation {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler ω : Environment d) :
    currentAnchorKernel e τ (measurable_of_stop_events _ τ hτ)
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) =
    currentAnchorKernel e τ (measurable_of_stop_events _ τ hτ) ω := by
  change Measure.infinitePi _ = Measure.infinitePi _
  congr 1
  funext a
  exact currentStoppedProfile_observation e τ hτ filler ω

lemma globalEpisodeAnchors_current {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (i : ℤ) :
    ((globalEpisodeAnchors e t ht) ω).map (fun U a => U (i,a)) =
      currentAnchorKernel e (fun ω => t ω i) (ht i) ω := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => by exact (Prod.mk.inj h).2)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyVariational
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience.Entropy

variable {X : Type*} [MeasurableSpace X]

lemma ExpBudget.nonneg (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : 0 ≤ C := by
  have hh := h (fun _ => 0) measurable_const ⟨0,fun _ => by simp⟩
  simpa using hh

lemma ExpBudget.absolutelyContinuous (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  by_contra hμs
  have hp : 0 < μ.real s := ENNReal.toReal_pos hμs (measure_ne_top _ _)
  let t : ℝ := (C+1) / μ.real s
  have ht : 0 < t := div_pos (by linarith [h.nonneg μ ν]) hp
  let F : X → ℝ := s.indicator (fun _ => t)
  have hF : Measurable F := measurable_const.indicator hs
  have hh := h F hF ⟨t,fun x => by
    by_cases hx : x ∈ s
    · simp [F,hx,abs_of_pos ht]
    · simp [F,hx,ht.le]⟩
  have he : (∫ x, Real.exp (F x) ∂ν) = 1 := by
    have heq : (fun x => Real.exp (F x)) =ᵐ[ν] fun _ => (1:ℝ) := by
      filter_upwards [show ∀ᵐ x ∂ν, x ∉ s from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hνs] with x hx
      simp [F,hx]
    simpa using integral_congr_ae heq
  rw [he,show (∫ x, F x ∂μ) = μ.real s * t by
    exact integral_indicator_const t hs] at hh
  dsimp [t] at hh
  rw [mul_div_cancel₀ _ hp.ne'] at hh
  linarith

lemma ExpBudget.finite_kl (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : klDiv μ ν ≠ ∞ := by
  have hac := h.absolutelyContinuous μ ν
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν) = 1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  let F : X → ℝ := fun x => Real.log (max 1 (g x))
  have hF : Measurable F := (measurable_const.max hg).log
  have hF0 (x : X) : 0 ≤ F x := Real.log_nonneg (le_max_left _ _)
  have hFi : Integrable F μ := by
    apply integrable_of_bounded_truncated_integrals μ F hF hF0 (C+1)
    intro n
    have hFn : Measurable (fun x => min (n:ℝ) (F x)) := measurable_const.min hF
    have hBn : ∃ B : ℝ, ∀ x, |min (n:ℝ) (F x)| ≤ B :=
      ⟨n,fun x => by
        rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
        exact min_le_left _ _⟩
    have he := h _ hFn hBn
    have he₂ : (∫ x, Real.exp (min (n:ℝ) (F x)) ∂ν) ≤ 2 := by
      have hp := integral_mono (exp_integrable_of_bounded hFn hBn)
        ((integrable_const 1).add hgi) (fun x => by
          calc Real.exp (min (n:ℝ) (F x)) ≤ Real.exp (F x) :=
              Real.exp_le_exp.mpr (min_le_right _ _)
            _ = max 1 (g x) := Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
            _ ≤ 1+g x := max_le (by linarith [hg0 x]) (by linarith))
      simpa only [Pi.add_apply,integral_add (integrable_const 1) hgi,integral_const,
        probReal_univ,one_smul,hg1,one_add_one_eq_two] using hp
    linarith
  have hpos : Integrable (fun x => g x * F x) ν :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hFi
  have hlog : Integrable (fun x => g x * Real.log (g x)) ν := by
    apply (hpos.add (integrable_const 1)).mono' (hg.mul hg.log).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |g x * Real.log (g x)| ≤ g x * F x + 1
      apply abs_le.mpr
      constructor
      · have hlow : -1 ≤ g x * Real.log (g x) := by
          by_cases hx : g x = 0
          · simp [hx]
          have hl := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log (hg0 x)) (hg0 x)
          rw [mul_neg,mul_inv_cancel₀ hx] at hl
          exact hl
        have hn : 0 ≤ g x * F x := mul_nonneg (hg0 x) (hF0 x)
        linarith
      · by_cases hx : g x = 0
        · simp [hx]
        have hl := mul_le_mul_of_nonneg_left
          (Real.log_le_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) (le_max_right 1 (g x))) (hg0 x)
        change g x * Real.log (g x) ≤ g x * F x at hl
        linarith
  exact klDiv_ne_top hac ((integrable_rnDeriv_mul_log_iff hac).mp hlog)

lemma abs_logClip_le (n : ℕ) (x : ℝ) : |logClip n x| ≤ (n:ℝ) := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩

lemma abs_logClip_le_abs (n : ℕ) (x : ℝ) : |logClip n x| ≤ |x| := by
  unfold logClip
  rcases le_total x (n:ℝ) with hx|hx
  · rw [min_eq_right hx]
    rcases le_total (-(n:ℝ)) x with hn|hn
    · rw [max_eq_right hn]
    · rw [max_eq_left hn,abs_neg,abs_of_nonneg (Nat.cast_nonneg n)]
      exact (by linarith : (n:ℝ) ≤ -x).trans (neg_le_abs _)
  · rw [min_eq_left hx,max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n]),abs_of_nonneg (Nat.cast_nonneg n)]
    exact hx.trans (le_abs_self _)

lemma logClip_eventually (x : ℝ) : ∀ᶠ n : ℕ in atTop, logClip n x = x := by
  obtain ⟨N,hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have h : |x| ≤ (n:ℝ) := hN.trans (Nat.cast_le.mpr hn)
  rw [logClip,min_eq_right ((le_abs_self _).trans h),max_eq_right]
  linarith [neg_le_abs x]

lemma exp_logClip_log_le {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (logClip n (Real.log u)) ≤ 1+u := by
  by_cases h : 0 ≤ Real.log u
  · calc Real.exp (logClip n (Real.log u)) ≤ Real.exp (Real.log u) := by
            apply Real.exp_le_exp.mpr
            exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)
         _ = u := Real.exp_log hu
         _ ≤ _ := by linarith
  · calc Real.exp (logClip n (Real.log u)) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr
            exact max_le (neg_nonpos.mpr (Nat.cast_nonneg n))
              ((min_le_right _ _).trans (le_of_not_ge h))
         _ = 1 := Real.exp_zero
         _ ≤ _ := by linarith

theorem kl_le_of_expBudget (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) :
    klDiv μ ν ≤ ENNReal.ofReal C := by
  have hfinite := h.finite_kl μ ν
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hfinite
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hgp : ∀ᵐ x ∂μ, 0 < g x := by
    filter_upwards [Measure.rnDeriv_pos hac,hac.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx ht
    exact ENNReal.toReal_pos hx.ne' ht.ne
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν) = 1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  let F : ℕ → X → ℝ := fun n x =>
    if g x = 0 then -(n:ℝ) else logClip n (Real.log (g x))
  have hFm (n : ℕ) : Measurable (F n) := by
    exact measurable_const.ite (measurableSet_eq_fun hg measurable_const)
      (measurable_const.max (measurable_const.min hg.log))
  have hFb (n : ℕ) (x : X) : |F n x| ≤ (n:ℝ) := by
    dsimp only [F]
    split_ifs
    · rw [abs_neg,abs_of_nonneg (Nat.cast_nonneg n)]
    · exact abs_logClip_le n _
  have hFdom (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖llr μ ν x‖ := by
    filter_upwards [hgp] with x hx
    simp only [F,ite_eq_right hx.ne',llr,Real.norm_eq_abs]
    exact abs_logClip_le_abs n _
  have hFpt : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (llr μ ν x)) := by
    filter_upwards [hgp] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [logClip_eventually (Real.log (g x))] with n hn
    simpa only [F,ite_eq_right hx.ne',llr] using hn.symm
  have hFlim : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, llr μ ν x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖llr μ ν x‖)
      (fun n => (hFm n).aestronglyMeasurable) hllr.norm hFdom hFpt
  have heDom (n : ℕ) (x : X) : ‖Real.exp (F n x)‖ ≤ 1+g x := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    dsimp only [F]
    split_ifs with hx
    · have he : Real.exp (-(n:ℝ)) ≤ 1 := by
        rw [←Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
      linarith [hg0 x]
    · exact exp_logClip_log_le (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) n
  have hePt (x : X) : Tendsto (fun n => Real.exp (F n x)) atTop (𝓝 (g x)) := by
    by_cases hx : g x = 0
    · simp only [F,hx,ite_eq_left]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    · apply tendsto_const_nhds.congr'
      filter_upwards [logClip_eventually (Real.log (g x))] with n hn
      simp only [F,ite_eq_right hx,hn,Real.exp_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx))]
  have heLim : Tendsto (fun n => ∫ x, Real.exp (F n x) ∂ν) atTop (𝓝 1) := by
    rw [←hg1]
    exact tendsto_integral_of_dominated_convergence (fun x => 1+g x)
      (fun n => (hFm n).exp.aestronglyMeasurable) ((integrable_const 1).add hgi)
      (fun n => ae_of_all _ (heDom n)) (ae_of_all _ hePt)
  have hbound (n : ℕ) := h (F n) (hFm n) ⟨n,hFb n⟩
  have hlimit := (hFlim.sub heLim).add (tendsto_const_nhds (x := (1:ℝ)))
  have hh := le_of_tendsto hlimit (Eventually.of_forall hbound)
  have hh' : (klDiv μ ν).toReal ≤ C := by
    rw [toReal_klDiv_of_measure_eq hac (by simp)]
    linarith
  rw [←ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hh'

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_OccupationEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.Entropy
variable {X I : Type*} [MeasurableSpace X]

lemma restricted_exp_test (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ∞)
    (E : Set X) (hE : MeasurableSet E)
    (F : X → ℝ) (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    (∫ x, F x ∂μ.restrict E) - (∫ x, Real.exp (F x) ∂ν.restrict E) + ν.real E ≤
      (klDiv μ ν).toReal := by
  let G : X → ℝ := E.indicator F
  have hG : Measurable G := hF.indicator hE
  have hGB : ∃ B : ℝ, ∀ x, |G x| ≤ B := by
    obtain ⟨B,hB⟩ := hB
    refine ⟨max B 0,fun x => ?_⟩
    by_cases hx : x ∈ E
    · simpa [G,hx] using (hB x).trans (le_max_left B 0)
    · simp [G,hx]
  have h := entropy_exp_test_le μ ν hkl G (integrable_of_bounded hG hGB)
    (exp_integrable_of_bounded hG hGB)
  have heq : (fun x => Real.exp (G x)) =
      fun x => E.indicator (fun x => Real.exp (F x)) x + Eᶜ.indicator (fun _ => (1:ℝ)) x := by
    funext x
    by_cases hx : x ∈ E <;> simp [G,hx]
  have hei := (exp_integrable_of_bounded (μ:=ν) hF hB).indicator hE
  have hci := (integrable_const (μ:=ν) (1:ℝ)).indicator hE.compl
  rw [heq, integral_add hei hci, integral_indicator hE,
    integral_indicator_const 1 hE.compl, smul_eq_mul, mul_one,
    probReal_compl_eq_one_sub hE] at h
  rw [integral_indicator hE] at h
  linarith

lemma activeSum_integral (s : Finset I) (μ : I → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (E : I → Set X)
    (F : X → ℝ) (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    (∫ x, F x ∂activeSum s μ E) = ∑ i ∈ s, ∫ x, F x ∂(μ i).restrict (E i) := by
  unfold activeSum
  exact integral_finsetSum_measure (fun i _ => integrable_of_bounded hF hB)

lemma activeSum_mass (s : Finset I) (μ : I → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (E : I → Set X) :
    (activeSum s μ E).real Set.univ = ∑ i ∈ s, (μ i).real (E i) := by
  have h := activeSum_integral s μ E (fun _ => (1:ℝ)) measurable_const ⟨1,fun _ => by norm_num⟩
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using h

theorem activeSum_exp_test (s : Finset I) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hkl : ∀ i ∈ s, klDiv (μ i) (ν i) ≠ ∞)
    (E : I → Set X) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (F : X → ℝ) (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    (∫ x, F x ∂activeSum s μ E) - (∫ x, Real.exp (F x) ∂activeSum s ν E) +
      (activeSum s ν E).real Set.univ ≤ ∑ i ∈ s, (klDiv (μ i) (ν i)).toReal := by
  have heB : ∃ B : ℝ, ∀ x, |Real.exp (F x)| ≤ B := by
    obtain ⟨B,hB⟩ := hB
    exact ⟨Real.exp B,fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))⟩
  rw [activeSum_integral s μ E F hF hB,activeSum_integral s ν E _ hF.exp heB,
    activeSum_mass,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi => restricted_exp_test (μ i) (ν i) (hkl i hi)
    (E i) (hE i hi) F hF hB

theorem normalized_activeSum_kl_le [Nonempty X]
    (s : Finset I) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hkl : ∀ i ∈ s, klDiv (μ i) (ν i) ≠ ∞)
    (E : I → Set X) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hequal : ∀ i ∈ s, μ i (E i) = ν i (E i))
    (hpos : 0 < (activeSum s μ E).real Set.univ) :
    let μs : FiniteMeasure X := ⟨activeSum s μ E,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    let νs : FiniteMeasure X := ⟨activeSum s ν E,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    klDiv (μs.normalize : Measure X) (νs.normalize : Measure X) ≤
      ENNReal.ofReal ((∑ i ∈ s, (klDiv (μ i) (ν i)).toReal) /
        (activeSum s μ E).real Set.univ) := by
  let μs : FiniteMeasure X := ⟨activeSum s μ E,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let νs : FiniteMeasure X := ⟨activeSum s ν E,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hm : (activeSum s ν E).real Set.univ = (activeSum s μ E).real Set.univ := by
    rw [activeSum_mass,activeSum_mass]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg ENNReal.toReal (hequal i hi).symm
  have hμne : μs ≠ 0 := by
    intro h
    have hz : (activeSum s μ E).real Set.univ = 0 := by
      change (μs : Measure X).real Set.univ = 0
      rw [h]; simp
    linarith
  have hνne : νs ≠ 0 := by
    intro h
    have hz : (activeSum s ν E).real Set.univ = 0 := by
      change (νs : Measure X).real Set.univ = 0
      rw [h]; simp
    linarith
  apply kl_le_of_expBudget
  intro F hF hB
  have h := activeSum_exp_test s μ ν hkl E hE F hF hB
  rw [hm] at h
  rw [← μs.average_eq_integral_normalize hμne,← νs.average_eq_integral_normalize hνne,
    average,average,integral_smul_measure,integral_smul_measure]
  change ((activeSum s μ E) Set.univ)⁻¹.toReal * _ -
    ((activeSum s ν E) Set.univ)⁻¹.toReal * _ + 1 ≤ _
  rw [ENNReal.toReal_inv,ENNReal.toReal_inv]
  change ((activeSum s μ E).real Set.univ)⁻¹ * _ -
    ((activeSum s ν E).real Set.univ)⁻¹ * _ + 1 ≤ _
  rw [hm]
  apply (le_div_iff₀ hpos).mpr
  field_simp
  exact h

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OwnMarginalOccupation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.Entropy
variable {Z F I : Type*} [MeasurableSpace Z] [MeasurableSpace F]

lemma fst_restrict_preimage (μ : Measure (Z × F)) (A : Set Z) (hA : MeasurableSet A) :
    (μ.restrict (Prod.fst ⁻¹' A)).fst = μ.fst.restrict A :=
  (Measure.restrict_map measurable_fst hA).symm

lemma fresh_restrict (ζ : Measure Z) [SFinite ζ] (π : Measure F) [SFinite π] (A : Set Z) :
    (ζ.prod π).restrict (Prod.fst ⁻¹' A) = (ζ.restrict A).prod π := by
  have he : (Prod.fst ⁻¹' A : Set (Z × F)) = A ×ˢ Set.univ := by ext p; simp
  rw [he,← Measure.prod_restrict,Measure.restrict_univ]

lemma fresh_activeSum (s : Finset I) (μ : I → Measure (Z × F))
    [∀ i, IsFiniteMeasure (μ i)] (π : Measure F) [IsProbabilityMeasure π]
    (A : I → Set Z) (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    activeSum s (fun i => (μ i).fst.prod π) (fun i => Prod.fst ⁻¹' A i) =
      (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).fst.prod π := by
  induction s using Finset.induction_on with
  | empty => simp [activeSum,Measure.fst]
  | @insert a s ha ih =>
    have hAa := hA a (Finset.mem_insert_self a s)
    have hAs : ∀ i ∈ s, MeasurableSet (A i) := fun i hi => hA i (Finset.mem_insert_of_mem hi)
    simp only [activeSum,Finset.sum_insert ha] at ih ⊢
    rw [Measure.fst_add,Measure.add_prod,fst_restrict_preimage _ _ hAa,fresh_restrict]
    rw [ih hAs]

lemma fresh_activeMass (μ : Measure (Z × F)) (π : Measure F) [IsProbabilityMeasure π]
    (A : Set Z) (hA : MeasurableSet A) :
    μ (Prod.fst ⁻¹' A) = (μ.fst.prod π) (Prod.fst ⁻¹' A) := by
  rw [← Measure.fst_apply hA, ← Measure.fst_apply hA,Measure.fst_prod]

lemma normalize_fst_prod [Nonempty (Z × F)]
    (μ : FiniteMeasure (Z × F)) (π : Measure F) [IsProbabilityMeasure π]
    (hμ : μ ≠ 0) :
    let ν : FiniteMeasure (Z × F) := ⟨(μ : Measure (Z × F)).fst.prod π,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    (ν.normalize : Measure (Z × F)) = (μ.normalize : Measure (Z × F)).fst.prod π := by
  let ν : FiniteMeasure (Z × F) := ⟨(μ : Measure (Z × F)).fst.prod π,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  change (ν.normalize : Measure (Z × F)) = (μ.normalize : Measure (Z × F)).fst.prod π
  have hm : ν.mass = μ.mass := by
    change ((μ : Measure (Z × F)).fst.prod π Set.univ).toNNReal = _
    rw [← Set.univ_prod_univ,Measure.prod_prod,measure_univ (μ:=π),mul_one,Measure.fst_univ]
    rfl
  have hν : ν ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff,hm]
    exact μ.mass_nonzero_iff.mpr hμ
  rw [ν.toMeasure_normalize_eq_of_nonzero hν,μ.toMeasure_normalize_eq_of_nonzero hμ,hm]
  change μ.mass⁻¹ • ((μ : Measure (Z × F)).fst.prod π) =
    ((μ.mass⁻¹ • (μ : Measure (Z × F))).map Prod.fst).prod π
  rw [Measure.map_smul,Measure.prod_smul_left]
  rfl

theorem own_normalized_activeSum_kl_le [Nonempty (Z × F)]
    (s : Finset I) (μ : I → Measure (Z × F)) [∀ i, IsProbabilityMeasure (μ i)]
    (π : Measure F) [IsProbabilityMeasure π]
    (A : I → Set Z) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hkl : ∀ i ∈ s, klDiv (μ i) ((μ i).fst.prod π) ≠ ∞)
    (hpos : 0 < (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).real Set.univ) :
    let μs : FiniteMeasure (Z × F) := ⟨activeSum s μ (fun i => Prod.fst ⁻¹' A i),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    klDiv (μs.normalize : Measure (Z × F)) ((μs.normalize : Measure (Z × F)).fst.prod π) ≤
      ENNReal.ofReal ((∑ i ∈ s, (klDiv (μ i) ((μ i).fst.prod π)).toReal) /
        (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).real Set.univ) := by
  let μs : FiniteMeasure (Z × F) := ⟨activeSum s μ (fun i => Prod.fst ⁻¹' A i),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hμ : μs ≠ 0 := by
    intro h
    have hz : (activeSum s μ (fun i => Prod.fst ⁻¹' A i)).real Set.univ = 0 := by
      change (μs : Measure (Z × F)).real Set.univ = 0
      rw [h]; simp
    linarith
  have h := normalized_activeSum_kl_le s μ (fun i => (μ i).fst.prod π) hkl
    (fun i => Prod.fst ⁻¹' A i) (fun i hi => (hA i hi).preimage measurable_fst)
    (fun i hi => fresh_activeMass (μ i) π (A i) (hA i hi)) hpos
  let νs : FiniteMeasure (Z × F) := ⟨activeSum s (fun i => (μ i).fst.prod π)
    (fun i => Prod.fst ⁻¹' A i),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let νs' : FiniteMeasure (Z × F) := ⟨(μs : Measure (Z × F)).fst.prod π,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have heq : νs = νs' := by
    apply Subtype.ext
    exact fresh_activeSum s μ π A hA
  change klDiv (μs.normalize : Measure (Z × F)) (νs.normalize : Measure (Z × F)) ≤ _ at h
  rw [heq] at h
  have hnorm : (νs'.normalize : Measure (Z × F)) =
      (μs.normalize : Measure (Z × F)).fst.prod π := normalize_fst_prod μs π hμ
  rw [hnorm] at h
  exact h

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_WindowProjectionEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience.StoppedWindow
variable {Z F D V : Type*} [MeasurableSpace Z] [MeasurableSpace F]
  [MeasurableSpace D] [MeasurableSpace V]

lemma product_map_reference (ζ : Measure Z) [IsFiniteMeasure ζ]
    (π : Measure F) [IsProbabilityMeasure π]
    (data : Z → D) (hd : Measurable data)
    (field : Z → F → V) (hf : Measurable (fun p : Z × F => field p.1 p.2))
    (R : Kernel D V) [IsMarkovKernel R]
    (hR : ∀ z, π.map (field z) = R (data z)) :
    (ζ.prod π).map (fun p => (data p.1,field p.1 p.2)) = (ζ.map data).compProd R := by
  have hout : Measurable (fun p : Z × F => (data p.1,field p.1 p.2)) :=
    (hd.comp measurable_fst).prodMk hf
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hout (hA.prod hB),
    Measure.prod_apply ((hA.prod hB).preimage hout),
    Measure.compProd_apply_prod hA hB, ← lintegral_indicator hA,
    lintegral_map (by exact (R.measurable_coe hB).indicator hA) hd]
  apply lintegral_congr
  intro z
  by_cases hz : data z ∈ A
  · rw [Set.indicator_of_mem hz]
    have he : Prod.mk z ⁻¹' ((fun p : Z × F => (data p.1,field p.1 p.2)) ⁻¹' (A ×ˢ B)) =
        field z ⁻¹' B := by ext v; simp [hz]
    have hfz : Measurable (field z) := hf.comp measurable_prodMk_left
    rw [he, ← Measure.map_apply hfz hB,hR z]
  · have he : Prod.mk z ⁻¹' ((fun p : Z × F => (data p.1,field p.1 p.2)) ⁻¹' (A ×ˢ B)) = ∅ := by
      ext v; simp [hz]
    simp [he,hz]

lemma map_data_field_fst (μ : Measure (Z × F))
    (data : Z → D) (hd : Measurable data)
    (field : Z → F → V) (hf : Measurable (fun p : Z × F => field p.1 p.2)) :
    (μ.map (fun p => (data p.1,field p.1 p.2))).fst = μ.fst.map data := by
  calc
    _ = μ.map (fun p : Z × F => data p.1) :=
      Measure.fst_map_prodMk hf
    _ = _ := (Measure.map_map hd measurable_fst).symm

theorem own_marginal_projection (μ : Measure (Z × F)) [IsFiniteMeasure μ]
    (π : Measure F) [IsProbabilityMeasure π]
    (data : Z → D) (hd : Measurable data)
    (field : Z → F → V) (hf : Measurable (fun p : Z × F => field p.1 p.2))
    (R : Kernel D V) [IsMarkovKernel R]
    (hR : ∀ z, π.map (field z) = R (data z)) :
    let out := μ.map (fun p => (data p.1,field p.1 p.2))
    klDiv out (out.fst.compProd R) ≤ klDiv μ (μ.fst.prod π) := by
  have hout : Measurable (fun p : Z × F => (data p.1,field p.1 p.2)) :=
    (hd.comp measurable_fst).prodMk hf
  have h := klDiv_map_le μ (μ.fst.prod π) hout
  rw [product_map_reference μ.fst π data hd field hf R hR] at h
  dsimp only
  rw [map_data_field_fst μ data hd field hf]
  exact h

end DirectionalTransience.StoppedWindow

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_StoppedWindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma stoppedWindowOutput_measurable {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) : Measurable (stoppedWindowOutput e τ σ filler) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  exact ((stoppedObservation_measurable S τ hτ filler).comp measurable_fst).prodMk
    ((upperField_joint_measurable e).comp
      ((stoppedRowGraft_measurable S σ (measurable_of_stop_events S σ hσ)).prodMk
        ((measurable_of_stop_events S τ hτ).comp measurable_fst)))

lemma stoppedWindowOutput_factor {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    stoppedWindowOutput e τ σ filler ∘
      Prod.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler) id =
        stoppedWindowOutput e τ σ filler := by
  funext p
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  change (stoppedObservation S τ filler (stoppedRowGraft S σ p.1 filler),
    upperField e (τ (stoppedObservation S σ filler p.1))
      (stoppedRowGraft S σ (stoppedObservation S σ filler p.1) p.2)) = _
  rw [stoppedObservation_nested S (belowHeight_mono e) τ σ hτσ hτ hσ,
    stoppedObservation_nested_stop S (belowHeight_mono e) τ σ hτσ hτ hσ,
    stoppedObservation_regraft S σ hσ]
  rfl

lemma stoppedWindowLaw_upper_observation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    stoppedWindowLaw e ν Q τ σ filler =
      ((Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler)).prod
        (environmentLaw ν)).map (stoppedWindowOutput e τ σ filler) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  have hG := stoppedObservation_measurable S σ hσ filler
  have hp := Measure.map_prod_map Q (environmentLaw ν) hG measurable_id
  simp only [Measure.map_id] at hp
  rw [hp, Measure.map_map (stoppedWindowOutput_measurable e τ σ hτ hσ filler)
    (hG.prodMap measurable_id), stoppedWindowOutput_factor e τ σ hτσ hτ hσ filler]
  rfl

lemma stoppedWindowLaw_fst {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    (stoppedWindowLaw e ν Q τ σ filler).fst =
      Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler) := by
  let G := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler
  have hG : Measurable G := stoppedObservation_measurable _ τ hτ filler
  have hF : Measurable (fun p : Environment d × Environment d =>
      upperField e (τ p.1) (stoppedRowGraft
        (fun n => BelowHeight (realPosition (step e)) n) σ p.1 p.2)) :=
    measurable_snd.comp (stoppedWindowOutput_measurable e τ σ hτ hσ filler)
  change ((Q.prod (environmentLaw ν)).map (fun p => ((G ∘ Prod.fst) p, _))).fst = _
  rw [Measure.fst_map_prodMk hF]
  rw [← Measure.map_map hG measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

lemma stoppedWindowLaw_reference {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    stoppedWindowLaw e ν (environmentLaw ν) τ σ filler =
      ((environmentLaw ν).map
        (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler)).prod
          (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) := by
  exact twoStopSplice_fresh e ν τ σ hτσ hτ hσ _
    (stoppedObservation_measurable _ τ hτ filler)
    (stoppedObservation_observable _ τ hτ filler)

theorem actual_stopped_window_entropy_increment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    let Gτ := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler
    let Gσ := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler
    klDiv (Q.map Gτ) ((environmentLaw ν).map Gτ) +
      klDiv (stoppedWindowLaw e ν Q τ σ filler)
        ((Q.map Gτ).prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) ≤
      klDiv (Q.map Gσ) ((environmentLaw ν).map Gσ) := by
  let : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let Gσ := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler
  have h := klDiv_map_le ((Q.map Gσ).prod (environmentLaw ν))
    (((environmentLaw ν).map Gσ).prod (environmentLaw ν))
    (stoppedWindowOutput_measurable e τ σ hτ hσ filler)
  rw [← stoppedWindowLaw_upper_observation e ν Q τ σ hτσ hτ hσ filler,
    ← stoppedWindowLaw_upper_observation e ν (environmentLaw ν) τ σ hτσ hτ hσ filler,
    stoppedWindowLaw_reference e ν τ σ hτσ hτ hσ filler,
    StoppedWindow.same_auxiliary_cost] at h
  have : IsFiniteMeasure (stoppedWindowLaw e ν Q τ σ filler) := by
    unfold stoppedWindowLaw
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply stoppedWindowOutput_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  rw [StoppedWindow.fresh_prod_chain,
    stoppedWindowLaw_fst e ν Q τ σ hτ hσ filler] at h
  exact h

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LocalStoppedSplice
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma prod_dependent_map_const {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [IsFiniteMeasure μ] (ν : Measure B) [IsFiniteMeasure ν]
    (ρ : Measure C) [IsFiniteMeasure ρ] (f : A → B → C)
    (hf : Measurable (fun p : A × B => f p.1 p.2))
    (h : ∀ a, ν.map (f a) = ρ) :
    (μ.prod ν).map (fun p => (p.1, f p.1 p.2)) = μ.prod ρ := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (measurable_fst.prodMk hf) (hs.prod ht),
    Measure.prod_apply ((hs.prod ht).preimage (measurable_fst.prodMk hf)),
    Measure.prod_prod]
  have inner (a : A) : ν (Prod.mk a ⁻¹' ((fun p : A × B => (p.1,f p.1 p.2)) ⁻¹' (s ×ˢ t))) =
      s.indicator (fun _ => ρ t) a := by
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha]
      have he : Prod.mk a ⁻¹' ((fun p : A × B => (p.1,f p.1 p.2)) ⁻¹' (s ×ˢ t)) =
          f a ⁻¹' t := by ext b; simp [ha]
      have hfa : Measurable (f a) := hf.comp measurable_prodMk_left
      rw [he, ← Measure.map_apply hfa ht, h a]
    · have he : Prod.mk a ⁻¹' ((fun p : A × B => (p.1,f p.1 p.2)) ⁻¹' (s ×ˢ t)) = ∅ := by
        ext b; simp [ha]
      simp [he,ha]
  simp_rw [inner]
  rw [lintegral_indicator hs, lintegral_const]
  simp [mul_comm]

lemma localStoppedField_measurable {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (hτ : Measurable τ) (hσ : Measurable σ) :
    Measurable (localStoppedField e τ σ) := by
  apply Measurable.of_eval
  intro q
  apply Measurable.ite (measurableSet_lt measurable_const ((hσ.comp measurable_fst).sub
    (hτ.comp measurable_fst)))
  · have hx : Measurable (fun p : Environment d × LocalUpperField e =>
        horizontalLift e (τ p.1 + q.1) q.2) :=
      (measurable_of_countable (fun n : ℕ => horizontalLift e (n + q.1) q.2)).comp
        (hτ.comp measurable_fst)
    exact measurable_current_row.comp (measurable_fst.prodMk hx)
  · exact (measurable_pi_apply q).comp measurable_snd

lemma localStoppedField_full_graft {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω) (ω η : Environment d) :
    localStoppedField e τ σ (ω, upperField e (τ ω) η) =
      upperField e (τ ω)
        (stoppedRowGraft (fun n => BelowHeight (realPosition (step e)) n) σ ω η) := by
  funext q
  have hn : horizontalLift e (τ ω + q.1) q.2 ∈
      BelowHeight (realPosition (step e)) (σ ω) ↔ q.1 < σ ω - τ ω := by
    simp only [BelowHeight, Set.mem_ofPred_eq, signedHeight_projection, signedHeight_horizontalLift]
    have hle := hτσ ω
    norm_cast
    omega
  change (if q.1 < σ ω - τ ω then _ else _) =
    (if horizontalLift e (τ ω + q.1) q.2 ∈ BelowHeight (realPosition (step e)) (σ ω) then _ else _)
  simp only [hn, upperField]

theorem localStoppedField_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    (Q.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))).map
      (fun p => (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1,
        localStoppedField e τ σ p)) = stoppedWindowLaw e ν Q τ σ filler := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  have hτm := measurable_of_stop_events S τ hτ
  have hσm := measurable_of_stop_events S σ hσ
  have hf : Measurable (fun p : Environment d × Environment d => upperField e (τ p.1) p.2) :=
    (upperField_joint_measurable e).comp (measurable_snd.prodMk (hτm.comp measurable_fst))
  have hh := prod_dependent_map_const Q (environmentLaw ν)
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))
    (fun ω η => upperField e (τ ω) η) hf (fun ω => upperField_map e ν (τ ω))
  have hF : Measurable (fun p : Environment d × LocalUpperField e =>
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1,
        localStoppedField e τ σ p)) :=
    ((stoppedObservation_measurable S τ hτ filler).comp measurable_fst).prodMk
      (localStoppedField_measurable e τ σ hτm hσm)
  rw [← hh, Measure.map_map hF (measurable_fst.prodMk hf)]
  unfold stoppedWindowLaw
  congr 1
  funext p
  exact Prod.ext rfl (localStoppedField_full_graft e τ σ hτσ p.1 p.2)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceContinuity
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

section Reindex
variable {I J K R : Type*} [MeasurableSpace R]

lemma map_iid_eq_of_same_fibers (ν : Measure R) [IsProbabilityMeasure ν]
    (f : I → J) (g : I → K) (h : ∀ i i', f i = f i' ↔ g i = g i') :
    (Measure.infinitePi (fun _ : J => ν)).map (fun ξ i => ξ (f i)) =
      (Measure.infinitePi (fun _ : K => ν)).map (fun ξ i => ξ (g i)) := by
  classical
  let t : Set.range f → K := fun x => g (Classical.choose x.2)
  have ht (i : I) : t ⟨f i,Set.mem_range_self i⟩ = g i :=
    (h _ _).mp (Classical.choose_spec (Set.mem_range_self i))
  have htinj : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    have hfg := (h (Classical.choose x.2) (Classical.choose y.2)).mpr hxy
    rw [Classical.choose_spec x.2,Classical.choose_spec y.2] at hfg
    exact hfg
  have h1 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : J => ν)
    (f := (Subtype.val : Set.range f → J)) Subtype.val_injective
  have h2 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : K => ν) htinj
  have hm : Measurable (fun ξ : Set.range f → R => fun i => ξ ⟨f i,Set.mem_range_self i⟩) := by
    fun_prop
  have hh := congrArg (fun μ : Measure (Set.range f → R) =>
    μ.map (fun ξ i => ξ ⟨f i,Set.mem_range_self i⟩)) (h1.trans h2.symm)
  rw [Measure.map_map hm (by fun_prop),Measure.map_map hm (by fun_prop)] at hh
  simpa only [Function.comp_def,ht] using hh

end Reindex

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AnchorFrameReference
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience.ReferenceClasses
variable {H : Type*} [AddCommGroup H]

lemma anchorOffsets_fibers (U : ℕ → H) (p q : Site H) :
    inputSite (anchorOffsets U) p = inputSite (anchorOffsets U) q ↔
      (p.2.1,U p.1+p.2.2) = (q.2.1,U q.1+q.2.2) := by
  rcases p with ⟨a,l,z⟩
  rcases q with ⟨b,l',z'⟩
  rw [inputSite_eq_iff]
  change (l=l' ∧ ((U b-U a:H):OnePoint H)=((z-z':H):OnePoint H)) ↔ _
  simp only [OnePoint.coe_eq_coe,Prod.mk.injEq]
  constructor
  · rintro ⟨hl,h⟩
    refine ⟨hl,?_⟩
    calc U a+z = U a+(z-z')+z' := by abel
      _ = U a+(U b-U a)+z' := by rw [h]
      _ = U b+z' := by abel
  · rintro ⟨hl,h⟩
    refine ⟨hl,?_⟩
    calc U b-U a = (U b+z')-(U a+z)+z-z' := by abel
      _ = z-z' := by rw [h]; abel

section Measurable
variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]
  {R : Type*} [MeasurableSpace R]

lemma anchorOffsets_measurable : Measurable (anchorOffsets : (ℕ → H) → Data H) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval
  intro p
  exact (OnePoint.continuous_coe.measurable).comp
    ((measurable_pi_apply p.2).sub (measurable_pi_apply p.1))

omit [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma anchorFields_measurable :
    Measurable (fun p : (ℕ → H) × UpperField H R => anchorFields p.1 p.2) := by
  apply Measurable.of_eval
  intro p
  have hev : Measurable (fun q : UpperField H R × (ℕ × H) => q.1 q.2) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply q
  exact hev.comp (measurable_snd.prodMk (measurable_const.prodMk
    (((measurable_pi_apply p.1).comp measurable_fst).add measurable_const)))

theorem anchorFields_reference (ν : Measure R) [IsProbabilityMeasure ν] (U : ℕ → H) :
    (Measure.infinitePi (fun _ : ℕ × H => ν)).map (anchorFields U) = reference ν (anchorOffsets U) := by
  rw [reference_apply]
  exact map_iid_eq_of_same_fibers ν (fun p : Site H => (p.2.1,U p.1+p.2.2))
    (inputSite (anchorOffsets U)) (fun p q => (anchorOffsets_fibers U p q).symm)

theorem anchorFrame_kl_le {Z P : Type*} [MeasurableSpace Z] [MeasurableSpace P]
    (μ : Measure (Z × UpperField H R)) [IsFiniteMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (U : Z → ℕ → H) (hU : Measurable U)
    (profile : Z → P) (hp : Measurable profile) :
    let out := μ.map (fun p => ((anchorOffsets (U p.1),profile p.1),anchorFields (U p.1) p.2))
    klDiv out (out.fst.compProd ((reference (H:=H) ν).comap Prod.fst measurable_fst)) ≤
      klDiv μ (μ.fst.prod (Measure.infinitePi (fun _ : ℕ × H => ν))) := by
  apply StoppedWindow.own_marginal_projection μ _
    (fun z => (anchorOffsets (U z),profile z)) ((anchorOffsets_measurable.comp hU).prodMk hp)
    (fun z ξ => anchorFields (U z) ξ)
    (anchorFields_measurable.comp ((hU.comp measurable_fst).prodMk measurable_snd))
    ((reference (H:=H) ν).comap Prod.fst measurable_fst)
  intro z
  exact anchorFields_reference ν (U z)

end Measurable
end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_InputMarginal
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma currentInput_measurable {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) :
    Measurable (currentInput e i m) := by
  exact ((measurable_fst.comp measurable_fst).prodMk
    (Measurable.of_eval fun a => (measurable_pi_apply (i,a)).comp
      (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_pi_apply (i,m)).comp measurable_snd)

theorem episodeInputLaw_current {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m : ℕ) :
    (episodeInputLaw e ν Q t ht).map (currentInput e i m) =
      (Q.compProd (currentAnchorKernel e (fun ω => t ω i) (ht i))).prod
        (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) := by
  let f : EpisodeAnchors e → ℕ → HorizontalSpace e := fun U a => U (i,a)
  have hf : Measurable f := Measurable.of_eval fun a => measurable_pi_apply (i,a)
  have hK : (globalEpisodeAnchors e t ht).map f =
      currentAnchorKernel e (fun ω => t ω i) (ht i) := by
    ext ω : 1
    rw [Kernel.map_apply _ hf]
    exact globalEpisodeAnchors_current e t ht ω i
  have hπ : (episodeAuxiliaryLaw e ν).map (fun V => V (i,m)) =
      Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν) := by
    exact Measure.infinitePi_map_eval _ (i,m)
  change ((Q.compProd (globalEpisodeAnchors e t ht)).prod (episodeAuxiliaryLaw e ν)).map
    (Prod.map (Prod.map id f) (fun V => V (i,m))) = _
  rw [← Measure.map_prod_map _ _ (measurable_id.prodMap hf) (measurable_pi_apply (i,m)),
    ← Measure.compProd_map hf,hK,hπ]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeEntropyTelescoping
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
namespace DirectionalTransience.StoppedWindow

theorem sum_window_increments (s : ℕ → ℝ) (N m : ℕ) :
    (∑ i ∈ Finset.range N, (s (i+m)-s i)) =
      ∑ j ∈ Finset.range m, (s (N+j)-s j) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h₁ := Finset.sum_range_add s N m
  have h₂ := Finset.sum_range_add s m N
  simp only [Nat.add_comm m N] at h₂
  have hh : (∑ i ∈ Finset.range N, s (i+m)) = ∑ i ∈ Finset.range N, s (m+i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]
  rw [hh]
  linarith

theorem sum_window_increments_le (s : ℕ → ℝ) (N m : ℕ) (C : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hC : ∀ i, s i ≤ C) :
    (∑ i ∈ Finset.range N, (s (i+m)-s i)) ≤ (m:ℝ)*C := by
  rw [sum_window_increments]
  calc
    (∑ j ∈ Finset.range m, (s (N+j)-s j)) ≤ ∑ _j ∈ Finset.range m, C := by
      apply Finset.sum_le_sum
      intro j _
      linarith [hs j, hC (N+j)]
    _ = _ := by simp

end DirectionalTransience.StoppedWindow

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_StoppedEntropySum
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma layerInformation_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler : Environment d) : layerInformation e ν Q τ filler ≤ klDiv Q (environmentLaw ν) :=
  klDiv_map_le Q (environmentLaw ν) (stoppedObservation_measurable _ τ hτ filler)

lemma ownedWindowEntropy_finite_budget {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    ownedWindowEntropy e ν Q τ σ filler ≠ ∞ ∧
    (ownedWindowEntropy e ν Q τ σ filler).toReal ≤
      (layerInformation e ν Q σ filler).toReal - (layerInformation e ν Q τ filler).toReal := by
  have h : layerInformation e ν Q τ filler + ownedWindowEntropy e ν Q τ σ filler ≤
      layerInformation e ν Q σ filler :=
    actual_stopped_window_entropy_increment e ν Q τ σ hτσ hτ hσ filler
  have hfσ : layerInformation e ν Q σ filler ≠ ∞ :=
    ne_top_of_le_ne_top hfin (layerInformation_le e ν Q σ hσ filler)
  have hf := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hfσ h)
  refine ⟨hf.2, ?_⟩
  have hr := ENNReal.toReal_mono hfσ h
  rw [ENNReal.toReal_add hf.1 hf.2] at hr
  linarith

theorem sum_actual_stopped_window_entropy {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (t : ℕ → Environment d → ℕ)
    (ht : ∀ i n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)]
      {ω | t i ω=n})
    (hmono : ∀ ω, Monotone (fun i => t i ω))
    (filler : Environment d) (N m : ℕ) :
    (∑ i ∈ Finset.range N, (ownedWindowEntropy e ν Q (t i) (t (i+m)) filler).toReal) ≤
      (m:ℝ)*(klDiv Q (environmentLaw ν)).toReal := by
  let s : ℕ → ℝ := fun i => (layerInformation e ν Q (t i) filler).toReal
  calc
    _ ≤ ∑ i ∈ Finset.range N, (s (i+m)-s i) := by
      apply Finset.sum_le_sum
      intro i _
      exact (ownedWindowEntropy_finite_budget e ν Q hfin (t i) (t (i+m))
        (fun ω => hmono ω (Nat.le_add_right i m)) (ht i) (ht (i+m)) filler).2
    _ ≤ _ := StoppedWindow.sum_window_increments_le s N m _
      (fun _ => ENNReal.toReal_nonneg)
      (fun i => ENNReal.toReal_mono hfin (layerInformation_le e ν Q (t i) (ht i) filler))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingRearrangement
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DirectionalTransience.StoppedWindow

variable {X A B V F : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSpace V] [MeasurableSpace F]

theorem sample_lower_map (μ : Measure X) [IsFiniteMeasure μ]
    (π : Measure V) [IsProbabilityMeasure π]
    (g : X → A) (hg : Measurable g)
    (f : X × V → F) (hf : Measurable f)
    (K : Kernel A B) [IsMarkovKernel K] :
    (((μ.compProd (K.comap g hg)).prod π).map
      (fun p : (X × B) × V => ((g p.1.1,p.1.2),f (p.1.1,p.2)))) =
      (((Kernel.id.prod K) ∥ₖ Kernel.id) ∘ₘ
        ((μ.prod π).map (fun p => (g p.1,f p)))) := by
  have hw : Measurable (fun p : (X × B) × V => ((g p.1.1,p.1.2),f (p.1.1,p.2))) :=
    ((hg.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hz : Measurable (fun p : X × V => (g p.1,f p)) := (hg.comp measurable_fst).prodMk hf
  apply Measure.ext_of_lintegral
  intro h hh
  have hhw : Measurable (fun p : (X × B) × V => h ((g p.1.1,p.1.2),f (p.1.1,p.2))) := hh.comp hw
  have hk : Measurable (fun z : A × F => ∫⁻ y, h y ∂((Kernel.id.prod K) ∥ₖ Kernel.id) z) :=
    hh.lintegral_kernel
  have hkm : Measurable (fun p : X × V => ∫⁻ y, h y ∂((Kernel.id.prod K) ∥ₖ Kernel.id) (g p.1,f p)) :=
    hk.comp hz
  rw [lintegral_map hh hw, lintegral_prod _ hhw.aemeasurable,
    Measure.lintegral_compProd hhw.lintegral_prod_right',
    Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    lintegral_map hk hz, lintegral_prod _ hkm.aemeasurable]
  apply lintegral_congr
  intro x
  simp only [Kernel.comap_apply]
  have hrow : Measurable (fun p : B × V => h ((g x,p.1),f (x,p.2))) :=
    hh.comp ((measurable_const.prodMk measurable_fst).prodMk
      (hf.comp (measurable_const.prodMk measurable_snd)))
  rw [← lintegral_prod _ hrow.aemeasurable, lintegral_prod_symm _ hrow.aemeasurable]
  apply lintegral_congr
  intro v
  rw [Kernel.lintegral_parallelComp _ hh]
  simp_rw [Kernel.id_apply]
  have hi (p : A × B) : (∫⁻ z : F, h (p,z) ∂Measure.dirac (f (x,v))) = h (p,f (x,v)) :=
    lintegral_dirac' _ (hh.comp measurable_prodMk_left)
  simp_rw [hi]
  have hs : Measurable (fun p : A × B => h (p,f (x,v))) := hh.comp measurable_prodMk_right
  simpa only [id_eq, Kernel.id] using
    (Kernel.lintegral_deterministic_prod (f:=id) measurable_id K (g x) hs).symm

end DirectionalTransience.StoppedWindow

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_RawWindow
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma sampled_stoppedWindow_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    let G := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler
    let K := currentAnchorKernel e τ (measurable_of_stop_events _ τ hτ)
    (((Q.compProd K).prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))).map
      (fun p => ((G p.1.1,p.1.2),localStoppedField e τ σ (p.1.1,p.2)))) =
      (((Kernel.id.prod K) ∥ₖ Kernel.id) ∘ₘ stoppedWindowLaw e ν Q τ σ filler) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  let G := stoppedObservation S τ filler
  let K := currentAnchorKernel e τ (measurable_of_stop_events S τ hτ)
  have hG := stoppedObservation_measurable S τ hτ filler
  have hK : K.comap G hG = K := by
    ext ω : 1
    exact currentAnchorKernel_observation e τ hτ filler ω
  have h := StoppedWindow.sample_lower_map Q
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) G hG
    (localStoppedField e τ σ)
    (localStoppedField_measurable e τ σ (measurable_of_stop_events S τ hτ)
      (measurable_of_stop_events S σ hσ)) K
  rw [hK, localStoppedField_law e ν Q τ σ hτσ hτ hσ filler] at h
  exact h

lemma rawCurrentWindow_measurable {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    Measurable (fun p : (Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e =>
      ((τ p.1.1,(stoppedObservation (fun n => BelowHeight (realPosition (step e)) n)
        τ filler p.1.1,p.1.2)),localStoppedField e τ σ (p.1.1,p.2))) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  have hw : Measurable (fun p : (Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e => p.1.1) :=
    measurable_fst.comp measurable_fst
  exact ((measurable_of_stop_events S τ hτ).comp hw).prodMk
    (((stoppedObservation_measurable S τ hτ filler).comp hw).prodMk
      (measurable_snd.comp measurable_fst)) |>.prodMk
      ((localStoppedField_measurable e τ σ (measurable_of_stop_events S τ hτ)
        (measurable_of_stop_events S σ hσ)).comp (hw.prodMk measurable_snd))

theorem rawCurrentWindow_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    let μ := rawCurrentWindow e ν Q τ σ (measurable_of_stop_events _ τ hτ) filler
    klDiv μ (μ.fst.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) ≤
      ownedWindowEntropy e ν Q τ σ filler := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  let G := stoppedObservation S τ filler
  let K := currentAnchorKernel e τ (measurable_of_stop_events S τ hτ)
  let π := Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)
  let μ := stoppedWindowLaw e ν Q τ σ filler
  let μ' : Measure ((Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e) :=
    (((Kernel.id.prod K) ∥ₖ (Kernel.id : Kernel (LocalUpperField e) (LocalUpperField e))) ∘ₘ μ)
  have : IsFiniteMeasure μ := by unfold μ stoppedWindowLaw; infer_instance
  have : IsFiniteMeasure μ' := by unfold μ'; infer_instance
  let dat : Environment d × (ℕ → HorizontalSpace e) → RawCurrentData e := fun p => (τ p.1,p)
  have hdat : Measurable dat := ((measurable_of_stop_events S τ hτ).comp measurable_fst).prodMk measurable_id
  have hproj := klDiv_map_le μ' (μ'.fst.prod π) (hdat.prodMap measurable_id)
  have hfst := StoppedWindow.map_data_field_fst μ' dat hdat
    (fun (_ : Environment d × (ℕ → HorizontalSpace e)) (ξ : LocalUpperField e) => ξ) measurable_snd
  change (μ'.map (Prod.map dat id)).fst = μ'.fst.map dat at hfst
  have hout : μ'.map (Prod.map dat id) =
      rawCurrentWindow e ν Q τ σ (measurable_of_stop_events S τ hτ) filler := by
    dsimp only [μ', μ, K]
    rw [← sampled_stoppedWindow_law e ν Q τ σ hτσ hτ hσ filler]
    rw [Measure.map_map (hdat.prodMap measurable_id)]
    · congr 1
      funext p
      have ht : τ (G p.1.1) = τ p.1.1 := stoppedRowGraft_stop S τ hτ p.1.1 filler
      exact Prod.ext (Prod.ext ht rfl) rfl
    · exact (((stoppedObservation_measurable S τ hτ filler).comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)).prodMk
        ((localStoppedField_measurable e τ σ (measurable_of_stop_events S τ hτ)
          (measurable_of_stop_events S σ hσ)).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have href : (μ'.fst.prod π).map (Prod.map dat id) =
      (μ'.map (Prod.map dat id)).fst.prod π := by
    rw [← Measure.map_prod_map _ _ hdat measurable_id, Measure.map_id]
    rw [hfst]
  rw [href, hout] at hproj
  refine hproj.trans ?_
  have h := StoppedWindow.parallel_lower_kl_le μ π (Kernel.id.prod K)
  rw [stoppedWindowLaw_fst e ν Q τ σ hτ hσ filler] at h
  exact h

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WindowProjection
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma rawCurrentProfileCoordinate_measurable {d : ℕ} (e : Direction d)
    (a : ℕ) (z : HorizontalSpace e) :
    Measurable (fun p : RawCurrentData e => globalHorizontalCoordinate e p.1 p.2.1 (p.2.2 a+z)) := by
  have hw : Measurable (fun p : RawCurrentData e => p.2.1) := measurable_fst.comp measurable_snd
  have hn : Measurable (fun p : RawCurrentData e => p.1) := measurable_fst
  have hu : Measurable (fun p : RawCurrentData e => p.2.2 a) :=
    (measurable_pi_apply a).comp (measurable_snd.comp measurable_snd)
  have ha : Measurable (fun p : RawCurrentData e => ((p.2.1,p.1),p.2.2 a+z)) :=
    (hw.prodMk hn).prodMk (hu.add_const z)
  have hm := (globalHorizontalCoordinate_joint_measurable e).comp ha
  simpa only [Function.comp_def] using hm

lemma rawCurrentProfiles_measurable {d : ℕ} (e : Direction d) :
    Measurable (rawCurrentProfiles e) :=
  Measurable.of_eval fun p => rawCurrentProfileCoordinate_measurable e p.1 p.2

lemma rawCurrentProjection_measurable {d : ℕ} (e : Direction d) :
    Measurable (rawCurrentProjection e) := by
  have hU : Measurable (fun p : RawCurrentData e × LocalUpperField e => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  exact ((ReferenceClasses.anchorOffsets_measurable.comp hU).prodMk
    ((rawCurrentProfiles_measurable e).comp measurable_fst)).prodMk
      (ReferenceClasses.anchorFields_measurable.comp (hU.prodMk measurable_snd))

lemma rawCurrentProjection_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (μ : Measure (RawCurrentData e × LocalUpperField e)) [IsFiniteMeasure μ] :
    let out := μ.map (rawCurrentProjection e)
    klDiv out (out.fst.compProd (currentWindowReference e ν)) ≤
      klDiv μ (μ.fst.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) := by
  exact ReferenceClasses.anchorFrame_kl_le μ ν (fun z => z.2.2)
    (measurable_snd.comp measurable_snd) (rawCurrentProfiles e) (rawCurrentProfiles_measurable e)

lemma globalHorizontalCoordinate_stoppedObservation {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler ω : Environment d) (z : HorizontalSpace e) :
    globalHorizontalCoordinate e (τ ω)
        (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) z =
      globalHorizontalCoordinate e (τ ω) ω z := by
  have h := currentStoppedProfile_observation e τ hτ filler ω
  have hn : τ (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) = τ ω :=
    stoppedRowGraft_stop (fun n => BelowHeight (realPosition (step e)) n) τ hτ ω filler
  dsimp only [currentStoppedProfile] at h
  rw [hn] at h
  apply Subtype.ext
  exact congrArg (fun μ : Measure (HorizontalSpace e) => (μ {z}).toReal) h

lemma actualCurrentWindow_raw {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (i : ℤ) (m : ℕ)
    (ht : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)]
      {ω | t ω i=n}) (filler : Environment d) (X : EpisodeInput e) :
    rawCurrentProjection e ((t X.1.1 i,
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n)
        (fun ω => t ω i) filler X.1.1,fun a => X.1.2 (i,a))),
        localStoppedField e (fun ω => t ω i) (fun ω => t ω (i+m)) (X.1.1,X.2 (i,m))) =
      actualCurrentWindow e t i m X := by
  dsimp only [rawCurrentProjection,actualCurrentWindow,rawCurrentProfiles]
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · funext p
    exact globalHorizontalCoordinate_stoppedObservation e (fun ω => t ω i) ht filler X.1.1 _
  · funext p
    dsimp only [ReferenceClasses.anchorFields,localStoppedField,episodeSplicedRow]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_OccupationEntropy2
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma rawCurrentWindow_probability {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (τ σ : Environment d → ℕ) (hτm : Measurable τ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    IsProbabilityMeasure (rawCurrentWindow e ν Q τ σ hτm filler) := by
  unfold rawCurrentWindow
  exact (Measure.isProbabilityMeasure_map_iff
    (rawCurrentWindow_measurable e τ σ hτ hσ filler).aemeasurable).2 inferInstance

theorem rawCurrentOccupation_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (t : ℕ → Environment d → ℕ) (htm : ∀ i, Measurable (t i))
    (ht : ∀ i n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t i ω=n})
    (hmono : ∀ ω, Monotone (fun i => t i ω))
    (filler : Environment d) (N m : ℕ)
    (hpos : 0 < (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) :
    haveI : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
    let μs : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
      ⟨rawCurrentOccupation e ν Q t htm filler N m,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    klDiv (μs.normalize : Measure (RawCurrentData e × LocalUpperField e))
      ((μs.normalize : Measure (RawCurrentData e × LocalUpperField e)).fst.prod
        (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let μ : ℕ → Measure (RawCurrentData e × LocalUpperField e) :=
    fun i => rawCurrentWindow e ν Q (t i) (t (i+m)) (htm i) filler
  let π := Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)
  let A : ℕ → Set (RawCurrentData e) := fun _ => {z | z.1 < N}
  have (i : ℕ) : IsProbabilityMeasure (μ i) :=
    rawCurrentWindow_probability e ν Q (t i) (t (i+m)) (htm i) (ht i) (ht (i+m)) filler
  have hle (i : ℕ) : klDiv (μ i) ((μ i).fst.prod π) ≤
      ownedWindowEntropy e ν Q (t i) (t (i+m)) filler :=
    rawCurrentWindow_kl_le e ν Q (t i) (t (i+m))
      (fun ω => hmono ω (Nat.le_add_right i m)) (ht i) (ht (i+m)) filler
  have hf (i : ℕ) := (ownedWindowEntropy_finite_budget e ν Q hfin (t i) (t (i+m))
    (fun ω => hmono ω (Nat.le_add_right i m)) (ht i) (ht (i+m)) filler).1
  have hkl (i : ℕ) : klDiv (μ i) ((μ i).fst.prod π) ≠ ∞ := ne_top_of_le_ne_top (hf i) (hle i)
  have h := Entropy.own_normalized_activeSum_kl_le (Finset.range N) μ π A
    (fun _ _ => measurableSet_lt measurable_fst measurable_const) (fun i _ => hkl i) hpos
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  apply div_le_div_of_nonneg_right _ hpos.le
  calc
    _ ≤ ∑ i ∈ Finset.range N, (ownedWindowEntropy e ν Q (t i) (t (i+m)) filler).toReal :=
      Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (hf i) (hle i)
    _ ≤ _ := sum_actual_stopped_window_entropy e ν Q hfin t ht hmono filler N m

theorem currentOccupation_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (t : ℕ → Environment d → ℕ) (htm : ∀ i, Measurable (t i))
    (ht : ∀ i n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t i ω=n})
    (hmono : ∀ ω, Monotone (fun i => t i ω))
    (filler : Environment d) (N m : ℕ)
    (hpos : 0 < (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) :
    let μs : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
      ⟨rawCurrentOccupation e ν Q t htm filler N m,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    haveI : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
    let out := (μs.normalize : Measure (RawCurrentData e × LocalUpperField e)).map (rawCurrentProjection e)
    klDiv out (out.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let μs : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
    ⟨rawCurrentOccupation e ν Q t htm filler N m,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  exact (rawCurrentProjection_kl_le e ν (μs.normalize : Measure _)).trans
    (rawCurrentOccupation_kl_le e ν Q hfin t htm ht hmono filler N m hpos)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_RestrictedWindow
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma actualCurrentWindow_restricted_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m N : ℕ)
    (hi : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (him : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω (i+m)=n})
    (filler : Environment d) :
    ((rawCurrentWindow e ν Q (fun ω => t ω i) (fun ω => t ω (i+m)) (ht i) filler).restrict
      {p | p.1.1<N}).map (rawCurrentProjection e) =
      ((episodeInputLaw e ν Q t ht).restrict {X | t X.1.1 i<N}).map
        (actualCurrentWindow e t i m) := by
  unfold rawCurrentWindow
  rw [← episodeInputLaw_current e ν Q t ht i m]
  rw [Measure.map_map (rawCurrentWindow_measurable e _ _ hi him filler)
    (currentInput_measurable e i m)]
  have hf := (rawCurrentWindow_measurable e _ _ hi him filler).comp (currentInput_measurable e i m)
  have hA : MeasurableSet {p : RawCurrentData e × LocalUpperField e | p.1.1<N} :=
    measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const
  rw [Measure.restrict_map hf hA]
  rw [Measure.map_map (rawCurrentProjection_measurable e) hf]
  congr 1
  funext X
  exact actualCurrentWindow_raw e t i m hi filler X

lemma rawCurrentOccupation_projected {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (filler : Environment d) (N m : ℕ) :
    (rawCurrentOccupation e ν Q (fun i ω => t ω i) (fun i => ht i) filler N m).map
      (rawCurrentProjection e) =
      ∑ i ∈ Finset.range N, ((episodeInputLaw e ν Q t ht).restrict {X | t X.1.1 i<N}).map
        (actualCurrentWindow e t i m) := by
  unfold rawCurrentOccupation Entropy.activeSum
  rw [Measure.map_finset_sum (rawCurrentProjection_measurable e).aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.cast_add] using actualCurrentWindow_restricted_law e ν Q t ht i m N
    (hst i) (hst (i+m)) filler

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClosed
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma actual_currentOffsets {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (j : ℤ) :
    ReferenceClasses.Consistent (currentOffsets e j (actualArrayMap e t J X)) := by
  constructor
  · intro a
    simp [currentOffsets,actualArrayMap]
  · intro a b z h
    have he : X.1.2 (j,b)-X.1.2 (j,a)=z := OnePoint.coe_injective h
    change ((X.1.2 (j,a)-X.1.2 (j,b) : HorizontalSpace e):OnePoint (HorizontalSpace e))=((-z : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←he,neg_sub]
  · intro a b c z w h₁ h₂
    have h₁ : X.1.2 (j,b)-X.1.2 (j,a)=z := OnePoint.coe_injective h₁
    have h₂ : X.1.2 (j,c)-X.1.2 (j,b)=w := OnePoint.coe_injective h₂
    change ((X.1.2 (j,c)-X.1.2 (j,a) : HorizontalSpace e):OnePoint (HorizontalSpace e))=((z+w : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←h₁,←h₂]
    congr 1
    abel

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Classical
namespace DirectionalTransience

lemma currentWindowInclude_injective {d : ℕ} (e : Direction d) :
    Function.Injective (currentWindowInclude e) := by
  intro W W' h
  have h1 : W.1.1.1=W'.1.1.1 := congrArg (fun p => p.1.1) h
  have h2 : W.1.2=W'.1.2 := congrArg (fun p => p.1.2) h
  have h3 : W.2=W'.2 := congrArg (fun p => p.2) h
  exact Prod.ext (Prod.ext (Subtype.ext h1) h2) h3

lemma currentArrayWindow_actual {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (j : ℤ) (m : ℕ) (X : EpisodeInput e) :
    currentArrayWindow e j m (actualArrayMap e t J X) =
      currentWindowInclude e (actualCurrentWindow e t j m X) := rfl

lemma currentArrayWindow_shift {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) :
    currentArrayWindow e j m (StationaryCompact.shift Y) = currentArrayWindow e (j+1) m Y := rfl

lemma currentArrayWindow_iterate {d : ℕ} (e : Direction d) (j : ℤ) (m i : ℕ)
    (Y : ActualEpisodeArray e) :
    currentArrayWindow e j m (StationaryCompact.shift^[i] Y) = currentArrayWindow e (j+i) m Y := by
  induction i generalizing Y with
  | zero => simp
  | succ i hi =>
    rw [Function.iterate_succ_apply,hi,currentArrayWindow_shift]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc]

lemma currentWindowInclude_typed {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) (h : ReferenceClasses.Consistent (currentOffsets e j Y)) :
    currentWindowInclude e (typedCurrentArrayWindow e j m Y) = currentArrayWindow e j m Y := by
  simp only [typedCurrentArrayWindow,dite_eq_left h,currentWindowInclude,currentArrayWindow]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_OccupationWindow
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma typedCurrentArrayWindow_iterate_actual {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (j : ℤ) (m i : ℕ) (X : EpisodeInput e) :
    typedCurrentArrayWindow e j m (StationaryCompact.shift^[i] (actualArrayMap e t J X)) =
      actualCurrentWindow e t (j+i) m X := by
  have hc : ReferenceClasses.Consistent
      (currentOffsets e j (StationaryCompact.shift^[i] (actualArrayMap e t J X))) := by
    have h := congrArg (fun W : AmbientCurrentWindow e => W.1.1)
      (currentArrayWindow_iterate e j m i (actualArrayMap e t J X))
    change currentOffsets e j (StationaryCompact.shift^[i] (actualArrayMap e t J X)) =
      currentOffsets e (j+i) (actualArrayMap e t J X) at h
    rw [h]
    exact actual_currentOffsets e t J X (j+i)
  apply currentWindowInclude_injective e
  rw [currentWindowInclude_typed e j m _ hc,currentArrayWindow_iterate,currentArrayWindow_actual]

lemma rawCurrentOccupation_actual {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (filler : Environment d) (N m : ℕ) (M : Environment d → ℕ)
    (hact : ∀ (i : ℕ) ω, t ω i<N ↔ i<M ω) :
    (rawCurrentOccupation e ν Q (fun i ω => t ω i) (fun i => ht i) filler N m).map
      (rawCurrentProjection e) =
      (actualOccupationRaw e ν Q t J ht N M).map (typedCurrentArrayWindow e 0 m) := by
  rw [rawCurrentOccupation_projected e ν Q t ht hst filler N m]
  unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
  rw [Measure.map_finset_sum (typedCurrentArrayWindow_measurable e 0 m).aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  have hA : {X : EpisodeInput e | t X.1.1 i<N}={X | i<M X.1.1} := by
    ext X
    exact hact i X.1.1
  have hm : Measurable (fun X : EpisodeInput e => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  rw [hA,Measure.map_map (typedCurrentArrayWindow_measurable e 0 m) hm]
  congr 1
  funext X
  exact ((typedCurrentArrayWindow_iterate_actual e t J 0 m i X).trans (by simp)).symm

namespace Entropy
lemma normalize_map_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (μ : FiniteMeasure X) (f : X → Y) (hf : Measurable f)
    (hμ : μ≠0) :
    let ν : FiniteMeasure Y := ⟨(μ : Measure X).map f,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    (ν.normalize : Measure Y) = (μ.normalize : Measure X).map f := by
  let ν : FiniteMeasure Y := ⟨(μ : Measure X).map f,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hm : ν.mass=μ.mass := by
    change ((μ : Measure X).map f Set.univ).toNNReal = _
    rw [Measure.map_apply hf MeasurableSet.univ,Set.preimage_univ]
    rfl
  have hν : ν≠0 := by
    rw [← ν.mass_nonzero_iff,hm]
    exact μ.mass_nonzero_iff.mpr hμ
  change (ν.normalize : Measure Y)=_
  rw [ν.toMeasure_normalize_eq_of_nonzero hν,μ.toMeasure_normalize_eq_of_nonzero hμ,hm,
    Measure.map_smul]
  rfl

lemma normalize_maps_equal {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (μ : FiniteMeasure X) (ν : FiniteMeasure Y) (f : X → Z) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) (hμ : μ≠0) (hν : ν≠0)
    (h : (μ : Measure X).map f = (ν : Measure Y).map g) :
    (μ.normalize : Measure X).map f = (ν.normalize : Measure Y).map g := by
  rw [←normalize_map_measure μ f hf hμ,←normalize_map_measure ν g hg hν]
  have he : (⟨(μ : Measure X).map f,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable | exact hg.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : FiniteMeasure Z) =
    ⟨(ν : Measure Y).map g,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable | exact hg.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ := Subtype.ext h
  rw [he]

lemma real_mass_eq_of_maps_equal {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (f : X → Z) (g : Y → Z)
    (hf : Measurable f) (hg : Measurable g) (h : μ.map f=ν.map g) :
    μ.real Set.univ=ν.real Set.univ := by
  have hh := congrArg (fun ρ : Measure Z => ρ.real Set.univ) h
  simpa only [Measure.real,Measure.map_apply hf MeasurableSet.univ,
    Measure.map_apply hg MeasurableSet.univ,Set.preimage_univ] using hh
end Entropy

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_WindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma finiteMeasure_ne_zero_of_real_mass_pos {X : Type*} [MeasurableSpace X]
    (μ : FiniteMeasure X) (h : 0<(μ : Measure X).real Set.univ) : μ≠0 := by
  intro hz
  rw [hz] at h
  simp at h

theorem actualOccupation_window_kl_le_oai {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν)≠∞)
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (hst : ∀ (i : ℤ) (n : ℕ), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (hmono : ∀ ω, Monotone (fun i : ℕ => t ω i))
    (N m : ℕ) (M : Environment d → ℕ)
    (hact : ∀ (i : ℕ) ω, t ω i<N ↔ i<M ω)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    let W := (actualCurrentLaw e m (actualOccupation e ν Q t J ht N M) : Measure (CurrentWindow e))
    klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (actualOccupationRaw e ν Q t J ht N M).real Set.univ) := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  have : Nonempty (ReferenceClasses.Data (HorizontalSpace e)) := ⟨ReferenceClasses.anchorOffsets (fun _ => 0)⟩
  let filler : Environment d := fun _ => Classical.choice ‹Nonempty (Row d)›
  let μ : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
    ⟨rawCurrentOccupation e ν Q (fun i ω => t ω i) (fun i => ht i) filler N m,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have he := rawCurrentOccupation_actual e ν Q t J ht hJ hst filler N m M hact
  have hmass : (μ : Measure (RawCurrentData e × LocalUpperField e)).real Set.univ=
      (ρ : Measure (ActualEpisodeArray e)).real Set.univ :=
    Entropy.real_mass_eq_of_maps_equal _ _ _ _ (rawCurrentProjection_measurable e)
      (typedCurrentArrayWindow_measurable e 0 m) he
  have hμpos : 0<(μ : Measure (RawCurrentData e × LocalUpperField e)).real Set.univ := by rw [hmass]; exact hpos
  have hn := Entropy.normalize_maps_equal μ ρ (rawCurrentProjection e) (typedCurrentArrayWindow e 0 m)
    (rawCurrentProjection_measurable e) (typedCurrentArrayWindow_measurable e 0 m)
    (finiteMeasure_ne_zero_of_real_mass_pos μ hμpos) (finiteMeasure_ne_zero_of_real_mass_pos ρ hpos) he
  have hb := currentOccupation_kl_le e ν Q hfin (fun i ω => t ω i)
    (fun i => ht i) (fun i => hst i) hmono filler N m hμpos
  change klDiv ((μ.normalize : Measure _).map (rawCurrentProjection e))
    (((μ.normalize : Measure _).map (rawCurrentProjection e)).fst.compProd (currentWindowReference e ν)) ≤ _ at hb
  rw [hn] at hb
  change klDiv ((ρ.normalize : Measure _).map (typedCurrentArrayWindow e 0 m))
    (((ρ.normalize : Measure _).map (typedCurrentArrayWindow e 0 m)).fst.compProd (currentWindowReference e ν)) ≤ _
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  exact congrArg (fun x : ℝ => ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal/x)) hmass.symm

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.actualOccupation_window_kl_le_oai := @OAI.DirectionalTransience.actualOccupation_window_kl_le_oai
