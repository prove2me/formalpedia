-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.measure_eq_haar_prod_of_left_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:37.024095+00:00
-- url     : https://prove2.me/submissions/2e68b788-af2e-4788-9136-395885c9eb53

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_InvariantProduct_exists_const_rect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution :
    ∀ (Q Z : Type) [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
      [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
      [IsTopologicalGroup Q] [TopologicalSpace Z] [LocallyCompactSpace Z]
      [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
      (η : Measure Q) [η.IsHaarMeasure] (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ],
      (∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ) →
        ∃ m : Measure Z, IsLocallyFiniteMeasure m ∧ ρ = η.prod m := by
  intro Q Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ η _ ρ _ hinv
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : Q)
  have hKpos : η K ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos η ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩)
    (measure_mono interior_subset)).ne'
  have hKfin : η K ≠ ∞ := hKc.measure_lt_top.ne
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  let m : Measure Z := (η K)⁻¹ • (ρ.restrict (K ×ˢ Set.univ)).map Prod.snd
  have hm : ∀ A : Set Z, MeasurableSet A → m A = (η K)⁻¹ * ρ (K ×ˢ A) := by
    intro A hA
    have hset : Prod.snd ⁻¹' A ∩ (K ×ˢ (Set.univ : Set Z)) = K ×ˢ A := by
      ext ⟨x, z⟩
      simp [and_comm]
    simp only [m, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA), hset]
  have hrect : ∀ (U : Set Q) (A C : Set Z), MeasurableSet U → MeasurableSet A → IsCompact C →
      A ⊆ C → ρ (U ×ˢ A) = η U * m A := by
    intro U A C hU hA hC hAC
    obtain ⟨c, hc⟩ := InvariantProduct.exists_const_rect η ρ hinv hA hC hAC
    rw [hc U hU, hm A hA, hc K hKm, ← mul_assoc (η K)⁻¹, mul_comm (η K)⁻¹,
      mul_assoc (c : ℝ≥0∞), ENNReal.inv_mul_cancel hKpos hKfin, mul_one, mul_comm]
  have hmC : ∀ C : Set Z, IsCompact C → m C < ∞ := by
    intro C hC
    rw [hm C hC.isClosed.measurableSet]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hKpos))
      (hKc.prod hC).measure_lt_top
  haveI hmfc : IsFiniteMeasureOnCompacts m := ⟨fun C hC => hmC C hC⟩
  refine ⟨m, inferInstance, ?_⟩
  symm
  let CQ : Set (Set Q) := {U | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L}
  let CZ : Set (Set Z) := {A | MeasurableSet A ∧ ∃ L, IsCompact L ∧ A ⊆ L}
  have genAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X],
      MeasurableSpace.generateFrom {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} =
        ‹MeasurableSpace X› := by
    intro X _ _ _ M _
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_le fun U hU => hU.1
    · intro B hB
      have : B = ⋃ n, B ∩ compactCovering X n := by
        rw [← Set.inter_iUnion, iUnion_compactCovering, Set.inter_univ]
      rw [this]
      exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
        ⟨hB.inter (isCompact_compactCovering X n).isClosed.measurableSet,
          _, isCompact_compactCovering X n, Set.inter_subset_right⟩
  have piAux : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X],
      IsPiSystem {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ U hU V hV _
    obtain ⟨hUm, L, hL, hUL⟩ := hU
    exact ⟨hUm.inter hV.1, L, hL, Set.inter_subset_left.trans hUL⟩
  have spanAux : ∀ (X : Type) [TopologicalSpace X] [SigmaCompactSpace X] [T2Space X]
      [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ],
      μ.FiniteSpanningSetsIn {U : Set X | MeasurableSet U ∧ ∃ L, IsCompact L ∧ U ⊆ L} := by
    intro X _ _ _ _ _ μ _
    exact ⟨compactCovering X,
      fun n => ⟨(isCompact_compactCovering X n).isClosed.measurableSet, _,
        isCompact_compactCovering X n, subset_rfl⟩,
      fun n => (isCompact_compactCovering X n).measure_lt_top,
      iUnion_compactCovering X⟩
  refine Measure.prod_eq_generateFrom (genAux Q) (genAux Z) (piAux Q) (piAux Z)
    (spanAux Q η) (spanAux Z m) ?_
  rintro U ⟨hU, -⟩ A ⟨hA, L, hL, hAL⟩
  exact (hrect U A L hU hA hL hAL)
end GlobalTheory.CompanionTheory.SW
