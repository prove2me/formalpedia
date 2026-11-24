-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.InvariantProduct.exists_const_rect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:15.464803+00:00
-- url     : https://prove2.me/submissions/dae6f266-19ed-4baa-a883-c991671938ee

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.InvariantProduct
namespace GlobalTheory.CompanionTheory.SW.InvariantProduct
theorem _root_.solution {Q Z : Type} [Group Q] [TopologicalSpace Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace Z] [T2Space Z]
    [MeasurableSpace Z] [BorelSpace Z] (η : Measure Q) [η.IsHaarMeasure]
    (ρ : Measure (Q × Z)) [IsLocallyFiniteMeasure ρ]
    (hinv : ∀ q : Q, ρ.map (fun p => (q * p.1, p.2)) = ρ)
    {A C : Set Z} (hA : MeasurableSet A) (hC : IsCompact C) (hAC : A ⊆ C) :
    ∃ c : ℝ≥0, ∀ U : Set Q, MeasurableSet U → ρ (U ×ˢ A) = c * η U := by
  let μ : Measure Q := (ρ.restrict (Set.univ ×ˢ A)).map Prod.fst
  have hμ : ∀ U : Set Q, MeasurableSet U → μ U = ρ (U ×ˢ A) := by
    intro U hU
    rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU)]
    congr 1
    ext ⟨x, z⟩
    simp
  haveI : μ.IsMulLeftInvariant := ⟨fun q => by
    ext U hU
    have hT : Measurable (fun p : Q × Z => (q * p.1, p.2)) :=
      (measurable_fst.const_mul q).prodMk measurable_snd
    rw [Measure.map_apply (measurable_const_mul q) hU, hμ _ (measurable_const_mul q hU), hμ U hU]
    conv_rhs => rw [← hinv q]
    rw [Measure.map_apply hT (hU.prod hA)]
    rfl⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun L hL => by
    rw [hμ L hL.isClosed.measurableSet]
    exact (measure_mono (Set.prod_mono subset_rfl hAC)).trans_lt (hL.prod hC).measure_lt_top⟩
  refine ⟨Measure.haarScalarFactor μ η, fun U hU => ?_⟩
  have h := congrArg (fun ν : Measure Q => ν U) (Measure.isMulLeftInvariant_eq_smul μ η)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  rw [← hμ U hU]
  exact h
end GlobalTheory.CompanionTheory.SW.InvariantProduct
