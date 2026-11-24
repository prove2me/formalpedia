-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.mass_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:13.250053+00:00
-- url     : https://prove2.me/submissions/869d1f07-65d9-47d9-8666-61b093d3426e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_gram_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_isUnit_tmul
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreRatio
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.CompanionTheory.SW.FibreRatio
theorem _root_.solution (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {μ : Measure (Fin 1 → Fin M → R ⊗[F] E)} {ν : Measure (HermR R σ 1)}
    {m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)} (hfib : IsGramFib R σ J 1 μ ν m)
    {A : Set (Fin 1 → Fin M → R ⊗[F] E)} (hA : MeasurableSet A) {V : Set R} (h0 : (0 : R) ∉ V)
    (hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V})
    (hP : MeasurableSet {S | qS R σ S ∈ V}) :
    μ (A ∩ {X | algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V}) =
      ∫⁻ S in {S | qS R σ S ∈ V}, m S A ∂ν := by
  obtain ⟨hf1, hf2, -⟩ := hfib
  set Q : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    {X | algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V} with hQdef
  set W : Set (Fin 1 → Fin M → R ⊗[F] E) := {X | IsUnit (gramR R σ J X).det} with hW
  have hAQ : MeasurableSet (A ∩ Q) := hA.inter hQ
  have hQW : Q ⊆ W := by
    intro X hX
    have hne : algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ≠ 0 :=
      fun e => h0 (e ▸ hX)
    show IsUnit (gramR R σ J X).det
    rw [Matrix.det_fin_one, gram_entry R h hJ X]
    exact isUnit_tmul R hne
  have key := hf2 ((A ∩ Q).indicator 1) (measurable_one.indicator hAQ)
  rw [lintegral_indicator_one₀ hAQ.nullMeasurableSet, Measure.restrict_apply hAQ,
    Set.inter_eq_left.mpr (Set.inter_subset_right.trans hQW)] at key
  rw [key, ← lintegral_indicator hP]
  refine lintegral_congr fun S => ?_
  rw [lintegral_indicator_one hAQ]
  set G : Set (Fin 1 → Fin M → R ⊗[F] E) := gramR R σ J ⁻¹' {(S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))} ∩ W
    with hG
  have hGc : m S Gᶜ = 0 := hf1 S
  have hGq : ∀ X ∈ G, algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) =
      qS R σ S := by
    intro X hX
    have : gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX.1
    rw [this]
    rfl
  by_cases hS : qS R σ S ∈ V
  · rw [Set.indicator_of_mem (show S ∈ {S | qS R σ S ∈ V} from hS)]
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    calc m S A = m S (A ∩ G) := (measure_inter_conull hGc).symm
      _ ≤ m S (A ∩ Q) := measure_mono fun X hX => ⟨hX.1, by
          show _ ∈ V
          rw [hGq X hX.2]; exact hS⟩
  · rw [Set.indicator_of_notMem (show S ∉ {S | qS R σ S ∈ V} from hS)]
    have hsub : A ∩ Q ⊆ Gᶜ := by
      intro X hX hXG
      have hXQ : algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ V := hX.2
      rw [hGq X hXG] at hXQ
      exact hS hXQ
    exact measure_mono_null hsub hGc
end GlobalTheory.CompanionTheory.SW.FibreRatio
