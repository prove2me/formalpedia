-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.coord_measures_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:30:04.831728+00:00
-- url     : https://prove2.me/submissions/b7bd242d-4ec2-48f1-baae-02e5d7be52cb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_haar_comap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_conj_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_hermCoord_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_hermCoord_isHomeomorph
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → (coordK R b lam).IsAddHaarMeasure ∧ (∀ n M : ℕ, (coordW R b lam n M).IsAddHaarMeasure) ∧ ∀ n : ℕ, (coordHerm R σ b lam n).IsAddHaarMeasure := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  have hK : (coordK R b lam).IsAddHaarMeasure := by
    refine HaarCoord.haar_comap _ ?_ (t7 d b) _
    intro x y
    funext k
    simp
  haveI a1 : MeasurableAdd (R ⊗[F] E) := inferInstance
  haveI a2 : SigmaFinite (coordK R b lam) := inferInstance
  refine ⟨hK, ?_, ?_⟩
  · intro n M
    unfold coordW
    haveI a3 : (Measure.pi fun _ : Fin M => coordK R b lam).IsAddHaarMeasure := inferInstance
    infer_instance
  · intro n
    haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
    haveI a3 : (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam).IsAddHaarMeasure :=
      inferInstance
    haveI a4 : (Measure.pi fun _ : Fin n => lam).IsAddHaarMeasure := inferInstance
    haveI a5 : ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)).IsAddHaarMeasure :=
      inferInstance
    exact HaarCoord.haar_comap (HaarCoord.hermCoord R σ n) (HaarCoord.hermCoord_add R σ n)
      (HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6) _
end GlobalTheory.CompanionTheory.SW
