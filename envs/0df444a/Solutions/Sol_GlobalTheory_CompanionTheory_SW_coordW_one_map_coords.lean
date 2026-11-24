-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.coordW_one_map_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:07.092349+00:00
-- url     : https://prove2.me/submissions/31d1d81c-1912-449a-b18a-6bc1ad92e919

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasurableCoordinateMapsTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_map_curry_pi_pi
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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (M : ℕ) (lam : Measure R), lam.IsAddHaarMeasure → (Measurable fun (X : Fin 1 → Fin M → R ⊗[F] E) (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) ∧ (coordW R b lam 1 M).map (fun X (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) = Measure.pi fun _ => lam := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b M lam hlam
  obtain ⟨-, -, -, -, -, -, hom, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hh := hom d b
  let e : (R ⊗[F] E) ≃ᵐ (Fin d → R) := (hh.homeomorph _).toMeasurableEquiv
  have hce : (⇑e : (R ⊗[F] E) → Fin d → R) =
      fun y k => (Algebra.TensorProduct.basis R b).repr y k := rfl
  have hK : (coordK R b lam).map e = Measure.pi fun _ => lam := by
    have h := e.measurableEmbedding.map_comap (Measure.pi fun _ : Fin d => lam)
    rw [e.surjective.range_eq, Measure.restrict_univ] at h
    rw [coordK, ← hce]
    exact h
  have hK' : coordK R b lam = (Measure.pi fun _ : Fin d => lam).map e.symm := by
    rw [← hK, Measure.map_map e.symm.measurable e.measurable]
    simp
  have : SigmaFinite (coordK R b lam) := by
    rw [hK']; exact e.symm.sigmaFinite_map
  have hmpK : MeasurePreserving e (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨e.measurable, hK⟩
  have h1 : MeasurePreserving (fun (X : Fin 1 → Fin M → R ⊗[F] E) => X default)
      (coordW R b lam 1 M) (Measure.pi fun _ : Fin M => coordK R b lam) :=
    measurePreserving_funUnique (Measure.pi fun _ : Fin M => coordK R b lam) (Fin 1)
  have h2 : MeasurePreserving (fun (Y : Fin M → R ⊗[F] E) (i : Fin M) => e (Y i))
      (Measure.pi fun _ : Fin M => coordK R b lam)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam) :=
    measurePreserving_pi _ _ fun _ => hmpK
  have h3 : MeasurePreserving (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2)
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam)
      (Measure.pi fun _ : Fin M × Fin d => lam) :=
    ⟨by fun_prop, map_curry_pi_pi lam M d⟩
  have h := h3.comp (h2.comp h1)
  exact ⟨h.measurable, h.map_eq⟩
end GlobalTheory.CompanionTheory.SW
