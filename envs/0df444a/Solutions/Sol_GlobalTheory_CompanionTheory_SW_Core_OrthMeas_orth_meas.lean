-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:32.065323+00:00
-- url     : https://prove2.me/submissions/2fc9e7f3-6952-4fc3-9831-faec9b5ea26f

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_OrthMeas_chiB_mulVec_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_OrthMeas_map_eq_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.OrthMeas
namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)),
    NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B →
      Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ →
        SB (fun x => φ (g *ᵥ x)) ∧
          ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by
  intro R _ _ _ ι _ _ ψ h B μ hQ g hdet hg
  obtain ⟨hTR, -, -, -, -, hD⟩ := hQ
  haveI := hTR
  have hBS : BorelSpace (ι → R) := hD.2.2.2.2.1
  have he : Continuous (mulVecEquiv g hdet) :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hes : Continuous (mulVecEquiv g hdet).symm :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hχ : ∀ x y, chiB ψ B (mulVecEquiv g hdet x) (mulVecEquiv g hdet y) = chiB ψ B x y :=
    chiB_mulVec_mulVec ψ B g hg
  have hmap : Measure.map (fun x => g *ᵥ x) μ = μ :=
    map_eq_self (chiB ψ B) μ hD (mulVecEquiv g hdet) he hes hχ
  let t : (ι → R) ≃ₜ (ι → R) :=
    { toEquiv := (mulVecEquiv g hdet).toEquiv, continuous_toFun := he, continuous_invFun := hes }
  refine ⟨hmap, fun φ hφ => ⟨⟨hφ.1.comp_continuous he, hφ.2.comp_homeomorph t⟩, fun y => ?_⟩⟩
  have hI := t.measurableEmbedding.integral_map (μ := μ) (fun x => φ x * chiB ψ B x (g *ᵥ y))
  have ht : (⇑t : (ι → R) → (ι → R)) = fun x => g *ᵥ x := rfl
  rw [ht, hmap] at hI
  simp only [fou]
  rw [hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [chiB_mulVec_mulVec ψ B g hg]
end GlobalTheory.CompanionTheory.SW.Core.OrthMeas
