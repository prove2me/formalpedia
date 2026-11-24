-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TopH.hform_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:07.056809+00:00
-- url     : https://prove2.me/submissions/d2ac33d8-b84b-479e-abe1-01f3d0a5520f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.TopH
theorem _root_.solution {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J g : Matrix (Fin m) (Fin m) A)
    (hg : cT σ g * J * g = J) (x y : Fin m → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ x y : Fin m → A, hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [key, key, hs]
  conv_lhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  congr 1
  change cT σ g *ᵥ (J *ᵥ (g *ᵥ y)) = J *ᵥ y
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
end GlobalTheory.CompanionTheory.SW.TopH
