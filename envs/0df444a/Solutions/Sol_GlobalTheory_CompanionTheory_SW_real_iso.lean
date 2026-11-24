-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.real_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:28.029089+00:00
-- url     : https://prove2.me/submissions/002e92c5-6949-4993-aa08-184a1146afd8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_isHomeomorph_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_abs_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_rho_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_algebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_map_coord_eq

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
open GlobalTheory.CompanionTheory.SW.RealCoord
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∃ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) ∧ IsHomeomorph e ∧ (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) ∧ (∀ y w, |e y w| = ‖y w‖) ∧ ∀ lam : Measure (Ainf F), IsStdInf lam → lam.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := by
  intro F _ _ hF
  haveI := hF
  exact ⟨rho F, coord F, rho_coe F, isHomeomorph_coord F, coord_algebraMap F, abs_coord F, map_coord_eq F⟩
end GlobalTheory.CompanionTheory.SW
