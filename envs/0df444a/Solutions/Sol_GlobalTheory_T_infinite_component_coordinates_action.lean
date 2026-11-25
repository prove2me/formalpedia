-- Prove2me | solution 1 for GlobalTheory.T.infinite_component_coordinates_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:27.759877+00:00
-- url     : https://prove2.me/submissions/17c1a8fd-1d37-4ad6-8dc1-bb4eea0feb83

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesAction
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesActionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_coords_ratTup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (ω : HA (AF F) σ J) (x : Fin M × Fin d → F), (∀ w, xw e b (projInf (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x)))) w = ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ∧ cv (Af F) b (projFin (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x))) 0) = gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup | exact GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup | (intros; apply GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup <;> assumption)
end _root_.GlobalTheory.T
