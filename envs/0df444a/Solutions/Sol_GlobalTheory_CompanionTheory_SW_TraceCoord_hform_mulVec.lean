-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.hform_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:39.665158+00:00
-- url     : https://prove2.me/submissions/c10e8e9f-5506-4595-a94e-315cc7a66b52

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_hform_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_dot_mulVec_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution (s : A →+* A) (J H : Matrix (Fin M) (Fin M) A)
    (hH : cT s H * J * H = J) (x y : Fin M → A) :
    hform s J (H *ᵥ x) (H *ᵥ y) = hform s J x y := by
  have h1 : s ∘ (H *ᵥ x) = (H.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s H x i
  have h2 : (H.map s)ᵀ * J * H = J := hH
  rw [hform_eq, hform_eq, h1, dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]
end GlobalTheory.CompanionTheory.SW.TraceCoord
