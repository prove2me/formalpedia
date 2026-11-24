-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.cT_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:01.446052+00:00
-- url     : https://prove2.me/submissions/b9754f2e-8605-415b-978e-2621bd3c83a2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {A : Type} [CommRing A] {M n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution (s : A →+* A) (hs : ∀ x, s (s x) = x) {m p : Type} (B : Matrix m p A) :
    cT s (cT s B) = B := by
  ext i j
  simp [cT, hs]
end GlobalTheory.CompanionTheory.SW.GramAlg
