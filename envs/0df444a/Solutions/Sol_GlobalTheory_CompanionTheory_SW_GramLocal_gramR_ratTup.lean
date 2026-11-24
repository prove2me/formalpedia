-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.gramR_ratTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:23.128288+00:00
-- url     : https://prove2.me/submissions/8c1ec394-2377-4651-9fa0-339ca4942123

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
namespace GlobalTheory.CompanionTheory.SW.GramLocal
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b
  simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]
end GlobalTheory.CompanionTheory.SW.GramLocal
