-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FTransfer.actTup_ratTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:18:56.261138+00:00
-- url     : https://prove2.me/submissions/f7ffaccb-3773-430d-922f-c99d6f1677c2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainTransportCongruentForm

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FTransfer
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.FTransfer
theorem _root_.solution {M n : ℕ} (g : GL (Fin M) E) (X : Fin n → Fin M → E) :
    actTup R (bc (inclR (F := F) R) g) (ratTup R X) =
      ratTup R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  have h := RingHom.map_mulVec (inclR (F := F) R) (g : Matrix (Fin M) (Fin M) E) (X a) i
  exact h.symm
end GlobalTheory.CompanionTheory.SW.FTransfer
