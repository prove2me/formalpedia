-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SizeScale.tup_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:40.792863+00:00
-- url     : https://prove2.me/submissions/21ceeb85-ff19-4fd8-bb72-e3c5e7634ea3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_size_nonneg

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeScale
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.SizeScale
theorem _root_.solution {M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    0 ≤ sizeTup b X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _
end GlobalTheory.CompanionTheory.SW.SizeScale
