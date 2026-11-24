-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.tensor_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:57.372707+00:00
-- url     : https://prove2.me/submissions/2c462abf-35f4-4659-8b1a-de44f3d2e3a2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_repr_bcE
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_adele_ext

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
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.GramLocal
theorem _root_.solution [Module.Finite F E] (z w : AF F ⊗[F] E)
    (h1 : bcE E (fstA F) z = bcE E (fstA F) w)
    (h2 : ∀ v, bcE E (evalV F v) (bcE E (sndA F) z) = bcE E (evalV F v) (bcE E (sndA F) w)) :
    z = w := by
  classical
  let b := Module.finBasis F E
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  apply adele_ext
  · rw [← repr_bcE, ← repr_bcE, h1]
  · intro v
    rw [← repr_bcE, ← repr_bcE, ← repr_bcE, ← repr_bcE, h2 v]
end GlobalTheory.CompanionTheory.SW.GramLocal
