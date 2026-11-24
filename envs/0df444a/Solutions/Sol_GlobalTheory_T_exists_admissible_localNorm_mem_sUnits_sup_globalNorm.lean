-- Prove2me | solution 1 for GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:10:59.984185+00:00
-- url     : https://prove2.me/submissions/bbd72f32-e923-4a96-8f23-1466b686647e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Theorems.Thm_GlobalTheory_QNorm_exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) → ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ, (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) → t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | exact GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | (intros; apply GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub <;> assumption)
end _root_.GlobalTheory.T
