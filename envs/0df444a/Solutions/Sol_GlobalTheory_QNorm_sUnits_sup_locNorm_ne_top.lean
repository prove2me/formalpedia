-- Prove2me | solution 1 for GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:21.090515+00:00
-- url     : https://prove2.me/submissions/efedc1fe-da63-4fbf-a542-d8d56939663e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Theorems.Thm_GlobalTheory_QNorm_normSub_id_le_locNorm
import Theorems.Thm_GlobalTheory_T_two_mul_relIndex_normSub_sUnits_le
import Theorems.Thm_GlobalTheory_T_two_pow_le_index_localNormsSqrtExtension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  intro F _ _ δ S hS hδ hsq htop
  obtain ⟨hne, hle⟩ := GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le F δ S hS hδ hsq
  obtain ⟨-, hge⟩ := GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension F (δ : F) S δ.ne_zero
  have h1 : (locNorm F δ S).index = (locNorm F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h2 : (locNorm F δ S).relIndex (sUnits F S) ≤
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) :=
    Subgroup.relIndex_le_of_le_left (normSub_id_le_locNorm F δ S) hne
  omega
end GlobalTheory.QNorm
