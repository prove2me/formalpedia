-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.isValChar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:29.156122+00:00
-- url     : https://prove2.me/submissions/abee0bcb-2a56-4377-8884-12e7dcf2a8c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_expIn_eq_zero
import Theorems.Thm_GlobalTheory_CMVal_Model_levelLe_one
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Model
theorem _root_.solution {I : Type} [Fintype I] (φ : I → E →+* ℂ) (Q : Finset (HeightOneSpectrum (OF E))) :
    IsValChar φ 0 (fun _ => 0) ⊤ Q (1 : HChar E) := by
  refine ⟨fun x => by simp, ⟨fun v k => ?_, fun w k => ?_⟩, fun k => ?_, fun v P _ => ⟨fun _ => levelLe_one P 1, fun _ m => ?_⟩⟩
  · unfold Formalism.L2.Host.HChar.resFin
    rw [MonoidHom.finset_prod_apply]
    exact Finset.prod_eq_one fun _ _ => rfl
  · unfold Formalism.L2.Host.HChar.resInf
    rw [MonoidHom.finset_prod_apply]
    exact Finset.prod_eq_one fun _ _ => rfl
  · have : (1 : HChar E).inf k = 1 := rfl
    simp [this]
  · have : expIn (⊤ : Ideal (OF E)) v = 0 := expIn_eq_zero.2 (fun h => v.isPrime.ne_top (by
      rwa [Ideal.dvd_iff_le, top_le_iff] at h))
    simp [this, levelLe_one]
end GlobalTheory.CMVal.Model
