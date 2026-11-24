-- Prove2me | solution 1 for GlobalTheory.VectorInclusion.vecIncl_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:47.9643+00:00
-- url     : https://prove2.me/submissions/2277c3b6-5fae-45ee-9c06-97f2259e93bf

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InclEIntMem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open scoped TensorProduct
noncomputable section
open Classical
open GlobalTheory GlobalTheory.VectorInclusion
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.VectorInclusion
theorem _root_.solution (c : 𝓞 E) (x : Fin n → E) :
    vecIncl (F := F) (c • x) =
      (⟨Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E), inclE_int_mem c⟩ : Formalism.MainNotions.S.IntAf F E) •
        vecIncl (F := F) x := by
  funext i
  simp only [vecIncl, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl
end GlobalTheory.VectorInclusion
