-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_adele_finite_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:36.676472+00:00
-- url     : https://prove2.me/submissions/b5c23ef1-956e-481e-bdcf-bfe2738c3ff9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩
end GlobalTheory.QNorm
