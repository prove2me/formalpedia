-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.finPart_infIdele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:58.820066+00:00
-- url     : https://prove2.me/submissions/6d39069b-24fd-4a14-9750-466c20ebb8af

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_infIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HeckeSplit.infPart_infIdele

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeSplit
open NumberField IsDedekindDomain HeckeValGen
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)
open NumberField IsDedekindDomain
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)
namespace GlobalTheory.HeckeSplit
namespace _root_.GlobalTheory.HeckeSplit
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L))
    (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.GlobalTheory.HeckeSplit.infIdele L x) = 1 :=
  Units.ext rfl
end _root_.GlobalTheory.HeckeSplit
end GlobalTheory.HeckeSplit
