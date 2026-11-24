-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.finPart_localIdele_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:48.520232+00:00
-- url     : https://prove2.me/submissions/6666feeb-3c3d-42de-8456-e060875f454a

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_infIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_finPart_infIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_finPart_localIdele
import Theorems.Thm_GlobalTheory_HeckeSplit_infPart_localIdele
import Theorems.Thm_Neutral_B1_localIdele_isSupportedAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HeckeSplit.infPart_infIdele
attribute [local simp] GlobalTheory.HeckeSplit.finPart_infIdele
attribute [local simp] GlobalTheory.HeckeSplit.finPart_localIdele
attribute [local simp] GlobalTheory.HeckeSplit.infPart_localIdele

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
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v)
    (x : (v.adicCompletion L)ˣ) : _root_.GlobalTheory.HeckeSplit.finPart L w (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext ((_root_.Neutral.B1.localIdele_isSupportedAt L v x).2 w h)
end _root_.GlobalTheory.HeckeSplit
end GlobalTheory.HeckeSplit
