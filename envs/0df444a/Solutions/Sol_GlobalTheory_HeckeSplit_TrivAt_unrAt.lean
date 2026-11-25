-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.TrivAt.unrAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:33.496772+00:00
-- url     : https://prove2.me/submissions/ec41cd9e-3c58-4924-8903-7a88f51a25c7

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeSplit
open NumberField IsDedekindDomain HeckeValGen
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)
variable {L}
namespace GlobalTheory.HeckeSplit
namespace TrivAt
theorem _root_.solution {χ : Ideles L →* ℂˣ} {v : HeightOneSpectrum (𝓞 L)} (h : TrivAt χ v) :
    UnrAt χ v := fun x _ => h x
end TrivAt
end GlobalTheory.HeckeSplit
