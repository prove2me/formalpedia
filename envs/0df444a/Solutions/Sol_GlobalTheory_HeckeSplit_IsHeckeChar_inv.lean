-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.IsHeckeChar.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:29.429167+00:00
-- url     : https://prove2.me/submissions/7d0e5620-059d-4458-a685-1121cee40b31

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
namespace IsHeckeChar
theorem _root_.solution {χ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) :
    IsHeckeChar L χ⁻¹ := (Formalism.L2.Host.hcharSub L).inv_mem hχ
end IsHeckeChar
end GlobalTheory.HeckeSplit
