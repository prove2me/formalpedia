-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.IsHeckeChar.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:27.68786+00:00
-- url     : https://prove2.me/submissions/5775de52-6105-4ab0-932d-2ae6c4fa755e

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
theorem _root_.solution {χ ψ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) (hψ : IsHeckeChar L ψ) :
    IsHeckeChar L (χ * ψ) := (Formalism.L2.Host.hcharSub L).mul_mem hχ hψ
end IsHeckeChar
end GlobalTheory.HeckeSplit
