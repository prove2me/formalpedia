-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.unrAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:37.377995+00:00
-- url     : https://prove2.me/submissions/894b8b84-d246-4327-8d8e-a0c13ba4cd3b

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
open NumberField IsDedekindDomain
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)
namespace GlobalTheory.HeckeSplit
namespace _root_.GlobalTheory.HeckeSplit
theorem _root_.solution (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.UnrAt χ.1 v ↔ χ.UnrAt v := by
  unfold _root_.GlobalTheory.HeckeSplit.UnrAt _root_.Formalism.L2.Host.HChar.UnrAt _root_.Formalism.L2.Host.IsUnitAt _root_.Formalism.L2.Host.HChar.loc
  rfl
end _root_.GlobalTheory.HeckeSplit
end GlobalTheory.HeckeSplit
