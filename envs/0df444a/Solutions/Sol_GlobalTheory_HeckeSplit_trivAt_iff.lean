-- Prove2me | solution 1 for GlobalTheory.HeckeSplit.trivAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:50.9688+00:00
-- url     : https://prove2.me/submissions/b047150e-1e83-496f-9462-f42aa8101321

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
    _root_.GlobalTheory.HeckeSplit.TrivAt χ.1 v ↔ χ.loc v = 1 := by
  unfold _root_.GlobalTheory.HeckeSplit.TrivAt
  rw [DFunLike.ext_iff]
  unfold _root_.Formalism.L2.Host.HChar.loc
  rfl
end _root_.GlobalTheory.HeckeSplit
end GlobalTheory.HeckeSplit
