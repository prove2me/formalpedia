-- Prove2me | solution 1 for GlobalTheory.NL.Model.mem_latSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:49.33163+00:00
-- url     : https://prove2.me/submissions/78897f4c-33d7-477d-bc2c-6689468c0c2f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_conv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
open TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.NL.Model
namespace _root_.GlobalTheory.NL.Model
theorem _root_.solution {ι : Type} (ex : ι → ℤ → M) (x : ι) :
    ex x ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex :=
  Submodule.subset_span ⟨1, x, (_root_.GlobalTheory.NL.Model.conv_one _).symm⟩
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model
