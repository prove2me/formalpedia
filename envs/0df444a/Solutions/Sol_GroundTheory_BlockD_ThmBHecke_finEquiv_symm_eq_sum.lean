-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.finEquiv_symm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:10.075795+00:00
-- url     : https://prove2.me/submissions/5168689f-1eb0-457a-96b0-a53ff7bf5bf7

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_symm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (t : FiniteAdeleRing (𝓞 E) E) :
    (finEquiv F E).symm t = ∑ i, finiteCoord b i t ⊗ₜ b i := by
  change (Algebra.TensorProduct.comm F (Af F) E).symm ((finiteTensorEquiv F E).symm t) = _
  rw [finiteTensorEquiv_symm_apply b, map_sum]
  rfl
end GroundTheory.BlockD.ThmBHecke
