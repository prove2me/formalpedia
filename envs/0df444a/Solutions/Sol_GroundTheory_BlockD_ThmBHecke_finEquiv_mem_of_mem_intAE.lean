-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.finEquiv_mem_of_mem_intAE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:57.499396+00:00
-- url     : https://prove2.me/submissions/dc2b8b69-4eab-4a2d-8414-80e89fc9c3d6

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finEquiv_tmul
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_algebraMap_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finiteAdeleMap_mem_integralFiniteAdeles

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
theorem _root_.solution {y : Af F ⊗[F] E} (hy : y ∈ intAE F E) :
    finEquiv F E y ∈ integralFiniteAdeles (𝓞 E) E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [finEquiv_tmul]
    exact Subring.mul_mem _ (algebraMap_mem_integralFiniteAdeles x)
      (finiteAdeleMap_mem_integralFiniteAdeles ha)
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact Subring.add_mem _ h1 h2
  | neg _ _ h => rw [map_neg]; exact Subring.neg_mem _ h
end GroundTheory.BlockD.ThmBHecke
