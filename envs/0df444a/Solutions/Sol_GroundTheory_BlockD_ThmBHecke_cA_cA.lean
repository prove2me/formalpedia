-- Prove2me | solution 1 for GroundTheory.BlockD.ThmBHecke.cA_cA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:18.567249+00:00
-- url     : https://prove2.me/submissions/ab0af946-c323-4fff-ba63-ace73f0b2b88

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_cA_tmul
import Theorems.Thm_GroundTheory_BlockD_ThmBHecke_IsCMExt_sigma_sigma

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
  GroundTheory.Global.SemiLocal
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E}
namespace GroundTheory.BlockD.ThmBHecke
theorem _root_.solution (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rw [cA_tmul, cA_tmul, IsCMExt.sigma_sigma h]
  | add y z hy hz => rw [map_add, map_add, hy, hz]
end GroundTheory.BlockD.ThmBHecke
