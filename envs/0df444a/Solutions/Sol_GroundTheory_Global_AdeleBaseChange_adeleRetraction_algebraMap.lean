-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleRetraction_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:48:39.806963+00:00
-- url     : https://prove2.me/submissions/9819b004-39c7-49b1-b3b5-75a32fe2e4d4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (l : L) :
    adeleRetraction K L (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (normalizedTrace K L l) := by
  have h : (adeleTensorEquiv K L).symm (algebraMap L 𝔸[L] l) = l ⊗ₜ 1 := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]
  rw [adeleRetraction, h]
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (l ⊗ₜ 1)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.algebraMap_eq_smul_one]
end GroundTheory.Global.AdeleBaseChange
