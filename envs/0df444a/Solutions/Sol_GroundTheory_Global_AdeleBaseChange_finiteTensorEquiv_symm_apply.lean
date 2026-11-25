-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.finiteTensorEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:18.753363+00:00
-- url     : https://prove2.me/submissions/e69cbce3-bf2a-4521-b32c-3f0bf1af003a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor

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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
attribute [local instance] GroundTheory.Global.AdeleBaseChange._p2m_local_instance_431a99de7f_75
attribute [local instance] GroundTheory.Global.AdeleBaseChange._p2m_local_instance_431a99de7f_78
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (y : FiniteAdeleRing (𝓞 L) L) :
    (finiteTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ finiteCoord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (finiteTensorMap_sum_finiteCoord b y).symm
end GroundTheory.Global.AdeleBaseChange
