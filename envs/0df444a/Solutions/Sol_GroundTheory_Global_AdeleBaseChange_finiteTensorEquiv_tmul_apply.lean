-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.finiteTensorEquiv_tmul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:48.269364+00:00
-- url     : https://prove2.me/submissions/e8e545fb-27de-414b-83f8-ca24d067f3c9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_tmul
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



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
theorem _root_.solution (l : L) (a : FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 L)) :
    finiteTensorEquiv K L (l ⊗ₜ a) w =
      tensorEquiv' L (below K w) (l ⊗ₜ a (below K w)) ⟨w, liesOver_below w⟩ := by
  rw [finiteTensorEquiv_tmul, tensorEquiv'_tmul]
  rfl
end GroundTheory.Global.AdeleBaseChange
