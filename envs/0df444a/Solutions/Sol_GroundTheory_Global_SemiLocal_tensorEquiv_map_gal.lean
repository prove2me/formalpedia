-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.tensorEquiv_map_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:26.520419+00:00
-- url     : https://prove2.me/submissions/cf9b53b9-3bbd-45c1-8329-903efdb343b1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Theorems.Thm_GroundTheory_Global_SemiLocal_galEquiv_algebraMap
import Theorems.Thm_GroundTheory_Global_SemiLocal_piGal_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero Topology Filter TensorProduct
open scoped Pointwise
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (σ : L ≃ₐ[K] L) (x : v.adicCompletion K ⊗[K] L) :
    tensorEquiv L v (Algebra.TensorProduct.map
      (AlgHom.id (v.adicCompletion K) (v.adicCompletion K)) σ.toAlgHom x) =
      piGal v σ (tensorEquiv L v x) := by
  have : (tensorEquiv L v).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        σ.toAlgHom) = (piGal v σ).comp (tensorEquiv L v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a l
    funext u
    simp [piGal_apply, Pi.mul_apply, galEquiv_algebraMap]
  exact DFunLike.congr_fun this x
end GroundTheory.Global.SemiLocal
