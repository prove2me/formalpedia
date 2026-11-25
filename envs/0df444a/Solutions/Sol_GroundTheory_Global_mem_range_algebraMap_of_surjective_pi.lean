-- Prove2me | solution 1 for GroundTheory.Global.mem_range_algebraMap_of_surjective_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:59.434238+00:00
-- url     : https://prove2.me/submissions/9353304d-af29-4054-8a32-b9e17bc32d51

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
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
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) (e : E) :
    e ∈ Set.range (algebraMap F E) := by
  obtain ⟨y, rfl⟩ := hf e
  have h0 : ∏ i, (y - algebraMap F (ι → F) (y i)) = 0 := by
    funext j
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  have h1 : ∏ i, (f y - algebraMap F E (y i)) = 0 := by
    simpa [map_prod, map_sub, AlgHom.commutes] using congrArg f h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h1
  exact ⟨y i, (sub_eq_zero.mp hi).symm⟩
end GroundTheory.Global
