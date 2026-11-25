-- Prove2me | solution 1 for GroundTheory.Global.prod_card_stabilizer_infinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:32:33.432359+00:00
-- url     : https://prove2.me/submissions/0a1c2d4d-8ef9-4282-aeac-38589398a951

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
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
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
omit [NumberField L]
open scoped Classical
namespace GroundTheory.Global
theorem _root_.solution
    [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L))] :
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L),
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) := by
  classical
  refine Fintype.prod_equiv InfinitePlace.orbitRelEquiv _ _ fun ω => ?_
  have h1 : InfinitePlace.orbitRelEquiv ω = (Quotient.out ω).comap (algebraMap K L) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  rw [h1, InfinitePlace.card_stabilizer, InfinitePlace.isUnramifiedIn_comap]
  split_ifs <;> simp
end GroundTheory.Global
