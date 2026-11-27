-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBaseChangeAt_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:02.53919+00:00
-- url     : https://prove2.me/submissions/ab4b4597-6f36-42f3-9238-98a341397f20

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sectionLinearAt_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBaseChangeAt_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBaseChangeAt_of_isOpenImmersion
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBaseChangeAt_of_comp_isOpenImmersion
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBaseChangeAt_top_of_isAffine
import Theorems.Thm_GroundTheory_Arith_Etale_openInclLE_left
import Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Etale.openInclLE_left
attribute [local simp] GroundTheory.Arith.Etale.openIncl_left


attribute [local simp] GroundTheory.Arith.SchemeCoh.sectionLinearAt_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {W T U : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (g : T ⟶ U) (N : U.Modules) [N.IsQuasicoherent]
    {V : U.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (g ⁻¹ᵁ V)) :
    IsBaseChangeAt g N V := by
  refine IsBaseChangeAt.of_comp_isOpenImmersion (f := (g ⁻¹ᵁ V).ι) (by simp) ?_
  rw [← morphismRestrict_ι g V]
  refine IsBaseChangeAt.comp (isBaseChangeAt_of_isOpenImmersion V.ι N (by simp)) ?_
  rw [Scheme.Opens.ι_preimage_self]
  have : IsAffine V := hV
  have : IsAffine (g ⁻¹ᵁ V) := hV'
  have : ((Scheme.Modules.pullback V.ι).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N) inferInstance
  exact isBaseChangeAt_top_of_isAffine (g ∣_ V) _
end GroundTheory.Arith.SchemeCoh
