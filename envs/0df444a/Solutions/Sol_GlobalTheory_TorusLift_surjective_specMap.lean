-- Prove2me | solution 1 for GlobalTheory.TorusLift.surjective_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:27.814835+00:00
-- url     : https://prove2.me/submissions/39e7058e-7682-44d2-930f-d2cd1cb0e2c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusLift
namespace GlobalTheory.TorusLift
theorem _root_.solution {A C : CommRingCat.{0}} (β : A ⟶ C) (hβ : Function.Surjective β)
    (h : IsNilpotent (RingHom.ker β.hom)) : Surjective (Spec.map β) := by
  obtain ⟨n, hn⟩ := h
  have hh : IsHomeomorph (PrimeSpectrum.comap β.hom) := by
    refine PrimeSpectrum.isHomeomorph_comap β.hom (fun x => ⟨1, one_pos, ?_⟩) ?_
    · obtain ⟨y, rfl⟩ := hβ x
      exact ⟨y, by simp⟩
    · intro x hx
      have hxn : x ^ n ∈ RingHom.ker β.hom ^ n := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hxn
      exact mem_nilradical.2 ⟨n, hxn⟩
  exact ⟨hh.surjective⟩
end GlobalTheory.TorusLift
