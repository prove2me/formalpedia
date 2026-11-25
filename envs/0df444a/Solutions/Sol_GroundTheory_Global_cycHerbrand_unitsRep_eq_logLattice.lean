-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_unitsRep_eq_logLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:05:05.05314+00:00
-- url     : https://prove2.me/submissions/406d07f0-3215-4b8a-8379-84af0225add7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_surjective_of_finite_ker
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_cycSubOne_of_finite
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
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L]
omit [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep K L) σ = cycHerbrand (logLatticeRep K L) σ := by
  let p : Additive (𝓞 L)ˣ →+ logLattice L := (fullLog L).toIntLinearMap.rangeRestrict.toAddMonoidHom
  have hp : Function.Surjective p := (fullLog L).toIntLinearMap.surjective_rangeRestrict
  have : Finite p.ker := by
    refine Finite.of_injective (β := torsion L)
      (fun x => ⟨(x : Additive (𝓞 L)ˣ).toMul, (fullLog_eq_zero_iff L x).1 ?_⟩) ?_
    · have := congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2)
      exact this
    · intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Additive.toMul.injective h)
  exact cycHerbrand_eq_of_surjective_of_finite_ker (unitsRep K L) (logLatticeRep K L) σ hp
    (fun g x => Subtype.ext (fullLog_unitsRep g x))
    (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
end GroundTheory.Global
