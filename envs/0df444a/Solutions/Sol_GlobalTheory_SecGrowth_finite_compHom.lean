-- Prove2me | solution 1 for GlobalTheory.SecGrowth.finite_compHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:25.758802+00:00
-- url     : https://prove2.me/submissions/0eb1c9b8-3306-4bd1-819a-030ec0d3f648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
namespace GlobalTheory.SecGrowth
theorem _root_.solution {K R V : Type} [CommRing K] [CommRing R] (e : K ≃+* R) [AddCommGroup V] [Module R V]
    [Module.Finite R V] :
    letI := Module.compHom V e.toRingHom
    Module.Finite K V := by
  letI := Module.compHom V e.toRingHom
  haveI : RingHomSurjective (e.symm : R →+* K) := ⟨e.symm.surjective⟩
  let φ : V →ₛₗ[(e.symm : R →+* K)] V :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun c v => congrArg (· • v) (e.apply_symm_apply c).symm }
  exact Module.Finite.of_surjective φ Function.surjective_id
end GlobalTheory.SecGrowth
