-- Prove2me | solution 1 for GlobalTheory.CM.TenExp.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:54.342416+00:00
-- url     : https://prove2.me/submissions/28cc1048-3f24-419a-ad06-52782f63ebc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp
variable {O M : Type} [CommRing O] [Algebra O ℂ] [AddCommGroup M] [Module O M]
namespace GlobalTheory.CM.TenExp
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (f : M →+ V)
    (hf : ∀ (o : O) a, f (o • a) = algebraMap O ℂ o • f a) :
    ∃ F : ℂ ⊗[O] M →ₗ[ℂ] V, ∀ z a, F (z ⊗ₜ a) = z • f a := by
  letI : Module O V := Module.compHom V (algebraMap O ℂ)
  haveI : IsScalarTower O ℂ V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f' : M →ₗ[O] V := { f with map_smul' := hf }
  exact ⟨f'.liftBaseChange ℂ, fun z a => rfl⟩
end GlobalTheory.CM.TenExp
