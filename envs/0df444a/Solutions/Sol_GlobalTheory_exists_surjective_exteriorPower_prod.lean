-- Prove2me | solution 1 for GlobalTheory.exists_surjective_exteriorPower_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:55.615915+00:00
-- url     : https://prove2.me/submissions/356e373d-1806-4daf-9ac6-1d07aeffef29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE

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
open GlobalTheory
open scoped TensorProduct
variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] {n : ℕ}
namespace GlobalTheory
theorem _root_.solution (bN : Module.Basis (Fin n) A N) :
    ∃ φ : ⋀[A]^(n + 1) (M × N) →ₗ[A] M, Function.Surjective φ := by
  let c : M × N →ₗ[A] (M × N) [⋀^Fin n]→ₗ[A] M :=
    { toFun := fun x ↦ (bN.det.compLinearMap (LinearMap.snd A M N)).smulRight x.1
      map_add' := fun x y ↦ AlternatingMap.ext fun _ ↦ by simp
      map_smul' := fun c x ↦ AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm] }
  refine ⟨exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin c),
    fun m ↦ ⟨exteriorPower.ιMulti A (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i)), ?_⟩⟩
  simp [c, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, Module.Basis.det_self]
end GlobalTheory
