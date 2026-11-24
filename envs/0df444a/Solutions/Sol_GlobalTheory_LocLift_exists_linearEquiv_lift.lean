-- Prove2me | solution 1 for GlobalTheory.LocLift.exists_linearEquiv_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:26.883792+00:00
-- url     : https://prove2.me/submissions/82e1ad81-fc25-4bce-9622-33fa656ea549

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Theorems.Thm_GlobalTheory_LocLift_isDiscrete_of_norm
import Theorems.Thm_GlobalTheory_existsUnique_linearEquiv_of_uniformisations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Q : Type} [Group Q]
namespace GlobalTheory.LocLift
theorem _root_.solution [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {x : V → Q} {e : W → Q}
    (hx : ∀ z w, x (z + w) = x z * x w) (h : ∀ z w, e (z + w) = e z * e w) (hsx : Function.Surjective x)
    (hs : Function.Surjective e) (hkx : IsDiscrete {z | x z = 1})
    {r : ℝ} (hr : 0 < r) (hk : ∀ z, ‖z‖ < r → e z = 1 → z = 0) {ζ : V → W}
    (hd : DifferentiableAt ℂ ζ 0) (hζ : ∀ᶠ z in 𝓝 0, e (ζ z) = x z) : ∃ L : V ≃L[ℂ] W, ∀ z, e (L z) = x z := by
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := hs a
      obtain ⟨b, rfl⟩ := hs b
      rw [← h, ← h, add_comm] }
  obtain ⟨L, hL, -⟩ := existsUnique_linearEquiv_of_uniformisations (𝕜 := ℂ) (A := Additive Q)
    (ex := AddMonoidHom.mk' (fun z => Additive.ofMul (x z)) fun z w => congrArg _ (hx z w))
    (ex' := AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => congrArg _ (h z w))
    hkx (isDiscrete_of_norm hr fun z hz hn => hk z hn hz) (fun q _ => hsx q) hd hζ
  exact ⟨L, hL.1⟩
end GlobalTheory.LocLift
