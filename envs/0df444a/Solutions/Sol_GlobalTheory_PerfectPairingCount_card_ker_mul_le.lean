-- Prove2me | solution 1 for GlobalTheory.PerfectPairingCount.card_ker_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:26.943936+00:00
-- url     : https://prove2.me/submissions/683ba164-f5be-47b5-a1a0-4ffbd8a378ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Theorems.Thm_GlobalTheory_PerfectPairingCount_finite_unitsChar
import Theorems.Thm_GlobalTheory_PerfectPairingCount_card_unitsChar_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PerfectPairingCount
variable {F : Type} [Field F]
variable {A : Type} [CommGroup A] [Finite A]
namespace GlobalTheory.PerfectPairingCount
theorem _root_.solution (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (H K : Subgroup A) (hK : ∀ k ∈ K, ∀ h ∈ H, E k h = 1) :
    Nat.card K * Nat.card H ≤ Nat.card A := by
  haveI := finite_unitsChar (F := F) (A ⧸ H)
  let φ : K → (A ⧸ H →* Fˣ) := fun k =>
    QuotientGroup.lift H (E k) (fun h hh => hK k k.2 h hh)
  have hφ : Function.Injective φ := by
    intro k k' hkk
    have h1 : E k = E k' := by
      apply MonoidHom.ext
      intro b
      have := DFunLike.congr_fun hkk (QuotientGroup.mk b)
      exact this
    have h2 : (k : A) * (k' : A)⁻¹ = 1 := by
      apply hE
      intro b
      rw [map_mul, map_inv, h1, mul_inv_cancel]
      rfl
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have h3 : Nat.card K ≤ Nat.card (A ⧸ H) :=
    (Nat.card_le_card_of_injective φ hφ).trans (card_unitsChar_le _)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
  exact Nat.mul_le_mul_right _ h3
end GlobalTheory.PerfectPairingCount
