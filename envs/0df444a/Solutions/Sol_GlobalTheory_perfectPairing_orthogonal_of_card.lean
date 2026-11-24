-- Prove2me | solution 1 for GlobalTheory.perfectPairing_orthogonal_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:51:39.140454+00:00
-- url     : https://prove2.me/submissions/96fede9c-307b-4167-9fdf-c028146f00ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Theorems.Thm_GlobalTheory_PerfectPairingCount_right_nondegenerate
import Theorems.Thm_GlobalTheory_PerfectPairingCount_one_side

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] (A : Type) [CommGroup A] [Finite A] (e : A → A → Fˣ), (∀ a a' b, e (a * a') b = e a b * e a' b) → (∀ a b b', e a (b * b') = e a b * e a b') → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ T H : Subgroup A, (∀ t ∈ T, ∀ h ∈ H, e t h = 1) → Nat.card T * Nat.card H = Nat.card A → (∀ x, (∀ h ∈ H, e x h = 1) ↔ x ∈ T) ∧ (∀ x, (∀ t ∈ T, e t x = 1) ↔ x ∈ H) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, e x h = χ h) ∧ (∀ χ : T →* Fˣ, ∃ x, ∀ t : T, e t x = χ t) := by
  intro F _ A _ _ e h1 h2 h3 T H hTH hc
  let E : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (e a) (h2 a)) (fun a a' => by
      apply MonoidHom.ext
      intro b
      exact h1 a a' b)
  have hE : ∀ a, (∀ b, E a b = 1) → a = 1 := h3
  have hE' : ∀ b, (∀ a, E.flip b a = 1) → b = 1 :=
    fun b hb => PerfectPairingCount.right_nondegenerate E hE b hb
  obtain ⟨a1, a2⟩ := PerfectPairingCount.one_side E hE T H hTH hc
  obtain ⟨b1, b2⟩ := PerfectPairingCount.one_side E.flip hE' H T
    (fun h hh t ht => hTH t ht h hh) (by rw [mul_comm, hc])
  exact ⟨a1, b1, a2, b2⟩
end GlobalTheory
