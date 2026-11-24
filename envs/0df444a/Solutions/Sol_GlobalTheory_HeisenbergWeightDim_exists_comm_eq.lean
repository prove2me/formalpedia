-- Prove2me | solution 1 for GlobalTheory.HeisenbergWeightDim.exists_comm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:26:18.430089+00:00
-- url     : https://prove2.me/submissions/b6905a1e-e1be-4e21-a075-908e3e2f9d9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_comm_swap
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_comm_mul_left
import Theorems.Thm_GlobalTheory_HeisenbergWeightDim_comm_mul_right

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
open GlobalTheory GlobalTheory.HeisenbergWeightDim
variable {F : Type} [Field F] {A : Type} [CommGroup A] {E : Type} [AddCommGroup E] [Module F E]
variable [Nontrivial E] {e : A → A → Fˣ} {Φ : A → (E ≃ₗ[F] E)}
namespace GlobalTheory.HeisenbergWeightDim
theorem _root_.solution [Finite A] [HasEnoughRootsOfUnity F (Monoid.exponent A)]
    (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v))
    (hn : ∀ a, (∀ b, e a b = 1) → a = 1) (T : Subgroup A) (χ : T →* Fˣ) :
    ∃ a, ∀ t : T, e t a = χ t := by
  let P : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => e b a) (fun b b' => comm_mul_left hm hc b b' a))
      (fun a a' => by
        apply MonoidHom.ext
        intro b
        exact comm_mul_right hm hc b a a')
  have hinj : Function.Injective P := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply hn
    intro b
    have h1 : e b a = 1 := DFunLike.congr_fun ha b
    have h2 := comm_swap hc a b
    rwa [h1, _root_.mul_one] at h2
  haveI : Finite (A →* Fˣ) :=
    Finite.of_equiv A (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A F).some.toEquiv.symm
  have hbij : Function.Bijective P :=
    hinj.bijective_of_nat_card_le (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A F).le
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective F T χ
  obtain ⟨a, ha⟩ := hbij.2 ψ
  refine ⟨a, fun t => ?_⟩
  rw [← hψ, ← ha]
  rfl
end GlobalTheory.HeisenbergWeightDim
