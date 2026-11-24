-- Prove2me | solution 1 for GlobalTheory.PerfectPairingCount.one_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:36:26.83718+00:00
-- url     : https://prove2.me/submissions/f31331de-2931-4c51-b8f0-fd9971e8ddd2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Theorems.Thm_GlobalTheory_PerfectPairingCount_finite_unitsChar
import Theorems.Thm_GlobalTheory_PerfectPairingCount_card_unitsChar_le
import Theorems.Thm_GlobalTheory_PerfectPairingCount_card_ker_mul_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
    (T H : Subgroup A) (hTH : ∀ t ∈ T, ∀ h ∈ H, E t h = 1)
    (hc : Nat.card T * Nat.card H = Nat.card A) :
    (∀ x, (∀ h ∈ H, E x h = 1) ↔ x ∈ T) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, E x h = χ h) := by
  let R : A →* (H →* Fˣ) :=
    { toFun := fun a => (E a).comp H.subtype
      map_one' := by apply MonoidHom.ext; intro h; simp
      map_mul' := by intro a a'; apply MonoidHom.ext; intro h; simp }
  have hR : ∀ x, x ∈ R.ker ↔ ∀ h ∈ H, E x h = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx h hh
      exact DFunLike.congr_fun hx ⟨h, hh⟩
    · intro hx
      apply MonoidHom.ext
      intro h
      exact hx h h.2
  have hle : T ≤ R.ker := fun t ht => (hR t).mpr (hTH t ht)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hcard : Nat.card R.ker ≤ Nat.card T := by
    have := card_ker_mul_le E hE H R.ker (fun k hk => (hR k).mp hk)
    rw [← hc] at this
    exact Nat.le_of_mul_le_mul_right this hHpos
  have heq : T = R.ker := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨fun x => by rw [← hR, heq], ?_⟩
  haveI := finite_unitsChar (F := F) H
  have hrange : Nat.card R.range = Nat.card H := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange R).toEquiv, ← heq, ← hc,
      mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hTpos h1).symm
  have htop : R.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hrange]
    exact card_unitsChar_le _
  intro χ
  have : χ ∈ R.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, fun h => DFunLike.congr_fun hx h⟩
end GlobalTheory.PerfectPairingCount
