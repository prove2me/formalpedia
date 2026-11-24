-- Prove2me | solution 1 for GlobalTheory.PrimeSection.exists_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:12.322088+00:00
-- url     : https://prove2.me/submissions/a30fbe57-902a-4494-a32d-bd6e16d7e0f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Theorems.Thm_GlobalTheory_PrimeSection_res_appLE
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_res
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_bijective
import Theorems.Thm_GlobalTheory_PrimeSection_eq_preimage_inf
import Theorems.Thm_GlobalTheory_PrimeSection_exists_unit_eq_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
omit [IsIntegral X] [IsLocallyNoetherian X]
include hj
namespace GlobalTheory.PrimeSection
theorem _root_.solution (r : ∀ a, Γ(Y, W a))
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) :
    ∃ (r' : ∀ a, Γ(X, U a ⊓ X.basicOpen t)) (τ' : Γ(X, X.basicOpen t)ˣ),
      (τ' : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t ∧
      (∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r' a) =
        X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op
          (g a b) * X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r' b)) ∧
      (∀ a, r' a = 0 → r a = 0) ∧ (∀ a, IsUnit (r a) → IsUnit (r' a)) ∧
      ∀ (n : ℤ) (a : ι) (s : Γ(X, U a)), X.presheaf.map (homOfLE inf_le_left).op s =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ' ^ n) : Γ(X, X.basicOpen t)) * r' a ↔
        j.appLE (U a) (W a) (hW a).le s =
          Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a := by
  have hb := fun a ↦ appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj (hW a))
  choose r' hr' using fun a ↦ (hb a).2 (r a)
  obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
  have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
  have hττ : Units.map (j.appLE _ ⊤ htop).hom.toMonoidHom τ' = τ := by
    ext
    rw [Units.coe_map, hτ, hτ']
    exact (appLE_res j _ _ _).trans (congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Y, ⊤) ↦ φ t) j.appLE_eq_app)
  refine ⟨r', τ', hτ', fun a b ↦ ?_, fun a h ↦ by rw [← hr', h, map_zero], fun a h ↦ ?_,
    fun n a s ↦ ?_⟩
  · have hab : W a ⊓ W b = j ⁻¹ᵁ (U a ⊓ U b) := by rw [hW, hW]; rfl
    refine (appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj hab)).1 ?_
    have := hr a b
    rw [← hr' a, ← hr' b, res_appLE, res_appLE] at this
    rw [map_mul, appLE_res, appLE_res, appLE_res]
    exact this
  · rw [← hr' a] at h
    exact (isUnit_map_iff (RingEquiv.ofBijective _ (hb a)) _).1 h
  · rw [← (hb a).1.eq_iff, map_mul, appLE_res, appLE_res, hr', ← hττ, ← map_zpow, Units.coe_map]
    exact iff_of_eq (congrArg (_ = · * _) (res_appLE j htop le_top _).symm)
end GlobalTheory.PrimeSection
