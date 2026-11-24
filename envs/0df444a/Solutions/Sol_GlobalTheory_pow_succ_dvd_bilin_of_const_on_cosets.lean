-- Prove2me | solution 1 for GlobalTheory.pow_succ_dvd_bilin_of_const_on_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:53.170832+00:00
-- url     : https://prove2.me/submissions/a752555e-caa2-42be-8a71-362debc011f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution (h2 : IsUnit (2 : R)) (r : R)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) (i : ℕ)
    (hi : ∀ x y, r ^ i ∣ B x y) (x y : M) : r ^ (i + 1) ∣ B x y := by
  have h1 : ∀ z, r ^ (i + 1) ∣ B z z - c := by
    intro z
    obtain ⟨t, ht, a, rfl⟩ := hT z
    have : B (t + r • a) (t + r • a) - c = (B t a + B a t + r * B a a) * r := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ← hc t ht]
      ring
    rw [this, pow_succ]
    exact mul_dvd_mul_right (((hi _ _).add (hi _ _)).add ((hi _ _).mul_left _)) r
  have h0 : r ^ (i + 1) ∣ c := by simpa using h1 0
  have h3 : ∀ z, r ^ (i + 1) ∣ B z z := fun z => by simpa using (h1 z).add h0
  have h4 : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
    simp only [map_add, LinearMap.add_apply, hB y x]
    ring
  exact h2.dvd_mul_left.1 (h4 ▸ ((h3 _).sub (h3 _)).sub (h3 _))
end GlobalTheory
