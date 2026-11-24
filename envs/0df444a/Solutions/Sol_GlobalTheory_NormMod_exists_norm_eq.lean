-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:13.596178+00:00
-- url     : https://prove2.me/submissions/542b07cc-a0a1-4f0e-b47b-047f287f7a52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Theorems.Thm_GlobalTheory_NormMod_exists_sq_sub_mul_sq
import Theorems.Thm_GlobalTheory_NormMod_exists_isUnit_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
variable {R : Type*} [CommRing R] [Finite R]
namespace GlobalTheory.NormMod
theorem _root_.solution (σ : R →+* R) (htop : Ideal.span {a | σ a = -a} = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h0 : (p : R) = 0) {ν : R} (hν : IsUnit ν) (hfix : σ ν = ν) :
    ∃ t, t * σ t = ν := by
  obtain ⟨δ, hδ, hu⟩ := exists_isUnit_neg σ htop
  have unit : ∀ (a : R) (ha : σ a = a), IsUnit a →
      IsUnit (⟨a, ha⟩ : σ.eqLocus (RingHom.id R)) := by
    intro a ha h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have h2 := congrArg σ hb
    rw [map_mul, ha, map_one] at h2
    have h3 : σ b = b := by linear_combination b * h2 - σ b * hb
    exact IsUnit.of_mul_eq_one ⟨b, h3⟩ (Subtype.ext hb)
  have hD : σ (δ ^ 2) = δ ^ 2 := by rw [map_pow, hδ, neg_sq]
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩ := exists_sq_sub_mul_sq hp hp2
    (R := σ.eqLocus (RingHom.id R)) (Subtype.ext (by simpa using h0))
    (unit _ hD (hu.pow 2)) (unit _ hfix hν)
  have hx' : σ x = x := hx
  have hy' : σ y = y := hy
  have h' : x ^ 2 - δ ^ 2 * y ^ 2 = ν := congrArg Subtype.val h
  refine ⟨x + y * δ, ?_⟩
  rw [map_add, map_mul, hx', hy', hδ]
  linear_combination h'
end GlobalTheory.NormMod
