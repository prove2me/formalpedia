-- Prove2me | solution 1 for GlobalTheory.SimLift.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:35.919564+00:00
-- url     : https://prove2.me/submissions/3894877c-4766-4129-aa24-f74a2f052960

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Theorems.Thm_GlobalTheory_SimLift_modN_of_dvd_modulus
import Theorems.Thm_GlobalTheory_SimLift_modN_trans
import Theorems.Thm_GlobalTheory_SimLift_IsSimMod_of_dvd
import Theorems.Thm_GlobalTheory_SimLift_step_sq
import Theorems.Thm_GlobalTheory_SimLift_step_coprime

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
noncomputable section
open GlobalTheory GlobalTheory.SimLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.SimLift
theorem _root_.solution (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), IsSimMod D n f ν →
    ∃ f' ν', IsSimMod D (n * m) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f ν hf
    exact ⟨f, ν, by simpa using hf, fun a => ⟨0, by simp⟩, by simp⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f ν hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f' ν', IsSimMod D (n * p) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', ν, h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2, by simp⟩
      · exact step_coprime D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, ν₁, h1, h2, h3⟩ := h1
    obtain ⟨f₂, ν₂, h4, h5, h6⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ ν₁ h1
    refine ⟨f₂, ν₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x), ?_⟩
    have h7 : (n : ℤ) ∣ ν₂ - ν₁ := (Int.natCast_dvd_natCast.mpr (dvd_mul_right n p)).trans h6
    simpa using dvd_add h7 h3
end GlobalTheory.SimLift
