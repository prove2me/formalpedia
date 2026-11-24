-- Prove2me | solution 1 for GlobalTheory.BaseRing.exists_pow_mul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:25.301336+00:00
-- url     : https://prove2.me/submissions/215a0216-36e3-4dd8-8a8b-f6e8b97c960a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmModelCoefficientSubringDedekindCompatibleEmbed
import Theorems.Thm_GlobalTheory_BaseRing_zeta_pow_self
import Theorems.Thm_GlobalTheory_BaseRing_isIntegral_half_one_add_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BaseRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.BaseRing
theorem _root_.solution (H : Host E) {S A : ℕ} (hS : 0 < S) (hA : 0 < A) {z : ℂ}
    (hz : z ∈ RZ H S A) : ∃ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k * z) := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hp : ∀ k : ℕ, IsIntegral ℤ ((S : ℂ) ^ k) := fun k => (isIntegral_natCast S).pow k
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simpa using isIntegral_half_one_add_sqrt H⟩
    · exact ⟨1, by simpa [hS'] using isIntegral_one⟩
    · exact ⟨0, by simpa using IsIntegral.of_pow hA (zeta_pow_self hA ▸ isIntegral_one)⟩
  | zero => exact ⟨0, by simpa using isIntegral_zero⟩
  | one => exact ⟨0, by simpa using isIntegral_one⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have e : (S : ℂ) ^ (a + b) * (x + y) = S ^ b * (S ^ a * x) + S ^ a * (S ^ b * y) := by ring
    exact ⟨a + b, e ▸ ((hp b).mul ha).add ((hp a).mul hb)⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by simpa using ha.neg⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have e : (S : ℂ) ^ (a + b) * (x * y) = (S ^ a * x) * (S ^ b * y) := by ring
    exact ⟨a + b, e ▸ ha.mul hb⟩
end GlobalTheory.BaseRing
