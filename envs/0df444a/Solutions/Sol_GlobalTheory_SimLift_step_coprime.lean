-- Prove2me | solution 1 for GlobalTheory.SimLift.step_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:08.886982+00:00
-- url     : https://prove2.me/submissions/496c946c-f461-4808-953e-9544e82e233e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus

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
theorem _root_.solution {n r : ℕ} (hnr : IsCoprime (n : ℤ) (r : ℤ)) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ}
    (hf : IsSimMod D n f ν) :
    ∃ f' ν', IsSimMod D (n * r) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  obtain ⟨x, y, hxy⟩ := hnr
  obtain ⟨hc, hB⟩ := hf
  refine ⟨(y * r) • f + (x * n) • LinearMap.id, y * r * ν + x * n, ⟨?_, fun a b => ?_⟩,
    fun a => ⟨x • (a - f a), ?_⟩, ⟨x * (1 - ν), by linear_combination ν * hxy⟩⟩
  · push_cast
    refine IsCoprime.mul_right ?_ ?_
    · obtain ⟨κ, t, hκ⟩ := hc
      exact ⟨κ, t - κ * x * (1 - ν), by linear_combination hκ + κ * ν * hxy⟩
    · exact ⟨1, y * (1 - ν), by linear_combination hxy⟩
  · obtain ⟨B, hB⟩ := hB a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_zsmul,
      smul_eq_mul]
    refine ⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩
    push_cast
    linear_combination (y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b) * hxy
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h : y * (r : ℤ) = 1 - n * x := by linear_combination hxy
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]; abel
end GlobalTheory.SimLift
