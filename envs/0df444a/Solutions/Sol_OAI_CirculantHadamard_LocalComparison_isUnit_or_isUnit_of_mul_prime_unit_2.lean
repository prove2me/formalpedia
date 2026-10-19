-- Prove2me | solution 2 for OAI.CirculantHadamard.LocalComparison.isUnit_or_isUnit_of_mul_prime_unit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:38:12.210245+00:00
-- url     : https://prove2.me/submissions/a9e7ed53-7bf4-4fdd-995b-b7163af2662c

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean:L19-L40
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalComparison.isUnit_or_isUnit_of_mul_prime_unit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparisonInduction ----
namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

/-- If the product has exactly one prime factor up to a unit, at least one
factor is a unit. This elementary base step does not use a valuation. -/
theorem isUnit_or_isUnit_of_mul_prime_unit {p x y : A} (hp : Prime p)
    (b : Aˣ) (hxy : x * y = p * (b : A)) : IsUnit x ∨ IsUnit y := by
  have hdvd : p ∣ x * y := ⟨(b : A), hxy⟩
  rcases hp.dvd_or_dvd hdvd with hx | hy
  · obtain ⟨z, hz⟩ := hx
    have hzy : z * y = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (z * y) = (p * z) * y := (mul_assoc _ _ _).symm
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inr (isUnit_of_mul_isUnit_right (hzy.symm ▸ b.isUnit))
  · obtain ⟨z, hz⟩ := hy
    have hxz : x * z = (b : A) := by
      apply mul_left_cancel₀ hp.ne_zero
      calc
        p * (x * z) = x * (p * z) := by ac_rfl
        _ = x * y := by rw [← hz]
        _ = p * (b : A) := hxy
    exact Or.inl (isUnit_of_mul_isUnit_left (hxz.symm ▸ b.isUnit))

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
open CyclicRing


theorem solution.{uA} : type_of% @_root_.OAI.CirculantHadamard.LocalComparison.isUnit_or_isUnit_of_mul_prime_unit.{uA} := @_root_.OAI.CirculantHadamard.LocalComparison.isUnit_or_isUnit_of_mul_prime_unit.{uA}
