-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicGauss_normalized_cube_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:43.172556+00:00
-- url     : https://prove2.me/submissions/141b58c2-0361-4f5e-9ade-fe7d57a15700

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_conjO_omega
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_cube_complex
import Theorems.Thm_OAI_ActualEisensteinCubic_primary_generator_mul_conj_eq_card
section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftFiniteGaussFourier
namespace PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
end PoissonChildCRT
namespace PoissonFirstLocal
open scoped Classical
end PoissonFirstLocal
open Finset Complex
namespace ActualCubicChar
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
variable [Fintype F]
end ActualCubicChar
namespace ActualEisensteinCubic
section
open NumberField
end
private theorem ringComplex_conjO (x : O) :
    ringComplex (conjO x) = star (ringComplex x) := by
  let z := ringComplex omega
  have hz3 : z ^ 3 = 1 := by
    change ringComplex omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ringComplex.comp conjO.toRingHom = (starRingEnd ℂ).comp ringComplex := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ringComplex (conjO omega) = star (ringComplex omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx
end ActualEisensteinCubic
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) /
      (‖ringComplex p‖ : ℂ)) ^ 3 =
      -(ringComplex p) / (‖ringComplex p‖ : ℂ) := by
  let z := ringComplex p
  let g := gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
    (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P))
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ringComplex hnormO
  rw [map_mul, ringComplex_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact hqne hq
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube_complex P hgood p hP hprimary
  change (g / (‖z‖ : ℂ)) ^ 3 = -z / (‖z‖ : ℂ)
  rw [div_pow, hg, hq]
  field_simp
end OAI.ActualEisensteinCubic
