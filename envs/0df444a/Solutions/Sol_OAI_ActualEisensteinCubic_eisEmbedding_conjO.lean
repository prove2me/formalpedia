-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.eisEmbedding_conjO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:02.437705+00:00
-- url     : https://prove2.me/submissions/868b946f-e863-4c9b-8402-5d2dc2c1dc09

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_conjO_omega


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
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (x : O) :
    ConcreteTraceCRT.eisEmbedding (conjO x) =
      star (ConcreteTraceCRT.eisEmbedding x) := by
  let ι := ConcreteTraceCRT.eisEmbedding
  let z := ι omega
  have hz3 : z ^ 3 = 1 := by
    change ι omega ^ 3 = 1
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
  have hhom : ι.comp conjO.toRingHom = (starRingEnd ℂ).comp ι := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ι (conjO omega) = star (ι omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx
end OAI.ActualEisensteinCubic
