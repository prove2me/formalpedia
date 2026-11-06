-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveGamma1_gammaMinus1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:48.349517+00:00
-- url     : https://prove2.me/submissions/0501b621-1b0e-40f6-a4a5-19f3f1083e55

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_conjO
import Theorems.Thm_OAI_ActualEisensteinCubic_primary_generator_mul_conj_eq_card
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_order
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_primitive
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


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
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
end
section
open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT
end
section
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
end
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
end ActualEisensteinCubic
namespace ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT
end ConcreteBreveE
namespace FixedRayActiveSet
open scoped BigOperators
end FixedRayActiveSet
namespace CubeInversion
end CubeInversion
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
private theorem canonicalSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (canonicalSextic P hgood) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  change orderOf (Φ (sexticChar P hgood)) = 6
  rw [orderOf_injective Φ hΦ, sexticChar_order P hgood hchar]
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
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
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGammaMinus1 P hgood p hP hp =
      canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)) := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have horder : orderOf χ = 6 :=
    canonicalSextic_order_six (Ideal.span {p}) hgood hchar
  have hχ5 : χ ^ 5 = χ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ * χ ^ 5 = χ ^ 6 := by group
      _ = 1 := hχ6
  have hprod := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ
  rw [horder, show 6 - 1 = 5 by decide, hχ5] at hprod
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  change (gaussSum χ ψ / s) * (gaussSum χ⁻¹ ψ / s) = χ (-1)
  field_simp
  rw [hs]
  simpa only [mul_comm] using hprod
end OAI.ActualEisensteinCubic
