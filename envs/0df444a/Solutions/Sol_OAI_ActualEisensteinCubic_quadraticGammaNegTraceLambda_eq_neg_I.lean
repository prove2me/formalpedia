-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaNegTraceLambda_eq_neg_I
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:36.07305+00:00
-- url     : https://prove2.me/submissions/31b49d3e-4e7b-4d17-beee-816c4471cbee

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Theorems.Thm_OAI_TraceLambdaPhase_breveE_traceLambda_square
import Theorems.Thm_OAI_ActualEisensteinCubic_traceLambda_quotient_card
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_traceLambda
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
namespace OAI.ActualEisensteinCubic
theorem _root_.solution :
    quadraticGammaNegTraceLambda = -Complex.I := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hspan : Ideal.span {c} = Ideal.span {traceLambda} := by
    change Ideal.span {-traceLambda} = Ideal.span {traceLambda}
    rw [show -traceLambda = (-1 : O) * traceLambda by ring]
    exact Ideal.span_singleton_mul_left_unit isUnit_neg_one traceLambda
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    have hcardNat : Nat.card (O ⧸ Ideal.span {c}) = 3 := by
      rw [hspan]
      exact traceLambda_quotient_card
    simpa only [Nat.card_eq_fintype_card] using hcardNat
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3⁻¹ := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3⁻¹
    rw [map_one, show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda]]
    have harg : (1 : ℂ) / (-eisLam * eisLam) =
        -((1 : ℂ) / (eisLam * eisLam)) := by ring
    rw [harg, ShortDraftTrace.breveE.map_neg_eq_inv,
      breveE_traceLambda_square]
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) =
      1 + 2 * omega3⁻¹ := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3⁻¹
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hωcube : omega3 ^ 3 = 1 := by
    linear_combination (omega3 - 1) * omega3_sq
  have hωinv : omega3⁻¹ = omega3 ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hωcube
  have hsumval : 1 + 2 * omega3⁻¹ = -eisLam := by
    rw [hωinv]
    dsimp [eisLam]
    linear_combination 2 * omega3_sq
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda], norm_neg, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaNegTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = -Complex.I
  rw [hsum, hsumval, hnorm, hLam]
  field_simp
end OAI.ActualEisensteinCubic
