-- Prove2me | solution 1 for GlobalTheory.Nef.exists_unique_place_ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:49.738141+00:00
-- url     : https://prove2.me/submissions/e7830f76-f9b6-44b8-9b3e-6a6805a81b99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
import Theorems.Thm_GlobalTheory_Nef_place_aeval_eq_pow
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef
open Polynomial
namespace GlobalTheory.Nef
theorem _root_.solution (k L : Type) [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) (htop : k⟮x⟯ = ⊤) :
    ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  have hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s := fun y =>
    (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h => hx ⟨p, hp, h⟩
  have hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ) := by
    intro u hu
    have hx0 : u.1 x ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h; apply hne X X_ne_zero; simpa using h
    set b := WithZero.log (u.1 x) with hb
    have hub : u.1 x = WithZero.exp b := (WithZero.exp_log hx0).symm
    have hb0 : b < 0 := by
      have : WithZero.exp b < WithZero.exp (0 : ℤ) := by rw [← hub, WithZero.exp_zero]; exact hu
      exact WithZero.exp_lt_exp.1 this
    obtain ⟨y, hy⟩ := u.2.1 (WithZero.exp (-1 : ℤ))
    obtain ⟨r, s, rfl⟩ := hmem y
    have hr : r ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    have hs : s ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    rw [map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj] at hy
    have hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1 := by
      rw [← hy]; simp only [nsmul_eq_mul]; ring
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h
    · omega
    · rw [hub, h]
  have hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 →
      u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0 := fun u hu p hp => by
    rw [place_aeval_eq_pow x u hu p hp, hval u hu]
  let e : RatFunc k ≃ₐ[k] L := ((RatFunc.algEquivOfTranscendental x hx).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv
  have heX : e RatFunc.X = x := by simp [e]
  have heXs : e.symm x = RatFunc.X := by rw [← heX, AlgEquiv.symm_apply_apply]
  let V := (Polynomial.idealX k).valuation (RatFunc k)
  let v0 : Valuation L (WithZero (Multiplicative ℤ)) := V.comap (e.symm : L →+* RatFunc k)
  have hv0 : ∀ y, v0 y = V (e.symm y) := fun y => rfl
  have hVX : V RatFunc.X = WithZero.exp (-1 : ℤ) := by
    rw [← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)
  let v : Place k L := ⟨v0, fun γ => by
      obtain ⟨r, hr⟩ := RatFunc.valuation_surjective (K := k) γ
      exact ⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,
    fun c hc => by
      rw [hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem'
      rw [Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff] at hmem'
      simp [hc] at hmem'⟩
  have hvx : v.1 x = WithZero.exp (-1 : ℤ) := by
    show v0 x = _; rw [hv0, heXs, hVX]
  refine ⟨v, by simp [ord, hvx], fun w hw => ?_⟩
  have hvl : v.1 x < 1 := by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero
  apply Subtype.ext
  ext y
  obtain ⟨r, s, rfl⟩ := hmem y
  rw [map_div₀, map_div₀]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]
end GlobalTheory.Nef
