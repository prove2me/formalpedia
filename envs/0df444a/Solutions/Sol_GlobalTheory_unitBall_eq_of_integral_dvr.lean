-- Prove2me | solution 1 for GlobalTheory.unitBall_eq_of_integral_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:39.788484+00:00
-- url     : https://prove2.me/submissions/e05b3509-58e5-4bed-b5df-6f404f8a0bb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallEqOfIntegralDvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [IsLocalHom (algebraMap V W)]
    (hinj : Function.Injective (algebraMap V W))
    (κ : FractionRing V →+* PadicAlgCl p) (κ' : FractionRing W →+* PadicAlgCl p)
    (hc : ∀ v : V, κ' (algebraMap W (FractionRing W) (algebraMap V W v)) =
      κ (algebraMap V (FractionRing V) v))
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  classical
  have hW1 : ∀ w : W, ‖κ' (algebraMap W (FractionRing W) w)‖ ≤ 1 := by
    intro w
    let vP : Valuation (PadicAlgCl p) NNReal := Valued.v
    have hmem : ∀ a : V, κ (algebraMap V (FractionRing V) a) ∈ vP.integer := by
      intro a
      rw [Valuation.mem_integer_iff]
      show ‖κ (algebraMap V (FractionRing V) a)‖₊ ≤ 1
      exact NNReal.coe_le_coe.1 (by simpa using (hV _).2 ⟨a, rfl⟩)
    let ψ : V →+* vP.integer :=
      (κ.comp (algebraMap V (FractionRing V))).codRestrict vP.integer hmem
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := V) w
    have hint : IsIntegral vP.integer (κ' (algebraMap W (FractionRing W) w)) := by
      refine ⟨q.map ψ, hqm.map ψ, ?_⟩
      have hcomp : (algebraMap vP.integer (PadicAlgCl p)).comp ψ =
          (κ'.comp (algebraMap W (FractionRing W))).comp (algebraMap V W) :=
        RingHom.ext fun a => (hc a).symm
      rw [Polynomial.eval₂_map, hcomp]
      have h0 : (κ'.comp (algebraMap W (FractionRing W))) (q.eval₂ (algebraMap V W) w) = 0 := by
        rw [hq, map_zero]
      exact (Polynomial.hom_eval₂ q (algebraMap V W) _ w).symm.trans h0
    have h1 := (Valuation.integer.integers vP).mem_of_integral hint
    rw [Valuation.mem_integer_iff] at h1
    have h2 : ‖κ' (algebraMap W (FractionRing W) w)‖₊ ≤ 1 := h1
    have h3 : ((‖κ' (algebraMap W (FractionRing W) w)‖₊ : NNReal) : ℝ) ≤ 1 := by exact_mod_cast h2
    simpa using h3
  have hunit : ∀ u : Wˣ, ‖κ' (algebraMap W (FractionRing W) u)‖ = 1 := by
    intro u
    have hm : ‖κ' (algebraMap W (FractionRing W) u)‖ *
        ‖κ' (algebraMap W (FractionRing W) ↑u⁻¹)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have ha := hW1 u
    have hb := hW1 ↑u⁻¹
    refine le_antisymm ha ?_
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (κ' (algebraMap W (FractionRing W) u)))]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπK0 : algebraMap V (FractionRing V) π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm)
  have hπ1 : ‖κ (algebraMap V (FractionRing V) π)‖ < 1 := by
    refine lt_of_le_of_ne ((hV _).2 ⟨π, rfl⟩) fun h => hπ.not_isUnit ?_
    have hinv : ‖κ (algebraMap V (FractionRing V) π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hinv
    refine isUnit_iff_exists_inv.2 ⟨a, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [map_mul, ha, mul_inv_cancel₀ hπK0, map_one]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hϖ1 : ‖κ' (algebraMap W (FractionRing W) ϖ)‖ < 1 := by
    have hπW0 : algebraMap V W π ≠ 0 := fun h =>
      hπ.ne_zero (hinj (h.trans (map_zero _).symm))
    obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπW0 hϖ
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at he
      exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap V W) π (he ▸ u.isUnit))
    have hnorm : ‖κ' (algebraMap W (FractionRing W) ϖ)‖ ^ e < 1 := by
      have h := congrArg norm (hc π)
      rw [he, map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, hunit, one_mul] at h
      rw [← h] at hπ1
      exact hπ1
    by_contra hge
    exact absurd hnorm (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))
  intro x
  constructor
  · intro hx
    by_contra hxW
    rcases ValuationRing.isInteger_or_isInteger W x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact hxW ⟨a, ha⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxW ⟨0, map_zero _⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hx0 (inv_eq_zero.1 ha.symm)
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hn
      apply hxW
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap W (FractionRing W) ↑u * algebraMap W (FractionRing W) ↑u⁻¹ = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [eq_inv_of_mul_eq_one_right h1, ← hn, ha, inv_inv]
    have hsmall : ‖κ' x⁻¹‖ < 1 := by
      rw [← ha, hn, map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow, hunit, one_mul]
      exact pow_lt_one₀ (norm_nonneg _) hϖ1 hn0
    have hprod : ‖κ' x‖ * ‖κ' x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h0 := norm_nonneg (κ' x⁻¹)
    nlinarith
  · rintro ⟨w, rfl⟩
    exact hW1 w
end GlobalTheory
