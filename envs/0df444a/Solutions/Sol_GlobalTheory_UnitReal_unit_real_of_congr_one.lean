-- Prove2me | solution 1 for GlobalTheory.UnitReal.unit_real_of_congr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:17.164316+00:00
-- url     : https://prove2.me/submissions/c5dac685-6cc3-4722-8096-b2c093600eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitRealOfCongrOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.UnitReal
namespace GlobalTheory.UnitReal
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime →
    ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E) := by
  intro E _ _ _ q hq hqt u hu φ
  set I : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with hI
  set c : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv with hc
  set v : (𝓞 E)ˣ := IsCMField.unitsComplexConj E u with hv
  have hvc : (v : 𝓞 E) = c u := rfl
  have hv1 : (v : 𝓞 E) - 1 ∈ I := by
    rw [hI, Ideal.mem_span_singleton] at hu ⊢
    obtain ⟨y, hy⟩ := hu
    refine ⟨c y, ?_⟩
    rw [hvc, ← map_one c, ← map_sub, hy, map_mul, map_natCast]
  set ζ : (𝓞 E)ˣ := (IsCMField.unitsMulComplexConjInv E u : (𝓞 E)ˣ) with hζ
  have hζv : ζ * v = u := by rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
  have hζ1 : Ideal.Quotient.mk I (ζ : 𝓞 E) = 1 := by
    have a1 : Ideal.Quotient.mk I (u : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hu
    have a2 : Ideal.Quotient.mk I (v : 𝓞 E) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hv1
    have := congrArg (fun x : (𝓞 E)ˣ => Ideal.Quotient.mk I (x : 𝓞 E)) hζv
    simp only [Units.val_mul, map_mul, a1, a2, mul_one] at this
    exact this
  have ht : ζ ^ Nat.card (Units.torsion E) = 1 := by
    have h4 : (IsCMField.unitsMulComplexConjInv E u) ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
    have := congrArg Subtype.val h4
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    exact this
  have hζeq : ζ = 1 := by
    by_contra hne
    have hne' : (ζ : 𝓞 E) - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; exact hne (Units.ext h)
    have hsum : ∑ j ∈ Finset.range (Nat.card (Units.torsion E)), (ζ : 𝓞 E) ^ j = 0 := by
      have := mul_geom_sum ((ζ : 𝓞 E)) (Nat.card (Units.torsion E))
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_left hne'
    have hmod := congrArg (Ideal.Quotient.mk I) hsum
    simp only [map_sum, map_pow, hζ1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, map_zero] at hmod
    have hmem : ((Nat.card (Units.torsion E) : ℕ) : 𝓞 E) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hmod
    rw [hI, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hn := congrArg (Algebra.norm ℤ) hy
    rw [map_mul] at hn
    have e1 : ∀ n : ℕ, Algebra.norm ℤ ((n : 𝓞 E)) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      intro n
      rw [← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
    rw [e1, e1] at hn
    have hd : 0 < Module.finrank ℤ (𝓞 E) := by
      rw [RingOfIntegers.rank]; exact Module.finrank_pos
    have hdvd : (q : ℤ) ∣ (Nat.card (Units.torsion E) : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [hn]; exact Dvd.dvd.mul_right (dvd_pow_self _ hd.ne') _
    have hdvd' : q ∣ Nat.card (Units.torsion E) ^ Module.finrank ℤ (𝓞 E) := by exact_mod_cast hdvd
    exact hqt (hq.dvd_of_dvd_pow hdvd')
  have huv : (v : 𝓞 E) = u := by rw [← hζv, hζeq, one_mul]
  have hE : IsCMField.complexConj E ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huv
    exact this
  rw [← IsCMField.complexEmbedding_complexConj, hE]
end GlobalTheory.UnitReal
