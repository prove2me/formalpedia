-- Prove2me | solution 1 for GlobalTheory.exists_fixed_dvd_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:02.657517+00:00
-- url     : https://prove2.me/submissions/e1c6324f-5971-4701-be78-4f0b22764b62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRootOfUnityFixedDvdWeilGroupDegree
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_Gal_not_valuation_lt_one_of_isPlaceOver
import Theorems.Thm_ReciprocityTheory_Gal_valuation_eq_one_of_pow_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply


section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
namespace GlobalTheory
open NumberField IsDedekindDomain Polynomial in
private theorem dvd_of_primitiveRoot_pow_pow_eq_self {Ω : Type} [Field Ω] {q k m : ℕ} (hq : 1 < q)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (q ^ k - 1)) (hpos : 0 < q ^ k - 1) (hm : ζ ^ q ^ m = ζ) :
    k ∣ m := by
  have hz : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have h1 : q ^ k - 1 ∣ q ^ m - 1 := by
    apply hζ.dvd_of_pow_eq_one
    have h0 : ζ ^ (q ^ m - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), one_mul]
      exact hm
    exact mul_right_cancel₀ hz h0
  have h2 := Nat.pow_sub_one_gcd_pow_sub_one q k m
  rw [Nat.gcd_eq_left h1] at h2
  have h3 : q ^ k = q ^ Nat.gcd k m := by
    have := Nat.one_le_pow (Nat.gcd k m) q (by omega)
    have := Nat.one_le_pow k q (by omega)
    omega
  have h4 := Nat.pow_right_injective hq h3
  rw [h4]
  exact Nat.gcd_dvd_right k m
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory
open NumberField IsDedekindDomain Polynomial
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (k : ℕ), 0 < k →
    ∃ ζ : Ω, ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ζ = ζ → (k : ℤ) ∣ _root_.GlobalTheory.WeilDeligne.deg σ := by
  intro E Ω _ _ _ _ _ A w h k hk
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hq1 : 1 < _root_.Formalism.ConjugateSelfDual.normV w := _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  have hpos : 0 < _root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hk.ne' hq1)
  haveI : NeZero ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap E Ω)]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hpos.ne')⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1)
  have hvN : ¬ A.valuation ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : Ω) < 1 := by
    have hmem : ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
      intro hN
      have h1 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
      have h2 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k ∈ w.asIdeal := Ideal.pow_mem_of_mem _ h1 _ hk
      have h3 : ((_root_.Formalism.ConjugateSelfDual.normV w : ℕ) : 𝓞 E) ^ k - ((_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1 : ℕ) : 𝓞 E) = 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
        ring
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h3 ▸ sub_mem h2 hN))
    simpa using _root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hmem h 1
  have hζv : A.valuation ζ ≤ 1 := le_of_eq (_root_.ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hpos.ne' hζ.pow_eq_one)
  have hroot : ∀ m : ℕ, (ζ ^ _root_.Formalism.ConjugateSelfDual.normV w ^ m) ^ (_root_.Formalism.ConjugateSelfDual.normV w ^ k - 1) = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ, fun σ hσ => ?_⟩
  rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hd
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := m) (b := 0)
      (by rw [hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN hζ.pow_eq_one (hroot m) hv
    rw [hm]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq.symm)
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hd.le)
    have hact := _root_.GlobalTheory.WeilDeligne.actsAs_of_deg (σ := σ) (a := 0) (b := m)
      (by rw [← hm]; simp)
    have hv := hact.2 ζ hζv
    rw [pow_zero, pow_one, hσ] at hv
    have heq := _root_.ReciprocityTheory.Gal.eq_of_pow_eq_one A hvN (hroot m) hζ.pow_eq_one hv
    rw [← neg_neg (_root_.GlobalTheory.WeilDeligne.deg σ), hm, dvd_neg]
    exact Int.natCast_dvd_natCast.2 (dvd_of_primitiveRoot_pow_pow_eq_self hq1 hζ hpos heq)
end _root_.GlobalTheory
end GlobalTheory
