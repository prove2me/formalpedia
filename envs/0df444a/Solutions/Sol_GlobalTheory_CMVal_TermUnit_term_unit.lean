-- Prove2me | solution 1 for GlobalTheory.CMVal.TermUnit.term_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:14.756617+00:00
-- url     : https://prove2.me/submissions/543723de-e4ad-4abd-9f36-5cab8cd19fe7

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_norm_sq
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_cpow
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.CMVal.TermUnit
theorem _root_.solution [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by
  set x := algebraMap (OF E) E (u : OF E) with hxdef
  have hxmem : x ∈ maximalRealSubfield E := by
    rw [hxdef, IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
    exact (algebraMap (OF E) (maximalRealSubfield E) u).2
  have hreal : ∀ i, starRingEnd ℂ (φ i x) = φ i x := fun i => by
    rw [starRingEnd_apply]
    exact (mem_maximalRealSubfield_iff x).mp hxmem (φ i)
  have hx0 : x ≠ 0 := (u.isUnit.map (algebraMap (OF E) E)).ne_zero
  have hN : |(Algebra.norm ℚ x : ℝ)| = 1 := by
    have hv := NumberField.isUnit_iff_norm.mp (u.isUnit.map (algebraMap (OF E) (𝓞 E)))
    have hc : ((algebraMap (OF E) (𝓞 E) u : 𝓞 E) : E) = x :=
      (IsScalarTower.algebraMap_apply (OF E) (𝓞 E) E u).symm
    rw [RingOfIntegers.coe_norm, hc] at hv
    exact_mod_cast hv
  have hprod : ∏ i, ‖φ i x‖ = 1 := by
    have hsq : (∏ i, ‖φ i x‖) ^ 2 = 1 := by rw [← Finset.prod_pow, prod_norm_sq h x, hN]
    exact (pow_eq_one_iff_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) two_ne_zero).mp hsq
  have hfac : ∀ i, (φ i x)⁻¹ ^ (2 * s + κ i) * starRingEnd ℂ (φ i x) ^ κ i * ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * ((s : ℂ) + σ)) := fun i => by
    have hr : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx0
    have ha : ((‖φ i x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
    have hsq : ((‖φ i x‖ : ℝ) : ℂ) ^ 2 = φ i x ^ 2 := by
      have hm := Complex.mul_conj (φ i x)
      rw [hreal, Complex.normSq_eq_norm_sq] at hm
      rw [sq (φ i x), hm]
      push_cast
      ring
    rw [show -2 * ((s : ℂ) + σ) = -((2 * s : ℕ) : ℂ) + -2 * σ by push_cast; ring,
      Complex.cpow_add _ _ ha, Complex.cpow_neg, Complex.cpow_natCast, hreal]
    congr 1
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hr, one_pow, mul_one, inv_pow, pow_mul, pow_mul, hsq]
  simp only [term]
  rw [Finset.prod_congr rfl fun i _ => hfac i, prod_cpow _ _ (fun i => norm_nonneg _), hprod]
  simp
end GlobalTheory.CMVal.TermUnit
