-- Prove2me | solution 1 for GlobalTheory.InertiaAlmostAll.finite_moves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:03:03.398956+00:00
-- url     : https://prove2.me/submissions/cb9e55a6-d50a-4ca3-837a-f67d25f29228

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
import Theorems.Thm_GlobalTheory_InertiaAlmostAll_val_le_one_of_isIntegral
import Theorems.Thm_GlobalTheory_InertiaAlmostAll_exists_int_mul
import Theorems.Thm_GlobalTheory_InertiaAlmostAll_finite_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll
namespace GlobalTheory.InertiaAlmostAll
theorem _root_.solution (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (x : Ω) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ∃ τ ∈ Ine (F := F) B, τ x ≠ x}.Finite := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨c₀, hc₀, hx⟩ := exists_int_mul F x
  set a : Ω := (c₀ : Ω) * x with ha
  choose c hc hci using fun β : Ω => exists_int_mul F (β - a)⁻¹
  have hfin : ((minpoly F a).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  refine (hfin.biUnion (t := fun β => {v : HeightOneSpectrum (𝓞 F) | (c β : 𝓞 F) ∈ v.asIdeal})
    fun β _ => finite_mem F (hc β)).subset ?_
  rintro v ⟨B, hB, τ, hτ, hne⟩
  have hne' : τ a - a ≠ 0 := by
    rw [ha, map_mul, map_intCast, ← mul_sub]
    exact mul_ne_zero (by exact_mod_cast hc₀) (sub_ne_zero.mpr hne)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨τ a, ?_, ?_⟩
  · rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [← hB]
    have h1 := hτ.2 a (val_le_one_of_isIntegral B hx)
    have h2 := val_le_one_of_isIntegral B (hci (τ a))
    have e : algebraMap F Ω (((c (τ a) : ℤ) : 𝓞 F) : F)
        = ((c (τ a) : Ω) * (τ a - a)⁻¹) * (τ a - a) := by
      rw [inv_mul_cancel_right₀ hne']
      simp
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h2 zero_le h1
end GlobalTheory.InertiaAlmostAll
