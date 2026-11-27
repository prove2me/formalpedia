-- Prove2me | solution 1 for NormOnePowProof.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:50:41.788943+00:00
-- url     : https://prove2.me/submissions/c84ac68f-3838-4e82-8fc1-910b21921598

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
import Theorems.Thm_NormOnePowProof_conj_pow
import Theorems.Thm_NormOnePowProof_conj_span
import Theorems.Thm_NormOnePowProof_pow_principal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]
namespace NormOnePowProof
theorem _root_.solution : PI.NormOnePow := by
  intro E _ _ c hc 𝔞 𝔟 hb hab
  obtain ⟨h, a, hpos, ha⟩ := pow_principal hab
  have hbh : 𝔟 ^ h = Submodule.span (𝓞 E) {c a} := by
    apply conj_span c hc a
    intro x
    rw [← ha]
    exact conj_pow c hc hb h x
  have hprod : Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {c a} = 1 := by
    rw [← ha, ← hbh, ← mul_pow, hab, one_pow]
  have hone : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul] at hprod
    rw [← hprod, Submodule.mem_bot] at hone
    exact one_ne_zero hone
  have hca0 : c a ≠ 0 := (map_ne_zero c).2 ha0
  have h1 : Submodule.span (𝓞 E) {c a} * Submodule.span (𝓞 E) {(c a)⁻¹} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hca0,
      ← Submodule.one_eq_span]
  have hinv : Submodule.span (𝓞 E) {(c a)⁻¹} = Submodule.span (𝓞 E) {a} := by
    calc Submodule.span (𝓞 E) {(c a)⁻¹}
        = (Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {c a}) *
            Submodule.span (𝓞 E) {(c a)⁻¹} := by rw [hprod, one_mul]
      _ = Submodule.span (𝓞 E) {a} *
            (Submodule.span (𝓞 E) {c a} * Submodule.span (𝓞 E) {(c a)⁻¹}) := mul_assoc _ _ _
      _ = Submodule.span (𝓞 E) {a} := by rw [h1, mul_one]
  refine ⟨2 * h, a * (c a)⁻¹, by omega, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hc]
    field_simp
  · rw [two_mul, pow_add, ha]
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, hinv]
end NormOnePowProof
