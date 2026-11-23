-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.sub_conj_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:11.887871+00:00
-- url     : https://prove2.me/submissions/3dfe1bab-3490-4b22-b259-65a16bb29c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
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
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
local notation "cj" => IsCMField.ringOfIntegersComplexConj E
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution {z : 𝓞 E} (hz : IsPrimitiveRoot z 21) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) : z - cj z ∉ P := by
  intro h
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hpow : z ^ 21 = 1 := hz.pow_eq_one
  have hc : cj z * z = 1 := by
    apply RingOfIntegers.ext
    apply σ.injective
    have hn : ‖σ (z : E)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := 21) (by
      rw [← map_pow]
      have : (z : E) ^ 21 = 1 := by exact_mod_cast congrArg (algebraMap (𝓞 E) E) hpow
      rw [this, map_one]) (by norm_num)
    change σ (IsCMField.complexConj E (z : E) * (z : E)) = σ 1
    rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.conj_mul', hn]; simp
  set q := Ideal.Quotient.mk P
  have h1 : q z = q (cj z) := Ideal.Quotient.eq.2 h
  have h2 : q z ^ 2 = 1 := by rw [sq]; nth_rw 1 [h1]; rw [← map_mul, hc, map_one]
  have h3 : q z ^ 21 = 1 := by rw [← map_pow, hpow, map_one]
  have h4 : q z = 1 := by
    have : q z ^ 21 = (q z ^ 2) ^ 10 * q z := by ring
    rw [this, h2] at h3; simpa using h3
  have a3 := congrArg q ((hz.pow (by norm_num) (show 21 = 7 * 3 by norm_num)).geom_sum_eq_zero (by norm_num))
  have a7 := congrArg q ((hz.pow (by norm_num) (show 21 = 3 * 7 by norm_num)).geom_sum_eq_zero (by norm_num))
  simp [h4] at a3 a7
  have : (1 : 𝓞 E ⧸ P) = 0 := by linear_combination a7 - 2 * a3
  exact hP (Ideal.Quotient.zero_eq_one_iff.1 this.symm)
end GlobalTheory.CMVal.InhabK
