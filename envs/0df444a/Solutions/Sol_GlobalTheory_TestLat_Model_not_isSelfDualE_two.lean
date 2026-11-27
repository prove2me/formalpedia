-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.not_isSelfDualE_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:02.490501+00:00
-- url     : https://prove2.me/submissions/23de546f-9f76-4539-8903-f9cfaad01d6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_GlobalTheory_TestLat_Model_map_mem_range
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
namespace GlobalTheory.TestLat.Model
theorem _root_.solution (σ : K →+* K) :
    ¬ IsSelfDualE σ (1 : Matrix (Fin 1) (Fin 1) K) (Submodule.span (𝓞 K) {fun _ => (2 : K)}) := by
  intro h
  have h1 : (fun _ => (1 : K)) ∈ (Submodule.span (𝓞 K) {fun _ : Fin 1 => (2 : K)}) := by
    rw [h.2]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : Formalism.UG.hform σ (1 : Matrix (Fin 1) (Fin 1) K) (a • fun _ => (2 : K)) (fun _ => 1) =
        σ (algebraMap (𝓞 K) K (a * 2)) := by
      simp [Formalism.UG.hform, Algebra.smul_def, map_ofNat]
    rw [this]
    exact map_mem_range σ ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  have h2 : algebraMap (𝓞 K) K a * 2 = 1 := by simpa [Algebra.smul_def] using congrFun ha 0
  have h3 : IsIntegral ℤ (algebraMap ℚ K 2⁻¹) := by
    have : algebraMap ℚ K 2⁻¹ = algebraMap (𝓞 K) K a := by
      rw [map_inv₀, map_ofNat]
      exact (eq_inv_of_mul_eq_one_left h2).symm
    rw [this]
    exact RingOfIntegers.isIntegral_coe a
  rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at h3
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (z : ℚ) * 2 = 1 := by
    have : (z : ℚ) = 2⁻¹ := hz
    rw [this]; norm_num
  have h5 : z * 2 = 1 := by exact_mod_cast h4
  omega
end GlobalTheory.TestLat.Model
