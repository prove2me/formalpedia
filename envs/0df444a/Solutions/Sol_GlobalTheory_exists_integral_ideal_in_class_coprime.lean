-- Prove2me | solution 1 for GlobalTheory.exists_integral_ideal_in_class_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:20.740916+00:00
-- url     : https://prove2.me/submissions/ebe7cc96-ebaf-44fc-b16b-72d9c52a7be5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)), m ≠ ⊥ → ∀ c : ClassGroup (𝓞 K), ∃ b : (Ideal (𝓞 K))⁰, ClassGroup.mk0 b = c ∧ (b : Ideal (𝓞 K)) ⊔ m = ⊤ := by
  intro K _ _ m hm c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (Ideal.mul_le_inf.trans inf_le_left : (J : Ideal (𝓞 K)) * m ≤ J) (mul_ne_zero hJ0 hm)
  have haJ : a ∈ (J : Ideal (𝓞 K)) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨L, hL⟩ : (J : Ideal (𝓞 K)) ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)
  have hcop : m ⊔ L = ⊤ := by
    have h1 : (J : Ideal (𝓞 K)) * (m ⊔ L) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hL, ha, Ideal.mul_top]
    exact mul_left_cancel₀ hJ0 h1
  by_cases hL0 : L = 0
  · have hmt : m = ⊤ := by simpa [hL0] using hcop
    obtain ⟨b, hb⟩ := ClassGroup.mk0_surjective c
    exact ⟨b, hb, by simp [hmt]⟩
  · refine ⟨⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩, ?_, by rw [sup_comm]; exact hcop⟩
    have hprod : ClassGroup.mk0 J * ClassGroup.mk0 ⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩ = 1 := by
      rw [← map_mul, ClassGroup.mk0_eq_one_iff]
      change ((J : Ideal (𝓞 K)) * L).IsPrincipal
      rw [← hL]
      exact ⟨⟨a, rfl⟩⟩
    rw [hJ] at hprod
    exact (inv_mul_eq_one.mp hprod).symm
end GlobalTheory
