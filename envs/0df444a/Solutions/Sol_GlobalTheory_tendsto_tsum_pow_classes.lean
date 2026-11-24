-- Prove2me | solution 1 for GlobalTheory.tendsto_tsum_pow_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:43:14.362807+00:00
-- url     : https://prove2.me/submissions/f94588a1-4fac-4b17-b25a-6aa831b6e925

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_pow_nsmul
import Theorems.Thm_GlobalTheory_tendsto_tsum_zero_of_eventually_notMem_range
import Theorems.Thm_GlobalTheory_mem_class_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n →
      ∀ (σ : X → K), Filter.Tendsto σ Filter.cofinite (nhds 0) → ∀ α : ℕ → X,
      (∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) →
      (∀ χ : X, (∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds (σ χ))) ∧
      ((¬ ∃ χ : X, ∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds 0)) := by
  classical
  intro K X _ _ _ _ _ _ n hn σ hσ α hα
  have hinj : ∀ j, Function.Injective (fun μ : X => α j + n ^ j • μ) := by
    intro j μ ν h
    simp only [add_right_inj] at h
    have hne : ((n ^ j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero j (by omega : n ≠ 0)
    have h' : ((n ^ j : ℕ) : ℤ) • μ = ((n ^ j : ℕ) : ℤ) • ν := by
      rw [natCast_zsmul, natCast_zsmul]
      exact h
    exact smul_right_injective X hne h'
  have hsum : ∀ τ : X → K, Tendsto τ cofinite (𝓝 0) → ∀ j, Summable (fun μ => τ (α j + n ^ j • μ)) :=
    fun τ hτ j => NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hτ.comp (hinj j).tendsto_cofinite)
  have hfar : ∀ z w : X, z ≠ w → ∀ᶠ j in atTop, ¬ ∃ μ, z = w + n ^ j • μ := by
    intro z w hzw
    by_contra h
    rw [Filter.not_eventually] at h
    simp only [not_not] at h
    apply hzw
    have h0 : z - w = 0 := by
      refine eq_zero_of_forall_pow_nsmul hn (fun j => ?_)
      obtain ⟨i, ⟨μ, hμ⟩, hji⟩ := (h.and_eventually (eventually_ge_atTop j)).exists
      refine ⟨n ^ (i - j) • μ, ?_⟩
      rw [hμ, add_sub_cancel_left, ← mul_smul, ← pow_add, Nat.add_sub_cancel' hji]
    exact sub_eq_zero.mp h0
  constructor
  · intro χ hχ
    let τ := Function.update σ χ 0
    have hτ : Tendsto τ cofinite (𝓝 0) := by
      apply hσ.congr'
      filter_upwards [(Set.finite_singleton χ).compl_mem_cofinite] with z hz
      simp [τ, Set.mem_compl_singleton_iff.mp hz]
    have h2 := tendsto_tsum_zero_of_eventually_notMem_range τ hτ (fun j μ => α j + n ^ j • μ) (by
      intro z hz
      have hzχ : z ≠ χ := by
        rintro rfl
        simp [τ] at hz
      filter_upwards [hfar z χ hzχ] with j hj μ hμ
      apply hj
      obtain ⟨ν, hν⟩ := hχ j
      have hμ' : z = α j + n ^ j • μ := hμ.symm
      refine ⟨μ - ν, ?_⟩
      rw [hμ', hν, smul_sub]
      abel)
    have heq : ∀ j, ∑' μ, σ (α j + n ^ j • μ) = σ χ + ∑' μ, τ (α j + n ^ j • μ) := by
      intro j
      obtain ⟨μj, hμj⟩ := hχ j
      rw [(hsum σ hσ j).tsum_eq_add_tsum_ite μj]
      congr 1
      · rw [hμj]
      · refine tsum_congr fun μ => ?_
        by_cases h : μ = μj
        · subst h
          simp [τ, ← hμj]
        · have hne : α j + n ^ j • μ ≠ χ := fun h' => h (hinj j (h'.trans hμj))
          simp [τ, h, hne]
    have h3 := tendsto_const_nhds (x := σ χ) |>.add h2
    rw [add_zero] at h3
    exact h3.congr (fun j => (heq j).symm)
  · intro hno
    apply tendsto_tsum_zero_of_eventually_notMem_range σ hσ (fun j μ => α j + n ^ j • μ)
    intro z _
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬ ∃ μ, z = α j0 + n ^ j0 • μ := by
      by_contra h
      exact hno ⟨z, fun j => by
        by_contra h'
        exact h ⟨j, h'⟩⟩
    filter_upwards [eventually_ge_atTop j0] with j hj μ hμ
    exact hj0 (mem_class_of_le hα hj ⟨μ, hμ.symm⟩)
end GlobalTheory
