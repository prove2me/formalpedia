-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelClose.kerClose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:36.653881+00:00
-- url     : https://prove2.me/submissions/8c621528-5d42-407b-b786-bb80e4e2562d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KerClose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelClose
namespace GlobalTheory.CompanionTheory.KernelClose
theorem _root_.solution : KerClose := by
  intro X Ω x y hΩ
  have hC : IsCompact ((fun o : X.G => x * o * y⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro φ hφ γ hγ
    have hmem : x⁻¹ * (γ : X.G) * y ∈ Ω := hφ hγ
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨_, hmem, by group⟩
  have hker : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      ker X.Γ φ x y = ∑ γ ∈ hfin.toFinset, φ (x⁻¹ * (γ : X.G) * y) := fun φ hφ =>
    finsum_eq_sum_of_support_subset _ (hsupp φ hφ)
  refine ⟨(hfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro φ φ' ε hφ hφ' hε
  rw [hker φ hφ, hker φ' hφ', ← Finset.sum_sub_distrib]
  calc ‖∑ γ ∈ hfin.toFinset, (φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y))‖
      ≤ ∑ γ ∈ hfin.toFinset, ‖φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y)‖ :=
        norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε := Finset.sum_le_card_nsmul _ _ _ fun γ _ => hε _
    _ = (hfin.toFinset.card : ℝ) * ε := nsmul_eq_mul _ _
end GlobalTheory.CompanionTheory.KernelClose
