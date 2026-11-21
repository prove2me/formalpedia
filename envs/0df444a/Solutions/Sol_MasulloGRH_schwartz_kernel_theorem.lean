-- Prove2me | solution 1 for MasulloGRH.schwartz_kernel_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:13:58.189174+00:00
-- url     : https://prove2.me/submissions/caf8e0ce-2cd3-4120-b606-3f012b073407

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_continuous_bilinear_seminorm_bound
import Theorems.Thm_MasulloGRH_nuclear_bilinear_series
import Theorems.Thm_MasulloGRH_equicontinuous_of_le_continuous_seminorm
import Theorems.Thm_MasulloGRH_tendstoUniformlyOn_bilinear_series

set_option autoImplicit false

open MasulloGRH

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsNuclear E) (hF : IsHLCS F)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : Continuous (fun p : E × F => B p.1 p.2)) :
    ∃ (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → StrongDual ℂ F) (c : ℕ → ℂ),
      Equicontinuous (fun m => (φ m : E → ℂ)) ∧ Equicontinuous (fun m => (ψ m : F → ℂ)) ∧
      Summable (fun m => ‖c m‖) ∧
      ∀ (S : Set E) (T : Set F), Bornology.IsVonNBounded ℂ S → Bornology.IsVonNBounded ℂ T →
        TendstoUniformlyOn
          (fun (k : ℕ) (p : E × F) => ∑ m ∈ Finset.range k, c m * φ m p.1 * ψ m p.2)
          (fun p : E × F => B p.1 p.2) Filter.atTop (S ×ˢ T) := by
  obtain ⟨p, r, hp, hr, hpr⟩ := continuous_bilinear_seminorm_bound E F hE.1.1 hF.1 B hB
  obtain ⟨φ, ψ, c, hφ, hψr, hc, hsum⟩ := nuclear_bilinear_series E F hE p hp r B hpr
  obtain ⟨ψ', hψ'eq, hψ'⟩ := equicontinuous_of_le_continuous_seminorm F hF.1 r hr ψ hψr
  refine ⟨φ, ψ', c, hφ, hψ', hc, fun S T hS hT => ?_⟩
  refine tendstoUniformlyOn_bilinear_series E F φ ψ' c hφ hψ' hc (fun x y => B x y) ?_ S T hS hT
  intro x y
  simpa only [hψ'eq] using hsum x y
