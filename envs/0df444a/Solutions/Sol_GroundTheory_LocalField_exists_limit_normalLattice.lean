-- Prove2me | solution 1 for GroundTheory.LocalField.exists_limit_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:37.695597+00:00
-- url     : https://prove2.me/submissions/0fab2e82-f7b5-4f4d-80bf-6793f9c94343

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice_add_iff
import Theorems.Thm_GroundTheory_LocalField_exists_limit_of_pow_dvd
import Theorems.Thm_GroundTheory_LocalField_smul_sum_sub_smul_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (π : 𝒪[K]) (θ : L)
namespace GroundTheory.LocalField
theorem _root_.solution (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} (y : ℕ → L)
    (hy : ∀ n, y n ∈ normalLattice π θ s)
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, y n - y m ∈ normalLattice π θ (s + N)) :
    ∃ z ∈ normalLattice π θ s, ∀ N, ∃ M, ∀ n ≥ M, y n - z ∈ normalLattice π θ (s + N) := by
  choose c hcy using fun n => (mem_normalLattice_iff π θ).mp (hy n)
  have hcc : ∀ σ, ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n σ - c m σ := by
    intro σ N
    obtain ⟨M, hM⟩ := hc N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := hM m hm n hn
    rw [← hcy n, ← hcy m, smul_sum_sub_smul_sum,
      smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ] at this
    exact this σ
  choose a ha using fun σ => exists_limit_of_pow_dvd hπ (fun n => c n σ) (hcc σ)
  refine ⟨π ^ s • ∑ σ, a σ • σ θ, smul_sum_mem_normalLattice π θ s a, fun N => ?_⟩
  choose M hM using fun σ => ha σ N
  refine ⟨univ.sup M, fun n hn => ?_⟩
  rw [← hcy n, smul_sum_sub_smul_sum, smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ]
  exact fun σ => hM σ n ((le_sup (mem_univ σ)).trans hn)
end GroundTheory.LocalField
