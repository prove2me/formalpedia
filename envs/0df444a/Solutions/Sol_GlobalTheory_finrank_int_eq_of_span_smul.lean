-- Prove2me | solution 1 for GlobalTheory.finrank_int_eq_of_span_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:41.829856+00:00
-- url     : https://prove2.me/submissions/c26d4e9f-0f06-4f31-b7e8-54b9a87e1bcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegree
import Theorems.Thm_GlobalTheory_smul_eq_zero_of_ringOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M)
    (hx : LinearIndependent (𝓞 F) x) (c : 𝓞 F) (hc : c ≠ 0)
    (hspan : ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) :
    Module.finrank ℤ M = r * Module.finrank ℚ F := by
  let φ : (Fin r → 𝓞 F) →ₗ[ℤ] M := (Fintype.linearCombination (𝓞 F) x).restrictScalars ℤ
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    funext i
    exact Fintype.linearIndependent_iff.mp hx g (by simpa [φ, Fintype.linearCombination_apply] using hg) i
  have hdom : Module.finrank ℤ (Fin r → 𝓞 F) = r * Module.finrank ℚ F := by
    rw [Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let ψ : M →ₗ[ℤ] M := (LinearMap.lsmul (𝓞 F) M c).restrictScalars ℤ
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    exact smul_eq_zero_of_ringOfIntegers hc (by simpa [ψ] using hm)
  have hrange : ∀ m, ψ m ∈ LinearMap.range φ := by
    intro m
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hspan m)
    exact ⟨g, by simpa [φ, ψ, Fintype.linearCombination_apply] using hg⟩
  let ψ' : M →ₗ[ℤ] LinearMap.range φ := ψ.codRestrict _ hrange
  have hψ' : Function.Injective ψ' := by
    intro a b hab
    apply hψ
    simpa [ψ'] using congrArg Subtype.val hab
  have h1 : Module.finrank ℤ (Fin r → 𝓞 F) ≤ Module.finrank ℤ M :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have hfin : Module.Finite ℤ (LinearMap.range φ) := inferInstance
  have h2 : Module.finrank ℤ M ≤ Module.finrank ℤ (LinearMap.range φ) :=
    LinearMap.finrank_le_finrank_of_injective hψ'
  rw [LinearMap.finrank_range_of_inj hφ] at h2
  omega
end GlobalTheory
