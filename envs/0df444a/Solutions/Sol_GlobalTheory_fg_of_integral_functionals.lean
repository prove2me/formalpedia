-- Prove2me | solution 1 for GlobalTheory.fg_of_integral_functionals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:44.008267+00:00
-- url     : https://prove2.me/submissions/6bb88142-105d-49f9-a003-735d39439314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgIntOfForallIsIntegral
import Theorems.Thm_GlobalTheory_fg_int_of_forall_isIntegral

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
theorem _root_.solution (K : Type) [Field K] [NumberField K] (C : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] [Module (𝓞 K) C]
    [IsScalarTower (𝓞 K) K C] (L : Submodule (𝓞 K) C)
    (h : ∀ x : C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (φ : C →ₗ[K] K'), φ x ≠ 0 ∧ ∀ y ∈ L, IsIntegral ℤ (φ y)) : L.FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  suffices H : ∀ W : Submodule K C, (L.restrictScalars ℤ ⊓ W.restrictScalars ℤ).FG by
    simpa using H ⊤
  intro W
  induction W using WellFoundedLT.induction with
  | _ W ih =>
    by_cases hW : W = ⊥
    · subst hW
      have hbot : L.restrictScalars ℤ ⊓ (⊥ : Submodule K C).restrictScalars ℤ = ⊥ := by
        ext y
        simp
      rw [hbot]
      exact Submodule.fg_bot
    · obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      obtain ⟨K', _, _, _, φ, hφx, hφL⟩ := h x hx0
      let f : C →ₗ[ℤ] K' := φ.toAddMonoidHom.toIntLinearMap
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left fun heq => hφx ?_
        have hx : x ∈ W ⊓ LinearMap.ker φ := by rw [heq]; exact hxW
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
      apply Submodule.fg_of_fg_map_of_fg_inf_ker f
      · apply fg_int_of_forall_isIntegral K'
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
        exact hφL y (Submodule.mem_inf.mp hy).1
      · have heq : L.restrictScalars ℤ ⊓ W.restrictScalars ℤ ⊓ LinearMap.ker f
            = L.restrictScalars ℤ ⊓ (W ⊓ LinearMap.ker φ).restrictScalars ℤ := by
          ext y
          simp [f, and_assoc]
          exact fun _ _ => Iff.rfl
        rw [heq]
        exact ih _ hlt
end GlobalTheory
