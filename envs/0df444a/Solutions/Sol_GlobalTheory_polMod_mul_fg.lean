-- Prove2me | solution 1 for GlobalTheory.polMod_mul_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:16.044239+00:00
-- url     : https://prove2.me/submissions/955396e1-504f-411e-97a0-81b014954446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationLatticeFg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  intro E _ _ _ L ⟨N, hN, hL⟩ hu
  have hLfg : L.FG := by
    apply Submodule.FG.of_restrictScalars ℤ
    let f : E →ₗ[ℤ] E := LinearMap.mulLeft ℤ (N : E)
    have hf : Function.Injective f := mul_right_injective₀ (Nat.cast_ne_zero.2 hN.ne')
    let g : 𝓞 E →ₗ[ℤ] E := (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
    have hg : (LinearMap.range g).FG := by
      rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
    refine Submodule.fg_of_fg_map_injective f hf (hg.of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(N : E) * x, hL x hx⟩, rfl⟩
  have hMfg : (polMod L).FG := Submodule.fg_of_isUnit hu
  have hP : (polMod L * L).FG := hMfg.mul hLfg
  exact (Submodule.fg_iff_addSubgroup_fg ((polMod L * L).restrictScalars ℤ)).1 (hP.restrictScalars)
end GlobalTheory
