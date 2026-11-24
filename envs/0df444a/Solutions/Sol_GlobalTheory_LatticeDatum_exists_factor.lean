-- Prove2me | solution 1 for GlobalTheory.LatticeDatum.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:40.680109+00:00
-- url     : https://prove2.me/submissions/6cc9003c-8fe4-4a19-822f-f2b792a9d660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice
import Theorems.Thm_GlobalTheory_LatticeDatum_exists_nsmul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.LatticeDatum
namespace GlobalTheory.LatticeDatum
theorem _root_.solution {E V L L' : Type} [Field E] [NumberField E] [AddCommGroup V] [Module (𝓞 E) V] [Module E V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    [Module.Finite (𝓞 E) L'] (φ : L →ₗ[𝓞 E] V) (φ' : L' →ₗ[𝓞 E] V) (hφ : Function.Injective φ)
    (hs : Submodule.span E (Set.range φ) = ⊤) :
    ∃ (N : ℕ) (ψ : L' →ₗ[𝓞 E] L), 0 < N ∧ ∀ x, φ (ψ x) = N • φ' x := by
  have hfg : (LinearMap.range φ').FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ'
  obtain ⟨N, hN, h⟩ := exists_nsmul_mem (LinearMap.range φ') (LinearMap.range φ) hfg
    (by rw [LinearMap.coe_range]; exact hs)
  choose g hg using fun x : L' => h (φ' x) ⟨x, rfl⟩
  refine ⟨N, ⟨⟨g, fun x y => hφ ?_⟩, fun a x => hφ ?_⟩, hN, hg⟩
  · rw [map_add, hg, hg, hg, map_add, smul_add]
  · rw [map_smul, hg, hg, map_smul, smul_comm]; rfl
end GlobalTheory.LatticeDatum
