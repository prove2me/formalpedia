-- Prove2me | solution 1 for GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:06:14.811911+00:00
-- url     : https://prove2.me/submissions/b35f46cb-d627-4c03-8dac-c88aa31f6db9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Theorems.Thm_GlobalTheory_DualFibreRank_cmp_natural
import Theorems.Thm_GlobalTheory_DualFibreRank_cmp_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DualFibreRank
namespace GlobalTheory.DualFibreRank
theorem _root_.solution :
    ∀ (O M N κ : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
      [Field κ] [Algebra O κ] (f : M →ₗ[O] N),
      Module.finrank κ (TensorProduct O κ (Module.Dual O M)) =
          Module.finrank κ (TensorProduct O κ M) ∧
        Module.finrank κ (LinearMap.range (f.dualMap.baseChange κ)) =
          Module.finrank κ (LinearMap.range (f.baseChange κ)) := by
  intro O M N κ _ _ _ _ _ _ _ _ _ _ _ f
  let eM := LinearEquiv.ofBijective (cmp κ M (O := O)) (cmp_bijective κ)
  refine ⟨by rw [eM.finrank_eq, Subspace.dual_finrank_eq], ?_⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (f.baseChange κ),
    ← LinearEquiv.finrank_map_eq eM]
  have : (LinearMap.range (f.dualMap.baseChange κ)).map (eM : _ →ₗ[κ] _) =
      LinearMap.range (f.baseChange κ).dualMap := by
    rw [← LinearMap.range_comp]
    change LinearMap.range (cmp κ M ∘ₗ f.dualMap.baseChange κ) = _
    rw [cmp_natural, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (cmp_bijective κ).2
  rw [this]
end GlobalTheory.DualFibreRank
