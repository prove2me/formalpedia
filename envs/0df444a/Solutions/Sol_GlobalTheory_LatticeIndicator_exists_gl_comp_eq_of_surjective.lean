-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_gl_comp_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:46.34996+00:00
-- url     : https://prove2.me/submissions/5488deaf-1214-40a2-8081-a59e9f7c385d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_gl_of_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O Q n : Type*} [CommRing O] [IsLocalRing O]
    [AddCommGroup Q] [Module O Q] [Fintype n] [DecidableEq n] (a b : (n → O) →ₗ[O] Q)
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    ∃ g : GL n O, a = b ∘ₗ Matrix.toLin' (g : Matrix n n O) := by
  have hspan : ∀ c : (n → O) →ₗ[O] Q, Function.Surjective c →
      Submodule.span O (Set.range fun i => c (Pi.basisFun O n i)) = ⊤ := by
    intro c hc
    have : (Set.range fun i => c (Pi.basisFun O n i)) = c '' Set.range (Pi.basisFun O n) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, (Pi.basisFun O n).span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 hc]
  obtain ⟨g, hg⟩ := exists_gl_of_span_eq_top _ _ (hspan a ha) (hspan b hb)
  refine ⟨g, (Pi.basisFun O n).ext fun j => ?_⟩
  rw [hg j, LinearMap.comp_apply]
  simp_rw [← map_smul, ← map_sum]
  congr 1
  ext i
  simp [Pi.single_apply, Finset.sum_apply]
end GlobalTheory.LatticeIndicator
