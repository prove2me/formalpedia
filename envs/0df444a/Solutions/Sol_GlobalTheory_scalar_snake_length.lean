-- Prove2me | solution 1 for GlobalTheory.scalar_snake_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:42.236072+00:00
-- url     : https://prove2.me/submissions/20c93c82-7325-41dd-8c91-682d4f82edb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_mid
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_of_injective
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_length_of_surjective
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_kerMap_injective
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_exact_kerMap
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_exact_quotMap
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_quotMap_surjective
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_exact_kerMap_delta
import Theorems.Thm_GlobalTheory_ScalarSnakeLength_exact_delta_quotMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [AddCommGroup M₂]
      [AddCommGroup M₃] [Module A M₁] [Module A M₂] [Module A M₃] (f : M₁ →ₗ[A] M₂)
      (g : M₂ →ₗ[A] M₃), Function.Injective f → Function.Surjective g → Function.Exact f g →
      ∀ b : A,
        Module.length A (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) =
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) +
            Module.length A (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) +
            Module.length A (M₃ ⧸ LinearMap.range (LinearMap.lsmul A M₃ b)) ∧
        Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) ≤
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) := by
  intro A _ M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg b
  open ScalarSnakeLength in
  have e1 := length_of_injective (kerMap f b) (kerMap_injective f hf b)
  have e2 := length_mid (kerMap f b) (kerMap g b) (exact_kerMap f g hf hfg b)
  have e3 := length_mid (kerMap g b) (delta f g hf hg hfg b) (exact_kerMap_delta f g hf hg hfg b)
  have e4 := length_mid (delta f g hf hg hfg b) (quotMap f b)
    (exact_delta_quotMap f g hf hg hfg b)
  have e5 := length_mid (quotMap f b) (quotMap g b) (exact_quotMap f g hg hfg b)
  have e6 := length_of_surjective (quotMap g b) (quotMap_surjective g hg b)
  rw [e1, e2, e3, e4, e5, ← e6]
  constructor
  · ac_rfl
  · exact add_le_add le_rfl le_self_add
end GlobalTheory
