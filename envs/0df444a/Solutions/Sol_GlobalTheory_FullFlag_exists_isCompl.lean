-- Prove2me | solution 1 for GlobalTheory.FullFlag.exists_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:04.968652+00:00
-- url     : https://prove2.me/submissions/f23c841d-62f5-4fb4-b2e4-ee906b528930

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution (F : FullFlag R M n) (k : Fin (n + 1)) :
    ∃ Q : Submodule R M, IsCompl (F.sub k) Q := by
  obtain ⟨r, h₁, h₂⟩ := F.exists_retraction k
  exact ⟨_, LinearMap.isCompl_of_proj (f := r.codRestrict _ h₁) fun x => Subtype.ext (h₂ x x.2)⟩
end GlobalTheory.FullFlag
