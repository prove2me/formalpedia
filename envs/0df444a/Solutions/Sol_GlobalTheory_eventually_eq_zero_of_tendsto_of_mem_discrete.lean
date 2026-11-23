-- Prove2me | solution 1 for GlobalTheory.eventually_eq_zero_of_tendsto_of_mem_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:27.187924+00:00
-- url     : https://prove2.me/submissions/fbcb425b-a022-4b4a-928a-34057ce83a6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution {α F : Type*} [AddCommGroup F]
    [TopologicalSpace F] {Γ : AddSubgroup F} (hΓ : IsDiscrete (Γ : Set F)) {l : Filter α}
    {f : α → F} (hf : Tendsto f l (𝓝 0)) (hm : ∀ᶠ a in l, f a ∈ Γ) : ∀ᶠ a in l, f a = 0 := by
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hΓ 0 Γ.zero_mem
  have h0 : (0 : F) ∈ U := (hU0.ge rfl).1
  filter_upwards [hf (hU.mem_nhds h0), hm] with a h1 h2
  exact hU0.le ⟨h1, h2⟩
end GlobalTheory
