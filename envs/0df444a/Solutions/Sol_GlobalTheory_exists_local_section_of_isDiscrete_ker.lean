-- Prove2me | solution 1 for GlobalTheory.exists_local_section_of_isDiscrete_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:55.354947+00:00
-- url     : https://prove2.me/submissions/1d6d9331-487e-40a7-9c0f-34b79bf87014

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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Type*} [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution {F : Type*} [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [TopologicalSpace A] {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) (hopen : 𝓝 (0 : A) ≤ map ex' (𝓝 0)) :
    ∃ s : A → F, s 0 = 0 ∧ ContinuousAt s 0 ∧ (∀ᶠ a in 𝓝 0, ex' (s a) = a) ∧
      ∀ᶠ z in 𝓝 0, s (ex' z) = z := by
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hker 0 ex'.ker.zero_mem
  obtain ⟨W, hW, hWU⟩ := exists_nhds_half_neg (hU.mem_nhds (hU0.ge rfl).1)
  have hinj : InjOn ex' W := fun x hx y hy hxy ↦
    sub_eq_zero.1 (hU0.le ⟨hWU x hx y hy, by simp [AddMonoidHom.mem_ker, hxy]⟩)
  have hs : ∀ᶠ z in 𝓝 0, Function.invFunOn ex' W (ex' z) = z := by
    filter_upwards [hW] with z hz using hinj.leftInvOn_invFunOn hz
  have h0 : Function.invFunOn ex' W 0 = 0 := by simpa using hs.self_of_nhds
  refine ⟨Function.invFunOn ex' W, h0, ?_, hopen ?_, hs⟩
  · rw [ContinuousAt, h0]
    exact (tendsto_map'_iff.2 (tendsto_id.congr' (hs.mono fun z hz ↦ hz.symm))).mono_left hopen
  · change ∀ᶠ a in map ex' (𝓝 0), _
    rw [eventually_map]
    filter_upwards [hs] with z hz
    rw [hz]
end GlobalTheory
