-- Prove2me | solution 1 for GlobalTheory.exists_contDiff_extension_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:15:14.060492+00:00
-- url     : https://prove2.me/submissions/3c544049-f783-4ebb-bac9-ff2652d573cd

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsContDiffExtensionOfIsClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped ContDiff Manifold Topology
open GlobalTheory
open scoped ContDiff Manifold Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsClosed S) (f : E → ℂ)
    (hf : ∀ x ∈ S, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ y ∈ U, y ∈ S → f y = F y) :
    ∃ F : E → ℂ, ContDiff ℝ ∞ F ∧ ∀ y ∈ S, F y = f y := by
  classical
  let t : E → Set ℂ := fun y => if y ∈ S then {f y} else Set.univ
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [t, if_pos hy]; exact convex_singleton _
    · simp only [t, if_neg hy]; exact convex_univ
  have hloc : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ g : E → ℂ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hf x hx
      refine ⟨U, hU.mem_nhds hxU, F, hF.contMDiffOn, fun y hy => ?_⟩
      by_cases hyS : y ∈ S
      · simp only [t, if_pos hyS, Set.mem_singleton_iff]; exact (hfF y hy hyS).symm
      · simp only [t, if_neg hyS, Set.mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, fun y hy => ?_⟩
      simp only [t, if_neg (show y ∉ S from hy), Set.mem_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, E) (n := ⊤) ht hloc
  refine ⟨g, g.contMDiff.contDiff, fun y hy => ?_⟩
  have hgy := hg y
  simpa only [t, if_pos hy, Set.mem_singleton_iff] using hgy
end _root_.GlobalTheory
end GlobalTheory
