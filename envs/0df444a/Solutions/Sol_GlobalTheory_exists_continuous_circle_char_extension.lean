-- Prove2me | solution 1 for GlobalTheory.exists_continuous_circle_char_extension
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:04.067789+00:00
-- url     : https://prove2.me/submissions/bf1110f7-61e1-4b3a-8659-c99962d6721d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension
import Theorems.Thm_GlobalTheory_circle_hom_extend_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (H N : Subgroup G) (ψ : H →* Circle), IsOpen (H : Set G) → Continuous ψ → (∀ x : H, (x : G) ∈ N → ψ x = 1) → ∃ χ : G →* Circle, Continuous χ ∧ (∀ x ∈ N, χ x = 1) ∧ ∀ x : H, χ x = ψ x := by
  intro G _ _ _ H N ψ hH hψ hN
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hker : f.ker ≤ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hN x ((QuotientGroup.eq_one_iff _).1 hx)
  obtain ⟨χ₀, hχ₀⟩ := circle_hom_extend_of_injective (QuotientGroup.kerLift f)
    (QuotientGroup.kerLift_injective f) (QuotientGroup.lift f.ker ψ hker)
  have hx : ∀ x : H, (χ₀.comp (QuotientGroup.mk' N)) x = ψ x := fun x => hχ₀ (QuotientGroup.mk x)
  refine ⟨χ₀.comp (QuotientGroup.mk' N), ?_, fun x hxN => ?_, hx⟩
  · refine continuous_of_continuousAt_one _ ?_
    have hc : ContinuousOn (χ₀.comp (QuotientGroup.mk' N)) (H : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hψ.congr fun x => (hx x).symm
    exact hc.continuousAt (hH.mem_nhds H.one_mem)
  · have : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff _).2 hxN
    rw [MonoidHom.comp_apply, this, map_one]
end GlobalTheory
