-- Prove2me | solution 1 for GlobalTheory.Pat.PhiFin.of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:24.837217+00:00
-- url     : https://prove2.me/submissions/d94d25dc-c952-442e-9aee-aeaa22002e45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
namespace PhiFin
theorem _root_.solution {l : ℕ} {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (h : PhiFin l G) (p : G →* G') (hc : Continuous p) (hs : Function.Surjective p) : PhiFin l G' := by
  intro H hH
  let q : H.comap p →* H := p.subgroupComap H
  have hq : Function.Surjective q := fun y => by
    obtain ⟨x, hx⟩ := hs y
    exact ⟨⟨x, by simp [hx]⟩, Subtype.ext hx⟩
  have hqc : Continuous q := (hc.comp continuous_subtype_val).subtype_mk _
  refine Set.Finite.of_finite_image (f := fun f => f.comp q)
    ((h (H.comap p) (hH.preimage hc)).subset ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact IsOpen.preimage hqc hf
  · intro f _ g _ e
    exact (MonoidHom.cancel_right hq).1 e
end PhiFin
end GlobalTheory.Pat
