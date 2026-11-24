-- Prove2me | solution 1 for GlobalTheory.Published.Heisenberg.isTopologicalGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:50.241929+00:00
-- url     : https://prove2.me/submissions/3c40d3e7-4e8c-4b63-baa5-99cf6cd5f59c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Splits_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open Heisenberg
variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]
namespace GlobalTheory.Published.SvN
namespace _root_.GlobalTheory.Published.Heisenberg
theorem _root_.solution : IsTopologicalGroup (Heisenberg B) := by
  have := IsModuleTopology.topologicalAddGroup F W
  have hcB : Continuous fun p : W × W => B p.1 p.2 := IsModuleTopology.continuous_bilinear_of_finite_left B
  have h0 : Continuous fun g : Heisenberg B => (g.vec, g.cen) := continuous_induced_dom
  have h1 : Continuous (Heisenberg.vec : Heisenberg B → W) := h0.fst
  have h2 : Continuous (Heisenberg.cen : Heisenberg B → F) := h0.snd
  exact
    { continuous_mul := continuous_induced_rng.2 (((h1.comp continuous_fst).add (h1.comp continuous_snd)).prodMk
        (((h2.comp continuous_fst).add (h2.comp continuous_snd)).add
          ((hcB.comp ((h1.comp continuous_fst).prodMk (h1.comp continuous_snd))).div_const 2)))
      continuous_inv := continuous_induced_rng.2 (h1.neg.prodMk (h2.neg.add ((hcB.comp (h1.prodMk h1)).div_const 2))) }
end _root_.GlobalTheory.Published.Heisenberg
end GlobalTheory.Published.SvN
