-- Prove2me | solution 1 for GlobalTheory.Published.SvN.eventually_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:57.715853+00:00
-- url     : https://prove2.me/submissions/9aa303d2-a212-4c65-bdc5-0db26ae233b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

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
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [IsModuleTopology F W]
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hs : PRep.IsSmooth π) (v : M) : ∀ᶠ u in 𝓝 (0 : W), π ⟨u, 0⟩ v = v := by
  have hc : Continuous fun u : W => (⟨u, 0⟩ : Heisenberg B) := continuous_induced_rng.2 (continuous_id.prodMk continuous_const)
  exact ((hs v).preimage hc).mem_nhds (show π 1 v = v by simp)
end GlobalTheory.Published.SvN
