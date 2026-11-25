-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:03.876281+00:00
-- url     : https://prove2.me/submissions/adca5eec-7d32-483a-ab9b-1582c8282b84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hn : h.Nondegenerate) (f : V →ₗ[K] K) :
    ∃ y, h y = f := by
  have h1 : (LinearMap.range h).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hn.2 x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : f ∈ LinearMap.range h := h2 ▸ Submodule.mem_top
  exact h3
end GlobalTheory.Mass.Hyperplane
