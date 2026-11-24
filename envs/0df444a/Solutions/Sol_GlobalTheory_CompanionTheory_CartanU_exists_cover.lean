-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartanU.exists_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:21:41.837533+00:00
-- url     : https://prove2.me/submissions/e28b494a-069c-4470-9fe4-d92537380b9c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU
namespace GlobalTheory.CompanionTheory.CartanU
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (K K₀ : Subgroup G)
    (hK : IsOpen (K : Set G)) (hc : IsCompact (K₀ : Set G)) :
    ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ k ∈ K, g = c i * k := by
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun c : K₀ => (fun x => (c : G)⁻¹ * x) ⁻¹' (K : Set G))
    (fun c => hK.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [one_mem]⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : t) : K₀), fun i => Subtype.coe_prop _, fun g hg => ?_⟩
  obtain ⟨c, hct, hgc⟩ : ∃ c ∈ t, (c : G)⁻¹ * g ∈ K := by simpa using ht hg
  refine ⟨t.equivFin ⟨c, hct⟩, (c : G)⁻¹ * g, hgc, ?_⟩
  simp
end GlobalTheory.CompanionTheory.CartanU
