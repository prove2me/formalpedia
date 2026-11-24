-- Prove2me | solution 1 for GlobalTheory.HyperplaneExt.extend_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:15.179129+00:00
-- url     : https://prove2.me/submissions/321ac43d-b5c2-46ed-88e9-5b3ca6918d0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionCoordinateHyperplaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossCoordinateHyperplanes
import Theorems.Thm_GlobalTheory_HyperplaneExt_norm_le_of_off_hyperplane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.HyperplaneExt
namespace GlobalTheory.HyperplaneExt
theorem _root_.solution (hR : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n : ℕ) (s : Finset (Fin n)) (W : Set (Fin n → ℂ)) (Φ : (Fin n → ℂ) → ℂ), IsOpen W →
      DifferentiableOn ℂ Φ {z | z ∈ W ∧ ∀ k ∈ s, z k ≠ 0} →
      (∀ z₀ ∈ W, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ W → (∀ k ∈ s, z k ≠ 0) → ‖Φ z‖ ≤ M) →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ W, (∀ k ∈ s, z k ≠ 0) → F z = Φ z := by
  intro n s
  induction s using Finset.induction_on with
  | empty =>
    intro W Φ _ hd _
    refine ⟨Φ, ?_, fun _ _ _ => rfl⟩
    simpa using hd
  | insert j t _ ih =>
    intro W Φ hW hd hb
    have hUeq : {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} = W ∩ ⋂ k ∈ t, {z | z k ≠ 0} := by
      ext z; simp
    have hU : IsOpen {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} := by
      rw [hUeq]
      exact hW.inter (isOpen_biInter_finset fun k _ => isOpen_ne_fun (continuous_apply k) continuous_const)
    have hd1 : DifferentiableOn ℂ Φ {z | z ∈ {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} ∧ z j ≠ 0} := by
      refine hd.mono fun z hz => ⟨hz.1.1, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz.2
      · exact hz.1.2 k hk
    obtain ⟨F1, hF1d, hF1e⟩ := hR n _ j Φ hU hd1 (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀.1
      refine ⟨V, hV, M, fun z hzV hzU hzj => hM z hzV hzU.1 ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzj
      · exact hzU.2 k hk)
    have hall : ∀ z : Fin n → ℂ, (∀ k ∈ insert j t, z k ≠ 0) ↔ z j ≠ 0 ∧ ∀ k ∈ t, z k ≠ 0 := by
      intro z; simp
    obtain ⟨F, hFd, hFe⟩ := ih W F1 hW hF1d (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
      refine ⟨interior V, interior_mem_nhds.mpr hV, M, ?_⟩
      intro z hzV hzW ht
      refine norm_le_of_off_hyperplane (k := j) hU isOpen_interior hF1d.continuousOn
        (fun w hwV hwU hwj => ?_) z hzV ⟨hzW, ht⟩
      rw [hF1e w hwU hwj]
      exact hM w (interior_subset hwV) hwU.1 ((hall w).2 ⟨hwj, hwU.2⟩))
    refine ⟨F, hFd, fun z hz hk => ?_⟩
    have hk' := (hall z).1 hk
    rw [hFe z hz hk'.2, hF1e z ⟨hz, hk'.2⟩ hk'.1]
end GlobalTheory.HyperplaneExt
