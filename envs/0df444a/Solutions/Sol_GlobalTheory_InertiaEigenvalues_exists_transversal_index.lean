-- Prove2me | solution 1 for GlobalTheory.InertiaEigenvalues.exists_transversal_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:42.092175+00:00
-- url     : https://prove2.me/submissions/5057a195-8555-4de1-8603-b4aef5a2fcfd

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_Induced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedRepresentationCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Published
noncomputable section
open GlobalTheory GlobalTheory.InertiaEigenvalues
open BrauerSchur
namespace GlobalTheory.InertiaEigenvalues
theorem _root_.solution {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ t : Fin H.index → G, (∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) ∧ ∀ x, ∃ i, (t i)⁻¹ * x ∈ H := by
  classical
  let e : G ⧸ H ≃ Fin H.index := Finite.equivFin (G ⧸ H)
  refine ⟨fun i => (e.symm i).out, fun i j => ?_, fun x => ⟨e (x : G ⧸ H), ?_⟩⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq', e.symm.injective.eq_iff]
  · rw [← QuotientGroup.eq]
    simp only [Equiv.symm_apply_apply, QuotientGroup.out_eq']
end GlobalTheory.InertiaEigenvalues
