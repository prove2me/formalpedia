-- Prove2me | solution 1 for GlobalTheory.IrredSB.mem_of_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:37.17059+00:00
-- url     : https://prove2.me/submissions/f19618c4-e5ce-4777-8913-e5cfd4862e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_IrredSB_ind_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {G : Type} [AddCommGroup G]
namespace GlobalTheory.IrredSB
theorem _root_.solution (W : Submodule ℂ (G → ℂ)) (hT : ∀ Φ ∈ W, ∀ x, (fun t => Φ (t + x)) ∈ W)
    {K : AddSubgroup G} (hK : ind K ∈ W) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ W := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert W.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s P _ ih =>
    intro Φ h2 h3
    have hm := Submodule.smul_mem _ (Φ s) (hT _ hK (-s))
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', u, hu, rfl⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by simpa using hu) (hval _ ht).2
        · exact ⟨s', hs', u, hu, rfl⟩
    simpa using add_mem this hm
end GlobalTheory.IrredSB
