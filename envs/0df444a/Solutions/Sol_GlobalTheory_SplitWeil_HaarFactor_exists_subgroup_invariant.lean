-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.exists_subgroup_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:17.714203+00:00
-- url     : https://prove2.me/submissions/3d5ed296-f2ee-4e47-95ff-3fab1d41f038

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) :
    ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧
      ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z := by
  have h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ z ∈ tsupport G, G (z.1, z.2 + t) = G z := by
    refine IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : A × (X₀ × A) => (G (q.2.1, q.2.2 + q.1), G q.2) :=
      (hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hUo, hUc, hUs⟩ := hbasis _ h1
  refine ⟨U, hUo, hUc, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport G
  · exact hUs hu z hz
  by_cases hz' : (z.1, z.2 + u) ∈ tsupport G
  · have := hUs (U.neg_mem hu) _ hz'
    simp only [add_neg_cancel_right, Prod.mk.eta] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
end GlobalTheory.SplitWeil.HaarFactor
