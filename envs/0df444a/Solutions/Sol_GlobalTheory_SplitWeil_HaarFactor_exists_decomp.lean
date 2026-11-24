-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:17.494419+00:00
-- url     : https://prove2.me/submissions/8a10aadc-aa6d-4ef4-9410-ed7fa1d67ceb

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
theorem _root_.solution {U : AddSubgroup A} (hU : IsOpen (U : Set A)) {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A))
    (hinv : ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z) :
    ∃ T : Finset (A ⧸ U), ∀ z : X₀ × A,
      G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) := by
  classical
  have hK : IsCompact (Prod.snd '' tsupport G) := hG.2.image continuous_snd
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩
  have hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) =
      if (z.2 : A ⧸ U) = q then 1 else 0 := by
    intro q
    have : (z.2 : A ⧸ U) = q ↔ z.2 - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : z.2 - q.out ∈ U
    · rw [Set.indicator_of_mem (show z.2 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]
    · rw [Set.indicator_of_notMem (show z.2 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
  split_ifs with h
  · have h2 : -z.2 + (z.2 : A ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have := hinv _ h2 z
    rw [add_neg_cancel_left] at this
    exact this.symm
  · refine image_eq_zero_of_notMem_tsupport fun hz => h ?_
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)
    exact Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩
end GlobalTheory.SplitWeil.HaarFactor
