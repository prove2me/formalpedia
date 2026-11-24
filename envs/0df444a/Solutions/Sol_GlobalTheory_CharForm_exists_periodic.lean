-- Prove2me | solution 1 for GlobalTheory.CharForm.exists_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:55.832067+00:00
-- url     : https://prove2.me/submissions/5e626c6b-3ba1-4b86-9cd9-ef10f3615a08

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
noncomputable section
open scoped Classical Topology
open GlobalTheory GlobalTheory.CharForm
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
namespace GlobalTheory.CharForm
theorem _root_.solution {C : Set (X → ℂ)}
    (H : ∀ N ∈ 𝓝 (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) {V : Set X} (hV : V ∈ 𝓝 (0 : X)) :
    ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ V ∧
      (∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) ∧ ∀ x, ∀ u ∈ U, g (x + u) = g x := by
  have hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X) := fun x =>
    ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)
  choose W hWo _ hWN _ using fun x => H _ (hN x)
  obtain ⟨t, -, hcov⟩ := hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) fun x _ =>
    ((hWo x).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  have hNm : V ∩ ⋂ x ∈ t, (W x : Set X) ∈ 𝓝 (0 : X) :=
    Filter.inter_mem hV ((Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (W x).zero_mem)
  obtain ⟨U, hUo, hUc, hUN, hUk⟩ := H _ hNm
  refine ⟨U, hUo, hUc, fun u hu => (hUN hu).1, hUk, ?_⟩
  have hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    have hu' : u ∈ W x := Set.mem_iInter₂.mp (hUN hu).2 x hxt
    have h1 : g (x + (y - x)) = g x := hWN x hyx
    have h2 : g (x + (y - x + u)) = g x := hWN x ((W x).add_mem hyx hu')
    rw [add_sub_cancel] at h1
    rw [← add_assoc, add_sub_cancel] at h2
    rw [h1, h2]
  intro y u hu
  by_cases hy : y ∈ tsupport g
  · exact hA y hy u hu
  by_cases hyu : y + u ∈ tsupport g
  · have := hA _ hyu (-u) (U.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]
end GlobalTheory.CharForm
