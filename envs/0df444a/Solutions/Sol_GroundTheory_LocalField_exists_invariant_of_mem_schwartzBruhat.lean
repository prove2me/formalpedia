-- Prove2me | solution 1 for GroundTheory.LocalField.exists_invariant_of_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:57:56.893207+00:00
-- url     : https://prove2.me/submissions/5f5a28bf-e171-4f4e-a14f-ce4664682381

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    ∃ N M : ℤ, (∀ x, ∀ h ∈ valBall K N, f (x + h) = f x) ∧ ∀ x, f x ≠ 0 → x ∈ valBall K M := by
  obtain ⟨hlc, hcs⟩ := hf
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport f ⊆ (valBall K (-(m : ℤ)) : Set K) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ => (valBall K (-(m : ℤ)) : Set K))
      (fun m => isOpen_valBall _) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      exact exists_mem_valBall_neg_nat x
    · exact Monotone.directed_le fun a b hab => valBall_antitone (by omega)
  have hloc : ∀ x : K, ∃ n : ℤ, ∀ h ∈ valBall K n, f (x + h) = f x := by
    intro x
    have ho : IsOpen {h : K | f (x + h) = f x} :=
      (hlc.isOpen_fiber (f x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh => hn hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => {z : K | z - x ∈ valBall K (n x)})
    (fun x _ => ((isOpen_valBall _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨N, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport f, ∀ h ∈ valBall K N, f (y + h) = f y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hN' : valBall K N ≤ valBall K (n x) :=
      valBall_antitone (hN _ (Finset.mem_image_of_mem n hxt))
    have e1 : f y = f x := by
      have := hn x (y - x) hyx
      rwa [add_sub_cancel] at this
    have e2 : f (y + h) = f x := by
      have := hn x (y + h - x)
        (by rw [show y + h - x = (y - x) + h by ring]; exact add_mem hyx (hN' hh))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N, -(m : ℤ), fun y h hh => ?_, fun x hx => hm (subset_tsupport f hx)⟩
  by_cases hy : y ∈ tsupport f
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport f
  · have := hval (y + h) hyh (-h) (neg_mem hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]
end GroundTheory.LocalField
