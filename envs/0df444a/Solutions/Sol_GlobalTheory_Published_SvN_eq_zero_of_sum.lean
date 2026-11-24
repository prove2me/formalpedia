-- Prove2me | solution 1 for GlobalTheory.Published.SvN.eq_zero_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:39:57.023175+00:00
-- url     : https://prove2.me/submissions/73e19b6d-c057-4d13-9413-ba9ec52df41b

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
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution {ι : Type} (s : Finset ι) (β : ι → W → ℂ) (hβ : ∀ i, ∃ a ∈ A, β i a ≠ α a) :
    ∀ (m : ι → M), (∀ i, ∀ a ∈ A, ρ a (m i) = β i a • m i) →
      (∀ a ∈ A, ρ a (∑ i ∈ s, m i) = α a • ∑ i ∈ s, m i) → ∑ i ∈ s, m i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _ _; simp
  | insert j s hj ih =>
    intro m hm hv
    obtain ⟨a, ha, hne⟩ := hβ j
    have key : ∑ i ∈ s, (β i a - β j a) • m i = (α a - β j a) • ∑ i ∈ insert j s, m i := by
      rw [sub_smul, ← hv a ha, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert hj, hm j a ha, sub_self,
        zero_add]
      exact Finset.sum_congr rfl fun i _ => by rw [hm i a ha, sub_smul]
    have := ih (fun i => (β i a - β j a) • m i) (fun i b hb => by rw [map_smul, hm i b hb, smul_comm])
      (fun b hb => by rw [key, map_smul, hv b hb, smul_comm])
    rw [key] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
end GlobalTheory.Published.SvN
