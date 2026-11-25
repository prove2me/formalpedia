-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eq_zero_of_forall_highestWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:40.632557+00:00
-- url     : https://prove2.me/submissions/2f1e1b51-12e7-46e2-a796-fc77e35eade6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_rowOp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_comm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_shift
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_conj_symm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_self_eq_zero_iff
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (T T' : Module.End ℂ (Poly n))
    (hcomm : ∀ i j, T * rowOp i j = rowOp i j * T)
    (hadj : ∀ f g, fischer (T f) g = fischer f (T' g))
    (hnormal : T * T' = T' * T)
    (hhw : ∀ (v : Poly n) (μ : Fin n → ℕ), (∀ i j, i < j → rowOp i j v = 0) → wtProj μ v = v →
      T v = 0) : T = 0 := by
  classical

  have hadj' : ∀ f g, fischer (T' f) g = fischer f (T g) := fun f g => by
    rw [← fischer_conj_symm, ← hadj, fischer_conj_symm]

  have hker : ∀ k, T k = 0 → T' k = 0 := by
    intro k hk
    have h1 : fischer (T' k) (T' k) = fischer (T k) (T k) := by
      rw [hadj', hadj]
      have := congrArg (fun S : Module.End ℂ (Poly n) => S k) hnormal
      simp only [Module.End.mul_apply] at this
      rw [this]
    rw [hk, fischer_zero_left] at h1
    exact (fischer_self_eq_zero_iff _).1 h1
  set S : Set (Poly n) := {s | ∀ k, T k = 0 → fischer s k = 0}
  have hS1 : ∀ f, T f ∈ S := fun f k hk => by rw [hadj, hker k hk, fischer_zero_right]
  have hS2 : ∀ μ, ∀ s ∈ S, wtProj μ s ∈ S := fun μ s hs k hk => by
    rw [fischer_wtProj]
    refine hs _ ?_
    rw [← wtProj_comm (fun a => hcomm a a), hk, map_zero]
  have hS3 : ∀ i j, ∀ s ∈ S, rowOp i j s ∈ S := fun i j s hs k hk => by
    rw [fischer_rowOp]
    refine hs _ ?_
    have := congrArg (fun S : Module.End ℂ (Poly n) => S k) (hcomm j i)
    simp only [Module.End.mul_apply] at this
    rw [this, hk, map_zero]
  have hS4 : ∀ s ∈ S, T s = 0 → s = 0 := fun s hs hT =>
    (fischer_self_eq_zero_iff s).1 (hs s hT)
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  by_contra hg
  set g := T f
  obtain ⟨m₀, hm₀⟩ : ∃ m, m ∈ g.support := by
    by_contra h
    push_neg at h
    exact hg (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  set μ₀ := rowWt m₀
  have hμ₀ : wtProj μ₀ g ≠ 0 := by
    intro h
    have := congrArg (coeff m₀) h
    rw [coeff_wtProj, if_pos rfl, coeff_zero] at this
    exact MvPolynomial.mem_support_iff.1 hm₀ this
  set d := ∑ a, μ₀ a
  set W : Finset (Fin n → ℕ) :=
    ((Finset.univ : Finset (Fin n → Fin (d + 1))).image fun μ i => (μ i : ℕ)).filter
      fun μ => ∑ a, μ a = d ∧ ∃ s ∈ S, wtProj μ s ≠ 0
  have hmemW : ∀ μ : Fin n → ℕ, ∑ a, μ a = d → (∃ s ∈ S, wtProj μ s ≠ 0) → μ ∈ W := by
    intro μ hsum hex
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨μ i, ?_⟩, Finset.mem_univ _, rfl⟩,
      hsum, hex⟩
    have : μ i ≤ d := hsum ▸ Finset.single_le_sum (fun a _ => Nat.zero_le (μ a)) (Finset.mem_univ i)
    omega
  have hW : W.Nonempty := ⟨μ₀, hmemW μ₀ rfl ⟨g, hS1 f, hμ₀⟩⟩
  obtain ⟨μ, hμW, hμmax⟩ := Finset.exists_max_image W wtHeight hW
  obtain ⟨hμsum, s, hs, hvne⟩ := (Finset.mem_filter.1 hμW).2
  set v := wtProj μ s
  have hvS : v ∈ S := hS2 μ s hs
  have hvv : wtProj μ v = v := by rw [wtProj_wtProj, if_pos rfl]
  have hhwv : ∀ i j, i < j → rowOp i j v = 0 := by
    intro i j hij
    by_contra hne
    obtain ⟨μ', h1, h2, h3⟩ := rowOp_shift hvv hij hne
    have hmem : μ' ∈ W := hmemW μ' (h2.trans hμsum) ⟨rowOp i j v, hS3 i j v hvS, by rw [h1]; exact hne⟩
    exact absurd (hμmax μ' hmem) (not_le.2 h3)
  exact hvne (hS4 v hvS (hhw v μ hhwv hvv))
end GroundTheory.Automorphic.HarishChandra
