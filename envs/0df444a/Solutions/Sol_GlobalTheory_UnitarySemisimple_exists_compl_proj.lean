-- Prove2me | solution 1 for GlobalTheory.UnitarySemisimple.exists_compl_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:42.016291+00:00
-- url     : https://prove2.me/submissions/39c56bdb-2971-4fc8-986a-a31525541154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Theorems.Thm_GlobalTheory_UnitarySemisimple_exists_orth_proj
import Theorems.Thm_GlobalTheory_UnitarySemisimple_rho_inv_rho
import Theorems.Thm_GlobalTheory_UnitarySemisimple_rho_rho_inv
import Theorems.Thm_GlobalTheory_OrthogonalProjection_exists_orth_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.UnitarySemisimple
theorem _root_.solution (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) (v : W) :
    ∃ t ∈ Z.toSubmodule, ∀ z ∈ Z.toSubmodule, B z (v - t) = 0 := by
  classical
  obtain ⟨K, hvK, hfd, hfin⟩ := hadm v
  have ofF : ∀ u ∈ GlobalTheory.PRep.fixed ρ K, ∀ k ∈ K, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K, ρ k u = u) → u ∈ GlobalTheory.PRep.fixed ρ K := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  haveI : FiniteDimensional ℂ (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K : Submodule ℂ W) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨m, hmM, hm⟩ := exists_orth_proj B hdef (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K) v
  refine ⟨m, hmM.1, fun z hz => ?_⟩
  have hwK : ∀ k ∈ K, ρ k (v - m) = v - m := by
    intro k hk
    rw [map_sub, hvK k hk, ofF m hmM.2 k hk]
  set s := (hfin z).toFinset with hs
  have hmem : ∀ o ∈ s, ∃ k' : K, ρ k' z = o := by
    intro o ho
    simpa [s] using ho
  have hperm : ∀ k ∈ K, ∑ o ∈ s, ρ k o = ∑ o ∈ s, o := by
    intro k hk
    apply Finset.sum_nbij' (fun o => ρ k o) (fun o => ρ k⁻¹ o)
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩⁻¹ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o _; exact rho_inv_rho ρ k o
    · intro o _; exact rho_rho_inv ρ k o
    · intro o _; rfl
  have heZ : ∑ o ∈ s, o ∈ Z.toSubmodule := by
    refine Submodule.sum_mem _ (fun o ho => ?_)
    obtain ⟨k', rfl⟩ := hmem o ho
    exact Z.apply_mem_toSubmodule _ hz
  have heF : ∑ o ∈ s, o ∈ GlobalTheory.PRep.fixed ρ K := by
    refine memF _ (fun k hk => ?_)
    rw [map_sum, hperm k hk]
  have h0 := hm _ ⟨heZ, heF⟩
  have hterm : ∀ o ∈ s, B o (v - m) = B z (v - m) := by
    intro o ho
    obtain ⟨k', rfl⟩ := hmem o ho
    rw [← hinv k' z (v - m), hwK k' k'.2]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hz1 : z ∈ s := by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, by simp⟩
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.2 ⟨z, hz1⟩
  rw [nsmul_eq_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (by exact_mod_cast h) hcard
  · exact h
end GlobalTheory.UnitarySemisimple
