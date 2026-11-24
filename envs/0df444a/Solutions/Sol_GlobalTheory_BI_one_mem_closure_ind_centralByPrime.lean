-- Prove2me | solution 1 for GlobalTheory.BI.one_mem_closure_ind_centralByPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:01:20.141897+00:00
-- url     : https://prove2.me/submissions/adb8aff6-f634-4730-90d1-6c130470498b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombinationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsInducedIntPrimeToStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndMulClassFunEqIndMulRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Theorems.Thm_GlobalTheory_BI_ind_mul_classFun_eq_ind_mul_restrict
import Theorems.Thm_GlobalTheory_T_exists_integral_comb_induced_linear_not_dvd
import Theorems.Thm_GlobalTheory_T_one_mem_virtualCharacters_of_integral_combination
import Theorems.Thm_GlobalTheory_T_virtualCharacters_mul_comap_conj_ind_linear
import Theorems.Thm_GlobalTheory_one_mem_of_mul_mem_of_forall_prime_not_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution :
    ∀ (G : Type) [Group G] [Finite G], (1 : G → ℂ) ∈ AddSubgroup.closure {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} := by
  intro G _ _
  classical
  set A : Set (G → ℂ) := {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} with hA
  obtain ⟨hmul, hpull, hclass, hind, -⟩ := GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear G
  have hAV : ∀ f ∈ A, f ∈ Virt ℂ ℂ G := by
    rintro f ⟨E, ψ, -, hψ, rfl⟩
    exact hind E ψ hψ
  have hJV : AddSubgroup.closure A ≤ Virt ℂ ℂ G := (AddSubgroup.closure_le _).2 hAV
  have hAA : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    have hgV := hAV g hg
    obtain ⟨E, ψ, hE, hψ, rfl⟩ := hf
    refine ⟨E, fun h => ψ h * g h, hE, ?_, ind_mul_classFun_eq_ind_mul_restrict G E ψ g (hclass g hgV)⟩
    exact (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).1 ψ hψ _ (hpull g hgV E E.subtype)
  let R := integralClosure ℤ ℂ
  let J : Submodule R (G → ℂ) := Submodule.span R A
  have hJJ : ∀ f ∈ J, ∀ g ∈ J, f * g ∈ J := by
    intro f hf g hg
    induction hf, hg using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact Submodule.subset_span (hAA x hx y hy)
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact J.add_mem h1 h2
    | add_right x y z hx hy hz h1 h2 => rw [mul_add]; exact J.add_mem h1 h2
    | smul_left r x y hx hy h => rw [smul_mul_assoc]; exact J.smul_mem r h
    | smul_right r x y hx hy h => rw [mul_smul_comm]; exact J.smul_mem r h
  let c : (G → ℤ) →+* (G → ℂ) := (Int.castRingHom ℂ).compLeft G
  let S : AddSubgroup (G → ℤ) := J.toAddSubgroup.comap c.toAddMonoidHom
  have hS : ∀ f, f ∈ S ↔ c f ∈ J := fun f => Iff.rfl
  have h1 : (1 : G → ℤ) ∈ S := by
    refine GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd G S ?_ ?_
    · intro f hf g hg
      rw [hS] at hf hg ⊢
      rw [map_mul]
      exact hJJ _ hf _ hg
    · intro x p hp
      obtain ⟨E, f, ι, _, r, lam, hE, hf, hr, hsum⟩ := GlobalTheory.T.exists_integral_comb_induced_linear_not_dvd G x p hp
      refine ⟨f, ?_, hf⟩
      rw [hS]
      have : c f = ∑ i, (⟨r i, hr i⟩ : R) • ind E (fun e => (lam i e : ℂ)) := by
        funext g
        rw [Finset.sum_apply]
        exact hsum g
      rw [this]
      refine J.sum_mem fun i _ => J.smul_mem _ (Submodule.subset_span ?_)
      exact ⟨E, _, hE, (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).2.2.2.2 (lam i), rfl⟩
  rw [hS, map_one] at h1
  obtain ⟨n, r, s, hsum⟩ := Submodule.mem_span_set'.1 h1
  refine GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination G _ hJV (Fin n) (fun i => (r i : ℂ)) (fun i => (s i : G → ℂ)) (fun i => (r i).2)
    (fun i => AddSubgroup.subset_closure (s i).2) fun g => ?_
  have := congrFun hsum g
  rw [Finset.sum_apply] at this
  exact this
end GlobalTheory.BI
