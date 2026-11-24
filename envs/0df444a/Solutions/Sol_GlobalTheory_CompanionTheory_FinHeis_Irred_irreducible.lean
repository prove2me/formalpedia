-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Irred.irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:15.542803+00:00
-- url     : https://prove2.me/submissions/7c22ec20-c302-43f2-bebd-201cb97fb899

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_mem_of_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.Irred
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
namespace GlobalTheory.CompanionTheory.FinHeis.Irred
theorem _root_.solution : ∀ {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
    (al : X → ℂ) (Γ : AddSubgroup X) (φ : M), SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ →
    Cyclic S φ →
    (∀ N : Submodule ℂ M, (∀ x, ∀ v ∈ N, S.rho x v ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ v : M, v ≠ 0 → Cyclic S v := by
  intro X M _ _ _ S al Γ φ hd hs hl hc
  have main : ∀ N : Submodule ℂ M, (∀ x, ∀ v ∈ N, S.rho x v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    rw [or_iff_not_imp_left]
    intro hb
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have hmem : v ∈ Submodule.span ℂ (Set.range fun x => S.rho x φ) := by
      rw [hc]; trivial
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
    have hφ : φ ∈ N := by
      refine mem_of_sum S hd hs hl N hN f.support f ?_ ?_
      · rw [← hf] at hv
        exact hv
      · exact fun h => hv0 (hf.symm.trans h)
    rw [eq_top_iff, ← hc, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hN x φ hφ
  refine ⟨main, fun v hv => ?_⟩
  have hinv : ∀ x, ∀ w ∈ Submodule.span ℂ (Set.range fun x => S.rho x v),
      S.rho x w ∈ Submodule.span ℂ (Set.range fun x => S.rho x v) := by
    intro x w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, rfl⟩ := hw
      show S.rho x (S.rho y v) ∈ _
      rw [S.rho_rho]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  rcases main _ hinv with h | h
  · exfalso
    have : v ∈ Submodule.span ℂ (Set.range fun x => S.rho x v) :=
      Submodule.subset_span ⟨0, S.rho_zero v⟩
    rw [h] at this
    exact hv this
  · exact h
end GlobalTheory.CompanionTheory.FinHeis.Irred
