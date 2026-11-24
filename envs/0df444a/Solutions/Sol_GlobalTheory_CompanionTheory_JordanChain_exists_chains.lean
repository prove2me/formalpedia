-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.JordanChain.exists_chains
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:32.989026+00:00
-- url     : https://prove2.me/submissions/2a4ae8bf-791b-4ab8-bdf9-41b814036b0d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
import Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_pow_coe_of_restrict
import Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_exists_chains_of_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JordanChain
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.CompanionTheory.JordanChain
theorem _root_.solution : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hn hf
    by_cases hV : Subsingleton V
    · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun a => a.elim, fun a => a.elim,
        ?_, Subsingleton.elim _ _⟩
      exact linearIndependent_empty_type
    · have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
      obtain ⟨m, hm⟩ := hf
      have hlt : finrank K (LinearMap.range f) < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro htop
        have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
        have hs : Function.Surjective (f ^ m) := by
          rw [Module.End.coe_pow]
          exact hsurj.iterate m
        rw [hm] at hs
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ := hs x
        exact hx (by simpa using hy.symm)
      let g : LinearMap.range f →ₗ[K] LinearMap.range f :=
        f.restrict (fun x _ => LinearMap.mem_range_self f x)
      have hg : ∀ x, (g x : V) = f x := fun x => rfl
      have hgn : IsNilpotent g := by
        refine ⟨m, LinearMap.ext fun x => Subtype.ext ?_⟩
        rw [pow_coe_of_restrict f g hg, hm]
        rfl
      obtain ⟨ι', _, e', w, he', h0, hli, hsp⟩ := ih _ hlt (LinearMap.range f) g rfl hgn
      exact exists_chains_of_range f g hg e' he' w h0 hli hsp
end GlobalTheory.CompanionTheory.JordanChain
