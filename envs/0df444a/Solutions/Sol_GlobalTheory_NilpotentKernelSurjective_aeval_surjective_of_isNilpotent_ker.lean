-- Prove2me | solution 1 for GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:25.906321+00:00
-- url     : https://prove2.me/submissions/6746f691-ea52-4c48-ae74-c262d59ff2a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Theorems.Thm_GlobalTheory_NilpotentKernelSurjective_pow_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NilpotentKernelSurjective
namespace GlobalTheory.NilpotentKernelSurjective
theorem _root_.solution :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A]
      [inst_2 : Algebra R A] (ε : A →ₐ[R] R), IsNilpotent (RingHom.ker ε) →
      ∀ {d : ℕ} (x : Fin d → A), (∀ (i : Fin d), x i ∈ RingHom.ker ε) →
      (∀ y ∈ RingHom.ker ε, ∃ (l : Fin d → R),
        y - ∑ i : Fin d, l i • x i ∈ RingHom.ker ε ^ (2 : ℕ)) →
      Function.Surjective (⇑(MvPolynomial.aeval x) : MvPolynomial (Fin d) R → A) := by
  intro R A _ _ _ ε hnil d x hx hspan
  set K : Ideal A := RingHom.ker ε with hK
  set S : Subalgebra R A := (MvPolynomial.aeval x).range with hS
  have hxS : ∀ i, x i ∈ S := fun i => ⟨MvPolynomial.X i, MvPolynomial.aeval_X x i⟩

  have h0 : ∀ y : A, ∃ s ∈ S, y - s ∈ K := by
    intro y
    refine ⟨algebraMap R A (ε y), S.algebraMap_mem _, ?_⟩
    rw [hK, RingHom.mem_ker]
    simp

  have h1 : ∀ y ∈ K, ∃ s ∈ S, s ∈ K ∧ y - s ∈ K ^ 2 := by
    intro y hy
    obtain ⟨l, hl⟩ := hspan y hy
    refine ⟨∑ i : Fin d, l i • x i, S.sum_mem fun i _ => S.smul_mem (hxS i) _,
      K.sum_mem fun i _ => K.smul_of_tower_mem _ (hx i), hl⟩

  have hall : ∀ k : ℕ, ∀ y : A, ∃ s ∈ S, y - s ∈ K ^ k := by
    intro k
    induction k with
    | zero => intro y; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro y
      obtain ⟨s, hsS, hs⟩ := ih y
      obtain ⟨t, htS, -, ht⟩ := pow_approx K S h0 h1 k (y - s) hs
      refine ⟨s + t, S.add_mem hsS htS, ?_⟩
      have hsplit : y - (s + t) = y - s - t := by ring
      rw [hsplit]
      exact ht
  obtain ⟨m, hm⟩ := hnil
  intro y
  obtain ⟨s, hsS, hs⟩ := hall m y
  rw [hm, Submodule.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hs
  obtain ⟨p, hp⟩ := hsS
  exact ⟨p, hp.trans hs.symm⟩
end GlobalTheory.NilpotentKernelSurjective
