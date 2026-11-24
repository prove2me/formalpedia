-- Prove2me | solution 1 for GlobalTheory.seminorm_perpVector_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:51.011399+00:00
-- url     : https://prove2.me/submissions/becdb4b7-bd28-4ce9-a52f-7deb6b18bbda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
import Theorems.Thm_GlobalTheory_ringSeminorm_det_le
import Theorems.Thm_GlobalTheory_ringSeminorm_adjugate_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply
section
open scoped BigOperators Nat
namespace GlobalTheory
section Covector
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
section Integral
variable {A : Type*} [CommRing A] [Algebra A R]
end Integral
end Covector
section Size
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
private theorem seminorm_sum_le {G κ : Type*} [AddCommGroup G] (ν : AddGroupSeminorm G)
    (s : Finset κ) (x : κ → G) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∑ k ∈ s, x k) ≤ s.card * C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.card_insert_of_notMem hk]
    have h1 := map_add_le_add ν (x k) (∑ k ∈ s, x k)
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    push_cast
    linarith
end Size
section Degree
open MvPolynomial
variable {S τ : Type*} [CommRing S]
end Degree
section Form
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}
end Form
section InnerProduct
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]
end InnerProduct
section Places
variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
end Places
end GlobalTheory
end

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (ε : Fin p → Module.Dual R M) (e' : Fin p → M) (g : M) {C r : ℝ}
    (he : ∀ a a', ν (ε a (e' a')) ≤ C) (hg : ∀ a, ν (ε a g) ≤ C)
    (he' : ∀ a, μ (e' a) ≤ r) (hgr : μ g ≤ r) :
    μ (perpVector ε e' g) ≤ (p + 1)! * C ^ p * r := by
  have hdet := ringSeminorm_det_le ν h1 (pairingMatrix ε e') (C := C) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  have hA : μ ((pairingMatrix ε e').det • g) ≤ p ! * C ^ p * r :=
    (hsmul _ _).trans (mul_le_mul hdet hgr (apply_nonneg μ _) ((apply_nonneg ν _).trans hdet))
  have hB : μ (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
      ≤ p * (p ! * C ^ p * r) := by
    cases p with
    | zero => simp
    | succ n =>
      have h := seminorm_sum_le μ Finset.univ
        (fun a => ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
        (C := ((n + 1 : ℕ) : ℝ) * (n ! * C ^ n * C * r)) (by
          intro a _
          have h' := seminorm_sum_le μ Finset.univ
            (fun a' => ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
            (C := n ! * C ^ n * C * r) (by
              intro a' _
              have hadj := ringSeminorm_adjugate_le ν h1 (pairingMatrix ε e') (C := C)
                (fun i j => he j i) a a'
              have hm : ν ((pairingMatrix ε e').adjugate a a' * ε a g) ≤ n ! * C ^ n * C :=
                (map_mul_le_mul ν _ _).trans
                  (mul_le_mul hadj (hg a) (apply_nonneg ν _) ((apply_nonneg ν _).trans hadj))
              exact (hsmul _ _).trans
                (mul_le_mul hm (he' a') (apply_nonneg μ _) ((apply_nonneg ν _).trans hm)))
          rwa [Finset.card_univ, Fintype.card_fin] at h')
      rw [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]; push_cast; ring
  have hsub := map_sub_le_add μ ((pairingMatrix ε e').det • g)
    (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
  rw [perpVector, Nat.factorial_succ]
  push_cast
  linarith
end GlobalTheory
