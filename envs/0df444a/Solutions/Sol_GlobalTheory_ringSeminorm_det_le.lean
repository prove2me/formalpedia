-- Prove2me | solution 1 for GlobalTheory.ringSeminorm_det_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:21.608531+00:00
-- url     : https://prove2.me/submissions/990d7108-af45-4ff3-a70c-8981fd22325e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
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
private theorem ringSeminorm_prod_le {κ : Type*} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (s : Finset κ) (x : κ → R) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∏ k ∈ s, x k) ≤ C ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.card_insert_of_notMem hk, pow_succ']
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    exact (map_mul_le_mul ν _ _).trans
      (mul_le_mul h2 h3 (apply_nonneg ν _) ((apply_nonneg ν _).trans h2))
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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : RingSeminorm R)
    (h1 : ν 1 ≤ 1) (H : Matrix ι ι R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C) :
    ν H.det ≤ (Fintype.card ι)! * C ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  have := seminorm_sum_le ν.toAddGroupSeminorm Finset.univ
    (fun σ : Equiv.Perm ι => Equiv.Perm.sign σ • ∏ i, H (σ i) i) (C := C ^ Fintype.card ι) (by
      intro σ _
      have h := ringSeminorm_prod_le ν h1 Finset.univ (fun i => H (σ i) i) fun i _ => hH _ _
      rw [Finset.card_univ] at h
      change ν _ ≤ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]; exact h
      · rw [hs, Units.neg_smul, one_smul, map_neg_eq_map]; exact h)
  rwa [Finset.card_univ, Fintype.card_perm] at this
end GlobalTheory
