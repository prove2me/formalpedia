-- Prove2me | solution 1 for GlobalTheory.QFam.exists_perm_of_sum_monomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:57:40.779604+00:00
-- url     : https://prove2.me/submissions/a26e4c9f-ff71-45c7-88a4-0f04260487d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMvPolynomialPickPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEq
import Theorems.Thm_GlobalTheory_QFam_sum_eval_eq_of_sum_monomial_eq
import Theorems.Thm_GlobalTheory_QFam_exists_mvPolynomial_pick_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution :
    ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ),
      (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) →
      ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  classical
  intro ι S _ _ x y h
  have hcard : ∀ p : S → ℂ, Fintype.card {i // x i = p} = Fintype.card {i // y i = p} := by
    intro p
    obtain ⟨Q, hQ1, hQ0⟩ := exists_mvPolynomial_pick_point S
      (Finset.univ.image x ∪ Finset.univ.image y) p
    have key : ∀ z : ι → S → ℂ, (∀ i, z i ∈ Finset.univ.image x ∪ Finset.univ.image y) →
        ∑ i, MvPolynomial.eval (z i) Q = (Fintype.card {i // z i = p} : ℂ) := by
      intro z hz
      have : ∀ i, MvPolynomial.eval (z i) Q = if z i = p then 1 else 0 := by
        intro i
        split_ifs with hi
        · rw [hi, hQ1]
        · exact hQ0 _ (hz i) hi
      simp only [this]
      rw [Finset.sum_boole, Fintype.card_subtype]
    have h1 := key x (fun i => by simp)
    have h2 := key y (fun i => by simp)
    have h3 := sum_eval_eq_of_sum_monomial_eq x y h Q
    rw [h1, h2] at h3
    exact_mod_cast h3
  refine ⟨Equiv.ofFiberEquiv (f := x) (g := y) (fun p => Fintype.equivOfCardEq (hcard p)),
    fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm
end GlobalTheory.QFam
