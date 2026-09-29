-- Prove2me | solution 1 for MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/88d70e45-f16a-51c2-8abc-91d0c2a97e27

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
import Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzNumber

variable {n : ℕ}

theorem finite_homogeneousSubmodule (A : Type) [CommRing A] (d : ℕ) :
    Module.Finite A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem natCard_degree_eq (d : ℕ) : Nat.card {s : Fin (n + 1) →₀ ℕ // s.degree = d} = (n + d).choose n := by
  classical
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} ≃ Sym (Fin (n + 1)) d :=
    { toFun := fun s => ⟨Finsupp.toMultiset s.1, by
        have h2 := s.2
        rw [Finsupp.degree_apply] at h2
        rw [Finsupp.card_toMultiset]
        simpa [Finsupp.sum] using h2⟩
      invFun := fun t => ⟨Multiset.toFinsupp (t : Multiset (Fin (n + 1))), by
        have h1 := Finsupp.card_toMultiset (Multiset.toFinsupp (t : Multiset (Fin (n + 1))))
        rw [Multiset.toFinsupp_toMultiset] at h1
        rw [Finsupp.degree_apply]
        have h2 : (t : Multiset (Fin (n + 1))).card = d := t.2
        simpa [Finsupp.sum, h2] using h1.symm⟩
      left_inv := fun s => by
        apply Subtype.ext
        simp
      right_inv := fun t => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

theorem finrank_homogeneousSubmodule (A : Type) [CommRing A] [Nontrivial A] (d : ℕ) :
    Module.finrank A ↥(homogeneousSubmodule (Fin (n + 1)) A d) = (n + d).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})).trans (natCard_degree_eq d)

theorem finrank_piece_le (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (d : ℕ) :
    Module.finrank K (piece J d) ≤ (n + d).choose n := by
  haveI := finite_homogeneousSubmodule (n := n) K d
  rw [← finrank_homogeneousSubmodule (n := n) K d]
  exact Submodule.finrank_quotient_le _

theorem decompose_eq {A : Type} [CommRing A] (q : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) q d : MvPolynomial (Fin (n + 1)) A) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem span_homogeneous (A : Type) [CommRing A] (s : Set (MvPolynomial (Fin (n + 1)) A)) (m : ℕ)
    (hs : ∀ p ∈ s, p.IsHomogeneous m) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) A) s (fun x hx => ⟨m, hs x hx⟩)
  have := H d hp
  rwa [decompose_eq] at this

end GotzNumber

open GotzNumber in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ e : ℕ, D₀ ≤ e →
      (∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) →
        (Module.finrank K (piece J (e + 1)) : ℚ) ≤ P.eval ((e : ℚ) + 1)) ∧
      ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
        (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
        (Module.finrank K (piece J e) : ℚ) = P.eval (e : ℚ) ∧
        (Module.finrank K (piece J (e + 1)) : ℚ) = P.eval ((e : ℚ) + 1) := by
  obtain ⟨K₀, _, I₀, hI₀, d₁, hHP⟩ := hP

  set H : ℕ → ℕ := fun d => Module.finrank K₀ (piece I₀ d) with hH
  have hMac : ∀ d, 1 ≤ d → H (d + 1) ≤ Nat.macaulayPow d (H d) := fun d hd =>
    MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K₀ I₀ hI₀
  obtain ⟨D₁, hD₁⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow H 1 le_rfl hMac
  refine ⟨max (max D₁ d₁) 1, fun e he => ?_⟩
  have heD₁ : D₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) he
  have hed₁ : d₁ ≤ e := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) he
  have he1 : 1 ≤ e := le_trans (le_max_right _ _) he
  have hHe : (H e : ℚ) = P.eval (e : ℚ) := hHP e hed₁
  have hHe1 : (H (e + 1) : ℚ) = P.eval ((e : ℚ) + 1) := by
    have := hHP (e + 1) (Nat.le_succ_of_le hed₁)
    simpa [Nat.cast_succ] using this
  have hgrow : H (e + 1) = Nat.macaulayPow e (H e) := hD₁ e heD₁
  refine ⟨?_, ?_⟩
  ·
    intro K _ J hJ hJe
    obtain ⟨s, hs, rfl⟩ := hJ
    have hJhom := span_homogeneous K s e hs
    have hfin : Module.finrank K (piece (Ideal.span s) e) = H e := by
      have : ((Module.finrank K (piece (Ideal.span s) e) : ℕ) : ℚ) = (H e : ℚ) := by rw [hJe, hHe]
      exact_mod_cast this
    have hle := MvPolynomial.finrank_piece_succ_le_macaulayPow n e he1 K (Ideal.span s) hJhom
    rw [hfin, ← hgrow] at hle
    rw [← hHe1]
    exact_mod_cast hle
  ·
    have ha : H e ≤ (n + e).choose n := finrank_piece_le K₀ I₀ e
    obtain ⟨J, hJ, hJe, hJe1⟩ :=
      MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
        n e he1 (H e) ha K₀
    refine ⟨K₀, ‹Field K₀›, J, hJ, ?_, ?_⟩
    · rw [hJe, hHe]
    · rw [hJe1, ← hgrow, hHe1]

end S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
end P2MW
export P2MW.S_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval (solution)
