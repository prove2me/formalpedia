-- Prove2me | solution 1 for MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c5ac6eab-57d6-5c7c-9079-cbb273cac391

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod

set_option autoImplicit false

noncomputable section

p2m_open "MvPolynomial P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod.MvPolynomial"

universe u v

namespace MvPolynomial
p2m_export "MvPolynomial" "X restrictSupport funext ext support basisRestrictSupport mem_ideal_span_monomial_image monomial coeff_zero mem_support_iff mem_supported mem_restrictSupport_iff X_pow_eq_monomial"
namespace TruncatedBox
p2m_open "MvPolynomial"

variable (k : Type u) [CommRing k] {ι : Type v} (N : ι → ℕ)

def box : Set (ι →₀ ℕ) := {m | ∀ i, m i < N i}

def K : Ideal (MvPolynomial ι k) :=
  Ideal.span (Set.range fun i : ι => (X i : MvPolynomial ι k) ^ N i)

theorem K_eq : K k N = Ideal.span ((fun s => monomial s (1 : k)) ''
    Set.range fun i : ι => Finsupp.single i (N i)) := by
  rw [K, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range ?_)
  funext i
  exact X_pow_eq_monomial

variable {k N}

theorem mem_K_iff (P : MvPolynomial ι k) : P ∈ K k N ↔ ∀ m ∈ P.support, m ∉ box N := by
  rw [K_eq, mem_ideal_span_monomial_image]
  refine forall₂_congr fun m _ => ?_
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hle⟩ hm
    have := hm i
    rw [Finsupp.single_le_iff] at hle
    omega
  · intro hm
    simp only [box, Set.mem_setOf_eq, not_forall, not_lt] at hm
    obtain ⟨i, hi⟩ := hm
    exact ⟨_, ⟨i, rfl⟩, Finsupp.single_le_iff.2 hi⟩

theorem mem_restrictSupport_iff (P : MvPolynomial ι k) :
    P ∈ restrictSupport k (box N) ↔ ∀ m ∈ P.support, m ∈ box N :=
  (MvPolynomial.mem_restrictSupport_iff k).trans Iff.rfl

theorem isCompl : IsCompl ((K k N).restrictScalars k) (restrictSupport k (box N)) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro P hK hbox
    rw [Submodule.restrictScalars_mem, mem_K_iff] at hK
    rw [mem_restrictSupport_iff] at hbox
    ext m
    rw [coeff_zero]
    by_contra hne
    have hm : m ∈ P.support := by rwa [MvPolynomial.mem_support_iff]
    exact hK m hm (hbox m hm)
  · rw [codisjoint_iff, eq_top_iff]
    rintro P -

    set P₁ : MvPolynomial ι k :=
      AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun m => m ∈ box N) (AddMonoidAlgebra.coeff P)) with hP₁
    set P₂ : MvPolynomial ι k :=
      AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun m => m ∉ box N) (AddMonoidAlgebra.coeff P)) with hP₂
    have hsum : P₁ + P₂ = P := by
      apply AddMonoidAlgebra.coeff_injective
      rw [AddMonoidAlgebra.coeff_add]
      exact Finsupp.filter_add_filter_not (AddMonoidAlgebra.coeff P) _
    rw [← hsum, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [Submodule.restrictScalars_mem, mem_K_iff]
      intro m hm
      have hm' : m ∈ (Finsupp.filter (fun m => m ∉ box N) (AddMonoidAlgebra.coeff P)).support := hm
      rw [Finsupp.support_filter, Finset.mem_filter] at hm'
      exact hm'.2
    · rw [mem_restrictSupport_iff]
      intro m hm
      have hm' : m ∈ (Finsupp.filter (fun m => m ∈ box N) (AddMonoidAlgebra.coeff P)).support := hm
      rw [Finsupp.support_filter, Finset.mem_filter] at hm'
      exact hm'.2

def boxEquiv [Fintype ι] : box N ≃ (∀ i, Fin (N i)) where
  toFun m := fun i => ⟨m.1 i, m.2 i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm fun i => (f i : ℕ), fun i => by
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact (f i).isLt⟩
  left_inv m := by
    ext i
    exact congrFun (Finsupp.coe_equivFunOnFinite_symm _) i
  right_inv f := by
    funext i
    exact Fin.ext (congrFun (Finsupp.coe_equivFunOnFinite_symm _) i)

variable (k N) in
theorem finrank_quotient [Nontrivial k] [Fintype ι] :
    Module.finrank k (MvPolynomial ι k ⧸ K k N) = ∏ i, N i := by
  have e₁ : (MvPolynomial ι k ⧸ (K k N).restrictScalars k) ≃ₗ[k] MvPolynomial ι k ⧸ K k N :=
    Submodule.Quotient.restrictScalarsEquiv k (K k N)
  have e₂ : (MvPolynomial ι k ⧸ (K k N).restrictScalars k) ≃ₗ[k] restrictSupport k (box N) :=
    Submodule.quotientEquivOfIsCompl _ _ isCompl
  rw [← e₁.finrank_eq, e₂.finrank_eq, Module.finrank_eq_nat_card_basis (basisRestrictSupport k (box N)),
    Nat.card_congr (boxEquiv (N := N)), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => Nat.card_fin (N i)

end MvPolynomial.TruncatedBox

theorem solution
    (k : Type u) [CommRing k] [Nontrivial k] {ι : Type v} [Fintype ι] (N : ι → ℕ) :
    Module.finrank k (MvPolynomial ι k ⧸
      Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k) ^ N i)) = ∏ i, N i :=
  MvPolynomial.TruncatedBox.finrank_quotient k N

end
end S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod
end P2MW
export P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod (solution)
