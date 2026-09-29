-- Prove2me | solution 1 for IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7def66ab-958d-513c-83bd-fc3233729f6c

import Mathlib
import Theorems.Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem solution
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
    (S : Finset E) (hS : (0 : E) ∉ S) :
    ∃ (A : ValuationSubring E) (hK : ∀ c : K, algebraMap K E c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      (∀ c : K, σ ⟨algebraMap K E c, hK c⟩ = c) ∧
      ∀ s ∈ S, A.valuation s = 1 := by
  classical

  let T : Finset E := S ∪ S.image (·⁻¹)
  let R : Subalgebra K E := Algebra.adjoin K (↑T : Set E)
  have hSmemR : ∀ s ∈ S, (s : E) ∈ R := fun s hs =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _ hs))
  have hSinvR : ∀ s ∈ S, (s⁻¹ : E) ∈ R := fun s hs =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)))

  have hRFG : R.FG := ⟨T, rfl⟩
  haveI : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).mp hRFG

  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  haveI := hm
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (R := K) (A := R)
      (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  haveI : Algebra.IsIntegral K (R ⧸ m) := Algebra.IsIntegral.of_finite K (R ⧸ m)
  have hsurj : Function.Surjective (algebraMap K (R ⧸ m)) := by
    intro x
    have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    exact minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  let e : K ≃+* (R ⧸ m) :=
    RingEquiv.ofBijective (algebraMap K (R ⧸ m)) ⟨(algebraMap K _).injective, hsurj⟩
  let φ : R →+* K := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have hφK : ∀ c : K, φ (algebraMap K R c) = c := fun c => by
    show e.symm (Ideal.Quotient.mk m (algebraMap K R c)) = c
    have h1 : (Ideal.Quotient.mk m) (algebraMap K R c) = algebraMap K (R ⧸ m) c := rfl
    rw [h1]; exact e.symm_apply_apply c

  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) R.toSubring φ
  have hKO : ∀ c : K, algebraMap K E c ∈ O := fun c => hRO (R.algebraMap_mem c)
  refine ⟨O, hKO, ψ, hker, ?_, ?_⟩
  · intro c
    have h0 : (⟨algebraMap K E c, hKO c⟩ : O)
        = Subring.inclusion hRO ⟨algebraMap K E c, R.algebraMap_mem c⟩ := rfl
    rw [h0, ← RingHom.comp_apply, hψ]
    exact hφK c
  ·
    intro s hs
    have hs0 : s ≠ 0 := fun h => hS (h ▸ hs)
    have hsO : s ∈ O := hRO (hSmemR s hs)
    have hsiO : s⁻¹ ∈ O := hRO (hSinvR s hs)
    have hsu : IsUnit (⟨s, hsO⟩ : O) :=
      ⟨⟨⟨s, hsO⟩, ⟨s⁻¹, hsiO⟩,
          Subtype.ext (mul_inv_cancel₀ hs0), Subtype.ext (inv_mul_cancel₀ hs0)⟩, rfl⟩
    exact (O.valuation_eq_one_iff ⟨s, hsO⟩).mp hsu

end S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
end P2MW
export P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one (solution)
