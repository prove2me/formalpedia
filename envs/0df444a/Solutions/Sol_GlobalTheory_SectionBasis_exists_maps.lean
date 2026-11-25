-- Prove2me | solution 1 for GlobalTheory.SectionBasis.exists_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:24.473336+00:00
-- url     : https://prove2.me/submissions/d3290867-c8ab-4f01-9afe-6f16611601e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_sHom_eq
import Theorems.Thm_GlobalTheory_SectionBasis_polyImg_freeVar
import Theorems.Thm_GlobalTheory_SectionBasis_sum_polyImg_succ
import Theorems.Thm_GlobalTheory_SectionBasis_sum_polyImg_zero
import Theorems.Thm_GlobalTheory_SectionBasis_exists_dvd
import Theorems.Thm_GlobalTheory_GenericSection_polyImg_same
import Theorems.Thm_GlobalTheory_GenericSection_polyImg_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}
namespace GlobalTheory.SectionBasis
theorem _root_.solution (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (t : TVar D N → K') (ht : AlgebraicIndependent K t)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    [FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    (hL : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom j0 x q)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) K']
    (hK : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) K' (algebraMap (MvPolynomial (TVar D N) K) _ q) = aeval t q)
    {Q : Type} [CommRing Q] (a : K' →+* Q) (ψ : Ω →+* Q)
    (hc : ∀ c : K, ψ (algebraMap K Ω c) = a (algebraMap K K' c))
    (hrel : ∀ i : Fin D, ∑ j, a (t (i.succ, j)) * ψ (v j) = 0)
    (huniv : ∀ (R : Type) [CommRing R] (a' : K' →+* R) (ψ' : Ω →+* R),
      (∀ c : K, ψ' (algebraMap K Ω c) = a' (algebraMap K K' c)) → IsUnit (∑ j, a' (t (0, j)) * ψ' (v j)) →
      (∀ i : Fin D, ∑ j, a' (t (i.succ, j)) * ψ' (v j) = 0) →
      ∃ g : Q →+* R, (∀ y, g (a y) = a' y) ∧ ∀ ω, g (ψ ω) = ψ' ω) :
    ∃ β : OmS Ω D N →+* Q, (∀ q : MvPolynomial (TVar D N) K, β (sHom j0 x q) = a (aeval t q)) ∧ (∀ ω, β (algebraMap Ω _ ω) = ψ ω) ∧
      ∃ α : Q →+* K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N,
        (∀ y, α (a y) = algebraMap K' _ y) ∧ Function.Surjective α := by
  let β₀ : MvPolynomial (SVar D N) Ω →+* Q := eval₂Hom ψ fun s => a (t (freeVar j0 s))
  have hX : ∀ s, β₀ (X s) = a (t (freeVar j0 s)) := fun s => eval₂Hom_X' _ _ _
  have hC : ∀ ω, β₀ (C ω) = ψ ω := fun ω => eval₂Hom_C _ _ _
  have hp : ∀ p, β₀ (polyImg j0 x p) = a (t p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [polyImg_same, if_pos rfl, hX]; rfl
      · have h1 := congrArg β₀ (sum_polyImg_succ j v x hv hx i)
        have h2 := hrel i
        rw [map_sum, map_zero, Fin.sum_univ_succAbove _ j] at h1
        rw [Fin.sum_univ_succAbove _ j] at h2
        simp only [map_mul, hC, polyImg_succAbove, hX] at h1
        have h3 : β₀ (polyImg j x (i.succ, j)) * ψ (v j) = a (t (i.succ, j)) * ψ (v j) :=
          add_right_cancel (h1.trans h2.symm)
        exact ((isUnit_iff_ne_zero.2 hv).map ψ).mul_right_cancel h3
    · rw [polyImg_succAbove, hX]; rfl
  have hq : ∀ q : MvPolynomial (TVar D N) K, β₀ (aeval (polyImg j0 x) q) = a (aeval t q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => rw [aeval_C, aeval_C, MvPolynomial.algebraMap_apply, hC, hc]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X q n hq => simp only [map_mul, aeval_X, hq, hp]
  have hunit : ∀ y : nonZeroDivisors (MvPolynomial (SVar D N) Ω), IsUnit (β₀ y) := by
    intro y
    obtain ⟨q, hq0, hd⟩ := exists_dvd j0 x hL y.1 (nonZeroDivisors.ne_zero y.2)
    have h1 := map_dvd β₀ hd
    rw [hq] at h1
    refine isUnit_of_dvd_unit h1 ((isUnit_iff_ne_zero.2 fun h => hq0 ?_).map a)
    exact algebraicIndependent_iff.mp ht q h
  let β : OmS Ω D N →+* Q := IsLocalization.lift hunit
  have hβ : ∀ f, β (algebraMap (MvPolynomial (SVar D N) Ω) _ f) = β₀ f := fun f => IsLocalization.lift_eq _ _
  have hΩ : ∀ ω : Ω, algebraMap Ω (OmS Ω D N) ω = algebraMap (MvPolynomial (SVar D N) Ω) _ (C ω) := fun ω =>
    IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) _ ω
  refine ⟨β, fun q => by rw [sHom_eq, hβ, hq], fun ω => by rw [hΩ, hβ, hC], ?_⟩
  let iR : OmS Ω D N →+* K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N :=
    (Algebra.TensorProduct.includeRight :
      OmS Ω D N →ₐ[FractionRing (MvPolynomial (TVar D N) K)] _).toRingHom
  have hT : ∀ q : MvPolynomial (TVar D N) K,
      algebraMap K' (K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N) (aeval t q) = iR (sHom j0 x q) := by
    intro q
    rw [← hL, ← hK, ← IsScalarTower.algebraMap_apply]
    exact (AlgHom.commutes _ _).symm
  have hTX : ∀ p, algebraMap K' (K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N) (t p) =
      iR (algebraMap (MvPolynomial (SVar D N) Ω) _ (polyImg j0 x p)) := by
    intro p
    have := hT (X p)
    rwa [sHom_eq, aeval_X, aeval_X] at this
  have hsum : ∀ i, ∑ j, algebraMap K' (K' ⊗[FractionRing (MvPolynomial (TVar D N) K)] OmS Ω D N) (t (i, j)) *
      (iR.comp (algebraMap Ω _)) (v j) =
      iR (algebraMap (MvPolynomial (SVar D N) Ω) _ (∑ j, polyImg j0 x (i, j) * C (v j))) := by
    intro i
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hTX, RingHom.comp_apply, hΩ, map_mul, map_mul]
  obtain ⟨α, hα1, hα2⟩ := huniv _ (algebraMap K' _) (iR.comp (algebraMap Ω _))
    (fun c => by
      have := hT (C c)
      rw [aeval_C, sHom, aeval_C, IsScalarTower.algebraMap_apply K Ω (OmS Ω D N)] at this
      exact this.symm)
    (by
      rw [hsum]
      refine (isUnit_iff_ne_zero.2 ?_).map iR
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact sum_polyImg_zero j0 v x hv hx)
    (fun i => by rw [hsum, sum_polyImg_succ j0 v x hv hx, map_zero, map_zero])
  refine ⟨α, hα1, ?_⟩
  have hαβ : α.comp β = iR := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (SVar D N) Ω)) ?_
    refine MvPolynomial.ringHom_ext (fun ω => ?_) (fun s => ?_)
    · simp only [RingHom.comp_apply]
      rw [hβ, hC, hα2, RingHom.comp_apply, hΩ]
    · simp only [RingHom.comp_apply]
      rw [hβ, hX, hα1, hTX, polyImg_freeVar]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add y z hy hz =>
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨z, rfl⟩ := hz
    exact ⟨y + z, map_add _ _ _⟩
  | tmul b y =>
    refine ⟨a b * β y, ?_⟩
    rw [map_mul, hα1, ← RingHom.comp_apply α β, hαβ, Algebra.TensorProduct.algebraMap_apply]
    show (_ ⊗ₜ _) * ((1 : K') ⊗ₜ y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp
end GlobalTheory.SectionBasis
