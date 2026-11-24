-- Prove2me | solution 1 for GlobalTheory.mem_sq_localization_of_pderiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:36.422055+00:00
-- url     : https://prove2.me/submissions/ac5a561f-f36f-4e23-9a35-b8a05e713804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem
import Theorems.Thm_GlobalTheory_kerCotangentToTensor_injective_of_formallySmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by
  intro Λ _ _ _ σ _ Q _ hQ x hx hd
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  let R := Localization.AtPrime Q
  let F := ResidueField R
  let k := FractionRing Λ
  have hunit : ∀ a : nonZeroDivisors Λ, IsUnit (algebraMap Λ R a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply Λ (MvPolynomial σ Λ) R]
    exact IsLocalization.map_units R (M := Q.primeCompl)
      ⟨MvPolynomial.C a.1, fun h => nonZeroDivisors.coe_ne_zero a (hQ _ h)⟩
  letI : Algebra k R := (IsLocalization.lift (M := nonZeroDivisors Λ) (S := k) hunit).toAlgebra
  haveI : IsScalarTower Λ k R := IsScalarTower.of_algebraMap_eq
    (fun a => (IsLocalization.lift_eq (M := nonZeroDivisors Λ) (S := k) hunit a).symm)
  letI : Algebra k F := ((algebraMap R F).comp (algebraMap k R)).toAlgebra
  haveI : IsScalarTower k R F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ k F := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply Λ R F, IsScalarTower.algebraMap_apply Λ k R]; rfl)
  haveI : Algebra.EssFiniteType (MvPolynomial σ Λ) R := .of_isLocalization R Q.primeCompl
  haveI : Algebra.EssFiniteType Λ R := .comp Λ (MvPolynomial σ Λ) R
  haveI : Algebra.EssFiniteType R F := .of_surjective (Algebra.ofId R F) residue_surjective
  haveI : Algebra.EssFiniteType Λ F := .comp Λ R F
  haveI : Algebra.EssFiniteType k F := Algebra.EssFiniteType.of_comp Λ k F
  haveI : Algebra.FormallySmooth k F := Algebra.FormallySmooth.of_perfectField
  haveI : Algebra.FormallySmooth Λ k := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors Λ)
  haveI : Algebra.FormallySmooth Λ F := Algebra.FormallySmooth.comp Λ k F
  have hinj := kerCotangentToTensor_injective_of_formallySmooth Λ R F (residue_surjective)
  have hker : RingHom.ker (algebraMap R F) = maximalIdeal R := ker_residue
  have hmem : ∀ p ∈ Q, algebraMap (MvPolynomial σ Λ) R p ∈ RingHom.ker (algebraMap R F) := by
    intro p hp
    rw [hker]; exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q p).mpr hp
  have hym := hmem x hx
  have hD : KaehlerDifferential.D Λ (MvPolynomial σ Λ) x =
      ∑ s, MvPolynomial.pderiv s x • KaehlerDifferential.D Λ (MvPolynomial σ Λ) (MvPolynomial.X s) := by
    conv_lhs => rw [← (KaehlerDifferential.mvPolynomialBasis Λ σ).sum_repr (KaehlerDifferential.D Λ _ x)]
    simp [KaehlerDifferential.mvPolynomialBasis_repr_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  have h0 : KaehlerDifferential.kerCotangentToTensor Λ R F
      ((RingHom.ker (algebraMap R F)).toCotangent ⟨_, hym⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    rw [← KaehlerDifferential.map_D Λ Λ (MvPolynomial σ Λ) R, hD, map_sum, tmul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [LinearMap.map_smul_of_tower, ← algebraMap_smul R, ← smul_tmul, Algebra.smul_def, mul_one,
      RingHom.mem_ker.mp (hmem _ (hd s)), zero_tmul]
  have h2 : algebraMap (MvPolynomial σ Λ) R x ∈ RingHom.ker (algebraMap R F) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ _).mp (hinj (h0.trans (map_zero _).symm))
  rw [hker, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h2
  obtain ⟨m, hm, hmx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := R) _ _).mp h2
  exact ⟨m, hm, hmx⟩
end GlobalTheory
