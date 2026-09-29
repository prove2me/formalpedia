-- Prove2me | solution 1 for MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/35633979-e008-54e9-96b6-4485b8bbd566

import Mathlib
import Theorems.Thm_MvPolynomial_formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization
import Theorems.Thm_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective
import Theorems.Thm_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization
import Theorems.Thm_MvPolynomial_exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem

set_option autoImplicit false

open MvPolynomial IsLocalRing

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) [hJ : J.IsMaximal]
    (hJac : ∀ v ∈ I, (∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) → v ∈ J * I) :
    haveI : (J.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact hIJ)
    Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) := by
  classical
  haveI h𝔮 : (J.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIJ)
  show Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))

  letI icr : CommRing ((MvPolynomial (Fin n) R) ⧸ I) := Ideal.Quotient.commRing I
  have hJq : J = (J.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hIJ]
  haveI h𝔮max : (J.map (Ideal.Quotient.mk I)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hJ with h | h
    · exfalso; apply hJ.ne_top; rw [hJq, h, Ideal.comap_top]
    · exact h

  let lh : Localization.AtPrime J →+* Localization.AtPrime (J.map (Ideal.Quotient.mk I)) :=
    Localization.localRingHom J (J.map (Ideal.Quotient.mk I)) (Ideal.Quotient.mk I) hJq
  letI algPS : Algebra (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) := lh.toAlgebra
  have hlh : ∀ a : (MvPolynomial (Fin n) R), lh (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J) a) =
      algebraMap ((MvPolynomial (Fin n) R) ⧸ I) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) (Ideal.Quotient.mk I a) :=
    fun a => Localization.localRingHom_to_map _ _ _ hJq a
  haveI : IsScalarTower R (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization.AtPrime J) (A := Localization.AtPrime (J.map (Ideal.Quotient.mk I))) fun r => by
      rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) (Localization.AtPrime J), hlh,
        ← RingHom.comp_apply (Ideal.Quotient.mk I) (algebraMap R (MvPolynomial (Fin n) R)), Ideal.Quotient.mk_comp_algebraMap,
        ← IsScalarTower.algebraMap_apply R ((MvPolynomial (Fin n) R) ⧸ I) (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))]
  letI algPK : Algebra (Localization.AtPrime J) (J.map (Ideal.Quotient.mk I)).ResidueField :=
    ((IsLocalRing.residue (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))).comp lh).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) (J.map (Ideal.Quotient.mk I)).ResidueField :=
    IsScalarTower.of_algebraMap_eq (R := Localization.AtPrime J) (S := Localization.AtPrime (J.map (Ideal.Quotient.mk I)))
      (A := (J.map (Ideal.Quotient.mk I)).ResidueField) fun x => rfl
  letI algP0K : Algebra (MvPolynomial (Fin n) R) (J.map (Ideal.Quotient.mk I)).ResidueField :=
    ((algebraMap (Localization.AtPrime J) (J.map (Ideal.Quotient.mk I)).ResidueField).comp
      (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin n) R) (Localization.AtPrime J) (J.map (Ideal.Quotient.mk I)).ResidueField :=
    IsScalarTower.of_algebraMap_eq (R := (MvPolynomial (Fin n) R)) (S := Localization.AtPrime J)
      (A := (J.map (Ideal.Quotient.mk I)).ResidueField) fun x => rfl
  have hK0 : ∀ a : (MvPolynomial (Fin n) R), algebraMap (MvPolynomial (Fin n) R) (J.map (Ideal.Quotient.mk I)).ResidueField a =
      IsLocalRing.residue _ (algebraMap ((MvPolynomial (Fin n) R) ⧸ I) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) (Ideal.Quotient.mk I a)) := by
    intro a
    show IsLocalRing.residue _ (lh (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J) a)) = _
    rw [hlh]
  have hK : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) (J.map (Ideal.Quotient.mk I)).ResidueField) := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (J.map (Ideal.Quotient.mk I)) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by rw [hK0]; rfl⟩
  have hJK : ∀ j ∈ J, algebraMap (MvPolynomial (Fin n) R) (J.map (Ideal.Quotient.mk I)).ResidueField j = 0 := by
    intro j hj
    rw [hK0, IsLocalRing.residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hj)
  have hKker : ∀ a : (MvPolynomial (Fin n) R), algebraMap (MvPolynomial (Fin n) R) (J.map (Ideal.Quotient.mk I)).ResidueField a = 0 → a ∈ J := by
    intro a ha
    rw [hK0, IsLocalRing.residue_eq_zero_iff] at ha
    have : Ideal.Quotient.mk I a ∈ Ideal.under ((MvPolynomial (Fin n) R) ⧸ I) (maximalIdeal (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))) := ha
    rw [Localization.AtPrime.under_maximalIdeal] at this
    rw [hJq]; exact this

  obtain ⟨hFSP, hFree, hFin⟩ := MvPolynomial.formallySmooth_and_free_and_finite_kaehlerDifferential_of_isLocalization R J.primeCompl (Localization.AtPrime J)
  haveI := hFSP; haveI := hFree; haveI := hFin
  obtain ⟨hsurj, hker⟩ := Localization.localRingHom_surjective_and_ker_eq_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J (J.map (Ideal.Quotient.mk I)) hJq
  have hsurj' : Function.Surjective (algebraMap (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))) := hsurj
  have h𝔞 : RingHom.ker (algebraMap (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))) =
      I.map (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J)) := by
    show RingHom.ker lh = _
    rw [hker, Ideal.mk_ker]
  have h₃ : maximalIdeal (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) ≤
      RingHom.ker (algebraMap (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) (J.map (Ideal.Quotient.mk I)).ResidueField) := by
    show maximalIdeal _ ≤ RingHom.ker (IsLocalRing.residue _)
    rw [IsLocalRing.ker_residue]
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (Localization.AtPrime J)
    (J.map (Ideal.Quotient.mk I)).ResidueField hsurj' (IsNoetherian.noetherian _) h₃]

  obtain ⟨hgen, hzero⟩ := Ideal.exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization R J.primeCompl (Localization.AtPrime J) I J
    (RingHom.ker (algebraMap (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))))) h𝔞
    (J.map (Ideal.Quotient.mk I)).ResidueField hK hJK
  obtain ⟨e, he⟩ := MvPolynomial.exists_tensor_kaehlerDifferential_linearEquiv_pi_of_isLocalization R J.primeCompl (Localization.AtPrime J) (J.map (Ideal.Quotient.mk I)).ResidueField

  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨c, a, ha, rfl⟩ := hgen z
  by_cases hc : c = 0
  · rw [hc, zero_smul]
  have h1 := congrArg e hz
  rw [map_zero, LinearMap.map_smul, KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
    KaehlerDifferential.kerToTensor_apply, LinearEquiv.map_smul] at h1
  have h2 : e ((1 : (J.map (Ideal.Quotient.mk I)).ResidueField) ⊗ₜ[Localization.AtPrime J]
      KaehlerDifferential.D R (Localization.AtPrime J) (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J) a)) =
      fun i => algebraMap (MvPolynomial (Fin n) R) (J.map (Ideal.Quotient.mk I)).ResidueField (MvPolynomial.pderiv i a) := he a
  have hall : ∀ i : Fin n, MvPolynomial.pderiv i a ∈ J := by
    intro i
    apply hKker
    have := congrFun h1 i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h hc
    · rw [h2] at h
      exact h
  have hmem : a ∈ J * I := hJac a ha hall
  have h0 := hzero a hmem
  rw [show (⟨algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J) a, h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J)) ha⟩ :
      ↥(RingHom.ker (algebraMap (Localization.AtPrime J) (Localization.AtPrime (J.map (Ideal.Quotient.mk I)))))) =
      ⟨algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J) a, h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime J)) (Ideal.mul_le_right hmem)⟩ from rfl,
    h0, smul_zero]

end S_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
end P2MW
export P2MW.S_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem (solution)
