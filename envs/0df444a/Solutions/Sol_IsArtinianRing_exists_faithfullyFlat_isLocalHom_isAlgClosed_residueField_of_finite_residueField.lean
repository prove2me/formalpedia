-- Prove2me | solution 1 for IsArtinianRing.exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2321c6b5-d212-51fb-87ad-f43efb680f63

import Mathlib
import Theorems.Thm_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField
import Theorems.Thm_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal
import Theorems.Thm_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing
import Theorems.Thm_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField
import Theorems.Thm_WittVector_exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField

set_option autoImplicit false

open IsLocalRing

open scoped TensorProduct

theorem solution
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D) (ℓ : ℕ) (_ : Fact ℓ.Prime),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D) ∧ CharP (ResidueField D) ℓ := by
  classical

  obtain ⟨ℓ, hℓ⟩ := CharP.exists (ResidueField C)
  haveI := hℓ
  have hℓprime : ℓ.Prime :=
    (CharP.char_is_prime_or_zero (ResidueField C) ℓ).resolve_right (CharP.char_ne_zero_of_finite (ResidueField C) ℓ)
  haveI hF : Fact ℓ.Prime := ⟨hℓprime⟩
  haveI : CharP (AlgebraicClosure (ZMod ℓ)) ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))).injective ℓ

  obtain ⟨O, iR, iD, iV, iZ, iA, iC, hmax, e, -⟩ :=
    WittVector.exists_isDiscreteValuationRing_charZero_residueField_ringEquiv_and_sq_eq_of_isAlgClosed ℓ (AlgebraicClosure (ZMod ℓ))
  letI : CommRing O := iR
  haveI : IsDomain O := iD
  haveI : IsDiscreteValuationRing O := iV
  haveI : CharZero O := iZ
  letI : Algebra ℤ_[ℓ] O := iA
  have hmax' : (Ideal.span {((ℓ : ℕ) : O)}).IsMaximal := by
    have : algebraMap ℤ_[ℓ] O (ℓ : ℤ_[ℓ]) = ((ℓ : ℕ) : O) := map_natCast _ ℓ
    rw [← this]; exact hmax
  have hℓO : maximalIdeal O = Ideal.span {((ℓ : ℕ) : O)} := (IsLocalRing.eq_maximalIdeal hmax').symm
  have hac : IsAlgClosed (ResidueField O) := IsAlgClosed.of_ringEquiv (AlgebraicClosure (ZMod ℓ)) _ e.symm

  obtain ⟨hflat, -, hnoeth, hnil⟩ := IsArtinianRing.flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField C O
  obtain ⟨hred, hart, hnt⟩ := IsArtinianRing.isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal ℓ C O hmax'
  haveI := hflat; haveI := hnoeth; haveI := hred; haveI := hart; haveI := hnt
  have hMne : (maximalIdeal C).map (algebraMap C (C ⊗[ℤ] O)) ≠ ⊤ := by
    intro h
    have := Ideal.Quotient.subsingleton_iff.mpr h
    exact not_subsingleton ((C ⊗[ℤ] O) ⧸ (maximalIdeal C).map (algebraMap C (C ⊗[ℤ] O))) this
  obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ hMne
  haveI := h𝔫

  obtain ⟨hmap, hloc, -, -⟩ := IsLocalRing.map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing 𝔫 hle
  obtain ⟨hacD, hchar⟩ := IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField ℓ C O hℓO hac 𝔫
  haveI : Module.Flat C (Localization.AtPrime 𝔫) := Module.Flat.trans C (C ⊗[ℤ] O) (Localization.AtPrime 𝔫)
  haveI := hloc
  have hart' : IsArtinianRing (Localization.AtPrime 𝔫) := by
    refine (isArtinianRing_iff_isNilpotent_maximalIdeal (Localization.AtPrime 𝔫)).mpr ?_
    rw [← hmap]
    obtain ⟨N, hN⟩ := hnil
    refine ⟨N, ?_⟩
    have : (maximalIdeal C).map (algebraMap C (Localization.AtPrime 𝔫)) =
        ((maximalIdeal C).map (algebraMap C (C ⊗[ℤ] O))).map (algebraMap (C ⊗[ℤ] O) (Localization.AtPrime 𝔫)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [this, ← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot]
    rfl
  exact ⟨Localization.AtPrime 𝔫, inferInstance, inferInstance, hart', inferInstance, ℓ, hF,
    Module.FaithfullyFlat.of_flat_of_isLocalHom, hloc, hmap, hacD, hchar⟩

end S_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField
end P2MW
export P2MW.S_IsArtinianRing_exists_faithfullyFlat_isLocalHom_isAlgClosed_residueField_of_finite_residueField (solution)
