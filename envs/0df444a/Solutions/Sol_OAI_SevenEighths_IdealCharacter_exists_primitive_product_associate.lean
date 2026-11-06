-- Prove2me | solution 1 for OAI.SevenEighths.IdealCharacter.exists_primitive_product_associate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:02:17.270119+00:00
-- url     : https://prove2.me/submissions/2794094b-88ed-4524-bac1-3ee9c2b1fc90

import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_product
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_exists_primitive_associate
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_inf_le_mul
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_finite_quotient_inf
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_product_global_units


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.IdealCharacter
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
variable [IsDomain A] [IsPrincipalIdealRing A]
variable [hInfinite : Infinite A]
include hInfinite
namespace OAI.SevenEighths.IdealCharacter
theorem _root_.solution (M N : Ideal A)
    [Finite (A ⧸ M)] [Finite (A ⧸ N)]
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.cardQuot ≤ M.cardQuot * N.cardQuot ∧
      (∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by
  let : Finite (A ⧸ M ⊓ N) := ResidueCharacter.finite_quotient_inf M N
  obtain ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm, hmask, hdelete⟩ :=
    exists_primitive_associate (M ⊓ N) (ResidueCharacter.product M N χ ψ)
      (ResidueCharacter.product_global_units M N χ ψ hχ hψ)
  refine ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul M N), ?_, ?_⟩
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hmask I)
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hdelete I)
end OAI.SevenEighths.IdealCharacter
