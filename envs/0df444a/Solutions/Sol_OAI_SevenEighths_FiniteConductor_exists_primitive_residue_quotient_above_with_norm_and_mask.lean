-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.exists_primitive_residue_quotient_above_with_norm_and_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:48:27.01559+00:00
-- url     : https://prove2.me/submissions/bcc51051-b09d-4ac0-abe6-fc3ac2e2ea21

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_primitive_quotient_above_with_bound_and_mask
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_comap_eq_quotient_card

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      (I.comap (Ideal.Quotient.mk M)).cardQuot ≤
        (J.comap (Ideal.Quotient.mk M)).cardQuot ∧
      ∀ a : A ⧸ M, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask χ J hJ
  refine ⟨I, φ, hJI, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard
end OAI.SevenEighths.FiniteConductor
