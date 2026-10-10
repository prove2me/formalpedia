-- Prove2me | solution 1 for MazurTransfer.polynomial_power_substitution_basis
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T11:09:15.181343+00:00
-- url     : https://prove2.me/submissions/d62c21bd-ad87-4e3c-a76c-47b24d67cd86

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the source-tagged constructor binds to the ordinary
polynomial-ring power action, with no tag in the public interface.
Named downstream consumer: the public parameter-power basis theorem. -/
import Definitions.Def_MazurTransfer_PolynomialPowerSubstitution

noncomputable section
universe u
open Polynomial Module
open scoped PolynomialPowerSubstitutionLibrary.MazurTransfer.PolynomialPowerSubstitutionPresentation

theorem solution (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    letI : Algebra (Polynomial R) (Polynomial R) :=
      (aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra
    letI : SMul (Polynomial R) (Polynomial R) :=
      ((aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra).toSMul
    letI : Module (Polynomial R) (Polynomial R) :=
      @Algebra.toModule _ _ _ _ ((aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra)
    Nonempty (Basis (Fin n) (Polynomial R) (Polynomial R)) := by
  letI : Algebra (Polynomial R) (Polynomial R) :=
    (aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra
  letI : SMul (Polynomial R) (Polynomial R) :=
    ((aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra).toSMul
  letI : Module (Polynomial R) (Polynomial R) :=
    @Algebra.toModule _ _ _ _ ((aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra)
  let b := PolynomialPowerSubstitutionLibrary.MazurTransfer.PolynomialPowerSubstitutionBasis.powerBasis R n hn
  refine ⟨b.mapCoeffs (RingEquiv.refl (Polynomial R)) ?_⟩
  intro c x
  change aeval ((X : Polynomial R)^n) c * x =
    PolynomialPowerSubstitutionLibrary.MazurTransfer.PolynomialPowerSubstitutionPresentation.powerMap R n c * x
  rfl


#print axioms solution
