-- Prove2me | solution 1 for MazurTransfer.RelativeGroupSchemeNsmulInternalPowerCompatibility.schemeNsmul_eq_internal_power
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:34:53.485773+00:00
-- url     : https://prove2.me/submissions/b75cf235-8ac2-440b-9e29-74cc5b3c4b05

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: integer multiplication in the relative group-law API is
exactly the underlying morphism of the internal pointwise power of the
identity. Named downstream consumer: formal unramifiedness of the actual
Picard norm factors via their checked scalar-nineteen composites.
-/
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)]

namespace MazurTransfer.RelativeGroupPowerCompatibilityHelpers20261017
theorem nsmul_eq_overHom_power {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).nsmul t n x =
      overHomToSchemeHomOver ((schemeHomOverToOverHom x) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]
    rfl

end MazurTransfer.RelativeGroupPowerCompatibilityHelpers20261017
open MazurTransfer.RelativeGroupPowerCompatibilityHelpers20261017
theorem solution (n : ℕ) :
    (relativeGroupLawOfGrpObj R f).schemeNsmul n = ((𝟙 (Over.mk f)) ^ n).left := by
  unfold RelativeGroupLaw.schemeNsmul
  rw [nsmul_eq_overHom_power]
  rfl


#print axioms solution
