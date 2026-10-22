-- Prove2me | solution 1 for MazurTransfer.original_bialgebra_mu19_quotient_point_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T02:27:39.38908+00:00
-- url     : https://prove2.me/submissions/5c5fd344-e3a7-4847-95bd-019d085a9ec8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the literal nineteenth-root quotient points induced by the given genuine bialgebra map and cyclic equivalence over every original coefficient algebra.
Named downstream consumer: the same selected integral pi norm-kernel map and pushforward of its norm-preimage cocycles at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalBialgebraMu19QuotientPointsData20261020
import Theorems.Thm_MazurTransfer_original_bialgebra_point_restriction_laws
import Theorems.Thm_MazurTransfer_original_bialgebra_cyclic_mu19_point_laws
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points MazurTransfer.BialgebraPointRestriction MazurTransfer.BialgebraMu19QuotientPoints
namespace MazurTransfer.OriginalBialgebraMu19QuotientPointBoundary20261020
end MazurTransfer.OriginalBialgebraMu19QuotientPointBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal mu19 quotient points induced by the GIVEN
bialgebra inclusion and normalized cyclic equivalence over EVERY algebra.
Named downstream consumer: the SAME actual integral pi norm-kernel map
and pushforward of its norm-preimage cocycles at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalBialgebraMu19QuotientPointProof20261020
open CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points BialgebraPointRestriction
variable {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable [CommRing G] [Bialgebra R G]
variable (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic)
variable (T : Type) [CommRing T] [Algebra R T]



theorem quotientPoint_mul (f g : WithConv (G →ₐ[R] T)) :
    quotientPoint j ψ T (f * g) = quotientPoint j ψ T f * quotientPoint j ψ T g := by
  unfold quotientPoint
  rw [MazurTransfer.original_bialgebra_point_restriction_laws.1, map_mul]

theorem quotientPoint_one : quotientPoint j ψ T (1 : WithConv (G →ₐ[R] T)) = 1 := by
  unfold quotientPoint
  rw [MazurTransfer.original_bialgebra_point_restriction_laws.2.1, map_one]

theorem quotientPoint_natural {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (G →ₐ[R] T)) :
    quotientPoint j ψ T' (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (quotientPoint j ψ T f) := by
  unfold quotientPoint
  rw [MazurTransfer.original_bialgebra_point_restriction_laws.2.2, MazurTransfer.original_bialgebra_cyclic_mu19_point_laws.2]

end MazurTransfer.OriginalBialgebraMu19QuotientPointProof20261020

theorem solution : (∀ {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing G] [Bialgebra R G] (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ (f g : WithConv (G →ₐ[R] T)),
quotientPoint j ψ T (f * g) = quotientPoint j ψ T f * quotientPoint j ψ T g) ∧ (∀ {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing G] [Bialgebra R G] (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], quotientPoint j ψ T (1 : WithConv (G →ₐ[R] T)) = 1) ∧ (∀ {R H G : Type} [CommRing R] [CommRing H] [Bialgebra R H] [CommRing G] [Bialgebra R G] (j : H →ₐc[R] G) (ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (G →ₐ[R] T)),
quotientPoint j ψ T' (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (quotientPoint j ψ T f)) := by
  exact ⟨MazurTransfer.OriginalBialgebraMu19QuotientPointProof20261020.quotientPoint_mul, MazurTransfer.OriginalBialgebraMu19QuotientPointProof20261020.quotientPoint_one, MazurTransfer.OriginalBialgebraMu19QuotientPointProof20261020.quotientPoint_natural⟩
#print axioms solution
