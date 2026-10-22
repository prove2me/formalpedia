-- Prove2me | solution 1 for MazurTransfer.original_bialgebra_cyclic_mu19_point_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T22:04:24.068119+00:00
-- url     : https://prove2.me/submissions/7d27df52-b7b1-4697-8a43-3eb9d4464701

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a given original cyclic bialgebra equivalence supplies literal nineteenth-root points over every coefficient algebra, with the same multiplication and all coefficient maps.
Named downstream consumer: normalization of the same selected integral pi quotient and its norm torsor pushforward at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points
namespace MazurTransfer.OriginalBialgebraCyclicMu19PointBoundary20261020
end MazurTransfer.OriginalBialgebraCyclicMu19PointBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a GIVEN cyclic bialgebra equivalence supplies literal mu19
points over EVERY coefficient algebra, naturally and multiplicatively.
Named downstream consumer: field-label normalization of the SAME selected
integral pi quotient and its norm torsor pushforward at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalBialgebraCyclicMu19PointProof20261020
open CyclicNineteenGroupAlgebraPoints
variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic)
variable (T : Type) [CommRing T] [Algebra R T]





theorem literalPointEquiv_val (f : WithConv (H →ₐ[R] T)) :
    ((literalPointEquiv φ T f : Tˣ) : T) = f (φ.symm (MonoidAlgebra.single generator 1)) := rfl

theorem literalPointEquiv_natural {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (H →ₐ[R] T)) :
    literalPointEquiv φ T' (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (literalPointEquiv φ T f) := by
  apply Subtype.ext
  apply Units.ext
  rfl

end MazurTransfer.OriginalBialgebraCyclicMu19PointProof20261020

theorem solution : (∀ {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ (f : WithConv (H →ₐ[R] T)),
((literalPointEquiv φ T f : Tˣ) : T) = f (φ.symm (MonoidAlgebra.single generator 1))) ∧ (∀ {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (T : Type) [CommRing T] [Algebra R T], ∀ {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (H →ₐ[R] T)),
literalPointEquiv φ T' (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (literalPointEquiv φ T f)) := by
  exact ⟨MazurTransfer.OriginalBialgebraCyclicMu19PointProof20261020.literalPointEquiv_val, MazurTransfer.OriginalBialgebraCyclicMu19PointProof20261020.literalPointEquiv_natural⟩
#print axioms solution
