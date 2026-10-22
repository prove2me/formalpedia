-- Prove2me | solution 1 for MazurTransfer.original_bialgebra_base_change_point_restriction_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T02:19:57.457712+00:00
-- url     : https://prove2.me/submissions/70099858-3f9a-46ab-81e2-3cad9b27a661

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: scalar change of the given genuine bialgebra map retains the original point restriction square with the same source and quotient labels.
Named downstream consumer: normalized literal mu19 realization of the previously selected integral pi quotient after canonical scalar change at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalBialgebraBaseChangePointRestrictionData20261020
import Definitions.Def_MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraPointRestrictionData20261020
noncomputable section
open MazurTransfer
open MazurTransfer.BialgebraBaseChangePointRestriction
open scoped TensorProduct
namespace MazurTransfer.OriginalBialgebraBaseChangePointRestrictionBoundary20261020
end MazurTransfer.OriginalBialgebraBaseChangePointRestrictionBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: base-change the GIVEN bialgebra map and prove its point
restriction square with the SAME original source and quotient labels.
Named downstream consumer: normalized mu19 realization of the PREVIOUSLY
SELECTED actual pi quotient after canonical scalar change at nineteen.
-/

noncomputable section
namespace MazurTransfer.OriginalBialgebraBaseChangePointRestrictionProof20261020
open scoped TensorProduct
variable {R S H G : Type} [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing H] [HopfAlgebra R H] [CommRing G] [HopfAlgebra R G]



theorem baseChangeMap_tmul (j : H →ₐc[R] G) (s : S) (h : H) :
    baseChangeMap (S := S) j (s ⊗ₜ[R] h) = s ⊗ₜ[R] j h := rfl

variable {K : Type} [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

theorem point_restriction_square (j : H →ₐc[R] G)
    (f : WithConv (S ⊗[R] G →ₐ[S] K)) :
    HopfBaseChangeArithmeticPoints.restrictPoint
        (BialgebraPointRestriction.restrictPoint (baseChangeMap (S := S) j) f) =
      BialgebraPointRestriction.restrictPoint j
        (HopfBaseChangeArithmeticPoints.restrictPoint f) := rfl

end MazurTransfer.OriginalBialgebraBaseChangePointRestrictionProof20261020

theorem solution : (∀ {R S H G : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing G] [HopfAlgebra R G], ∀ (j : H →ₐc[R] G) (s : S) (h : H),
baseChangeMap (S := S) j (s ⊗ₜ[R] h) = s ⊗ₜ[R] j h) ∧ (∀ {R S H G : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing G] [HopfAlgebra R G], ∀ {K : Type} [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ (j : H →ₐc[R] G)
    (f : WithConv (S ⊗[R] G →ₐ[S] K)),
HopfBaseChangeArithmeticPoints.restrictPoint
        (BialgebraPointRestriction.restrictPoint (baseChangeMap (S := S) j) f) =
      BialgebraPointRestriction.restrictPoint j
        (HopfBaseChangeArithmeticPoints.restrictPoint f)) := by
  exact ⟨MazurTransfer.OriginalBialgebraBaseChangePointRestrictionProof20261020.baseChangeMap_tmul, MazurTransfer.OriginalBialgebraBaseChangePointRestrictionProof20261020.point_restriction_square⟩
#print axioms solution
