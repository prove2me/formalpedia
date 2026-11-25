-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.algebraMap_epsA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:14.622626+00:00
-- url     : https://prove2.me/submissions/5f929c22-4b21-407b-b364-2b852c287e85

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}
attribute [local instance] unit_isAffine
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (x : (OSys A.hom S).obj (op a₀)) :
    algebraMap R (Sec (𝟙_ (Over (Sp R))).hom ⊤) (epsA ha x) = secA (wOver η[A]) (ptPair ha) x :=
  (AlgEquiv.ofBijective (Algebra.ofId R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) (unit_bijective R)).apply_symm_apply
    (secA (wOver η[A]) (ptPair ha) x)
end GlobalTheory.CompanionTheory.HopfSys
