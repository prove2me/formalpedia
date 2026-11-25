-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_fibres_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:56.87956+00:00
-- url     : https://prove2.me/submissions/75557893-1426-46dc-9525-f3d5e5bea28f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Theorems.Thm_GlobalTheory_FibreFlat_flatOver_of_pullback
import Theorems.Thm_GlobalTheory_FibreFlat_flat_of_flatOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (X Y : Over (Sp T)) (φ : X ⟶ Y), Flat X.hom → Flat Y.hom →
      LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom →
      Flat ((Over.pullback (spMap (algebraMap T K))).map φ).left →
      Flat ((Over.pullback (spMap (IsLocalRing.residue T))).map φ).left → Flat φ.left := by
  intro T K _ _ _ _ _ _ X Y φ h1 _ h2 h3 hK hκ
  exact FibreFlat.flat_of_flatOver T K φ.left Y.hom (by rwa [Over.w]) (by rwa [Over.w]) h3
    (FibreFlat.flatOver_of_pullback φ _ hK) (FibreFlat.flatOver_of_pullback φ _ hκ)
end GlobalTheory
