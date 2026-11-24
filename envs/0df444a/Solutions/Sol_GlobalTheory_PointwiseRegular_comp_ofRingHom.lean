-- Prove2me | solution 1 for GlobalTheory.PointwiseRegular.comp_ofRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:06.282685+00:00
-- url     : https://prove2.me/submissions/2ea07c5c-d863-432b-9708-7601a31e6f18

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
import Theorems.Thm_P2M_GlobalTheory_PointwiseRegular_top_le_preimage___710ebdfb7c4b
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.PointwiseRegular
namespace GlobalTheory.PointwiseRegular
theorem _root_.solution {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D)
    (r : Γ(X, D) →+* Γ(Y, U)) (y : Sp ℂ ⟶ U.toScheme) (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ D)
    (h : ∀ φ, valAt' (y ≫ U.ι) U (r φ) = valAt' x D φ) : y ≫ ofRingHom U hD r = x := by
  have hy := top_le_preimage_ι U y
  have e1 : CommRingCat.ofHom r ≫ (y ≫ U.ι).appLE U ⊤ hy = x.appLE D ⊤ hx := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    ext φ
    have := h φ
    rw [valAt'_eq_valAt _ hy, valAt'_eq_valAt _ hx] at this
    exact this
  have e2 : (isAffineOpen_top (Sp ℂ)).fromSpec ≫ y ≫ U.toSpecΓ = Spec.map ((y ≫ U.ι).appLE U ⊤ hy) := by
    rw [IsAffineOpen.fromSpec_top, Iso.inv_comp_eq, Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc,
      ← Spec.map_comp]
    congr 2
    rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have : IsIso (isAffineOpen_top (Sp ℂ)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top (Sp ℂ)).fromSpec, ← hD.SpecMap_appLE_fromSpec x _ hx, ← e1, ofRingHom,
    reassoc_of% e2, Spec.map_comp_assoc]
end GlobalTheory.PointwiseRegular
