-- Prove2me | solution 1 for GlobalTheory.exists_lift_of_schemeTheoreticallyDominant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:32.784617+00:00
-- url     : https://prove2.me/submissions/89ec843b-b91e-417a-b85c-f680a3042fba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {W Y X Z : Scheme.{0}} (φ : W ⟶ Y)
    [IsSchemeTheoreticallyDominant φ] (i : Z ⟶ X) [IsClosedImmersion i] (a : Y ⟶ X) (c : W ⟶ Z)
    (h : c ≫ i = φ ≫ a) : ∃ b : Y ⟶ Z, b ≫ i = a := by
  have H : i.ker ≤ a.ker := by
    have h1 : i.ker ≤ (c ≫ i).ker := Scheme.Hom.le_ker_comp c i
    rwa [h, ← Scheme.IdealSheafData.map_ker, φ.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h1
  exact ⟨IsClosedImmersion.lift i a H, IsClosedImmersion.lift_fac i a H⟩
end GlobalTheory
