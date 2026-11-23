-- Prove2me | solution 1 for GlobalTheory.ThetaQuotient.exists_div_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:45.93255+00:00
-- url     : https://prove2.me/submissions/65fb3dfe-9b90-447c-84e5-f1bc75791ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
import Theorems.Thm_P2M_GlobalTheory_valAt__map_238ef0722272
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__units_inv_d8876f25a60d


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
open GlobalTheory.ThetaQuotient
namespace GlobalTheory.ThetaQuotient
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (f g : Γ(X, U)) :
    ∃ s : Γ(X, X.basicOpen g), ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ X.basicOpen g →
      valAt' x (X.basicOpen g) s = valAt' x U f / valAt' x U g := by
  have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom f * (u⁻¹).val, fun x hx => ?_⟩
  have h1 : valAt' x (X.basicOpen g) u.val = valAt' x U g := by
    rw [hu]
    exact valAt'_map x _ g hx
  rw [valAt'_mul, valAt'_map x _ f hx, div_eq_mul_inv, ← h1]
  congr 1
  exact valAt'_units_inv x hx u
end GlobalTheory.ThetaQuotient
